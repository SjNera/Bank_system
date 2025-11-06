#include <iostream>
#include <vector>
#include <string>
#include <regex>
#include <ctime>
#include <iomanip>
#include <sstream>
#include <map>
#include <cmath>
#include <limits>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <random>
#include <chrono>
#include <bit>
#include <stdexcept>
#include <optional> // Used for database find operations

// --- NEW: SQLite3 ---
// This is a C library, so include it here.
#include <sqlite3.h>

// External C library (libsodium)
// Wrap in extern "C" to prevent C++ name mangling.
extern "C" {
#include <sodium.h>
}

using namespace std;

// --- Forward Declarations ---
class passwordHasher;
class Encryption;
class Loan;
class SavingsGoal;
struct Transaction;
class DatabaseManager;

enum class HMAC { SHA1, SHA256, SHA512 };

// Anonymous namespace for file-local helper functions
namespace {

// Calculates the decoded length (in bytes) of a Base32 string.
inline constexpr size_t base32_length_decoded(size_t n_b32_chars) {
    auto n_bits = n_b32_chars * 5;
    auto n_bytes = n_bits / 8;
    return n_bytes;
}

// Decodes a Base32 encoded string into raw bytes.
ssize_t base32_decode(const char* b32, void* decoded) {
    int bitbuf = 0;
    int bits_rem = 0;
    ssize_t count = 0;
    uint8_t* dec = reinterpret_cast<uint8_t*>(decoded);

    for (const char* ptr = b32; *ptr; ++ptr) {
        char ch = *ptr;

        // Skip whitespace, padding, and separators
        if (ch == ' ' || ch == '\t' || ch == '\r' || ch == '\n' || ch == '-' || ch == '=')
            continue;

        bitbuf <<= 5; // Make room for 5 new bits

        // Handle common character ambiguities (0->O, 1->L, 8->B)
        if (ch == '0') ch = 'O';
        else if (ch == '1') ch = 'L';
        else if (ch == '8') ch = 'B';

        // Convert Base32 character to its 5-bit integer value
        if ((ch >= 'A' && ch <= 'Z') || (ch >= 'a' && ch <= 'z'))
            ch = (ch & 0b1'1111) - 1; // A-Z maps to 0-25
        else if (ch >= '2' && ch <= '7')
            ch -= '2' - 26; // 2-7 maps to 26-31
        else
            return -1; // Invalid character

        bitbuf |= ch;
        bits_rem += 5;

        // If we have at least 8 bits, output a byte
        if (bits_rem >= 8) {
            dec[count++] = bitbuf >> (bits_rem - 8); // Get the top 8 bits
            bits_rem -= 8;
        }
    }
    return count;
}

// Performs dynamic truncation (RFC 4226) on an HMAC result.
uint32_t dyn_truncate(const uint8_t* in, int in_len) {
    // Get the last nibble (4 bits) of the hash
    int offset = in[in_len - 1] & 0xf;

    // Get 4 bytes from the hash at that offset
    uint32_t hdigits = in[offset] & 0x7f; // Get first byte, clear MSB
    for (int k = 1; k < 4; ++k)
        hdigits = (hdigits << 8) | (in[offset + k] & 0xff); // Append next 3 bytes

    return hdigits;
}

inline constexpr uint64_t ipow(uint64_t b, uint64_t e) {
    uint64_t v = 1;
    for (uint64_t k = 1; k <= e; ++k) v *= b;
    return v;
}

// Swaps the byte order of a 64-bit integer (little-endian <-> big-endian).
inline constexpr uint64_t byteswap(uint64_t ull) {
    return (ull >> 56) | ((ull << 40) & 0x00FF000000000000) |
           ((ull << 24) & 0x0000FF0000000000) | ((ull << 8) & 0x000000FF00000000) |
           ((ull >> 8) & 0x00000000FF000000) | ((ull >> 24) & 0x0000000000FF0000) |
           ((ull >> 40) & 0x000000000000FF00) | (ull << 56);
}
} // namespace

// Generates an HMAC-based One-Time Password (HOTP).
uint32_t generate_HOTP(const char* b32_secret, unsigned int digits, uint64_t counter, HMAC hash_algo) {
    size_t hmac_bytes, key_bytes;

    // Select libsodium function parameters
    switch (hash_algo) {
        case HMAC::SHA256:
            hmac_bytes = crypto_auth_hmacsha256_BYTES;
            key_bytes = crypto_auth_hmacsha256_KEYBYTES;
            break;
        case HMAC::SHA512:
            hmac_bytes = crypto_auth_hmacsha512_BYTES;
            key_bytes = crypto_auth_hmacsha512_KEYBYTES;
            break;
        default:
            throw invalid_argument("HMAC algorithm not supported");
    }
    if (digits > 9) throw invalid_argument("digits must not exceed 9");

    // Decode the Base32 secret key
    auto key_plain_len_max = base32_length_decoded(strlen(b32_secret));
    auto key_plain = make_unique<uint8_t[]>(key_plain_len_max);
    ssize_t key_len = base32_decode(b32_secret, key_plain.get());
    if (key_len < 0) throw invalid_argument("BASE32 decoding failed");

    auto key = make_unique<unsigned char[]>(key_bytes);
    memcpy(key.get(), key_plain.get(), key_len < key_bytes ? key_len : key_bytes);

    // RFC 4226 requires the counter to be a 64-bit Big-Endian value.
    if constexpr (std::endian::native == std::endian::little)
        counter = byteswap(counter);

    // Compute the HMAC
    auto hmac = make_unique<unsigned char[]>(hmac_bytes);
    switch (hash_algo) {
        case HMAC::SHA256:
            crypto_auth_hmacsha256(hmac.get(), (const unsigned char*)&counter, sizeof(counter), key.get());
            break;
        case HMAC::SHA512:
            crypto_auth_hmacsha512(hmac.get(), (const unsigned char*)&counter, sizeof(counter), key.get());
            break;
        default: break;
    }

    // Perform dynamic truncation
    uint64_t otp_digits = dyn_truncate(hmac.get(), hmac_bytes);

    // Modulo by 10^digits to get the final code
    return static_cast<uint32_t>(otp_digits % ipow(10, digits));
}

// Generates a Time-based One-Time Password (TOTP).
uint32_t generate_TOTP(const char* b32_secret, unsigned int digits, unsigned int period,
                        int t0, HMAC hash_algo, int64_t seconds_since_epoch = -1) {
    uint64_t counter;
    if (seconds_since_epoch >= 0) {
        // Use provided time (for testing/verification)
        counter = (static_cast<uint64_t>(seconds_since_epoch) + t0) / period;
    } else {
        // Use system's current time
        auto ts_utc = time(nullptr);
        if (int64_t(ts_utc) + t0 < 0)
            throw invalid_argument("invalid shift value");
        counter = (ts_utc + t0) / period;
    }
    // TOTP is just HOTP with the counter being derived from time
    return generate_HOTP(b32_secret, digits, counter, hash_algo);
}

// Generates a cryptographically random Base32 secret key.
void generate_b32_secret(char* buffer, unsigned int buffer_length) {
    if (buffer_length == 0) return;
    random_device rd; // Non-deterministic hardware random source
    default_random_engine prng(rd()); // PRNG seeded
    uniform_int_distribution<int> randu(0, 31);

    for (unsigned int k = 0; k < buffer_length - 1; ++k)
        // Map 0-31 to the Base32 character set
        buffer[k] = "ABCDEFGHIJKLMNOPQRSTUVWXYZ234567"[randu(prng)];

    buffer[buffer_length - 1] = '\0'; // Null-terminate
}

// Manages password hashing and key derivation using Argon2id.
class passwordHasher {
private:
    unsigned char derived_key_[crypto_secretbox_KEYBYTES];
    unsigned char salt_[crypto_pwhash_SALTBYTES];
    bool key_derived_ = false;

    // Internal function to perform key derivation.
    void deriveKey(const string& password, const unsigned char* salt_to_use) {
        // crypto_pwhash is libsodium's high-level API for Argon2id.
        if (crypto_pwhash(derived_key_, sizeof(derived_key_),
                         password.c_str(), password.size(),
                         salt_to_use,
                         crypto_pwhash_OPSLIMIT_INTERACTIVE,
                         crypto_pwhash_MEMLIMIT_INTERACTIVE,
                         crypto_pwhash_ALG_DEFAULT) != 0) { // ALG_DEFAULT is Argon2id
            throw runtime_error("Key derivation failed");
        }
        key_derived_ = true;
    }

public:
    passwordHasher() {}

    // Generates a new key and a new salt from a password (for registration).
    void generateKeyFromPassword(const string& password) {
        // Generate a new, cryptographically random salt
        randombytes_buf(salt_, sizeof(salt_));
        deriveKey(password, salt_);
    }

    // Regenerates a key from a password and a stored salt (for login).
    void regenerateKeyFromPassword(const string& password, const unsigned char* stored_salt) {
        if (stored_salt == nullptr) throw runtime_error("Invalid salt");
        memcpy(salt_, stored_salt, sizeof(salt_));
        // Derive the key using the *same* salt
        deriveKey(password, salt_);
    }

    const unsigned char* getKey() const {
        if (!key_derived_) throw runtime_error("Key not derived");
        return derived_key_;
    }

    const unsigned char* getSalt() const {
        if (!key_derived_) throw runtime_error("Salt not generated");
        return salt_;
    }

    // Check if key is derived
    bool isKeyDerived() const { return key_derived_; }
};

// Handles symmetric encryption (XChaCha20-Poly1305).
class Encryption {
private:
    unsigned char key_[crypto_secretbox_KEYBYTES];
    bool key_set_ = false;
public:
    Encryption() {}

    // Sets the encryption key from a passwordHasher instance.
    void setKeyFromPasswordHasher(const passwordHasher& hasher) {
        if (!hasher.isKeyDerived()) {
            throw runtime_error("Cannot set key from underived hasher");
        }
        const unsigned char* derived_key = hasher.getKey();
        memcpy(key_, derived_key, crypto_secretbox_KEYBYTES);
        key_set_ = true;
    }

    // Encrypts data and returns [nonce][ciphertext][mac].
    vector<unsigned char> encryptByte(const unsigned char* data, size_t len) {
        if (!key_set_) throw runtime_error("Encryption key not set");

        const size_t nonce_len = crypto_secretbox_NONCEBYTES;
        const size_t mac_len = crypto_secretbox_MACBYTES;
        size_t total_len = nonce_len + mac_len + len;

        vector<unsigned char> output_vector(total_len);

        unsigned char* nonce_ptr = output_vector.data();
        unsigned char* ciphertext_ptr = output_vector.data() + nonce_len;

        // Generate a new, random nonce for every message
        randombytes_buf(nonce_ptr, nonce_len);

        // Encrypt and authenticate
        if (crypto_secretbox_easy(ciphertext_ptr, data, len, nonce_ptr, key_) != 0)
            throw runtime_error("Encryption failed");

        return output_vector;
    }

    // Decrypts data from [nonce][ciphertext][mac].
    vector<unsigned char> decryptByte(const vector<unsigned char>& encrypted_package) {
        if (!key_set_) throw runtime_error("Decryption key not set");

        const size_t nonce_len = crypto_secretbox_NONCEBYTES;
        const size_t mac_len = crypto_secretbox_MACBYTES;
        const size_t min_len = nonce_len + mac_len;

        if (encrypted_package.size() < min_len) throw runtime_error("Package too small");

        size_t ciphertext_len = encrypted_package.size() - nonce_len;
        size_t plaintext_len = ciphertext_len - mac_len;

        vector<unsigned char> decrypted_vector(plaintext_len);

        const unsigned char* nonce_ptr = encrypted_package.data();
        const unsigned char* ciphertext_ptr = encrypted_package.data() + nonce_len;

        // Decrypt and verify. Fails if key is wrong or data is tampered with.
        if (crypto_secretbox_open_easy(decrypted_vector.data(), ciphertext_ptr,
                                       ciphertext_len, nonce_ptr, key_) != 0)
            throw runtime_error("Decryption failed (invalid key or tampered message)");

        return decrypted_vector;
    }
};

string toHexString(const unsigned char* data, size_t length) {
    stringstream ss;
    ss << hex << setfill('0');
    for (size_t i = 0; i < length; i++) {
        ss << setw(2) << (int)data[i];
    }
    return ss.str();
}

void fromHexString(const string& hex, unsigned char* output, size_t output_size) {
    if (hex.length() != output_size * 2) throw runtime_error("Invalid hex length");
    for (size_t i = 0; i < output_size; i++) {
        string byte = hex.substr(i * 2, 2);
        output[i] = (unsigned char)strtol(byte.c_str(), nullptr, 16);
    }
}

// Verifies a user-provided TOTP code against the current, previous, and next time steps.
bool verifyOTP(const string& b32_secret, const string& userCode) {
    uint32_t code_int = 0;
    try {
        code_int = stoul(userCode);
    } catch (const invalid_argument&) {
        return false;
    } catch (const out_of_range&) {
        return false;
    }

    const unsigned int digits = 6;
    const unsigned int period = 30;
    const HMAC hash_algo = HMAC::SHA256;

    auto ts_utc = chrono::duration_cast<chrono::seconds>(
        chrono::system_clock::now().time_since_epoch()).count();

    try {
        // Check current time step (t)
        uint32_t totp_now = generate_TOTP(b32_secret.c_str(),
            digits, period, 0, hash_algo, ts_utc);
        if (totp_now == code_int) return true;

        // Check previous time step (t-1)
        uint32_t totp_prev = generate_TOTP(b32_secret.c_str(),
            digits, period, 0, hash_algo, ts_utc - period);
        if (totp_prev == code_int) return true;

        // Check next time step (t+1)
        uint32_t totp_next = generate_TOTP(b32_secret.c_str(),
            digits, period, 0, hash_algo, ts_utc + period);
        if (totp_next == code_int) return true;

    } catch (const exception& e) {
        cerr << "OTP generation error: " << e.what() << endl;
        return false;
    }

    return false;
}

// Clears the standard input buffer.
void clearInput() {
    cin.clear();
    cin.ignore(numeric_limits<streamsize>::max(), '\n');
}

enum LoanType { PERSONAL, CAR, HOUSING, BUSINESS };

// Represents a loan account.
class Loan {
protected:
    int loanID; // This will now be the database Primary Key
    double amount, balance, interestRate;
    int termMonths;
    bool isActive;
    LoanType type;
    static map<LoanType, double> fixedRates;
public:
    // Constructor for creating a *new* loan
    Loan(LoanType t, double amt, int months)
        : loanID(0), amount(amt), balance(amt), termMonths(months), isActive(true), type(t) {
        interestRate = fixedRates[type];
    }

    // Constructor for loading an *existing* loan from the DB
    Loan(int id, LoanType t, double amt, double bal, int months, bool active)
        : loanID(id), amount(amt), balance(bal), termMonths(months), isActive(active), type(t) {
        interestRate = fixedRates[type];
    }

    // Applies a payment to the loan balance.
    // Returns the amount of overpayment, if any.
    double makePayment(double payment) {
        if (!isActive) {
            cout << "This loan has already been fully paid!\n";
            return payment; // Return full payment
        }
        if (payment <= 0) {
            cout << "Payment must be a positive amount!\n";
            return 0;
        }

        balance -= payment;
        double overpayment = 0;

        if (balance <= 0) {
            if (balance < 0) {
                overpayment = -balance; // Calculate overpayment
                cout << "Overpayment: " << fixed << setprecision(2) << overpayment << " Php will be refunded to your account.\n";
            }
            balance = 0;
            isActive = false;
            cout << "\n************************\n"
                 << "  LOAN FULLY PAID!  \n"
                 << "************************\n";
        } else {
            cout << "Payment: " << fixed << setprecision(2) << payment << " Php\n"
                 << "New Balance: " << fixed << setprecision(2) << balance << " Php\n";
        }
        return overpayment;
    }

    // Reverts the in-memory state of the object if a DB transaction fails.
    void revertPayment(double oldBalance, bool oldActive) {
        balance = oldBalance;
        isActive = oldActive;
    }

    // --- Getters ---
    double getAmount() const { return amount; }
    double getBalance() const { return balance; }
    int getLoanID() const { return loanID; }
    bool getIsActive() const { return isActive; }
    int getTermMonths() const { return termMonths; }
    LoanType getLoanType() const { return type; }
    double getInterestRate() const { return interestRate; }

    // --- Setter ---
    // Needed to set the ID after inserting into the DB
    void setLoanID(int id) { loanID = id; }


    void displayLoanDetails() const {
        cout << "Loan ID: " << loanID << "\n"
             << "Original Amount: " << fixed << setprecision(2) << amount << " Php\n"
             << "Current Balance: " << fixed << setprecision(2) << balance << " Php\n"
             << "Interest Rate: " << fixed << setprecision(1) << interestRate << "%\n"
             << "Term: " << termMonths << " Months\n"
             << "Loan Type: ";
        switch (type) {
            case PERSONAL: cout << "Personal"; break;
            case CAR: cout << "Car"; break;
            case HOUSING: cout << "Housing"; break;
            case BUSINESS: cout << "Business"; break;
        }
        cout << "\nStatus: " << (isActive ? "Active" : "Paid") << "\n";
    }

    // Calculates the fixed monthly payment (amortization).
    double calculateMonthlyRate() const {
        if (termMonths == 0) return amount;
        if (interestRate == 0) return amount / termMonths;
        double mr = interestRate / 100 / 12; // Monthly interest rate
        double denom = pow(1 + mr, termMonths);
        return (amount * mr * denom) / (denom - 1);
    }

    void displayRepaymentSchedule() const {
        cout << "\n*** Repayment Schedule ***\nLoan ID: " << loanID << "\n";
        double mp = calculateMonthlyRate();
        for (int i = 1; i <= termMonths; ++i) {
            cout << "Month " << i << ": " << fixed << setprecision(2) << mp << " Php\n";
        }
    }
};

// Initialize static members for Loan class
map<LoanType, double> Loan::fixedRates = {{PERSONAL, 5.0}, {CAR, 7.0}, {HOUSING, 4.0}, {BUSINESS, 6.0}};

// Represents a user-defined savings goal.
class SavingsGoal {
private:
    int goalID; // Database Primary Key
    string goalName;
    double targetAmount, savedAmount;
    bool completed;
public:
    // Constructor for creating a *new* goal
    SavingsGoal(string name, double target)
        : goalID(0), goalName(name), targetAmount(target), savedAmount(0), completed(false) {}

    // Constructor for loading an *existing* goal from the DB
    SavingsGoal(int id, string name, double target, double saved, bool is_completed)
        : goalID(id), goalName(name), targetAmount(target), savedAmount(saved), completed(is_completed) {}


    string getName() const { return goalName; }
    double getTarget() const { return targetAmount; }
    double getSaved() const { return savedAmount; }
    bool isCompleted() const { return completed; }
    int getGoalID() const { return goalID; }

    // --- Setter ---
    void setGoalID(int id) { goalID = id; }


    // Deposits money into the savings goal.
    bool deposit(double amount, double& excess) {
        if (completed) {
            cout << "This goal is already completed.\n";
            excess = amount; // Return the full amount
            return false;
        }

        savedAmount += amount;
        excess = 0;

        if (savedAmount >= targetAmount) {
            excess = savedAmount - targetAmount; // Calculate overpayment
            savedAmount = targetAmount;
            completed = true;
            cout << "\n************************\n"
                 << "  SAVINGS GOAL REACHED: " << goalName << "!\n"
                 << "************************\n";
            if (excess > 0) {
                cout << "Excess amount: PHP " << fixed << setprecision(2) << excess
                     << " will be returned to your main balance.\n";
            }
            return true;
        }

        cout << "Deposited to " << goalName << ". You need PHP "
             << fixed << setprecision(2) << (targetAmount - savedAmount) << " more.\n";
        return true;
    }

    // Reverts the in-memory state of the object if a DB transaction fails.
    void revertDeposit(double oldSaved, bool oldCompleted) {
        savedAmount = oldSaved;
        completed = oldCompleted;
    }

    void viewProgress() const {
        double progress = (targetAmount > 0) ? (savedAmount / targetAmount * 100) : 100.0;
        cout << "Goal: " << goalName << " (ID: " << goalID << ")\n"
             << "Saved: PHP " << fixed << setprecision(2) << savedAmount
             << " / PHP " << targetAmount << "\n"
             << "Progress: " << fixed << setprecision(1) << progress << "%\n"
             << "Status: " << (completed ? "Completed!\n" : "In Progress\n")
             << "---------------------------\n";
    }
};

// Holds transaction history data.
struct Transaction {
    string type;
    double amount;
    string date;
};

// =================================================================
// == NEW: DatabaseManager Class
// =================================================================
// This class encapsulates all SQLite3 database operations.

// Struct to hold user data retrieved from the database
struct UserData {
    int id;
    string username;
    string accountNumber;
    string passwordHash;
    string passwordSalt;
    string gmail;
    string phoneNumber;
    string otpKey;
    vector<unsigned char> encryptedBalance;
    double dailyWithdrawn;
    string lastWithdrawalDate;
};


class DatabaseManager {
private:
    sqlite3* db_ = nullptr;

    // Helper to throw runtime errors with SQLite messages
    void checkError(int rc, const string& context) {
        if (rc != SQLITE_OK) {
            string errMsg = sqlite3_errmsg(db_);
            sqlite3_close(db_); // Close connection on error
            db_ = nullptr;
            throw runtime_error(context + ": " + errMsg);
        }
    }

    // Helper to execute simple SQL commands
    void exec(const string& sql) {
        char* errMsg = nullptr;
        int rc = sqlite3_exec(db_, sql.c_str(), 0, 0, &errMsg);
        if (rc != SQLITE_OK) {
            string err = errMsg;
            sqlite3_free(errMsg);
            checkError(rc, "SQL exec failed (" + sql.substr(0, 20) + "...)");
        }
    }

public:
    DatabaseManager(const char* dbName) {
        int rc = sqlite3_open(dbName, &db_);
        checkError(rc, "Failed to open database");
        cout << "Database opened successfully: " << dbName << endl;
        // Enable foreign key support
        exec("PRAGMA foreign_keys = ON;");
    }

    ~DatabaseManager() {
        if (db_) {
            sqlite3_close(db_);
            cout << "Database closed." << endl;
        }
    }

    // Creates all necessary tables if they don't exist
    void initSchema() {
        exec(R"(
            CREATE TABLE IF NOT EXISTS Users (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                username TEXT UNIQUE NOT NULL,
                account_number TEXT UNIQUE NOT NULL,
                password_hash TEXT NOT NULL,
                password_salt TEXT NOT NULL,
                gmail TEXT UNIQUE NOT NULL,
                phone_number TEXT UNIQUE NOT NULL,
                otp_key TEXT NOT NULL,
                encrypted_balance BLOB NOT NULL,
                daily_withdrawn REAL DEFAULT 0.0,
                last_withdrawal_date TEXT NOT NULL DEFAULT '1970-01-01'
            );
        )"); // Added last_withdrawal_date

        exec(R"(
            CREATE TABLE IF NOT EXISTS Loans (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                loan_type INTEGER NOT NULL,
                original_amount REAL NOT NULL,
                current_balance REAL NOT NULL,
                interest_rate REAL NOT NULL,
                term_months INTEGER NOT NULL,
                is_active BOOLEAN NOT NULL,
                FOREIGN KEY(user_id) REFERENCES Users(id) ON DELETE CASCADE
            );
        )");

        exec(R"(
            CREATE TABLE IF NOT EXISTS SavingsGoals (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                goal_name TEXT NOT NULL,
                target_amount REAL NOT NULL,
                saved_amount REAL NOT NULL,
                is_completed BOOLEAN NOT NULL,
                FOREIGN KEY(user_id) REFERENCES Users(id) ON DELETE CASCADE
            );
        )");

        exec(R"(
            CREATE TABLE IF NOT EXISTS Transactions (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                type TEXT NOT NULL,
                amount REAL NOT NULL,
                date TEXT NOT NULL,
                FOREIGN KEY(user_id) REFERENCES Users(id) ON DELETE CASCADE
            );
        )");
        cout << "Database schema initialized." << endl;

        // Add indexes
        exec("CREATE INDEX IF NOT EXISTS idx_users_username ON Users(username);");
        exec("CREATE INDEX IF NOT EXISTS idx_users_account_number ON Users(account_number);");
        exec("CREATE INDEX IF NOT EXISTS idx_loans_user_id ON Loans(user_id);");
        exec("CREATE INDEX IF NOT EXISTS idx_savingsgoals_user_id ON SavingsGoals(user_id);");
        exec("CREATE INDEX IF NOT EXISTS idx_transactions_user_id ON Transactions(user_id);");
        cout << "Database indexes created." << endl;
    }

    // --- User Management ---

    // Fetches a user's data by username
    optional<UserData> findUserByUsername(const string& username) {
        sqlite3_stmt* stmt = nullptr;
        const char* sql = "SELECT * FROM Users WHERE username = ?;";

        if (sqlite3_prepare_v2(db_, sql, -1, &stmt, 0) != SQLITE_OK) return nullopt;

        sqlite3_bind_text(stmt, 1, username.c_str(), -1, SQLITE_STATIC);

        if (sqlite3_step(stmt) == SQLITE_ROW) {
            UserData data;
            data.id = sqlite3_column_int(stmt, 0);
            data.username = (const char*)sqlite3_column_text(stmt, 1);
            data.accountNumber = (const char*)sqlite3_column_text(stmt, 2);
            data.passwordHash = (const char*)sqlite3_column_text(stmt, 3);
            data.passwordSalt = (const char*)sqlite3_column_text(stmt, 4);
            data.gmail = (const char*)sqlite3_column_text(stmt, 5);
            data.phoneNumber = (const char*)sqlite3_column_text(stmt, 6);
            data.otpKey = (const char*)sqlite3_column_text(stmt, 7);

            const void* blob_data = sqlite3_column_blob(stmt, 8);
            int blob_size = sqlite3_column_bytes(stmt, 8);
            data.encryptedBalance.assign((const unsigned char*)blob_data, (const unsigned char*)blob_data + blob_size);

            data.dailyWithdrawn = sqlite3_column_double(stmt, 9);
            data.lastWithdrawalDate = (const char*)sqlite3_column_text(stmt, 10);

            sqlite3_finalize(stmt);
            return data;
        }

        sqlite3_finalize(stmt);
        return nullopt;
    }

    // Fetches a user's data by account number
    optional<UserData> findUserByAccountNumber(const string& accNum) {
        sqlite3_stmt* stmt = nullptr;
        const char* sql = "SELECT * FROM Users WHERE account_number = ?;";

        if (sqlite3_prepare_v2(db_, sql, -1, &stmt, 0) != SQLITE_OK) return nullopt;

        sqlite3_bind_text(stmt, 1, accNum.c_str(), -1, SQLITE_STATIC);

        if (sqlite3_step(stmt) == SQLITE_ROW) {
            UserData data;
            data.id = sqlite3_column_int(stmt, 0);
            data.username = (const char*)sqlite3_column_text(stmt, 1);
            data.accountNumber = (const char*)sqlite3_column_text(stmt, 2);
            data.passwordHash = (const char*)sqlite3_column_text(stmt, 3);
            data.passwordSalt = (const char*)sqlite3_column_text(stmt, 4);
            data.gmail = (const char*)sqlite3_column_text(stmt, 5);
            data.phoneNumber = (const char*)sqlite3_column_text(stmt, 6);
            data.otpKey = (const char*)sqlite3_column_text(stmt, 7);
            const void* blob_data = sqlite3_column_blob(stmt, 8);
            int blob_size = sqlite3_column_bytes(stmt, 8);
            data.encryptedBalance.assign((const unsigned char*)blob_data, (const unsigned char*)blob_data + blob_size);
            data.dailyWithdrawn = sqlite3_column_double(stmt, 9);
            data.lastWithdrawalDate = (const char*)sqlite3_column_text(stmt, 10);

            sqlite3_finalize(stmt);
            return data;
        }

        sqlite3_finalize(stmt);
        return nullopt;
    }

    // Checks if gmail or phone are already in use
    bool findUserGmailOrPhone(const string& gmail, const string& phone) {
        sqlite3_stmt* stmt = nullptr;
        const char* sql = "SELECT 1 FROM Users WHERE gmail = ? OR phone_number = ? LIMIT 1;";

        if (sqlite3_prepare_v2(db_, sql, -1, &stmt, 0) != SQLITE_OK) return false;

        sqlite3_bind_text(stmt, 1, gmail.c_str(), -1, SQLITE_STATIC);
        sqlite3_bind_text(stmt, 2, phone.c_str(), -1, SQLITE_STATIC);

        bool exists = (sqlite3_step(stmt) == SQLITE_ROW);
        sqlite3_finalize(stmt);
        return exists;
    }

    // Creates a new user in the database
    int createUser(const string& u, const string& an, const string& ph, const string& ps,
                   const string& e, const string& p, const string& k,
                   const vector<unsigned char>& b) {
        sqlite3_stmt* stmt = nullptr;
        // Note: last_withdrawal_date will use its default value
        const char* sql = R"(
            INSERT INTO Users (username, account_number, password_hash, password_salt, gmail, phone_number, otp_key, encrypted_balance)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?);
        )";

        int rc = sqlite3_prepare_v2(db_, sql, -1, &stmt, 0);
        checkError(rc, "Failed to prepare create user statement");

        sqlite3_bind_text(stmt, 1, u.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_text(stmt, 2, an.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_text(stmt, 3, ph.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_text(stmt, 4, ps.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_text(stmt, 5, e.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_text(stmt, 6, p.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_text(stmt, 7, k.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_blob(stmt, 8, b.data(), b.size(), SQLITE_TRANSIENT);

        rc = sqlite3_step(stmt);
        if (rc != SQLITE_DONE) {
            string errMsg = sqlite3_errmsg(db_);
            sqlite3_finalize(stmt);
            throw runtime_error("Failed to create user: " + errMsg);
        }

        sqlite3_finalize(stmt);
        return static_cast<int>(sqlite3_last_insert_rowid(db_));
    }

    // Updates a user's encrypted balance
    void updateUserBalance(int userId, const vector<unsigned char>& balance) {
        sqlite3_stmt* stmt = nullptr;
        const char* sql = "UPDATE Users SET encrypted_balance = ? WHERE id = ?;";

        int rc = sqlite3_prepare_v2(db_, sql, -1, &stmt, 0);
        checkError(rc, "Failed to prepare update balance statement");

        sqlite3_bind_blob(stmt, 1, balance.data(), balance.size(), SQLITE_TRANSIENT);
        sqlite3_bind_int(stmt, 2, userId);

        rc = sqlite3_step(stmt);
        if (rc != SQLITE_DONE) {
            sqlite3_finalize(stmt);
            throw runtime_error("Failed to update balance");
        }
        sqlite3_finalize(stmt);
    }

    // Update withdrawal amount and date
    void updateUserWithdrawalStatus(int userId, double withdrawn, const string& date) {
        sqlite3_stmt* stmt = nullptr;
        const char* sql = "UPDATE Users SET daily_withdrawn = ?, last_withdrawal_date = ? WHERE id = ?;";

        int rc = sqlite3_prepare_v2(db_, sql, -1, &stmt, 0);
        checkError(rc, "Failed to prepare update daily withdrawal");

        sqlite3_bind_double(stmt, 1, withdrawn);
        sqlite3_bind_text(stmt, 2, date.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_int(stmt, 3, userId);

        rc = sqlite3_step(stmt);
        if (rc != SQLITE_DONE) {
            sqlite3_finalize(stmt);
            throw runtime_error("Failed to update daily withdrawal status");
        }
        sqlite3_finalize(stmt);
    }

    // Updates password, salt, and re-encrypted balance
    void updateUserPasswordAndBalance(int userId, const string& hash, const string& salt, const vector<unsigned char>& balance) {
        sqlite3_stmt* stmt = nullptr;
        const char* sql = "UPDATE Users SET password_hash = ?, password_salt = ?, encrypted_balance = ? WHERE id = ?;";

        int rc = sqlite3_prepare_v2(db_, sql, -1, &stmt, 0);
        checkError(rc, "Failed to prepare update password/balance");

        sqlite3_bind_text(stmt, 1, hash.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_text(stmt, 2, salt.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_blob(stmt, 3, balance.data(), balance.size(), SQLITE_TRANSIENT);
        sqlite3_bind_int(stmt, 4, userId);

        rc = sqlite3_step(stmt);
        if (rc != SQLITE_DONE) {
            sqlite3_finalize(stmt);
            throw runtime_error("Failed to update password and balance");
        }
        sqlite3_finalize(stmt);
    }

    // --- Loan Management ---

    int createLoan(int userId, const Loan& loan) {
        sqlite3_stmt* stmt = nullptr;
        const char* sql = R"(
            INSERT INTO Loans (user_id, loan_type, original_amount, current_balance, interest_rate, term_months, is_active)
            VALUES (?, ?, ?, ?, ?, ?, ?);
        )";

        int rc = sqlite3_prepare_v2(db_, sql, -1, &stmt, 0);
        checkError(rc, "Failed to prepare create loan");

        sqlite3_bind_int(stmt, 1, userId);
        sqlite3_bind_int(stmt, 2, static_cast<int>(loan.getLoanType()));
        sqlite3_bind_double(stmt, 3, loan.getAmount());
        sqlite3_bind_double(stmt, 4, loan.getBalance());
        sqlite3_bind_double(stmt, 5, loan.getInterestRate());
        sqlite3_bind_int(stmt, 6, loan.getTermMonths());
        sqlite3_bind_int(stmt, 7, loan.getIsActive());

        rc = sqlite3_step(stmt);
        if (rc != SQLITE_DONE) {
            sqlite3_finalize(stmt);
            throw runtime_error("Failed to create loan");
        }

        sqlite3_finalize(stmt);
        return static_cast<int>(sqlite3_last_insert_rowid(db_));
    }

    void updateLoan(const Loan& loan) {
        sqlite3_stmt* stmt = nullptr;
        const char* sql = "UPDATE Loans SET current_balance = ?, is_active = ? WHERE id = ?;";

        int rc = sqlite3_prepare_v2(db_, sql, -1, &stmt, 0);
        checkError(rc, "Failed to prepare update loan");

        sqlite3_bind_double(stmt, 1, loan.getBalance());
        sqlite3_bind_int(stmt, 2, loan.getIsActive());
        sqlite3_bind_int(stmt, 3, loan.getLoanID());

        rc = sqlite3_step(stmt);
        if (rc != SQLITE_DONE) {
            sqlite3_finalize(stmt);
            throw runtime_error("Failed to update loan");
        }
        sqlite3_finalize(stmt);
    }

    vector<Loan> getLoans(int userId) {
        vector<Loan> loans;
        sqlite3_stmt* stmt = nullptr;
        const char* sql = "SELECT * FROM Loans WHERE user_id = ?;";

        if (sqlite3_prepare_v2(db_, sql, -1, &stmt, 0) != SQLITE_OK) {
            throw runtime_error("Failed to prepare get loans statement");
        }

        sqlite3_bind_int(stmt, 1, userId);

        while (sqlite3_step(stmt) == SQLITE_ROW) {
            loans.emplace_back(
                sqlite3_column_int(stmt, 0), // id
                static_cast<LoanType>(sqlite3_column_int(stmt, 2)), // loan_type
                sqlite3_column_double(stmt, 3), // original_amount
                sqlite3_column_double(stmt, 4), // current_balance
                sqlite3_column_int(stmt, 6), // term_months
                static_cast<bool>(sqlite3_column_int(stmt, 7)) // is_active
            );
        }
        sqlite3_finalize(stmt);
        return loans;
    }

    // get user count
    int getUserCount() {
        sqlite3_stmt* stmt = nullptr;
        const char* sql = "SELECT COUNT(*) FROM Users;";

        if (sqlite3_prepare_v2(db_, sql, -1, &stmt, 0) != SQLITE_OK) {
            sqlite3_finalize(stmt);
            throw runtime_error("Failed to prepare user count statement");
        }

        int count = 0;
        if (sqlite3_step(stmt) == SQLITE_ROW) {
            count = sqlite3_column_int(stmt, 0);
        }

        sqlite3_finalize(stmt);
        return count;
    }

    // --- Savings Goal Management ---

    int createSavingsGoal(int userId, const SavingsGoal& goal) {
        sqlite3_stmt* stmt = nullptr;
        const char* sql = R"(
            INSERT INTO SavingsGoals (user_id, goal_name, target_amount, saved_amount, is_completed)
            VALUES (?, ?, ?, ?, ?);
        )";

        int rc = sqlite3_prepare_v2(db_, sql, -1, &stmt, 0);
        checkError(rc, "Failed to prepare create savings goal");

        sqlite3_bind_int(stmt, 1, userId);
        sqlite3_bind_text(stmt, 2, goal.getName().c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_double(stmt, 3, goal.getTarget());
        sqlite3_bind_double(stmt, 4, goal.getSaved());
        sqlite3_bind_int(stmt, 5, goal.isCompleted());

        rc = sqlite3_step(stmt);
        if (rc != SQLITE_DONE) {
            sqlite3_finalize(stmt);
            throw runtime_error("Failed to create savings goal");
        }

        sqlite3_finalize(stmt);
        return static_cast<int>(sqlite3_last_insert_rowid(db_));
    }

    void updateSavingsGoal(const SavingsGoal& goal) {
        sqlite3_stmt* stmt = nullptr;
        const char* sql = "UPDATE SavingsGoals SET saved_amount = ?, is_completed = ? WHERE id = ?;";

        int rc = sqlite3_prepare_v2(db_, sql, -1, &stmt, 0);
        checkError(rc, "Failed to prepare update savings goal");

        sqlite3_bind_double(stmt, 1, goal.getSaved());
        sqlite3_bind_int(stmt, 2, goal.isCompleted());
        sqlite3_bind_int(stmt, 3, goal.getGoalID());

        rc = sqlite3_step(stmt);
        if (rc != SQLITE_DONE) {
            sqlite3_finalize(stmt);
            throw runtime_error("Failed to update savings goal");
        }
        sqlite3_finalize(stmt);
    }

    vector<SavingsGoal> getSavingsGoals(int userId) {
        vector<SavingsGoal> goals;
        sqlite3_stmt* stmt = nullptr;
        const char* sql = "SELECT * FROM SavingsGoals WHERE user_id = ?;";

        if (sqlite3_prepare_v2(db_, sql, -1, &stmt, 0) != SQLITE_OK) {
            throw runtime_error("Failed to prepare get savings goals");
        }

        sqlite3_bind_int(stmt, 1, userId);

        while (sqlite3_step(stmt) == SQLITE_ROW) {
            goals.emplace_back(
                sqlite3_column_int(stmt, 0), // id
                (const char*)sqlite3_column_text(stmt, 2), // goal_name
                sqlite3_column_double(stmt, 3), // target_amount
                sqlite3_column_double(stmt, 4), // saved_amount
                static_cast<bool>(sqlite3_column_int(stmt, 5)) // is_completed
            );
        }
        sqlite3_finalize(stmt);
        return goals;
    }

    // --- Transaction Management ---

    void createTransaction(int userId, const string& type, double amount, const string& date) {
        sqlite3_stmt* stmt = nullptr;
        const char* sql = "INSERT INTO Transactions (user_id, type, amount, date) VALUES (?, ?, ?, ?);";

        int rc = sqlite3_prepare_v2(db_, sql, -1, &stmt, 0);
        checkError(rc, "Failed to prepare create transaction");

        sqlite3_bind_int(stmt, 1, userId);
        sqlite3_bind_text(stmt, 2, type.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_double(stmt, 3, amount);
        sqlite3_bind_text(stmt, 4, date.c_str(), -1, SQLITE_TRANSIENT);

        rc = sqlite3_step(stmt);
        if (rc != SQLITE_DONE) {
            sqlite3_finalize(stmt);
            throw runtime_error("Failed to create transaction");
        }
        sqlite3_finalize(stmt);
    }

    vector<Transaction> getTransactions(int userId) {
        vector<Transaction> history;
        sqlite3_stmt* stmt = nullptr;
        const char* sql = "SELECT type, amount, date FROM Transactions WHERE user_id = ? ORDER BY id ASC;";

        if (sqlite3_prepare_v2(db_, sql, -1, &stmt, 0) != SQLITE_OK) {
            throw runtime_error("Failed to prepare get transactions");
        }

        sqlite3_bind_int(stmt, 1, userId);

        while (sqlite3_step(stmt) == SQLITE_ROW) {
            history.push_back({
                (const char*)sqlite3_column_text(stmt, 0), // type
                sqlite3_column_double(stmt, 1), // amount
                (const char*)sqlite3_column_text(stmt, 2) // date
            });
        }
        sqlite3_finalize(stmt);
        return history;
    }

    // --- Database Transaction ---
    void beginTransaction() { exec("BEGIN TRANSACTION;"); }
    void commit() { exec("COMMIT;"); }
    void rollback() { exec("ROLLBACK;"); }
};

class BankAccount {
private:
    // --- User Data (Loaded from DB) ---
    int userId_;
    string username_, accountNumber_;
    string passwordHash_, passwordSalt_; // Stored as hex strings
    string gmail_, phoneNumber_, otpKey_; // OTP key is Base32

    // Balance is stored as an encrypted vector of bytes
    vector<unsigned char> encryptedBalance_;

    double dailyLimit_, withdrawnToday_;
    string lastWithdrawalDate_;

    // --- Sub-data (Loaded from DB) ---
    vector<Loan> loans_;
    vector<SavingsGoal> savingsGoals_;
    vector<Transaction> transactionHistory_;

    // --- Session Objects ---
    DatabaseManager& db_; // Reference to the database

    // Gets the current formatted date and time as a string.
    string getCurrentDateTime() const {
        time_t now = time(nullptr);
        string dt = ctime(&now);
        dt.pop_back(); // Remove the trailing newline
        return dt;
    }

    // Gets the current date in YYYY-MM-DD format
    string getTodayDate() const {
        auto t = time(nullptr);
        auto tm = *localtime(&t); // Using localtime for "today"
        stringstream ss;
        ss << put_time(&tm, "%Y-%m-%d");
        return ss.str();
    }


    // --- ENCRYPTION HELPER FUNCTIONS ---

    // Decrypts the stored balance.
    double getDecryptedBalance(Encryption& encryptor) {
        try {
            vector<unsigned char> decryptedBytes = encryptor.decryptByte(encryptedBalance_);
            if (decryptedBytes.size() != sizeof(double)) {
                // This should not happen if encryption is correct
                throw runtime_error("Decrypted data size mismatch.");
            }
            double balance;
            memcpy(&balance, decryptedBytes.data(), sizeof(double));
            return balance;
        } catch (const exception& e) {
            cerr << "CRITICAL: FAILED TO DECRYPT BALANCE for user " << username_ << ". Error: " << e.what() << endl;
            // Return 0 or handle as a critical security fault
            return 0.0;
        }
    }

    // Encrypts and saves the new balance (in memory).
    void setEncryptedBalance(double newBalance, Encryption& encryptor) {
        try {
            encryptedBalance_ = encryptor.encryptByte(
                reinterpret_cast<const unsigned char*>(&newBalance),
                sizeof(newBalance)
            );
        } catch (const exception& e) {
            cerr << "CRITICAL: FAILED TO ENCRYPT BALANCE for user " << username_ << ". Error: " << e.what() << endl;
            // This is a critical state, may need to lock account
        }
    }

public:
    // Constructor updated to take UserData from DB
    BankAccount(const UserData& data, DatabaseManager& db)
        : userId_(data.id),
          username_(data.username),
          accountNumber_(data.accountNumber),
          passwordHash_(data.passwordHash),
          passwordSalt_(data.passwordSalt),
          gmail_(data.gmail),
          phoneNumber_(data.phoneNumber),
          otpKey_(data.otpKey),
          encryptedBalance_(data.encryptedBalance),
          dailyLimit_(40000),
          withdrawnToday_(data.dailyWithdrawn),
          lastWithdrawalDate_(data.lastWithdrawalDate),
          db_(db) {

        // Now load associated data
        loadData();
    }

    // Loads Loans, SavingsGoals, and Transactions from the DB
    void loadData() {
        try {
            loans_ = db_.getLoans(userId_);
            savingsGoals_ = db_.getSavingsGoals(userId_);
            transactionHistory_ = db_.getTransactions(userId_);
        } catch (const exception& e) {
            cerr << "Failed to load account sub-data for user " << username_ << ": " << e.what() << endl;
        }
    }

    // --- Getters ---
    int getUserId() const { return userId_; }
    string getUsername() const { return username_; }
    string getAccountNumber() const { return accountNumber_; }
    string getPasswordHash() const { return passwordHash_; }
    string getPasswordSalt() const { return passwordSalt_; }
    string getGmail() const { return gmail_; }
    string getPhoneNumber() const { return phoneNumber_; }
    string getOtpKey() const { return otpKey_; }
    int getLoanCount() const { return loans_.size(); }
    const vector<unsigned char>& getEncryptedBalance() const { return encryptedBalance_; }


    // --- Setters ---
    // These now need to persist to the DB
    void setPasswordAndSalt(const string& h, const string& s, const vector<unsigned char>& b) {
        passwordHash_ = h;
        passwordSalt_ = s;
        encryptedBalance_ = b; // Update in-memory balance too
        // Persist change
        db_.updateUserPasswordAndBalance(userId_, passwordHash_, passwordSalt_, encryptedBalance_);
    }

    // --- Balance-related methods now require an Encryption object ---

    // Gets the balance (requires decryption).
    double getBalance(Encryption& encryptor) {
        return getDecryptedBalance(encryptor);
    }

    // Deposits money into the main account balance.
    void deposit(double amt, Encryption& encryptor) {
        if (amt <= 0) {
            cout << "Deposit amount must be positive.\n";
            return;
        }

        // Decrypt, update, re-encrypt
        double currentBalance = getDecryptedBalance(encryptor);
        double newBalance = currentBalance + amt;
        setEncryptedBalance(newBalance, encryptor); // Updates in-memory encryptedBalance_

        // --- Persist to DB ---
        db_.updateUserBalance(userId_, encryptedBalance_);
        string dt = getCurrentDateTime();
        db_.createTransaction(userId_, "Deposit", amt, dt);
        // --- End DB ---

        transactionHistory_.push_back({"Deposit", amt, dt});
        cout << "Successfully deposited PHP " << fixed << setprecision(2) << amt << "\n"
             << "New Balance: PHP " << newBalance << "\n";
    }

    // Withdraws money from the main account balance.
    bool withdraw(double amt, Encryption& encryptor) {
        // FIX: Reset daily withdrawal limit if date changed
        string today = getTodayDate();
        if (lastWithdrawalDate_ != today) {
            cout << "New day detected. Resetting daily withdrawal limit.\n";
            withdrawnToday_ = 0.0;
            lastWithdrawalDate_ = today;
        }


        // Decrypt balance
        double currentBalance = getDecryptedBalance(encryptor);

        if (amt < 500) { cout << "Minimum withdrawal is PHP 500.\n"; return false; }
        if (amt > 20000) { cout << "Maximum single withdrawal is PHP 20,000.\n"; return false; }
        if (amt > currentBalance) { cout << "Insufficient funds.\n"; return false; }

        // Check against daily limit
        double remaining_limit = dailyLimit_ - withdrawnToday_;
        if (amt > remaining_limit) {
            cout << "Daily withdrawal limit exceeded. You can only withdraw PHP "
                 << fixed << setprecision(2) << remaining_limit << " more today.\n";
            return false;
        }

        // Update, re-encrypt
        double newBalance = currentBalance - amt;
        setEncryptedBalance(newBalance, encryptor);
        withdrawnToday_ += amt;

        // --- Persist to DB ---
        db_.updateUserBalance(userId_, encryptedBalance_);
        db_.updateUserWithdrawalStatus(userId_, withdrawnToday_, lastWithdrawalDate_);
        string dt = getCurrentDateTime();
        db_.createTransaction(userId_, "Withdrawal", amt, dt);
        // --- End DB ---

        transactionHistory_.push_back({"Withdrawal", amt, dt});
        cout << "\nSuccessfully withdrew PHP " << fixed << setprecision(2) << amt << "\n"
             << "Remaining Balance: PHP " << fixed << setprecision(2) << newBalance << "\n";
        return true;
    }

    // --- Special method for external balance update (used by transfer) ---
    void externalBalanceUpdate(double newBalance, Encryption& encryptor, const string& transType, double transAmt, const string& transDate) {
        // Re-encrypt
        setEncryptedBalance(newBalance, encryptor);

        // Persist
        db_.updateUserBalance(userId_, encryptedBalance_);
        db_.createTransaction(userId_, transType, transAmt, transDate);

        // Update in-memory history
        transactionHistory_.push_back({transType, transAmt, transDate});
    }

    // Transfers money to another BankAccount.
    // NOTE: The receiver object 'rec' is temporary and loaded just for this transaction.
    bool transfer(unique_ptr<BankAccount>& rec, double amt, Encryption& senderEncryptor) {
        // Decrypt sender's balance
        double senderBalance = getDecryptedBalance(senderEncryptor);

        if (amt <= 0) { cout << "Transfer amount must be positive.\n"; return false; }
        if (amt > senderBalance) { cout << "Insufficient funds for transfer.\n"; return false; }

        // --- Receiver Verification ---
        cout << "\n--- Receiver Verification (SIMULATION) ---\n"
             << "To complete the transfer, the *receiver's* password must be entered.\n"
             << "This is a simulation of the server-side ledger decryption.\n"
             << "Enter password for " << rec->getUsername() << ": ";
        string rec_pass;
        cin >> rec_pass;
        clearInput();

        passwordHasher recHasher;
        unsigned char recSalt[crypto_pwhash_SALTBYTES];
        try {
            fromHexString(rec->getPasswordSalt(), recSalt, crypto_pwhash_SALTBYTES);
            recHasher.regenerateKeyFromPassword(rec_pass, recSalt);
            // Verify password
            if (toHexString(recHasher.getKey(), crypto_secretbox_KEYBYTES) != rec->getPasswordHash()) {
                cout << "Invalid receiver password. Transfer cancelled.\n";
                return false;
            }
        } catch (...) {
            cout << "Invalid receiver password. Transfer cancelled.\n";
            return false;
        }

        // --- Keys are verified, proceed with transaction ---
        Encryption recEncryptor;
        recEncryptor.setKeyFromPasswordHasher(recHasher);

        // Get receiver's current balance
        double recBalance = rec->getBalance(recEncryptor); // Decrypts receiver's balance

        // Perform the transfer
        double newSenderBalance = senderBalance - amt;
        double newRecBalance = recBalance + amt;

        string dt = getCurrentDateTime();

        // Use a database transaction for atomicity
        try {
            db_.beginTransaction();

            // --- Update Sender ---
            setEncryptedBalance(newSenderBalance, senderEncryptor); // Update self in-memory
            db_.updateUserBalance(userId_, encryptedBalance_); // Persist self
            db_.createTransaction(userId_, "Transfer to " + rec->username_, amt, dt);
            transactionHistory_.push_back({"Transfer to " + rec->username_, amt, dt}); // Update self history

            // --- Update Receiver ---
            // Use the special method on the temporary receiver object
            rec->externalBalanceUpdate(newRecBalance, recEncryptor, "Transfer from " + username_, amt, dt);

            db_.commit();
        } catch (const exception& e) {
            db_.rollback();
            cerr << "CRITICAL: Transfer failed and was rolled back. Error: " << e.what() << endl;
            // Manually revert sender's in-memory balance
            setEncryptedBalance(senderBalance, senderEncryptor);
            transactionHistory_.pop_back();
            return false;
        }

        cout << "Transfer successful!\n"
             << "Sent PHP " << fixed << setprecision(2) << amt << " to " << rec->username_ << "\n"
             << "Your new balance: PHP " << fixed << setprecision(2) << newSenderBalance << "\n";
        return true;
    }

    void applyForLoan(LoanType t, double amt, int term, Encryption& encryptor) {
        Loan newLoan(t, amt, term);

        // --- Persist to DB ---
        int newLoanId = db_.createLoan(userId_, newLoan);
        newLoan.setLoanID(newLoanId); // Set the ID from the DB
        // --- End DB ---

        loans_.push_back(newLoan); // Add to in-memory list

        // Deposit the loan principal into the user's account
        deposit(amt, encryptor);

        cout << "\n************************\n"
             << "   LOAN APPROVED! (ID: " << newLoanId << ")\n"
             << "************************\n"
             << "PHP " << fixed << setprecision(2) << amt << " has been deposited into your account.\n";
    }

    void makePaymentOnLoan(int idx, double amt, Encryption& encryptor) {
        if (idx < 0 || idx >= loans_.size()) { cout << "Invalid loan selection.\n"; return; }

        double currentBalance = getDecryptedBalance(encryptor);

        if (amt > currentBalance) { cout << "Insufficient balance to make this payment.\n"; return; }
        if (amt <= 0) { cout << "Payment must be positive.\n"; return; }
        if (!loans_[idx].getIsActive()) { cout << "This loan is already fully paid.\n"; return; }


        // FIX: Capture old state for rollback
        double oldLoanBalance = loans_[idx].getBalance();
        bool oldLoanActive = loans_[idx].getIsActive();

        double overpayment = loans_[idx].makePayment(amt); // Mutates loans_[idx]

        // Update balance and re-encrypt
        double newBalance = (currentBalance - amt) + overpayment; // Add back any refund
        setEncryptedBalance(newBalance, encryptor); // Mutates encryptedBalance_

        string dt = getCurrentDateTime();

        // --- Persist to DB ---
        db_.beginTransaction();
        try {
            db_.updateUserBalance(userId_, encryptedBalance_);
            db_.updateLoan(loans_[idx]); // Persist loan changes
            db_.createTransaction(userId_, "Loan Payment (ID: " + to_string(loans_[idx].getLoanID()) + ")",
                                 amt - overpayment, dt);
            db_.commit();
        } catch (const exception& e) {
            db_.rollback();
            // Revert in-memory changes
            setEncryptedBalance(currentBalance, encryptor);
            loans_[idx].revertPayment(oldLoanBalance, oldLoanActive);

            cerr << "CRITICAL: Loan payment failed and was rolled back: " << e.what() << endl;
            cout << "Your account balance and loan status have not been changed.\n";
            return;
        }
        // --- End DB ---

        if (overpayment > 0) {
            cout << "Overpayment refunded. New Balance: PHP " << fixed << setprecision(2) << newBalance << "\n";
        }

        transactionHistory_.push_back({"Loan Payment (ID: " + to_string(loans_[idx].getLoanID()) + ")",
                                     amt - overpayment, dt});
    }

    void displayLoans() const {
        if (loans_.empty()) {
            cout << "You have no active or previous loans.\n";
            return;
        }
        for (size_t i = 0; i < loans_.size(); ++i) {
            cout << "\n--- Loan " << (i + 1) << " ---\n";
            loans_[i].displayLoanDetails();
        }
    }

    void displayRepaymentSchedules() const {
        if (loans_.empty()) { cout << "You have no loans.\n"; return; }
        for (const auto& l : loans_) {
            l.displayRepaymentSchedule();
            cout << "============================\n";
        }
    }

    void createSavingsGoal(const string& name, double target) {
        SavingsGoal newGoal(name, target);

        // --- Persist to DB ---
        int newGoalId = db_.createSavingsGoal(userId_, newGoal);
        newGoal.setGoalID(newGoalId);
        // --- End DB ---

        savingsGoals_.push_back(newGoal); // Add to in-memory list
        cout << "Savings goal '" << name << "' created! (ID: " << newGoalId << ")\n";
    }

    void depositToSavingsGoal(size_t idx, double amt, Encryption& encryptor) {
        if (idx >= savingsGoals_.size()) { cout << "Invalid savings goal selection.\n"; return; }

        double currentBalance = getDecryptedBalance(encryptor);

        if (amt > currentBalance) { cout << "Insufficient balance for this deposit.\n"; return; }
        if (amt <= 0) { cout << "Deposit must be positive.\n"; return; }

        // FIX: Capture old state for rollback
        double oldSavedAmount = savingsGoals_[idx].getSaved();
        bool oldCompleted = savingsGoals_[idx].isCompleted();

        double excess = 0;

        // Mutates savingsGoals_[idx]
        if (savingsGoals_[idx].deposit(amt, excess)) {
            // Update balance and re-encrypt
            double newBalance = (currentBalance - amt) + excess; // Add back any refund
            setEncryptedBalance(newBalance, encryptor); // Mutates encryptedBalance_

            string dt = getCurrentDateTime();

            // --- Persist to DB ---
            db_.beginTransaction();
            try {
                db_.updateUserBalance(userId_, encryptedBalance_);
                db_.updateSavingsGoal(savingsGoals_[idx]);
                db_.createTransaction(userId_, "Savings Goal: " + savingsGoals_[idx].getName(),
                                     amt - excess, dt);
                db_.commit();
            } catch (const exception& e) {
                db_.rollback();
                // Revert in-memory changes
                setEncryptedBalance(currentBalance, encryptor);
                savingsGoals_[idx].revertDeposit(oldSavedAmount, oldCompleted);

                cerr << "CRITICAL: Savings deposit failed and was rolled back: " << e.what() << endl;
                cout << "Your account balance and goal status have not been changed.\n";
                return;
            }
            // --- End DB ---

            transactionHistory_.push_back({"Savings Goal: " + savingsGoals_[idx].getName(),
                                         amt - excess, dt});
        } else {
            // Deposit failed (e.g., goal already completed)
            cout << "Deposit failed. Amount not withdrawn.\n";
        }
    }

    void displaySavingsGoals() const {
        if (savingsGoals_.empty()) { cout << "You have not set up any savings goals.\n"; return; }
        cout << "\n*** Your Savings Progress ***\n"
             << "---------------------------\n";
        for (const auto& g : savingsGoals_) {
            g.viewProgress();
        }
    }

    void listSavingsGoals() const {
        if (savingsGoals_.empty()) {
            cout << "You have no savings goals.\n";
            return;
        }
        cout << "Please select a goal:\n";
        for (size_t i = 0; i < savingsGoals_.size(); ++i) {
            cout << (i + 1) << ". " << savingsGoals_[i].getName() << " (PHP "
                 << fixed << setprecision(2) << savingsGoals_[i].getSaved()
                 << " / PHP " << savingsGoals_[i].getTarget() << ")\n";
        }
    }

    void displayTransactionHistory() const {
        cout << "\n==============================\n"
             << "   BONIFACIO BANKING SYSTEM   \n"
             << "==============================\n"
             << "      TRANSACTION HISTORY     \n"
             << "Account: " << accountNumber_ << "\n"
             << "As of: " << getCurrentDateTime() << "\n"
             << "------------------------------\n";

        if (transactionHistory_.empty()) {
            cout << "No transactions found.\n";
        } else {
            for (size_t i = 0; i < transactionHistory_.size(); ++i) {
                const auto& t = transactionHistory_[i];
                cout << "Transaction #" << (i + 1) << "\n"
                     << "  Type: " << t.type << "\n"
                     << "  Amount: PHP " << fixed << setprecision(2) << t.amount << "\n"
                     << "  Date: " << t.date << "\n"
                     << "------------------------------\n";
            }
            cout << "Total Transactions: " << transactionHistory_.size() << "\n";
        }
        cout << "==============================\n\n";
    }

    // Displays a summary of the account status.
    void displayAccountSummary(Encryption& encryptor) {
        // Decrypt balance just for display
        double currentBalance = getDecryptedBalance(encryptor);

        cout << "\n==============================\n"
             << "   BONIFACIO BANKING SYSTEM   \n"
             << "==============================\n"
             << "Welcome, " << username_ << "!\n"
             << "Account Number: " << accountNumber_ << "\n"
             "------------------------------\n"
             << "Current Balance: PHP " << fixed << setprecision(2) << currentBalance << "\n"
             << "As of: " << getCurrentDateTime() << "\n"
             "------------------------------\n"
             << "Active Loans: " << loans_.size() << "\n"
             << "Active Savings Goals: " << savingsGoals_.size() << "\n"
             << "==============================\n\n";
    }

    // Method to re-encrypt the balance with a new key
    // Used during password reset
    bool reEncryptBalance(Encryption& oldEncryptor, Encryption& newEncryptor) {
        try {
            // 1. Decrypt with old key
            double plaintextBalance = getDecryptedBalance(oldEncryptor);
            // 2. Re-encrypt with new key (updates in-memory balance)
            setEncryptedBalance(plaintextBalance, newEncryptor);
            return true;
        } catch (const exception& e) {
            // This will fail if the old key is wrong
            cerr << "CRITICAL: FAILED TO RE-ENCRYPT BALANCE. Error: " << e.what() << endl;
            return false;
        }
    }
};


// =================================================================
// == MODIFIED: BankingSystem Class
// =================================================================
// Manages all BankAccount objects and high-level operations.
// Now interacts with the DatabaseManager.
class BankingSystem {
private:
    // No longer holds accounts in memory
    // vector<BankAccount> accounts;

    unique_ptr<DatabaseManager> db_;

    // Validates a password: 8-20 chars, 1 uppercase, 1 lowercase, 1 digit.
    static bool isPasswordValid(const string& p) {
        // Regex: (?=.*[a-z])(?=.*[A-Z])(?=.*\d).{8,20}
        regex pat("^(?=.*[a-z])(?=.*[A-Z])(?=.*\\d).{8,20}$");
        return regex_match(p, pat);
    }

public:
    // Constructor initializes the database
    BankingSystem(const char* dbName) {
        try {
            db_ = make_unique<DatabaseManager>(dbName);
            db_->initSchema();
        } catch (const exception& e) {
            cerr << "CRITICAL DATABASE ERROR: " << e.what() << endl;
            exit(1); // Cannot run without a database
        }
    }


    // Registers a new user account.
    void registerAccount(string& u, string& p, string& g, string& ph) {
        // --- Validation ---
        if (db_->findUserByUsername(u)) { cout << "This username is already taken.\n"; return; }
        if (db_->findUserGmailOrPhone(g, ph)) { cout << "This Gmail or Phone is already in use.\n"; return; }

        regex gp("^[a-zA-Z0-9._]+@gmail\\.com$", regex_constants::icase);
        regex pp("^09[0-9]{9}$"); // Philippine phone format

        bool pok = isPasswordValid(p), gok = regex_match(g, gp), phok = regex_match(ph, pp);

        if (!pok || !gok || !phok) {
            cout << "\nRegistration failed. Please fix the following:\n";
            if (!pok) cout << " - Password must be 8-20 chars, with 1 uppercase, 1 lowercase, and 1 digit.\n";
            if (!gok) cout << " - Invalid Gmail. Must be a @gmail.com address.\n";
            if (!phok) cout << " - Invalid phone. Must be in 09XXXXXXXXX format.\n";
            return;
        }

        try {
            // Generate a 52-character Base32 secret key
            char kb[53];
            generate_b32_secret(kb, 53);
            kb[52] = '\0';
            string uk = kb;

            // --- Encrypt initial balance ---
            // 1. Hash the password to get the key
            passwordHasher initialHasher;
            initialHasher.generateKeyFromPassword(p);

            // 2. Encrypt the initial 10k bonus
            Encryption e_temp;
            e_temp.setKeyFromPasswordHasher(initialHasher);
            double initialBalance = 10000.0;
            auto encryptedBalance = e_temp.encryptByte(
                reinterpret_cast<const unsigned char*>(&initialBalance),
                sizeof(initialBalance)
            );

            // 3. Get the hex hash and salt for storage
            string phash = toHexString(initialHasher.getKey(), crypto_secretbox_KEYBYTES);
            string psalt = toHexString(initialHasher.getSalt(), crypto_pwhash_SALTBYTES);

            // FIX: Generate sequential account number
            int userCount = db_->getUserCount();
            string an = "ACC" + to_string(1001 + userCount); // Starts at ACC1001


            // 5. Create the user in the database
            db_->createUser(u, an, phash, psalt, g, ph, uk, encryptedBalance);


            cout << "\n==============================\n"
                 << "   REGISTRATION SUCCESSFUL!   \n"
                 << "==============================\n"
                 << "Your new Account Number: " << an << "\n"
                 << "Starting Balance: PHP 10,000.00\n\n"
                 << "--- IMPORTANT: 2FA SETUP ---\n"
                 << "Please add this key to your authenticator app (e.g.,Authenticator):\n"
                 << "Your 2FA Key: " << uk << "\n"
                 << "==============================\n\n";

        } catch (const exception& e) {
            cout << "A critical error occurred during registration: " << e.what() << "\n";
        }
    }

    // Logs in a user, verifying password/2FA and creating a session object.
    // Returns the BankAccount and the active password hasher (session key).
    pair<unique_ptr<BankAccount>, passwordHasher> loginAccount(const string& u, const string& p) {
        // 1. Find user in database
        auto userDataOpt = db_->findUserByUsername(u);

        if (!userDataOpt) {
            cout << "Invalid username or password.\n";
            return {nullptr, passwordHasher()};
        }

        UserData userData = *userDataOpt; // We have a user

        // 2. Verify username and password
        // --- Regenerate key from password and salt ---
        passwordHasher sessionHasher; // This will hold the key for this session
        unsigned char salt[crypto_pwhash_SALTBYTES];
        try {
            fromHexString(userData.passwordSalt, salt, crypto_pwhash_SALTBYTES);
            sessionHasher.regenerateKeyFromPassword(p, salt);
        } catch (const exception& e) {
            cerr << "Login error during key regeneration: " << e.what() << endl;
            cout << "Invalid username or password.\n";
            return {nullptr, passwordHasher()};
        }

        // Now verify the regenerated key against the stored hash
        if (toHexString(sessionHasher.getKey(), crypto_secretbox_KEYBYTES) != userData.passwordHash) {
            cout << "Invalid username or password.\n";
            return {nullptr, passwordHasher()};
        }

        cout << "\nPassword verified!\n"
             << "--- TWO-FACTOR AUTHENTICATION ---\n"
             << "Enter the 6-digit code from your authenticator app:\n";

        string c;
        // 3. Verify 2FA (give 3 attempts)
        for (int i = 0; i < 3; ++i) {
            cout << "Code: ";
            cin >> c;
            clearInput();

            if (c.length() != 6) {
                cout << "Invalid code. Must be 6 digits.\n";
                continue;
            }

            if (verifyOTP(userData.otpKey, c)) {
                // Success! Create the session BankAccount object
                cout << "\n==============================\n"
                     << "       LOGIN SUCCESSFUL!      \n"
                     << "==============================\n"
                     << "Welcome back, " << userData.username << "!\n"
                     << "==============================\n\n";

                auto account = make_unique<BankAccount>(userData, *db_);
                return {std::move(account), sessionHasher};
            }

            if (i < 2) cout << "Invalid code. " << (2 - i) << " attempts remaining.\n";
        }

        cout << "\nToo many failed 2FA attempts. Login denied.\n";
        return {nullptr, passwordHasher()};
    }

    // Resets a user's password after verifying identity.
    void forgotPassword() {
        string u, g;
        cout << "\n==============================\n"
             << "        CHANGE PASSWORD       \n"
             << "==============================\n"
             << "Please enter your username: ";
        cin >> u;
        clearInput();
        cout << "Please enter your registered Gmail: ";
        cin >> g;
        clearInput();

        // 1. Find account by username
        auto userDataOpt = db_->findUserByUsername(u);
        if (!userDataOpt || userDataOpt->gmail != g) {
            cout << "Account not found or Gmail does not match.\n";
            return;
        }

        UserData userData = *userDataOpt; // We have a user

        // 2. Verify identity using 2FA
        string otp;
        cout << "\nAccount found. Please enter your 6-digit 2FA code to verify: ";
        cin >> otp;
        clearInput();

        if (!verifyOTP(userData.otpKey, otp)) {
            cout << "Invalid 2FA code. Password reset failed.\n";
            return;
        }

        cout << "Identity verified!\n\n";

        // 3. Get and validate new password
        string np1, np2;
        cout << "Enter new password: ";
        cin >> np1;
        clearInput();
        cout << "Confirm new password: ";
        cin >> np2;
        clearInput();

        if (np1 != np2) { cout << "Passwords do not match.\n"; return; }
        if (!isPasswordValid(np1)) {
            cout << "New password is not valid (must be 8-20 chars, 1 upper, 1 lower, 1 digit).\n";
            return;
        }

        // 4. Hash and save the new password
        // *** CRITICAL STEP: Re-encrypt balance with new key ***
        try {
            // A) We need the OLD key to decrypt the balance.
            cout << "\n--- Security Step ---\n"
                 << "To re-encrypt your balance, please enter your OLD password one last time: ";
            string old_pass;
            cin >> old_pass;
            clearInput();

            passwordHasher oldHasher;
            unsigned char oldSalt[crypto_pwhash_SALTBYTES];
            fromHexString(userData.passwordSalt, oldSalt, crypto_pwhash_SALTBYTES);
            oldHasher.regenerateKeyFromPassword(old_pass, oldSalt);

            // Verify old password
            if (toHexString(oldHasher.getKey(), crypto_secretbox_KEYBYTES) != userData.passwordHash) {
                cout << "Invalid OLD password. Password reset failed.\n";
                return;
            }

            // B) Old password is correct. Generate NEW key.
            passwordHasher newHasher;
            newHasher.generateKeyFromPassword(np1); // Hash new pass to get new key/salt

            // C) Create encryptors for both keys
            Encryption oldEncryptor;
            oldEncryptor.setKeyFromPasswordHasher(oldHasher);
            Encryption newEncryptor;
            newEncryptor.setKeyFromPasswordHasher(newHasher);

            // D) Decrypt with old, re-encrypt with new
            vector<unsigned char> decryptedBytes = oldEncryptor.decryptByte(userData.encryptedBalance);
            double plaintextBalance;
            memcpy(&plaintextBalance, decryptedBytes.data(), sizeof(double));

            vector<unsigned char> newEncryptedBalance = newEncryptor.encryptByte(
                reinterpret_cast<const unsigned char*>(&plaintextBalance), sizeof(plaintextBalance));


            // E) Now that balance is re-encrypted, save the NEW hash, salt, and balance to DB
            string newHash = toHexString(newHasher.getKey(), crypto_secretbox_KEYBYTES);
            string newSalt = toHexString(newHasher.getSalt(), crypto_pwhash_SALTBYTES);

            db_->updateUserPasswordAndBalance(userData.id, newHash, newSalt, newEncryptedBalance);

            cout << "\n==============================\n"
                 << "    PASSWORD RESET SUCCESSFUL!  \n"
                 << "==============================\n"
                 << "Your password has been changed and your balance has been re-encrypted.\n\n";

        } catch (const exception& e) {
            cout << "An error occurred while resetting password: " << e.what() << "\n";
        }
    }

    // Finds and creates a temporary BankAccount object for the receiver
    unique_ptr<BankAccount> findAccountForTransfer(const string& n) {
        auto userDataOpt = db_->findUserByAccountNumber(n);
        if (userDataOpt) {
            // Create a temporary BankAccount object for the receiver
            return make_unique<BankAccount>(*userDataOpt, *db_);
        }
        return nullptr;
    }
};

// Main menu loop for a logged-in user.
// Now accepts the sessionHasher to create an encryptor.
void displayMainMenu(BankAccount* acc, BankingSystem& bank, passwordHasher& sessionHasher) {

    // Create one Encryption object for this entire session
    Encryption sessionEncryptor;
    try {
        sessionEncryptor.setKeyFromPasswordHasher(sessionHasher);
    } catch (const exception& e) {
        cerr << "CRITICAL: FAILED TO CREATE SESSION ENCRYPTOR. LOGGING OUT. " << e.what() << endl;
        return;
    }

    while (true) {
        cout << "\n==============================\n"
             << " BONIFACIO BANKING MAIN MENU \n"
             << "==============================\n"
             << "  1. Account Summary\n"
             << "  2. Deposit\n"
             << "  3. Withdraw\n"
             << "  4. Transfer Funds\n"
             << "  5. Loan Management\n"
             << "  6. Savings Goals\n"
             << "  7. Transaction History\n"
             << "  8. Logout\n"
             << "==============================\n"
             << "Enter your choice (1-8): ";

        int ch;
        cin >> ch;
        if (cin.fail()) {
            clearInput();
            cout << "Invalid input. Please enter a number.\n";
            continue;
        }
        clearInput();

        try { // Add a try-catch block for all crypto/DB operations
            switch (ch) {
                case 1:
                    acc->displayAccountSummary(sessionEncryptor);
                    break;
                case 2: {
                    double a;
                    cout << "Enter amount to deposit: PHP ";
                    cin >> a;
                    if (cin.fail()) { clearInput(); cout << "Invalid amount.\n"; break; }
                    clearInput();
                    acc->deposit(a, sessionEncryptor);
                    break;
                }
                case 3: {
                    double a;
                    cout << "Enter amount to withdraw: PHP ";
                    cin >> a;
                    if (cin.fail()) { clearInput(); cout << "Invalid amount.\n"; break; }
                    clearInput();
                    acc->withdraw(a, sessionEncryptor);
                    break;
                }
                case 4: {
                    string rn;
                    double a;
                    cout << "Enter recipient's Account Number (e.g., ACC1001): ";
                    cin >> rn;
                    clearInput();
                    cout << "Enter amount to transfer: PHP ";
                    cin >> a;
                    if (cin.fail()) { clearInput(); cout << "Invalid amount.\n"; break; }
                    clearInput();

                    cout << "\n--- Transfer Security Check ---\n"
                         << "Enter your 6-digit 2FA code to confirm: ";
                    string c;
                    cin >> c;
                    clearInput();

                    // Verify 2FA before allowing transfer
                    if (!verifyOTP(acc->getOtpKey(), c)) {
                        cout << "Invalid 2FA code. Transfer cancelled.\n";
                        break;
                    }

                    unique_ptr<BankAccount> r = bank.findAccountForTransfer(rn);
                    if (!r) {
                        cout << "Recipient account not found.\n";
                        break;
                    }
                    if (r->getAccountNumber() == acc->getAccountNumber()) {
                        cout << "You cannot transfer money to yourself.\n";
                        break;
                    }

                    acc->transfer(r, a, sessionEncryptor);
                    break;
                }
                case 5: { // Loan Management
                    cout << "\n--- Loan Management Menu ---\n"
                         << "  1. Apply for a New Loan\n"
                         << "  2. View My Loans\n"
                         << "  3. Make a Loan Payment\n"
                         << "  4. View Repayment Schedules\n"
                         << "  5. Back to Main Menu\n"
                         << "------------------------------\n"
                         << "Choice: ";
                    int lc;
                    cin >> lc;
                    if (cin.fail()) { clearInput(); cout << "Invalid choice.\n"; break; }
                    clearInput();

                    if (lc == 1) {
                        cout << "\n--- Apply for Loan ---\n"
                             << "  1. Personal Loan (5.0%, max 1M, 1-120 mos)\n"
                             << "  2. Car Loan (7.0%, max 10M, 1-360 mos)\n"
                             << "  3. Housing Loan (4.0%, max 10M, 1-360 mos)\n"
                             << "  4. Business Loan (6.0%, max 20M, 1-360 mos)\n"
                             << "Choice: ";
                        int tc;
                        cin >> tc;
                        if (cin.fail()) { clearInput(); cout << "Invalid choice.\n"; break; }
                        clearInput();

                        double amt, max_amt;
                        int term, max_term;
                        LoanType t;

                        switch (tc) {
                            case 1: t = PERSONAL; max_amt = 1000000; max_term = 120; break;
                            case 2: t = CAR; max_amt = 10000000; max_term = 360; break;
                            case 3: t = HOUSING; max_amt = 10000000; max_term = 360; break;
                            case 4: t = BUSINESS; max_amt = 20000000; max_term = 360; break;
                            default: cout << "Invalid loan type.\n"; continue;
                        }

                        cout << "Enter desired amount (max " << fixed << setprecision(0) << max_amt << "): PHP ";
                        cin >> amt;
                        if (cin.fail()) { clearInput(); cout << "Invalid amount.\n"; break; }
                        clearInput();
                        if (amt <= 0 || amt > max_amt) { cout << "Invalid amount.\n"; break; }

                        cout << "Enter term in months (1-" << max_term << "): ";
                        cin >> term;
                        if (cin.fail()) { clearInput(); cout << "Invalid term.\n"; break; }
                        clearInput();
                        if (term < 1 || term > max_term) { cout << "Invalid term.\n"; break; }

                        // This method now handles DB creation and deposit
                        acc->applyForLoan(t, amt, term, sessionEncryptor);

                    } else if (lc == 2) {
                        acc->displayLoans();
                    } else if (lc == 3) {
                        if (acc->getLoanCount() == 0) { cout << "You have no loans to pay.\n"; break; }
                        acc->displayLoans();
                        cout << "\nEnter Loan # (1-" << acc->getLoanCount() << ") to pay: ";
                        int li;
                        cin >> li;
                        if (cin.fail()) { clearInput(); cout << "Invalid selection.\n"; break; }
                        clearInput();
                        cout << "Enter payment amount: PHP ";
                        double p;
                        cin >> p;
                        if (cin.fail()) { clearInput(); cout << "Invalid amount.\n"; break; }
                        clearInput();
                        acc->makePaymentOnLoan(li - 1, p, sessionEncryptor); // Use 0-based index
                    } else if (lc == 4) {
                        acc->displayRepaymentSchedules();
                    }
                    break;
                }
                case 6: { // Savings Goals
                    cout << "\n--- Savings Goals Menu ---\n"
                         << "  1. Create a New Goal\n"
                         << "  2. Deposit to a Goal\n"
                         << "  3. View Goal Progress\n"
                         << "  4. Back to Main Menu\n"
                         << "----------------------------\n"
                         << "Choice: ";
                    int sc;
                    cin >> sc;
                    if (cin.fail()) { clearInput(); cout << "Invalid choice.\n"; break; }
                    clearInput();

                    if (sc == 1) {
                        string n;
                        double t;
                        cout << "Enter goal name (e.g., 'New Phone'): ";
                        getline(cin, n); // Use getline for names with spaces
                        cout << "Enter target amount: PHP ";
                        cin >> t;
                        if (cin.fail()) { clearInput(); cout << "Invalid amount.\n"; break; }
                        clearInput();
                        if (t <= 0) { cout << "Target must be positive.\n"; break; }
                        acc->createSavingsGoal(n, t);
                    } else if (sc == 2) {
                        acc->listSavingsGoals();
                        cout << "Enter Goal # to deposit into: ";
                        size_t gi;
                        cin >> gi;
                        if (cin.fail()) { clearInput(); cout << "Invalid selection.\n"; break; }
                        clearInput();
                        cout << "Enter amount to deposit: PHP ";
                        double a;
                        cin >> a;
                        if (cin.fail()) { clearInput(); cout << "Invalid amount.\n"; break; }
                        clearInput();
                        acc->depositToSavingsGoal(gi - 1, a, sessionEncryptor); // Use 0-based index
                    } else if (sc == 3) {
                        acc->displaySavingsGoals();
                    }
                    break;
                }
                case 7:
                    acc->displayTransactionHistory();
                    break;
                case 8:
                    cout << "\nLogging you out...\n"
                         << "Thank you for banking with Bonifacio Bank!\n\n";
                    // Clear the session key from memory by destroying the hasher
                    sessionHasher = passwordHasher(); // Reset to default
                    return; // Exit the main menu loop
                default:
                    cout << "Invalid choice. Please select from 1-8.\n";
            }
        } catch (const exception& e) {
            // Catch any crypto or DB failures
            cerr << "\n\nAn unexpected error occurred: " << e.what() << endl;
            cout << "For your security, you are being logged out." << endl;
            sessionHasher = passwordHasher(); // Clear key
            return; // Exit menu
        }
    }
}

// Main function - Entry point
int main() {
    // Initialize the libsodium library. This is mandatory.
    if (sodium_init() < 0) {
        cerr << "CRITICAL: Failed to initialize libsodium!\n";
        return 1;
    }

    // Initialize the BankingSystem with the database file
    BankingSystem bank("bonifacio.db");

    unique_ptr<BankAccount> loggedInAccount = nullptr; // Pointer to the logged-in account
    passwordHasher sessionHasher; // Holds the key for the current session

    while (true) {
        if (!loggedInAccount) {
            // --- Logged-Out Menu ---
            cout << "\n==============================\n"
                 << "   WELCOME TO BONIFACIO BANK  \n"
                 << "==============================\n"
                 << "  1. Register New Account\n"
                 << "  2. Login\n"
                 << "  3. Change Password\n"
                 << "  4. Exit\n"
                 << "==============================\n"
                 << "Enter your choice (1-4): ";
            int c;
            cin >> c;
            if (cin.fail()) {
                clearInput();
                cout << "Invalid input. Please enter a number.\n";
                continue;
            }
            clearInput();

            switch (c) {
                case 1: {
                    string u, p, g, ph;
                    cout << "\n--- New Account Registration ---\n"
                         << "Enter Username: ";
                    cin >> u;
                    cout << "Enter Password: ";
                    cin >> p;
                    cout << "Enter Gmail: ";
                    cin >> g;
                    cout << "Enter Phone (09xxxxxxxxx): ";
                    cin >> ph;
                    clearInput();
                    bank.registerAccount(u, p, g, ph);
                    break;
                }
                case 2: {
                    string u, p;
                    cout << "\n--- Secure Login ---\n"
                         << "Enter Username: ";
                    cin >> u;
                    cout << "Enter Password: ";
                    cin >> p;
                    clearInput();

                    // loginAccount now returns a pair
                    auto loginResult = bank.loginAccount(u, p);
                    loggedInAccount = std::move(loginResult.first); // Move ownership
                    sessionHasher = loginResult.second; // Store the session key
                    break;
                }
                case 3:
                    bank.forgotPassword();
                    break;
                case 4:
                    cout << "\nThank you for using Bonifacio Bank!\n"
                         << "Goodbye!\n";
                    return 0; // Exit the program
                default:
                    cout << "Invalid choice. Please select from 1-4.\n";
            }
        } else {
            // --- Logged-In State ---
            // Pass the account and the active session key to the menu
            displayMainMenu(loggedInAccount.get(), bank, sessionHasher);

            loggedInAccount.reset(); // Destroy the session object
            sessionHasher = passwordHasher(); // Clear the session key
        }
    }
    return 0;
}