#include <cctype>
#include <cmath>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <map>
#include <memory>
#include <set>
#include <sstream>
#include <string>
#include <vector>

using namespace std;

// ------------------------------------------------------------ basics
struct HLError {
    string msg;
    int line;
};

enum Kind { RES, SYM, ID, NUM, STR, END };

struct Token {
    Kind kind;
    string text;
    int line;
};

static string lower(string s) {
    for (char &c : s) c = (char)tolower((unsigned char)c);
    return s;
}

static const set<string> RESERVED = {"integer", "double", "output", "if"};

// Lexical
vector<Token> tokenize(const string &src) {
    vector<Token> toks;
    int line = 1;
    size_t i = 0, n = src.size();
    while (i < n) {
        char c = src[i];
        if (c == '\n') { line++; i++; }
        else if (isspace((unsigned char)c)) { i++; }
        else if (c == '"') {
            size_t j = i + 1;
            while (j < n && src[j] != '"' && src[j] != '\n') j++;
            if (j >= n || src[j] != '"') throw HLError{"Unterminated string", line};
            toks.push_back({STR, src.substr(i + 1, j - i - 1), line});
            i = j + 1;
        }
        else if (isdigit((unsigned char)c)) {
            size_t j = i;
            while (j < n && isdigit((unsigned char)src[j])) j++;
            if (j + 1 < n && src[j] == '.' && isdigit((unsigned char)src[j + 1])) {
                j++;
                while (j < n && isdigit((unsigned char)src[j])) j++;
            }
            toks.push_back({NUM, src.substr(i, j - i), line});
            i = j;
        }
        else if (isalpha((unsigned char)c) || c == '_') {
            size_t j = i;
            while (j < n && (isalnum((unsigned char)src[j]) || src[j] == '_')) j++;
            string w = src.substr(i, j - i);
            if (RESERVED.count(lower(w))) toks.push_back({RES, lower(w), line});
            else toks.push_back({ID, w, line});
            i = j;
        }
        else {
            string two = src.substr(i, 2);
            if (two == ":=" || two == "<<" || two == "==" || two == "!=") {
                toks.push_back({SYM, two, line});
                i += 2;
            } else if (string(":;=<>+-()").find(c) != string::npos) {
                toks.push_back({SYM, string(1, c), line});
                i++;
            } else {
                throw HLError{string("Invalid character '") + c + "'", line};
            }
        }
    }
    return toks;
}

// AST nodes
struct Value {
    bool isDouble = false;
    int i = 0;
    double d = 0;
    double num() const { return isDouble ? d : (double)i; }
};

struct Expr {
    enum T { NUMBER, VAR, BIN } type;
    Value val;         
    string name;       
    char op = '+';     
    shared_ptr<Expr> l, r;
};
using ExprP = shared_ptr<Expr>;

struct Stmt;
using StmtP = shared_ptr<Stmt>;

struct Stmt {
    enum T { DECL, ASSIGN, OUT, IF } type;
    string name;               
    bool declDouble = false;   
    ExprP expr;               
    bool isString = false;    
    string str;                
    string relop;             
    ExprP left, right;        
    StmtP body;               
};

// parser
class Parser {
public:
    explicit Parser(vector<Token> t) : toks(move(t)) {}
    map<string, bool> types;  // variable -> isDouble

    vector<StmtP> program() {
        vector<StmtP> out;
        while (peek().kind != END) out.push_back(statement());
        return out;
    }

private:
    vector<Token> toks;
    size_t pos = 0;

    Token peek(size_t ahead = 0) const {
        size_t k = pos + ahead;
        if (k < toks.size()) return toks[k];
        return {END, "", toks.empty() ? 1 : toks.back().line};
    }
    Token next() { Token t = peek(); pos++; return t; }

    Token expect(Kind k, const string &text = "") {
        Token t = peek();
        if (t.kind != k || (!text.empty() && t.text != text)) {
            string want = text.empty() ? "token" : text;
            string got = t.kind == END ? "end of file" : t.text;
            throw HLError{"Expected '" + want + "' but found '" + got + "'", t.line};
        }
        return next();
    }
    bool isSym(const Token &t, const string &s) const {
        return t.kind == SYM && t.text == s;
    }

    StmtP statement() {
        Token t = peek();
        if (t.kind == ID) {
            if (isSym(peek(1), ":")) return declaration();
            return assignment();
        }
        if (t.kind == RES && t.text == "output") return output();
        if (t.kind == RES && t.text == "if") return ifStmt();
        throw HLError{"Unexpected '" + t.text + "' at start of statement", t.line};
    }

    StmtP declaration() {
        Token id = expect(ID);
        expect(SYM, ":");
        Token ty = next();
        if (ty.kind != RES || (ty.text != "integer" && ty.text != "double"))
            throw HLError{"Expected data type 'integer' or 'double'", ty.line};
        expect(SYM, ";");
        if (types.count(id.text))
            throw HLError{"Variable '" + id.text + "' already declared", id.line};
        types[id.text] = (ty.text == "double");
        auto s = make_shared<Stmt>();
        s->type = Stmt::DECL; s->name = id.text; s->declDouble = (ty.text == "double");
        return s;
    }

    StmtP assignment() {
        Token id = expect(ID);
        if (!types.count(id.text))
            throw HLError{"Variable '" + id.text + "' not declared", id.line};
        Token op = next();
        if (!isSym(op, ":=") && !isSym(op, "="))
            throw HLError{"Expected ':=' but found '" + op.text + "'", op.line};
        bool isD;
        ExprP e = expr(isD);
        expect(SYM, ";");
        if (!types[id.text] && isD)
            throw HLError{"Cannot assign double value to integer '" + id.text + "'", id.line};
        auto s = make_shared<Stmt>();
        s->type = Stmt::ASSIGN; s->name = id.text; s->expr = e;
        return s;
    }

    StmtP output() {
        expect(RES, "output");
        expect(SYM, "<<");
        auto s = make_shared<Stmt>();
        s->type = Stmt::OUT;
        if (peek().kind == STR) {
            s->isString = true;
            s->str = next().text;
        } else {
            bool isD;
            s->expr = expr(isD);
        }
        expect(SYM, ";");
        return s;
    }

    StmtP ifStmt() {
        Token kw = expect(RES, "if");
        expect(SYM, "(");
        bool d1, d2;
        ExprP l = expr(d1);
        Token op = next();
        if (op.kind != SYM || (op.text != ">" && op.text != "<" &&
                               op.text != "==" && op.text != "!="))
            throw HLError{"Expected relational operator (> < == !=) but found '" + op.text + "'", op.line};
        ExprP r = expr(d2);
        expect(SYM, ")");
        StmtP body = statement();
        if (body->type == Stmt::DECL)
            throw HLError{"Declaration not allowed inside 'if'", kw.line};
        auto s = make_shared<Stmt>();
        s->type = Stmt::IF; s->relop = op.text; s->left = l; s->right = r; s->body = body;
        return s;
    }

  
    ExprP expr(bool &isD) {
        ExprP node = operand(isD);
        while (isSym(peek(), "+") || isSym(peek(), "-")) {
            char op = next().text[0];
            bool rd;
            ExprP right = operand(rd);
            auto b = make_shared<Expr>();
            b->type = Expr::BIN; b->op = op; b->l = node; b->r = right;
            node = b;
            if (rd) isD = true;
        }
        return node;
    }

    ExprP operand(bool &isD) {
        Token t = next();
        auto e = make_shared<Expr>();
        if (t.kind == NUM) {
            e->type = Expr::NUMBER;
            size_t dot = t.text.find('.');
            if (dot != string::npos) {
                if (t.text.size() - dot - 1 > 2)
                    throw HLError{"Precision of more than 2 decimals: " + t.text, t.line};
                e->val.isDouble = true; e->val.d = stod(t.text); isD = true;
            } else {
                e->val.i = stoi(t.text); isD = false;
            }
            return e;
        }
        if (t.kind == ID) {
            if (!types.count(t.text))
                throw HLError{"Variable '" + t.text + "' not declared", t.line};
            e->type = Expr::VAR; e->name = t.text; isD = types[t.text];
            return e;
        }
        string got = t.kind == END ? "end of file" : t.text;
        throw HLError{"Expected a value or variable but found '" + got + "'", t.line};
    }
};

//  executor
struct RuntimeErr { string msg; };

class Runner {
public:
    explicit Runner(map<string, bool> t) : types(move(t)) {}

    void run(const vector<StmtP> &prog) {
        for (auto &s : prog) exec(*s);
    }

private:
    map<string, bool> types;
    map<string, Value> vals;

    Value eval(const Expr &e) {
        if (e.type == Expr::NUMBER) return e.val;
        if (e.type == Expr::VAR) {
            auto it = vals.find(e.name);
            if (it == vals.end())
                throw RuntimeErr{"Variable '" + e.name + "' used before assignment"};
            return it->second;
        }
        Value a = eval(*e.l), b = eval(*e.r), r;
        if (a.isDouble || b.isDouble) {
            r.isDouble = true;
            r.d = e.op == '+' ? a.num() + b.num() : a.num() - b.num();
        } else {
            r.i = e.op == '+' ? a.i + b.i : a.i - b.i;
        }
        return r;
    }

    static void print(const Value &v) {
        if (v.isDouble) cout << fixed << setprecision(2) << v.d << "\n";
        else cout << v.i << "\n";
    }

    void exec(const Stmt &s) {
        switch (s.type) {
        case Stmt::DECL:
            break;
        case Stmt::ASSIGN: {
            Value v = eval(*s.expr), stored;
            if (types[s.name]) {
                stored.isDouble = true;
                stored.d = round(v.num() * 100.0) / 100.0;
            } else {
                stored.i = v.i;
            }
            vals[s.name] = stored;
            break;
        }
        case Stmt::OUT:
            if (s.isString) cout << s.str << "\n";
            else print(eval(*s.expr));
            break;
        case Stmt::IF: {
            double a = eval(*s.left).num(), b = eval(*s.right).num();
            bool ok = (s.relop == ">")  ? a > b :
                      (s.relop == "<")  ? a < b :
                      (s.relop == "==") ? a == b : a != b;
            if (ok) exec(*s.body);
            break;
        }
        }
    }
};

// main
int main(int argc, char *argv[]) {
    string src;

    if (argc >= 2) {
        // Mode 1: source file given on the command line
        ifstream in(argv[1]);
        if (!in) {
            cout << "Cannot open file: " << argv[1] << "\n";
            return 1;
        }
        stringstream buf;
        buf << in.rdbuf();
        src = buf.str();
    } else {
        // 
        cout << "HLInt - type your HL program below.\n";
        cout << "Type END on its own line when you are done.\n\n";
        string line;
        while (getline(cin, line)) {
            string t;
            for (char c : line)
                if (!isspace((unsigned char)c)) t += c;
            if (lower(t) == "end") break;
            src += line + "\n";
        }
        ofstream saved("INPUT.HL");  
        saved << src;
        cout << "\n";
    }

    // 
    {
        ofstream out("NOSPACES.TXT");
        for (char c : src)
            if (c != ' ' && c != '\t' && c != '\r') out << c;
        if (!src.empty() && src.back() != '\n') out << "\n";
    }

    //
    vector<Token> toks;
    bool lexOk = true;
    HLError lexErr{"", 0};
    try {
        toks = tokenize(src);
    } catch (HLError &e) {
        lexOk = false;
        lexErr = e;
    }
    {
        ofstream out("RES_SYM.TXT");
        if (lexOk) {
            for (auto &t : toks) {
                if (t.kind == RES) out << t.text << "\tRESERVED WORD\n";
                else if (t.kind == SYM) out << t.text << "\tSYMBOL\n";
                else if (t.kind == STR) out << "\"\tSYMBOL\n";
            }
        }
    }

    // check
    vector<StmtP> prog;
    Parser parser(toks);
    try {
        if (!lexOk) throw lexErr;
        prog = parser.program();
        
    } catch (HLError &e) {
        cout << "ERROR\n";
        cout << "  Line " << e.line << ": " << e.msg << "\n";
        return 0;
    }
    cout << "NO ERROR(S) FOUND\n";

    // Execute
    cout << "OUTPUT\n";
    try {
        Runner(parser.types).run(prog);
    } catch (RuntimeErr &e) {
        cout << "RUNTIME ERROR: " << e.msg << "\n";
    }
    return 0;
}
