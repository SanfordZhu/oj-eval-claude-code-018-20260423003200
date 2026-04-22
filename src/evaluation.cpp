/**
 * @file evaluation.cpp
 * @brief Expression evaluation implementation for the Scheme interpreter
 * @author luke36
 * 
 * This file implements evaluation methods for all expression types in the Scheme
 * interpreter. Functions are organized according to ExprType enumeration order
 * from Def.hpp for consistency and maintainability.
 */

#include "value.hpp"
#include "expr.hpp" 
#include "RE.hpp"
#include "syntax.hpp"
#include <cstring>
#include <vector>
#include <map>
#include <climits>

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

// Forward declaration
Value syntaxToValue(const Syntax &syntax);

Value Fixnum::eval(Assoc &e) { // evaluation of a fixnum
    return IntegerV(n);
}

Value RationalNum::eval(Assoc &e) { // evaluation of a rational number
    return RationalV(numerator, denominator);
}

Value StringExpr::eval(Assoc &e) { // evaluation of a string
    return StringV(s);
}

Value True::eval(Assoc &e) { // evaluation of #t
    return BooleanV(true);
}

Value False::eval(Assoc &e) { // evaluation of #f
    return BooleanV(false);
}

Value MakeVoid::eval(Assoc &e) { // (void)
    return VoidV();
}

Value Exit::eval(Assoc &e) { // (exit)
    return TerminateV();
}

Value Unary::eval(Assoc &e) { // evaluation of single-operator primitive
    return evalRator(rand->eval(e));
}

Value Binary::eval(Assoc &e) { // evaluation of two-operators primitive
    return evalRator(rand1->eval(e), rand2->eval(e));
}

Value Variadic::eval(Assoc &e) { // evaluation of multi-operator primitive
    // Evaluate all arguments
    std::vector<Value> args;
    for (const auto& expr : rands) {
        args.push_back(expr->eval(e));
    }
    return evalRator(args);
}

Value Var::eval(Assoc &e) { // evaluation of variable
    // TODO: TO identify the invalid variable
    // We request all valid variable just need to be a symbol,you should promise:
    //The first character of a variable name cannot be a digit or any character from the set: {.@}
    //If a string can be recognized as a number, it will be prioritized as a number. For example: 1, -1, +123, .123, +124., 1e-3
    //Variable names can overlap with primitives and reserve_words
    //Variable names can contain any non-whitespace characters except #, ', ", `, but the first character cannot be a digit
    //When a variable is not defined in the current scope, your interpreter should output RuntimeError

    Value matched_value = find(x, e);
    if (matched_value.get() == nullptr) {
        // Variable not found, check if it's a primitive
        if (primitives.count(x)) {
            // Return a primitive procedure
            // For now, just throw RuntimeError as we need to implement primitive procedures properly
            throw RuntimeError("Undefined variable: " + x);
        } else {
            throw RuntimeError("Undefined variable: " + x);
        }
    }
    return matched_value;
}

Value Plus::evalRator(const Value &rand1, const Value &rand2) { // +
    // Handle integer addition
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        return IntegerV(n1 + n2);
    }
    // Handle rational number addition
    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        int num = r1->numerator * r2->denominator + r2->numerator * r1->denominator;
        int den = r1->denominator * r2->denominator;
        return RationalV(num, den);
    }
    // Handle mixed integer and rational
    else if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        int num = n1 * r2->denominator + r2->numerator;
        int den = r2->denominator;
        return RationalV(num, den);
    }
    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        int num = r1->numerator + n2 * r1->denominator;
        int den = r1->denominator;
        return RationalV(num, den);
    }
    throw(RuntimeError("Wrong typename for addition"));
}

Value Minus::evalRator(const Value &rand1, const Value &rand2) { // -
    // Handle integer subtraction
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        return IntegerV(n1 - n2);
    }
    // Handle rational number subtraction
    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        int num = r1->numerator * r2->denominator - r2->numerator * r1->denominator;
        int den = r1->denominator * r2->denominator;
        return RationalV(num, den);
    }
    // Handle mixed integer and rational
    else if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        int num = n1 * r2->denominator - r2->numerator;
        int den = r2->denominator;
        return RationalV(num, den);
    }
    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        int num = r1->numerator - n2 * r1->denominator;
        int den = r1->denominator;
        return RationalV(num, den);
    }
    throw(RuntimeError("Wrong typename for subtraction"));
}

Value Mult::evalRator(const Value &rand1, const Value &rand2) { // *
    // Handle integer multiplication
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        return IntegerV(n1 * n2);
    }
    // Handle rational number multiplication
    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        int num = r1->numerator * r2->numerator;
        int den = r1->denominator * r2->denominator;
        return RationalV(num, den);
    }
    // Handle mixed integer and rational
    else if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        int num = n1 * r2->numerator;
        int den = r2->denominator;
        return RationalV(num, den);
    }
    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        int num = r1->numerator * n2;
        int den = r1->denominator;
        return RationalV(num, den);
    }
    throw(RuntimeError("Wrong typename for multiplication"));
}

Value Div::evalRator(const Value &rand1, const Value &rand2) { // /
    // Check for division by zero
    if (rand2->v_type == V_INT) {
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        if (n2 == 0) {
            throw(RuntimeError("Division by zero"));
        }
    } else if (rand2->v_type == V_RATIONAL) {
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        if (r2->numerator == 0) {
            throw(RuntimeError("Division by zero"));
        }
    }

    // Handle integer division (results in rational)
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        return RationalV(n1, n2);
    }
    // Handle rational number division
    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        int num = r1->numerator * r2->denominator;
        int den = r1->denominator * r2->numerator;
        return RationalV(num, den);
    }
    // Handle mixed integer and rational
    else if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        int num = n1 * r2->denominator;
        int den = r2->numerator;
        return RationalV(num, den);
    }
    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        int num = r1->numerator;
        int den = r1->denominator * n2;
        return RationalV(num, den);
    }
    throw(RuntimeError("Wrong typename for division"));
}

Value Modulo::evalRator(const Value &rand1, const Value &rand2) { // modulo
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int dividend = dynamic_cast<Integer*>(rand1.get())->n;
        int divisor = dynamic_cast<Integer*>(rand2.get())->n;
        if (divisor == 0) {
            throw(RuntimeError("Division by zero"));
        }
        return IntegerV(dividend % divisor);
    }
    throw(RuntimeError("modulo is only defined for integers"));
}

Value PlusVar::evalRator(const std::vector<Value> &args) { // + with multiple args
    // For Basic tasks, we only need binary operations
    // This is for Extension (arbitrary parameters)
    if (args.empty()) {
        return IntegerV(0); // (+) returns 0
    }

    // Start with first argument
    Value result = args[0];

    // Fold over remaining arguments
    for (size_t i = 1; i < args.size(); i++) {
        // Handle integer addition
        if (result->v_type == V_INT && args[i]->v_type == V_INT) {
            int n1 = dynamic_cast<Integer*>(result.get())->n;
            int n2 = dynamic_cast<Integer*>(args[i].get())->n;
            result = IntegerV(n1 + n2);
        }
        // Handle rational number addition
        else if (result->v_type == V_RATIONAL && args[i]->v_type == V_RATIONAL) {
            Rational* r1 = dynamic_cast<Rational*>(result.get());
            Rational* r2 = dynamic_cast<Rational*>(args[i].get());
            int num = r1->numerator * r2->denominator + r2->numerator * r1->denominator;
            int den = r1->denominator * r2->denominator;
            result = RationalV(num, den);
        }
        // Handle mixed integer and rational
        else if (result->v_type == V_INT && args[i]->v_type == V_RATIONAL) {
            int n1 = dynamic_cast<Integer*>(result.get())->n;
            Rational* r2 = dynamic_cast<Rational*>(args[i].get());
            int num = n1 * r2->denominator + r2->numerator;
            int den = r2->denominator;
            result = RationalV(num, den);
        }
        else if (result->v_type == V_RATIONAL && args[i]->v_type == V_INT) {
            Rational* r1 = dynamic_cast<Rational*>(result.get());
            int n2 = dynamic_cast<Integer*>(args[i].get())->n;
            int num = r1->numerator + n2 * r1->denominator;
            int den = r1->denominator;
            result = RationalV(num, den);
        }
        else {
            throw(RuntimeError("Wrong typename for addition"));
        }
    }

    return result;
}

Value MinusVar::evalRator(const std::vector<Value> &args) { // - with multiple args
    if (args.empty()) {
        throw RuntimeError("Wrong number of arguments for -");
    }
    if (args.size() == 1) {
        // (- x) returns -x
        Value arg = args[0];
        if (arg->v_type == V_INT) {
            int n = dynamic_cast<Integer*>(arg.get())->n;
            return IntegerV(-n);
        } else if (arg->v_type == V_RATIONAL) {
            Rational* r = dynamic_cast<Rational*>(arg.get());
            return RationalV(-r->numerator, r->denominator);
        } else {
            throw RuntimeError("Wrong typename for negation");
        }
    }
    // For binary case, use the logic from Minus::evalRator
    if (args.size() == 2) {
        // Handle integer subtraction
        if (args[0]->v_type == V_INT && args[1]->v_type == V_INT) {
            int n1 = dynamic_cast<Integer*>(args[0].get())->n;
            int n2 = dynamic_cast<Integer*>(args[1].get())->n;
            return IntegerV(n1 - n2);
        }
        // Handle rational number subtraction
        else if (args[0]->v_type == V_RATIONAL && args[1]->v_type == V_RATIONAL) {
            Rational* r1 = dynamic_cast<Rational*>(args[0].get());
            Rational* r2 = dynamic_cast<Rational*>(args[1].get());
            int num = r1->numerator * r2->denominator - r2->numerator * r1->denominator;
            int den = r1->denominator * r2->denominator;
            return RationalV(num, den);
        }
        // Handle mixed integer and rational
        else if (args[0]->v_type == V_INT && args[1]->v_type == V_RATIONAL) {
            int n1 = dynamic_cast<Integer*>(args[0].get())->n;
            Rational* r2 = dynamic_cast<Rational*>(args[1].get());
            int num = n1 * r2->denominator - r2->numerator;
            int den = r2->denominator;
            return RationalV(num, den);
        }
        else if (args[0]->v_type == V_RATIONAL && args[1]->v_type == V_INT) {
            Rational* r1 = dynamic_cast<Rational*>(args[0].get());
            int n2 = dynamic_cast<Integer*>(args[1].get())->n;
            int num = r1->numerator - n2 * r1->denominator;
            int den = r1->denominator;
            return RationalV(num, den);
        }
        throw(RuntimeError("Wrong typename for subtraction"));
    }
    // For more than 2 args: (- a b c) = a - b - c
    Value result = args[0];
    for (size_t i = 1; i < args.size(); i++) {
        // Reuse the binary logic
        if (result->v_type == V_INT && args[i]->v_type == V_INT) {
            int n1 = dynamic_cast<Integer*>(result.get())->n;
            int n2 = dynamic_cast<Integer*>(args[i].get())->n;
            result = IntegerV(n1 - n2);
        }
        // Similar for other type combinations...
        else {
            throw RuntimeError("Wrong typename for subtraction");
        }
    }
    return result;
}

Value MultVar::evalRator(const std::vector<Value> &args) { // * with multiple args
    if (args.empty()) {
        return IntegerV(1); // (*) returns 1
    }
    Value result = args[0];
    for (size_t i = 1; i < args.size(); i++) {
        // Simplified: only handle integers for now
        if (result->v_type == V_INT && args[i]->v_type == V_INT) {
            int n1 = dynamic_cast<Integer*>(result.get())->n;
            int n2 = dynamic_cast<Integer*>(args[i].get())->n;
            result = IntegerV(n1 * n2);
        } else {
            throw RuntimeError("Wrong typename for multiplication");
        }
    }
    return result;
}

Value DivVar::evalRator(const std::vector<Value> &args) { // / with multiple args
    if (args.empty()) {
        throw RuntimeError("Wrong number of arguments for /");
    }
    if (args.size() == 1) {
        // (/ x) returns 1/x
        Value arg = args[0];
        if (arg->v_type == V_INT) {
            int n = dynamic_cast<Integer*>(arg.get())->n;
            if (n == 0) throw RuntimeError("Division by zero");
            return RationalV(1, n);
        } else if (arg->v_type == V_RATIONAL) {
            Rational* r = dynamic_cast<Rational*>(arg.get());
            if (r->numerator == 0) throw RuntimeError("Division by zero");
            return RationalV(r->denominator, r->numerator);
        } else {
            throw RuntimeError("Wrong typename for division");
        }
    }
    Value result = args[0];
    for (size_t i = 1; i < args.size(); i++) {
        // Simplified: only handle integers for now
        if (result->v_type == V_INT && args[i]->v_type == V_INT) {
            int n1 = dynamic_cast<Integer*>(result.get())->n;
            int n2 = dynamic_cast<Integer*>(args[i].get())->n;
            if (n2 == 0) throw RuntimeError("Division by zero");
            result = RationalV(n1, n2);
        } else {
            throw RuntimeError("Wrong typename for division");
        }
    }
    return result;
}

Value Expt::evalRator(const Value &rand1, const Value &rand2) { // expt
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int base = dynamic_cast<Integer*>(rand1.get())->n;
        int exponent = dynamic_cast<Integer*>(rand2.get())->n;
        
        if (exponent < 0) {
            throw(RuntimeError("Negative exponent not supported for integers"));
        }
        if (base == 0 && exponent == 0) {
            throw(RuntimeError("0^0 is undefined"));
        }
        
        long long result = 1;
        long long b = base;
        int exp = exponent;
        
        while (exp > 0) {
            if (exp % 2 == 1) {
                result *= b;
                if (result > INT_MAX || result < INT_MIN) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            b *= b;
            if (b > INT_MAX || b < INT_MIN) {
                if (exp > 1) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            exp /= 2;
        }
        
        return IntegerV((int)result);
    }
    throw(RuntimeError("Wrong typename"));
}

//A FUNCTION TO SIMPLIFY THE COMPARISON WITH INTEGER AND RATIONAL NUMBER
int compareNumericValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        return (n1 < n2) ? -1 : (n1 > n2) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        int left = r1->numerator;
        int right = n2 * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_INT && v2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int left = n1 * r2->denominator;
        int right = r2->numerator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int left = r1->numerator * r2->denominator;
        int right = r2->numerator * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    throw RuntimeError("Wrong typename in numeric comparison");
}

Value Less::evalRator(const Value &rand1, const Value &rand2) { // <
    int cmp = compareNumericValues(rand1, rand2);
    return BooleanV(cmp < 0);
}

Value LessEq::evalRator(const Value &rand1, const Value &rand2) { // <=
    int cmp = compareNumericValues(rand1, rand2);
    return BooleanV(cmp <= 0);
}

Value Equal::evalRator(const Value &rand1, const Value &rand2) { // =
    int cmp = compareNumericValues(rand1, rand2);
    return BooleanV(cmp == 0);
}

Value GreaterEq::evalRator(const Value &rand1, const Value &rand2) { // >=
    int cmp = compareNumericValues(rand1, rand2);
    return BooleanV(cmp >= 0);
}

Value Greater::evalRator(const Value &rand1, const Value &rand2) { // >
    int cmp = compareNumericValues(rand1, rand2);
    return BooleanV(cmp > 0);
}

Value LessVar::evalRator(const std::vector<Value> &args) { // < with multiple args
    if (args.size() < 2) {
        throw RuntimeError("Wrong number of arguments for <");
    }
    for (size_t i = 0; i < args.size() - 1; i++) {
        int cmp = compareNumericValues(args[i], args[i+1]);
        if (cmp >= 0) { // not <
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value LessEqVar::evalRator(const std::vector<Value> &args) { // <= with multiple args
    if (args.size() < 2) {
        throw RuntimeError("Wrong number of arguments for <=");
    }
    for (size_t i = 0; i < args.size() - 1; i++) {
        int cmp = compareNumericValues(args[i], args[i+1]);
        if (cmp > 0) { // not <=
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value EqualVar::evalRator(const std::vector<Value> &args) { // = with multiple args
    if (args.size() < 2) {
        throw RuntimeError("Wrong number of arguments for =");
    }
    for (size_t i = 0; i < args.size() - 1; i++) {
        int cmp = compareNumericValues(args[i], args[i+1]);
        if (cmp != 0) { // not =
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value GreaterEqVar::evalRator(const std::vector<Value> &args) { // >= with multiple args
    if (args.size() < 2) {
        throw RuntimeError("Wrong number of arguments for >=");
    }
    for (size_t i = 0; i < args.size() - 1; i++) {
        int cmp = compareNumericValues(args[i], args[i+1]);
        if (cmp < 0) { // not >=
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value GreaterVar::evalRator(const std::vector<Value> &args) { // > with multiple args
    if (args.size() < 2) {
        throw RuntimeError("Wrong number of arguments for >");
    }
    for (size_t i = 0; i < args.size() - 1; i++) {
        int cmp = compareNumericValues(args[i], args[i+1]);
        if (cmp <= 0) { // not >
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value Cons::evalRator(const Value &rand1, const Value &rand2) { // cons
    return PairV(rand1, rand2);
}

Value ListFunc::evalRator(const std::vector<Value> &args) { // list function
    // Build list from right to left
    Value result = NullV();
    for (auto it = args.rbegin(); it != args.rend(); ++it) {
        result = PairV(*it, result);
    }
    return result;
}

Value IsList::evalRator(const Value &rand) { // list?
    // Check if value is a proper list (ends with null)
    Value current = rand;
    while (current->v_type == V_PAIR) {
        Pair* pair = dynamic_cast<Pair*>(current.get());
        current = pair->cdr;
    }
    // Proper list ends with null
    return BooleanV(current->v_type == V_NULL);
}

Value Car::evalRator(const Value &rand) { // car
    if (rand->v_type != V_PAIR) {
        throw RuntimeError("car: argument is not a pair");
    }
    Pair* pair = dynamic_cast<Pair*>(rand.get());
    return pair->car;
}

Value Cdr::evalRator(const Value &rand) { // cdr
    if (rand->v_type != V_PAIR) {
        throw RuntimeError("cdr: argument is not a pair");
    }
    Pair* pair = dynamic_cast<Pair*>(rand.get());
    return pair->cdr;
}

Value SetCar::evalRator(const Value &rand1, const Value &rand2) { // set-car!
    if (rand1->v_type != V_PAIR) {
        throw RuntimeError("set-car!: argument is not a pair");
    }
    Pair* pair = dynamic_cast<Pair*>(rand1.get());
    // Note: This modifies the pair in place
    // For simplicity, we'll just throw an error for now
    throw RuntimeError("set-car! not implemented");
}

Value SetCdr::evalRator(const Value &rand1, const Value &rand2) { // set-cdr!
    if (rand1->v_type != V_PAIR) {
        throw RuntimeError("set-cdr!: argument is not a pair");
    }
    Pair* pair = dynamic_cast<Pair*>(rand1.get());
    // Note: This modifies the pair in place
    // For simplicity, we'll just throw an error for now
    throw RuntimeError("set-cdr! not implemented");
}

Value IsEq::evalRator(const Value &rand1, const Value &rand2) { // eq?
    // Check if type is Integer
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        return BooleanV((dynamic_cast<Integer*>(rand1.get())->n) == (dynamic_cast<Integer*>(rand2.get())->n));
    }
    // Check if type is Boolean
    else if (rand1->v_type == V_BOOL && rand2->v_type == V_BOOL) {
        return BooleanV((dynamic_cast<Boolean*>(rand1.get())->b) == (dynamic_cast<Boolean*>(rand2.get())->b));
    }
    // Check if type is Symbol
    else if (rand1->v_type == V_SYM && rand2->v_type == V_SYM) {
        return BooleanV((dynamic_cast<Symbol*>(rand1.get())->s) == (dynamic_cast<Symbol*>(rand2.get())->s));
    }
    // Check if type is Null or Void
    else if ((rand1->v_type == V_NULL && rand2->v_type == V_NULL) ||
             (rand1->v_type == V_VOID && rand2->v_type == V_VOID)) {
        return BooleanV(true);
    } else {
        return BooleanV(rand1.get() == rand2.get());
    }
}

Value IsBoolean::evalRator(const Value &rand) { // boolean?
    return BooleanV(rand->v_type == V_BOOL);
}

Value IsFixnum::evalRator(const Value &rand) { // number?
    return BooleanV(rand->v_type == V_INT);
}

Value IsNull::evalRator(const Value &rand) { // null?
    return BooleanV(rand->v_type == V_NULL);
}

Value IsPair::evalRator(const Value &rand) { // pair?
    return BooleanV(rand->v_type == V_PAIR);
}

Value IsProcedure::evalRator(const Value &rand) { // procedure?
    return BooleanV(rand->v_type == V_PROC);
}

Value IsSymbol::evalRator(const Value &rand) { // symbol?
    return BooleanV(rand->v_type == V_SYM);
}

Value IsString::evalRator(const Value &rand) { // string?
    return BooleanV(rand->v_type == V_STRING);
}

Value Display::evalRator(const Value &rand) { // display function
    if (rand->v_type == V_STRING) {
        String* str_ptr = dynamic_cast<String*>(rand.get());
        std::cout << str_ptr->s;
    } else {
        rand->show(std::cout);
    }

    return VoidV();
}

Value Begin::eval(Assoc &e) {
    if (es.empty()) {
        return VoidV();
    }

    Value lastValue = VoidV();
    for (const auto& expr : es) {
        lastValue = expr->eval(e);
    }
    return lastValue;
}

// Helper function to convert Syntax to Value for quote
Value syntaxToValue(const Syntax &syntax) {
    // Try to cast to different syntax types
    if (auto* num = dynamic_cast<Number*>(syntax.get())) {
        return IntegerV(num->n);
    }
    else if (auto* rat = dynamic_cast<RationalSyntax*>(syntax.get())) {
        return RationalV(rat->numerator, rat->denominator);
    }
    else if (auto* sym = dynamic_cast<SymbolSyntax*>(syntax.get())) {
        return SymbolV(sym->s);
    }
    else if (auto* str = dynamic_cast<StringSyntax*>(syntax.get())) {
        return StringV(str->s);
    }
    else if (auto* trueSyn = dynamic_cast<TrueSyntax*>(syntax.get())) {
        return BooleanV(true);
    }
    else if (auto* falseSyn = dynamic_cast<FalseSyntax*>(syntax.get())) {
        return BooleanV(false);
    }
    else if (auto* list = dynamic_cast<List*>(syntax.get())) {
        if (list->stxs.empty()) {
            return NullV();
        }
        // Convert list to pair chain
        // For now, return a simple representation
        // We'll need to implement proper list conversion
        return NullV(); // Placeholder
    }
    throw RuntimeError("Unknown syntax type in quote");
}

Value Quote::eval(Assoc& e) {
    // Convert syntax to value without evaluation
    return syntaxToValue(s);
}

Value AndVar::eval(Assoc &e) { // and with short-circuit evaluation
    if (rands.empty()) {
        return BooleanV(true); // (and) returns #t
    }

    Value lastValue = BooleanV(false);
    for (const auto& expr : rands) {
        lastValue = expr->eval(e);
        // Check if lastValue is false
        if (lastValue->v_type == V_BOOL) {
            Boolean* b = dynamic_cast<Boolean*>(lastValue.get());
            if (!b->b) {
                return BooleanV(false); // short-circuit
            }
        }
        // Non-boolean values are considered true in Scheme
    }
    return lastValue; // Return the last value
}

Value OrVar::eval(Assoc &e) { // or with short-circuit evaluation
    if (rands.empty()) {
        return BooleanV(false); // (or) returns #f
    }

    for (const auto& expr : rands) {
        Value val = expr->eval(e);
        // Check if val is true (non-false)
        if (val->v_type == V_BOOL) {
            Boolean* b = dynamic_cast<Boolean*>(val.get());
            if (b->b) {
                return val; // short-circuit, return the true value
            }
        } else {
            // Non-boolean values are considered true in Scheme
            return val; // short-circuit, return the non-false value
        }
    }
    return BooleanV(false); // All were false
}

Value Not::evalRator(const Value &rand) { // not
    // In Scheme, only #f is false, everything else is true
    if (rand->v_type == V_BOOL) {
        Boolean* b = dynamic_cast<Boolean*>(rand.get());
        return BooleanV(!b->b);
    }
    return BooleanV(false); // non-boolean values are true, so not returns false
}

Value If::eval(Assoc &e) {
    Value condValue = cond->eval(e);

    // In Scheme, only #f is false, everything else is true
    bool conditionIsTrue = true;
    if (condValue->v_type == V_BOOL) {
        Boolean* b = dynamic_cast<Boolean*>(condValue.get());
        conditionIsTrue = b->b;
    }

    if (conditionIsTrue) {
        return conseq->eval(e);
    } else {
        return alter->eval(e);
    }
}

Value Cond::eval(Assoc &env) {
    for (const auto& clause : clauses) {
        if (clause.size() < 1) {
            throw RuntimeError("Invalid cond clause");
        }
        // Evaluate predicate
        Value predValue = clause[0]->eval(env);
        bool conditionIsTrue = true;
        if (predValue->v_type == V_BOOL) {
            Boolean* b = dynamic_cast<Boolean*>(predValue.get());
            conditionIsTrue = b->b;
        }
        // In Scheme, only #f is false
        if (conditionIsTrue) {
            // Evaluate and return the result
            if (clause.size() == 1) {
                return predValue; // No body, return predicate value
            }
            // Evaluate body expressions
            Value lastValue = VoidV();
            for (size_t i = 1; i < clause.size(); i++) {
                lastValue = clause[i]->eval(env);
            }
            return lastValue;
        }
    }
    // No matching clause
    return VoidV();
}

Value Lambda::eval(Assoc &env) {
    // Create a closure: capture current environment and parameters
    return ProcedureV(x, e, env);
}

Value Apply::eval(Assoc &e) {
    Value ratorValue = rator->eval(e);
    if (ratorValue->v_type != V_PROC) {
        throw RuntimeError("Attempt to apply a non-procedure");
    }

    Procedure* clos_ptr = dynamic_cast<Procedure*>(ratorValue.get());

    // Evaluate arguments
    std::vector<Value> args;
    for (const auto& argExpr : rand) {
        args.push_back(argExpr->eval(e));
    }

    if (args.size() != clos_ptr->parameters.size()) {
        throw RuntimeError("Wrong number of arguments");
    }

    // Create new environment by extending the closure's environment with parameter bindings
    Assoc param_env = clos_ptr->env;
    for (size_t i = 0; i < clos_ptr->parameters.size(); i++) {
        param_env = extend(clos_ptr->parameters[i], args[i], param_env);
    }

    return clos_ptr->e->eval(param_env);
}

Value Define::eval(Assoc &env) {
    // Evaluate the expression
    Value val = e->eval(env);

    // Add binding to global environment
    // Note: This modifies the environment in place
    // For simplicity, we'll add to the current environment
    // In a real Scheme, define should add to global environment

    // Check if variable already exists
    Value existing = find(var, env);
    if (existing.get() != nullptr) {
        // Modify existing binding
        modify(var, val, env);
    } else {
        // Add new binding
        env = extend(var, val, env);
    }

    return VoidV(); // define returns void
}

Value Let::eval(Assoc &env) {
    // For now, just throw not implemented
    throw RuntimeError("let not implemented");
}

Value Letrec::eval(Assoc &env) {
    // For now, just throw not implemented
    throw RuntimeError("letrec not implemented");
}

Value Set::eval(Assoc &env) {
    // For now, just throw not implemented
    throw RuntimeError("set! not implemented");
}
