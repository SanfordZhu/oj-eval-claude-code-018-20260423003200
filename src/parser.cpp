/**
 * @file parser.cpp
 * @brief Parsing implementation for Scheme syntax tree to expression tree conversion
 * 
 * This file implements the parsing logic that converts syntax trees into
 * expression trees that can be evaluated.
 * primitive operations, and function applications.
 */

#include "RE.hpp"
#include "Def.hpp"
#include "syntax.hpp"
#include "value.hpp"
#include "expr.hpp"
#include <map>
#include <string>
#include <iostream>

#define mp make_pair
using std::string;
using std::vector;
using std::pair;

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

/**
 * @brief Default parse method (should be overridden by subclasses)
 */
Expr Syntax::parse(Assoc &env) {
    throw RuntimeError("Unimplemented parse method");
}

Expr Number::parse(Assoc &env) {
    return Expr(new Fixnum(n));
}

Expr RationalSyntax::parse(Assoc &env) {
    return Expr(new RationalNum(numerator, denominator));
}

Expr SymbolSyntax::parse(Assoc &env) {
    return Expr(new Var(s));
}

Expr StringSyntax::parse(Assoc &env) {
    return Expr(new StringExpr(s));
}

Expr TrueSyntax::parse(Assoc &env) {
    return Expr(new True());
}

Expr FalseSyntax::parse(Assoc &env) {
    return Expr(new False());
}

Expr List::parse(Assoc &env) {
    if (stxs.empty()) {
        return Expr(new Quote(Syntax(new List())));
    }

    //TODO: check if the first element is a symbol
    //If not, use Apply function to package to a closure;
    //If so, find whether it's a variable or a keyword;
    SymbolSyntax *id = dynamic_cast<SymbolSyntax*>(stxs[0].get());
    if (id == nullptr) {
        // First element is not a symbol, so it's an expression that should evaluate to a procedure
        // Parse it and then parse arguments
        Expr ratorExpr = stxs[0]->parse(env);
        std::vector<Expr> argExprs;
        for (size_t i = 1; i < stxs.size(); i++) {
            argExprs.push_back(stxs[i]->parse(env));
        }
        return Expr(new Apply(ratorExpr, argExprs));
    }else{
    string op = id->s;
    if (find(op, env).get() != nullptr) {
        // Variable found in environment, treat as function application
        Expr ratorExpr = Expr(new Var(op));
        std::vector<Expr> argExprs;
        for (size_t i = 1; i < stxs.size(); i++) {
            argExprs.push_back(stxs[i]->parse(env));
        }
        return Expr(new Apply(ratorExpr, argExprs));
    }
    if (primitives.count(op) != 0) {
        vector<Expr> parameters;
        // Parse parameters
        for (size_t i = 1; i < stxs.size(); i++) {
            parameters.push_back(stxs[i]->parse(env));
        }

        ExprType op_type = primitives[op];
        if (op_type == E_PLUS) {
            if (parameters.size() == 2) {
                return Expr(new Plus(parameters[0], parameters[1]));
            } else {
                throw RuntimeError("Wrong number of arguments for +");
            }
        } else if (op_type == E_MINUS) {
            if (parameters.size() == 2) {
                return Expr(new Minus(parameters[0], parameters[1]));
            } else {
                throw RuntimeError("Wrong number of arguments for -");
            }
        } else if (op_type == E_MUL) {
            if (parameters.size() == 2) {
                return Expr(new Mult(parameters[0], parameters[1]));
            } else {
                throw RuntimeError("Wrong number of arguments for *");
            }
        }  else if (op_type == E_DIV) {
            if (parameters.size() == 2) {
                return Expr(new Div(parameters[0], parameters[1]));
            } else {
                throw RuntimeError("Wrong number of arguments for /");
            }
        } else if (op_type == E_MODULO) {
            if (parameters.size() != 2) {
                throw RuntimeError("Wrong number of arguments for modulo");
            }
            return Expr(new Modulo(parameters[0], parameters[1]));
        } else if (op_type == E_LIST) {
            return Expr(new ListFunc(parameters));
        } else if (op_type == E_LT) {
            if (parameters.size() == 2) {
                return Expr(new Less(parameters[0], parameters[1]));
            } else {
                throw RuntimeError("Wrong number of arguments for <");
            }
        } else if (op_type == E_LE) {
            if (parameters.size() == 2) {
                return Expr(new LessEq(parameters[0], parameters[1]));
            } else {
                throw RuntimeError("Wrong number of arguments for <=");
            }
        } else if (op_type == E_EQ) {
            if (parameters.size() == 2) {
                return Expr(new Equal(parameters[0], parameters[1]));
            } else {
                throw RuntimeError("Wrong number of arguments for =");
            }
        } else if (op_type == E_GE) {
            if (parameters.size() == 2) {
                return Expr(new GreaterEq(parameters[0], parameters[1]));
            } else {
                throw RuntimeError("Wrong number of arguments for >=");
            }
        } else if (op_type == E_GT) {
            if (parameters.size() == 2) {
                return Expr(new Greater(parameters[0], parameters[1]));
            } else {
                throw RuntimeError("Wrong number of arguments for >");
            }
        } else if (op_type == E_AND) {
            return Expr(new AndVar(parameters));
        } else if (op_type == E_OR) {
            return Expr(new OrVar(parameters));
        } else if (op_type == E_CONS) {
            if (parameters.size() != 2) {
                throw RuntimeError("Wrong number of arguments for cons");
            }
            return Expr(new Cons(parameters[0], parameters[1]));
        } else if (op_type == E_CAR) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for car");
            }
            return Expr(new Car(parameters[0]));
        } else if (op_type == E_CDR) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for cdr");
            }
            return Expr(new Cdr(parameters[0]));
        } else if (op_type == E_NOT) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for not");
            }
            return Expr(new Not(parameters[0]));
        } else {
            //TODO: TO COMPLETE THE LOGIC
        }
    }

    if (reserved_words.count(op) != 0) {
    	switch (reserved_words[op]) {
            case E_QUOTE:
                if (stxs.size() != 2) {
                    throw RuntimeError("Wrong number of arguments for quote");
                }
                return Expr(new Quote(stxs[1]));
            case E_BEGIN: {
                std::vector<Expr> exprs;
                for (size_t i = 1; i < stxs.size(); i++) {
                    exprs.push_back(stxs[i]->parse(env));
                }
                return Expr(new Begin(exprs));
            }
            case E_IF: {
                if (stxs.size() != 4) {
                    throw RuntimeError("Wrong number of arguments for if");
                }
                Expr condExpr = stxs[1]->parse(env);
                Expr conseqExpr = stxs[2]->parse(env);
                Expr alterExpr = stxs[3]->parse(env);
                return Expr(new If(condExpr, conseqExpr, alterExpr));
            }
            case E_LAMBDA: {
                if (stxs.size() < 3) {
                    throw RuntimeError("Wrong number of arguments for lambda");
                }
                // Parse parameter list
                List* paramList = dynamic_cast<List*>(stxs[1].get());
                if (!paramList) {
                    throw RuntimeError("Lambda parameters must be a list");
                }
                std::vector<std::string> params;
                for (const auto& paramSyntax : paramList->stxs) {
                    SymbolSyntax* sym = dynamic_cast<SymbolSyntax*>(paramSyntax.get());
                    if (!sym) {
                        throw RuntimeError("Lambda parameters must be symbols");
                    }
                    params.push_back(sym->s);
                }
                // Parse body (can be multiple expressions, wrapped in begin)
                std::vector<Expr> bodyExprs;
                for (size_t i = 2; i < stxs.size(); i++) {
                    bodyExprs.push_back(stxs[i]->parse(env));
                }
                Expr body = bodyExprs[0]; // Default to first expression
                if (bodyExprs.size() > 1) {
                    body = Expr(new Begin(bodyExprs));
                }
                return Expr(new Lambda(params, body));
            }
            case E_DEFINE: {
                if (stxs.size() < 3) {
                    throw RuntimeError("Wrong number of arguments for define");
                }
                // Check if first argument is a symbol (simple variable definition)
                SymbolSyntax* varSym = dynamic_cast<SymbolSyntax*>(stxs[1].get());
                if (varSym) {
                    // Simple variable definition: (define var expr)
                    if (stxs.size() != 3) {
                        throw RuntimeError("Wrong number of arguments for define");
                    }
                    Expr expr = stxs[2]->parse(env);
                    return Expr(new Define(varSym->s, expr));
                } else {
                    // Function definition: (define (func params...) body...)
                    List* funcList = dynamic_cast<List*>(stxs[1].get());
                    if (!funcList || funcList->stxs.empty()) {
                        throw RuntimeError("Invalid define syntax");
                    }
                    SymbolSyntax* funcNameSym = dynamic_cast<SymbolSyntax*>(funcList->stxs[0].get());
                    if (!funcNameSym) {
                        throw RuntimeError("Function name must be a symbol in define");
                    }
                    std::string funcName = funcNameSym->s;
                    // Parse parameters
                    std::vector<std::string> params;
                    for (size_t i = 1; i < funcList->stxs.size(); i++) {
                        SymbolSyntax* paramSym = dynamic_cast<SymbolSyntax*>(funcList->stxs[i].get());
                        if (!paramSym) {
                            throw RuntimeError("Function parameters must be symbols");
                        }
                        params.push_back(paramSym->s);
                    }
                    // Parse body
                    std::vector<Expr> bodyExprs;
                    for (size_t i = 2; i < stxs.size(); i++) {
                        bodyExprs.push_back(stxs[i]->parse(env));
                    }
                    Expr body = bodyExprs[0]; // Default to first expression
                    if (bodyExprs.size() > 1) {
                        body = Expr(new Begin(bodyExprs));
                    }
                    // Create lambda expression
                    Expr lambdaExpr = Expr(new Lambda(params, body));
                    // Create define expression for the function name
                    return Expr(new Define(funcName, lambdaExpr));
                }
            }
            case E_COND: {
                // Parse cond clauses
                std::vector<std::vector<Expr>> clauses;
                for (size_t i = 1; i < stxs.size(); i++) {
                    List* clauseList = dynamic_cast<List*>(stxs[i].get());
                    if (!clauseList) {
                        throw RuntimeError("cond clause must be a list");
                    }
                    std::vector<Expr> clauseExprs;
                    for (const auto& exprSyntax : clauseList->stxs) {
                        clauseExprs.push_back(exprSyntax->parse(env));
                    }
                    clauses.push_back(clauseExprs);
                }
                return Expr(new Cond(clauses));
            }
            case E_LET:
            case E_LETREC:
            case E_SET:
                // For now, throw not implemented
                throw RuntimeError(op + " not implemented");
			//TODO: TO COMPLETE THE reserve_words PARSER LOGIC
        	default:
            	throw RuntimeError("Unknown reserved word: " + op);
    	}
    }

    //default: use Apply to be an expression
    // Symbol not found in environment, not a primitive, not a reserved word
    // Treat as function application (will fail at runtime if not defined)
    Expr ratorExpr = Expr(new Var(op));
    std::vector<Expr> argExprs;
    for (size_t i = 1; i < stxs.size(); i++) {
        argExprs.push_back(stxs[i]->parse(env));
    }
    return Expr(new Apply(ratorExpr, argExprs));
}
}
