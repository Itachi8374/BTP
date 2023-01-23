/* A Bison parser, made by GNU Bison 3.8.2.  */

/* Bison interface for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2015, 2018-2021 Free Software Foundation,
   Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <https://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* DO NOT RELY ON FEATURES THAT ARE NOT DOCUMENTED in the manual,
   especially those whose name start with YY_ or yy_.  They are
   private implementation details that can be changed or removed.  */

#ifndef YY_YY_FSMDA_TAB_H_INCLUDED
# define YY_YY_FSMDA_TAB_H_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif
#if YYDEBUG
extern int yydebug;
#endif

/* Token kinds.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    YYEMPTY = -2,
    YYEOF = 0,                     /* "end of file"  */
    YYerror = 256,                 /* error  */
    YYUNDEF = 257,                 /* "invalid token"  */
    IDENTIFIER = 258,              /* IDENTIFIER  */
    CONSTANT = 259,                /* CONSTANT  */
    STRING_LITERAL = 260,          /* STRING_LITERAL  */
    LE_OP = 261,                   /* LE_OP  */
    GE_OP = 262,                   /* GE_OP  */
    EQ_OP = 263,                   /* EQ_OP  */
    NE_OP = 264,                   /* NE_OP  */
    AND = 265,                     /* AND  */
    OR = 266,                      /* OR  */
    NOT = 267,                     /* NOT  */
    READ = 268,                    /* READ  */
    OUT = 269,                     /* OUT  */
    EQUAL = 270,                   /* EQUAL  */
    COMMA = 271,                   /* COMMA  */
    SEMIC = 272,                   /* SEMIC  */
    SEPARATOR = 273,               /* SEPARATOR  */
    LT_OP = 274,                   /* LT_OP  */
    GT_OP = 275,                   /* GT_OP  */
    LEFT_BR = 276,                 /* LEFT_BR  */
    RIGHT_BR = 277,                /* RIGHT_BR  */
    LEFT_SQBR = 278,               /* LEFT_SQBR  */
    RIGHT_SQBR = 279,              /* RIGHT_SQBR  */
    MULT = 280,                    /* MULT  */
    DIV = 281,                     /* DIV  */
    MOD = 282,                     /* MOD  */
    PLUS = 283,                    /* PLUS  */
    MINUS = 284                    /* MINUS  */
  };
  typedef enum yytokentype yytoken_kind_t;
#endif

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
union YYSTYPE
{
#line 16 "./src/fsmda.y"

	char* string;
	struct normalized_cell* norm;
	struct Assign* data_trans;
	struct Assign_list* dt_list;
	struct Substatement* substmt;
	struct Substatement_list* substmt_list;
	struct Statement* stmt;
	struct Statement_list* stmt_list;
	

#line 105 "fsmda.tab.h"

};
typedef union YYSTYPE YYSTYPE;
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif


extern YYSTYPE yylval;


int yyparse (void);


#endif /* !YY_YY_FSMDA_TAB_H_INCLUDED  */
