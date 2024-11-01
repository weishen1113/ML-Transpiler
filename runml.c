//  CITS2002 Project 1 2024
//  Student1:   24250666   Wei Shen Hong
//  Student2:   24122057   Yize Sun
//  Platform:   Ubuntu Linux
#include <assert.h>
#include <errno.h>
#include <math.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>  // Include this for getpid()
#include <sys/types.h>  // For getpid() on some systems
#include <sys/wait.h>   // For waitpid()
typedef unsigned char BOOL;
static const char* constC11_Header =
    "#include <stdlib.h>\n"
    "#include <stdio.h>\n"
    "#include <math.h>\n"
    "static double arg0=0.0,arg1=0.0,arg2=0.0,arg3=0.0,arg4=0.0,arg5=0.0,arg6=0.0,arg7=0.0,arg8=0.0,arg9=0.0;\n"
    "static void parseInputArgs(int argc, char** argv){\n"
    "    switch (argc) {\n"
    "    case 10:\n"
    "        arg9 = atof(argv[9]);\n"
    "    case 9:\n"
    "        arg8 = atof(argv[8]);\n"
    "    case 8:\n"
    "        arg7 = atof(argv[7]);\n"
    "    case 7:\n"
    "        arg6 = atof(argv[6]);\n"
    "    case 6:\n"
    "        arg5 = atof(argv[5]);\n"
    "    case 5:\n"
    "        arg4 = atof(argv[4]);\n"
    "    case 4:\n"
    "        arg3 = atof(argv[3]);\n"
    "    case 3:\n"
    "        arg2 = atof(argv[2]);\n"
    "    case 2:\n"
    "        arg1 = atof(argv[1]);\n"
    "    case 1:\n"
    "        arg0 = atof(argv[0]);\n"
    "        break;\n"
    "    default:\n"
    "        break;\n"
    "    }\n"
    "}\n"
    "static void _fin_print(double x){\n"
    "    if(fmod(x, 1) == 0){\n"
    "        printf(\"%.0f\\n\",x);\n"
    "    }else{\n"
    "        printf(\"%.6f\\n\",x);\n"
    "    }\n"
    "}\n"
    ;
static const char* constC11_mainStart =
    "int main(int argc, char** argv){\n"
    "    if(argc > 1){\n"
    "        argc --;\n"
    "        argv++;\n"
    "        parseInputArgs(argc,argv);\n"
    "    }\n";
static const char* constC11_mainEnd =
    "    return 0;\n"
    "}\n";
#define ML_FILE_MAX_BYTES (1 * 1024 * 1024)
#define ML_FILE_ROW_NUMX 2000
#define ML_INDENTIFIERS_MAX 50
#define ML_CMDARG_NUMX  10
typedef unsigned int U32;
static char m_strMsgBuff[4096];
typedef struct _S_SLINE1_ {
    char* pLineStart;
    int MLRowLen;
    int orgLineNo;
    int lineIndex;
    unsigned char bStatement;
    unsigned char bVarDec;
    unsigned char bFunDec;
    unsigned char bFunInner;
    unsigned char bPrint;
    unsigned char reserve00[3];
    unsigned char reserve10[4];
} SLINE1;
typedef enum _E_ESTMT_TYPE_ {
    eStmtNone,
    eStmtPrint,
    eStmtVarSet,
    eStmtFuncDec,
    eStmtFuncCall,
    eStmtFuncBody,
    eStmtBodyRet
} ESTMT_TYPE;
typedef struct _S_SSTATEMENT1_ {
    char* pName;
    char* pExpr;
    SLINE1* pStartLine;
    struct _S_SFUNC1_* pSFunc1;
    char* pC11VarDec;
    char* pC11Statement;
    ESTMT_TYPE eStmtType;
    int LineNum;
    BOOL bFuncBody;
    unsigned char reserve00[3];
    unsigned char reserve10[4];
} SSTATEMENT1;
typedef enum _E_EIDTYPE_ {
    eID_var,
    eID_func
} EIDTYPE;
typedef struct _S_SFUNC1_ {
    char* pName;
    SSTATEMENT1* pSDecStmt;
    char* pC11Start;
    int paramNum;
    int reserve00;
} SFUNC1;
typedef struct _S_SVAR1_ {
    char* pName;
    SSTATEMENT1* pSDecStmt;
    char* pC11Start;
} SVAR1;
typedef struct _S_SIDENTIFY_ {
    EIDTYPE idType;
    int reserve0;
    union _U_UID_ {
        char* pName;
        SFUNC1 func;
        SVAR1 var;
    } id;
} SIDENTIFY;
static SLINE1 m_listLines[ML_FILE_ROW_NUMX];
static SSTATEMENT1 m_sListStmts[ML_FILE_ROW_NUMX];
static SIDENTIFY m_slistIDs[ML_INDENTIFIERS_MAX];
static BOOL m_bMLParseError;
static BOOL m_bConvC11Error;
static int m_nMLOrgLineNum;
static void DebugPrintf(const char* pformat, ...) {
    va_list args;
    va_start(args, pformat);
    vsnprintf(m_strMsgBuff, sizeof(m_strMsgBuff) - 1, (const char* __restrict)pformat, args);
    va_end(args);
    fputs("@ Debug: ", stderr);
    fputs(m_strMsgBuff, stderr);
    fflush(stderr);
}
static void FatalPrintf(const char* pformat, ...) {
    va_list args;
    va_start(args, pformat);
    vsnprintf(m_strMsgBuff, sizeof(m_strMsgBuff) - 1, (const char* __restrict)pformat, args);
    va_end(args);
    fputs("! Error: ", stderr);
    fputs(m_strMsgBuff, stderr);
    fflush(stderr);
    exit(1);
}
static void ParseMLError(int lineNo, const char* pformat, ...) {
    va_list args;
    va_start(args, pformat);
    int len1 = vsnprintf(m_strMsgBuff, sizeof(m_strMsgBuff) - 1, (const char* __restrict)pformat, args);
    va_end(args);
    fprintf(stderr, "! Error: ParseML [line-%d] ", lineNo);
    if (m_strMsgBuff[len1 - 2] == '\n') {
        m_strMsgBuff[len1 - 1] = '\0';
    }
    fputs(m_strMsgBuff, stderr);
    fflush(stderr);
    m_bMLParseError = 1;
}
static void ConvC11Error(int lineNo, const char* pformat, ...) {
    va_list args;
    va_start(args, pformat);
    int len1 = vsnprintf(m_strMsgBuff, sizeof(m_strMsgBuff) - 1, (const char* __restrict)pformat, args);
    va_end(args);
    fprintf(stderr, "! Error: ConvC11 [line-%d] ", lineNo);
    if (m_strMsgBuff[len1 - 2] == '\n') {
        m_strMsgBuff[len1 - 1] = '\0';
    }
    fputs(m_strMsgBuff, stderr);
    fflush(stderr);
    m_bConvC11Error = 1;
}
// Responsible for loading a text file into memory, performing basic parsing and validation checks
int ml_file_load(int* pLineNumML, const char* pathML) {
    static char m_strMLBuff[ML_FILE_MAX_BYTES];
    DebugPrintf("Load ML file %s into cache\n", pathML);
    FILE* fileML = fopen(pathML, "r");
    if (fileML == NULL) {
        FatalPrintf("Failed to open file: %s\n", pathML); // Print file name for more clarity
        return -1;
    }
    fseek(fileML, 0, SEEK_END);
    long len = ftell(fileML);
    if (len >= ML_FILE_MAX_BYTES) {
        fclose(fileML);
        FatalPrintf("File size exceeds limit\n");
        return -1;
    }
    fseek(fileML, 0, SEEK_SET);
    char* pMLBuff = m_strMLBuff;
    char lineBuff[2048];
    int orgLineNo = 0;
    int LineNumML = 0;
    int i;
    SLINE1* pSLine1 = m_listLines;
    while (fgets(lineBuff, sizeof(lineBuff) - 1, fileML)) {
        orgLineNo++;
        if (lineBuff[0] == '#')
            continue;
        char* pFind = strchr(lineBuff, '#');
        if (pFind != NULL) {
            *pFind = 0;
        }
        int lineLine = (int)strlen(lineBuff);
        if (lineLine >= 2) {
            if (lineBuff[lineLine - 2] == '\r' && lineBuff[lineLine - 1] == '\n') {
                lineBuff[lineLine - 2] = 0;
                lineLine -= 2;
            }else if (lineBuff[lineLine - 1] == '\n') {
                lineBuff[lineLine - 1] = 0;
                lineLine -= 1;
            }
        } else if (lineLine >= 1) {
            if (lineBuff[lineLine - 1] == '\n') {
                lineBuff[lineLine - 1] = 0;
                lineLine -= 1;
            }
        }
        // Character validation
        if (lineLine == 0)
            continue;
        for (i = 0; i < lineLine; i++) {
            if ('a' <= lineBuff[i] && lineBuff[i] <= 'z') {
                continue;
            }
            if ('0' <= lineBuff[i] && lineBuff[i] <= '9') {
                continue;
            }
            if (lineBuff[i] == '(' || lineBuff[i] == ')' || lineBuff[i] == '<' || lineBuff[i] == ' ' || lineBuff[i] == '\t' || lineBuff[i] == '.' || lineBuff[i] == ',') {
                continue;
            }
            if (lineBuff[i] == '+' || lineBuff[i] == '-' || lineBuff[i] == '*' || lineBuff[i] == '/') {
                continue;
            }
            ParseMLError(orgLineNo, "illegal characters %c\n", lineBuff[i]);
            break;
        }
        if (i != lineLine) {
            continue;
        }
        char* pLineBuffNew = lineBuff;
        for (i = 0; i < lineLine - 1; i++) {
            if (*pLineBuffNew == ' ') {
                pLineBuffNew++;
                continue;
            }
            if (pLineBuffNew[0] == '\t' && pLineBuffNew[1] == '\t') {
                pLineBuffNew++;
                continue;
            }
            break;
        }
        lineLine = (int)strlen(pLineBuffNew);
        if (lineLine == 0)
            continue;
        char* pLineEnd = &pLineBuffNew[lineLine - 1];
        for (i = 0; i < lineLine; i++) {
            if (*pLineEnd == ' ' || *pLineEnd == '\t') {
                *pLineEnd = 0;
                pLineEnd--;
                continue;
            }
            break;
        }
        lineLine = (int)strlen(pLineBuffNew);
        if (lineLine == 0)
            continue;
        memcpy(pMLBuff, pLineBuffNew, (U32)lineLine);
        pMLBuff[lineLine] = '\n';
        pMLBuff[lineLine + 1] = 0;
        pSLine1->pLineStart = pMLBuff;
        pSLine1->MLRowLen = lineLine + 1;
        pSLine1->lineIndex = LineNumML;
        pSLine1->orgLineNo = orgLineNo;
        LineNumML++;
        pSLine1++;
        pMLBuff += lineLine + 2;
        if (LineNumML >= ML_FILE_ROW_NUMX) {
            FatalPrintf("The number of file lines exceeds the limit\n");
            break;
        }
    }
    *pLineNumML = LineNumML;
    m_nMLOrgLineNum = orgLineNo;
    fclose(fileML);
    if (m_bMLParseError || m_bConvC11Error) {
        exit(2);
    }
    return 0;
}
int strStartsWith(const char* str, const char* prefix) {
    return strncmp(str, prefix, strlen(prefix));
}
// Validates the name of an identifier
int identify_name_check(int orgLineNo, const char* name, ESTMT_TYPE eStmtType) {
    if (eStmtType == eStmtVarSet) {
        if (strStartsWith(name, "arg") == 0) {
            return 0;
        }
    }
    int len1 = (int)strlen(name);
    if (len1 > 12) {
        ParseMLError(orgLineNo, "Identifier name %s exceeds 12 characters\n", name);
        return -1;
    } else if (len1 < 1) {
        ParseMLError(orgLineNo, "Identifier name %s is less than 1 character\n", name);
        return -1;
    }
    int i;
    for (i = 0; i < len1; i++) {
        if (name[i] < 'a' || name[i] > 'z') {
            ParseMLError(orgLineNo, "Identifier name %s needs to be lowercase alphabetic characters\n", name);
            return -1;
        }
    }
    return 0;
}
static char m_strC11Buff[ML_FILE_MAX_BYTES * 2];
static char* m_pStrC11Buff = m_strC11Buff;
static char m_strVarDecBuff[ML_INDENTIFIERS_MAX * 128];
static char* m_pStrVarDecBuff = m_strVarDecBuff;
static char m_strFuncDecBuff[ML_INDENTIFIERS_MAX * 4096];
static char* m_pStrFuncDecBuff = m_strFuncDecBuff;
static int m_nIndentifyNum;
static int m_nStmtNum;
static char* m_pParamList[ML_INDENTIFIERS_MAX];
static int SplitFuncDefArgs(char* pParamList[], char* strParams) {
    char* token;
    token = strtok(strParams, " ");
    int paramNum = 0;
    while (token != NULL) {
        pParamList[paramNum] = token;
        token = strtok(NULL, " ");
        paramNum++;
    }
    return paramNum;
}
static int SplitFuncCallArgs(char* pParamList[], char* strParams) {
    char* token;
    token = strtok(strParams, ",");
    int paramNum = 0;
    while (token != NULL) {
        pParamList[paramNum] = token;
        token = strtok(NULL, ",");
        paramNum++;
    }
    return paramNum;
}
static SIDENTIFY* identify_name_find(const char* name) {
    int i;
    for (i = 0; i < m_nIndentifyNum; i++) {
        if (strcmp(m_slistIDs[i].id.pName, name) == 0) {
            return &m_slistIDs[i];
        }
    }
    return NULL;
}
static SIDENTIFY* var_name_find(const char* name, int maxOrgLineNo) {
    int i;
    if (strStartsWith(name, "arg") == 0) {
        return (SIDENTIFY*)-1;
    }
    for (i = 0; i < m_nIndentifyNum; i++) {
        if (m_slistIDs[i].idType != eID_var)
            continue;
        if (m_slistIDs[i].id.var.pSDecStmt->pStartLine->orgLineNo >= maxOrgLineNo) {
            break;
        }
        if (strcmp(m_slistIDs[i].id.pName, name) == 0) {
            return &m_slistIDs[i];
        }
    }
    return NULL;
}
static SIDENTIFY* func_name_find(const char* name, int maxOrgLineNo) {
    int i;
    for (i = 0; i < m_nIndentifyNum; i++) {
        if (m_slistIDs[i].idType != eID_func)
            continue;
        if (m_slistIDs[i].id.func.pSDecStmt->pStartLine->orgLineNo >= maxOrgLineNo) {
            break;
        }
        if (strcmp(m_slistIDs[i].id.pName, name) == 0) {
            return &m_slistIDs[i];
        }
    }
    return NULL;
}
// Adding new statement (such as variable declaration, function call, or print statement) to the ML-to-C11 conversion program
static SSTATEMENT1* ml_stmt_add_com(SLINE1* pSLine1, const char* name, const char* expression, ESTMT_TYPE eStmtType, BOOL bFuncBody) {
    char* pLineStart = pSLine1->pLineStart;
    if (m_nStmtNum >= ML_FILE_ROW_NUMX) {
        ParseMLError(pSLine1->orgLineNo, "The number of executed statements exceeds the limit\n");
        return NULL;
    }
    if (identify_name_check(pSLine1->orgLineNo, name, eStmtType) != 0) {
        return NULL;
    }
    int nameLen = (int)strlen(name);
    memcpy(pLineStart, name, nameLen + 1);
    char* pExpr = pLineStart + nameLen + 1;
    if (expression) {
        int exprLen = (int)strlen(expression) + 1;
        int i;
        char* pTmp = pExpr;
        for (i = 0; i < exprLen; i++, expression++) {
            if (eStmtType == eStmtFuncDec) {
                if (*expression == '\t' || *expression == '\n')
                    continue;
            } else {
                if (*expression == ' ' || *expression == '\t' || *expression == '\n')
                    continue;
            }
            *pTmp++ = *expression;
        }
    } else {
        pExpr = NULL;
    }
    SSTATEMENT1* pSStmt1 = &m_sListStmts[m_nStmtNum];
    pSStmt1->pName = pLineStart;
    pSStmt1->pExpr = pExpr;
    pSStmt1->pStartLine = pSLine1;
    pSStmt1->eStmtType = eStmtType;
    pSStmt1->bFuncBody = bFuncBody;
    pSStmt1->LineNum = 1;
    m_nStmtNum++;
    return pSStmt1;
}
static int ml_stmt_add_print1(SLINE1* pSLine1, const char* name, const char* expression, BOOL bFuncBody) {
    SSTATEMENT1* pSStmt1 = ml_stmt_add_com(pSLine1, name, expression, eStmtPrint, bFuncBody);
    if (pSStmt1 == NULL)
        return -1;
    return 0;
}
static int ml_stmt_add_varset(SLINE1* pSLine1, const char* pVarName, const char* expression, BOOL bFuncBody) {
    SSTATEMENT1* pSStmt1 = ml_stmt_add_com(pSLine1, pVarName, expression, eStmtVarSet, bFuncBody);
    if (pSStmt1 == NULL)
        return -1;
    if (strcmp(pVarName, "print") == 0 || strcmp(pVarName, "function") == 0 || strcmp(pVarName, "return") == 0) {
        ParseMLError(pSLine1->orgLineNo, "Keywords cannot be used as variable names\n");
        return -1;
    }
    SIDENTIFY* pSIdentify = identify_name_find(pVarName);
    if (pSIdentify == NULL) {
        if (m_nIndentifyNum >= ML_INDENTIFIERS_MAX) {
            ParseMLError(pSLine1->orgLineNo, "The number of indentifiers exceeds the limit\n");
            return -1;
        }
        pSIdentify = &m_slistIDs[m_nIndentifyNum];
        pSIdentify->idType = eID_var;
        pSIdentify->id.var.pName = pSStmt1->pName;
        pSIdentify->id.var.pSDecStmt = pSStmt1;
        m_nIndentifyNum++;
    }
    return 0;
}
static int ml_stmt_add_return(SLINE1* pSLine1, const char* name, const char* expression) {
    SSTATEMENT1* pSStmt1 = ml_stmt_add_com(pSLine1, name, expression, eStmtBodyRet, 1);
    if (pSStmt1 == NULL)
        return -1;
    return 0;
}
static int ml_stmt_add_func_call(SLINE1* pSLine1, char* pFuncName, char* expression, BOOL bFuncBody) {
    SSTATEMENT1* pSStmt1 = ml_stmt_add_com(pSLine1, pFuncName, expression, eStmtFuncCall, bFuncBody);
    if (pSStmt1 == NULL)
        return -1;
    if (strcmp(pFuncName, "print") == 0 || strcmp(pFuncName, "function") == 0 || strcmp(pFuncName, "return") == 0) {
        ParseMLError(pSLine1->orgLineNo, "Keywords cannot be used as function names\n");
        return -1;
    }
    SIDENTIFY* pSIdentify = identify_name_find(pFuncName);
    if (pSIdentify == NULL) {
        ParseMLError(pSLine1->orgLineNo, "This function %s is undefined\n", pFuncName);
        return -1;
    }
    pSStmt1->pSFunc1 = &pSIdentify->id.func;
    int argNum = SplitFuncCallArgs(m_pParamList, expression);
    if (argNum != pSIdentify->id.func.paramNum) {
        ParseMLError(pSLine1->orgLineNo, "The number of function parameters does not match the definition\n");
        return -1;
    }
    return 0;
}
static int ml_stmt_add_func_def(SLINE1* pSLine1, char* pFuncName, char* expression, int bodyLinesNum) {
    int paramNum = 0;
    char bak_expression[512];
    strcpy(bak_expression,expression);
    if (expression[0] != '\0') {
        paramNum = SplitFuncDefArgs(m_pParamList, expression);
        if (paramNum < 0) {
            ParseMLError(pSLine1->orgLineNo, "Function parameter format error\n");
            return -1;
        }
        int i;
        for (i=0;i<paramNum;i++) {
            if(identify_name_check(pSLine1->orgLineNo,m_pParamList[i],eStmtFuncDec) != 0){
                ParseMLError(pSLine1->orgLineNo, "Function %s parameter %s format error\n",pFuncName,m_pParamList[i]);
                return -1;
            }
        }
    }
    SSTATEMENT1* pSStmt1 = ml_stmt_add_com(pSLine1, pFuncName, bak_expression, eStmtFuncDec, 1);
    if (pSStmt1 == NULL)
        return -1;
    pSStmt1->LineNum = 1 + bodyLinesNum;
    if (strcmp(pFuncName, "print") == 0 || strcmp(pFuncName, "function") == 0 || strcmp(pFuncName, "return") == 0) {
        ParseMLError(pSLine1->orgLineNo, "Keywords cannot be used as variable names\n");
        return -1;
    }
    SIDENTIFY* pSIdentify = identify_name_find(pFuncName);
    if (pSIdentify) {
        ParseMLError(pSLine1->orgLineNo, "Function %s repetition definition\n", pFuncName);
        return -1;
    }
    if (m_nIndentifyNum >= ML_INDENTIFIERS_MAX) {
        ParseMLError(pSLine1->orgLineNo, "The number of indentifiers exceeds the limit\n");
        return -1;
    }
    pSIdentify = &m_slistIDs[m_nIndentifyNum];
    pSIdentify->idType = eID_func;
    pSIdentify->id.func.pName = pSStmt1->pName;
    pSIdentify->id.func.pSDecStmt = pSStmt1;
    pSIdentify->id.func.paramNum = paramNum;
    pSStmt1->pSFunc1 = &pSIdentify->id.func;
    m_nIndentifyNum++;
    return 0;
}
static int ml_lines_scan_print(char name[], char expression[], char* pLineStart, SLINE1* pSLine1, BOOL bFuncBody) {
    name[0] = 0;
    expression[0] = 0;
    if (strStartsWith(pLineStart, "print ") == 0) {
        if (sscanf(pLineStart, "print %[^\n]", expression) != 1) {
            ParseMLError(pSLine1->orgLineNo, "print format error\n");
            return -1;
        }
        return ml_stmt_add_print1(pSLine1, "print", expression, bFuncBody);
    }
    return 1;
}
static void StripString(char* name){
    int i;
    int len1 = strlen(name);
    char strtmp[len1+1];
    for (i=0;i<len1;i++) {
        if(name[i] == 't' || name[i] == ' '){
            continue;
        }
        break;
    }
    int j = i;
    for (i=0;i<len1;i++) {
        if(name[len1-i-1] == '\n' || name[len1-i-1] == ' ' || name[len1-i-1] == '\t'){
            name[len1-i-1] = 0;
            continue;
        }
        break;
    }
    strcpy(strtmp,&name[j]);
    strcpy(name,strtmp);
}
static int ml_lines_scan_varset(char name[], char expression[], char* pLineStart, SLINE1* pSLine1, BOOL bFuncBody) {
    name[0] = 0;
    expression[0] = 0;
    char* pFind = strstr(pLineStart,"<-");
    if(pFind == NULL){
        return 1;
    }
    *pFind = 0;
    pFind += 2;
    strcpy(name,pLineStart);
    StripString(name);
    strcpy(expression,pFind);
    StripString(expression);
    return ml_stmt_add_varset(pSLine1, name, expression, bFuncBody);
}
static int ml_lines_scan_funcall(char name[], char expression[], char* pLineStart, SLINE1* pSLine1, BOOL bFuncBody) {
    name[0] = 0;
    expression[0] = 0;
    char* pFind = strstr(pLineStart, "(");
    if (pFind == NULL) {
        ParseMLError(pSLine1->orgLineNo, "Invalid statement %s\n", pLineStart);
        return -1;
    } else {
        *pFind = 0;
        pFind++;
        char* pFind2 = strchr(pLineStart, ' ');
        if (pFind2 != NULL) {
            *pFind2 = 0;
        }
        pFind2 = strchr(pFind, ')');
        if (pFind2 == NULL) {
            ParseMLError(pSLine1->orgLineNo, "Function call parameter format error\n");
            return -1;
        } else {
            *pFind2 = 0;
        }
        strcpy(name, pLineStart);
        strcpy(expression, pFind);
        return ml_stmt_add_func_call(pSLine1, name, expression, bFuncBody);
    }
}
static int ml_lines_scan_return(char name[], char expression[], char* pLineStart, SLINE1* pSLine1) {
    name[0] = 0;
    expression[0] = 0;
    if (sscanf(pLineStart, "return %[^\n]", expression) == 1) {
        return ml_stmt_add_return(pSLine1, "return", expression);
    }
    return 1;
}
static int ml_lines_scan_funcdef(char name[], char expression[], char* pLineStart, SLINE1* pSLine1, int i, int nLineNumML) {
    int j;
    name[0] = 0;
    expression[0] = 0;
    int bodyLinesNum = 0;
    if (sscanf(pLineStart, "function %s %[^\n]", name, expression) == 2) {
        bodyLinesNum = 0;
    } else if (sscanf(pLineStart, "function %s\n", name) == 1) {
        bodyLinesNum = 0;
    } else {
        ParseMLError(pSLine1->orgLineNo, "print format error\n");
        return -1;
    }
    SLINE1* pStatement;
    pStatement = pSLine1 + 1;
    for (j = i + 1; j < nLineNumML; j++, pStatement++) {
        pLineStart = pStatement->pLineStart;
        if (*pLineStart != '\t') {
            break;
        }
        pLineStart ++;
        if (strStartsWith(pLineStart, "function ") == 0) {
            ParseMLError(pStatement->orgLineNo, "Functions cannot be defined inside the function body anymore\n");
            return -1;
        } else if (strStartsWith(pLineStart, "arg") == 0) {
            ParseMLError(pSLine1->orgLineNo, "The name of variable arg[x] are reserved as command-line parameters for ML programs\n");
            continue;
        } else if (strStartsWith(pLineStart, "return ") == 0) {
            bodyLinesNum++;
            break;
        }
        bodyLinesNum++;
    }
    if (bodyLinesNum == 0) {
        ParseMLError(pSLine1->orgLineNo, "The function body is empty\n");
        return -1;
    }
    if(ml_stmt_add_func_def(pSLine1, name, expression, bodyLinesNum) != 0)
        return -1;
    pStatement = pSLine1 + 1;
    for (j = 0; j < bodyLinesNum; j++, pStatement++) {
        pLineStart = pStatement->pLineStart + 1;
        if (ml_lines_scan_print(name, expression, pLineStart, pStatement, 1) <= 0) {
            continue;
        } else if (ml_lines_scan_varset(name, expression, pLineStart, pStatement, 1) <= 0) {
            continue;
        } else if (ml_lines_scan_return(name, expression, pLineStart, pStatement) <= 0) {
            break;
        }else if(ml_lines_scan_funcall(name, expression, pLineStart, pStatement, 1) <= 0) {
            continue;
        }
    }
    return bodyLinesNum;
}
static int ml_lines_scan(SLINE1* listLines, int nLineNumML) {
    int i;
    char name[256];
    char expression[2048];
    fprintf(stderr, "@ Debug: ParseML LineNum:%d\n", m_nMLOrgLineNum);
    m_bMLParseError = 0;
    m_bConvC11Error = 0;
    SLINE1* pSLine1 = listLines;
    for (i = 0; i < nLineNumML; i++, pSLine1++) {
        char* pLineStart = pSLine1->pLineStart;
        if (strStartsWith(pLineStart, "return ") == 0) {
            ParseMLError(pSLine1->orgLineNo, "The keyword 'return' must be written at the end of the function\n");
            continue;
        }
        if (strStartsWith(pLineStart, "arg") == 0) {
            ParseMLError(pSLine1->orgLineNo, "The name of variable arg[x] are reserved as command-line parameters for ML programs\n");
            continue;
        }
        if (strStartsWith(pLineStart, "\targ") == 0) {
            ParseMLError(pSLine1->orgLineNo, "The name of variable arg[x] are reserved as command-line parameters for ML programs\n");
            continue;
        }
        if (strStartsWith(pLineStart, "function ") == 0) {
            int bodyLinesNum = ml_lines_scan_funcdef(name, expression, pLineStart, pSLine1, i, nLineNumML);
            if (bodyLinesNum <= 0)
                continue;
            pSLine1 += bodyLinesNum;
            i += bodyLinesNum;
            continue;
        }
        if (pLineStart[0] == '\t') {
            ParseMLError(pSLine1->orgLineNo, "Invalid statement\n");
            continue;
        }
        if (ml_lines_scan_print(name, expression, pLineStart, pSLine1, 0) <= 0) {
            continue;
        } else if (ml_lines_scan_varset(name, expression, pLineStart, pSLine1, 0) <= 0) {
            continue;
        } else if (ml_lines_scan_funcall(name, expression, pLineStart, pSLine1, 0) <= 0) {
            continue;
        }
    }
    if (m_bMLParseError || m_bConvC11Error) {
        exit(2);
    }
    return 0;
}
static int StrToDouble(double* outDbl, const char* str) {
    char* end;
    double val = strtod(str, &end);
    if (end == str || *end != '\0') {
        return -1;
    }
    if (errno == EINVAL) {
        return -1;
    }
    *outDbl = val;
    return 0;
}
static int ExprToC11Str_Dbl(char* c11Out, char* pInExpr) {
    int len1;
    double dtmp;
    if (StrToDouble(&dtmp, pInExpr) == 0) {
        len1 = sprintf(c11Out, "%s", pInExpr);
        return len1;
    }
    return -1;
}
static char m_strBodyVar[ML_INDENTIFIERS_MAX][16];
static int m_nBodyVarNum;
// Manage local variables within a function body during code parsing or generation
static void body_var_name_add(const char* pVarName,SLINE1* pSLine1){
    if(m_nBodyVarNum >= ML_INDENTIFIERS_MAX){
        ConvC11Error(pSLine1->orgLineNo, "The number of local variables in the function exceeds 50\n");
        return;
    }
    strcpy(m_strBodyVar[m_nBodyVarNum],pVarName);
    m_nBodyVarNum++;
}
static BOOL body_var_name_find(const char* pVarName){
    int i;
    for (i=0;i<m_nBodyVarNum;i++) {
        if (strcmp(m_strBodyVar[i],pVarName) == 0) {
            return 1;
        }
    }
    return 0;
}
static void body_var_name_clear(){
    m_nBodyVarNum = 0;
}
// Generate C11 code from a variable expression in a ML programming language
static int ExprToC11Str_Var(char* c11Out, char* pInExpr, SLINE1* pSLine1, BOOL bFuncBody,int lCount,int rCount) {
    int len1;
    char* pVarName = pInExpr;
    if (identify_name_check(pSLine1->orgLineNo, pVarName, eStmtVarSet) != 0) {
        ConvC11Error(pSLine1->orgLineNo, "Identifier %s format error\n", pVarName);
        return -1;
    }
    SIDENTIFY* pSIdentify1 = var_name_find(pVarName, pSLine1->orgLineNo);
    
    if(pSIdentify1){
        len1 = sprintf(c11Out, "%s", pVarName);
        return len1;
    }
    if(bFuncBody){
    
        if(body_var_name_find(pVarName)){
        if(lCount>0){
          char countL[10];  // Buffer to store the parentheses
          int i =0;
          for(;i<lCount;i++)
            countL[i]='(';  // Add 'lCount' opening parentheses
          countL[i]='\0';
          len1=sprintf(c11Out,"%s %s",countL,pVarName);
          return len1; 
    }
    if(rCount>0){
    char countR[10];
    int i =0;
    for(;i<rCount;i++)
      countR[i]=')';    // Add 'rCount' closing parentheses
    countR[i]='\0';
      len1=sprintf(c11Out,"%s %s",pVarName,countR);
      return len1;
    }
            len1 = sprintf(c11Out, "%s", pVarName);
            return len1;
        }
    }
    if (pSIdentify1 == NULL) {
        len1 = sprintf(c11Out, "0");
        return len1;
    }
    return -1;
}
static int ExprToC11Str_FuncCall(char* c11Out, char* pInExpr, char* pFind, SLINE1* pSLine1,BOOL bFuncBody) {
    int len1;
    //char* bak_c11Out = c11Out;
    *pFind = 0;
    pFind++;
    char* pFuncName = pInExpr;
    if (identify_name_check(pSLine1->orgLineNo, pFuncName, eStmtFuncCall) != 0) {
        ConvC11Error(pSLine1->orgLineNo, "Identifier %s format error\n", pFuncName);
        return -1;
    }
    SIDENTIFY* pSIdentify1 = func_name_find(pFuncName, pSLine1->orgLineNo);
    if (pSIdentify1 == NULL) {
        ConvC11Error(pSLine1->orgLineNo, "Function %s undefined\n", pFuncName);
        return -1;
    } else {
        SFUNC1* func1 = &pSIdentify1->id.func;
        char* pFind2 = strchr(pFind, ')');
        if (pFind2 == NULL) {
            ConvC11Error(pSLine1->orgLineNo, "Function %s call format error\n", pFuncName);
            return -1;
        }
        *pFind2 = 0;
        char* pArgs = pFind;
        int argNum = SplitFuncCallArgs(m_pParamList, pArgs);
        if (argNum != func1->paramNum) {
            ConvC11Error(pSLine1->orgLineNo, "Inconsistent number and definition of function %s call parameters\n", pFuncName);
            return -1;
        }
        if (argNum == 0) {
            len1 = sprintf(c11Out, "%s()", pFuncName);
            return len1;
        }
        int lenTot = 0;
        len1 = sprintf(c11Out, "%s(", pFuncName);
        lenTot += len1;
        c11Out += len1;
        for (int i = 0; i < argNum; i++) {
            if (i > 0) {
                len1 = sprintf(c11Out, ", ");
                lenTot += len1;
                c11Out += len1;
            }
            char* pVarName = m_pParamList[i];
            len1 = ExprToC11Str_Dbl(c11Out, pVarName);
            if (len1 < 0) {
                len1 = ExprToC11Str_Var(c11Out, pVarName, pSLine1,bFuncBody,0,0);
                if (len1 <= 0) {
                    ConvC11Error(pSLine1->orgLineNo, "Function %s call parameter %s format error\n", pFuncName, pVarName);
                    return -1;
                }
            }
            lenTot += len1;
            c11Out += len1;
        }
        len1 = sprintf(c11Out, ")");
        lenTot += len1;
        c11Out += len1;
        return lenTot;
    }
    return -1;
}
static int ExprToC11Str_Single(char* c11Out, char* pInExpr, SSTATEMENT1* pSStmt1,BOOL bFuncBody,int lCount,int rCount) {
    int len1;
    SLINE1* pSLine1 = pSStmt1->pStartLine;
    len1 = ExprToC11Str_Dbl(c11Out, pInExpr);
    if (len1 > 0) {
        return len1;
    } else {
        char* pFind = strchr(pInExpr, '(');
        if (pFind == NULL ) {
            return ExprToC11Str_Var(c11Out, pInExpr, pSLine1,bFuncBody,lCount,rCount);
           
        } 
        else {
            return ExprToC11Str_FuncCall(c11Out, pInExpr, pFind, pSLine1,bFuncBody);
        }
        
    }
    return -1;
}
static int ExprToC11Str_FunCallMutiParam(char* c11Out, char* pInExpr, SSTATEMENT1* pSStmt1,BOOL bFuncBody) {
    int len1;
    SFUNC1* pSFunc1 = pSStmt1->pSFunc1;
    SLINE1* pSLine1 = pSStmt1->pStartLine;
    int lenTot = 0;
    int i;
    int argNum = SplitFuncCallArgs(m_pParamList, pInExpr);
    assert(argNum == pSFunc1->paramNum);
    for (i=0;i<argNum;i++) {
        if (i > 0) {
            len1 = sprintf(c11Out, ", ");
            lenTot += len1;
            c11Out += len1;
        }
        char* pVarName = m_pParamList[i];
        len1 = ExprToC11Str_Dbl(c11Out, pVarName);
        if (len1 < 0) {
            len1 = ExprToC11Str_Var(c11Out, pVarName, pSLine1,bFuncBody,0,0);
            if (len1 <= 0) {
                ConvC11Error(pSLine1->orgLineNo, "Function %s call parameter %s format error\n", pSStmt1->pName, pVarName);
                return -1;
            }
        }
        lenTot += len1;
        c11Out += len1;
    }
    return lenTot;
}
static int ExprToC11Str(char* c11Out, SSTATEMENT1* pSStmt1,BOOL bFuncBody) {
    SLINE1* pSLine1 = pSStmt1->pStartLine;
    char* pInExpr = pSStmt1->pExpr;
    int exprLen = (int)strlen(pSStmt1->pExpr);
    int lCount=0,rCount=0;
    if (exprLen <= 0) {
        return 0;
    }
    char tmp[20];
        int j = 0,k=0;
    // char* bak_c11Out = c11Out;
    int len1;
    int TotLen = 0;
    int i;
    int opindex;
    BOOL bSingle = 1;
Next1:
    opindex = -1;
    for (i = 0; i < exprLen; i++) {
        if (pInExpr[i] == '+' || pInExpr[i] == '-' || pInExpr[i] == '*' || pInExpr[i] == '/') {
            opindex = i;
            break;
        }
    }
    if (opindex < 0) {
        pInExpr[exprLen] = 0;
        if(bSingle){
            bSingle = 0;
            if(pSStmt1->eStmtType == eStmtFuncCall){
                if(pSStmt1->pSFunc1->paramNum > 1){
                    len1 = ExprToC11Str_FunCallMutiParam(c11Out, pInExpr, pSStmt1,bFuncBody);
                    return len1;
                }
            }
        }
        char * rLastFind = strchr(pInExpr,')');
        if(rLastFind != NULL && bFuncBody)
        {
         j=k=0;
         for(;pInExpr[k]!=0;k++)
         {
          if(pInExpr[k]==')')
            rCount++;
            else
            tmp[j++]=pInExpr[k];
         }
         tmp[j]='\0';
         len1=ExprToC11Str_Single(c11Out, tmp, pSStmt1,bFuncBody,lCount,rCount);
         
        }else
        len1 = ExprToC11Str_Single(c11Out, pInExpr, pSStmt1,bFuncBody,0,0);
        return len1;
    } else {
        bSingle = 0;
        char op;
        
        op = pInExpr[opindex];
        pInExpr[opindex] = 0;
        if(bFuncBody){
        j=k=0;
        for(;pInExpr[k]!=0;k++){
          if(pInExpr[k]=='(')
            lCount++;
            else if(pInExpr[k]==')')
            rCount++;
            else
            tmp[j++]=pInExpr[k];
        }
        
        tmp[i]='\0';
        len1 = ExprToC11Str_Single(c11Out, tmp, pSStmt1,bFuncBody,lCount,rCount);
        }else
        len1 = ExprToC11Str_Single(c11Out, pInExpr, pSStmt1,bFuncBody,0,0);
        if (len1 <= 0) {
            return -1;
        }
        c11Out += len1;
        TotLen += len1;
        c11Out[0] = ' ';
        c11Out[1] = op;
        c11Out[2] = ' ';
        c11Out += 3;
        TotLen += 3;
        pInExpr += opindex + 1;
        exprLen = (int)strlen(pInExpr);
        lCount=rCount=0;
        goto Next1;
    }
    pInExpr[exprLen] = 0;
    ConvC11Error(pSLine1->orgLineNo, "Expression %s format error\n", pInExpr);
    return -1;
}
static int c11_conv_print(SSTATEMENT1* pSStmt1, char* pC11Buff,BOOL bFuncBody) {
    int len1 = 0;
    char c11Expression[512];
    len1 = ExprToC11Str(c11Expression, pSStmt1,bFuncBody);
    if (len1 <= 0) {
        return -1;
    }
    pSStmt1->pC11Statement = pC11Buff;
    len1 = sprintf(pC11Buff, "\t_fin_print(%s);\n", c11Expression);
    return len1;
}
static int c11_conv_return(SSTATEMENT1* pSStmt1, char* pC11Buff) {
    int len1 = 0;
    char c11Expression[512];
    len1 = ExprToC11Str(c11Expression, pSStmt1,1);
    if (len1 <= 0) {
        return -1;
    }
    pSStmt1->pC11Statement = pC11Buff;
    len1 = sprintf(pC11Buff, "\treturn %s;\n", c11Expression);
    return len1;
}
static int c11_conv_funcall(SSTATEMENT1* pSStmt1, char* pC11Buff,BOOL bFuncBody) {
    int len1 = 0;
    char c11Expression[512];
    len1 = ExprToC11Str(c11Expression, pSStmt1,bFuncBody);
    if (len1 <= 0) {
        return -1;
    }
    pSStmt1->pC11Statement = pC11Buff;
    len1 = sprintf(pC11Buff, "\t%s(%s);\n", pSStmt1->pName,c11Expression);
    return len1;
}
static int c11_conv_varset(SSTATEMENT1* pSStmt1, char* pC11Buff,BOOL bFuncBody) {
    int len1 = 0;
    int totlen = 0;
    if(bFuncBody){
        if(body_var_name_find(pSStmt1->pName) == 0){
            len1 = sprintf(pC11Buff, "\tdouble %s=0;\n", pSStmt1->pName);
            pSStmt1->pC11VarDec = pC11Buff;
            pC11Buff += len1;
            totlen += len1;
            body_var_name_add(pSStmt1->pName,pSStmt1->pStartLine);
        }
    }else{
        if(var_name_find(pSStmt1->pName,pSStmt1->pStartLine->orgLineNo) == NULL){
            len1 = sprintf(m_pStrVarDecBuff, "static double %s=0;\n", pSStmt1->pName);
            pSStmt1->pC11VarDec = m_pStrVarDecBuff;
            m_pStrVarDecBuff += len1;

        }
    }
    char c11Expression[512];
    len1 = ExprToC11Str(c11Expression, pSStmt1,bFuncBody);
    if (len1 <= 0) {
        return -1;
    }
    pSStmt1->pC11Statement = pC11Buff;
    len1 = sprintf(pC11Buff, "\t%s = %s;\n", pSStmt1->pName, c11Expression);
    totlen += len1;
    return totlen;
}
static int c11_conv_funcdec(SSTATEMENT1* pSStmt1) {
    int len1 = 0;
    int i;
    SFUNC1* pSFunc1 = pSStmt1->pSFunc1;
    body_var_name_clear();
    pSStmt1->pC11VarDec = m_pStrFuncDecBuff;
    if (pSFunc1->paramNum == 0) {
        len1 = sprintf(m_pStrFuncDecBuff, "static double %s(){\n", pSStmt1->pName);
        m_pStrFuncDecBuff += len1;
    } else {
        int paramNum = SplitFuncDefArgs(m_pParamList, pSStmt1->pExpr);
        assert(paramNum == pSFunc1->paramNum);
        len1 = sprintf(m_pStrFuncDecBuff, "static double %s(", pSStmt1->pName);
        m_pStrFuncDecBuff += len1;
        for (int i = 0; i < paramNum; i++) {
            if (i > 0) {
                len1 = sprintf(m_pStrFuncDecBuff, ",double %s", m_pParamList[i]);
            } else {
                len1 = sprintf(m_pStrFuncDecBuff, "double %s", m_pParamList[i]);
            }
            body_var_name_add(m_pParamList[i],pSStmt1->pStartLine);
            m_pStrFuncDecBuff += len1;
        }
        len1 = sprintf(m_pStrFuncDecBuff, "){\n");
        m_pStrFuncDecBuff += len1;
    }
    SSTATEMENT1* bodyStmt1 = pSStmt1 + 1;
    int bodyLinesNum = pSStmt1->LineNum - 1;
    for (i = 0; i < bodyLinesNum; i++, bodyStmt1++) {
        assert(bodyStmt1->bFuncBody);
        len1 = -1;
        switch (bodyStmt1->eStmtType) {
        case eStmtPrint:
            len1 = c11_conv_print(bodyStmt1, m_pStrFuncDecBuff,1);
            break;
        case eStmtVarSet:
            len1 = c11_conv_varset(bodyStmt1, m_pStrFuncDecBuff,1);
            break;
        case eStmtBodyRet:
            len1 = c11_conv_return(bodyStmt1, m_pStrFuncDecBuff);
            break;
        case eStmtFuncCall:
            len1 = c11_conv_funcall(bodyStmt1, m_pStrFuncDecBuff,1);
            break;
        default:
            ConvC11Error(bodyStmt1->pStartLine->orgLineNo,"Statement that cannot be converted\n");
            break;
        }
        if(len1 > 0){
            m_pStrFuncDecBuff += len1;
        }
    }
    body_var_name_clear();
    len1 = sprintf(m_pStrFuncDecBuff, "}\n");
    m_pStrFuncDecBuff += len1;
    return 0;
}
static int ml_trans_c11() {
    int i;
    int len1;
    m_bMLParseError = 0;
    m_bConvC11Error = 0;
    SSTATEMENT1* pSStmt1 = m_sListStmts;
    m_pStrC11Buff = m_strC11Buff;
    for (i = 0; i < m_nStmtNum; ) {
        len1 = -1;
        switch (pSStmt1->eStmtType) {
        case eStmtPrint:
            len1 = c11_conv_print(pSStmt1, m_pStrC11Buff,pSStmt1->bFuncBody);
            i++;pSStmt1++;
            break;
        case eStmtVarSet:
            len1 = c11_conv_varset(pSStmt1, m_pStrC11Buff,pSStmt1->bFuncBody);
            i++;pSStmt1++;
            break;
        case eStmtFuncDec:
            c11_conv_funcdec(pSStmt1);
            i += pSStmt1->LineNum;
            pSStmt1 += pSStmt1->LineNum;
            break;
        case eStmtFuncCall:
            len1 = c11_conv_funcall(pSStmt1, m_pStrC11Buff,pSStmt1->bFuncBody);
            i++;pSStmt1++;
            break;
        default:
            ConvC11Error(pSStmt1->pStartLine->orgLineNo,"Statement that cannot be converted\n");
            i++;pSStmt1++;
            break;
        }
        if (len1 > 0) {
            m_pStrC11Buff += len1;
        }
    }
    if (m_bMLParseError || m_bConvC11Error) {
        exit(2);
    }
    return 0;
}
// Managing the process of loading, scanning, and converting ML file into C11 source file
static int ml_file_parse(const char* pathML) {
    int LineNumML = 0;
    if(ml_file_load(&LineNumML, pathML) != 0)
        return -1;
    if(ml_lines_scan(m_listLines, LineNumML) != 0)
        return -1;
    if(ml_trans_c11() != 0)
        return -1;
    return 0;
}
// Function to generate C filename from the given ML file path
void pathML_to_cFileName(char cFileName[],const char* pathML){
    char pathMLTmp[512];
    strcpy(pathMLTmp,pathML);
    char* pMLName = strrchr(pathMLTmp,'/');
    if(pMLName == NULL){
        pMLName = pathMLTmp;
    }
    char* pFind = strchr(pMLName,'.');
    if(pFind){
        *pFind = 0;
    }
    sprintf(cFileName,"ml-%d",getpid());    // Generate process-ID of the file
}
// Generate and write a C source file from the contents and structure derived from the ML file
static int ml_write_c11(const char* cFileName) {
    char c11FilePath[512];
    strcpy(c11FilePath,cFileName);
    strcat(c11FilePath,".c");
    int len1;
    DebugPrintf("Writing to file: %s\n", c11FilePath);  // Log the filename
    FILE* cfile = fopen(c11FilePath,"w+");
    if(cfile == NULL){
        FatalPrintf("Create file %s failed\n",c11FilePath);
        return -1;
    }
    DebugPrintf("File %s created successfully\n", c11FilePath);
    len1 = strlen(constC11_Header);
    if(fwrite(constC11_Header,len1,1,cfile) != 1){
        FatalPrintf("Write file %s failed\n",c11FilePath);
        return -1;
    }
    len1 = m_pStrVarDecBuff - m_strVarDecBuff;
    if(len1){
        if(fwrite(m_strVarDecBuff,len1,1,cfile) != 1){
            FatalPrintf("Write file %s failed\n",c11FilePath);
            return -1;
        }
    }
    len1 = m_pStrFuncDecBuff - m_strFuncDecBuff;
    if(len1){
        if(fwrite(m_strFuncDecBuff,len1,1,cfile) != 1){
            FatalPrintf("Write file %s failed\n",c11FilePath);
            return -1;
        }
    }
    len1 = strlen(constC11_mainStart);
    if(fwrite(constC11_mainStart,len1,1,cfile) != 1){
        FatalPrintf("Write file %s failed\n",c11FilePath);
        return -1;
    }
    len1 = m_pStrC11Buff - m_strC11Buff;
    if(len1){
        if(fwrite(m_strC11Buff,len1,1,cfile) != 1){
            FatalPrintf("Write file %s failed\n",c11FilePath);
            return -1;
        }
    }
    len1 = strlen(constC11_mainEnd);
    if(fwrite(constC11_mainEnd,len1,1,cfile) != 1){
        FatalPrintf("Write file %s failed\n",c11FilePath);
        return -1;
    }
    fclose(cfile);
    return 0;
}
// Deletes the .c source file generated during the conversion from ML to C
static void removeC11File(const char* cFileName){
    char runStr[512];
    sprintf(runStr,"rm %s.c",cFileName);
    system(runStr);
}
// Compile the generated C code into an executable
static int ml_compile_c11(const char* cFileName){
    char complStr[1024];
    sprintf(complStr,"gcc -std=c11 -o %s %s.c -lm",cFileName,cFileName);
    DebugPrintf("Compile C11 program: %s\n", complStr);
    int rst = system(complStr);
    removeC11File(cFileName);
    if(rst != 0){
        FatalPrintf("C11 program compilation failed\n");
        return -1;
    }
    return 0;
}
// Deletes the compiled executable after the program has been run
static void removeRunC11(const char* cFileName){

    fprintf(stderr,"@ Debug: Cleaning up\n");

    char runStr[512];
    sprintf(runStr,"rm %s",cFileName);
    system(runStr);
}
// Execute the compiled program
static int ml_run_c11(const char* cFileName,int argc, char** argv){
    char runStr[1024];
    sprintf(runStr,"./%s",cFileName);
    int i;
    char strtmp[128];
    for (i=0;i<argc;i++) {
        sprintf(strtmp,"  %s",argv[i]);
        strcat(runStr,strtmp);
    }
    DebugPrintf("Run command: %s\n", runStr);
    int rst = system(runStr);
    removeRunC11(cFileName);
    if(rst != 0){
        FatalPrintf("C11 program failed to run\n");
        return -1;
    }
    return 0;
}
static int MLRunArgCheck(int argc, char** argv){
    int i;
    if(argc > ML_CMDARG_NUMX){
        FatalPrintf("The number of ML command line parameters exceeds the maximum limit\n");
        return -1;
    }
    for (i=0;i<argc;i++) {
        double tmp;
        if(StrToDouble(&tmp,argv[i]) != 0){
            FatalPrintf("Command line parameter %s format error\n",argv[i]);
            return -1;
        }
    }
    return 0;
}
int main(int argc, char** argv) {
    if (argc < 2) {
        FatalPrintf("Command line parameter format error\n");
        return -1;
    }
    const char* pathML = argv[1];
    argc -= 2;
    argv += 2;
    static char cFileName[128];
    pathML_to_cFileName(cFileName,pathML);
    if(MLRunArgCheck(argc,argv) != 0){
        return -1;
    }
    if(ml_file_parse(pathML) != 0)
        return -1;
    if(ml_write_c11(cFileName) != 0)
        return -1;
    if(ml_compile_c11(cFileName) != 0)
        return -1;
    return ml_run_c11(cFileName,argc,argv);
}
// References
// Anjalibo. (2024, August 16). How to Convert an Integer to a String in C? Retrieved from Geeksforgeeks: https://www.geeksforgeeks.org/how-to-convert-an-integer-to-a-string-in-c/
// Hall, J. (2022, April 30). Parsing data with strtok in C. Retrieved from Opensource: https://opensource.com/article/22/4/parsing-data-strtok-c