
package semant;
import ast.*;

import java.util.*;
import util.*;

public class TypeCheckVisitor extends SemanticVisitor {
    private SymbolTable vTable;
    private SymbolTable mTable;
    private ErrorHandler errorHandler;
    private String fileName;
    private String className;
    private String methodName;
    private String methodReturnType;
    private boolean inLoop;
    private Hashtable<String,ClassTreeNode> classMap;
    private int inLoopCounter = 0;
    
    public TypeCheckVisitor(SymbolTable v, SymbolTable m, ErrorHandler e,  
                           Hashtable<String,ClassTreeNode> cm) {
        vTable = v;
        mTable = m;
        errorHandler = e;
        classMap = cm;
    }

    public Object visit(Class_ node) {
        fileName = node.getFilename();
        className = node.getName();
        node.getMemberList().accept(this);
        return null;
    }

    public Object visit(MemberList node) {
        for (Iterator it = node.getIterator(); it.hasNext(); )
            ((Member)it.next()).accept(this);
        return null;
    }

    public Object visit(Field node) {
        if (node.getInit() != null) {
            String initType = (String) node.getInit().accept(this);
            node.getInit().setExprType(initType);
            String fieldType = node.getType();
            int lineNum = node.getLineNum();
            String name = node.getName();
            String initTypeNoArr = initType.replace("[]", "");
            String fieldTypeNoArr = fieldType.replace("[]", "");
            boolean fieldIsArr = fieldType.contains("[]");
            boolean initIsArr = initType.contains("[]");
            boolean fieldIsClass = classMap.containsKey(fieldTypeNoArr);
            boolean initIsClass = classMap.containsKey(initTypeNoArr);
            //checks if assigning a void to  the lhs
            if (initType.equals("void")) {
                errorHandler.register(errorHandler.SEMANT_ERROR, 
                                      fileName, 
                                      lineNum,
                                      "expression type '" + initType +  
                                      "' of field '" + name +
                                      "' cannot be void");
            } 
            //checks if either lhs or rhs is primitive and do not match
            else if ((fieldType.equals("boolean") 
                     || fieldType.equals("int")) 
                     && !fieldType.equals(initType)) {
                errorHandler.register(errorHandler.SEMANT_ERROR, 
                                      fileName, 
                                      lineNum,
                                      "expression type '" + initType +  
                                      "' of field '" + name +
                                      "' does not match declared type '" +
                                      fieldType + "'");
            } 
            //Check Class != Class || Class != null 
            else if (fieldIsClass && !initIsClass 
                    && !initType.equals("null")) {
                        errorHandler.register(
                            errorHandler.SEMANT_ERROR, 
                            fileName, 
                            lineNum,
                            "expression type '" 
                            + initType +  
                            "' of field '" + name +
                            "' does not conform to" + 
                            " declared type '" +
                            fieldType + "'");
            }
            //Check primitive[] != primitive[]  
            //!initType.equals("null") should check for null assignment
            else if (!fieldIsClass && !initIsClass 
                     && !fieldType.equals(initType) 
                     && !initType.equals("null")) {
                        errorHandler.register(
                            errorHandler.SEMANT_ERROR, 
                            fileName, 
                            lineNum,
                            "expression type '" 
                            + initType +  
                            "' of field '" + name +
                            "' does not conform to" + 
                            " declared type '" +
                            fieldType + "'");
            }
            //Check Class = Class || Class[] = Class[] 
            else if (fieldIsClass && initIsClass) {
                boolean isParent = false;
                for (ClassTreeNode parent = classMap.get(initTypeNoArr); 
                    parent != null && isParent == false; 
                    parent = parent.getParent()) {
                    if (parent.getASTNode().getName()
                    .equals(fieldTypeNoArr)) {
                        isParent = true;
                        break;
                    }
                }
                //Non-Conform Classes 
                if (!isParent && !initType.equals("null")) {
                    errorHandler.register(
                                          errorHandler.SEMANT_ERROR, 
                                          fileName, 
                                          lineNum,
                                          "expression type '" 
                                          + initType +  
                                          "' of field '" + name +
                                          "' does not conform to" + 
                                          " declared type '" +
                                          fieldType + "'");
                }
                //Classes conform, but array [] does not match 
                if (isParent && (fieldIsArr != initIsArr) && 
                    !initType.equals("null")) {
                    errorHandler.register(
                                          errorHandler.SEMANT_ERROR, 
                                          fileName, 
                                          lineNum,
                                          "expression type '" 
                                          + initType +  
                                          "' of field '" + name +
                                          "' does not conform to" + 
                                          " declared type '" +
                                          fieldType + "'");
                }
            }
        }
        return null; 
    }

    public Object visit(Method node) {
        int lineNum = node.getLineNum();
        methodName = node.getName();
        methodReturnType = node.getReturnType();
        vTable.enterScope();  
        //Check for class Main errors
        if (methodName.equals("main") && className.equals("Main")) {
            if (((ListNode) node.getFormalList()).getSize() > 0) {
                errorHandler.register(errorHandler.SEMANT_ERROR, 
                                          fileName, 
                                          lineNum,
                                          "'main' method in class " +
                                          "'Main' cannot take arguments");
            }
            if (!node.getReturnType().equals("void")) {
                errorHandler.register(errorHandler.SEMANT_ERROR, 
                                          fileName, 
                                          lineNum,
                                          "'main' method in class "+
                                          "'Main' must be void");
            }
        }
        //Goes through method arguments to check for type of each arg
        for (Iterator it = node.getFormalList().getIterator();
                                                 it.hasNext();) {
            Formal f = (Formal) it.next();
            lineNum = f.getLineNum();
            String name = f.getName();
            String type = f.getType();
            String checkType = type.replace("[]", "");
            boolean noError = true;
            boolean unknownType = false;
            //check if formal type exists
            if ((!checkType.equals("boolean") && !checkType.equals("int")) 
            && !classMap.containsKey(checkType)) {
                    unknownType = true;
                    errorHandler.register(errorHandler.SEMANT_ERROR, 
                                          fileName, 
                                          lineNum,
                                          "type '" + type +  
                                          "' of formal '" + name +
                                          "' is undefined");
            }
            //check for duplicate names within formal list
            if (vTable.peek(f.getName()) != null){ 
                noError = false;
                errorHandler.register(errorHandler.SEMANT_ERROR, 
                                      fileName, 
                                      lineNum,
                                      "formal '" + name +  
                                      "' is multiply defined");
            }
            //check for illegal names
            else if (name.equals("null") || name.equals("super") || 
                name.equals("this")) { 
                errorHandler.register(errorHandler.SEMANT_ERROR, 
                                      fileName, 
                                      lineNum,
                                      "formals cannot be named '"
                                       + name + "'");
            }
            //add to scope if good formal
            if (noError && unknownType) {
                vTable.add(f.getName(), "Object");
            }
            else if (noError) {
                vTable.add(f.getName(), f.getType());
            }
        }
        node.getStmtList().accept(this);
        vTable.exitScope();
        return null; 
    }

    public Object visit(StmtList node) {
        //Traverses through all the stmt in a method body
        for (Iterator it = node.getIterator(); it.hasNext(); )
            ((Stmt)it.next()).accept(this);
        return null;
    }

    public Object visit(DeclStmt node) {
        int lineNum = node.getLineNum();        
        String name = node.getName();

        String lhsType = node.getType();
        String rhsType = (String) node.getInit().accept(this);

        boolean lhsIsArray = lhsType.contains("[]");
        boolean rhsIsArray = rhsType.contains("[]");

        String lhsTypeNoBracket = lhsType.replace("[]", "");
        String rhsTypeNoBracket = rhsType.replace("[]", "");

        boolean lhsIsClass = classMap.containsKey(lhsTypeNoBracket);
        boolean rhsIsClass = classMap.containsKey(rhsTypeNoBracket);

        boolean duplicate = false;
        //Check lhs is an actual type, else set to object
        if ((!lhsTypeNoBracket.equals("int") && 
             !lhsTypeNoBracket.equals("boolean")) &&
             !classMap.containsKey(lhsTypeNoBracket)) {
            errorHandler.register(errorHandler.SEMANT_ERROR, 
                                fileName, 
                                lineNum,
                                "type '" + lhsType +  
                                "' of declaration '" + name + 
                                "' is undefined");
            
            lhsType = "Object";
            lhsTypeNoBracket = lhsType;
            lhsIsClass = true;
            
        }

        //Reserved name check
        if (name.equals("null") || name.equals("super") || 
            name.equals("this")) {
            errorHandler.register(errorHandler.SEMANT_ERROR, 
                                  fileName, 
                                  lineNum,
                                  "variables cannot be named '" 
                                  + name + "'");
        }
        //Duplicate name check
        //if duplicate found, do not add to vTable later on
        //if scope is less than 0, first of its name, ok
        //if scope is greater than its parents scope + 1 (for the field)
        //then there exists a duplicate above the data field of the class 
        if ( (vTable.getScopeLevel(name) > 0) &&
                 (vTable.getScopeLevel(name) > (((ClassTreeNode) classMap
                                                    .get(className))
                                                    .getParent()
                                                    .getVarSymbolTable()
                                                    .getCurrScopeLevel() 
                                                    + 1))) {
            duplicate = true;
            errorHandler.register(errorHandler.SEMANT_ERROR, 
                                    fileName, 
                                    lineNum,
                                    "variable '" + name +  
                                    "' is already defined in method " +
                                    methodName );
        }
        //Almost the same as field.
        //Check if either is primitive and do not match 
        if ((lhsType.equals("boolean") || lhsType.equals("int")) 
            && !lhsType.equals(rhsType)) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                    fileName,
                                    lineNum,
                                    "expression type '" + rhsType +
                                    "' of declaration '" + name +
                                    "' does not match declared "
                                    + "type '" + lhsType + "'");
        }
        //Check Class != Class || Class != null
        else if (lhsIsClass && !rhsIsClass && !rhsType.equals("null")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                fileName,
                                lineNum,
                                "expression type '" + rhsType + "' " 
                                + "of declaration '" + name + 
                                "' does not match declared " +
                                "type '" + lhsType + "'"
                                );
        }
        //Check primitive[] != primitive[] && primitive[] != null
        else if (!lhsIsClass && !rhsIsClass && (lhsIsArray != rhsIsArray) 
                 && !rhsType.equals("null")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                fileName,
                                lineNum,
                                "expression type '" + rhsType + "' " 
                                + "of declaration '" + name + 
                                "' does not match declared " +
                                "type '" + lhsType + "'"
                                );
        }
        //Check primitive[] = Class([])?
        else if (!lhsIsClass && rhsIsClass && !lhsType.equals(rhsType)
                 && !rhsType.equals("null")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                fileName,
                                lineNum,
                                "expression type '" + rhsType + "' " 
                                + "of declaration '" + name + 
                                "' does not conform to declared " +
                                "type '" + lhsType + "'"
                                );
        }
        //Check Class = Class || Class[] = Class[]
        else if (lhsIsClass && rhsIsClass) {
            boolean isParent = false;
                for (ClassTreeNode parent = classMap.get(rhsTypeNoBracket); 
                    parent != null && isParent == false; 
                    parent = parent.getParent()) {
                    if (parent.getASTNode().getName()
                    .equals(lhsTypeNoBracket)) {
                        isParent = true;
                        break;
                    }
                }
                //Non-Conform Classes
                if (!isParent && !rhsType.equals("null")) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "expression type '" +
                                           rhsType + "' of declaration '" 
                                          +  name + "' does not conform" + 
                                          " to declared type '"
                                          + lhsType + "'");
                }
                //Classes conform, but type[] does not match
                if (isParent && (lhsIsArray != rhsIsArray) && 
                    !rhsType.equals("null")) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                        fileName,
                                        lineNum,
                                        "expression type '" +
                                         rhsType + "' " 
                                        + "of declaration '" + name + 
                                        "' does not conform to declared " +
                                        "type '" + lhsType + "'");
                }
        }
        
        if (!duplicate)
            vTable.add(name, lhsType);
        return null;
    }

    public Object visit(ExprStmt node) {
        int lineNum = node.getLineNum();
        String type = (String)node.getExpr().accept(this);
        node.getExpr().setExprType(type);
        Expr temp = node.getExpr();
        if (!(temp instanceof AssignExpr) 
            && !(temp instanceof ArrayAssignExpr) 
            && !(temp instanceof NewExpr) 
            && !(temp instanceof DispatchExpr) 
            && !(temp instanceof UnaryDecrExpr) 
            && !(temp instanceof UnaryIncrExpr)) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "not a statement");
        }
        return null;
    }
    

    public Object visit(IfStmt node) { 
        vTable.enterScope();
        String temp = (String) node.getPredExpr().accept(this);
        node.getPredExpr().setExprType(temp);
        int lineNum = node.getLineNum();
        //Check if Pred is a boolean Expr
        if (!temp.equals("boolean")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "predicate in if-statement "
                                  + "does not have type boolean");
        }
        node.getThenStmt().accept(this);
        // Exit Scope after then
        vTable.exitScope();
        //Scope for Else Statment Added
        vTable.enterScope();
        node.getElseStmt().accept(this);
        vTable.exitScope();
        return null; 
    }

    public Object visit(WhileStmt node) { 
        vTable.enterScope();
        String temp = (String) node.getPredExpr().accept(this);
        node.getPredExpr().setExprType(temp);

        int lineNum = node.getLineNum();
        
        if (!temp.equals("boolean")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "predicate in while-statement " +
                                  "does not have type boolean");
        } 
        //Check if already in Loop beforehand
        inLoopCounter++;
        inLoop = true;
        node.getBodyStmt().accept(this);
        vTable.exitScope();
        if (inLoopCounter ==1)
            inLoop = false;
        inLoopCounter--;
        return null; 
    }
    
    public Object visit(ForStmt node) {
        //Enters a new scope
        vTable.enterScope();
        if (node.getInitExpr() != null)
            node.getInitExpr().accept(this);
        if (node.getPredExpr() != null) {
            String temp = (String) node.getPredExpr().accept(this);
            node.getPredExpr().setExprType(temp);
            int lineNum = node.getLineNum();
            if (!temp.equals("boolean")) {
                //Register error here if not boolean
                errorHandler.register(errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "predicate in for-statement " +
                                      "does not have type boolean");
            }
        }
        if (node.getUpdateExpr() != null) {
            node.getUpdateExpr().accept(this);
        }
        //Check if already in Loop beforehand
        inLoopCounter++;
        inLoop = true;
        node.getBodyStmt().accept(this);
        vTable.exitScope();
        if (inLoopCounter ==1)
            inLoop = false;
        inLoopCounter--;
        return null; 
    }
    
    public Object visit(BreakStmt node) { 
        //Check if within a loop
        int lineNum = node.getLineNum();
        if (!inLoop) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "break statement is not inside a loop");
        }
        return null;
    }
    
    public Object visit(BlockStmt node) { 
        //Enter a new scope
        vTable.enterScope(); 
        //Statements must be type-checked in this scope
        node.getStmtList().accept(this);
        vTable.exitScope();
        return null; 
    }
    
    public Object visit(ReturnStmt node) { 
        int lineNum = node.getLineNum();
        String returnType = "void";
        String methodReturnTypeNoArray = methodReturnType.replace("[]","");
        boolean methodReturnIsClass = classMap
                                    .containsKey(methodReturnTypeNoArray);
        boolean methodReturnIsArray = methodReturnType.contains("[]");

        if (node.getExpr() != null) {
            returnType = (String) node.getExpr().accept(this);
            String returnTypeNoArray = returnType.replace("[]", "");
            boolean returnTypeIsClass = classMap
                                        .containsKey(returnTypeNoArray);
            boolean returnTypeIsArray = returnType.contains("[]");
            if (returnTypeNoArray.equals("void")) {
                errorHandler.register(errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "cannot return an expression of"
                                      + " type 'void' from a method");
                returnType = "Object";
            }

            //primitve method() returns ( prim[] | Class | Class[] )
            if ((methodReturnType.equals("int") 
                || methodReturnType.equals("boolean"))  
                && !methodReturnType.equals(returnType)) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                              fileName,
                                              lineNum,
                                              "return type '" 
                                              + returnType +
                                              "' is not compatible with " +
                                              "declared return type '" +
                                              methodReturnType + "' in " +
                                              "method '" + methodName 
                                              + "'");
                }
            //primitive[] method return
            else if (!methodReturnIsClass) {
                //void method() 
                if (methodReturnType.equals("void")) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                              fileName,
                                              lineNum,
                                              "return type '" + returnType
                                              + "' is not compatible with " 
                                              + "declared return type '" +
                                              methodReturnType + "' in " +
                                              "method '" + methodName 
                                              + "'");
                }
                //prim[] method returns (Class | CLass[])
                else if (returnTypeIsClass) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                              fileName,
                                              lineNum,
                                              "return type '" + returnType 
                                              + "' does not conform to" +
                                              " declared return type '" +
                                              methodReturnType + "' in " +
                                              "method '" + methodName 
                                              + "'");
                }
                //prim[] method returns (wrongPrim[] | prim)
                else if (!methodReturnType.equals(returnType) &&
                         !returnType.equals("null")) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                        fileName,
                                        lineNum,
                                        "return type '" + returnType +
                                        "' does not conform to declared" +
                                        " return type '" +
                                        methodReturnType + "' in " +
                                        "method '" + methodName + "'");
                }
            }
            //Class([])+ method returns (prim | prim[]) 
            else if (methodReturnIsClass && !returnTypeIsClass &&
                     !returnType.equals("null")) {
                errorHandler.register(errorHandler.SEMANT_ERROR,
                                    fileName,
                                    lineNum,
                                    "return type '" + returnType +
                                    "' does not conform to declared" +
                                    " return type '" +
                                    methodReturnType + "' in " +
                                    "method '" + methodName + "'");
            }
            //Class([])+ method returns Class([])+
            else if (methodReturnIsClass && returnTypeIsClass) {
                //Check if return type conforms to method type
                boolean isParent = false;
                for (ClassTreeNode parent = 
                                        classMap.get(returnTypeNoArray); 
                    parent != null && isParent == false; 
                    parent = parent.getParent()) {
                    if (parent.getASTNode().getName()
                    .equals(methodReturnTypeNoArray)) {
                        isParent = true;
                        break;
                    }
                }
                //No conformation between classes
                if (!isParent) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                        fileName,
                                        lineNum,
                                        "return type '" + returnType +
                                        "' does not conform to declared" +
                                        " return type '" +
                                        methodReturnType + "' in " +
                                        "method '" + methodName + "'");
                }
                //Classes conform, but one is type[] while the other not
                else if (isParent &&
                         (methodReturnIsArray != returnTypeIsArray)) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                        fileName,
                                        lineNum,
                                        "return type '" + returnType +
                                        "' does not conform to declared" +
                                        " return type '" +
                                        methodReturnType + "' in " +
                                        "method '" + methodName + "'");
                }
            }
        }
        //RETURN TYPE IS VOID
        else {
            if (methodReturnTypeNoArray.equals("boolean") ||
                methodReturnTypeNoArray.equals("int") ||
                classMap.containsKey(methodReturnTypeNoArray)) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "return type 'void' is not"+
                                          " compatible with declared" 
                                          +" return type '" +
                                          methodReturnType + "' in " +
                                          "method '" + methodName + "'");
            }
            else if (!methodReturnType.equals("void")) {
                errorHandler.register(errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "declared return type of method '" + 
                                      methodName + "' is '" 
                                      + methodReturnType + "' but method"+
                                      " body is not returning "+ 
                                      "any expression");
            } 
        }

        return returnType; 
    }
    
    public Object visit(ExprList node) {
        for (Iterator it = node.getIterator(); it.hasNext(); )
            ((Expr)it.next()).accept(this);
        return null;
    }
    
    public Object visit(DispatchExpr node) { 
        String refType = (String) node.getRefExpr().accept(this);
        String methodName = node.getMethodName();
        int lineNum = node.getLineNum();
        String toBeReturned = "Object";
        FormalList fl;
        ExprList el;
        int numFormals, numParams;
        //Check if (void | int | boolean).methodName()
        if (refType.equals("int") || refType.equals("boolean") ||
            refType.equals("void")) {
            node.setExprType(toBeReturned);
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "can't dispatch on " +
                                  "a primitive or void type");
            return toBeReturned;
        }
        //Check type[].methodName(), method table of Object class
        else if (refType.contains("[]")) {
            Method methodToUse = (Method) classMap.get("Object").
                                          getMethodSymbolTable().
                                          peek(methodName);
            //If method does not exist, register error
            if (methodToUse == null) {
                errorHandler.register(errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "dispatch to uknown method '" +
                                      methodName + "'");
            }
            //if method exists, get formal list and get actual list
            else {
                toBeReturned = methodToUse.getReturnType();
                node.setExprType(toBeReturned);
                fl = methodToUse.getFormalList();
                el = (ExprList) node.getActualList();
                
                numFormals = fl.getSize();
                numParams = el.getSize();
                //Check if same number of arguments
                if (numParams != numFormals) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "number of actual" + 
                                          " parameters (" + numParams +
                                           ") differs from" +
                                          " number of formal parameters (" 
                                          + numFormals + ") in dispatch to"
                                          + " method '" + 
                                          methodName + "'");
                }
                //Check type of arguments 
                else {
                    fl = methodToUse.getFormalList();
                    el = (ExprList) node.getActualList();
                    Iterator i1 = fl.getIterator();
                    Iterator i2 = el.getIterator();
                    int paramNumber = 1;
                    while (i1.hasNext()) {
                        String formalType = ((Formal) i1.next()).getType();
                        String paramType =
                                   (String) ((Expr)i2.next()).accept(this);
                        String formalTypeNoArr = 
                                             formalType.replace("[]", "");
                        String paramTypeNoArray = 
                                              paramType.replace("[]", "");
                        boolean formalIsArray = formalType.contains("[]");
                        boolean formalIsClass = classMap
                                            .containsKey(formalTypeNoArr);
                        boolean paramIsClass = classMap
                                            .containsKey(paramTypeNoArray);
                        if (paramType.equals("void")) {
                            errorHandler.register(
                                                errorHandler.SEMANT_ERROR,
                                                fileName,
                                                lineNum,
                                                "actual parameter " + 
                                                paramNumber +
                                                " in the call to" +
                                                " method " + methodName +
                                                " is void and cannot" +
                                                " be used within an " +
                                                "expression");
                        } 
                        else if (!formalTypeNoArr
                                            .equals(paramTypeNoArray)) {
                            //Check for conformity
                            if (formalIsClass && paramIsClass) {
                                boolean conforms = false;
                                for (ClassTreeNode parent = classMap
                                                    .get(paramTypeNoArray); 
                                     parent != null && conforms == false; 
                                     parent = parent.getParent()) {
                                    if (parent.getASTNode()
                                    .getName()
                                    .equals(formalTypeNoArr)) {
                                        conforms = true;
                                    }
                                }
                                //Classes do not conform
                                if (!conforms) {
                                    errorHandler.register(
                                                errorHandler.SEMANT_ERROR,
                                                fileName,
                                                lineNum,
                                                "actual parameter " + 
                                                paramNumber+ " with type '"
                                                 + paramType +
                                                "' does not conform " + 
                                                "to formal parameter " 
                                                + paramNumber +
                                                 " with declared" +
                                                " type '" + formalType 
                                                + "' in " +
                                                "dispatch to method '" + 
                                                methodName + "'");
                                }
                                //Classes conform, array[] does not
                                if (conforms && (formalType.contains("[]") 
                                    != paramType.contains("[]"))
                                    && !formalType.equals("Object")) {
                                    errorHandler.register(
                                                errorHandler.SEMANT_ERROR,
                                                fileName,
                                                lineNum,
                                                "actual parameter " + 
                                                paramNumber+ " with type '"
                                                + paramType + "' does not "
                                                + "match formal parameter " 
                                                + paramNumber +
                                                 " with declared" +
                                                " type '" + formalType 
                                                + "' in dispatch to method" 
                                                + "dispatch to method '" + 
                                                methodName + "'");
                                }
                            }
                            //prim != primm
                            else if (formalType.equals("boolean") 
                                    || formalType.equals("int")) {
                                        errorHandler.register(
                                            errorHandler.SEMANT_ERROR,
                                            fileName,
                                            lineNum,
                                            "actual parameter "
                                            + paramNumber
                                            + " with type '" + 
                                            paramType + "' does not"
                                            + " match formal" + 
                                            " parameter " 
                                            + paramNumber +
                                            " with declared" +
                                            " type '" + formalType 
                                            + "' in " +
                                            "dispatch to method '" + 
                                            methodName + "'");
                            }
                            //prim[] != prim[]
                            else if (formalIsArray 
                                     && !paramType.equals("null")  
                                     && !formalIsClass) {
                                errorHandler.register(
                                                errorHandler.SEMANT_ERROR,
                                                fileName,
                                                lineNum,
                                                "actual parameter "
                                                + paramNumber
                                                + " with type '" + 
                                                paramType + "' does not"
                                                + " match formal" + 
                                                " parameter " 
                                                + paramNumber +
                                                " with declared" +
                                                " type '" + formalType 
                                                + "' in " +
                                                "dispatch to method '" + 
                                                methodName + "'");
                            }
                            //Class != null
                            else if (formalIsClass 
                                     && !paramType.equals("null")) {
                                errorHandler.register(
                                                errorHandler.SEMANT_ERROR,
                                                fileName,
                                                lineNum,
                                                "actual parameter "
                                                + paramNumber
                                                + " with type '" + 
                                                paramType + "' does not"
                                                + " match formal" + 
                                                " parameter " 
                                                + paramNumber +
                                                " with declared" +
                                                " type '" + formalType 
                                                + "' in " +
                                                "dispatch to method '" + 
                                                methodName + "'");
                            }
                        }
                        paramNumber++;
                    }
                }
            }
        }
        else {
            //Type must be a CLASS type
            Method methodToUse = (Method) classMap
                                                .get(refType)
                                                .getMethodSymbolTable()
                                                .lookup(methodName);
            //If the method does not exist, we register error
            if (methodToUse == null) {
                errorHandler.register(errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "dispatch to unknown method '" +
                                      methodName + "'");
            } 
            
            //If the method exists, we check parameters against formals
            else {
                toBeReturned = methodToUse.getReturnType();
                node.setExprType(toBeReturned);
                fl = methodToUse.getFormalList();
                el = (ExprList) node.getActualList();
                numFormals = fl.getSize();
                numParams = el.getSize();
                //Check if same number of arguments
                if (numParams != numFormals) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "number of actual" + 
                                          " parameters (" + numParams +
                                           ") differs from" +
                                          " number of formal parameters (" 
                                          + numFormals + ") in dispatch " +
                                          "to method '" + methodName 
                                          + "'");
                } 
                //Check if same type of arguments
                else {
                    Iterator i1 = fl.getIterator();
                    Iterator i2 = el.getIterator();
                    int paramNumber = 1;
                    while (i1.hasNext()) {
                        String formalType = ((Formal) i1.next()).getType();
                        String paramType = (String) ((Expr)i2.next())
                                                            .accept(this);
                        String formalTypeNoArr = formalType
                                                        .replace("[]", "");
                        String paramTypeNoArray = paramType 
                                                        .replace("[]", "");
                        boolean formalIsArray = formalType.contains("[]");
                        boolean formalIsClass = classMap
                                            .containsKey(formalTypeNoArr);
                        boolean paramIsClass = classMap
                                            .containsKey(paramTypeNoArray);
                        if (paramType.equals("void")) {
                            errorHandler.register(
                                                errorHandler.SEMANT_ERROR,
                                                fileName,
                                                lineNum,
                                                "actual parameter " + 
                                                paramNumber +
                                                " in the call to" +
                                                " method " + methodName +
                                                " is void and cannot" +
                                                " be used within an " +
                                                "expression");
                        } 
                        else if (!formalTypeNoArr.equals(paramTypeNoArray)) 
                        {
                            //Check for conformity
                            if (formalIsClass && paramIsClass) {
                                boolean conforms = false;
                                for (ClassTreeNode parent = classMap
                                                    .get(paramTypeNoArray); 
                                     parent != null && conforms == false; 
                                     parent = parent.getParent()) {
                                    if (parent.getASTNode()
                                    .getName()
                                    .equals(formalTypeNoArr)) {
                                        conforms = true;
                                    }
                                }
                                //Classes do not conform
                                if (!conforms) {
                                    errorHandler.register(
                                                errorHandler.SEMANT_ERROR,
                                                fileName,
                                                lineNum,
                                                "actual parameter " + 
                                                paramNumber+ " with type '"
                                                 + paramType +
                                                "' does not conform " + 
                                                "to formal parameter " 
                                                + paramNumber +
                                                 " with declared" +
                                                " type '" + formalType 
                                                + "' in " +
                                                "dispatch to method '" + 
                                                methodName + "'");
                                }
                                //Classes conform, array[] does not
                                if (conforms && (formalType.contains("[]") 
                                    != paramType.contains("[]"))
                                    && !formalType.equals("Object")) {
                                    errorHandler.register(
                                                errorHandler.SEMANT_ERROR,
                                                fileName,
                                                lineNum,
                                                "actual parameter " + 
                                                paramNumber+ " with type '"
                                                + paramType + "' does not "
                                                + "match formal parameter " 
                                                + paramNumber +
                                                 " with declared" +
                                                " type '" + formalType 
                                                + "' in dispatch to method" 
                                                + "dispatch to method '" + 
                                                methodName + "'");
                                }
                            }
                            //prim != primm
                            else if (formalType.equals("boolean") 
                                     || formalType.equals("int")) {
                                errorHandler.register(
                                            errorHandler.SEMANT_ERROR,
                                            fileName,
                                            lineNum,
                                            "actual parameter "
                                            + paramNumber
                                            + " with type '" + 
                                            paramType + "' does not"
                                            + " match formal" + 
                                            " parameter " 
                                            + paramNumber +
                                            " with declared" +
                                            " type '" + formalType 
                                            + "' in " +
                                            "dispatch to method '" + 
                                            methodName + "'");
                            }
                            //prim[] != prim[]
                            else if (formalIsArray 
                                     && !paramType.equals("null")  
                                     && !formalIsClass) {
                                errorHandler.register(
                                                errorHandler.SEMANT_ERROR,
                                                fileName,
                                                lineNum,
                                                "actual parameter "
                                                + paramNumber
                                                + " with type '" + 
                                                paramType + "' does not"
                                                + " match formal" + 
                                                " parameter " 
                                                + paramNumber +
                                                " with declared" +
                                                " type '" + formalType 
                                                + "' in " +
                                                "dispatch to method '" + 
                                                methodName + "'");
                            }
                            //Class != null
                            else if (formalIsClass 
                                     && !paramType.equals("null")) {
                                errorHandler.register(
                                                errorHandler.SEMANT_ERROR,
                                                fileName,
                                                lineNum,
                                                "actual parameter "
                                                + paramNumber
                                                + " with type '" + 
                                                paramType + "' does not"
                                                + " match formal" + 
                                                " parameter " 
                                                + paramNumber +
                                                " with declared" +
                                                " type '" + formalType 
                                                + "' in " +
                                                "dispatch to method '" + 
                                                methodName + "'");
                            }
                        }
                        paramNumber++;
                    }
                }
            }
        } 
        node.setExprType(toBeReturned);
        return toBeReturned; 
    }
    
    //Returns a String of its type
    public Object visit(NewExpr node) { 
        int lineNum = node.getLineNum();
        String newType = node.getType();
        if (newType.equals("int") || newType.equals("boolean")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "type '" + newType + "' of new" 
                                  + " construction is primitive and " +
                                  "cannot be constructed");
            newType = "Object";
            node.setExprType("Object");
        }
        else if (!classMap.containsKey(newType)) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "type '" + newType + "' of new" 
                                  + " construction is undefined");
            newType = "Object";
            node.setExprType("Object");
        }
        else {
            node.setExprType(newType);
        }
        return newType; 
    }
    
    public Object visit(NewArrayExpr node) { 
        int lineNum = node.getLineNum();
        String type = node.getType();
        if (!type.equals("int") && !type.equals("boolean") &&
            !classMap.containsKey(type)) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "type '" + type + "' of new" 
                                  + " construction is undefined");
            type = "Object";
            node.setExprType(type);
            return type;
        }
        String size = (String) node.getSize().accept(this);
        if ( !size.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "size in the array construction has type" 
                                  + " '" + size + "' rather than int");
        }
        type += "[]";
        node.setExprType(type);
        return type; 
    }
    
    //Returns a a null or "boolean"
    public Object visit(InstanceofExpr node) { 
        int lineNum = node.getLineNum();
        String lhs = (String) node.getExpr().accept(this);
        node.getExpr().setExprType(lhs);
        String rhs = node.getType();
        String rhsNoArr = rhs.replace("[]", "");
        boolean rhsIsArray = rhs.contains("[]");
        boolean rhsIsClass = classMap.containsKey(rhsNoArr);
        String toBeReturned = "boolean";
        //Check LHS
        if (lhs.equals("boolean") || lhs.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                fileName,
                                lineNum,
                                "the instanceof lefthand expression has" +
                                " type '" + lhs + "', which is primitive" +
                                " and not an object type");
            lhs = "Object"; 
        }
        else if (lhs.equals("void")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "Instanceof has expression type void");
            lhs = "Object"; 
        }

        //Check RHS
        if (rhs.equals("boolean") || rhs.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the instanceof righthand type '" + rhs +
                                  "' is primitive and not an object type");
        }
        else if (rhsIsArray) {
            if (!rhsIsClass && !rhsNoArr.equals("boolean") 
                && !rhsNoArr.equals("int")) {
                errorHandler.register(errorHandler.SEMANT_ERROR,
                                    fileName,
                                    lineNum,
                                    "the base type in the instanceof " +
                                    "righthand array type '" + rhsNoArr +
                                    "' is undefined");
            }
        }
        else if (!rhsIsClass) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "the instanceof righthand type '"
                                       + rhs +
                                      "' is undefined");
        }
        node.setExprType(toBeReturned);
        return toBeReturned; 
    }
    
    //Returns the String type of castType
    public Object visit(CastExpr node) {
        String castType = node.getType();
        boolean legitCast = false;
        boolean upCast = false;
        int lineNum = node.getLineNum();
        String exprType = (String) node.getExpr().accept(this);
        String castTypeNoArr = castType.replace("[]", "");
        String exprTypeNoArr = exprType.replace("[]", "");
        boolean exprIsArray = exprType.contains("[]");
        boolean castIsArray = castType.contains("[]");
        boolean castIsClass = classMap.containsKey(castTypeNoArr);
        boolean exprIsClass = classMap.containsKey(exprTypeNoArr);
        
        //if it is an int or boolean cast
        if (castType.equals("int") || castType.equals("boolean")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the target type '" + castType +
                                  "' is primitive and not an object type");
            castType = "Object";
            castTypeNoArr = castType;
            castIsClass = true;
        }
        //If it is a int[] or boolean[] cast
        else if (!classMap.containsKey(castTypeNoArr) 
                 && !castTypeNoArr.equals("int") 
                 && !castTypeNoArr.equals("boolean")) {
            if (castIsArray) {
                errorHandler.register(errorHandler.SEMANT_ERROR,
                                fileName,
                                lineNum,
                                "the base type in the target array type '" 
                                + castTypeNoArr + "' is undefined");
                castType = "Object[]";
            }
            else {
                errorHandler.register(errorHandler.SEMANT_ERROR,
                                fileName,
                                lineNum,
                                "the target type '" +
                                castType + "' is undefined");
                castType = "Object";
            }
            castTypeNoArr = "Object";
            castIsClass = true;
        }

        //Cannot cast (Object) primitive
        if (exprType.equals("int") || exprType.equals("boolean")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                    fileName,
                                    lineNum,
                                    "expression in cast has type '" +
                                    exprType + "', which is primitive"
                                    + " and can't be casted");
        }
        else if (!castType.equals(exprType))
        {
            // Checks if not (Object) prim[]
            if (castIsClass && !exprIsClass && !castType.equals("Object"))
            {
                errorHandler.register(errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "inconvertible types ('" + exprType 
                                      + "'=>'" + castType + "')");
            }
            // Checks (prim[]) Object
            else if (!castIsClass && !exprType.equals("Object")) {
                errorHandler.register(errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "inconvertible types ('" + exprType 
                                      + "'=>'" + castType + "')");
            }
            else if (castIsClass && exprIsClass) {
                for (ClassTreeNode parent = classMap.get(exprTypeNoArr); 
                    parent != null && legitCast == false; 
                    parent = parent.getParent()) {
                    if (parent.getASTNode().getName()
                                                .equals(castTypeNoArr)) {
                        legitCast = true;
                        upCast = true;
                    }
                }
                //Check for downcast from the castExpr
                for (ClassTreeNode parent = classMap.get(castTypeNoArr); 
                    parent != null && legitCast == false; 
                    parent = parent.getParent()) {
                    if (parent.getASTNode().getName()
                                                .equals(exprTypeNoArr)) {
                        legitCast = true;
                    }
                }

                //Checks for side casting 
                if (!legitCast) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "inconvertible types ('" 
                                          + exprType 
                                          + "'=>'" + castType + "')");
                }
                //Checks if not (Object) class[]
                else if (!castType.equals("Object") 
                        && (castIsArray != exprIsArray)) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                    fileName,
                                    lineNum,
                                    "inconvertible types ('" + exprType 
                                    + "'=>'" + castType + "')");
                }

            }
        }
        node.setExprType(castType);
        node.setUpCast(upCast);
        return castType; 
    }
    
    public Object visit(AssignExpr node) {
        int lineNum = node.getLineNum();
        String rhsType = (String) node.getExpr().accept(this);  
        String refName = node.getRefName();
        String varName = node.getName();
        String lhsType;
        node.getExpr().setExprType(rhsType);
        if (refName != null) {
            if (refName.equals("this")) {
                lhsType = (String) vTable.lookup(refName + "." + varName);
                if (lhsType == null) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "variable '" + varName + 
                                          "' in assignment is undeclared");
                }
                else if (rhsType.equals("void")) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                        fileName,
                                        lineNum,
                                        "the righthand type 'void'"+ 
                                        " does not" + 
                                        " conform to the lefthand type '" +
                                        lhsType + "' in assignment");
                }
                else if (!lhsType.equals(rhsType)) {
                    String lhsTypeNoArr = lhsType.replace("[]", "");
                    String rhsTypeNoArr = rhsType.replace("[]", "");
                    boolean lhsIsClass = 
                                        classMap.containsKey(lhsTypeNoArr);
                    boolean rhsIsClass = 
                                        classMap.containsKey(rhsTypeNoArr);
                    boolean lhsIsArray = lhsType.contains("[]");
                    boolean rhsIsArray = rhsType.contains("[]");
                    //Check Class conformity
                    if (lhsIsClass && rhsIsClass) {
                        boolean isParent = false;
                        for (ClassTreeNode parent = 
                             classMap.get(rhsTypeNoArr); 
                             parent != null && isParent == false; 
                             parent = parent.getParent()) {
                            if (parent.getASTNode().getName()
                                .equals(lhsTypeNoArr)) {
                                isParent = true;
                                break;
                            }
                        }
                        //Classes do not conform
                        if (!isParent) {
                            errorHandler.register(
                                          errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "the righthand type '" + rhsType 
                                          + "' does not conform " + 
                                          "to the lefthand"
                                          + " type '" + lhsType + "'" +
                                          " in assignment");
                        }
                        //Classes conform, but not with type array[]
                        else if (isParent && (lhsIsArray != rhsIsArray)) {
                            errorHandler.register(
                                          errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "the righthand type '" + rhsType 
                                          + "' does not conform " + 
                                          "to the lefthand"
                                          + " type '" + lhsType + "'" +
                                          " in assignment");
                        }
                    }
                    //Check prim[] = prim[]
                    else if (!lhsIsClass && lhsIsArray) {
                        errorHandler.register(
                                        errorHandler.SEMANT_ERROR,
                                        fileName,
                                        lineNum,
                                        "the righthand type '" + rhsType 
                                        + "' does not conform " + 
                                        "to the lefthand"
                                        + " type '" + lhsType + "'" +
                                        " in assignment");
                    }
                    // handles prim = prim 
                    else {
                        errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "the lefthand type '" + 
                                          lhsType +
                                          "' and righthand type '" +
                                          rhsType 
                                          + "' are not compatible" 
                                          + " in assignment");
                    }
                }
            }
            else if (refName.equals("super")) {
                lhsType = (String) classMap.get(className).getParent()
                                            .getVarSymbolTable()
                                            .lookup("this." + varName);
                if (lhsType == null) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                        fileName,
                                        lineNum,
                                        "variable '" + varName + 
                                        "' in assignment is undeclared");
                }
                else if (rhsType.equals("void")) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                        fileName,
                                        lineNum,
                                        "the righthand type 'void'"+ 
                                        " does not" + 
                                        " conform to the lefthand type '"
                                        + lhsType + "' in assignment");
                }
                else if (!lhsType.equals(rhsType)) {
                    String lhsTypeNoArr = lhsType.replace("[]", "");
                    String rhsTypeNoArr = rhsType.replace("[]", "");
                    boolean lhsIsClass = 
                                    classMap.containsKey(lhsTypeNoArr);
                    boolean rhsIsClass = 
                                    classMap.containsKey(rhsTypeNoArr);
                    boolean lhsIsArray = lhsType.contains("[]");
                    boolean rhsIsArray = rhsType.contains("[]");
                    //Check Class conformity
                    if (lhsIsClass && rhsIsClass) {
                        boolean isParent = false;
                        for (ClassTreeNode parent = 
                                classMap.get(rhsTypeNoArr); 
                                parent != null && isParent == false; 
                                parent = parent.getParent()) {
                            if (parent.getASTNode().getName()
                                .equals(lhsTypeNoArr)) {
                                isParent = true;
                                break;
                            }
                        }
                        //Classes do not conform
                        if (!isParent) {
                            errorHandler.register(
                                        errorHandler.SEMANT_ERROR,
                                        fileName,
                                        lineNum,
                                        "the righthand type '" + rhsType 
                                        + "' does not conform " + 
                                        "to the lefthand"
                                        + " type '" + lhsType + "'" +
                                        " in assignment");
                        }
                        //Classes conform, but not with type array[]
                        else if (isParent && (lhsIsArray != rhsIsArray)) {
                            errorHandler.register(
                                        errorHandler.SEMANT_ERROR,
                                        fileName,
                                        lineNum,
                                        "the righthand type '" + rhsType 
                                        + "' does not conform " + 
                                        "to the lefthand"
                                        + " type '" + lhsType + "'" +
                                        " in assignment");
                        }
                    }
                    //Check prim[] = prim[]
                    else if (!lhsIsClass && lhsIsArray) {
                        errorHandler.register(
                                        errorHandler.SEMANT_ERROR,
                                        fileName,
                                        lineNum,
                                        "the righthand type '" + rhsType 
                                        + "' does not conform " + 
                                        "to the lefthand"
                                        + " type '" + lhsType + "'" +
                                        " in assignment");
                    }
                    // handles prim = prim 
                    else {
                        errorHandler.register(errorHandler.SEMANT_ERROR,
                                            fileName,
                                            lineNum,
                                            "the lefthand type '" + 
                                            lhsType +
                                            "' and righthand type '" +
                                            rhsType 
                                            + "' are not compatible" 
                                            + " in assignment");
                    }
                }
            }
            //ref is not "this" | "super"
            else {
                String arrayType = (String) vTable.lookup(refName);
                if (arrayType != null && arrayType.contains("[]") 
                                        && varName.equals("length")) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "length field in array '" + refName + 
                                      "': cannot be modified");
                } 
                else {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "bad reference '" + refName + "': " 
                                      + "fields are 'protected' and " +
                                      "can only be accessed within the " +
                                      "class or subclass via" + 
                                      " 'this' or 'super'");
                }
            }
        }
        //There is no referance before the variable name
        else {
            
            lhsType = (String) vTable.lookup(varName);
            if (lhsType == null) {
                errorHandler.register(errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "variable '" + varName + 
                                      "' in assignment is undeclared");
            }
            else if (rhsType.equals("void")) {
                errorHandler.register(errorHandler.SEMANT_ERROR,
                                    fileName,
                                    lineNum,
                                    "the righthand type 'void'"+ 
                                    " does not" + 
                                    " conform to the lefthand type '" +
                                    lhsType + "' in assignment");
            }
            else if (!lhsType.equals(rhsType)) {
                String lhsTypeNoArr = lhsType.replace("[]", "");
                String rhsTypeNoArr = rhsType.replace("[]", "");
                boolean lhsIsClass = classMap.containsKey(lhsTypeNoArr);
                boolean rhsIsClass = classMap.containsKey(rhsTypeNoArr);
                boolean lhsIsArray = lhsType.contains("[]");
                boolean rhsIsArray = rhsType.contains("[]");
                //Check Class conformity
                if (lhsIsClass && rhsIsClass) {
                    
                    boolean isParent = false;
                    for (ClassTreeNode parent = 
                         classMap.get(rhsTypeNoArr); 
                         parent != null && isParent == false; 
                         parent = parent.getParent()) {
                        if (parent.getASTNode().getName()
                            .equals(lhsTypeNoArr)) {
                            isParent = true;
                            break;
                        }
                    }
                    //Classes do not conform
                    if (!isParent) {
                        errorHandler.register(
                                      errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "the righthand type '" + rhsType 
                                      + "' does not conform " + 
                                      "to the lefthand"
                                      + " type '" + lhsType + "'" +
                                      " in assignment");
                    }
                    //Classes conform, but not with type array[]
                    else if (isParent && (lhsIsArray != rhsIsArray)) {
                        errorHandler.register(
                                      errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "the righthand type '" + rhsType 
                                      + "' does not conform " + 
                                      "to the lefthand"
                                      + " type '" + lhsType + "'" +
                                      " in assignment");
                    }
                }
                //Check prim[] = prim[]
                else if (!lhsIsClass && lhsIsArray) {
                    errorHandler.register(
                                      errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "the righthand type '" + rhsType 
                                      + "' does not conform " + 
                                      "to the lefthand"
                                      + " type '" + lhsType + "'" +
                                      " in assignment");
                }
                // handles prim = prim 
                else {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "the lefthand type '" + 
                                      lhsType +
                                      "' and righthand type '" +
                                      rhsType 
                                      + "' are not compatible" 
                                      + " in assignment");
                }
            }
        }
        node.setExprType(rhsType);
        return rhsType; 
    }
    
    public Object visit(ArrayAssignExpr node) {
        String index = (String) node.getIndex().accept(this);
        node.getIndex().setExprType(index);
        String rhsType = (String) node.getExpr().accept(this);
        node.getExpr().setExprType(rhsType);
        int lineNum = node.getLineNum();
        String refName = node.getRefName();
        String varName = node.getName();
        String lhsType;

        if (!index.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "ArrayAssignExpr wrong size type," + 
                                  " not int");
        }

        if (refName != null) {
            if (refName.equals("this")) {
                lhsType = (String) vTable.lookup(refName + "." + varName);
                if (lhsType != null) {
                    lhsType = lhsType.replace("[]", "");
                }
                if (lhsType == null) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "variable '" + varName + 
                                          "' in assignment is undeclared");
                }
                else if (rhsType.equals("void")) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                        fileName,
                                        lineNum,
                                        "the righthand type 'void'"+ 
                                        " does not" + 
                                        " conform to the lefthand type '" +
                                        lhsType + "' in assignment");
                }
                else if (!lhsType.equals(rhsType)) {
                    String lhsTypeNoArr = lhsType.replace("[]", "");
                    String rhsTypeNoArr = rhsType.replace("[]", "");
                    boolean lhsIsClass = 
                                        classMap.containsKey(lhsTypeNoArr);
                    boolean rhsIsClass = 
                                        classMap.containsKey(rhsTypeNoArr);
                    boolean lhsIsArray = lhsType.contains("[]");
                    boolean rhsIsArray = rhsType.contains("[]");
                    //Check Class conformity
                    if (lhsIsClass && rhsIsClass) {
                        boolean isParent = false;
                        for (ClassTreeNode parent = 
                             classMap.get(rhsTypeNoArr); 
                             parent != null && isParent == false; 
                             parent = parent.getParent()) {
                            if (parent.getASTNode().getName()
                                .equals(lhsTypeNoArr)) {
                                isParent = true;
                                break;
                            }
                        }
                        //Classes do not conform
                        if (!isParent) {
                            errorHandler.register(
                                          errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "the righthand type '" + rhsType 
                                          + "' does not conform " + 
                                          "to the lefthand"
                                          + " type '" + lhsType + "'" +
                                          " in assignment");
                        }
                        //Classes conform, but not with type array[]
                        else if (isParent && (lhsIsArray != rhsIsArray)) {
                            errorHandler.register(
                                          errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "the righthand type '" + rhsType 
                                          + "' does not conform " + 
                                          "to the lefthand"
                                          + " type '" + lhsType + "'" +
                                          " in assignment");
                        }
                    }
                    //Check prim[] = prim[]
                    else if (!lhsIsClass && lhsIsArray) {
                        errorHandler.register(
                                        errorHandler.SEMANT_ERROR,
                                        fileName,
                                        lineNum,
                                        "the righthand type '" + rhsType 
                                        + "' does not conform " + 
                                        "to the lefthand"
                                        + " type '" + lhsType + "'" +
                                        " in assignment");
                    }
                    // handles prim = prim 
                    else {
                        errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "the lefthand type '" + 
                                          lhsType +
                                          "' and righthand type '" +
                                          rhsType 
                                          + "' are not compatible" 
                                          + " in assignment");
                    }
                }
            }
            else if (refName.equals("super")) {
                lhsType = (String) classMap.get(className).getParent()
                                            .getVarSymbolTable()
                                            .lookup("this." + varName);
                if (lhsType != null) {
                    lhsType = lhsType.replace("[]", "");
                }
                if (lhsType == null) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                        fileName,
                                        lineNum,
                                        "variable '" + varName + 
                                        "' in assignment is undeclared");
                }
                else if (rhsType.equals("void")) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                        fileName,
                                        lineNum,
                                        "the righthand type 'void'"+ 
                                        " does not" + 
                                        " conform to the lefthand type '" +
                                        lhsType + "' in assignment");
                }
                else if (!lhsType.equals(rhsType)) {
                    String lhsTypeNoArr = lhsType.replace("[]", "");
                    String rhsTypeNoArr = rhsType.replace("[]", "");
                    boolean lhsIsClass = 
                                        classMap.containsKey(lhsTypeNoArr);
                    boolean rhsIsClass = 
                                        classMap.containsKey(rhsTypeNoArr);
                    boolean lhsIsArray = lhsType.contains("[]");
                    boolean rhsIsArray = rhsType.contains("[]");
                    //Check Class conformity
                    if (lhsIsClass && rhsIsClass) {
                        boolean isParent = false;
                        for (ClassTreeNode parent = 
                                classMap.get(rhsTypeNoArr); 
                                parent != null && isParent == false; 
                                parent = parent.getParent()) {
                            if (parent.getASTNode().getName()
                                .equals(lhsTypeNoArr)) {
                                isParent = true;
                                break;
                            }
                        }
                        //Classes do not conform
                        if (!isParent) {
                            errorHandler.register(
                                        errorHandler.SEMANT_ERROR,
                                        fileName,
                                        lineNum,
                                        "the righthand type '" + rhsType 
                                        + "' does not conform " + 
                                        "to the lefthand"
                                        + " type '" + lhsType + "'" +
                                        " in assignment");
                        }
                        //Classes conform, but not with type array[]
                        else if (isParent && (lhsIsArray != rhsIsArray)) {
                            errorHandler.register(
                                        errorHandler.SEMANT_ERROR,
                                        fileName,
                                        lineNum,
                                        "the righthand type '" + rhsType 
                                        + "' does not conform " + 
                                        "to the lefthand"
                                        + " type '" + lhsType + "'" +
                                        " in assignment");
                        }
                    }
                    //Check prim[] = prim[]
                    else if (!lhsIsClass && lhsIsArray) {
                        errorHandler.register(
                                        errorHandler.SEMANT_ERROR,
                                        fileName,
                                        lineNum,
                                        "the righthand type '" + rhsType 
                                        + "' does not conform " + 
                                        "to the lefthand"
                                        + " type '" + lhsType + "'" +
                                        " in assignment");
                    }
                    // handles prim = prim 
                    else {
                        errorHandler.register(errorHandler.SEMANT_ERROR,
                                            fileName,
                                            lineNum,
                                            "the lefthand type '" + 
                                            lhsType +
                                            "' and righthand type '" +
                                            rhsType 
                                            + "' are not compatible" 
                                            + " in assignment");
                    }
                }
            }
            //ref is not "this" | "super"
            else {
                String arrayType = (String) vTable.lookup(refName);
                if (arrayType != null && arrayType.contains("[]") 
                                        && varName.equals("length")) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "length field in array '" + refName + 
                                      "': cannot be modified");
                } 
                else {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "bad reference '" + refName + "': " 
                                      + "fields are 'protected' and " +
                                      "can only be accessed within the " +
                                      "class or subclass via" + 
                                      " 'this' or 'super'");
                }
            }
        }
        //There is no referance before the variable name
        else {
            lhsType = (String) vTable.lookup(varName);
            //Remove the [] from the type 
            if (lhsType != null) {
                lhsType = lhsType.replace("[]", "");
            }
            if (lhsType == null) {
                errorHandler.register(errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "variable '" + varName + 
                                      "' in assignment is undeclared");
            }
            else if (rhsType.equals("void")) {
                errorHandler.register(errorHandler.SEMANT_ERROR,
                                    fileName,
                                    lineNum,
                                    "the righthand type 'void'"+ 
                                    " does not" + 
                                    " conform to the lefthand type '" +
                                    lhsType + "' in assignment");
            }
            else if (!lhsType.equals(rhsType)) {
                String lhsTypeNoArr = lhsType.replace("[]", "");
                String rhsTypeNoArr = rhsType.replace("[]", "");
                boolean lhsIsClass = classMap.containsKey(lhsTypeNoArr);
                boolean rhsIsClass = classMap.containsKey(rhsTypeNoArr);
                boolean lhsIsArray = lhsType.contains("[]");
                boolean rhsIsArray = rhsType.contains("[]");
                //Check Class conformity
                if (lhsIsClass && rhsIsClass) {
                    boolean isParent = false;
                    for (ClassTreeNode parent = 
                         classMap.get(rhsTypeNoArr); 
                         parent != null && isParent == false; 
                         parent = parent.getParent()) {
                        if (parent.getASTNode().getName()
                            .equals(lhsTypeNoArr)) {
                            isParent = true;
                            break;
                        }
                    }
                    //Classes do not conform
                    if (!isParent) {
                        errorHandler.register(
                                      errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "the righthand type '" + rhsType 
                                      + "' does not conform " + 
                                      "to the lefthand"
                                      + " type '" + lhsType + "'" +
                                      " in assignment");
                    }
                    //Classes conform, but not with type array[]
                    else if (isParent && (lhsIsArray != rhsIsArray)) {
                        errorHandler.register(
                                      errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "the righthand type '" + rhsType 
                                      + "' does not conform " + 
                                      "to the lefthand"
                                      + " type '" + lhsType + "'" +
                                      " in assignment");
                    }
                }
                //Check prim[] = prim[]
                else if (!lhsIsClass && lhsIsArray) {
                    errorHandler.register(
                                    errorHandler.SEMANT_ERROR,
                                    fileName,
                                    lineNum,
                                    "the righthand type '" + rhsType 
                                    + "' does not conform " + 
                                    "to the lefthand"
                                    + " type '" + lhsType + "'" +
                                    " in assignment");
                }
                // handles prim = prim s
                else {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "the lefthand type '" + 
                                      lhsType +
                                      "' and righthand type '" +
                                      rhsType 
                                      + "' are not compatible" 
                                      + " in assignment");
                }
            }
        }
        node.setExprType(rhsType);
        return rhsType; 
    }
    
    public Object visit(BinaryCompEqExpr node) { 
        int lineNum = node.getLineNum();
        String type1 = (String) node.getLeftExpr().accept(this);
        String type2 = (String) node.getRightExpr().accept(this);
        if (!type1.equals(type2)) {
            String type1NoBrackets = type1.replace("[]", "");
            String type2NoBrackets = type2.replace("[]", "");
            boolean type2IsClass = classMap.containsKey(type1NoBrackets);
            boolean type1IsClass = classMap.containsKey(type2NoBrackets);
            boolean type1IsArray = type1.contains("[]");
            boolean type2IsArray = type2.contains("[]");

            //One of them is a primitive, 
            if (type1.equals("int") || type1.equals("boolean") 
                || type2.equals("int") || type2.equals("boolean")) {
                errorHandler.register(errorHandler.SEMANT_ERROR,
                                        fileName,
                                        lineNum,
                                        "the lefthand type '" 
                                        + type1 + "'" +
                                        " in the binary " + 
                                        "operation ('==')" +
                                        " does not match " + 
                                        "the righthand type '" +
                                        type2 + "'");
            }
            //check if prim1[] != null | prim2[] != null
            else if ((!type1IsClass && !type2.equals("null") 
                     && type1IsArray) || (!type2IsClass && 
                     !type1.equals("null") && type2IsArray)) {
                errorHandler.register(errorHandler.SEMANT_ERROR,
                        fileName,
                        lineNum,
                        "the lefthand type '" 
                        + type1 + "'" +
                        " in the binary " + 
                        "operation ('==')" +
                        " does not match " + 
                        "the righthand type '" +
                        type2 + "'");
            }
            //Both are classes, check conformity
            else if (type1IsClass && type2IsClass) {
                boolean foundRelation = false;
                
                for (ClassTreeNode parent = classMap.get(type1);
                        parent != null && !foundRelation; 
                        parent = parent.getParent()) {

                    if (parent.getASTNode().getName().equals(type2)) {
                        foundRelation = true;
                    }
                }

                for (ClassTreeNode parent = classMap.get(type2);
                        parent != null && !foundRelation; 
                        parent = parent.getParent()) {

                    if (parent.getASTNode().getName().equals(type1)) {
                        foundRelation = true;
                    }
                }

                if (!foundRelation) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "the lefthand type '" 
                                          + type1 + "'" +
                                          " in the binary " + 
                                          "operation ('==')" +
                                          " does not match " + 
                                          "the righthand type '" +
                                          type2 + "'");
                }
                //Conform, but one is array[] and other is not and
                //the other is also not "Object"
                else if (foundRelation && ( (type1IsArray != type2IsArray) 
                         && type1.equals("Object") 
                         && type2.equals("Object") ) ) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                            fileName,
                            lineNum,
                            "the lefthand type '" 
                            + type1 + "'" +
                            " in the binary " + 
                            "operation ('==')" +
                            " does not match " + 
                            "the righthand type '" +
                            type2 + "'");
                }
            }
        }
        node.setExprType(node.getOpType());
        return "boolean"; 
    }
    
    public Object visit(BinaryCompNeExpr node) {
        int lineNum = node.getLineNum();
        String type1 = (String) node.getLeftExpr().accept(this);
        String type2 = (String) node.getRightExpr().accept(this);
        if (!type1.equals(type2)) {
            String type1NoBrackets = type1.replace("[]", "");
            String type2NoBrackets = type2.replace("[]", "");
            boolean type2IsClass = classMap.containsKey(type1NoBrackets);
            boolean type1IsClass = classMap.containsKey(type2NoBrackets);
            boolean type1IsArray = type1.contains("[]");
            boolean type2IsArray = type2.contains("[]");

            //One of them is a primitive, 
            if (type1.equals("int") || type1.equals("boolean") 
                || type2.equals("int") || type2.equals("boolean")) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                    fileName,
                    lineNum,
                    "the lefthand type '" 
                    + type1 + "'" +
                    " in the binary " + 
                    "operation ('!=')" +
                    " does not match the " + 
                    "righthand type '" +
                    type2 + "'");
            }
            //check if prim1[] != null | prim2[] != null
            else if ((!type1IsClass && !type2.equals("null") 
                     && type1IsArray) || (!type2IsClass && 
                     !type1.equals("null") && type2IsArray)) {
                        errorHandler.register(errorHandler.SEMANT_ERROR,
                        fileName,
                        lineNum,
                        "the lefthand type '" 
                        + type1 + "'" +
                        " in the binary " + 
                        "operation ('!=')" +
                        " does not match the " + 
                        "righthand type '" +
                        type2 + "'");
            }
            //Both are classes, check conformity
            else if (type1IsClass && type2IsClass) {
                boolean foundRelation = false;
                
                for (ClassTreeNode parent = classMap.get(type1);
                        parent != null && !foundRelation; 
                        parent = parent.getParent()) {

                    if (parent.getASTNode().getName().equals(type2)) {
                        foundRelation = true;
                    }
                }

                for (ClassTreeNode parent = classMap.get(type2);
                        parent != null && !foundRelation; 
                        parent = parent.getParent()) {

                    if (parent.getASTNode().getName().equals(type1)) {
                        foundRelation = true;
                    }
                }

                if (!foundRelation) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                        fileName,
                                        lineNum,
                                        "the lefthand type '" 
                                        + type1 + "'" +
                                        " in the binary " + 
                                        "operation ('!=')" +
                                        " does not match the " + 
                                        "righthand type '" +
                                        type2 + "'");
                }
                //Conform, but one is array[] and other is not and
                //the other is also not "Object"
                else if (foundRelation && ( (type1IsArray != type2IsArray) 
                         && type1.equals("Object") 
                         && type2.equals("Object") ) ) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                        fileName,
                                        lineNum,
                                        "the lefthand type '" 
                                        + type1 + "'" +
                                        " in the binary " + 
                                        "operation ('!=')" +
                                        " does not match the " + 
                                        "righthand type '" +
                                        type2 + "'");
                }
            }
        }
        node.setExprType(node.getOpType());
        return "boolean";
    }
    
    public Object visit(BinaryCompLtExpr node) { 
        int lineNum = node.getLineNum();
        String type1 = (String) node.getLeftExpr().accept(this);
        //node.getLeftExpr().setExprType(type1);
        String type2 = (String) node.getRightExpr().accept(this);
        //node.getLeftExpr().setExprType(type2);
        if (!type1.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the lefthand type '" + type1 + "' in " +
                                  "the binary operation ('<') is "
                                  + "incorrect; should have been: int");
        }
        if (!type2.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the righthand type '" + type2 + "' in "
                                  + "the binary operation ('<') is "
                                  + "incorrect; should have been: int");
        }
        node.setExprType(node.getOpType());
        return "boolean"; 
    }
    
    public Object visit(BinaryCompLeqExpr node) { 
        int lineNum = node.getLineNum();
        String type1 = (String) node.getLeftExpr().accept(this);
        //node.getLeftExpr().setExprType(type1);
        String type2 = (String) node.getRightExpr().accept(this);
        //node.getLeftExpr().setExprType(type2);
        if (!type1.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the lefthand type '" + type1 + "' in "
                                  + "the binary operation ('<=') is "
                                  + "incorrect; should have been: int");
        }
        if (!type2.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the righthand type '" + type2 + "' in "
                                  + "the binary operation ('<=') is "
                                  + "incorrect; should have been: int");
        }
        node.setExprType(node.getOpType());
        return "boolean";
    }
    
    public Object visit(BinaryCompGtExpr node) {
        int lineNum = node.getLineNum();
        String type1 = (String) node.getLeftExpr().accept(this);
        //node.getLeftExpr().setExprType(type1);
        String type2 = (String) node.getRightExpr().accept(this);
        //node.getLeftExpr().setExprType(type2);
        if (!type1.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the lefthand type '" + type1 + "' in "
                                  + "the binary operation ('>') is "
                                  + "incorrect; should have been: int");
        }
        if (!type2.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the righthand type '" + type2 + "' in "
                                  + "the binary operation ('>') is "
                                  + "incorrect; should have been: int");
        }
        node.setExprType(node.getOpType());
        return "boolean";
    }
    
    public Object visit(BinaryCompGeqExpr node) { 
        int lineNum = node.getLineNum();
        String type1 = (String) node.getLeftExpr().accept(this);
        node.getLeftExpr().setExprType(type1);
        String type2 = (String) node.getRightExpr().accept(this);
        node.getLeftExpr().setExprType(type2);
        if (!type1.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the lefthand type '" + type1 + "' in "
                                  + "the binary operation ('>=') is "
                                  + "incorrect; should have been: int");
        }
        if (!type2.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the righthand type '" + type2 + "' in "
                                  + "the binary operation ('>=') is "
                                  + "incorrect; should have been: int");
        }
        node.setExprType(node.getOpType());
        return "boolean";
    }
    
    public Object visit(BinaryArithPlusExpr node) { 
        int lineNum = node.getLineNum(); 
        
        String type1 = (String) node.getLeftExpr().accept(this);
        node.getLeftExpr().setExprType(type1);
        String type2 = (String) node.getRightExpr().accept(this);
        node.getLeftExpr().setExprType(type2);
        if (!type1.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the lefthand type '" + type1 + "' in "
                                  + "the binary operation ('+') is "
                                  + "incorrect; should have been: int");
        }
        if (!type2.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the righthand type '" + type2 + "' in "
                                  + "the binary operation ('+') is "
                                  + "incorrect; should have been: int");
        }
        node.setExprType(node.getOpType());
        return "int"; 
    }
    
    public Object visit(BinaryArithMinusExpr node) { 
        int lineNum = node.getLineNum();
        String type1 = (String) node.getLeftExpr().accept(this);
        node.getLeftExpr().setExprType(type1);
        String type2 = (String) node.getRightExpr().accept(this);
        node.getLeftExpr().setExprType(type2);
        if (!type1.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the lefthand type '" + type1 + "' in "
                                  + "the binary operation ('-') is "
                                  + "incorrect; should have been: int");
        }
        if (!type2.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the righthand type '" + type2 + "' in "
                                  + "the binary operation ('-') is "
                                  + "incorrect; should have been: int");
        }
        node.setExprType(node.getOpType());
        return "int"; 
    }
    
    public Object visit(BinaryArithTimesExpr node) {
        int lineNum = node.getLineNum();
        String type1 = (String) node.getLeftExpr().accept(this);
        node.getLeftExpr().setExprType(type1);
        String type2 = (String) node.getRightExpr().accept(this);
        node.getLeftExpr().setExprType(type2);
        if (!type1.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the lefthand type '" + type1 + "' in "
                                  + "the binary operation ('*') is "
                                  + "incorrect; should have been: int");
        }
        if (!type2.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the righthand type '" + type2 + "' in "
                                  + "the binary operation ('*') is "
                                  + "incorrect; should have been: int");
        }
        node.setExprType(node.getOpType());
        return "int"; 
    }
    
    public Object visit(BinaryArithDivideExpr node) { 
        int lineNum = node.getLineNum();
        String type1 = (String) node.getLeftExpr().accept(this);
        node.getLeftExpr().setExprType(type1);
        String type2 = (String) node.getRightExpr().accept(this);
        node.getLeftExpr().setExprType(type2);
        if (!type1.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the lefthand type '" + type1 + "' in "
                                  + "the binary operation ('/') is "
                                  + "incorrect; should have been: int");
        }
        if (!type2.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the righthand type '" + type2 + "' in "
                                  + "the binary operation ('/') is "
                                  + "incorrect; should have been: int");
        }
        node.setExprType(node.getOpType());
        return "int"; 
    }
    
    public Object visit(BinaryArithModulusExpr node) { 
        int lineNum = node.getLineNum();
        String type1 = (String) node.getLeftExpr().accept(this);
        node.getLeftExpr().setExprType(type1);
        String type2 = (String) node.getRightExpr().accept(this);
        node.getLeftExpr().setExprType(type2);
        if (!type1.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the lefthand type '" + type1 + "' in "
                                  + "the binary operation ('%') is "
                                  + "incorrect; should have been: int");
        }
        if (!type2.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the righthand type '" + type2 + "' in "
                                  + "the binary operation ('%') is "
                                  + "incorrect; should have been: int");
        }
        node.setExprType(node.getOpType());
        return "int"; 
    }
    
    public Object visit(BinaryLogicAndExpr node) { 
        int lineNum = node.getLineNum();
        String type1 = (String) node.getLeftExpr().accept(this);
        node.getLeftExpr().setExprType(type1);
        String type2 = (String) node.getRightExpr().accept(this);
        node.getLeftExpr().setExprType(type2);
        if (!type1.equals("boolean")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the lefthand type '" + type1 + "' in "
                                  + "the binary operation ('&&') is " +
                                  "incorrect; should have been: boolean");
        }
        if (!type2.equals("boolean")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the righthand type '" + type2 + "' in "
                                  + "the binary operation ('&&') is " +
                                  "incorrect; should have been: boolean");
        }
        node.setExprType(node.getOpType());
        return "boolean"; 
    }
    
    public Object visit(BinaryLogicOrExpr node) { 
        int lineNum = node.getLineNum();
        String type1 = (String) node.getLeftExpr().accept(this);
        node.getLeftExpr().setExprType(type1);
        String type2 = (String) node.getRightExpr().accept(this);
        node.getLeftExpr().setExprType(type2);

        if (!type1.equals("boolean")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the lefthand type '" + type1 + "' in "
                                  + "the binary operation ('||') is " +
                                  "incorrect; should have been: boolean");
        }
        if (!type2.equals("boolean")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the righthand type '" + type2 + "' in "
                                  + "the binary operation ('||') is " +
                                  "incorrect; should have been: boolean");
        }
        node.setExprType(node.getOpType());
        return "boolean";
    }
    
    public Object visit(UnaryNegExpr node) { 
        int lineNum = node.getLineNum();
        String type = (String) node.getExpr().accept(this);
        if (!type.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the expression type '" + type +
                                  "' in the unary operation ('-') is " +
                                  "incorrect; should have been: int" );
        }
        node.setExprType(node.getOpType());
        return "int"; 
    }
    
    public Object visit(UnaryNotExpr node) { 
        int lineNum = node.getLineNum();
        String type = (String) node.getExpr().accept(this);
        if (!type.equals("boolean")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the expression type '" + type +
                                  "' in the unary operation ('!') is " +
                                  "incorrect; should have been: boolean" );
        }
        node.setExprType(node.getOpType());
        return "boolean"; 
    }
    
    public Object visit(UnaryIncrExpr node) { 
        int lineNum = node.getLineNum();
        String type = (String) node.getExpr().accept(this);
        if (!type.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the expression type '" + type +
                                  "' in the unary operation ('++') is " +
                                  "incorrect; should have been: int" );
        }
        node.setExprType(node.getOpType());
        return "int"; 
    }
    
    public Object visit(UnaryDecrExpr node) { 
        int lineNum = node.getLineNum();
        String type = (String) node.getExpr().accept(this);
        if (!type.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the expression type '" + type +
                                  "' in the unary operation ('--') is " +
                                  "incorrect; should have been: int" );
        }
        node.setExprType(node.getOpType());
        return "int";
    }
    
    public Object visit(VarExpr node) {
        int lineNum = node.getLineNum();
        String name = node.getName();
        
        if (node.getRef() != null)
        {
            String varType;        
            String refName = (String) node.getRef().accept(this);
            if (refName.equals("this")) {
                //check local 
                varType = (String) vTable.lookup("this." + name);
                if (varType == null) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "variable '" + name + 
                                          "' in assignment is undeclared");
                    //Maybe delete later
                    node.setExprType("Object");
                    return "Object";
                }
                //everything is good when ref is this
                else {
                    node.setExprType(varType);
                    return varType;
                }   
            }
            else if (refName.equals("super")) {
                varType = (String) classMap.get(className).getParent()
                                                .getVarSymbolTable()
                                                .lookup("this." + name);
                if (varType == null) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "variable '" + name + 
                                          "' in assignment is undeclared");
                    node.setExprType("Object");
                    return "Object";
                }
                else {
                    node.setExprType(varType);
                    return varType;
                }
            }
            else if (refName.contains("[]")) {
                //name = length
                if (!name.equals("length")) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "bad reference to '" + name +
                                          "': arrays do not have this " 
                                          + "field (they only have a " +
                                          "'length' field)");
                    node.setExprType("Object");
                    return "Object";
                }
                else {
                    node.setExprType("int");
                    return "int";
                }
            }
            else {
                node.setExprType(refName);
                return refName;
            }

        }
        //ref does not exist here
        else if (name.equals("this")) {
            //return className
            node.setExprType(className);
            return className;
        }
        else if (name.equals("super")) {
            //return superclassName
            String parentName = classMap.get(className).getParent()
                                                        .getName();
            node.setExprType(parentName);
            return parentName;
        } 
        else if (name.equals("null")) {
            node.setExprType("null");
            return "null";
        }
        else {
            String varType = (String) vTable.lookup(name);
            if (varType == null) {
                errorHandler.register(errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "Variable in VarExpr not found");
                node.setExprType("Object");
                return "Object";
            }
            else {
                node.setExprType(varType);
                return varType;
            }
        }
    }
    
    public Object visit(ArrayExpr node) { 
        int lineNum = node.getLineNum();
        if (node.getRef() != null)
            node.getRef().accept(this);
        String index = (String) node.getIndex().accept(this); 
        if (!index.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "Index in ArrayExpr is not int");
        }

        //Everything below this is copied and pasted
        String name = node.getName();
        if (node.getRef() != null)
        {
            String varType;
            
            String refName = (String) node.getRef().accept(this);
            
            if (refName.equals("this")) {
                //check local 
                varType = (String) vTable.lookup("this." + name);
                if (varType == null) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "variable '" + name + 
                                          "' in assignment is undeclared");
                    node.setExprType("Object");
                    return "Object";
                }
                //everything is good when ref is this
                else {
                    node.setExprType(varType.replace("[]", ""));
                    return varType.replace("[]", "");
                }   
            }
            else if (refName.equals("super")) {
                varType = (String) classMap.get(className).getParent()
                                                .getVarSymbolTable()
                                                .lookup("this." + name);
                if (varType == null) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "variable '" + name + 
                                          "' in assignment is undeclared");
                    node.setExprType("Object");
                    return "Object";
                }
                //Everything is correct when ref is super
                else {
                    node.setExprType(varType.replace("[]", ""));
                    return varType.replace("[]", "");
                }
            }
            //NEXT LOGIC POINT
            else if (refName.contains("[]")) {
                //name = length
                if (!name.equals("length")) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "bad reference to '" + name +
                                          "': arrays do not have this" + 
                                          " field (they only have a " 
                                          + "'length' field)");
                    node.setExprType("Object");
                    return "Object";
                }
                else {
                    node.setExprType("int");
                    return "int";
                }
            }
            else {
                node.setExprType(refName.replace("[]", ""));
                return refName.replace("[]", "");
            }

            
        }
        //ref does not exist here
        else if (name.equals("this")) {
            //return className
            node.setExprType(className);
            return className;
        }
        else if (name.equals("super")) {
            //return superclassName
            String parentName = classMap.get(className).getParent()
                                                        .getName();
            node.setExprType(parentName);
            return parentName;
        } 
        else if (name.equals("null")) {
            node.setExprType("null");
            return "null";
        }
        else {
            String varType = (String) vTable.lookup(name);
            if (varType == null) {
                errorHandler.register(errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "Variable in VarExpr not found");
                node.setExprType("Object");
                return "Object";
            }
            else {
                node.setExprType(varType.replace("[]", ""));
                return varType.replace("[]", "");
            }
        }
    }
    
    public Object visit(ConstIntExpr node) {
        node.setExprType("int");
        return "int";
    }
    
    public Object visit(ConstBooleanExpr node) { 
        node.setExprType("boolean");
        return "boolean"; 
    }
    
    public Object visit(ConstStringExpr node) { 
        node.setExprType("String");
        return "String"; 
    }
}
