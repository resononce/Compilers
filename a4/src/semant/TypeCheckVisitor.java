
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
            String rhsType = (String) node.getInit().accept(this);
            String lhsType = node.getType();
            int lineNum = node.getLineNum();
            String name = node.getName();
            String rCheckType = rhsType.replace("[]", "");
            String lCheckType = lhsType.replace("[]", "");
            //checks if assigning a void to  the lhs
            if (rhsType.equals("void")) {
                errorHandler.register(errorHandler.SEMANT_ERROR, 
                                      fileName, 
                                      lineNum,
                                      "expression type '" + rhsType +  
                                      "' of field '" + name +
                                      "' cannot be void");
            } 
            //checks if either lhs or rhs is primitive and do not match
            else if (((lCheckType.equals("boolean") || lCheckType.equals("int")) 
                    || (rCheckType.equals("boolean") || rCheckType.equals("int"))) 
                    && !lCheckType.equals(rCheckType) && !rCheckType.equals("null")) {
                errorHandler.register(errorHandler.SEMANT_ERROR, 
                                      fileName, 
                                      lineNum,
                                      "expression type '" + rhsType +  
                                      "' of field '" + name +
                                      "' does not match declared type '" +
                                      lhsType + "'");
            } 
            //checks if they are Class type and if rhs is subtype of lhs
                else if (classMap.containsKey(lCheckType) 
                        && classMap.containsKey(rCheckType) 
                        && !rCheckType.equals("null")) {
                Iterator childrenList = classMap.get(lCheckType).getChildrenList();
                boolean notChild = true;
                while (childrenList.hasNext()) {
                    ClassTreeNode ctn = (ClassTreeNode) childrenList.next();
                    if (ctn.getASTNode().getName().equals(rCheckType)) {
                        notChild = false;
                        break;
                    }
                }
                if (notChild) {
                    errorHandler.register(errorHandler.SEMANT_ERROR, 
                                          fileName, 
                                          lineNum,
                                          "expression type '" + rhsType +  
                                          "' of field '" + name +
                                          "' does not conform to declared type '" +
                                          lhsType + "'");
                } 
            }
        }
        return null; 
    }

    public Object visit(Method node) {
        methodReturnType = node.getReturnType();
        vTable.enterScope();  //Changed from mTable to vTable based on slide 15-2
        methodName = node.getName();
        //moves forward into body of method
        //node.getStmtList().accept(this);
        //Goes through method arguments to check for type of each arg
        for (Iterator it = node.getFormalList().getIterator(); it.hasNext();) {
            Formal f = (Formal) it.next();
            int lineNum = f.getLineNum();
            String name = f.getName();
            String type = f.getType();
            String checkType = type.replace("[]", "");
            boolean noError = true;
            boolean unknownType = false;
            //check type of arg exists
            if ((!checkType.equals("boolean") && !checkType.equals("int")) &&
                !classMap.containsKey(checkType)) {
                    unknownType = true;
                    errorHandler.register(errorHandler.SEMANT_ERROR, 
                                          fileName, 
                                          lineNum,
                                          "type '" + type +  
                                          "' of formal '" + name +
                                          "' is undefined");
            }
            //check for duplicates
            if (vTable.peek(f.getName()) != null){ //mTable to vTable
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
                noError = false;
                errorHandler.register(errorHandler.SEMANT_ERROR, 
                                      fileName, 
                                      lineNum,
                                      "formals cannot be named '" + name + "'");
            }
            //add to scope if legit arg
            if (noError && unknownType) {
                //Maybe take this out, check semantic errors later
                //Arbitrarily set type to "Object"
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
        boolean noError = true;
        int lineNum = node.getLineNum();
        String type = node.getType();
        String checkType = type.replace("[]", "");
        String name = node.getName();
        String rhsType = (String)node.getInit().accept(this);
        String rhsTypeNoBracket = rhsType.replace("[]", "");
        boolean duplicate = false;
        //Type Check of rhs
        if ((!checkType.equals("boolean") && !checkType.equals("int")) &&
            !classMap.containsKey(checkType)) {
                errorHandler.register(errorHandler.SEMANT_ERROR, 
                                      fileName, 
                                      lineNum,
                                      "type '" + type +  
                                      "' of declaration '" + name + 
                                      "' is undefined");
                //Sets to default type "Object" when unknown
                type = "Object";
        }
        //Reserved name check
        if (name.equals("null") || name.equals("super") || 
            name.equals("this")) {
            noError = false;
            errorHandler.register(errorHandler.SEMANT_ERROR, 
                                  fileName, 
                                  lineNum,
                                  "variables cannot be named '" 
                                  + name + "'");
        }
        //Duplicate name check
        else if ( (vTable.getScopeLevel(name) > 0) &&
                 (vTable.getScopeLevel(name) > (((ClassTreeNode) classMap.get(className)).getParent()
                 .getVarSymbolTable().getCurrScopeLevel() + 1))) {
            duplicate = true;
            errorHandler.register(errorHandler.SEMANT_ERROR, 
                                    fileName, 
                                    lineNum,
                                    "variable '" + name +  
                                    "' is already defined in method " +
                                    methodName );
        }
        if (!rhsType.equals(type)) {
            //Need to check if conforms or not
            if (classMap.containsKey(rhsTypeNoBracket) && classMap.containsKey(checkType)){
                Iterator iterate = classMap.get(checkType).getChildrenList();
                boolean doesConform = false;
                while (iterate.hasNext() && !doesConform) {
                    if (((ClassTreeNode) iterate.next()).getName().equals(checkType)) {
                        doesConform = true;
                    }
                }
                if (!doesConform) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "expression type '" + rhsType + "' " 
                                          + "of declaration '" + name + 
                                          "' does not conform to declared " +
                                          "type '" + type + "'"
                                          );
                }
                if (doesConform && (type.contains("[]") != rhsType.contains("[]"))) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "expression type '" + rhsType + "' " 
                                          + "of declaration '" + name + 
                                          "' does not conform to declared " +
                                          "type '" + type + "'"
                                          );
                }
            } 
            //at least one is not a class, and they don't match
            else {
                errorHandler.register(errorHandler.SEMANT_ERROR,
                                    fileName,
                                    lineNum,
                                    "expression type '" + rhsType +
                                    "' of declaration '" + name +
                                    "' does not match declared "
                                    + "type '" + type + "'");
            }
        } 
        if (!duplicate)
            vTable.add(name, type);
        return null;
    }

    public Object visit(ExprStmt node) {
        int lineNum = node.getLineNum();
        //Maybe set the Type of Expression with setExprType()****
        //Goes forward to the expression ..Original: node.getExpr().accept(this);
        node.getExpr().accept(this);
        //Checks that the ExprStmt is a legit statement
        Expr temp = node.getExpr();
        if (!(temp instanceof AssignExpr) && !(temp instanceof ArrayAssignExpr) &&
            !(temp instanceof NewExpr) && !(temp instanceof DispatchExpr) &&
            !(temp instanceof UnaryDecrExpr) && !(temp instanceof UnaryIncrExpr)) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "not a statement");
        }
        //Check for appropriate expressions and register error if not
        return null; //Might return type
    }
    

    public Object visit(IfStmt node) { 
        //Needs to enter a new scope
        vTable.enterScope();
        //Check if Pred is a boolean Expr
        String temp = (String) node.getPredExpr().accept(this);
        int lineNum = node.getLineNum();
        if (!temp.equals("boolean")) {
            //Register error here if not boolean
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "predicate in if-statement "
                                  + "does not have type boolean");
        }
        node.getThenStmt().accept(this);
        // Exit Scope after then
        vTable.exitScope();
        //TODO scopes
        node.getElseStmt().accept(this);
        return null; 
    }

    public Object visit(WhileStmt node) { 
        //Have to add something to check if a break; is within a loop
        //Enters a new scope
        vTable.enterScope();
        String temp = (String) node.getPredExpr().accept(this);
        int lineNum = node.getLineNum();
        if (!temp.equals("boolean")) {
            //Register error here if not boolean
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "predicate in while-statement " +
                                  "does not have type boolean");
        } 
        inLoop = true;
        node.getBodyStmt().accept(this);
        vTable.exitScope();
        inLoop = false;
        return null; 
    }
    
    public Object visit(ForStmt node) { 
        //Have to add something to check if a break; is within a loop
        //Enters a new scope
        vTable.enterScope();
        if (node.getInitExpr() != null)
            node.getInitExpr().accept(this);
        if (node.getPredExpr() != null) {
            String temp = (String) node.getPredExpr().accept(this);
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
        inLoop = true;
        node.getBodyStmt().accept(this);
        vTable.exitScope();
        inLoop = false;
        return null; 
    }
    
    public Object visit(BreakStmt node) { 
        //Set private boolean inLoop later
        //Check if within a loop, will do later
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
        boolean noError = true;
        String returnType = "void";
        String methodReturnTypeNoArray = methodReturnType.replace("[]", "");
        if (node.getExpr() != null) {
            returnType = (String) node.getExpr().accept(this);
            Expr expr = (Expr) node.getExpr();
            lineNum = expr.getLineNum();
            if (returnType.equals("void")) {
                noError = false;
                //Register void return error
                errorHandler.register(errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "cannot return an expression of"
                                      + " type 'void' from a method");
                //set to default type "Object" when type is void
                return "Object";
            }

            
            String returnTypeNotArray = returnType.replace("[]", "");
            //Double check this if later
            if (returnTypeNotArray.equals("null")) {
                return "null";
            }
            //Check if return expr is class type and method return is class type
            if (classMap.containsKey(returnTypeNotArray) && 
                classMap.containsKey(methodReturnTypeNoArray)) {
                //get children of method returnType if classType
                Iterator children = classMap.get(methodReturnTypeNoArray).getChildrenList();
                boolean conform = false;
                if (!returnTypeNotArray.equals(methodReturnTypeNoArray)) {
                    //Stil need to check for conformity
                    
                    while (children.hasNext()) {
                        if (returnTypeNotArray.equals(((ClassTreeNode) children.next())
                            .getASTNode().getName())) {
                            conform = true;
                            boolean b1 = methodReturnType.contains("[]");
                            boolean b2 = returnType.contains("[]");
                            //Check if return expr type is not child of method return type
                            if (b1 != b2) {
                                noError = false;
                                errorHandler.register(errorHandler.SEMANT_ERROR,
                                                      fileName,
                                                      lineNum,
                                                      "return type '" + returnType +
                                                      "' is not compatible with " +
                                                      "declared return type '" + 
                                                      methodReturnType + "' in method"
                                                      + " '" + methodName + "'");
                            }
                            //Something might be wrong with this return
                            //return returnType;
                        }
                    }
                    if (!conform) {
                        errorHandler.register(errorHandler.SEMANT_ERROR,
                                              fileName,
                                              lineNum,
                                              "return type '" + returnType +
                                              "' does not conform to declared" +
                                              " return type '" +
                                              methodReturnType + "' in " +
                                              "method '" + methodName + "'");
                    }
                    return returnType;
                }
                //Check if either one is an array type
                else {
                    boolean b1 = methodReturnType.contains("[]");
                    boolean b2 = returnType.contains("[]");
                    if (b1 != b2) {
                        noError = false;
                        errorHandler.register(errorHandler.SEMANT_ERROR,
                                              fileName,
                                              lineNum,
                                              "return type '" + returnType +
                                              "' is not compatible with " +
                                              "declared return type '" + 
                                              methodReturnType + "' in method"
                                              + " '" + methodName + "'");
                    }
                    return returnType;
                } 
            }
            //return expression is primitive type 
            //if primitive types do not match, handles [] 
            else if (!returnType.equals(methodReturnType)) {
                noError = false;
                errorHandler.register(errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "return type '" + returnType +
                                      "' is not compatible with " +
                                      "declared return type '" + 
                                      methodReturnType + "' in method"
                                      + " '" + methodName + "'");
            }
        }
        // in the case where it is just return; We return "void"
        //bool this(){return;}
        else {
            if (methodReturnTypeNoArray.equals("boolean") ||
                methodReturnTypeNoArray.equals("int") ||
                classMap.containsKey(methodReturnTypeNoArray)) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "return type 'void' is not"+
                                          " compatible with declared return type" +
                                          " '" + methodReturnType + "' " +
                                          "in method '" + methodName + "'");
                }
            else if (!methodReturnType.equals("void")) {
                noError = false;
                errorHandler.register(errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "declared return type of method '" + 
                                      methodName + "' is '" + methodReturnType +
                                      "' but method body is not returning "+ 
                                      "any expression");
            } 
            //declared return type of method 'this' is 'bool' but method body is not returning any expression
        }
        //Whether incorrect or correct, we will always return the returnType
        //node.getExpr().setExprType(returnType);
        return returnType; 
    }
    
    public Object visit(ExprList node) {
        for (Iterator it = node.getIterator(); it.hasNext(); )
            ((Expr)it.next()).accept(this);
        return null;
    }

    public Object visit(Expr node) { 
        throw new RuntimeException("This visitor method should not be called (node is abstract)");
    }
    
    //The type for this node can be obtained from getExprType() or
    //from the return of this visit
    public Object visit(DispatchExpr node) { 
        String exprType = (String) node.getRefExpr().accept(this);
        //node.getActualList().accept(this);
        String methodName = node.getMethodName();
        int lineNum = node.getLineNum();
        String toBeReturned = "Object";
        FormalList fl;
        ExprList el;
        int numFormals, numParams;
        //Check that LHS refExpr is not primitive or void
        if (exprType.equals("boolean") || exprType.equals("int") 
        || exprType.equals("void")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "can't dispatch on " +
                                  "a primitive or void type");
            return toBeReturned;
        } 
        else if (exprType.contains("[]")) { //if the expr is an array type
            //has the same dispatch table (symbol table) as the Object class, Slide 15-19
            //gets Object's methodTable method
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
                fl = methodToUse.getFormalList();
                el = (ExprList) node.getActualList();
                
                numFormals = fl.getSize();
                numParams = el.getSize();
                //Check if same number of arguments
                if (numParams != numFormals) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "number of actual parameters (" +
                                          numParams + ") differs from" +
                                          "number of formal parameters (" +
                                          numFormals + ") in dispatch " +
                                          "method '" + methodName + "'");
                } 
                //Check if same type of arguments
                else {
                    Iterator i1 = fl.getIterator();
                    Iterator i2 = el.getIterator();
                    int paramNumber = 1;
                    boolean noError = true;
                    while (i1.hasNext()) {
                        String formalType = ((Formal) i1.next()).getType();
                        String paramType = (String) ((Expr)i2.next()).accept(this);
                        if (paramType.equals("void")) {
                            noError = false;
                            errorHandler.register(errorHandler.SEMANT_ERROR,
                                                  fileName,
                                                  lineNum,
                                                  "actual parameter " + 
                                                  paramNumber + "in the call" +
                                                  " to method " + methodName +
                                                  " is void and cannot be used" +
                                                  " within an expression");
                        } 
                        else if (!formalType.equals(paramType)) {
                            noError = false;
                            errorHandler.register(errorHandler.SEMANT_ERROR,
                                                  fileName,
                                                  lineNum,
                                                  "actual parameter " + paramNumber
                                                  + "with type '" + paramType +
                                                  "does not match forma parameter " 
                                                  + paramNumber + " with declared" +
                                                  "type '" + formalType + "in " +
                                                  "dispath to method '" + 
                                                  methodName + "'");
                        } 
                    }
                    //If no error and everything matches, setExprType() and return Type
                    if (noError) {
                        toBeReturned = methodToUse.getReturnType();
                    }
                }
            }
        }
        else {
            //Type must be a CLASS type
            //Don't think it handles THIS.method()
            
            Method methodToUse = (Method) classMap.get(exprType).getMethodSymbolTable()
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
                fl = methodToUse.getFormalList();
                el = (ExprList) node.getActualList();
                numFormals = fl.getSize();
                numParams = el.getSize();
                //Check if same number of arguments
                if (numParams != numFormals) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "number of actual parameters (" +
                                          numParams + ") differs from" +
                                          "number of formal parameters (" +
                                          numFormals + ") in dispatch " +
                                          "method '" + methodName + "'");
                } 
                //Check if same type of arguments
                else {
                    Iterator i1 = fl.getIterator();
                    Iterator i2 = el.getIterator();
                    int paramNumber = 1;
                    boolean noError = true;
                    while (i1.hasNext()) {
                        String formalType = ((Formal) i1.next()).getType();
                        String paramType = (String) ((Expr)i2.next()).accept(this);
                        if (paramType.equals("void")) {
                            noError = false;
                            errorHandler.register(errorHandler.SEMANT_ERROR,
                                                  fileName,
                                                  lineNum,
                                                  "actual parameter " + 
                                                  paramNumber + "in the call" +
                                                  " to method " + methodName +
                                                  " is void and cannot be used" +
                                                  " within an expression");
                        } 
                        else if (!formalType.equals(paramType)) {
                            noError = false;
                            errorHandler.register(errorHandler.SEMANT_ERROR,
                                                  fileName,
                                                  lineNum,
                                                  "actual parameter " + paramNumber
                                                  + "with type '" + paramType +
                                                  "does not match forma parameter " 
                                                  + paramNumber + " with declared" +
                                                  "type '" + formalType + "in " +
                                                  "dispath to method '" + 
                                                  methodName + "'");
                        } 
                    }
                    //If no error and everything matches, setExprType() and return Type
                    if (noError) {
                        toBeReturned = methodToUse.getReturnType();
                    }
                }
            }
        }
        node.setExprType(toBeReturned);
        return toBeReturned; 
    }
    
    //Returns a String of its type
    public Object visit(NewExpr node) { 
        String newType = node.getType();
        if (!classMap.containsKey(newType)) {
            newType = "Object";
            node.setExprType("Object");
        }
        else {
            node.setExprType(newType);
        }
        return newType; //Setting expr type and returning it, Slide 15-21
    }
    
    //Returns String type of the new array
    public Object visit(NewArrayExpr node) { 
        int lineNum = node.getLineNum();
        String type = node.getType();
        if (!type.equals("int") && !type.equals("boolean") &&
            !classMap.containsKey(type)) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "type '" + type + "' of new" 
                                  + "construction is undefined");
            type = "Object";
        }
        String size = (String) node.getSize().accept(this);
        if ( !size.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "size in the array construction has type " +
                                  "'" + size + "' rather than int");
        }
        return type; 
    }
    
    //Returns a a null or "boolean"
    public Object visit(InstanceofExpr node) { 
        int lineNum = node.getLineNum();
        String lhs = (String) node.getExpr().accept(this);
        String rhs = node.getType();
        String lhsNoArr = lhs.replace("[]", "");
        String rhsNoArr = rhs.replace("[]", "");
        boolean noError = true;
        String toBeReturned = "boolean";
        //Check LHS
        if (lhsNoArr.equals("boolean") || lhsNoArr.equals("int")) {
            noError = false;
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the instanceof lefthand expression has" +
                                  "type '" + lhs + "', which is primitive" +
                                  " and not an object type");
        }
        else if (lhsNoArr.equals("void")) {
            noError = false;
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "Instanceof has expression type void");
        }

        //Check RHS
        if (rhsNoArr.equals("boolean") || rhsNoArr.equals("int")) {
            noError = false;
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the instanceof righthand type '" + rhs +
                                  "' is primitive and not an object type");
        } 
        //Fix later
        else if (rhsNoArr.equals("void")) {
            noError = false;
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "RHS void of instanceOf");
        }
        //If the rhs of castExpr is not a valid type
        else if (!classMap.containsKey(rhsNoArr)) {
            noError = false;
            if (rhs.contains("[]")) {
                errorHandler.register(errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "the base type in the instanceof" +
                                      "righthand array type '" + rhsNoArr +
                                      "' is undefined");
            }
            else {
                errorHandler.register(errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "the instanceof righthand type '" + rhs +
                                      "' is undefined");
            }
        } 

        //Original: node.getExpr().accept(this);
        //Either returns null or "boolean"
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

        if (castTypeNoArr.equals("int") || castTypeNoArr.equals("boolean")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the target type '" + castType +
                                  "' is primitive and not an object type");
            castType = "Object";
            castTypeNoArr = "Object";
            //Maybe node.setExprType("Object"); Slide 15-20
        }
        else if (!classMap.containsKey(castTypeNoArr)) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the target type '" +
                                  castType + "' is undefined");
            castType = "Object";
            castTypeNoArr = "Object";
        }
        //if expr, from node.getExpr() is primitive or neither an up or down cast, register error
        //Set boolean flag and setExprType()
        if (exprTypeNoArr.equals("int") || exprTypeNoArr.equals("boolean")) {
            //Register an error
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                   fileName,
                                   lineNum,
                                   "expression in cast has type '" +
                                   exprType + "' which is primitive"
                                   + " and can't be casted");
        } 
        //Check for appropriate upcasting and downcasting
        else {
            Iterator childrenList = classMap.get(castTypeNoArr).getChildrenList();
            //Checks for a upcast from the current
            while (childrenList.hasNext() && legitCast == false) {
                if (((ClassTreeNode) childrenList.next()).getASTNode()
                      .getName().equals(exprTypeNoArr)) {
                    legitCast = true;
                    upCast = true;
                }
            }
            //Check for downcast from the current
            ClassTreeNode parent = classMap.get(castTypeNoArr).getParent();
            while (parent != null && legitCast == false) {
                if (parent.getASTNode().getName().equals(exprTypeNoArr)) {
                    legitCast = true;
                }
                //get the parent's parent
                parent = classMap.get(parent.getASTNode().getName()).getParent();
            }
            if (castType.equals(exprTypeNoArr)) {
                legitCast = true;
            }

            if (!legitCast) {
                errorHandler.register(errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "Inconvertible types: ('" + exprType 
                                      + "'=>'" + castType + "')");
            }
            //This should take care of the array portion
            //If legal cast but does not pass array check, register error
            if ((exprType.contains("[]") != castType.contains("[]")) && 
                legitCast) {
                errorHandler.register(errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "Inconvertible types: ('" + exprType 
                                      + "'=>'" + castType + "')");
            }
        }
        node.setExprType(castType);
        node.setUpCast(upCast);
        return castType; 
    }
    
    public Object visit(AssignExpr node) {
        //Slide example a.b = RHS
        int lineNum = node.getLineNum();
        String rhsType = (String) node.getExpr().accept(this);  //This type checks the rhs, maybe type-check before grabbing node
        String refName = node.getRefName();
        String varName = node.getName();
        String varType;

        if (refName != null) {
            if (refName.equals("this")) {
                //get the parent, because we're gonna remove it
                //SymbolTable tempParent = classMap.get(className).getParent().getVarSymbolTable();
                //vTable.setParent(null);
                varType = (String) vTable.lookup("this." + varName);
                int scopeLevel = vTable.getScopeLevel("this." + varName); //-1 if not found
                // getSize() is total size, getCurrScopeSize is child size
                int inheritedScopeSize = vTable.getSize() - vTable.getCurrScopeSize(); //0 if not found
                if (scopeLevel <= inheritedScopeSize) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "variable '" + varName + 
                                          "in assignment is undeclared");
                }
                else if (!varType.equals(rhsType)) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "the righthand type '" + rhsType +
                                          "' does not conform to the lefthand"
                                          + " type '" + varType + "'" +
                                          " in assignment");
                }
                node.setExprType(rhsType);
            } else if (refName.equals("super")) {
                //check the parent's VarSymbolTable scope for type of b in a.b
                varType = (String) classMap.get(className).getParent()
                                        .getVarSymbolTable().lookup(varName);
                int scopeLevel = vTable.getScopeLevel("this." + varName); //-1 if not found
                int inheritedScopeSize = vTable.getSize() - vTable.getCurrScopeSize();
                //TODO
                if (scopeLevel <= inheritedScopeSize) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "variable '" + varName + 
                                          "in assignment is undeclared");
                }
                else if (!varType.equals(rhsType)) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "the righthand type '" + rhsType +
                                          "' does not conform to the lefthand"
                                          + " type '" + varType + "'" +
                                          " in assignment");
                }
                node.setExprType(rhsType);
            }
        }
        else {
            varType = (String) vTable.lookup(varName);
            if (varType == null) {
                errorHandler.register(errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "variable '" + varName + 
                                      "in assignment is undeclared");
            }
            else if (!varType.equals(rhsType)) {
                errorHandler.register(errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "the righthand type '" + rhsType +
                                      "' does not conform to the lefthand"
                                      + " type '" + varType + "'" +
                                      " in assignment");
            }
            node.setExprType(rhsType);
        }
        //If RHS = void, error register
        //If RHS != LHS type b, error register

        //return the RHS return type
        return rhsType; 
    }
    
    public Object visit(ArrayAssignExpr node) { 
        //Almost the same as visit(AssignExpr node) except an extra check to make sure that we have an int expr in array["int"]
        String index = (String) node.getIndex().accept(this);
        String rhsType = (String) node.getExpr().accept(this);
        int lineNum = node.getLineNum();
        //node.getExpr().accept(this);  //This type checks the rhs, maybe type-check before grabbing node
        String refName = node.getRefName();
        String varName = node.getName();
        String varType;

        if (!index.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "ArrayAssignExpr wrong size type, not int");
        }
        if (refName != null) {
            if (refName.equals("this")) {
                //get the parent, because we're gonna remove it
                //SymbolTable tempParent = classMap.get(className).getParent().getVarSymbolTable();
                //vTable.setParent(null);
                varType = (String) vTable.lookup("this." + varName);
                int scopeLevel = vTable.getScopeLevel("this." + varName); //-1 if not found
                // getSize() is total size, getCurrScopeSize is child size
                int inheritedScopeSize = vTable.getSize() - vTable.getCurrScopeSize(); //0 if not found
                if (scopeLevel <= inheritedScopeSize) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "variable '" + varName + 
                                          "in assignment is undeclared");
                }
                else if (!varType.equals(rhsType)) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "the righthand type '" + rhsType +
                                          "' does not conform to the lefthand"
                                          + " type '" + varType + "'" +
                                          " in assignment");
                }
                node.setExprType(rhsType);
            } else if (refName.equals("super")) {
                //check the parent's VarSymbolTable scope for type of b in a.b
                varType = (String) classMap.get(className).getParent()
                                        .getVarSymbolTable().lookup(varName);
                int scopeLevel = vTable.getScopeLevel("this." + varName); //-1 if not found
                int inheritedScopeSize = vTable.getSize() - vTable.getCurrScopeSize();
                //TODO
                if (scopeLevel <= inheritedScopeSize) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "variable '" + varName + 
                                          "in assignment is undeclared");
                }
                else if (!varType.equals(rhsType)) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "the righthand type '" + rhsType +
                                          "' does not conform to the lefthand"
                                          + " type '" + varType + "'" +
                                          " in assignment");
                }
                node.setExprType(rhsType);
            }
        }
        else {
            varType = (String) vTable.lookup(varName);
            if (varType == null) {
                errorHandler.register(errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "variable '" + varName + 
                                      "in assignment is undeclared");
            }
            else if (!varType.equals(rhsType)) {
                errorHandler.register(errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "the righthand type '" + rhsType +
                                      "' does not conform to the lefthand"
                                      + " type '" + varType + "'" +
                                      " in assignment");
            }
            node.setExprType(rhsType);
        }
        return null; 
    }
    
    public Object visit(BinaryExpr node) { 
        throw new RuntimeException("This visitor method should not be called (node is abstract)");
    }
    
    public Object visit(BinaryCompExpr node) { 
        throw new RuntimeException("This visitor method should not be called (node is abstract)");
    }
    
    public Object visit(BinaryCompEqExpr node) { 
        int lineNum = node.getLineNum();
        String type1 = (String) node.getLeftExpr().accept(this);
        String type2 = (String) node.getRightExpr().accept(this);
        if (!type1.equals(type2)) {
            boolean is2NotPrimitive = !type2.equals("int") && !type2.equals("boolean");
            boolean is1NotPrimitve = !type1.equals("int") && !type1.equals("boolean");
            //both are classes
            if ( is2NotPrimitive && is1NotPrimitve) {
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

                if (!foundRelation && !type2.equals("null")) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "the lefthand type '" + type1 + "'" +
                                          " in the binary operation ('==')" +
                                          " does not match righthand type '" +
                                          type2 + "'");
                }
            }
            //only one is class
            else {
                errorHandler.register(errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "the lefthand type '" + type1 + "'" +
                                      " in the binary operation ('==')" +
                                      " does not match righthand type '" +
                                      type2 + "'");
            }
        }
        
        return "boolean"; 
    }
    
    public Object visit(BinaryCompNeExpr node) { 
        int lineNum = node.getLineNum();
        String type1 = (String) node.getLeftExpr().accept(this);
        String type2 = (String) node.getRightExpr().accept(this);
        if (!type1.equals(type2)) {
            boolean is2NotPrimitive = !type2.equals("int") && !type2.equals("boolean");
            boolean is1NotPrimitve = !type1.equals("int") && !type1.equals("boolean");
            //both are classes
            if ( is2NotPrimitive && is1NotPrimitve) {
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

                if (!foundRelation && !type1.equals("boolean")) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "the lefthand type '" + type1 + "'" +
                                          " in the binary operation ('!=')" +
                                          " does not match righthand type '" +
                                          type2 + "'");
                }
            }
            //only one is class
            else {
                errorHandler.register(errorHandler.SEMANT_ERROR,
                                      fileName,
                                      lineNum,
                                      "the lefthand type '" + type1 + "'" +
                                      " in the binary operation ('!=')" +
                                      " does not match righthand type '" +
                                      type2 + "'");
            }
        }
        
        return "boolean";
    }
    
    public Object visit(BinaryCompLtExpr node) { 
        int lineNum = node.getLineNum();
        String type1 = (String) node.getLeftExpr().accept(this);
        String type2 = (String) node.getRightExpr().accept(this);
        if (!type1.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the lefthand type '" + type1 + "' in "
                                  + "the binary operation ('<') is incorrect;"
                                  + " should have been: int");
        }
        if (!type2.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the righthand type '" + type2 + "' in "
                                  + "the binary operation ('<') is incorrect;"
                                  + " should have been: int");
        }
        return "boolean"; 
    }
    
    public Object visit(BinaryCompLeqExpr node) { 
        int lineNum = node.getLineNum();
        String type1 = (String) node.getLeftExpr().accept(this);
        String type2 = (String) node.getRightExpr().accept(this);
        if (!type1.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the lefthand type '" + type1 + "' in "
                                  + "the binary operation ('<=') is incorrect;"
                                  + " should have been: int");
        }
        if (!type2.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the righthand type '" + type2 + "' in "
                                  + "the binary operation ('<=') is incorrect;"
                                  + " should have been: int");
        }
        return "boolean";
    }
    
    public Object visit(BinaryCompGtExpr node) {
        int lineNum = node.getLineNum();
        String type1 = (String) node.getLeftExpr().accept(this);
        String type2 = (String) node.getRightExpr().accept(this);
        if (!type1.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the lefthand type '" + type1 + "' in "
                                  + "the binary operation ('>') is incorrect;"
                                  + " should have been: int");
        }
        if (!type2.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the righthand type '" + type2 + "' in "
                                  + "the binary operation ('>') is incorrect;"
                                  + " should have been: int");
        }
        return "boolean";
    }
    
    public Object visit(BinaryCompGeqExpr node) { 
        int lineNum = node.getLineNum();
        String type1 = (String) node.getLeftExpr().accept(this);
        String type2 = (String) node.getRightExpr().accept(this);
        if (!type1.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the lefthand type '" + type1 + "' in "
                                  + "the binary operation ('>=') is incorrect;"
                                  + " should have been: int");
        }
        if (!type2.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the righthand type '" + type2 + "' in "
                                  + "the binary operation ('>=') is incorrect;"
                                  + " should have been: int");
        }
        return "boolean";
    }
    
    public Object visit(BinaryArithExpr node) { 
        throw new RuntimeException("This visitor method should not be called (node is abstract)");
    }
    
    public Object visit(BinaryArithPlusExpr node) { 
        int lineNum = node.getLineNum(); 
        
        String type1 = (String) node.getLeftExpr().accept(this);
        String type2 = (String) node.getRightExpr().accept(this);
        if (!type1.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the lefthand type '" + type1 + "' in "
                                  + "the binary operation ('+') is incorrect;"
                                  + " should have been: int");
        }
        if (!type2.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the righthand type '" + type2 + "' in "
                                  + "the binary operation ('+') is incorrect;"
                                  + " should have been: int");
        }
        return "int"; 
    }
    
    public Object visit(BinaryArithMinusExpr node) { 
        int lineNum = node.getLineNum();
        String type1 = (String) node.getLeftExpr().accept(this);
        String type2 = (String) node.getRightExpr().accept(this);
        if (!type1.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the lefthand type '" + type1 + "' in "
                                  + "the binary operation ('-') is incorrect;"
                                  + " should have been: int");
        }
        if (!type2.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the righthand type '" + type2 + "' in "
                                  + "the binary operation ('-') is incorrect;"
                                  + " should have been: int");
        }
        return "int"; 
    }
    
    public Object visit(BinaryArithTimesExpr node) {
        int lineNum = node.getLineNum();
        String type1 = (String) node.getLeftExpr().accept(this);
        String type2 = (String) node.getRightExpr().accept(this);
        if (!type1.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the lefthand type '" + type1 + "' in "
                                  + "the binary operation ('*') is incorrect;"
                                  + " should have been: int");
        }
        if (!type2.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the righthand type '" + type2 + "' in "
                                  + "the binary operation ('*') is incorrect;"
                                  + " should have been: int");
        }
        return "int"; 
    }
    
    public Object visit(BinaryArithDivideExpr node) { 
        int lineNum = node.getLineNum();
        String type1 = (String) node.getLeftExpr().accept(this);
        String type2 = (String) node.getRightExpr().accept(this);
        if (!type1.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the lefthand type '" + type1 + "' in "
                                  + "the binary operation ('/') is incorrect;"
                                  + " should have been: int");
        }
        if (!type2.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the righthand type '" + type2 + "' in "
                                  + "the binary operation ('/') is incorrect;"
                                  + " should have been: int");
        }
        return "int"; 
    }
    
    public Object visit(BinaryArithModulusExpr node) { 
        int lineNum = node.getLineNum();
        String type1 = (String) node.getLeftExpr().accept(this);
        String type2 = (String) node.getRightExpr().accept(this);
        if (!type1.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the lefthand type '" + type1 + "' in "
                                  + "the binary operation ('%') is incorrect;"
                                  + " should have been: int");
        }
        if (!type2.equals("int")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the righthand type '" + type2 + "' in "
                                  + "the binary operation ('%') is incorrect;"
                                  + " should have been: int");
        }
        return "int"; 
    }
    
    public Object visit(BinaryLogicExpr node) { 
        throw new RuntimeException("This visitor method should not be called (node is abstract)");
    }
    
    public Object visit(BinaryLogicAndExpr node) { 
        int lineNum = node.getLineNum();
        String type1 = (String) node.getLeftExpr().accept(this);
        String type2 = (String) node.getRightExpr().accept(this);
        if (!type1.equals("boolean")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the lefthand type '" + type1 + "' in "
                                  + "the binary operation ('&&') is incorrect;"
                                  + " should have been: boolean");
        }
        if (!type2.equals("boolean")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the righthand type '" + type2 + "' in "
                                  + "the binary operation ('&&') is incorrect;"
                                  + " should have been: boolean");
        }
        return "boolean"; 
    }
    
    public Object visit(BinaryLogicOrExpr node) { 
        int lineNum = node.getLineNum();
        String type1 = (String) node.getLeftExpr().accept(this);
        String type2 = (String) node.getRightExpr().accept(this);
        if (!type1.equals("boolean")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the lefthand type '" + type1 + "' in "
                                  + "the binary operation ('||') is incorrect;"
                                  + " should have been: boolean");
        }
        if (!type2.equals("boolean")) {
            errorHandler.register(errorHandler.SEMANT_ERROR,
                                  fileName,
                                  lineNum,
                                  "the righthand type '" + type2 + "' in "
                                  + "the binary operation ('||') is incorrect;"
                                  + " should have been: boolean");
        }
        return "boolean";
    }
    
    public Object visit(UnaryExpr node) { 
        throw new RuntimeException("This visitor method should not be called (node is abstract)");
    }
    
    public Object visit(UnaryNegExpr node) { 
        //Type check the expression, returns the type of the expression? Not sure though
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
        return "int"; 
    }
    
    public Object visit(UnaryNotExpr node) { 
        //Type check the expression, returns the type of the expression? Not sure though
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
        return "int";
    }
    
    public Object visit(VarExpr node) { 
        //node.getRef needs to be checked if it is this or super, check appropriate symbol table 
        //if found, return its type, else return "Object"
        //Much more, check slide 15-24 for rest
        int lineNum = node.getLineNum();
        String name = node.getName();
        if (node.getRef() != null)
        {
            String varType;        
            String refName = (String) node.getRef().accept(this);
            if (refName.equals("this")) {
                //check local 
                varType = (String) vTable.lookup("this." + name);
                int scopeLevel = vTable.getScopeLevel("this." + name); //-1 if not found
                // getSize() is total size, getCurrScopeSize is child size
                int inheritedScopeSize = vTable.getSize() - vTable.getCurrScopeSize(); //0 if not found
                if (scopeLevel <= inheritedScopeSize) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "variable '" + name + 
                                          "in assignment is undeclared");
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
                //check the parent's VarSymbolTable scope for type of b in a.b
                varType = (String) classMap.get(className).getParent()
                                        .getVarSymbolTable().lookup("this." + name);
                int scopeLevel = vTable.getScopeLevel("this." + name); //-1 if not found
                int inheritedScopeSize = vTable.getSize() - vTable.getCurrScopeSize();
                //TODO
                if (scopeLevel <= inheritedScopeSize) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "variable '" + name + 
                                          "in assignment is undeclared");
                    node.setExprType("Object");
                    return "Object";
                }
                //Everything is correct when ref is super
                else {
                    node.setExprType(varType);
                    return varType;
                }
            }
            //NEXT LOGIC POINT
            else if (refName.contains("[]")) {
                //name = length
                if (!name.equals("length")) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "bad reference to '" + refName +
                                          "': arrays do not have this field" 
                                          + " (they only have a 'length'" +
                                          " field)");
                }

            }
        }
        //ref does not exist here
        else if (name.equals("this")) {
            //Prob return classType
            node.setExprType(className);
            return className;
        }
        else if (name.equals("super")) {
            //Prob return superclassName
            String parentName = classMap.get(className).getParent().getName();
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
        return "Object"; 
    }
    
    public Object visit(ArrayExpr node) { 
        int lineNum = node.getLineNum();
        if (node.getRef() != null)
            node.getRef().accept(this);
        String index = (String) node.getIndex().accept(this); //Taking a big guess here
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
                int scopeLevel = vTable.getScopeLevel("this." + name); //-1 if not found
                // getSize() is total size, getCurrScopeSize is child size
                int inheritedScopeSize = vTable.getSize() - vTable.getCurrScopeSize(); //0 if not found
                if (scopeLevel <= inheritedScopeSize) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "variable '" + name + 
                                          "in assignment is undeclared");
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
                //check the parent's VarSymbolTable scope for type of b in a.b
                varType = (String) classMap.get(className).getParent()
                                        .getVarSymbolTable().lookup("this." + name);
                int scopeLevel = vTable.getScopeLevel("this." + name); //-1 if not found
                int inheritedScopeSize = vTable.getSize() - vTable.getCurrScopeSize();
                //TODO
                if (scopeLevel <= inheritedScopeSize) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "variable '" + name + 
                                          "in assignment is undeclared");
                    node.setExprType("Object");
                    return "Object";
                }
                //Everything is correct when ref is super
                else {
                    node.setExprType(varType);
                    return varType;
                }
            }
            //NEXT LOGIC POINT
            else if (refName.contains("[]")) {
                //name = length
                if (!name.equals("length")) {
                    errorHandler.register(errorHandler.SEMANT_ERROR,
                                          fileName,
                                          lineNum,
                                          "bad reference to '" + refName +
                                          "': arrays do not have this field" 
                                          + " (they only have a 'length'" +
                                          " field)");
                }

            }
        }
        //ref does not exist here
        else if (name.equals("this")) {
            //Prob return classType
            node.setExprType(className);
            return className;
        }
        else if (name.equals("super")) {
            //Prob return superclassName
            String parentName = classMap.get(className).getParent().getName();
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
        return "Object"; 
    }
    
    //Probably return a string of the type it is rather than this
    //Change very possibly
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
