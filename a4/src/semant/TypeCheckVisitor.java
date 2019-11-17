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
        String rhsType = node.getInit().getExprType();
        String lhsType = node.getType();
        int lineNum = node.getLineNum();
        String name = node.getName();
        String rCheckType = rhsType.replaceAll("[]", "");
        String lCheckType = lhsType.replaceAll("[]", "");
        if (rhsType.equals("void")) {
            errorHandler.register(errorHandler.SEMANT_ERROR, 
                                  fileName, 
                                  lineNum,
                                  "expression type '" + rhsType +  
                                  "' of field '" + name +
                                  "' cannot be void");
        } 
        else if ((lCheckType.equals("boolean") || lCheckType.equals("int")) ||
                 (rCheckType.equals("boolean") || rCheckType.equals("int")) &&
                 !lCheckType.equals(rCheckType)) {
            errorHandler.register(errorHandler.SEMANT_ERROR, 
                                  fileName, 
                                  lineNum,
                                  "expression type '" + rhsType +  
                                  "' of field '" + name +
                                  "' does not match declared type '" +
                                  lhsType + "'");
        } 
        else if (classMap.contains(lCheckType) && 
                 classMap.contains(rCheckType)) {
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
        return null; 
    }

    public Object visit(Method node) {
        mTable.enterScope();
        methodName = node.getName();
        methodReturnType = node.getReturnType();
        for (Iterator it = node.getFormalList().getIterator(); it.hasNext();) {
            Formal f = (Formal) it.next();
            int lineNum = f.getLineNum();
            String name = f.getName();
            String type = f.getType();
            String checkType = type.replaceAll("[]", "");
            boolean noError = true;
            if ((!checkType.equals("boolean") && !checkType.equals("int")) &&
                !classMap.contains(checkType)) {
                    noError = false;
                    errorHandler.register(errorHandler.SEMANT_ERROR, 
                                          fileName, 
                                          lineNum,
                                          "type '" + type +  
                                          "' of formal '" + name +
                                          "' is undefined");
            }
            if (mTable.peek(f.getName()) != null){
                noError = false;
                errorHandler.register(errorHandler.SEMANT_ERROR, 
                                      fileName, 
                                      lineNum,
                                      "formal '" + name +  
                                      "' is multiply defined");
            }
            else if (name.equals("null") || name.equals("super") || 
                name.equals("this")) {
                noError = false;
                errorHandler.register(errorHandler.SEMANT_ERROR, 
                                      fileName, 
                                      lineNum,
                                      "formals cannot be named '" + name + "'");
            }
            if (noError) {
                mTable.add(f.getName(), f.getType());
            }
        }
        node.getStmtList().accept(this);
        return null; 
    }

    public Object visit(StmtList node) {
        for (Iterator it = node.getIterator(); it.hasNext(); )
            ((Stmt)it.next()).accept(this);
        return null;
    }

    public Object visit(DeclStmt node) {
        boolean noError = true;
        int lineNum = node.getLineNum();
        String type = node.getType();
        String checkType = type.replaceAll("[]", "");
        String name = node.getName();
        //Type Check
        if ((!checkType.equals("boolean") && !checkType.equals("int")) &&
            !classMap.contains(checkType)) {
                errorHandler.register(errorHandler.SEMANT_ERROR, 
                                      fileName, 
                                      lineNum,
                                      "type '" + type +  
                                      "' of delcaration '" + name + 
                                      "' is undefined");
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
        else if (vTable.peek(name) != null) {
            noError = false;
            errorHandler.register(errorHandler.SEMANT_ERROR, 
                                    fileName, 
                                    lineNum,
                                    "varible '" + name +  
                                    "' is already defined in method" +
                                    methodName );
        } 
        //Will continue when done with Expr
        node.getInit().accept(this);
        return null;
    }

    public Object visit(ExprStmt node) { 
        node.getExpr().accept(this);
        return null; //Might return type
    }
    

    public Object visit(IfStmt node) { 
        node.getPredExpr().accept(this);
        node.getThenStmt().accept(this);
        node.getElseStmt().accept(this);
        return null; 
    }

    public Object visit(WhileStmt node) { 
        node.getPredExpr().accept(this);
        node.getBodyStmt().accept(this);
        return null; 
    }
    
    public Object visit(ForStmt node) { 
        if (node.getInitExpr() != null)
            node.getInitExpr().accept(this);
        if (node.getPredExpr() != null)
            node.getPredExpr().accept(this);
        if (node.getUpdateExpr() != null)
            node.getUpdateExpr().accept(this);
        node.getBodyStmt().accept(this);
        return null; 
    }
    
    public Object visit(BreakStmt node) { 
        return null;
    }
    
    public Object visit(BlockStmt node) { 
        node.getStmtList().accept(this);
        return null; 
    }
    
    public Object visit(ReturnStmt node) { 
        if (node.getExpr() != null)
            node.getExpr().accept(this);
        return null; 
    }
    
    public Object visit(ExprList node) {
        for (Iterator it = node.getIterator(); it.hasNext(); )
            ((Expr)it.next()).accept(this);
        return null;
    }

    public Object visit(Expr node) { 
        throw new RuntimeException("This visitor method should not be called (node is abstract)");
    }
    
    public Object visit(DispatchExpr node) { 
        node.getRefExpr().accept(this);
        node.getActualList().accept(this);
        return null; 
    }
    
    public Object visit(NewExpr node) { 
        return null; 
    }
    
    
    public Object visit(NewArrayExpr node) { 
        node.getSize().accept(this);
        return null; 
    }
    
    public Object visit(InstanceofExpr node) { 
        node.getExpr().accept(this);
        return null; 
    }
    
    public Object visit(CastExpr node) { 
        node.getExpr().accept(this);
        return null; 
    }
    
    public Object visit(AssignExpr node) { 
        node.getExpr().accept(this);
        return null; 
    }
    
    public Object visit(ArrayAssignExpr node) { 
        node.getIndex().accept(this);
        node.getExpr().accept(this);
        return null; 
    }
    
    public Object visit(BinaryExpr node) { 
        throw new RuntimeException("This visitor method should not be called (node is abstract)");
    }
    
    public Object visit(BinaryCompExpr node) { 
        throw new RuntimeException("This visitor method should not be called (node is abstract)");
    }
    
    public Object visit(BinaryCompEqExpr node) { 
        node.getLeftExpr().accept(this);
        node.getRightExpr().accept(this);
        return null; 
    }
    
    public Object visit(BinaryCompNeExpr node) { 
        node.getLeftExpr().accept(this);
        node.getRightExpr().accept(this);
        return null; 
    }
    
    public Object visit(BinaryCompLtExpr node) { 
        node.getLeftExpr().accept(this);
        node.getRightExpr().accept(this);
        return null; 
    }
    
    public Object visit(BinaryCompLeqExpr node) { 
        node.getLeftExpr().accept(this);
        node.getRightExpr().accept(this);
        return null; 
    }
    
    public Object visit(BinaryCompGtExpr node) { 
        node.getLeftExpr().accept(this);
        node.getRightExpr().accept(this);
        return null; 
    }
    
    public Object visit(BinaryCompGeqExpr node) { 
        node.getLeftExpr().accept(this);
        node.getRightExpr().accept(this);
        return null; 
    }
    
    public Object visit(BinaryArithExpr node) { 
        throw new RuntimeException("This visitor method should not be called (node is abstract)");
    }
    
    public Object visit(BinaryArithPlusExpr node) { 
        node.getLeftExpr().accept(this);
        node.getRightExpr().accept(this);
        return null; 
    }
    
    public Object visit(BinaryArithMinusExpr node) { 
        node.getLeftExpr().accept(this);
        node.getRightExpr().accept(this);
        return null; 
    }
    
    public Object visit(BinaryArithTimesExpr node) { 
        node.getLeftExpr().accept(this);
        node.getRightExpr().accept(this);
        return null; 
    }
    
    public Object visit(BinaryArithDivideExpr node) { 
        node.getLeftExpr().accept(this);
        node.getRightExpr().accept(this);
        return null; 
    }
    
    public Object visit(BinaryArithModulusExpr node) { 
        node.getLeftExpr().accept(this);
        node.getRightExpr().accept(this);
        return null; 
    }
    
    public Object visit(BinaryLogicExpr node) { 
        throw new RuntimeException("This visitor method should not be called (node is abstract)");
    }
    
    public Object visit(BinaryLogicAndExpr node) { 
        node.getLeftExpr().accept(this);
        node.getRightExpr().accept(this);
        return null; 
    }
    
    public Object visit(BinaryLogicOrExpr node) { 
        node.getLeftExpr().accept(this);
        node.getRightExpr().accept(this);
        return null; 
    }
    
    public Object visit(UnaryExpr node) { 
        throw new RuntimeException("This visitor method should not be called (node is abstract)");
    }
    
    public Object visit(UnaryNegExpr node) { 
        node.getExpr().accept(this);
        return null; 
    }
    
    public Object visit(UnaryNotExpr node) { 
        node.getExpr().accept(this);
        return null; 
    }
    
    public Object visit(UnaryIncrExpr node) { 
        node.getExpr().accept(this);
        return null; 
    }
    
    public Object visit(UnaryDecrExpr node) { 
        //Check if the expr is VarExpr or ArrayExpr else error
        node.getExpr().accept(this);
        return null; 
    }
    
    public Object visit(VarExpr node) { 
        if (node.getRef() != null)
            node.getRef().accept(this);
        return null; 
    }
    
    public Object visit(ArrayExpr node) { 
        if (node.getRef() != null)
            node.getRef().accept(this);
        node.getIndex().accept(this);
        return null; 
    }
    
    public Object visit(ConstIntExpr node) { 
        return "int";
    }
    
    public Object visit(ConstBooleanExpr node) { 
        return "boolean"; 
    }
    
    public Object visit(ConstStringExpr node) { 
        return "String"; 
    }
}