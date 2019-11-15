package semant;
import ast.*;
import util.*;
import semant.*;

import java.util.*;

public class ClassEnvVisitor extends SemanticVisitor{
    
    private SymbolTable vTable;
    private SymbolTable mTable;
    private ErrorHandler errorHandler;
    private String fileName;
    private String className;
    private Hashtable<String,ClassTreeNode> classMap;
    
    public ClassEnvVisitor(SymbolTable v, SymbolTable m, ErrorHandler e, 
                           Hashtable<String,ClassTreeNode> cm) {
        vTable = v;
        mTable = m;
        errorHandler = e;
        classMap = cm;
    }

    public Object visit(Class_ node) {
        
        vTable.enterScope();
        mTable.enterScope();
        fileName = node.getFilename();
        className = node.getName();
        node.getMemberList().accept(this);
        //vTable.exitScope();
        //mTable.exitScope();
        return node;
    }

    public Object visit(MemberList node) {
        
        for (Iterator it = node.getIterator(); it.hasNext(); ){
            
            ((Member)it.next()).accept(this);
        }
        
        return node;
    }

    public Object visit(Field node) {
        boolean noError = true;
        String name = node.getName();
        String fieldType = node.getType();
        int lineNum = node.getLineNum();
        if (name.equals("null")) {
            noError = false;
            errorHandler.register(errorHandler.SEMANT_ERROR, 
                                  fileName, 
                                  lineNum,
                                  "fields cannot be named 'null'");
        }
        else if (name.equals("this")) {
            noError = false;
            errorHandler.register(errorHandler.SEMANT_ERROR, 
                                  fileName, 
                                  lineNum,
                                  "fields cannot be named 'this'");
        }
        else if (name.equals("super")) {
            noError = false;
            errorHandler.register(errorHandler.SEMANT_ERROR, 
                                  fileName, 
                                  lineNum,
                                  "fields cannot be named 'super'");
        }
        else if (vTable.peek(name) != null) {
            noError = false;
            errorHandler.register(errorHandler.SEMANT_ERROR, 
                                  fileName, 
                                  lineNum,
                                  "field '" + name +  
								  "' is already defined in class" +
								  " '" + className + "'");
        }
        if ((!fieldType.equals("int") && !fieldType.equals("boolean")) &&
				  !classMap.containsKey(fieldType)) {
                    noError = false;
					errorHandler.register(errorHandler.SEMANT_ERROR, 
										  fileName, 
										  lineNum,
										  "type '" + fieldType +  
										  "' of field '" + name +
										  "' is undefined");
        }
        if (noError) {
            vTable.add(name, fieldType);
        }
        return node;
    }

    public Object visit(Method node) {
        String name = node.getName();
        String returnType = node.getReturnType();
        int lineNum = node.getLineNum();
        if (name.equals("null")) {
            errorHandler.register(errorHandler.SEMANT_ERROR, 
                                  fileName, 
                                  lineNum,
                                  "methods cannot be named 'null'");
        }
        else if (name.equals("this")) {
            errorHandler.register(errorHandler.SEMANT_ERROR, 
                                  fileName, 
                                  lineNum,
                                  "methods cannot be named 'this'");
        }
        else if (name.equals("super")) {
            errorHandler.register(errorHandler.SEMANT_ERROR, 
                                  fileName, 
                                  lineNum,
                                  "methods cannot be named 'super'");
        }
        else if (mTable.peek(name) != null) {
            errorHandler.register(errorHandler.SEMANT_ERROR, 
                                  fileName, 
                                  lineNum,
                                  "method '" + name +  
								  "' is already defined in class" +
								  " '" + className + "'");
        }
        else if (mTable.lookup(name) != null) {
            System.out.println("Here");
            Method n = (Method) mTable.lookup(name);
            System.out.println("Where chu at?");
            if (!n.getReturnType().equals(returnType)) {
                errorHandler.register(errorHandler.SEMANT_ERROR, 
									  fileName, 
									  lineNum,
                                      "overriding method '" + name + 
                                      "' has return type '" + returnType +
                                      "', which differs from the inerited "+ 
                                      "method's return type '" + 
                                      n.getReturnType() + "'");
            }
        }
        else {
            if ((!returnType.equals("int") && !returnType.equals("boolean") && 
                 !returnType.equals("void")) &&
                 !classMap.containsKey(returnType)) {
						errorHandler.register(errorHandler.SEMANT_ERROR, 
											  fileName, 
											  lineNum,
											  "type '" + returnType +  
											  "' of method '" + name +
											  "' is undefined");
            }
            else {
                mTable.add(name, node);
            }
        }
        return node;
    }
}