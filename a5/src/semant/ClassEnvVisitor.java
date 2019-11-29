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
        String checkType = fieldType.replace("[]", "");
        int lineNum = node.getLineNum();
        if (name.equals("null") || name.equals("this") || 
            name.equals("super")) {
            noError = false;
            errorHandler.register(errorHandler.SEMANT_ERROR, 
                                  fileName, 
                                  lineNum,
                                  "fields cannot be named '" + name + "'");
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
        if ((!checkType.equals("int") && !checkType.equals("boolean")) &&
				  !classMap.containsKey(checkType)) {
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
            vTable.add("this." + name, fieldType);
        }
        return node;
    }

    public Object visit(Method node) {
        boolean noError = true;
        String name = node.getName();
        String returnType = node.getReturnType();
        String checkType = returnType.replace("[]", "");
        int lineNum = node.getLineNum();
        if ((!checkType.equals("int") && !checkType.equals("boolean") && 
            !checkType.equals("void")) &&
            !classMap.containsKey(checkType)) {
            noError = false;
			errorHandler.register(errorHandler.SEMANT_ERROR, 
                                  fileName, 
                                  lineNum,
                                  "return type '" + returnType +  
                                  "' of method '" + name +
                                  "' is undefined");
        }
        if (name.equals("null")) {
            noError = false;
            errorHandler.register(errorHandler.SEMANT_ERROR, 
                                  fileName, 
                                  lineNum,
                                  "methods cannot be named 'null'");
        }
        else if (name.equals("this")) {
            noError = false;
            errorHandler.register(errorHandler.SEMANT_ERROR, 
                                  fileName, 
                                  lineNum,
                                  "methods cannot be named 'this'");
        }
        else if (name.equals("super")) {
            noError = false;
            errorHandler.register(errorHandler.SEMANT_ERROR, 
                                  fileName, 
                                  lineNum,
                                  "methods cannot be named 'super'");
        }
        else if (mTable.peek(name) != null) {
            noError = false;
            errorHandler.register(errorHandler.SEMANT_ERROR, 
                                  fileName, 
                                  lineNum,
                                  "method '" + name +  
								  "' is already defined in class" +
								  " '" + className + "'");
        }
        else if (mTable.lookup(name) != null) {
            Method n = (Method) mTable.lookup(name);
            if (!n.getReturnType().equals(returnType)) {
                noError = false;
                errorHandler.register(errorHandler.SEMANT_ERROR, 
									  fileName, 
									  lineNum,
                                      "overriding method '" + name + 
                                      "' has return type '" + 
                                      returnType + "', which differs from"
                                      + " the inherited method's "+ 
                                      "return type '" + 
                                      n.getReturnType() + "'");
            }
            else if (n.getFormalList().getSize()!= 
                     node.getFormalList().getSize()) {
                noError = false;
                errorHandler.register(errorHandler.SEMANT_ERROR, 
                                      fileName, 
                                      lineNum,
                                      "overriding method '" + name +  
                                      "' has " + 
                                      node.getFormalList().getSize() +
                                      " formals, which differs from the" +
                                      " inherited method (" + 
                                      n.getFormalList().getSize() + ")");
            } 
            else {
                int count = 1;
                Iterator current = node.getFormalList().getIterator();
                for(Iterator parent = n.getFormalList().getIterator();
                    parent.hasNext();) {
                    Formal p = (Formal) parent.next();
                    Formal c = (Formal) current.next();
                    if (!p.getType().equals(c.getType())) {
                        noError = false;
                        errorHandler.register(errorHandler.SEMANT_ERROR, 
                                              fileName, 
                                              lineNum,
                                              "overriding method '" +
                                               name +  
                                              "' has formal type '" + 
                                              c.getType() +
                                               "' for formal " + 
                                              count +
                                               ", which differs from the" +
                                              " inherited method's formal "
                                              + "type '" 
                                              + p.getType() + "'");
                    }
                    count++;
                }
            }
        }
        if (noError)
            mTable.add(name, node);
        return node;
    }
}