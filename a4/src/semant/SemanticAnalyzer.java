/* By Yee Thao, Cheng Xiong, Esteban Lopez
   Bantam Java Compiler and Language Toolset.

   Copyright (C) 2007 by Marc Corliss (corliss@hws.edu) and 
                         E Christopher Lewis (lewis@vmware.com).
   ALL RIGHTS RESERVED.

   The Bantam Java toolset is distributed under the following 
   conditions:

     You may make copies of the toolset for your own use and 
     modify those copies.

     All copies of the toolset must retain the author names and 
     copyright notice.

     You may not sell the toolset or distribute it in 
     conjunction with a commerical product or service without 
     the expressed written consent of the authors.

   THIS SOFTWARE IS PROVIDED ``AS IS'' AND WITHOUT ANY EXPRESS 
   OR IMPLIED WARRANTIES, INCLUDING, WITHOUT LIMITATION, THE 
   IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A 
   PARTICULAR PURPOSE. 
*/

package semant;

import ast.*;
import util.*;
import visitor.*;
import java.util.*;

/** The <tt>SemanticAnalyzer</tt> class performs semantic analysis.
  * In particular this class is able to perform (via the <tt>analyze()</tt>
  * method) the following tests and analyses: (1) legal inheritence
  * hierarchy (all classes have existing parent, no cycles), (2) 
  * legal class member declaration, (3) there is a correct Main class
  * and main() method, and (4) each class member is correctly typed.
  * 
  * This class is incomplete and will need to be implemented by the student. 
  * */
public class SemanticAnalyzer {
    /** Root of the AST */
    private Program program;
    
    /** Root of the class hierarchy tree */
    private ClassTreeNode root;
    
    /** Maps class names to ClassTreeNode objects describing the class */
    private Hashtable<String,ClassTreeNode>
	classMap = new Hashtable<String,ClassTreeNode>();

    /** Ordered list of ClassTreeNode objects (breadth first) */
    private Vector<ClassTreeNode> orderedClassList = new Vector<ClassTreeNode>();
    
    /** Object for error handling */
    private ErrorHandler errorHandler = new ErrorHandler();
    
    /** Boolean indicating whether debugging is enabled */
    private boolean debug = false;

    /** Maximum number of inherited and non-inherited fields that can
     * be defined for any one class */
    private final int MAX_NUM_FIELDS = 1500;

    /** SemanticAnalyzer constructor
      * @param program root of the AST
      * @param debug boolean indicating whether debugging is enabled
      * */
    public SemanticAnalyzer(Program program, boolean debug) {
	this.program = program;
	this.debug = debug;
    }
    
    /** Analyze the AST checking for semantic errors and annotating the tree
      * Also builds an auxiliary class hierarchy tree 
      * @return root of the class hierarchy tree (needed for code generation)
      *
      * Must add code to do the following:
      *   1 - build built-in class nodes in class hierarchy tree (already done) and
      *       build and check the rest of the class hierarchy tree
      *   2 - build the environment for each class (adding class members only) 
      *       and check that members are declared properly
      *   3 - check that the Main class and main method are declared properly
      *   4 - type check each class member
      * See the lab manual for more details on each of these steps.
      * */
    public ClassTreeNode analyze() {

	// list of class declarations
	ClassList classList = program.getClassList();
	
	// PART 1: class tree
	// build and check class hierarchy tree
	buildClassTree(classList);
	
	// PART 2: class symbol table
	// build class symbol table for members and check that members are
	// declared properly
	buildSymbolTable();
	
	// PART 3: Main class/main method
	// check that there is a Main class and main method
	checkMain();
	
	// PART 4: type checking
	// type check each member (fields and methods) of each user-defined class
	typeCheck();

	errorHandler.checkErrors();	
	return root;

    }
    
    /** Add built in classes to the class tree 
      * */
    private void updateBuiltins() {
	// create AST node for object
	Class_ astNode = 
	    new Class_(-1, "<built-in class>", "Object", null, 
		       (MemberList)(new MemberList(-1))
		       .addElement(new Method(-1, "Object", "clone", 
					      new FormalList(-1), 
					      (StmtList)(new StmtList(-1))
					      .addElement(new ReturnStmt(-1, null)))));
	// create a class tree node for object, save in variable root
	root = new ClassTreeNode(astNode,
				 /*built-in?*/true, /*extendable?*/true, classMap);
	// add object class tree node to the mapping
	classMap.put("Object", root);
	
	// note: String, TextIO, and Sys all have fields that are not
	// shown below.  Because these classes cannot be extended and
	// fields are protected, they cannot be accessed by other
	// classes, so they do not have to be included in the AST.
	
	// create AST node for String
	astNode =
	    new Class_(-1, "<built-in class>",
		       "String", "Object", 					
		       (MemberList)(new MemberList(-1))
                       .addElement(new Method(-1, "int", "length",
                                              new FormalList(-1), 
					      (StmtList)(new StmtList(-1))
					      .addElement(new ReturnStmt(-1, null))))
		       .addElement(new Method(-1, "boolean", "equals",
					      (FormalList)(new FormalList(-1))
					      .addElement(new Formal(-1, "Object", 
								     "str")),
					      (StmtList)(new StmtList(-1))
					      .addElement(new ReturnStmt(-1, null))))
		       .addElement(new Method(-1, "String", "substring",
					      (FormalList)(new FormalList(-1))
					      .addElement(new Formal(-1, "int", 
								     "beginIndex"))
					      .addElement(new Formal(-1, "int",
								     "endIndex")),
					      (StmtList)(new StmtList(-1))
					      .addElement(new ReturnStmt(-1, null))))
		       .addElement(new Method(-1, "String", "concat",
					      (FormalList)(new FormalList(-1))
					      .addElement(new Formal(-1, "String",
								     "str")), 
					      (StmtList)(new StmtList(-1))
					      .addElement(new ReturnStmt(-1, null)))));
	// create class tree node for String, add it to the mapping
	classMap.put("String", new ClassTreeNode(astNode, /*built-in?*/true,
						 /*extendable?*/false, classMap));
	
	// create AST node for TextIO
	astNode =
	    new Class_(-1, "<built-in class>", 
		       "TextIO", "Object", 					
		       (MemberList)(new MemberList(-1))
		       .addElement(new Method(-1, "void", "readStdin", 
					      new FormalList(-1), 
					      (StmtList)(new StmtList(-1))
					      .addElement(new ReturnStmt(-1, null))))
		       .addElement(new Method(-1, "void", "readFile",
					      (FormalList)(new FormalList(-1))
					      .addElement(new Formal(-1, "String", 
								     "readFile")),
					      (StmtList)(new StmtList(-1))
					      .addElement(new ReturnStmt(-1, null))))
		       .addElement(new Method(-1, "void", "writeStdout", 
					      new FormalList(-1), 
					      (StmtList)(new StmtList(-1))
					      .addElement(new ReturnStmt(-1, null))))
		       .addElement(new Method(-1, "void", "writeStderr", 
					      new FormalList(-1), 
					      (StmtList)(new StmtList(-1))
					      .addElement(new ReturnStmt(-1, null))))
		       .addElement(new Method(-1, "void", "writeFile",
					      (FormalList)(new FormalList(-1))
					      .addElement(new Formal(-1, "String", 
								     "writeFile")),
					      (StmtList)(new StmtList(-1))
					      .addElement(new ReturnStmt(-1, null))))
		       .addElement(new Method(-1, "String", "getString",
					      new FormalList(-1), 
					      (StmtList)(new StmtList(-1))
					      .addElement(new ReturnStmt(-1, null))))
		       .addElement(new Method(-1, "int", "getInt",
					      new FormalList(-1), 
					      (StmtList)(new StmtList(-1))
					      .addElement(new ReturnStmt(-1, null))))
		       .addElement(new Method(-1, "TextIO", "putString",
					      (FormalList)(new FormalList(-1))
					      .addElement(new Formal(-1, "String", 
								     "str")),
					      (StmtList)(new StmtList(-1))
					      .addElement(new ReturnStmt(-1, null))))
		       .addElement(new Method(-1, "TextIO", "putInt",
					      (FormalList)(new FormalList(-1))
					      .addElement(new Formal(-1, "int", 
								     "n")),
					      (StmtList)(new StmtList(-1))
					      .addElement(new ReturnStmt(-1, null)))));
	// create class tree node for TextIO, add it to the mapping
	classMap.put("TextIO", new ClassTreeNode(astNode, /*built-in?*/true,
						 /*extendable?*/false, classMap));
	
	// create AST node for Sys
	astNode =
	    new Class_(-1, "<built-in class>",
		       "Sys", "Object", 
		       (MemberList)(new MemberList(-1))
		       .addElement(new Method(-1, "void", "exit",
					      (FormalList)(new FormalList(-1))
					      .addElement(new Formal(-1, "int", 
								     "status")), 
					      (StmtList)(new StmtList(-1))
					      .addElement(new ReturnStmt(-1, null))))
		       /*
		       .addElement(new Method(-1, "int", "time",
					      new FormalList(-1), 
					      (StmtList)(new StmtList(-1))
				              .addElement(new ReturnStmt(-1, null))))
                       */
		       );
	// create class tree node for Sys, add it to the mapping
	classMap.put("Sys", new ClassTreeNode(astNode, /*built-in?*/true,
					      /*extendable?*/false, classMap));
    }


    /*************************************************************************
     *       You should not have to modify the code above this point         *
     *************************************************************************/

    /** Build class hierarchy tree, checking to make sure it is well-formed
      * Broken up into three parts: (1) build class tree nodes, add nodes to 
      * the mapping, and check for duplicate class names; (2) set parent links
      * of the nodes, and check if parent exists; (3) check that there are
      * no cycles in the graph (i.e., that it's a tree)
      * @param classList list of AST class nodes
      * */
    private void buildClassTree(ClassList classList)
    {
	    updateBuiltins();
		//Part 1
		Iterator iter = classList.getIterator();
		while (iter.hasNext()) {
			ClassTreeNode ctn = new ClassTreeNode((Class_)iter.next(), false, true,
											      classMap);
			if (!classMap.containsKey(ctn.getName())) {
				orderedClassList.addElement(ctn);
				classMap.put(ctn.getName(), ctn);
			}
			else {
				if (classMap.get(ctn.getName()).isBuiltIn()) {
					errorHandler.register(errorHandler.SEMANT_ERROR, 
										  ctn.getASTNode().getFilename(), 
										  ctn.getASTNode().getLineNum(),
										  "built-in class '" +
										  ctn.getName() + 
										  "' cannot be redefined");
				}
				else {
					errorHandler.register(errorHandler.SEMANT_ERROR, 
										  ctn.getASTNode().getFilename(), 
										  ctn.getASTNode().getLineNum(),
										  "duplicate class '" +
										  ctn.getName() + 
										  "' (originally defined " +
										  "at line " + 
										  ctn.getASTNode().getLineNum());
				}
			}
		}

		// Part 2
		for (int i = 0; i < orderedClassList.size(); i++) {
			ClassTreeNode ctn = orderedClassList.get(i);
			String parent = ctn.getASTNode().getParent();
			if (classMap.containsKey(parent)) {
				if (classMap.get(parent).isExtendable()) {
					ctn.setParent(classMap.get(parent));
				}
				else {
					errorHandler.register(errorHandler.SEMANT_ERROR, 
										  ctn.getASTNode().getFilename(), 
										  ctn.getASTNode().getLineNum(),
										  "class '" +
										  ctn.getName() + 
										  "' extends non-extendable class " +
										  ctn.getASTNode().getParent());
				}
			}
			else {
				errorHandler.register(errorHandler.SEMANT_ERROR, 
										ctn.getASTNode().getFilename(), 
										ctn.getASTNode().getLineNum(),
										"class '" +
										ctn.getName() + 
										"' extends non-existent class " +
										ctn.getASTNode().getParent());
			}
		}

		// Part 3
		for (int i = 0; i < orderedClassList.size(); i++) {
			Vector<ClassTreeNode> v = new Vector<ClassTreeNode>();
	    	for (ClassTreeNode ctn = orderedClassList.get(i).getParent();
			     ctn != null;
				 ctn = ctn.getParent()) {

				if (v.contains(ctn)) {
					errorHandler.register(errorHandler.SEMANT_ERROR, 
								          ctn.getASTNode().getFilename(), 
									      ctn.getASTNode().getLineNum(),
								          "inheritance cylce " +
										  "found involving class '" +
									      ctn.getName() + "'");
					break;
				}
				v.add(ctn);
			}
		}
    }
    
    /** Build symbol table for each class
      * Note: builds symbol table only for class members not for locals
      * Must be done before any type checking can be done since classes may
      * contain code that refer to members in other classes
      * Note also: cannot build symbol table for a subclass before its 
      * parent class (since child may use symbols in superclass).
      * */
    private void buildSymbolTable()
    {
		ClassEnvVisitor cev = new ClassEnvVisitor();
		for (ClassTreeNode node : orderedClassList) {
			node.getMethodSymbolTable().enterScope();
			node.getVarSymbolTable().enterScope();
			Object o1 = cev.visit(node.getASTNode());
			MemberList ml = (MemberList) o1;
			for (Iterator it = ml.getIterator(); it.hasNext(); ) {
				Object o2 = it.next();
				Member mem = (Member) o2;
				if (mem instanceof Method) {
					Method m = (Method) mem;
					String name = m.getName();
					node.getMethodSymbolTable().add(name, m);
					System.out.println("The method is " + m.getName());
				}
				else {
					Field f = (Field) mem;
					node.getVarSymbolTable().add(f.getName(), f.getType());
					System.out.println("The data field is " + f.getName());
				}
			}
		}
		
	// complete this method
    }
    
    /** Check that Main class and main() method are defined correctly
      * */
    private void checkMain()
    {
	// complete this method
    }
    
    /** Type check each class member
      * */
    private void typeCheck()
    {
	// complete this method
    }

}
