/* Bantam Java Compiler and Language Toolset.

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

package ast;

import visitor.*;

import java.util.*;

/** The <tt>FormalList</tt> class represents a list of formal parameters.
  * @see ListNode
  * @see Formal
  * */
public class FormalList extends ListNode {
    /** Formal list constructor
      * @param lineNum source line number corresponding to this AST node
      * */
    public FormalList(int lineNum) {
	super(lineNum);
    }
    
    /** Visitor method
      * @param v visitor object
      * @return result of visiting this node
      * @see visitor.Visitor
      * */
    public Object accept(Visitor v) {
	return v.visit(this);
    }
}
