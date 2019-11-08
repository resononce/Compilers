package semant;
import ast.*;
import java.util.*;

public class ClassEnvVisitor extends SemanticVisitor{
    public Object visit(Class_ node) {
        MemberList  m = node.getMemberList();
        return m;
    }

    public Object visit(MemberList node) {
        for (Iterator it = node.getIterator(); it.hasNext(); )
            ((Member)it.next()).accept(this);
        return node;
    }

    public Object visit(Field node) { 
        return node; 
    }

    public Object visit(Method node) {
        return node; 
    }
}