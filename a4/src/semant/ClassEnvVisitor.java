package semant;
import ast.*;
import java.util.*;

public class ClassEnvVisitor extends SemanticVisitor{
    public Object visit(Class_ node) {
        MemberList  m = node.getMemberList();
        return m;
    }

    public Object visit(MemberList node) {
        return node;
    }
}