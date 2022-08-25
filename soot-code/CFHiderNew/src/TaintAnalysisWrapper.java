import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import polyglot.types.Flags;
import java_cup.internal_error;
import soot.G;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.AssignStmt;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.toolkits.graph.UnitGraph;
import soot.toolkits.scalar.ForwardFlowAnalysis;


public class TaintAnalysisWrapper {
	 public TaintAnalysisWrapper(UnitGraph graph,Map<String, Set<Value>> taintMap,String name,Map<String, int[]> hashfortaint,List<String> sootMethodsNameList) {
			TaintAnalysis analysis = new TaintAnalysis(graph,name,hashfortaint,sootMethodsNameList);
			
			taintMap.put(name, analysis.outSet);
			//if (analysis.hashtaint != null) {
				hashfortaint.putAll(analysis.hashtaint);
			//}
			
			G.v().out.println("analysis.taintedSinks.size():"+analysis.taintedSinks.size());
			if(analysis.taintedSinks.size() > 0) {
			    G.v().out.println("zystble: ");
			    Set keys = analysis.taintedSinks.keySet();
			    for(Object key : keys){
		    		  G.v().out.println("key:"+key+" value:"+analysis.taintedSinks.get(key).toString());
		    	  }
			}
		    }
}
interface GetUseBoxes {
    public List<ValueBox> getUseBoxes();
}
class TaintAnalysis extends ForwardFlowAnalysis<Unit, Set<Value>> {
    public Map<Unit, Set<Set<Value>>> taintedSinks;
    public Set<Value> outSet;
    public String MethodName;
    public Map<String, int[]> hashtaint;
    public Map<String, int[]> tainttemp;
    public int[] temp;
    public boolean flag;
    public List<String> sMethodsList;
    public TaintAnalysis(UnitGraph graph,String name,Map<String, int[]> hashfortaint,List<String> sootMethodsNameList) {
		super(graph);
		//tainted = taintMap;
		taintedSinks = new HashMap();
		outSet = new HashSet<>();
		MethodName = new String();
		MethodName = name;
		hashtaint = new HashMap<>();
		tainttemp = hashfortaint;
		temp = new int[10];
		flag = false;
		sMethodsList = new ArrayList<>();
		sMethodsList = sootMethodsNameList;
		doAnalysis();
		
		//taintMap.putAll(tainted);
    }

    protected Set<Value> newInitialFlow() {
	return new HashSet();
    }

    protected Set<Value> entryInitialFlow() {
	return new HashSet();
    }

    protected void copy(Set<Value> src, Set<Value> dest) {
		dest.removeAll(dest);
		dest.addAll(src);
    }

    // Called after if/else blocks, with the result of the analysis from both
    // branches.
    protected void merge(Set<Value> in1, Set<Value> in2, Set<Value> out) {
		out.removeAll(out);
		out.addAll(in1);
		out.addAll(in2);
    }

    protected void flowThrough(Set<Value> in, Unit node, Set<Value> out) {
		Set<Value> filteredIn = stillTaintedValues(in, node);
		Set<Value> newOut = newTaintedValues(filteredIn, node);
	
		out.removeAll(out);
		out.addAll(filteredIn);
		out.addAll(newOut);
		if (in.size()>0) {
			G.v().out.println("flowThrough in :"+in);
			G.v().out.println("flowThrough node:"+node);
			G.v().out.println("flowThrough out:"+out);
		}
		if (!out.isEmpty()) {
			//for(Value value : out){
			//	outSet.add(value);
			//}
			outSet.addAll(out);
		}
		//tainted.put(methodname, out);
		
		if(isTaintedPublicSink(node, in)) {
		    if(!taintedSinks.containsKey(node))
		    	taintedSinks.put(node, new HashSet());
	
		    taintedSinks.get(node).add(in);
		}
    }

    protected Set<Value> stillTaintedValues(Set<Value> in, Unit node) {
    	return in;
    }

    // It would be sweet if java had a way to duck type, but it doesn't so we have to do this.
    protected boolean containsValues(Collection<Value> vs, Object s) {
	for(Value v : vs)
	    if(containsValue(v, s))
		return true;
	return false;
    }

    protected boolean containsValue(Value v, Object s) {
	try {
	    // I'm so sorry.
	    Method m = s.getClass().getMethod("getUseBoxes");
	    for(ValueBox b : (Collection<ValueBox>) m.invoke(s))
		if(b.getValue().equals(v))
		    return true;
	    return false;
	} catch(Exception e) {
	    return false;
	}
    }

    protected Set<Value> newTaintedValues(Set<Value> in, Unit node) {
	Set<Value> out = new HashSet();

	if(containsValues(in, node)) {
	    if(node instanceof AssignStmt) {
		out.add(((AssignStmt) node).getLeftOpBox().getValue());
	    } else if(node instanceof IfStmt) {
		IfStmt i = (IfStmt) node;
		if(i.getTarget() instanceof AssignStmt)
		    out.add(((AssignStmt) i.getTarget()).getLeftOpBox().getValue());
	    }
	} else if(node instanceof AssignStmt) {
	    AssignStmt assn = (AssignStmt) node;

	    if(isPrivateSource(assn.getRightOpBox().getValue()))
	    out.add(assn.getLeftOpBox().getValue());
	} else if(node instanceof IdentityStmt){   //for invoke source
		IdentityStmt idStmt = (IdentityStmt)node;
		if (tainttemp.containsKey(MethodName)) {
			for (int i = 0; i < 10; i++) {
				if (idStmt.getRightOp().toString().startsWith("@parameter")) {
					int index = Integer.parseInt(idStmt.getRightOp().toString().substring(10, 11));
					G.v().out.println("index"+index);
					if (tainttemp.get(MethodName)[i] == 1 && index == i) {
						 out.add(idStmt.getLeftOp());
					}
				}
				
			}
		}
	}

	return out;
    }

    protected boolean isPrivateSource(Value u) {
    //G.v().out.println("[taint]Value:"+u.toString());
	/*if(u instanceof VirtualInvokeExpr) {
	    VirtualInvokeExpr e = (VirtualInvokeExpr) u;
	    SootMethod m = e.getMethod();
	    G.v().out.println("[taint]sootmethod:"+m.getName());
	    if(m.getName().equals("readLine") &&
	       m.getDeclaringClass().getName().equals("(java.io.Console"))
		return true;
	}*/
	    G.v().out.println("[taint source]method name:"+MethodName);
	    G.v().out.println("[taint] Value:"+u.toString());
	    if (u.toString().equals("")) {//<test.Sort_Quick: int a><test.BinarySearch: int a>
	    	G.v().out.println("[taint]real Value:"+u.toString());
	    	return true;
		}
	   
		return false;
    }

    protected boolean isTaintedPublicSink(Unit u, Set<Value> in) {
		if(u instanceof InvokeStmt) {
		    InvokeExpr e = ((InvokeStmt) u).getInvokeExpr();
		    SootMethod m = e.getMethod();
		    G.v().out.println("invoke "+((InvokeStmt) u).getInvokeExpr().getArgCount());
		    for (int i = 0; i < ((InvokeStmt) u).getInvokeExpr().getArgCount(); i++) {
				Value value = ((InvokeStmt) u).getInvokeExpr().getArg(i);
				if (outSet.contains(value)) {
					G.v().out.println("i "+i+" value "+value);
					temp[i] = 1;
					flag = true;
				}else {
					temp[i] = 2;
				}
			}
		    G.v().out.println("flag="+flag+"  name="+m.getName()+" "+sMethodsList.contains(m.getName()));
		    if (flag && sMethodsList.contains(m.getName())) {
		    	hashtaint.put(m.getName(), temp);
				temp = new int[10];       //clean up
			}
		    flag = false;
		    if(m.getName().equals("println") &&
		       m.getDeclaringClass().getName().equals("java.io.PrintStream") &&
		       containsValues(in, e))

			    G.v().out.println("[isTaintedPublicSink]invoke m ="+m.toString());
			return true;
		}
		if (u instanceof AssignStmt) {
			if(((AssignStmt) u).containsInvokeExpr()){
				SootMethod m = ((AssignStmt) u).getInvokeExpr().getMethod();
				 G.v().out.println("assign "+((AssignStmt) u).getInvokeExpr().getArgCount());
				for (int i = 0; i < ((AssignStmt) u).getInvokeExpr().getArgCount(); i++) {
					Value value = ((AssignStmt) u).getInvokeExpr().getArg(i);
					if (outSet.contains(value)) {
						temp[i] = 1;
						flag = true;
					}else {
						temp[i] = 2;
					}
				}
				if (flag && sMethodsList.contains(m.getName())) {
				    hashtaint.put(m.getName(), temp);
					temp = new int[10];       //clean up
				}
				flag = false;
				
				 if(containsValues(in, ((AssignStmt) u).getInvokeExpr()))
					 G.v().out.println("[isTaintedPublicSink]assign:"+m.toString());
						return true;
			}
			
		}
		
		return false;
    }

}
