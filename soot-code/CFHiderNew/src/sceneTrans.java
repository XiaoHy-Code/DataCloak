import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import java_cup.internal_error;
import soot.Body;
import soot.G;
import soot.PatchingChain;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.Constant;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.StaticInvokeExpr;


public class sceneTrans {

	static Map<String, int[]> hash = new HashMap<>();
	
	public Map<String, int[]> sceneTran(String  arg0,Body body,SootMethod sootMethod){
		boolean Flags = false;
		G.v().out.println("[INFO] phase: "+arg0);
		/*for(SootClass cls:Scene.v().getApplicationClasses()){
			
			if (cls.toString().equals("invoker.sgx_invoker")) {
				continue;
			}
			G.v().out.println("[INFO] scanTrans class: "+cls);
			List<SootMethod> sootMethods = cls.getMethods();
			for (int i = 0; i <sootMethods.size(); i++) {
				G.v().out.println("[INFO] number===================:"+i);
				for (int x= 0; x<sootMethods.size();x++) {
					SootMethod sootMethod = sootMethods.get(x);
					if (!sootMethod.getName().equals("<init>") && !sootMethod.getName().equals("<clinit>")) {
						G.v().out.println("[INFO] sootMethod: "+sootMethod.getName()+" cls:"+cls);
						if((!sootMethod.hasActiveBody()) || hash.containsKey(sootMethod.getName())){
							G.v().out.println("[INFO] 1224"+hash.containsKey(sootMethod.getName())+" "+(!sootMethod.hasActiveBody()));
							continue;
						}
						Body body = sootMethod.getActiveBody();*/
						G.v().out.println("[INFO] scanTrans class: "+sootMethod.getDeclaringClass().toString());
						G.v().out.println("[INFO] scanTrans method: "+sootMethod.toString());
						PatchingChain<Unit> units = body.getUnits();
						Iterator<Unit> scanIt1 = units.snapshotIterator();
						Iterator<Unit> scanIt2 = units.snapshotIterator();
						Unit currStmt = null;
						 Unit currStmt1 = null;
						ArrayList<Value> list = new ArrayList<>();   //store temp control-flow variables
				    	  while (scanIt1.hasNext()) {//stmt 
				    		  currStmt = scanIt1.next();
				    		  if (currStmt instanceof IfStmt) {
								@SuppressWarnings("unchecked")
								Iterator<ValueBox> ubIt=((IfStmt) currStmt).getCondition().getUseBoxes().iterator();
								 while(ubIt.hasNext()){
					    				ValueBox vBox = (ValueBox) ubIt.next();
					    				Value tValue = vBox.getValue();
					    				if (!(tValue instanceof Constant)) {
					    					list.add(tValue);                      //collect
						    				G.v().out.println("[wjtp]tvalue:"+tValue);
										}
					    				
								 }
							  }
				    		  if (currStmt instanceof InvokeStmt) {
				    			    G.v().out.println("[wjtp]invoke:"+currStmt);
				    			    G.v().out.println("[wjtp]invoke of method:"+sootMethod.toString());
									InvokeExpr inExpr = ((InvokeStmt) currStmt).getInvokeExpr();
									if (hash.containsKey(inExpr.getMethod().getName())) {
										 G.v().out.println("[wjtp]invoke hash:"+currStmt);
										int tem[] = hash.get(inExpr.getMethod().getName());
										for (int j = 0; j < inExpr.getArgCount(); j++) {
											G.v().out.println("[wjtp]tem["+j+"]:"+tem[j]);
											if (tem[j] == 1) {
												list.add(inExpr.getArg(j));
											}
										}
									}
							  }
				    	  }
				    	  int variable [] = new int[10];
				    	  
				    	  while (scanIt2.hasNext()) {//stmt
				    		  currStmt1 = scanIt2.next();
				    		  if (currStmt1 instanceof IdentityStmt) {
								String s = ((IdentityStmt) currStmt1).getRightOp().toString();
								if (s.startsWith("@parameter")) {
									G.v().out.println("rigtht@parameter:"+s);
									if (list.contains(((IdentityStmt) currStmt1).getLeftOp())) {   //select
										G.v().out.println("sindex:"+Integer.parseInt(s.substring(10, 11)));
										variable[Integer.parseInt(s.substring(10, 11))] = 1;
										Flags = true;
									}
								}
							}
						}
				    	G.v().out.println("Flags="+Flags);
				    	if (Flags) {
				    		hash.put(body.getMethod().getName(), variable);  
				    		G.v().out.println("[wjtp]body.getMethod():"+body.getMethod().toString());
				    		//hashflagforRecursive.put(body.getMethod().toString(), false);
				    		G.v().out.println("[wjtp]hash.size():"+hash.size());
						}
				        Flags = false;
				        
				        if (hash.containsKey(body.getMethod().getName())) {
				    		  for (int k = 0; k < body.getMethod().getParameterCount(); k++) {
									if (hash.get(body.getMethod().getName())[k] != 1) {
										hash.get(body.getMethod().getName())[k] = 2;
									}
							  }
						}
				        //G.v().out.println("[INFO] scanTrans class: "+cls.toString()+" "+hash.size());
				        return hash;
					}
				//}	
			//}
			
		//}
		
//	}
	
}
