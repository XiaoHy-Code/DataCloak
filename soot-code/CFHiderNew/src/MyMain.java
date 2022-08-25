/* Soot - a J*va Optimization Framework
 * Copyright (C) 2008 Eric Bodden
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the
 * Free Software Foundation, Inc., 59 Temple Place - Suite 330,
 * Boston, MA 02111-1307, USA.
 */
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import polyglot.types.Flags;
import java_cup.internal_error;
import soot.Body;
import soot.BodyTransformer;
import soot.G;
import soot.Local;
import soot.PackManager;
import soot.PatchingChain;
import soot.RefLikeType;
import soot.RefType;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Transform;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.JastAddJ.Signatures.FieldSignature;
import soot.jimple.AssignStmt;
import soot.jimple.Constant;
import soot.jimple.DefinitionStmt;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.StaticInvokeExpr;
import soot.options.Options;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.util.Chain;

import java.util.*;
import java.lang.reflect.Method;

import soot.*;
import soot.options.*;
import soot.toolkits.graph.*;
import soot.toolkits.scalar.*;
import soot.baf.*;
import soot.jimple.*;

public class MyMain {	
   public static Map<String, int[]> hash = new HashMap<>();
   public static Map<String, int[]> hashfortaint = new HashMap<>();
   static boolean Flags = false;
   
   static Map<String, Set<Value>> taintMap = new HashMap<>();
   
   public static void main(String[] args) {
	   List<String> argList = new ArrayList<String>(Arrays.asList(args));
	   argList.addAll(Arrays.asList(new String[]{
			"-w",
	   }));
	   
	   PackManager.v().getPack("wjtp").add(new Transform("wjtp.T", new SceneTransformer() {
		   @Override
			protected void internalTransform(String arg0,Map arg1) {
				// TODO Auto-generated method stub
			   
			   for(SootClass cls:Scene.v().getApplicationClasses()){
				   G.v().out.println("[taint]SooClass:"+cls.toString());
					if (cls.toString().equals("invoker.sgx_invoker")) {
						continue;
					}
					G.v().out.println("[taint] class: "+cls.toString());
					List<SootMethod> sootMethods = cls.getMethods();
					List<String> sootMethodsNameList = new ArrayList<>();
					for (int i = 0; i <sootMethods.size(); i++) {
						sootMethodsNameList.add(sootMethods.get(i).getName());
					}
					
					for (int i = 0; i <sootMethods.size(); i++) {
						for (int x= 0; x<sootMethods.size();x++) {
							SootMethod sootMethod = sootMethods.get(x);
							if (!sootMethod.getName().equals("<clinit>") && !sootMethod.getName().equals("<init>")) {
								G.v().out.println("[taint] sootMethod: "+sootMethod.getName());
								if(!sootMethod.hasActiveBody()){
									//Body body = sootMethod.retrieveActiveBody();
									//UnitGraph g = new BriefUnitGraph(body);
									//new TaintAnalysisWrapper(new ExceptionalUnitGraph(body),taintMap,sootMethod.getName(),hashfortaint,sootMethodsNameList);
								}else {
									Body body = sootMethod.getActiveBody();
									UnitGraph g = new BriefUnitGraph(body);
									//new TaintAnalysisMain(g);
									G.v().out.println("[taint] hashfortaint: "+hashfortaint.size() +" sMethodsList");
	                                new TaintAnalysisWrapper(new ExceptionalUnitGraph(body),taintMap,sootMethod.getName(),hashfortaint,sootMethodsNameList);
								}
							}
						}
					}
			   }
			   
			   
			   for(SootClass cls:Scene.v().getApplicationClasses()){
					if (cls.toString().equals("invoker.sgx_invoker")) {
						continue;
					}
					G.v().out.println("[SCENE] class: "+cls.toString());
					List<SootMethod> sootMethods = cls.getMethods();
					
					for (int i = 0; i <sootMethods.size(); i++) {
						for (int x= 0; x<sootMethods.size();x++) {
							SootMethod sootMethod = sootMethods.get(x);
							
							if (!sootMethod.getName().equals("<clinit>") && !sootMethod.getName().equals("<init>")) {
								G.v().out.println("[SCENE] sootMethod: "+sootMethod.getName());
								if (hash.containsKey(sootMethod.getName())) {
									continue;
								}
								if(!sootMethod.hasActiveBody()){
									G.v().out.println("[SCENE] sootMethod have not activity body: "+sootMethod.getName());
									if (sootMethod.getName().equals("findPartition") || sootMethod.getName().equals("print")) {
										continue;
									}
									Body body = sootMethod.retrieveActiveBody();
									sceneTrans sceneTrans = new sceneTrans();
									hash.putAll(sceneTrans.sceneTran(arg0,body,sootMethod));
								}else {
									Body body = sootMethod.getActiveBody();
									sceneTrans sceneTrans = new sceneTrans();
									hash.putAll(sceneTrans.sceneTran(arg0,body,sootMethod));
								}
							}
						}
					}
			   }
			  
			   
			   G.v().out.println("[wjtp] hash.size():"+hash.size());
			   
			   Set<String> tkey = hashfortaint.keySet();
			   for(Object tkeys : tkey){
			    	if (hash.containsKey(tkeys)) {
			    		for (int i = 0; i < 10; i++) {
			    			if (hash.get(tkeys)[i] == 1 || hashfortaint.get(tkeys)[i] == 1) {
			    				hash.get(tkeys)[i] = 1;
							}
						}
			    	}else{
			    	 	hash.put(tkeys.toString(), hashfortaint.get(tkeys));
			    	}	 
			    }
			   G.v().out.println("[wjtp] hash.size()2:"+hash.size());
			   
			   /**
			     * print hashmap
			     */
//			    Set<String> keys = taintMap.keySet();
//			    for(Object key : keys){
//			    	 G.v().out.println("[ZYSTBLE1104]taintMap key:"+key+"  value:"+taintMap.get(key));
//		    	}
			    Set<String> key = hash.keySet();
			    //G.v().out.println("[ZYSTBLE1104] hash.size():"+hash.size());
			    for(Object keyss : key){
			    	 G.v().out.print("[ZYSTBLE1104] hash key:"+keyss);
			    	 G.v().out.print(" value:[");
			    	 for(int a:hash.get(keyss)){
			    		 G.v().out.print(" "+a);
			    	 }
			    	 G.v().out.print("]");
			    	 G.v().out.println();
		    	}
			    Set<String> ttkey = hashfortaint.keySet();
			    for(Object keyss : ttkey){
			    	 G.v().out.print("[ZYSTBLE1104]hashfortaint key:"+keyss);
			    	 G.v().out.print(" value:[");
			    	 for(int a:hashfortaint.get(keyss)){
			    		 G.v().out.print(" "+a);
			    	 }
			    	 G.v().out.print("]");
			    	 G.v().out.println();
		    	}
			}
	}));
	    
		PackManager.v().getPack( "jtp" ).add(
				new Transform("jtp.LogInserter", new BodyTransformer() {
				      protected void internalTransform(Body body, String phase, Map options) {
					    phase = "zystble";
					    
					    
					    new Transformer(body,phase,hash,taintMap,hashfortaint);
				      }
				    }) );
		args = argList.toArray(new String[0]);		
		soot.Main.main(args);
		//closeWriter();
	}
   
}  















   
