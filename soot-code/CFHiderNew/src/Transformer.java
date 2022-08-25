import java.io.*;
import java.util.*;
import java.util.concurrent.CopyOnWriteArrayList;

import java_cup.internal_error;

import org.omg.CORBA.PRIVATE_MEMBER;

import com.sun.java.swing.plaf.windows.WindowsTreeUI.ExpandedIcon;

import soot.*;
import soot.JastAddJ.ArrayAccess;
import soot.javaToJimple.LocalGenerator;
import soot.jimple.AddExpr;
import soot.jimple.AnyNewExpr;
import soot.jimple.ArrayRef;
import soot.jimple.AssignStmt;
import soot.jimple.BinopExpr;
import soot.jimple.CastExpr;
import soot.jimple.Constant;
import soot.jimple.DefinitionStmt;
import soot.jimple.DoubleConstant;
import soot.jimple.Expr;
import soot.jimple.FloatConstant;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InstanceOfExpr;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.LongConstant;
import soot.jimple.NewArrayExpr;
import soot.jimple.NewExpr;
import soot.jimple.NopStmt;
import soot.jimple.NullConstant;
import soot.jimple.ParameterRef;
import soot.jimple.Ref;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StaticFieldRef;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.internal.AbstractBinopExpr;
import soot.jimple.internal.JEqExpr;
import soot.jimple.internal.JInstanceFieldRef;
import soot.jimple.internal.JLengthExpr;
import soot.jimple.internal.JStaticInvokeExpr;
import soot.options.*;
import soot.toolkits.graph.*;
import soot.toolkits.scalar.FlowSet;
import soot.util.Numberable;
//import sun.security.action.GetLongAction;

/**
 * @author ZyStBle
 **/
public class Transformer
{

	static final int N=20;
	static long counter = 0;
	static Writer indexWriter=null;
    final static double ratio = 0.5;
    
	static Writer getWriter(){
		String filename = "/tmp/SGXindex";
	    if(indexWriter==null){
			try{
				indexWriter = new PrintWriter(filename, "UTF-8");

			} catch (IOException e) {
			   // do something
			}
	    }
		return indexWriter;
	}

	static void closeWriter(){
		if(indexWriter !=null){
			try {
				indexWriter.close();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			indexWriter = null;
		}
	}
	public static void indexwriter(String content) {
		String file="/tmp/SGXindex";
		BufferedWriter out = null;
		try {
			out = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(file, true)));
			out.write(content+"\n");
		} catch (Exception e) {
			e.printStackTrace();
		} finally {
			try {
				out.close();
				} catch (IOException e) {
					e.printStackTrace();
					}
			}
		}
	ArrayList<Value> InvokeVals = new ArrayList<Value>();
	
	ArrayList<Value> condVals = new ArrayList<Value>();
	ArrayList<Value> condValsInt = new ArrayList<Value>();
	ArrayList<Value> condValsDouble = new ArrayList<Value>();
	ArrayList<Value> condValsFloat = new ArrayList<Value>();
	ArrayList<Value> condValsChar = new ArrayList<Value>();
	ArrayList<Value> condValsLong = new ArrayList<Value>();
	ArrayList<Value> condValsByte = new ArrayList<Value>();
	ArrayList<Value> condValsOtherType = new ArrayList<Value>();		
//	ArrayList<Value> condValsType = new ArrayList<Value>();		
	ArrayList<Value> condValsTypeArray = new ArrayList<Value>();
    Unit lastIdentityStmt = null;
	
    @SuppressWarnings("unchecked")
	public Transformer(Body aBody,String phase,Map<String, int[]> hash,Map<String, Set<Value>> taintMap,Map<String, int[]> hashfortaint)
    {
    	Set keys = hash.keySet();
    	//G.v().out.println("---===-:"+hash.containsKey("es"));
    	 for(Object key : keys){
    		  G.v().out.println("Transfomer:"+key+"==="+hash.get(key)[0]+"-"+hash.get(key)[1]);
    	  }
		String declaredClassName = "";
		//G.v().out.println("<<!!!!!!START!!!!!!>>fields in class: "+	aBody.getMethod().getDeclaringClass().getFields().g+"; ");
	//	G.v().out.println("<<!!!!!!START!!!!!!>>fields in class: "+	aBody.getMethod().getDeclaringClass().getType().toString()+"; ");
	//	G.v().out.println("<<!!!!!!START!!!!!!>>fields in class: "+	aBody.getMethod().getDeclaringClass().getFieldCount()+"; ");
		
		//G.v().out.println("<<!!!!!!START!!!!!!>>fields in class: "+	aBody.get+"; ");
		declaredClassName = aBody.getMethod().getDeclaringClass().toString();
		String declaredFunction = aBody.getMethod().toString();
		String declaredName = aBody.getMethod().getName();
//		String argsInfoString = aBody.getMethod().get
		G.v().out.println("<<!!!!!!START!!!!!!>>start insertting at class: "+declaredClassName);
//		G.v().out.println("argsInfoString: "+argsInfoString+";");
		G.v().out.println("<<!!!!!!START!!!!!!>>start processing function: "+declaredFunction+";");
    	if(declaredClassName.contains("sgx_invoker")){
//			G.v().out.println("Encounters the sgxinvoker class ...skip...");
			return;
		}
    	PatchingChain<Unit> units = aBody.getUnits();//all statements
//    	G.v().out.println("units:"+units.toString());
    	Local invokeUUIDLocal = Jimple.v().newLocal("invokeUUID", RefType.v("java.lang.String"));
        Local getUUIDLocal = Jimple.v().newLocal("getUUID", RefType.v("java.lang.String"));
        Local branchResultLocal = Jimple.v().newLocal("branchInvokeResult", BooleanType.v());
        Local sgxObjLocal = Jimple.v().newLocal("sgxInvoker", RefType.v("invoker.sgx_invoker"));//sgx object
        aBody.getLocals().add(getUUIDLocal);
        aBody.getLocals().add(invokeUUIDLocal);
        aBody.getLocals().add(branchResultLocal);  //1.insert local boolean branchInvokeResultLocal
        aBody.getLocals().add(sgxObjLocal); //2.insert local reftype invokerLocal
       // LocalGenerator localGenerator = new LocalGenerator(aBody);
	   //    Local invokeUUIDLocal = localGenerator.generateLocal
	   // 			(RefType.v("java.lang.String")); 
	    //aBody.getLocals().add(invokeUUIDLocal);  
    	Unit currStmt = null;
    	Unit currProStmt = null;
    	Unit currScan3Stmt = null;
    	Unit currScan0Stmt = null;
    	
    	
    	boolean isInitValueInSgx = false;
    	
        HashSet<Value> identifiedLocal = new HashSet<Value>();

        List<Local> localArray = new CopyOnWriteArrayList<Local>();//declaration valuables
        List<Local> tmpLocalArray = new CopyOnWriteArrayList<Local>();//declaration valuables
        Iterator<Local> locali = aBody.getLocals().iterator();
        
        while(locali.hasNext()){
        	Local tLocal = locali.next();
        	G.v().out.println("tLocal="+tLocal.toString());
        	localArray.add(tLocal);
        	tmpLocalArray.add(tLocal);
        }
        
      
        
        ArrayList<AssignStmt> copySensInvokeList = new ArrayList<>();
        boolean isRecursiveFlag = true;
        ArrayList<Value> conValsIdentitySens = new ArrayList<>();
        ArrayList<Value> conValsIdentitySensforCopy = new ArrayList<>();
        Iterator<Unit> scanIt3 = units.snapshotIterator();
        //int Number = 99;
		while (scanIt3.hasNext()) {//for add invoke variables to control-flow list
			currScan3Stmt = scanIt3.next();
			G.v().out.println("====currScan3Stmt==1206====="+currScan3Stmt);
			if (currScan3Stmt instanceof IdentityStmt) {
				if (((IdentityStmt) currScan3Stmt).getRightOp().toString().startsWith("@parameter")) {
					int index = Integer.parseInt(((IdentityStmt) currScan3Stmt).getRightOp().toString().substring(10, 11));//parameter number
					if (hash.containsKey(aBody.getMethod().getName())) { //this body method is sensitive method
						if (hash.get(aBody.getMethod().getName())[index] == 1) { 
							G.v().out.println("zystble1203 currScan4Stmt:"+currScan3Stmt);
							condVals.add(((IdentityStmt) currScan3Stmt).getLeftOp());
							if (!condValsInt.contains(((IdentityStmt) currScan3Stmt).getLeftOp())) {
								condValsInt.add(((IdentityStmt) currScan3Stmt).getLeftOp());
							}
							if (!condValsDouble.contains(((IdentityStmt) currScan3Stmt).getLeftOp())) {
								condValsDouble.add(((IdentityStmt) currScan3Stmt).getLeftOp());
							}
//							conValsIdentitySens.add(((IdentityStmt) currScan3Stmt).getLeftOp());
						}
					}				
				}
			}
			if(currScan3Stmt instanceof InvokeStmt){
				G.v().out.println("zystble1128 currScan3Stmt:"+currScan3Stmt);
				int k = 0;
				int length = ((InvokeStmt) currScan3Stmt).getInvokeExpr().getArgCount(); //args length
				String name = ((InvokeStmt) currScan3Stmt).getInvokeExpr().getMethodRef().name();
				G.v().out.println("[invoke]zystble1205 name:"+name);
				//G.v().out.println("sMethodRef :"+((InvokeStmt) currScan3Stmt).getInvokeExpr().getMethodRef());
					if (hash.containsKey(name)) { // if it invokes a sens-method
						G.v().out.println("zystble1205 currScan3Stmt:"+currScan3Stmt);
						
//						if (name.equals(declaredName)) {   // //sovle the sensitive method and this method is recursive
							
//							G.v().out.println("[invoke]the sensitive method and this method is recursive :"+name);
//							if (isRecursiveFlag) {
//								for (int i = 0; i < conValsIdentitySens.size(); i++) {
//									LocalGenerator localGenerator = new LocalGenerator(aBody);
//									Local newLocal = localGenerator.generateLocal(conValsIdentitySens.get(i).getType()); //temp1
//									//aBody.getLocals().add(newLocal);  
//									conValsIdentitySensforCopy.add(newLocal);
//									//Local newLocal = Jimple.v().newLocal(name, InvokeVals.get(i).getType());
//									AssignStmt assignStmt = Jimple.v().newAssignStmt(newLocal,conValsIdentitySens.get(i)); //$i0 = i0
//									//units.insertBefore(assignStmt, currScan3Stmt);
//									G.v().out.println("[invoke] recursive :"+assignStmt);
//									condVals.add(newLocal);
//									if (!condValsInt.contains(newLocal)) {
//										condValsInt.add(newLocal);
//									}
//									copySensInvokeList.add(assignStmt);
//								}
//							}
//							isRecursiveFlag = false;
//							int count = 0;
//							for (int i = 0; i < length; i++) {
//								if (hash.get(name)[i] == 1) { //sensitive
//									Value qesValue = ((InvokeStmt) currScan3Stmt).getInvokeExpr().getArg(i);
//									G.v().out.println("[invoke] recursive qesValue1209:"+qesValue);
//									if (conValsIdentitySens.contains(qesValue)) {
//										int index = conValsIdentitySens.indexOf(qesValue);
//										G.v().out.println("[invoke] recursive index1209:"+index);
//										AssignStmt assignStmt = Jimple.v().newAssignStmt(conValsIdentitySens.get(index),
//												conValsIdentitySensforCopy.get(index)); //$i0 = i0
//										units.insertBefore(assignStmt, currScan3Stmt);
//										G.v().out.println("[invoke] recursive assignStmt1209:"+assignStmt);
//									}else {
//										AssignStmt assignStmt = Jimple.v().newAssignStmt(conValsIdentitySens.get(count),
//												qesValue); //i1 = i3
//										units.insertBefore(assignStmt, currScan3Stmt);
//										G.v().out.println("[invoke] recursive assignStmt1209:"+assignStmt);
//									}
//									count++;
//								}
//							}	
//						}
												
						List<Value> argList = new ArrayList<>();
						List<Type> argtypeList = new ArrayList<>();
						int Number = 99;
						for (int i = 0; i < length; i++) {
							if (hash.get(name)[i] == 1) {
								G.v().out.println("zystble1128 int["+i+"]:"+hash.get(name)[i]);
								Value qesValue = ((InvokeStmt) currScan3Stmt).getInvokeExpr().getArg(i);
								G.v().out.println("zystble1128 qesValue:"+qesValue.toString());
								condVals.add(qesValue);
								if (!condValsInt.contains(qesValue)) {
									condValsInt.add(qesValue);   //only test 'int'  12.2
								}
								insertCallerUpdateStmt(aBody, sgxObjLocal, units, tmpLocalArray, qesValue, currScan3Stmt, getUUIDLocal,Number--);
							}else {
								argList.add(((InvokeStmt) currScan3Stmt).getInvokeExpr().getArg(i));
								argtypeList.add(((InvokeStmt) currScan3Stmt).getInvokeExpr().getArg(i).getType());
							}
						}
						
						argtypeList.add(getUUIDLocal.getType()); // after edit arg list
						argList.add(getUUIDLocal);   //after edit arg list
						SootMethod sootMethod = ((InvokeStmt) currScan3Stmt).getInvokeExpr().getMethodRef().declaringClass().getMethodByName(name);
						G.v().out.println("zystble1206 sootMethod :"+sootMethod);
						//((InvokeStmt) currScan3Stmt).getInvokeExpr().setMethodRef();
						sootMethod.setParameterTypes(argtypeList);
						G.v().out.println("[insi] 1223  sootMethod:"+sootMethod.toString());
						if (sootMethod.isStatic()) {
							InvokeExpr inc = Jimple.v().newStaticInvokeExpr(sootMethod.makeRef(), argList);
							Stmt inStmt = Jimple.v().newInvokeStmt(inc);
							units.insertBefore(inStmt, currScan3Stmt);
							G.v().out.println("[insi]   inStmt:"+inStmt.toString());
							units.remove(currScan3Stmt);	
						}else {
							((InvokeStmt) currScan3Stmt).getInvokeExpr().setMethodRef(sootMethod.makeRef());
							int i = 0;
							for(Value argValue:argList){
								((InvokeStmt) currScan3Stmt).getInvokeExpr().setArg(i, argValue);
								i++;
							}
						}
					}
					
			}
			if(currScan3Stmt instanceof AssignStmt){
				G.v().out.println("[assi]zystble1206 currScan3Stmt is AssignStmt:"+currScan3Stmt);
				
				if(((AssignStmt)currScan3Stmt).containsInvokeExpr()){
					String name = ((AssignStmt) currScan3Stmt).getInvokeExpr().getMethodRef().name();
					G.v().out.println("[assi]zystble1204 currScan3Stmt:"+currScan3Stmt);
					//G.v().out.println("zystble1204 name:"+((AssignStmt) currScan3Stmt).getInvokeExpr().getMethod().getName());
					if (hash.containsKey(((AssignStmt) currScan3Stmt).getInvokeExpr().getMethodRef().name())) {
						G.v().out.println("[assi]zystble1205 currScan3Stmt:"+currScan3Stmt);
						
						/**
						 * add on 2020/11/4 by zystble
						 */
						Value qeValue = ((AssignStmt)currScan3Stmt).getLeftOp();
						if (TypeForSpecialCallerPost(qeValue)!= 10) {
							condVals.add(qeValue);
							if (!condValsInt.contains(qeValue)) {
								condValsInt.add(qeValue);   //only test 'int'  12.2
							}
							insertCallerPostUpdateStmt(aBody, sgxObjLocal, units, tmpLocalArray, qeValue, currScan3Stmt, getUUIDLocal);
						}
						//*****************************
						
						
						int k = 0;
						int length = ((AssignStmt) currScan3Stmt).getInvokeExpr().getArgCount();
						G.v().out.println("[assi]zystble1204 length:"+length);
						List<Value> argList = new ArrayList<>();
						List<Type> argtypeList = new ArrayList<>();
						int Number = 99;
						for (int i = 0; i < length; i++) {
							if (hash.get(((AssignStmt) currScan3Stmt).getInvokeExpr().getMethodRef().name())[i] == 1) {
								G.v().out.println("[assi]zystble1128 int["+i+"]:"+hash.get(((AssignStmt) currScan3Stmt).getInvokeExpr().getMethodRef().name())[i]);
								Value qesValue = ((AssignStmt) currScan3Stmt).getInvokeExpr().getArg(i);
								G.v().out.println("[assi]zystble1128 qesValue:"+qesValue.toString());
								condVals.add(qesValue);
								if (!condValsInt.contains(qesValue)) {
									condValsInt.add(qesValue);   //only test 'int'  12.2
								}
								//InvokeVals.add(qesValue); 
								insertCallerUpdateStmt(aBody, sgxObjLocal, units, tmpLocalArray, qesValue, currScan3Stmt, getUUIDLocal,Number--);
							}else {
								argList.add(((AssignStmt) currScan3Stmt).getInvokeExpr().getArg(i));
								argtypeList.add(((AssignStmt) currScan3Stmt).getInvokeExpr().getArg(i).getType());
							}
						}
						argtypeList.add(getUUIDLocal.getType());
						argList.add(getUUIDLocal);
						SootMethod sootMethod = ((AssignStmt) currScan3Stmt).getInvokeExpr().getMethodRef().declaringClass().getMethodByName(name);
						sootMethod.setParameterTypes(argtypeList);
						/**
						 * add on 2020/11/4 by zystble
						 */
						if (TypeForSpecialCallerPost(qeValue)!= 10) {
							sootMethod.setReturnType(VoidType.v()); 
							G.v().out.println("[zystble20201104 void]"+sootMethod.toString());
						}
						
						if (sootMethod.isStatic()) {
//							InvokeExpr inc = Jimple.v().newStaticInvokeExpr(sootMethod.makeRef(), argList);
//							//Stmt inStmt = Jimple.v().newInvokeStmt(inc);
//							Stmt asStmt = Jimple.v().newAssignStmt(((AssignStmt) currScan3Stmt).getLeftOp(), inc);
//							units.insertBefore(asStmt, currScan3Stmt);
//							G.v().out.println("[assi]   asStmt:"+asStmt.toString());
//							units.remove(currScan3Stmt);
							InvokeExpr inc = Jimple.v().newStaticInvokeExpr(sootMethod.makeRef(), argList);
							if (TypeForSpecialCallerPost(qeValue)!= 10) {
				    			Stmt inStmt = Jimple.v().newInvokeStmt(inc);
				    			units.insertBefore(inStmt, currScan3Stmt);
				    			units.remove(currScan3Stmt);	
							}else {
								Stmt asStmt = Jimple.v().newAssignStmt(((AssignStmt) currScan3Stmt).getLeftOp(), inc);
								units.insertBefore(asStmt, currScan3Stmt);
								units.remove(currScan3Stmt);
							}
							
						}else {
							((AssignStmt) currScan3Stmt).getInvokeExpr().setMethodRef(sootMethod.makeRef());
							int i = 0;
							for(Value argValue:argList){
								((AssignStmt) currScan3Stmt).getInvokeExpr().setArg(i, argValue);
								i++;
							}
						}
					}
				}
			}
		}
		
		Iterator<Unit> scanIt1 = units.snapshotIterator();
    	while (scanIt1.hasNext()) {//stmt
    		currStmt = scanIt1.next();
    		if(currStmt instanceof IfStmt){//IfStmt
    			Value orgIfCondition = ((IfStmt) currStmt).getCondition();
    			//orgIfCondition.getUseBoxes().
    			Iterator<ValueBox> ubIt=orgIfCondition.getUseBoxes().iterator();
    			    			
    			while(ubIt.hasNext()){
    				ValueBox vBox = (ValueBox) ubIt.next();
    				Value tValue = vBox.getValue();
    				String tValueTypeStr=tValue.getType().toString();
    				//G.v().out.println("<<<<<<ZYSTBLE>>>>>> ttValueTypeStr: ++++++++++++++++++++++++++ "+tValueTypeStr+"++++++++++++++++++++++");
    				if(!(tValue instanceof Constant)){
    					if(!condVals.contains(tValue)){
        					condVals.add(tValue);
        					//G.v().out.println("---==condVals:"+condVals.toString());
    					}
	//        			conditionValuesType.add(vBox.getValue().getType());
	            	    localArray.removeAll(condVals);
		    			if(tValueTypeStr.equals("int") || tValueTypeStr.equals("java.lang.Integer") || tValueTypeStr.equals("short")){
		    				if (!condValsInt.contains(tValue)) {
		    					condValsInt.add(tValue);
		    	            }
//		    				condValsInt.add(tValue);
		    			}else if(tValueTypeStr.equals("boolean")){
		    				if (!condValsInt.contains(tValue)) {
		    					
		    					condValsInt.add(tValue);
		    	            }
		    			}else if(tValueTypeStr.equals("double")){
		    				if (!condValsDouble.contains(tValue)) {
		    					condValsDouble.add(tValue);
		    	            }
//		    				condValsDouble.add(tValue);
		    			}
		    			else if(tValueTypeStr.equals("float")){
		    				if (!condValsFloat.contains(tValue)) {
		    					condValsFloat.add(tValue);
		    	            }
//		    				condValsFloat.add(tValue);
		    			}
		    			else if(tValueTypeStr.equals("char")){
		    				//G.v().out.println("sss");
		    				if (!condValsChar.contains(tValue)) {
		    					condValsChar.add(tValue);
		    	            }
//		    				condValsChar.add(tValue);
		    			}
		    			else if(tValueTypeStr.equals("long")){
		    				if (!condValsLong.contains(tValue)) {
		    					condValsLong.add(tValue);
		    	            }
//		    				condValsLong.add(tValue);
		    			}
		    			else if(tValueTypeStr.equals("byte")){
		    				if (!condValsByte.contains(tValue)) {
		    					condValsByte.add(tValue);
		    	            }
//		    				condValsByte.add(tValue);
		    			}
		    			else {
		    				G.v().out.println("Other condValsOtherType"+tValueTypeStr);
		    				//if (!condValsOtherType.contains(tValue)) {
		    				//		condValsOtherType.add(tValue);
		    	            //}
		    				if (!condValsInt.contains(tValue)) {
		    					G.v().out.println("8.1 tValue:"+tValue.toString());
		    					condValsInt.add(tValue);
		    	            }
//		    				condValsOtherType.add(tValue);
		//    				condValTypeNum.add(0);
		    			}
    				}
    			}
//    	    	G.v().out.println("ValuesType in condition: "+conditionValuesType.toString()+";");
    	    	//Readin stmt transformation
    	    	//IfStmt transformation
    	    }
    		if((currStmt instanceof IdentityStmt)){
        	    G.v().out.println("IdentityStmt:"+currStmt.toString());
        		identifiedLocal.add(((IdentityStmt)currStmt).getLeftOp());
        	    G.v().out.println("identifiedLocal:"+identifiedLocal.toString());
        	}
    	}    	
    	G.v().out.println("Values in condition: "+condVals.toString()+";");
    	
    	  /**
    	 * taint 1215
    	 */
    	G.v().out.println("1215 declaredFunction:"+declaredName);
    	if (taintMap.containsKey(declaredName)) {
    		G.v().out.println("1215 taint Value: 1111111");
			Set<Value> taintSet = taintMap.get(declaredName);
			for(Value taint:taintSet){
				if (!condValsInt.contains(taint) && taint.getType().toString().equals("int") && !(taint instanceof ArrayRef)) {
					G.v().out.println("1215 taint Value:"+taint);
					condValsInt.add(taint);
					condVals.add(taint);
	            }
			}
		}
    	Iterator<Unit> scanIt5 = units.snapshotIterator();
		Unit currScan5Stmt = null;
    	while(scanIt5.hasNext()){
			currScan5Stmt = scanIt5.next();
			if(currScan5Stmt instanceof InvokeStmt){
		    	//deal with invoke(secret)
				String name = ((InvokeStmt) currScan5Stmt).getInvokeExpr().getMethodRef().name();
				if (!hash.containsKey(name)) {
					G.v().out.println("1218 deal with invoke(secret):"+currScan5Stmt);
					List<Value> argList = ((InvokeStmt) currScan5Stmt).getInvokeExpr().getArgs();
					int index =0;
					for(Value arg:argList){
						if (condVals.contains(arg) && condValsInt.contains(arg)) {
							G.v().out.println("1218 deal with arg:"+arg);
							LocalGenerator localGenerator = new LocalGenerator(aBody);
							Local newLocal = localGenerator.generateLocal(arg.getType()); //temp1
							Stmt asStmt = Jimple.v().newAssignStmt(newLocal, arg);
							units.insertBefore(asStmt, currScan5Stmt);
							((InvokeStmt) currScan5Stmt).getInvokeExpr().setArg(index, newLocal);
						}
						index++;
					}
				}
			}
    	}

    	
    	condValsTypeArray.add(IntConstant.v(condValsInt.size()));
    	condValsTypeArray.add(IntConstant.v(condValsDouble.size()));
    	condValsTypeArray.add(IntConstant.v(condValsFloat.size()));
    	condValsTypeArray.add(IntConstant.v(condValsChar.size()));
    	condValsTypeArray.add(IntConstant.v(condValsLong.size()));
    	condValsTypeArray.add(IntConstant.v(condValsByte.size()));
    	condValsTypeArray.add(IntConstant.v(condValsOtherType.size()));
    	
//    	G.v().out.println("typeNumber of type: "+tArrayList+";");
//		G.v().out.println("current stmt is: ----------#"+currStmt+"#----------------");
    	//insertInitValueStmt(condValTypeNum);

        boolean isInitSgxInvoker = false;
     //   boolean isInitValueInSgx = false;
        boolean isInitidentyLocal = false;
        boolean isInitInvoker = false;
        lastIdentityStmt = units.getFirst();
        G.v().out.println("***zy+++lastIdentityStmt is： "+lastIdentityStmt.toString()+";");

	    G.v().out.println("localArray:"+localArray.toString());
	    
	    
		G.v().out.println("ok condVals"+condVals.size());
		//G.v().out.println("aBody.getMethod().getName() :"+aBody.getMethod().getName()+"  "+hash.get("es")[0]);
	    /***
		 * this method is a sensitive method
		  */
		 boolean addinvokeuuidflag = false; //only add once
		 if (hash.containsKey(aBody.getMethod().getName())) {   //
	        	G.v().out.println("aBody.getMethod():"+aBody.getMethod());
	        	Iterator<Unit> scanIt4 = units.snapshotIterator();   //solve the IdentityStmt problem
				Unit currScan4Stmt = null;
	        	while(scanIt4.hasNext()){
					currScan4Stmt = scanIt4.next();
					if(currScan4Stmt instanceof IdentityStmt){
						G.v().out.println("zystble1207 currScan4Stmt:"+((IdentityStmt) currScan4Stmt).getRightOp().toString());
						if (((IdentityStmt) currScan4Stmt).getRightOp().toString().startsWith("@parameter")) {
							int index = Integer.parseInt(((IdentityStmt) currScan4Stmt).getRightOp().toString().substring(10, 11));
							if (hash.containsKey(aBody.getMethod().getName()) && (hash.get(aBody.getMethod().getName())[index] == 1)) { 
								G.v().out.println("zystble1203 currScan4Stmt:"+currScan4Stmt);
								InvokeVals.add(((IdentityStmt) currScan4Stmt).getLeftOp());   
								addinvokeuuidflag = true;
							}
						}
						continue;
					}
					if (addinvokeuuidflag) {
						G.v().out.println("ielse Vals 1207"+addinvokeuuidflag+" count "+aBody.getMethod().getParameterCount());
						int k = 0;
			        	for (int i = 0; i < 10; i++) {
			        		if (hash.get(aBody.getMethod().getName())[i] == 0) {
			        			k = i;
							    break;
						    }
			        	}	   
			        	ParameterRef ref = Jimple.v().newParameterRef(invokeUUIDLocal.getType(), k);
			        	IdentityStmt identity = Jimple.v().newIdentityStmt(invokeUUIDLocal, ref);
			            G.v().out.println("units.insertBefore identity"+currScan4Stmt.toString());
			            units.insertBefore(identity, currScan4Stmt);
			            
			            identifiedLocal.add(invokeUUIDLocal);
			            localArray.add(invokeUUIDLocal);
			            
			            //units.add(identity);
			            G.v().out.println("invokeuuid identity Vals "+identity.toString());
			            addinvokeuuidflag = false;
			            //lastIdentityStmt = identity;
			        }
				}
				
			}

	    Iterator<Unit> scanIt2 = units.snapshotIterator();
	    ArrayList<AssignStmt> stmtArrayList = new ArrayList<>();
	    ArrayList<AssignStmt> invokeArraylist = new ArrayList<>();
	    ArrayList<Value> invokerealvaluelist = new ArrayList<>();
	    int index = 0;
	    int IdNumber = 99;
	    ArrayList<Value> preCallee = new ArrayList<>();
    	while(scanIt2.hasNext()){	
    		currProStmt=scanIt2.next();
    		ArrayList<Value> currDefVals = new ArrayList<Value>();
    		ArrayList<Value> currUseVals = new ArrayList<Value>();
    		G.v().out.println(" line258 current stmt is: ----------#"+currProStmt+"#----------------");
    		//G.v().out.println("currProStmt.getUseAndDefBoxes().toString():#"+currProStmt.getUseAndDefBoxes()+"#");
    		
			Iterator<ValueBox> ubIt=currProStmt.getDefBoxes().iterator();
			while(ubIt.hasNext()){
				ValueBox vBox = ubIt.next();
				Value tmpValue = vBox.getValue();
				if(!currDefVals.contains(tmpValue))
					currDefVals.add(tmpValue);
			}
    	    G.v().out.println("currDefVals:"+currDefVals.toString());//def number === 1???
    	    currDefVals.retainAll(condVals);
    	    
    	    G.v().out.println("currDefVals after retainAll:"+currDefVals.toString());//def number === 1???
    	    
    	    ubIt=currProStmt.getUseBoxes().iterator();
			while(ubIt.hasNext()){
				ValueBox vBox = ubIt.next();
				Value tmpValue = vBox.getValue();
				if(!currUseVals.contains(tmpValue))
					currUseVals.add(tmpValue);
			}    	    	   	
    	    G.v().out.println("currUseVals:"+currUseVals.toString()); 
    	    currUseVals.retainAll(condVals);
    	    G.v().out.println("currUseVals after retainAll:"+currUseVals.toString()); 
    	    
    		
//    		if(!currUseVals.isEmpty()){
//    			G.v().out.println("use: "+currProStmt.getUseBoxes()+";");
//        		G.v().out.println("current stmt type is: ----------#"+currProStmt.getClass()+"#----------------");
//    		}
    		
			if((currProStmt instanceof IdentityStmt)){
        	    G.v().out.println("currProStmt is IdentityStmt:"+currProStmt.toString());
        	   // G.v().out.println("currProStmt is IdentityStmt aBody.getMethod().toString():"+aBody.getMethod().toString());
        	   if (((IdentityStmt) currProStmt).getRightOp().toString().startsWith("@parameter")) {
        		   G.v().out.println("assi zyInvokeVals "+InvokeVals.size());
        		   G.v().out.println("currProStmt "+currProStmt.toString());
        		   if (InvokeVals.contains(((IdentityStmt) currProStmt).getLeftOp())) {
        			   G.v().out.println("in the InvokeVals");
//        			   LocalGenerator localGenerat = new LocalGenerator(aBody);
//	        	       Local locali1 = localGenerat.generateLocal
//	        	    			(((IdentityStmt) currProStmt).getLeftOp().getType()); 
//	        	       G.v().out.println("[invoke]locali1:"+locali1.toString());    
//	        	       localArray.add(locali1);
//	            	   identifiedLocal.add(locali1);
//	            	   AssignStmt invokegetStmt = Jimple.v().newAssignStmt(locali1, IntConstant.v(9));  //i0 = 9 -->  tem = 9 (get)
//        			   AssignStmt assignStmt = Jimple.v().newAssignStmt(((IdentityStmt) currProStmt)     // i0 = temp
//        						.getLeftOp(), locali1);  //9 is for test
//        			   G.v().out.println("[invoke]assignStmt is IdentityStmt:"+assignStmt.toString());
//        			   invokerealvaluelist.add(((IdentityStmt) currProStmt).getLeftOp());
//        			   invokeArraylist.add(invokegetStmt);
//        			   stmtArrayList.add(assignStmt);
        			   /**
        			    * add on 20201104 by zystble
        			    */
        			   //insertCalleeUpdateStmt(aBody, sgxObjLocal, units, tmpLocalArray, ((IdentityStmt)currProStmt).getLeftOp(), IdNumber--, currProStmt, getUUIDLocal);
        			   preCallee.add(((IdentityStmt)currProStmt).getLeftOp());
        			   lastIdentityStmt = currProStmt;
        			   units.remove(currProStmt);
				   }else if(currDefVals.isEmpty()){
					   G.v().out.println("not in the InvokeVals");
					   ParameterRef ref = Jimple.v().newParameterRef(((IdentityStmt) currProStmt).getLeftOp().getType(), index);
					   index++;
					   IdentityStmt identity = Jimple.v().newIdentityStmt(((IdentityStmt) currProStmt).getLeftOp(), ref);
					   units.insertBefore(identity, currProStmt);
					   units.remove(currProStmt);
					   G.v().out.println("1207 identity Vals "+identity.toString());
					   lastIdentityStmt = identity;
				   }
        	   }
        	    continue;
        	    
        	}
			G.v().out.println("line 284 current stmt is: ----------#"+currProStmt+"#----------------");
      	   
      	   
        	//init sgx enclave
			if(!isInitSgxInvoker){// && (!condVals.isEmpty())
        	    initidentyLocal(localArray, units, currProStmt,identifiedLocal);
        	    insertSgxInitStmt(aBody, sgxObjLocal, units, currProStmt, "invoker.sgx_invoker");
        		isInitSgxInvoker = true;
        		if(!isInitValueInSgx && (!condVals.isEmpty())){
        			insertValueInitStmt(aBody, sgxObjLocal, units, currProStmt,invokeUUIDLocal,getUUIDLocal,preCallee);
        			isInitValueInSgx = true;
        		}
        	    //lastIdentityStmt = currProStmt;//
//        	    G.v().out.println("***++++++lastIdentityStmt is:++++++++++"+lastIdentityStmt.toString());

//        		if(declaredFunction.contains("void main(java.lang.String[])")){
//	    			if(!isInitSgxInvoker){
//	            		insertSgxInitStmt(aBody, sgxObjLocal, units, currProStmt, "invoker.sgx_invoker");
//	            		isInitSgxInvoker = true;
//	    			}
//        		}
        		
        		
//        		for (int i = 0; i < invokeArraylist.size(); i++) {
//        			//G.v().out.println("the new sgx assignment is:"+stmt.toString());
//        	    	units.insertBefore(invokeArraylist.get(i), currProStmt);
//        	    	InvokeGetStmt(sgxObjLocal,units,invokeArraylist.get(i),invokeUUIDLocal,invokerealvaluelist.get(i));
//				}
    			
//    			for(AssignStmt stmt:stmtArrayList){
//        	    	G.v().out.println("the new sgx assignment is:"+stmt.toString());
//        	    	units.insertBefore(stmt, currProStmt);
//        	    	replaceValueUpdateStmt(aBody, sgxObjLocal, units, localArray, stmt,getUUIDLocal);
//    			}
//    			for(AssignStmt stmt:copySensInvokeList){
//        	    	G.v().out.println("the new sgx assignment is:"+stmt.toString());
//        	    	units.insertBefore(stmt, currProStmt);
//        	    	replaceValueUpdateStmt(aBody, sgxObjLocal, units, localArray, stmt,getUUIDLocal);
//    			}
			}
			
//    		if(declaredFunction.contains("void main(java.lang.String[])")){
//	            if(currProStmt.toString().contains("return"))
//	            {
//	            	//G.v().out.print("asjfdbashklfbhsak"+currStmt.toString());
//	            	insertCloseEnclaveStmt(sgxObjLocal, units, currProStmt, "invoker.sgx_invoker");
//	            }
//	        }
			
//			G.v().out.println("***++++++lastIdentityStmt is:++++++++++"+lastIdentityStmt.toString());
    		if((currProStmt instanceof AssignStmt)){
    	    	G.v().out.println("currProStmt is AssignStmt: "+currProStmt.toString()+";");
//        	    G.v().out.println("conditionValues:"+condVals.toString());
    	    	//G.v().out.println("DefValues:"+currDefVals.toString());
    	    	if(!currDefVals.isEmpty()){//update
            	    G.v().out.println("toBeHiddenDefValues:"+currDefVals.toString());
            	    //DefValue transformation
            	    replaceValueUpdateStmt(aBody, sgxObjLocal, units, localArray, currProStmt,getUUIDLocal);
    	    	}
    	    	else if(!currUseVals.isEmpty()){//getLocal 
            	    G.v().out.println("toBeHiddenUseValues:"+currUseVals.toString());
            	    replaceValueGetStmt(aBody, sgxObjLocal, units, localArray, currProStmt, currUseVals,getUUIDLocal);
    	    	}
    		}

    		if(currProStmt instanceof IfStmt){
    	    	G.v().out.println("currProStmt is IfStmt: "+currProStmt.toString()+";");
//        	    G.v().out.println("conditionValues:"+condVals.toString());
        	    replaceBranchStmt(aBody, sgxObjLocal, branchResultLocal, units, localArray, currProStmt,getUUIDLocal);
    		}
    		
    		if(currProStmt instanceof ReturnStmt){
    	    	G.v().out.println("currProStmt is ReturnStmt: "+currProStmt.toString()+";");
    	    	
    	    	Value reValue = ((ReturnStmt)currProStmt).getOp();
    	    	G.v().out.println("reValue is : "+reValue+";");
    	    	if(hash.containsKey(aBody.getMethod().getName())){
    	    		/**
    	    		 * add on 20201104 by zystble
    	    		 */
    	    		if (TypeForSpecialCallerPost(((ReturnStmt)currProStmt).getOp())!= 10) {
    	    			G.v().out.println("[zystble1104] A");
    	    			insertCalleePostUpdateStmt(aBody, sgxObjLocal, units, tmpLocalArray, reValue, currProStmt, getUUIDLocal);
    	    		}
    	    		
    	    		//	    	    	G.v().out.println("use: "+currUseVals+";");
//	    	    	
//	    	    	Local tmpReturnValue = Jimple.v().newLocal("tmpReturnValue"+Long.toString(counter), currUseVals.get(0).getType());
//	    			aBody.getLocals().add(tmpReturnValue);
//	    			localArray.add(tmpReturnValue);
//	    			G.v().out.println("tmpValue: "+tmpReturnValue.toString());    	        	
//	    			DefinitionStmt newAssignStmt = initAssignStmt(tmpReturnValue);
//	    			G.v().out.println("newAssignStmt is: "+newAssignStmt.toString());    	        	
//	    			G.v().out.println("lastIdentityStmt is: "+lastIdentityStmt.toString());
//	//    	        units.addFirst(newAssignStmt);
//	    			units.insertAfter(newAssignStmt, lastIdentityStmt);
//	    			
//	    			G.v().out.println("add newAssignStmt is: ++++++++++++++++++++++++++ "+newAssignStmt+"++++++++++++++++++++++");
//	    			
//	    			newAssignStmt = Jimple.v().newAssignStmt(tmpReturnValue,currUseVals.get(0));
//	    			G.v().out.println("newAssignStmt is: ++++++++++++++++++++++++++ "+newAssignStmt+"++++++++++++++++++++++");
//	    			units.insertBefore(newAssignStmt, currProStmt);
//	//    	        units.addFirst(newAssignStmt);
//	    			//
//	//    	    	rightOp = newAssignStmt.getRightOp();
//	//    	    	leftOpValue = newAssignStmt.getLeftOp();
//	    			replaceValueGetStmt(aBody, sgxObjLocal, units, localArray, newAssignStmt, currUseVals,getUUIDLocal);
//	    			G.v().out.println("ReturnStmt to be replaced is: ++++++++++++++++++++++++++ "+currProStmt+"++++++++++++++++++++++");
//	    			((ReturnStmt)currProStmt).setOp(tmpReturnValue);
//	    			G.v().out.println("new ReturnStmt is: ++++++++++++++++++++++++++ "+currProStmt+"++++++++++++++++++++++");
    	    	}
    	    	if(condVals.contains(reValue)){
    	    		G.v().out.println("[zystble1108 returnstatement]A : "+currProStmt.toString());
    	    		Local tmpReturnValue = Jimple.v().newLocal("tmpReturnValue"+Long.toString(counter), reValue.getType());
	    			aBody.getLocals().add(tmpReturnValue);
	    			localArray.add(tmpReturnValue);
	    			G.v().out.println("[zystble1108 returnstatement]B : "+currProStmt.toString());
	    			DefinitionStmt newAssignStmt = initAssignStmt(tmpReturnValue);
	    			units.insertAfter(newAssignStmt, lastIdentityStmt);
	    			G.v().out.println("[zystble1108 newAssignStmt]C : "+newAssignStmt.toString());
	    			newAssignStmt = Jimple.v().newAssignStmt(tmpReturnValue,reValue);
	    			units.insertBefore(newAssignStmt, currProStmt);
	    			G.v().out.println("[zystble1108 returnstatement]D : "+newAssignStmt.toString());
	    			replaceValueGetStmt(aBody, sgxObjLocal, units, localArray, newAssignStmt, currUseVals,getUUIDLocal);
	    			((ReturnStmt)currProStmt).setOp(tmpReturnValue);
    	    	}
    	    }
    		
    		//insert deleteValue stmt after process returnstmt
//			if(currProStmt.toString().contains("return")){
    		if((currProStmt instanceof ReturnStmt) || (currProStmt instanceof ReturnVoidStmt)){
	            	G.v().out.println("currProStmt return stmt before deleteValuestmt: "+currProStmt.toString());
	            	G.v().out.println("<<!!!!!!ZYreturn!!!!!!>>this processing function: "+declaredFunction+";");
	            	//!declaredFunction.contains("void <init>") && !declaredFunction.contains("void <clinit>") && 
        			//!declaredFunction.contains("<cfhider.WordCount$TokenizerMapper: void map(java.lang.Object,java.lang.Object,org.apache.hadoop.mapreduce.Mapper$Context)>")
        			//&& !declaredFunction.contains("void reduce(java.lang.Object,java.lang.Iterable,org.apache.hadoop.mapreduce.Reducer$Context)")
	            	if(isInitValueInSgx){
	            		insertDeletValueStmt(aBody, sgxObjLocal, units, currProStmt,getUUIDLocal);
	            		//G.v().out.println(".............zy............."+isInitSgxInvoker);
	            	}
	            	G.v().out.println("A");
	        		if(declaredFunction.contains("void main(java.lang.String[])")){
	    	            //G.v().out.print("asjfdbashklfbhsak"+currStmt.toString());
	    	            insertCloseEnclaveStmt(sgxObjLocal, units, currProStmt, "invoker.sgx_invoker");
	    	        }
	        		G.v().out.println("B");
	        		if((currProStmt instanceof ReturnStmt) && hash.containsKey(aBody.getMethod().getName()) && TypeForSpecialCallerPost(((ReturnStmt)currProStmt).getOp())!= 10){
	        			G.v().out.println("[zystble20201104] before");
	        			ReturnVoidStmt returnVoidStmt = Jimple.v().newReturnVoidStmt();
	        			units.insertBefore(returnVoidStmt, currProStmt);
	        			units.remove(currProStmt);
	        			G.v().out.println("[zystble20201104] after");
	        		}
	        		G.v().out.println("C");
			}
    	}
    	G.v().out.println("***++++++lastIdentityStmt is:++++++++++"+lastIdentityStmt.toString());
    	G.v().out.println("***++++++declaredName is:++++++++++"+declaredName);
    }
   
    
    
    @SuppressWarnings("unused")
	private void replaceValueGetStmt(
			Body aBody,
			Local sgxObjLocal,
			PatchingChain<Unit> units,
			List<Local> localArray,
			Unit currProStmt,
			ArrayList<Value> currUseVals,
			Local getUUIDLocal) {
		// TODO Auto-generated method stub
    	Value rightOp = null;
    	Value leftOpValue = null;
    	if(currProStmt instanceof AssignStmt){
    		rightOp = ((AssignStmt)currProStmt).getRightOp();
    		leftOpValue = ((AssignStmt)currProStmt).getLeftOp();
    		G.v().out.println("<<<<<<ZYSTBLE>>>>>>replaceValueGetStmt AssignStmt leftOpValue is: ++++++++++++++++++++++++++"+leftOpValue.toString()+"++++++++++++++++++++++");
    	}else if(currProStmt instanceof IdentityStmt){
   		 	rightOp = ((IdentityStmt)currProStmt).getRightOp();
   		 	leftOpValue = ((IdentityStmt)currProStmt).getLeftOp();
   		 	G.v().out.println("<<<<<<ZYSTBLE>>>>>> replaceValueGetStmt IdentityStmt leftOpValue is: ++++++++++++++++++++++++++"+leftOpValue.toString()+"++++++++++++++++++++++");
    	}else if(currProStmt instanceof InvokeStmt){
    		G.v().out.println(" currProStmt InvokeStmt IN GET: "+currProStmt.toString()+";");
    		//rightOp = (Value) ((InvokeStmt)currProStmt);
    	}
		ArrayList<Value> variable = new ArrayList<Value>();//
		ArrayList<Value> cons = new ArrayList<Value>();//
		ArrayList<Value> values = new ArrayList<Value>();
		ArrayList<String> operator = new ArrayList<String>();
		
		/* deal with there is conval in leftop(ArrayRef) */
		if(leftOpValue instanceof ArrayRef){
			Value indexValue = ((ArrayRef) leftOpValue).getIndex();
        	G.v().out.println("ArrayRef indexValue: "+indexValue+";");
        	
        	/* just deal with baseValue, beacause baseValue maybe in condvalue*/
			if(currUseVals.contains(indexValue)){
				ArrayList<Value> oneValueList = new ArrayList<>();
	    		oneValueList.add(indexValue);
	    		
				Local tmpArrRefBase = Jimple.v().newLocal("tmpArrRefBase"+Long.toString(counter), indexValue.getType());//leftOpValue
				aBody.getLocals().add(tmpArrRefBase);
				localArray.add(tmpArrRefBase);
    			G.v().out.println("tmpArrRefBase: "+tmpArrRefBase.toString());    	        	

    			/* insert tmpArrRefBase init stmt after all identitystmt*/
				DefinitionStmt assignStmt = initAssignStmt(tmpArrRefBase);
    			G.v().out.println("newAssignStmt is: "+assignStmt.toString());
   	            G.v().out.println("lastIdentityStmt is: "+lastIdentityStmt.toString());
    			units.insertAfter(assignStmt, lastIdentityStmt);
    			/* insert new assignstmt*/
				assignStmt = Jimple.v().newAssignStmt(tmpArrRefBase, indexValue);
    			G.v().out.println("newAssignStmt is: "+assignStmt.toString());
				units.insertBefore(assignStmt, currProStmt);
				
				/* replace new assignstmt*/
    			replaceValueGetStmt(aBody, sgxObjLocal, units, localArray, assignStmt, oneValueList,getUUIDLocal);
    			
    			/* replace leftOpValue*/
    			((ArrayRef)leftOpValue).setIndex(tmpArrRefBase);
    			//G.v().out.println("<<<<<<ZYSTBLE>>>>>> new leftOpValue is: ++++++++++++++++++++++++++ "+leftOpValue+"++++++++++++++++++++++");
    			
    			/* replace currProstmt*/
    			((AssignStmt)currProStmt).setLeftOp(leftOpValue);
    			//G.v().out.println("<<<<<<ZYSTBLE>>>>>> currProStmt is: ++++++++++++++++++++++++++ "+currProStmt+"++++++++++++++++++++++");

			}
		}
		
    	analyzeExp(rightOp, values, operator, cons, variable);//

		G.v().out.println("values length:"+values.size());
		boolean rightOpIsInvoke = false;
		boolean rightOpHasArrRef = false;
		boolean leftOpHasArrRef = false;
		boolean rightCast = false;
    	for(Value val:values){
    		G.v().out.println("<<<<<<ZYSTBLE>>>>>>the val is: "+val+";");
    		if(val instanceof InvokeExpr){//||(val instanceof ArrayRef)
    			rightOpIsInvoke = true;
    		    G.v().out.println("InvokeExpr");
    		}
    		else if(val instanceof ArrayRef){
    			G.v().out.println("ArrayRef");
    			rightOpHasArrRef = true;
    		}   
    		
    		if (val instanceof CastExpr){
    			G.v().out.println("CastExpr");
    			rightCast = true;
    		}
    	}
    	if(rightOpIsInvoke){
      	G.v().out.println("the invokestmt rightop is: "+rightOp+";");
			for(Value invokeParaValue:currUseVals){
	    		ArrayList<Value> oneValueList = new ArrayList<>();
	    		oneValueList.add(invokeParaValue);
//				Local tmpGetInvoke = Jimple.v().newLocal("tmpGetInvoke"+Long.toString(counter), leftOpValue.getType());
				Local tmpGetInvoke = Jimple.v().newLocal("tmpGetInvoke"+Long.toString(counter), invokeParaValue.getType());

				aBody.getLocals().add(tmpGetInvoke);
				localArray.add(tmpGetInvoke);
    			G.v().out.println("tmpValue: "+tmpGetInvoke.toString());    	        	

				DefinitionStmt assignStmt = initAssignStmt(tmpGetInvoke);
    			G.v().out.println("newAssignStmt is: "+assignStmt.toString());
    	        G.v().out.println("lastIdentityStmt is: "+lastIdentityStmt.toString());
    			units.insertAfter(assignStmt, lastIdentityStmt);
				
				assignStmt = Jimple.v().newAssignStmt(tmpGetInvoke, invokeParaValue);
				units.insertBefore(assignStmt, currProStmt);

    			replaceValueGetStmt(aBody, sgxObjLocal, units, localArray, assignStmt, oneValueList,getUUIDLocal);
    			G.v().out.println("after get stmt is: ++++++++++++++++++++++++++ "+currProStmt+"++++++++++++++++++++++");
    			G.v().out.println("InvokeExpr to be replaced is: ++++++++++++++++++++++++++ "+rightOp+"++++++++++++++++++++++");        			
    			int argIndex = ((InvokeExpr)rightOp).getArgs().indexOf(invokeParaValue);
    			((InvokeExpr)rightOp).setArg(argIndex, tmpGetInvoke);     			
    			G.v().out.println("new invokeExpr is: ++++++++++++++++++++++++++ "+rightOp+"++++++++++++++++++++++");
    			((AssignStmt)currProStmt).setRightOp(rightOp);
    		}
			G.v().out.println("new rightOpIsInvoke stmt is: ++++++++++++++++++++++++++ "+currProStmt+"++++++++++++++++++++++");
			return;
		}
    	else if(rightOpHasArrRef){
        	G.v().out.println("[<rightOpHasArrRef>]the arrayRef rightop is: "+rightOp+";");
			for(Value arrRefParaValue:currUseVals){
				//the new currUseValue for the new assignstmt
	    		ArrayList<Value> oneValueList = new ArrayList<>();
	    		oneValueList.add(arrRefParaValue);
	    		
	    		//contruct tmpGetInvoke to store currUseValue
				Local tmpGetArrRef = Jimple.v().newLocal("tmpGetArrRef"+Long.toString(counter), arrRefParaValue.getType());
				aBody.getLocals().add(tmpGetArrRef);
				localArray.add(tmpGetArrRef);
    			G.v().out.println("tmpValue: "+tmpGetArrRef.toString());    	        	

    			/*init tmpGetInvoke after all IdentityStmts*/
				DefinitionStmt assignStmt = initAssignStmt(tmpGetArrRef);
//    			G.v().out.println("newAssignStmt is: "+assignStmt.toString());
//    	        G.v().out.println("lastIdentityStmt is: "+lastIdentityStmt.toString());
    			units.insertAfter(assignStmt, lastIdentityStmt);
				
    			/*contruct assignstmt "tmpGetInvoke = arrRefParaValue"*/
				assignStmt = Jimple.v().newAssignStmt(tmpGetArrRef, arrRefParaValue);
    			G.v().out.println("newAssignStmt is: "+assignStmt.toString());
				units.insertBefore(assignStmt, currProStmt);

    			G.v().out.println("currUseValu is: "+oneValueList.toString());
    			replaceValueGetStmt(aBody, sgxObjLocal, units, localArray, assignStmt, oneValueList,getUUIDLocal);
    			
    			G.v().out.println("arrRefExpr to be replaced is: ++++++++++++++++++++++++++ "+rightOp+"++++++++++++++++++++++");        			
    			    			
    			if(arrRefParaValue.toString().equals(((ArrayRef)rightOp).getBase().toString())){
    				((ArrayRef)rightOp).setBase(tmpGetArrRef);
    			}
    			else if(arrRefParaValue.toString().equals(((ArrayRef)rightOp).getIndex().toString())){
    				((ArrayRef)rightOp).setIndex(tmpGetArrRef);
    			}
    			
    			G.v().out.println("new arrRefExpr is: ++++++++++++++++++++++++++ "+rightOp+"++++++++++++++++++++++");
    			((AssignStmt)currProStmt).setRightOp(rightOp);
    		}
			G.v().out.println("new arrRefExprStmt is: ++++++++++++++++++++++++++ "+currProStmt+"++++++++++++++++++++++");
			return;
    	}else if (rightCast) {
			//CastExpr castExpr = (CastExpr) exp;
			//exp = castExpr.getOp();
			for(Value castValue:currUseVals){
				//the new currUseValue for the new assignstmt
	    		ArrayList<Value> oneValueList = new ArrayList<>();
	    		oneValueList.add(castValue);
	    		
	    		//contruct tmpGetInvoke to store currUseValue
				Local tmpGetCast = Jimple.v().newLocal("tmpGetCast"+Long.toString(counter), castValue.getType());
				aBody.getLocals().add(tmpGetCast);
				localArray.add(tmpGetCast);
    			G.v().out.println("tmpValue: "+tmpGetCast.toString());    	        	

    			/*init tmpGetInvoke after all IdentityStmts*/
				DefinitionStmt assignStmt = initAssignStmt(tmpGetCast);
//    			G.v().out.println("newAssignStmt is: "+assignStmt.toString());
//    	        G.v().out.println("lastIdentityStmt is: "+lastIdentityStmt.toString());
    			units.insertAfter(assignStmt, lastIdentityStmt);
				
    			/*contruct assignstmt "tmpGetInvoke = arrRefParaValue"*/
				assignStmt = Jimple.v().newAssignStmt(tmpGetCast, castValue);
    			G.v().out.println("newAssignStmt is: "+assignStmt.toString());
				units.insertBefore(assignStmt, currProStmt);

    			G.v().out.println("currUseValu is: "+oneValueList.toString());
    			replaceValueGetStmt(aBody, sgxObjLocal, units, localArray, assignStmt, oneValueList,getUUIDLocal);
    			
    			G.v().out.println("CastExpr to be replaced is: ++++++++++++++++++++++++++ "+rightOp+"++++++++++++++++++++++");        			
    			    			
    			//if(castValue.toString().equals(((ArrayRef)rightOp).getBase().toString())){
    			//	((CastExpr)rightOp).setBase(tmpGetCast);
    			//}
    			//else if(castValue.toString().equals(((CastExpr)rightOp).getIndex().toString())){
    			//	((CastExpr)rightOp).setIndex(tmpGetCast);
    			//}
    			((CastExpr)rightOp).setOp(tmpGetCast);//
    			
    			G.v().out.println("new CastExpr is: ++++++++++++++++++++++++++ "+rightOp+"++++++++++++++++++++++");
    			((AssignStmt)currProStmt).setRightOp(rightOp);
    		}
			G.v().out.println("new CastExprStmt is: ++++++++++++++++++++++++++ "+currProStmt+"++++++++++++++++++++++");
			return;
		}
    	
    	//leftop 不包含condval,可退出
    	ArrayList<Value> testValuesArrayList = new ArrayList<Value>();
    	for (Value v:values){
    		testValuesArrayList.add(v);
    	}
    	testValuesArrayList.retainAll(condVals);
		G.v().out.println("testValuesArrayList length is:"+testValuesArrayList.size());
    	if(testValuesArrayList.isEmpty()){ //add in 0613
    		G.v().out.println("testValuesArrayList.retainAll(condVals) is null;");
    		return;
    	}
    	
		int index=0;

		String left_index="-1";
		String right_index="-1";
		String return_index="-1";
		boolean setParam0 = false, setParam1 = false;
		String symbolString = null;
		int val_type=0;
		int pos_index=0;
		
    	for(Value local: values){
//			G.v().out.println("values:********"+local+"*************");
		}			

		for(String local: operator){
			symbolString = local;
//			G.v().out.println("operator:********"+local+"*************");
		}
		//insert stmt
		//SootMethod toCall = Scene.v().getMethod
		//	      ("<invoker.sgx_invoker: void clear()>");
		Stmt newInvokeStmt = null;
				//Jimple.v().newInvokeStmt(
		//		Jimple.v().newVirtualInvokeExpr
		//           (sgxObjLocal, toCall.makeRef(), Arrays.asList()));
	//G.v().out.println("newInvokeStmt to insert is: ++++++++++++++++++++++++++ "+newInvokeStmt+"++++++++++++++++++++++");
	G.v().out.println("start insert before currStmt: ++++++++++++++++++++++++++ "+currProStmt+"++++++++++++++++++++++");
		//units.insertBefore(newInvokeStmt, currProStmt);

		//toCall = Scene.v().getMethod
		//	      ("<invoker.sgx_invoker: void setCounter(long)>");
		//newInvokeStmt = Jimple.v().newInvokeStmt(
		//		Jimple.v().newVirtualInvokeExpr
		//           (sgxObjLocal, toCall.makeRef(), Arrays.asList(LongConstant.v(counter))));
//		G.v().out.println("newInvokeStmt to insert is: ++++++++++++++++++++++++++ "+newInvokeStmt+"++++++++++++++++++++++");
//		G.v().out.println("start insert before currStmt: ++++++++++++++++++++++++++ "+currProStmt+"++++++++++++++++++++++");
		//units.insertBefore(newInvokeStmt, currProStmt);
//		G.v().out.println("zzzzzzzzzzzzzzyyyyyyyyyyyyyyy1");
		int returnTypeIndex = TypeIndex(leftOpValue);//return value type index
		G.v().out.println("consint 1221 size："+condValsInt.size());
		G.v().out.println("returnTypeIndex 1221："+returnTypeIndex);
		G.v().out.println("<<<<<<ZYSTBLE>>>>>> leftOpValue: ++++++++++++++++++++++++++"+leftOpValue.toString()+"++++++++++++++++++++++");
		pos_index = typeToList(returnTypeIndex).indexOf(leftOpValue);
		G.v().out.println("1221 pos_index:"+pos_index);
		return_index = Integer.toString(returnTypeIndex*100+pos_index);
		G.v().out.println("1221 return_index:"+return_index);
		int opTypeIndex = TypeIndex(values.get(0));
		indexwriter(Integer.toString(opTypeIndex));//tuple-0
		G.v().out.println("<<<<<<ZYSTBLE>>>>>> tuple-0 Get: ++++++++++++++++++++++++++ "+Integer.toString(opTypeIndex)+"++++++++++++++++++++++");
		int list_size = 0;
		int MaxSize = (localArray.size()>N)?N:localArray.size();
		Random rand = new Random();
		
		if(values.size()==1){
			G.v().out.println("values.size()==1");
			if(condVals.contains(values.get(0))){
				val_type = TypeIndex(values.get(0));//int or float
				G.v().out.println("val_type:"+val_type);
				pos_index = typeToList(val_type).indexOf(values.get(0));
				G.v().out.println("pos_index:"+pos_index);
				left_index = Integer.toString(val_type*100+pos_index);
			}else{
				for(Local loc:localArray){//将variable随机插入localarray
					if((loc.equals(values.get(0))) && (list_size >= MaxSize - 1)){
						int index_random = rand.nextInt(MaxSize - 1);
						localArray.remove(loc);
						localArray.add(index_random, loc);
					}
					list_size++;
				}
				for(Local loc:localArray){
					if(!isTypeCompatible(values.get(0).getType(), loc.getType()))
						continue;
					if((loc.equals(values.get(0)) || (rand.nextDouble()<=ratio)) && (index<N)){
						if(loc.equals(values.get(0))){
//							val_type = TypeIndex(values.get(0));//int or float
							left_index = Integer.toString(index);
							setParam0 = true;
						}						
						newInvokeStmt = prepareInsertStmt(loc, sgxObjLocal, "invoker.sgx_invoker");//只add类型相同的变量
						units.insertBefore(newInvokeStmt, currProStmt);
						index++;
					}
				}
				if(!setParam0){
					left_index = ((Value)(values.get(0))).getType().toString()+"_"+values.get(0);
					setParam0 = true;
				}
			}
		}else if(values.size()==2){
			G.v().out.println("values.size()==2");
			if(condVals.contains(values.get(0))){
				val_type = TypeIndex(values.get(0));//int or float
				pos_index = typeToList(val_type).indexOf(values.get(0));
				left_index = Integer.toString(val_type*100+pos_index);
				setParam0 = true;
			}
			if(condVals.contains(values.get(1))){
				val_type = TypeIndex(values.get(1));//int or float
				pos_index = typeToList(val_type).indexOf(values.get(1));
				right_index = Integer.toString(val_type*100+pos_index);
				setParam1 = true;
			}
			if(!setParam0 && !setParam1){
				for(Value val: values){//variable-tobehidden;
					for(Local loc:localArray){//将variable随机插入localarray
						if((loc.equals(val)) && (list_size >= MaxSize - 1)){
							int index_random = rand.nextInt(MaxSize - 1);
							localArray.remove(loc);
							localArray.add(index_random, loc);
						}
						list_size++;
					}
				}
				for(Local loc:localArray){
					if(!isTypeCompatible(values.get(0).getType(), loc.getType()))
						continue;
//					if(isTypeCompatible(values.get(0).getType(), values.get(1).getType())){
					if((loc.equals(values.get(0))||loc.equals(values.get(1))||(rand.nextDouble()<=ratio)) && (index<N)){
						if(loc.equals(values.get(0))){
//							val_type = TypeIndex(values.get(0));//int or float
							left_index = Integer.toString(index);
							setParam0 = true;
						}
						if(loc.equals(values.get(1))){
//							val_type = TypeIndex(values.get(1));//int or float
							right_index = Integer.toString(index);
							setParam1 = true;
						}
						newInvokeStmt = prepareInsertStmt(loc, sgxObjLocal, "invoker.sgx_invoker");//只add类型相同的变量
						units.insertBefore(newInvokeStmt, currProStmt);
						index++;
					}
//					}	
				}
			}else if(!setParam0){
				for(Local loc:localArray){//将variable随机插入localarray
					if((loc.equals(values.get(0))) && (list_size >= MaxSize - 1)){
						int index_random = rand.nextInt(MaxSize - 1);
						localArray.remove(loc);
						localArray.add(index_random, loc);
					}
					list_size++;
				}
				for(Local loc:localArray){
					if(!isTypeCompatible(values.get(0).getType(), loc.getType()))
						continue;
					if((loc.equals(values.get(0)) || (rand.nextDouble()<=ratio)) && (index<N)){
						if(loc.equals(values.get(0))){
//							val_type = TypeIndex(values.get(0));//int or float
							left_index = Integer.toString(index);
							setParam0 = true;
						}
						newInvokeStmt = prepareInsertStmt(loc, sgxObjLocal, "invoker.sgx_invoker");//只add类型相同的变量
						units.insertBefore(newInvokeStmt, currProStmt);
						index++;
					}
				}
			}else if(!setParam1){
				for(Local loc:localArray){//将variable随机插入localarray
					if((loc.equals(values.get(1))) && (list_size >= MaxSize - 1)){
						int index_random = rand.nextInt(MaxSize - 1);
						localArray.remove(loc);
						localArray.add(index_random, loc);
					}
					list_size++;
				}
				for(Local loc:localArray){
					if(!isTypeCompatible(values.get(1).getType(), loc.getType()))
						continue;
					if((loc.equals(values.get(1)) || (rand.nextDouble()<=ratio)) && (index<N)){
						if(loc.equals(values.get(1))){
//							val_type = TypeIndex(values.get(1));//int or float
							right_index = Integer.toString(index);
							setParam1 = true;
						}
						
						newInvokeStmt = prepareInsertStmt(loc, sgxObjLocal, "invoker.sgx_invoker");//只add类型相同的变量
						units.insertBefore(newInvokeStmt, currProStmt);
						index++;
					}
				}
			}
			if(!setParam0){//constant
				left_index = ((Value)(values.get(0))).getType().toString()+"_"+values.get(0);
				setParam0=true;
			}
			if(!setParam1){//constant
				right_index = ((Value)(values.get(1))).getType().toString()+"_"+values.get(1);
				setParam1=true;
			}
		}else{
	//		G.v().out.println("********error: values size isnot 1 nor 2!********");
		}
		indexwriter(left_index);//tuple-1
		indexwriter(right_index);//tuple-2
		if(!operator.isEmpty()){
			if(symbolString.equals(" + "))
				indexwriter("1");
			else if(symbolString.equals(" - ") || symbolString.equals(" cmp ") || symbolString.equals(" cmpg "))
				indexwriter("2");
			else if(symbolString.equals(" * "))
				indexwriter("3");
			else if(symbolString.equals(" / "))
				indexwriter("4");
			else if(symbolString.equals(" % "))
				indexwriter("5");
			else 
				indexwriter("-1");
		}else{
			indexwriter("-1");
		}
		indexwriter("-1");
		G.v().out.println("stmt get first operand:********"+left_index+"*************");
		G.v().out.println("stmt get second operand:********"+right_index+"*************");
		//if(left_index == "-1")
		//	G.v().out.println("stmt has no first operand:********"+left_index+"*************");
		//if(right_index == "-1")
		//	G.v().out.println("A stmt has no second operand:********"+right_index+"*************");
		
		boolean LeftOpIsArrayRef=false;
		boolean LeftOpIsObject=false;

		G.v().out.println("curr stmt："+currProStmt.toString());
		G.v().out.println("leftOpValue："+leftOpValue.toString());
    	if(leftOpValue instanceof ArrayRef){
    		G.v().out.println("rrrrrrrrrrrrrrrrrrrrrrrrr");
    		LeftOpIsArrayRef = true;
    	}else if(leftOpValue.getType().toString().equals("org.apache.hadoop.mapred.JobConf")){
    		G.v().out.println("kkkkkkkkkkkkkkkkkkkkkkkkk");
    		LeftOpIsObject=true;
		}

		G.v().out.println("start insert an un-invoke get");
//		G.v().out.println("LeftOpBaseTYpe---------------zystble2:"+((ArrayRef)leftOpValue).getBase().getType());
		G.v().out.println("returnTypeIndex:"+returnTypeIndex);
		G.v().out.println("returnTypeIndexToCallFunc:"+returnTypeIndexToCallFunc(returnTypeIndex));
    	SootMethod toCall = Scene.v().getMethod (returnTypeIndexToCallFunc(returnTypeIndex));
		DefinitionStmt assignStmt=null;
		
		G.v().out.println("zystble1");
		if(LeftOpIsArrayRef){
			G.v().out.println("LeftOpIsArrayRef---------------zystble2:"+leftOpValue.toString());
			/*contruct tmpRef */
			Local tmpRef=Jimple.v().newLocal
					("tmpArrayRef"+String.valueOf(counter),leftOpValue.getType());				 
			aBody.getLocals().add(tmpRef);
			localArray.add(tmpRef);    			
			G.v().out.println("tmpValue: "+tmpRef.toString());    	        	
		
			/*tmpRef init stmt after all identitystmt*/
			assignStmt = initAssignStmt(tmpRef);
			G.v().out.println("newAssignStmt is: "+assignStmt.toString());	        			
			G.v().out.println("lastIdentityStmt is: "+lastIdentityStmt.toString());
			units.insertAfter(assignStmt, lastIdentityStmt);

			/*tmpRef assignstmt "tmpArrayRef=getIntValue()"*/
			assignStmt = Jimple.v().newAssignStmt(tmpRef,
					Jimple.v().newVirtualInvokeExpr
				          (sgxObjLocal, toCall.makeRef(), Arrays.asList(getUUIDLocal,LongConstant.v(counter))));
			units.insertBefore(assignStmt, currProStmt);
			
			/*currstmt "leftop=tmpArrayRef"*/
			((AssignStmt)currProStmt).setRightOp(tmpRef);
		}else if (LeftOpIsObject) {
			/*contruct tmpRef */
			G.v().out.println("LeftOpIsObject---------------zystble2");
			Local tmpRef=Jimple.v().newLocal
					("tmpObjectRef"+String.valueOf(counter),leftOpValue.getType());				 
			aBody.getLocals().add(tmpRef);
			localArray.add(tmpRef);    			
			G.v().out.println("tmpValue: "+tmpRef.toString());    	        	
		
			/*tmpRef init stmt after all identitystmt*/
			assignStmt = initAssignStmt(tmpRef);
			G.v().out.println("object newAssignStmt is: "+assignStmt.toString());	        			
			G.v().out.println("object lastIdentityStmt is: "+lastIdentityStmt.toString());
			units.insertAfter(assignStmt, lastIdentityStmt);

			/*tmpRef assignstmt "tmpArrayRef=getIntValue()"*/
			assignStmt = Jimple.v().newAssignStmt(tmpRef,
					Jimple.v().newVirtualInvokeExpr
				          (sgxObjLocal, toCall.makeRef(), Arrays.asList(getUUIDLocal,LongConstant.v(counter))));
			units.insertBefore(assignStmt, currProStmt);
			
			/*currstmt "leftop=tmpArrayRef"*/
			((AssignStmt)currProStmt).setRightOp(tmpRef);
			G.v().out.println("already set rightop");
		}
		else{
			G.v().out.println("general stmt--------------zystble3");
			G.v().out.println("0611============leftOpValue is: "+leftOpValue.toString());	        			
			G.v().out.println("0611============curr AssignStmt is: "+currProStmt.toString());	        			

			assignStmt = Jimple.v().newAssignStmt(leftOpValue,
					Jimple.v().newVirtualInvokeExpr
				          (sgxObjLocal, toCall.makeRef(), Arrays.asList(getUUIDLocal,LongConstant.v(counter))));
			G.v().out.println("0611============newAssignStmt is: "+assignStmt.toString());	        			
			units.insertBefore(assignStmt, currProStmt);
			units.remove(currProStmt);
		}
		//G.v().out.println("zystble");
//		InvokeExpr invokeExprtmpExpr = Jimple.v().newVirtualInvokeExpr
//		          (sgxObjLocal, toCall.makeRef(), Arrays.asList());
//		G.v().out.println("invokeExprtmpExpr is:++++++"+invokeExprtmpExpr+"++++++++");
////		G.v().out.println("invokeExprtmpExpr type is:++++++"+invokeExprtmpExp+"++++++++");
//		((AssignStmt)currProStmt).setRightOp((Value)invokeExprtmpExpr);
		
//		G.v().out.println("rightOpvalueOfAssignment is:++++++"+rightOp+"++++++++");
//		G.v().out.println("currProStmt units is: ++++ "+currProStmt.getUseBoxes()+"++++++++++++");
		G.v().out.println("get counter:"+counter);
		counter++;
	}
    
    private String returnTypeIndexToCallFunc(int returnTypeIndex){
    	String funcString=new String();
    	switch (returnTypeIndex) {
		case 1:
			funcString =  "<invoker.sgx_invoker: int getIntValue(java.lang.String,long)>";//getIntValue
			break;
		case 2:
			funcString = "<invoker.sgx_invoker: double getDoubleValue()>";
			break;
		case 3:
			funcString = "<invoker.sgx_invoker: float getFloatValue()>";
			break;
		case 4:
			funcString = "<invoker.sgx_invoker: char getCharValue()>";
			break;
		case 5:
			funcString = "<invoker.sgx_invoker: long getLongValue()>";
			break;
		case 6:
			funcString = "<invoker.sgx_invoker: byte getByteValue()>";
			break;
			
		default:
			break;
		}
    	return funcString;
    }
    
	@SuppressWarnings("unused")
	private void replaceBranchStmt(
			Body aBody,
			Local sgxObjLocal,
			Local branchResultLocal,
			PatchingChain<Unit> units,
			List<Local> localArray,
			Unit currProStmt,
			Local getUUIDLocal) {
		
    	Value ifCondition = ((IfStmt)currProStmt).getCondition();
    	G.v().out.println(" curr pro Unit: "+ifCondition+";");
		ArrayList<Value> variable = new ArrayList<Value>();//
		ArrayList<Value> values = new ArrayList<Value>();
    	ArrayList<Value> cons= new ArrayList<Value>();
		ArrayList<String> operator = new ArrayList<String>();

		analyzeExp(ifCondition, values, operator, cons, variable);
		
		int index=0;
		String left_index="-1";
		String right_index="-1";
		String return_index="-1";
		boolean setParam0 = false, setParam1 = false;
		String symbolString = null;
		int val_type=0;
		int pos_index=0;
		
//    	for(Value local: values){
//			G.v().out.println("values:********"+local+"*************");
//		}			
//		for(Value local: variable){
//			G.v().out.println("variable:********"+local+"*************");//parameter non-constant
//		}
//		for(Value local: cons){
//			G.v().out.println("cons:********"+local+"*************");//constant
//		}
		for(String local: operator){
			symbolString = local;
			G.v().out.println("operator:********"+local+"*************");
		}
//		SootMethod toCall = Scene.v().getMethod
//			      ("<invoker.sgx_invoker: void clear()>");
//		Stmt newInvokeStmt = Jimple.v().newInvokeStmt(
//				Jimple.v().newVirtualInvokeExpr
//		           (sgxObjLocal, toCall.makeRef(), Arrays.asList()));
//		G.v().out.println("newInvokeStmt to insert is: ++++++++++++++++++++++++++ "+newInvokeStmt+"++++++++++++++++++++++");
//		G.v().out.println("start insert before currStmt: ++++++++++++++++++++++++++ "+currProStmt+"++++++++++++++++++++++");
//		units.insertBefore(newInvokeStmt, currProStmt);
//		
//		toCall = Scene.v().getMethod
//			      ("<invoker.sgx_invoker: void setCounter(long)>");
//		newInvokeStmt = Jimple.v().newInvokeStmt(
//				Jimple.v().newVirtualInvokeExpr
//		           (sgxObjLocal, toCall.makeRef(), Arrays.asList(LongConstant.v(counter))));
////		G.v().out.println("curr counter is: ++++++++++++++++++++++++++ "+counter+"++++++++++++++++++++++");
////		G.v().out.println("newInvokeStmt to insert is: ++++++++++++++++++++++++++ "+newInvokeStmt+"++++++++++++++++++++++");
////		G.v().out.println("start insert before currStmt: ++++++++++++++++++++++++++ "+currProStmt+"++++++++++++++++++++++");
//		units.insertBefore(newInvokeStmt, currProStmt);
		
		int opTypeIndex = TypeIndex(values.get(0));//op value type index
		indexwriter(Integer.toString(opTypeIndex));//tuple-0
		G.v().out.println("<<<<<<ZYSTBLE>>>>>> tuple-0 branch: ++++++++++++++++++++++++++ "+Integer.toString(opTypeIndex)+"++++++++++++++++++++++");
		int list_size = 0;
		int MaxSize = (localArray.size()>N)?N:localArray.size();
		Random rand = new Random();
		
		if(values.size()==1){
			G.v().out.println("there is only one para in condition values!!!++++++++++++++++++++++++++++++++");
		}else if(values.size()==2){
			if(condVals.contains(values.get(0))){
				G.v().out.println("values0 is in condvals!");
				val_type = TypeIndex(values.get(0));//int or float
				G.v().out.println("val_type is:===="+val_type);
				pos_index = typeToList(val_type).indexOf(values.get(0));
				G.v().out.println("pos_index is:===="+pos_index);
				left_index = Integer.toString(val_type*100+pos_index);
				G.v().out.println("left_index is:===="+left_index);
				setParam0 = true;
			}
			if(condVals.contains(values.get(1))){
				G.v().out.println("values1 is in condvals!");
				val_type = TypeIndex(values.get(1));//int or float
				G.v().out.println("val_type is:===="+val_type);
				pos_index = typeToList(val_type).indexOf(values.get(1));
				G.v().out.println("pos_index is:===="+pos_index);
				right_index = Integer.toString(val_type*100+pos_index);
				G.v().out.println("right_index is:===="+right_index);
				setParam1 = true;
			}
			if(!setParam0){
				G.v().out.println("values0 is constant!");
				left_index = ((Value)(values.get(0))).getType().toString()+"_"+values.get(0);
				setParam0=true;
			}
			if(!setParam1){
				G.v().out.println("values1 is constant!");
				G.v().out.println("values.get(1):"+(Value)values.get(1));
				G.v().out.println("values.get(1).type:"+((Value)(values.get(1))).getType().toString());
				right_index = ((Value)(values.get(1))).getType().toString()+"_"+values.get(1);
				if(((Value)(values.get(1))).getType().toString().equals("null_type")){
					right_index = "int_0";
				}
				setParam1=true;
			}
		}else{
			G.v().out.println("********error: values size is not 1 nor 2!********");
		}
		if(!setParam0 || !setParam1)
			G.v().out.println("values are not in hidden list!!!!!********");
		
		indexwriter(left_index);//tuple-1
		G.v().out.println("left_index：====b==:"+left_index);
		indexwriter(right_index);//tuple-2
		G.v().out.println("right_index：===b===:"+right_index);
		G.v().out.println("operator：===b===:"+operator);
		if(!operator.isEmpty()){
			if(symbolString.equals(" == "))
				indexwriter("6");
			else if(symbolString.equals(" != ") || symbolString.equals(" cmp "))
				indexwriter("7");
			else if(symbolString.equals(" > "))
				indexwriter("8");
			else if(symbolString.equals(" < "))
				indexwriter("9");
			else if(symbolString.equals(" >= "))
				indexwriter("10");
			else if(symbolString.equals(" <= "))
				indexwriter("11");
			else 
				indexwriter("-1");
		}else{
			indexwriter("-1");
		}
		indexwriter("-1");
		G.v().out.println("re：===b===:-1");
		G.v().out.println("counter：===b===:"+counter);
		if(left_index == "-1")
			G.v().out.println("stmt branch has no first operand:********"+left_index+"*************");
		if(right_index == "-1")
			G.v().out.println("stmt branch has no second operand:********"+right_index+"*************");

		SootMethod toCall = Scene.v().getMethod ("<invoker.sgx_invoker: boolean getBooleanValue(java.lang.String,long)>");
//		toCall = Scene.v().getMethod (returnTypeIndexToCallFunc(1));//返回值为int类型
		DefinitionStmt assignStmt = Jimple.v().newAssignStmt(branchResultLocal,
				Jimple.v().newVirtualInvokeExpr
		           (sgxObjLocal, toCall.makeRef(), Arrays.asList(getUUIDLocal,LongConstant.v(counter))));//IntConstant.v(1)));//返回值为int类型
		units.insertBefore(assignStmt, currProStmt);
		((IfStmt)currProStmt).setCondition(new JEqExpr(branchResultLocal, IntConstant.v(1)));

		G.v().out.println("assignStmt to insert is: ++++++++++++++++++++++++++ "+assignStmt+"++++++++++++++++++++++");
		G.v().out.println("start insert before currStmt: ++++++++++++++++++++++++++ "+currProStmt+"++++++++++++++++++++++");
		counter++;
    }
    
	@SuppressWarnings("unused")
    private Unit replaceValueUpdateStmt(
			Body aBody,
			Local sgxObjLocal,
			PatchingChain<Unit> units,
			List<Local> localArray,
			Unit currProStmt,
			Local getUUIDLocal) {
		// TODO Auto-generated method stub
    	Value rightOp = null;
    	Value leftOpValue = null;
    	if(currProStmt instanceof AssignStmt){
    		rightOp = ((AssignStmt)currProStmt).getRightOp();
    		leftOpValue = ((AssignStmt)currProStmt).getLeftOp();
            G.v().out.println("ass r curr pro Unit: "+rightOp+";");
            G.v().out.println("ass r curr pro Unit type: "+rightOp.getType().toString()+";");
            G.v().out.println("ass l curr pro Unit: "+leftOpValue+";");
            G.v().out.println("ass l curr pro Unit type: "+leftOpValue.getType().toString()+";");
    	}else if(currProStmt instanceof IdentityStmt){
   		 	rightOp = ((IdentityStmt)currProStmt).getRightOp();
   		 	leftOpValue = ((IdentityStmt)currProStmt).getLeftOp();
            G.v().out.println("ide r curr pro Unit: "+rightOp+";");
            G.v().out.println("ide l curr pro Unit: "+leftOpValue+";");
    	}else{

            G.v().out.println(" currProStmt Type: "+currProStmt.getClass()+";");
        }
    	G.v().out.println("=curr pro Unit: "+rightOp+";");
    	
		ArrayList<Value> variable = new ArrayList<Value>();//
		ArrayList<Value> cons = new ArrayList<Value>();//
		ArrayList<Value> values = new ArrayList<Value>();
		ArrayList<String> operator = new ArrayList<String>();
		boolean RightOpIsInvoke = false;
		boolean isRightOpInCondVal = false;
		boolean isRightOpStaticFiled = false;
		
    	analyzeExp(rightOp, values, operator, cons, variable);//
    	
    	for(Value local: values){
			G.v().out.println("values:********"+local+"*************");
			G.v().out.println("values.type:********"+local.getType().toString()+"*************");
		}			
//		for(Value local: variable){
//			G.v().out.println("variable:********"+local+"*************");//parameter non-constant
//		}
//		for(Value local: cons){
//			G.v().out.println("cons:********"+local+"*************");//constant
//		}
    	
    	ArrayList<Value> rightCondValue = new ArrayList<Value>();
    	for(Value val:values){
    		if((val instanceof JLengthExpr)||(val instanceof InstanceInvokeExpr)||(val instanceof ArrayRef)|| (val instanceof JStaticInvokeExpr)|| (val instanceof StaticFieldRef)  || (val instanceof JInstanceFieldRef))
    			RightOpIsInvoke = true;
    		// || (val instanceof JStaticInvokeExpr)  || (val instanceof JInstanceFieldRef)
    		//if(val instanceof StaticFieldRef){
    		//	G.v().out.println("isRightOpStaticFiled:********"+isRightOpStaticFiled+"*************");
    		//	isRightOpStaticFiled = true;
    		//}
        	Iterator<ValueBox> vbIterator =  val.getUseBoxes().iterator();
        	while(vbIterator.hasNext()){
            	Value tValue = vbIterator.next().getValue();
            	rightCondValue.add(tValue);
            }	
//    		if(condVals.contains(val))
//    			isRightOpInCondVal=true;
//    		if(val instanceof ParameterRef){
//				G.v().out.println("the ParameterRef is: "+val);
//				localArray.add(val);
//				((ParameterRef)val).
//    		}
    			
    	}
    	G.v().out.println("rightCondValue1: "+rightCondValue);
    	G.v().out.println("condVals: "+condVals);
    	rightCondValue.retainAll(condVals); //n
    	G.v().out.println("rightCondValue2: "+rightCondValue);
    	
    	//to process stmt like x=invoke(temp1) or x=invoke(y)
		if(RightOpIsInvoke){
//			G.v().out.println("start insert an invoke tmp");
			Local tmpValue = Jimple.v().newLocal("tmpResult"+Long.toString(counter), leftOpValue.getType());
			aBody.getLocals().add(tmpValue);
			localArray.add(tmpValue);
			G.v().out.println("RightOpIsInvoke tmpValue: "+tmpValue.toString());    	        	

			//insert tmpValue init stmt after all IdentityStmts
			DefinitionStmt assignStmt = initAssignStmt(tmpValue);
			G.v().out.println("newAssignStmt is: "+assignStmt.toString());	        			
			G.v().out.println("lastIdentityStmt is: "+lastIdentityStmt.toString());
			units.insertAfter(assignStmt, lastIdentityStmt);
			
			//insert tmp=a[x] or tmp=a[b]
			assignStmt = Jimple.v().newAssignStmt(tmpValue,rightOp); //tem = invoker
			G.v().out.println("newAssignStmt is: "+assignStmt.toString());	
			//G.v().out.println("currProStmt is: "+currProStmt.toString());	
			units.insertBefore(assignStmt, currProStmt);
			//G.v().out.println("currProStmt is: "+currProStmt.toString());	
			if(!rightCondValue.isEmpty()){//del with tmp=a[x]
//				rightOp = assignStmt.getRightOp();
//    	    	leftOpValue = assignStmt.getLeftOp();
				replaceValueGetStmt(aBody, sgxObjLocal, units, localArray, (Unit)assignStmt, rightCondValue,getUUIDLocal);
			}

			G.v().out.println("newInvokeStmt to insert is: ++++++++++++++++++++++++++ "+assignStmt+"++++++++++++++++++++++");
			G.v().out.println("start insert before currStmt: ++++++++++++++++++++++++++ "+currProStmt+"++++++++++++++++++++++");
//			G.v().out.println("InvokeExpr class is: ++++++++++++++++++++++++++ "+rightOp.getClass()+"++++++++++++++++++++++");        			
			((AssignStmt)currProStmt).setRightOp(tmpValue);
//			G.v().out.println("InvokeExpr class is: ++++++++++++++++++++++++++ "+tmpValue.getClass()+"++++++++++++++++++++++");        			
			G.v().out.println("currStmt: ++++++++++++++++++++++++++ "+currProStmt+"++++++++++++++++++++++");
			values.clear();
			operator.clear();
	    	analyzeExp(tmpValue, values, operator, cons, variable);//
		}

		int index=0;
		String left_index="-1";
		String right_index="-1";
		String return_index="-1";
		boolean setParam0 = false, setParam1 = false;
		String symbolString = null;
		int val_type=0;
		int pos_index=0;
	
		for(String local: operator){
			symbolString = local;
			G.v().out.println("operator:********"+local+"*************");
		}

		SootMethod toCall = null;
				//Scene.v().getMethod
		//	      ("<invoker.sgx_invoker: void clear()>");
		Stmt newInvokeStmt = null;
//				Jimple.v().newInvokeStmt(
//				Jimple.v().newVirtualInvokeExpr
//		           (sgxObjLocal, toCall.makeRef(), Arrays.asList()));
//		G.v().out.println("newInvokeStmt to insert is: ++++++++++++++++++++++++++ "+newInvokeStmt+"++++++++++++++++++++++");
//		G.v().out.println("start insert before currStmt: ++++++++++++++++++++++++++ "+currProStmt+"++++++++++++++++++++++");
//		units.insertBefore(newInvokeStmt, currProStmt);

//		toCall = Scene.v().getMethod("<invoker.sgx_invoker: void setCounter(long)>");
//		newInvokeStmt = Jimple.v().newInvokeStmt(
//				Jimple.v().newVirtualInvokeExpr
//		           (sgxObjLocal, toCall.makeRef(), Arrays.asList(LongConstant.v(counter))));
//		G.v().out.println("newInvokeStmt to insert is: ++++++++++++++++++++++++++ "+newInvokeStmt+"++++++++++++++++++++++");
		G.v().out.println("start insert before currStmt: ++++++++++++++++++++++++++ "+currProStmt+"++++++++++++++++++++++");
//		units.insertBefore(newInvokeStmt, currProStmt);
		G.v().out.println("=leftOpValue.type=="+leftOpValue.getType().toString());
		G.v().out.println("=leftOpValue=="+leftOpValue);
		int returnTypeIndex = TypeIndex(leftOpValue);//return value type index
		G.v().out.println("returnTypeIndex="+returnTypeIndex);
		pos_index = typeToList(returnTypeIndex).indexOf(leftOpValue);
		G.v().out.println("pos_index="+pos_index);
		return_index = Integer.toString(returnTypeIndex*100+pos_index);
		G.v().out.println("return_index="+return_index);
		val_type = TypeIndex(values.get(0));
		G.v().out.println("values.get(0)="+values.get(0));
		
		pos_index = typeToList(val_type).indexOf(values.get(0));   //???
		G.v().out.println("pos_index="+pos_index);
		indexwriter(Integer.toString(val_type));//tuple-0: opOne's type
		G.v().out.println("<<<<<<ZYSTBLE>>>>>> tuple-0 update: ++++++++++++++++++++++++++ "+Integer.toString(val_type)+"++++++++++++++++++++++");
		int list_size = 0;
		int MaxSize = (localArray.size()>N)?N:localArray.size();
		Random rand = new Random();
		G.v().out.println("values.size="+values.size());
		if(values.size()==1){
			if(condVals.contains(values.get(0))){
				val_type = TypeIndex(values.get(0));//int or float
				pos_index = typeToList(val_type).indexOf(values.get(0));
				left_index = Integer.toString(val_type*100+pos_index);//
				
				G.v().out.println("values.get(0):"+values.get(0));
				G.v().out.println("pos_index:"+pos_index);
				G.v().out.println("left_index"+left_index);
			}else{
				for(Local loc:localArray){//将variable随机插入localarray
					if((loc.equals(values.get(0))) && (list_size >= MaxSize - 1)){
						int index_random = rand.nextInt(MaxSize - 1);
						localArray.remove(loc);
						localArray.add(index_random, loc);
					}
					list_size++;
				}
				for(Local loc:localArray){
					if(!isTypeCompatible(values.get(0).getType(), loc.getType()))
						continue;
					if((loc.equals(values.get(0)) || (rand.nextDouble()<=ratio)) && (index<N)){
						if(loc.equals(values.get(0))){
							//val_type = TypeIndex(values.get(0));//int or float
							//left_index = "1"+Integer.toString(val_type*10+index);//
							left_index = Integer.toString(index);//
							setParam0 = true;
						}						
						newInvokeStmt = prepareInsertStmt(loc, sgxObjLocal, "invoker.sgx_invoker");//只add类型相同的变量
						units.insertBefore(newInvokeStmt, currProStmt);
						index++;
					}
				}
				if(!setParam0){
					if(values.get(0) instanceof ParameterRef){
						G.v().out.println("the only @paraRef Value is: "+values.get(0));
						//new local = @paraRef1
					}
					else if(values.get(0) instanceof Constant){
						left_index = ((Value)(values.get(0))).getType().toString()+"_"+values.get(0);
						setParam0 = true;
					}
				}
			}
		}else if(values.size()==2){
			G.v().out.println("!!!!!enter!!!!!!!!!");
			if(condVals.contains(values.get(0))){
				G.v().out.println("values0 is cond val"+"++++++++++++++"+values.get(0));
				val_type = TypeIndex(values.get(0));//int or float
				pos_index = typeToList(val_type).indexOf(values.get(0));
				left_index = Integer.toString(val_type*100+pos_index);
				setParam0 = true;
			}
			if(condVals.contains(values.get(1))){
				G.v().out.println("values1 is cond val"+"++++++++++++++"+values.get(1));
				val_type = TypeIndex(values.get(1));//int or float
				pos_index = typeToList(val_type).indexOf(values.get(1));
				right_index = Integer.toString(val_type*100+pos_index);
				setParam1 = true;
			}
			if(!setParam0 && !setParam1){
				for(Value val: values){//variable-tobehidden;
					for(Local loc:localArray){//将variable随机插入localarray
						if((loc.equals(val)) && (list_size >= MaxSize - 1)){
							int index_random = rand.nextInt(MaxSize - 1);
							localArray.remove(loc);
							localArray.add(index_random, loc);
						}
						list_size++;
					}
				}
				for(Local loc:localArray){
					if(!isTypeCompatible(values.get(0).getType(), loc.getType()) )
						continue;
					if((loc.equals(values.get(0))||(loc.equals(values.get(1)))||(rand.nextDouble()<=ratio)) && (index<N)){	
						if(loc.equals(values.get(0))){
//							val_type = TypeIndex(values.get(0));//int or float
							left_index = Integer.toString(index);//val_type*10+index);//
							setParam0 = true;
						}
						if(loc.equals(values.get(1))){
//							val_type = TypeIndex(values.get(1));//int or float
							right_index = Integer.toString(index);//
							setParam1 = true;
						}
						newInvokeStmt = prepareInsertStmt(loc, sgxObjLocal, "invoker.sgx_invoker");//只add类型相同的变量
						units.insertBefore(newInvokeStmt, currProStmt);
						index++;
					}
//					}
				}
			}else if(!setParam0){
				for(Local loc:localArray){//将variable随机插入localarray
					if((loc.equals(values.get(0))) && (list_size >= MaxSize - 1)){
						int index_random = rand.nextInt(MaxSize - 1);
						localArray.remove(loc);
						localArray.add(index_random, loc);
					}
					list_size++;
				}
				for(Local loc:localArray){
					if(!isTypeCompatible(values.get(0).getType(), loc.getType()))
						continue;
					if((loc.equals(values.get(0)) || (rand.nextDouble()<=ratio)) && (index<N)){
						if(loc.equals(values.get(0))){
							val_type = TypeIndex(values.get(0));//int or float
							left_index = Integer.toString(index);//
							setParam0 = true;
						}
						newInvokeStmt = prepareInsertStmt(loc, sgxObjLocal, "invoker.sgx_invoker");//只add类型相同的变量
						units.insertBefore(newInvokeStmt, currProStmt);
						index++;
					}
				}
			}else if(!setParam1){
				for(Local loc:localArray){//将variable随机插入localarray
					if((loc.equals(values.get(1))) && (list_size >= MaxSize - 1)){
						int index_random = rand.nextInt(MaxSize - 1);
						localArray.remove(loc);
						localArray.add(index_random, loc);
					}
					list_size++;
				}
				for(Local loc:localArray){
					if(!isTypeCompatible(values.get(1).getType(), loc.getType()))
						continue;
					if((loc.equals(values.get(1)) || (rand.nextDouble()<=ratio)) && (index<N)){
						if(loc.equals(values.get(1))){
							val_type = TypeIndex(values.get(1));//int or float
							right_index = Integer.toString(index);//
							setParam1 = true;
						}
						newInvokeStmt = prepareInsertStmt(loc, sgxObjLocal, "invoker.sgx_invoker");//只add类型相同的变量
						units.insertBefore(newInvokeStmt, currProStmt);
						index++;
					}
				}
			}
			
			G.v().out.println("-----------8.1------------");
			if(!setParam0){
				G.v().out.println("left @paraRef Value is: "+values.get(0));
				left_index = ((Value)(values.get(0))).getType().toString()+"_"+values.get(0);
				
				G.v().out.println("8.1 left_constants left_index:"+left_index.toString());
				setParam0=true;
			}
			if(!setParam1){
				G.v().out.println("right @paraRef Value is: "+values.get(1));
				right_index = ((Value)(values.get(1))).getType().toString()+"_"+values.get(1);
				setParam1=true;
			}
		}else{
			G.v().out.println("********error: values size isnot 1 nor 2!********");
		}
		G.v().out.println("left_index:"+left_index);
		G.v().out.println("right_index:"+right_index);
		indexwriter(left_index);//tuple-1
		indexwriter(right_index);//tuple-2
		
		if(!operator.isEmpty()){
			if(symbolString.equals(" + "))
				indexwriter("1");
			else if(symbolString.equals(" - ") || symbolString.equals(" cmp ")  || symbolString.equals(" cmpl ") || symbolString.equals(" cmpg "))
				indexwriter("2");
			else if(symbolString.equals(" * "))
				indexwriter("3");
			else if(symbolString.equals(" / "))
				indexwriter("4");
			else if(symbolString.equals(" % "))
				indexwriter("5");
			else if(symbolString.equals(" & ")){     //new add on 8.18 by ZyStBle
				indexwriter("12");
			}else {
				G.v().out.println("not normal operator:"+operator);
				indexwriter("-1");
			}
		}else{
			indexwriter("-1");
		}
		indexwriter(return_index);
		G.v().out.println("return_index:"+return_index);
		G.v().out.println("counter:"+counter);
		if(left_index == "-1")
			G.v().out.println("stmt update has no first operand:********"+left_index+"*************");
		if(right_index == "-1")
			G.v().out.println("stmt update has no second operand:********"+right_index+"*************");

		toCall = Scene.v().getMethod ("<invoker.sgx_invoker: void updateValueInEnclave(java.lang.String,long)>");
		
		newInvokeStmt = Jimple.v().newInvokeStmt(
				Jimple.v().newVirtualInvokeExpr
		           (sgxObjLocal, toCall.makeRef(), Arrays.asList(getUUIDLocal,LongConstant.v(counter)))); //IntConstant.v(returnTypeIndex)));
//		G.v().out.println("newInvokeStmt to insert is: ++++++++++++++++++++++++++ "+newInvokeStmt+"++++++++++++++++++++++");
//		G.v().out.println("start insert before currStmt: ++++++++++++++++++++++++++ "+currProStmt+"++++++++++++++++++++++");
		units.insertBefore(newInvokeStmt, currProStmt);
		units.remove(currProStmt);
		counter++;
		
		return newInvokeStmt;
	}
	
	private InvokeStmt prepareInsertStmt(Value loggedValue, Local loggerLocal, String className){
		Type vType = loggedValue.getType();
		G.v().out.println("loggedValue type:"+loggedValue.getType().toString());
		SootMethod toCall = null;
		if(vType instanceof IntType || vType instanceof BooleanType || vType instanceof ShortType){
			 toCall = Scene.v().getMethod
				      ("<"+className+": void add(int)>");}
		else if(vType instanceof DoubleType){
			 toCall = Scene.v().getMethod
				      ("<"+className+": void add(double)>");}
		else if(vType instanceof FloatType){
			 toCall = Scene.v().getMethod
				      ("<"+className+": void add(float)>");}
		else if(vType instanceof soot.LongType){
			 toCall = Scene.v().getMethod
				      ("<"+className+": void add(long)>");}
		else if(vType instanceof CharType){
			 toCall = Scene.v().getMethod
				      ("<"+className+": void add(char)>");}
		else if(vType instanceof ByteType){
			 toCall = Scene.v().getMethod
				      ("<"+className+": void add(byte)>");}
		else if(vType instanceof ArrayType){
			//toCall = Scene.v().getMethod
			//	      ("<"+className+": void add(java.lang.Object)>");
			G.v().out.println("ArrayType loggedValue:"+loggedValue);
			G.v().out.println("ArrayType loggedValue:"+loggedValue.getType().toString());
			G.v().out.println("ArrayType loggedValue:"+loggedValue.hashCode());
			toCall = Scene.v().getMethod
				      ("<"+className+": void add(java.lang.Object)>");
		}else{
			G.v().out.println("else loggedValue:"+loggedValue);
			toCall = Scene.v().getMethod
				      ("<"+className+": void add(java.lang.Object)>");
		}
		InvokeStmt newInvokeStmt = Jimple.v().newInvokeStmt(
					Jimple.v().newVirtualInvokeExpr
			           (loggerLocal, toCall.makeRef(), Arrays.asList(loggedValue)));
		G.v().out.println("ZY newInvokeStmt to insert is: ++++++++++++++++++++++++++ "+newInvokeStmt+"++++++++++++++++++++++");
			 return newInvokeStmt;
	}
	
	@SuppressWarnings("unused")
	private boolean isTypeCompatible(Type typeValue, Type localType){
		if((localType.toString().equals(typeValue.toString())) || ( typeValue instanceof RefLikeType && localType instanceof RefLikeType) )
			return true;
		else
			return false;
	}
	
	@SuppressWarnings("unused")
	private void analyzeExp(
			Value exp,//x>y
//			ArrayList<String> params, 
			ArrayList<Value> values, 
			ArrayList<String> operator, 
			ArrayList<Value> cons, 
			ArrayList<Value> variable) {
//		G.v().out.println("exp:********"+exp.toString()+"*************");

		if(exp instanceof JLengthExpr){
			G.v().out.println("JLengthExpr exp********"+exp.toString()+"*************");
			values.add(exp);
//			isInvoke = true;
		}
		else if(exp instanceof InstanceInvokeExpr){
			G.v().out.println("InvokeExpr:********"+exp.toString()+"*************");
			values.add(exp);
//			isInvoke = true;
		}else if(exp instanceof JStaticInvokeExpr){
			G.v().out.println("JStaticInvokeExpr:********"+exp.toString()+"*************");
			values.add(exp);
//			isInvoke = true;
		}
		else if(exp instanceof BinopExpr){//add add div mul or sub xor rem shl shr 
			//G.v().out.println("BinopExpr:********"+exp.toString()+"*************");
			analyzeExp(((BinopExpr)exp).getOp1(), values, operator, cons, variable);
			analyzeExp(((BinopExpr)exp).getOp2(), values, operator, cons, variable);	
			operator.add(((BinopExpr)exp).getSymbol());
		}
		else if(exp instanceof InstanceOfExpr){
			G.v().out.println("InstanceOfExpr exp********"+exp.toString()+"*************");
		}
		else if(exp instanceof CastExpr){
			/**
			G.v().out.println("CastExpr exp********"+exp.toString()+"*************");
			analyzeExp(((BinopExpr)exp).getOp1(), values, operator, cons, variable);
			G.v().out.println("CastExpr exp********finish*************");
			*/
			values.add(exp);
//			operator.add(((CastExpr)exp).get);
		}else{
			if(exp instanceof Constant){
				G.v().out.println("Constant exp********"+exp.toString()+"*************");
				values.add(exp);
				cons.add(exp);
			}else if(exp instanceof Local){
				G.v().out.println("Local exp********"+exp.toString()+"*************");
				values.add(exp);
				// variable.add(((Local)exp));
			}else if(exp instanceof ArrayRef){
				G.v().out.println("ArrayRef:********"+exp.toString()+"*************");
				values.add(exp);
//				isInvoke = true;
			}else if (exp instanceof StaticFieldRef) {
				G.v().out.println("StaticFieldRef:********"+exp.getClass()+"*************");
				values.add(exp);
			}
			else if (exp instanceof JInstanceFieldRef) {
				values.add(exp);
				G.v().out.println("JInstanceFieldRef:********"+exp.getClass()+"*************");
			}
			else {
				G.v().out.println("other type:********"+exp.getClass()+"*************");
				values.add(exp);
				// isInvoke = true;
			}
		}		
	}
	
	@SuppressWarnings("unused")
	private int TypeIndex(Value tValue){
		int typeIndex = -1;
		String typeStr = tValue.getType().toString();
		//G.v().out.println("<<<<<<ZYSTBLE>>>>>> in Function TypeIndex typeStr:********"+typeStr+"*************");
		if(typeStr.equals("int") || typeStr.equals("short")||typeStr.equals("java.lang.Integer")){
			typeIndex = 1;
		}else if(typeStr.equals("double")){
			typeIndex = 2;
		}else if(typeStr.equals("float")){
			typeIndex = 3;
		}else if(typeStr.equals("char")){
			typeIndex = 4;
		}else if(typeStr.equals("long")){
			typeIndex = 5;
		}else if(typeStr.equals("byte")){
			typeIndex = 6;
		}else if(typeStr.equals("boolean")){    // Add by ZyStBle 6.5
			typeIndex = 1;
		}else{ //TODO: contains type object , boolean , short
			G.v().out.println("<<<<<<ZYSTBLE>>>>>>other Value.getType():"+tValue.getType());
			typeIndex = 1;  //for hashcode
		}
		return typeIndex;
	}
	
	@SuppressWarnings("unused")
	private int TypeForSpecialCallerPost(Value tValue){
		int typeIndex = -1;
		String typeStr = tValue.getType().toString();
		//G.v().out.println("<<<<<<ZYSTBLE>>>>>> in Function TypeIndex typeStr:********"+typeStr+"*************");
		if(typeStr.equals("int") || typeStr.equals("short")||typeStr.equals("java.lang.Integer")){
			//typeIndex = 1;
		}else if(typeStr.equals("double")){
			//typeIndex = 2;
		}else if(typeStr.equals("float")){
			//typeIndex = 3;
		}else if(typeStr.equals("char")){
			//typeIndex = 4;
		}else if(typeStr.equals("long")){
			//typeIndex = 5;
		}else if(typeStr.equals("byte")){
			//typeIndex = 6;
		}else if(typeStr.equals("boolean")){    // Add by ZyStBle 6.5
			//typeIndex = 1;
		}else{ //TODO: contains type object , boolean , short
			typeIndex = 10;  //for hashcode
		}
		return typeIndex;
	}
	
	private ArrayList<Value> typeToList(int typeIndex){
		if(typeIndex == 1)
			return condValsInt;
		else if(typeIndex == 2)
			return condValsDouble;
		else if(typeIndex == 3)
			return condValsFloat;
		else if(typeIndex == 4)
			return condValsChar;
		else if(typeIndex == 5)
			return condValsLong;
		else if(typeIndex == 6)
			return condValsByte;
		else //TODO: contains type object , boolean , short
			G.v().out.println("other condvalstype");
			return condValsOtherType;
	}
    
	private void insertDeletValueStmt(
			Body aBody,
			Local sgxObjLocal,
			PatchingChain<Unit> units, 
			Unit currStmt,
			Local getUUIDLocal){	

        SootMethod toCall = Scene.v().getMethod
				("<invoker.sgx_invoker: boolean deleteValueInEnclave(java.lang.String)>");

		VirtualInvokeExpr initValueExpr = Jimple.v().newVirtualInvokeExpr
				(sgxObjLocal, toCall.makeRef(), 
						Arrays.asList(getUUIDLocal));
		Stmt newInitInvokeStmt = Jimple.v().newInvokeStmt(initValueExpr);
		G.v().out.println("ValueDeleteStmt is:#"+newInitInvokeStmt+"#--");
		units.insertBefore(newInitInvokeStmt, currStmt);
//		units.
	}
	
	@SuppressWarnings("unused")
	private void insertValueInitStmt(
			Body aBody,
			Local sgxObjLocal,
			PatchingChain<Unit> units, 
			Unit currStmt,
			Local invokeUUID,
			Local getUUID,
			List<Value> preCallee){		

//        LocalGenerator localGenerator = new LocalGenerator(aBody);
//        Local local1 = localGenerator.generateLocal(soot.ArrayType.v(IntType.v(), 1));
//        NewArrayExpr newArrayExpr = Jimple.v().newNewArrayExpr(IntType.v(), IntConstant.v(condValsTypeArray.size()));
//        AssignStmt assignStmt2 = Jimple.v().newAssignStmt(local1, newArrayExpr);    
//        G.v().out.println("ZYSTBLE assignStmt2 1222:"+assignStmt2.toString());
//        units.insertBefore(assignStmt2, currStmt);
//        
//        G.v().out.println("ZYSTBLE condValsTypeArray:"+condValsTypeArray.toString());
//        int i=0;
//        for(Value num:condValsTypeArray){
//            ArrayRef arrayRef = Jimple.v().newArrayRef(local1, IntConstant.v(i++));
//            G.v().out.println("ZYSTBLE 8.31 arrayRef:"+arrayRef.toString());
//            AssignStmt assignStmt = Jimple.v().newAssignStmt(arrayRef, num);    //赋值
//            G.v().out.println("ZYSTBLE 8.31 assignStmt:"+assignStmt);
//    		units.insertBefore(assignStmt, currStmt);
//        }
       
        
        
        G.v().out.println("ZYSTBLE 8.31:");
        
        SootMethod toCall1 = Scene.v().getMethod
				("<invoker.sgx_invoker: java.lang.String getUUID()>");
        
        G.v().out.println("ZYSTBLE 9.1");
        VirtualInvokeExpr getuuidExpr = Jimple.v().newVirtualInvokeExpr
				(sgxObjLocal, toCall1.makeRef());
        AssignStmt asStmt = Jimple.v().newAssignStmt(getUUID, getuuidExpr);
        units.insertBefore(asStmt, currStmt);
        
        SootMethod toCall = Scene.v().getMethod
				("<invoker.sgx_invoker: boolean initValueInEnclave(java.lang.String,java.lang.String)>");

		VirtualInvokeExpr initValueExpr = Jimple.v().newVirtualInvokeExpr
				(sgxObjLocal, toCall.makeRef(), 
						Arrays.asList(invokeUUID==null?null:invokeUUID,getUUID));
		Stmt newInitInvokeStmt = Jimple.v().newInvokeStmt(initValueExpr);
		G.v().out.println("ValueInitStmt is:#"+newInitInvokeStmt+"#--");
		units.insertBefore(newInitInvokeStmt, currStmt);
		int IdNumber = 99;
		for(Value v:preCallee){
			G.v().out.println("[zystble20201104]:"+currStmt);
			insertCalleeUpdateStmt(aBody, sgxObjLocal, units, null, v, IdNumber--, newInitInvokeStmt, getUUID);
		}
	}

	@SuppressWarnings("unused")
	private void insertSgxInitStmt(
			Body aBody,
			Local sgxObjLocal, //sgxObjLocal
			PatchingChain<Unit> units,
			Unit currStmt, //first stmt
			String className) { //Object NewArrayExpr)
//		String funcNameString = aBody.getMethod().toString();
//		G.v().out.println("funcNameString: "+funcNameString+";");
//		int argsString = aBody.getMethod().equivHashCode();
//		G.v().out.println("argsString: "+argsString+";");
//		G.v().out.println("getNumberedSubSignature: "+aBody.getMethod().getNumberedSubSignature()+";");
//		G.v().out.println("getTags: "+aBody.getTags());
//		G.v().out.println("hashCode: "+aBody.hashCode());
//		G.v().out.println("getParameterCount: "+aBody.getMethod().getParameterCount());
//		StringBuilder methodID = new StringBuilder();
//		methodID.append(funcNameString);
//		for(int i=0; i<aBody.getMethod().getParameterCount(); i++){
//			G.v().out.println("ParameterLocal-"+i+": "+aBody.getParameterLocal(i).toString());
//			methodID.append("_");
//			methodID.append(aBody.getParameterLocal(i));
//		}
//		G.v().out.println("methodID: "+methodID);
		

        ///"sgxInvoker = new invoker.sgx_invoker;"
		soot.jimple.NewExpr sootNew = soot.jimple.Jimple.v().newNewExpr(RefType.v(className));
	    soot.jimple.AssignStmt stmt = soot.jimple.Jimple.v().newAssignStmt(sgxObjLocal, sootNew);
		units.insertBefore(stmt, currStmt);
		
        //"specialinvoke sgxInvoker.<invoker.sgx_invoker: void <init>()>();"
		SpecialInvokeExpr newTrans = Jimple.v().newSpecialInvokeExpr(sgxObjLocal,
				Scene.v().getMethod("<invoker.sgx_invoker: void <init>()>").makeRef(),
				Arrays.asList());
		soot.jimple.Stmt invokeStmt = soot.jimple.Jimple.v().newInvokeStmt(newTrans);
		units.insertBefore(invokeStmt, currStmt);

        //"virtualinvoke sgxInvoker.<invoker.sgx_invoker: boolean initenclave()>();"
		SootMethod toCall = Scene.v().getMethod
			      ("<invoker.sgx_invoker: boolean initenclave()>");
		Stmt newInvokeStmt = Jimple.v().newInvokeStmt(
				Jimple.v().newVirtualInvokeExpr
		           (sgxObjLocal, toCall.makeRef(), Arrays.asList()));//IntConstant.v(1)
		units.insertBefore(newInvokeStmt, currStmt);
	}

	private AssignStmt initAssignStmt(Local l){
		Type t = l.getType();
		soot.jimple.AssignStmt stmt = null;
		if(t instanceof RefLikeType){
			stmt = soot.jimple.Jimple.v().newAssignStmt(l, NullConstant.v());
		}
		else if(t instanceof IntType){
			stmt = soot.jimple.Jimple.v().newAssignStmt(l, IntConstant.v(0));
		}
		else if(t instanceof DoubleType){
			stmt = soot.jimple.Jimple.v().newAssignStmt(l, DoubleConstant.v(0));
		}
		else if(t instanceof FloatType){
			stmt = soot.jimple.Jimple.v().newAssignStmt(l, FloatConstant.v(0));
		}
		else if(t instanceof soot.LongType){
			stmt = soot.jimple.Jimple.v().newAssignStmt(l, LongConstant.v(0));
		}
		else if(t instanceof BooleanType){
			stmt = soot.jimple.Jimple.v().newAssignStmt(l, IntConstant.v(0));
		}
		else if(t instanceof ShortType){
			stmt = soot.jimple.Jimple.v().newAssignStmt(l, IntConstant.v(0));
		}
		else if(t instanceof CharType){
			stmt = soot.jimple.Jimple.v().newAssignStmt(l, IntConstant.v(0));
		}
		else if(t instanceof ByteType){
			stmt = soot.jimple.Jimple.v().newAssignStmt(l, IntConstant.v(0));
		}
		return stmt;
	}
	
private void initidentyLocal(
			List<Local> localList,
			PatchingChain<Unit> units, 
			Unit currStmt, 
			HashSet<Value> identifiedLocal){
		
		soot.jimple.AssignStmt stmt = null;
		for(Local l: localList){
//			G.v().out.println("++++++Local is:++++++++++"+l.toString());
			if(identifiedLocal.contains(l)){			
				G.v().out.println(l.toString()+": has been inited in original javafile!");
					continue;
			}
			stmt = initAssignStmt(l);
			G.v().out.println(l.toString()+": init stmt will be inserted into jimplefile!");
			units.insertBefore(stmt, currStmt);
		}
	}
	
	@SuppressWarnings("unused")
	private void insertCloseEnclaveStmt(
			Local sgxObjLocal, //sgxObjLocal
			PatchingChain<Unit> units,
			Unit currStmt, //first stmt
			String className) {

		SootMethod toCall = Scene.v().getMethod
			      ("<invoker.sgx_invoker: boolean closeenclave()>");
		Stmt newInvokeStmt = Jimple.v().newInvokeStmt(
				Jimple.v().newVirtualInvokeExpr
		           (sgxObjLocal, toCall.makeRef(), Arrays.asList()));
		units.insertBefore(newInvokeStmt, currStmt);
	}
	
	@SuppressWarnings("unused")
	private void insertCallerUpdateStmt(
			Body aBody,
			Local sgxObjLocal,
			PatchingChain<Unit> units,
			List<Local> localArray,
			Value currValue,
			Unit currProStmt,
			Local getUUIDLocal,
			int Number) {
    	
//    	SootMethod toCall = Scene.v().getMethod
//			      ("<invoker.sgx_invoker: void clear()>");
//		Stmt newInvokeStmt = Jimple.v().newInvokeStmt(
//				Jimple.v().newVirtualInvokeExpr
//		           (sgxObjLocal, toCall.makeRef(), Arrays.asList()));
//		
//		units.insertBefore(newInvokeStmt, currProStmt);
//
//		toCall = Scene.v().getMethod("<invoker.sgx_invoker: void setCounter(long)>");
//		newInvokeStmt = Jimple.v().newInvokeStmt(
//				Jimple.v().newVirtualInvokeExpr
//		           (sgxObjLocal, toCall.makeRef(), Arrays.asList(LongConstant.v(counter))));
//		units.insertBefore(newInvokeStmt, currProStmt);
		SootMethod toCall = Scene.v().getMethod ("<invoker.sgx_invoker: void updateValueInEnclave(java.lang.String,long)>");
		
		Stmt newInvokeStmt = Jimple.v().newInvokeStmt(
				Jimple.v().newVirtualInvokeExpr
		           (sgxObjLocal, toCall.makeRef(), Arrays.asList(getUUIDLocal,LongConstant.v(counter)))); 
		units.insertBefore(newInvokeStmt, currProStmt);
		if (currValue instanceof Constant) {
			G.v().out.println("444");   
			int leftIndex = TypeIndex(currValue);
			indexwriter(""+leftIndex);
			indexwriter(((Value)(currValue)).getType().toString()+"_"+currValue);
			indexwriter("-1");
			indexwriter("-1");
			indexwriter(Integer.toString(leftIndex*100+Number));
		}else{
			int leftIndex = TypeIndex(currValue);
			int left_index = typeToList(leftIndex).indexOf(currValue);
			indexwriter(""+leftIndex);
			indexwriter(Integer.toString(leftIndex*100+left_index));
			indexwriter("-1");
			indexwriter("-1");
			indexwriter(Integer.toString(leftIndex*100+Number));
		}
		
		counter++;
	}
	
	@SuppressWarnings("unused")
	private void insertCalleeUpdateStmt(
			Body aBody,
			Local sgxObjLocal,
			PatchingChain<Unit> units,
			List<Local> localArray,
			Value currValue,
			int Number,
			Unit currProStmt,
			Local getUUIDLocal) {
    	
		SootMethod toCall = Scene.v().getMethod ("<invoker.sgx_invoker: void updateValueInEnclave(java.lang.String,long)>");
		Stmt newInvokeStmt = Jimple.v().newInvokeStmt(
				Jimple.v().newVirtualInvokeExpr
		           (sgxObjLocal, toCall.makeRef(), Arrays.asList(getUUIDLocal,LongConstant.v(counter)))); 
		units.insertAfter(newInvokeStmt, currProStmt);
		
		int leftIndex = TypeIndex(currValue);
		int left_index = typeToList(leftIndex).indexOf(currValue);
		indexwriter(""+leftIndex);
		indexwriter(Integer.toString(leftIndex*100+Number));
		indexwriter("-1");
		indexwriter("-1");
		indexwriter(Integer.toString(leftIndex*100+left_index));
		counter++;
	}
	
	@SuppressWarnings("unused")
	private void insertCallerPostUpdateStmt(
			Body aBody,
			Local sgxObjLocal,
			PatchingChain<Unit> units,
			List<Local> localArray,
			Value currValue,
			Unit currProStmt,
			Local getUUIDLocal) {
		SootMethod toCall = Scene.v().getMethod ("<invoker.sgx_invoker: void updateValueInEnclave(java.lang.String,long)>");
		Stmt newInvokeStmt = Jimple.v().newInvokeStmt(
				Jimple.v().newVirtualInvokeExpr
		           (sgxObjLocal, toCall.makeRef(), Arrays.asList(getUUIDLocal,LongConstant.v(counter)))); 
		units.insertAfter(newInvokeStmt, currProStmt);
		
		if (currValue instanceof Constant) {
			G.v().out.println("444");   
			int leftIndex = TypeIndex(currValue);
			indexwriter(""+leftIndex);
			indexwriter(Integer.toString(leftIndex*100+50));
			indexwriter("-1");
			indexwriter("-1");
			indexwriter(((Value)(currValue)).getType().toString()+"_"+currValue);
			G.v().out.println("555");   
		}else{
			int leftIndex = TypeIndex(currValue);
			int left_index = typeToList(leftIndex).indexOf(currValue);
			indexwriter(""+leftIndex);
			indexwriter(Integer.toString(leftIndex*100+50));
			indexwriter("-1");
			indexwriter("-1");
			indexwriter(Integer.toString(leftIndex*100+left_index));
		}
		G.v().out.println("666");   
		counter++;
	}
	
	@SuppressWarnings("unused")
	private void insertCalleePostUpdateStmt(
			Body aBody,
			Local sgxObjLocal,
			PatchingChain<Unit> units,
			List<Local> localArray,
			Value currValue,
			Unit currProStmt,
			Local getUUIDLocal) {
    	SootMethod toCall = null;
    	Stmt newInvokeStmt = null;
		
		if (currValue instanceof Constant) {
			G.v().out.println("444");   
			int leftIndex = TypeIndex(currValue);
			indexwriter(""+leftIndex);
			indexwriter(((Value)(currValue)).getType().toString()+"_"+currValue);
			indexwriter("-1");
			indexwriter("-1");
			indexwriter(Integer.toString(leftIndex*100+50));
			G.v().out.println("555");   
		}else{
			int leftIndex = TypeIndex(currValue);
			int left_index = typeToList(leftIndex).indexOf(currValue);
			if(left_index == -1){
				newInvokeStmt = prepareInsertStmt(currValue, sgxObjLocal, "invoker.sgx_invoker");//只add类型相同的变量
				units.insertBefore(newInvokeStmt, currProStmt);
				indexwriter(""+leftIndex);
				indexwriter(Integer.toString(0));
				indexwriter("-1");
				indexwriter("-1");
				indexwriter(Integer.toString(leftIndex*100+50));
			}else{
				indexwriter(""+leftIndex);
				indexwriter(Integer.toString(leftIndex*100+left_index));
				indexwriter("-1");
				indexwriter("-1");
				indexwriter(Integer.toString(leftIndex*100+50));
			}
		}
		toCall = Scene.v().getMethod ("<invoker.sgx_invoker: void updateValueInEnclave(java.lang.String,long)>");
		newInvokeStmt = Jimple.v().newInvokeStmt(
				Jimple.v().newVirtualInvokeExpr
		           (sgxObjLocal, toCall.makeRef(), Arrays.asList(getUUIDLocal,LongConstant.v(counter)))); 
		units.insertBefore(newInvokeStmt, currProStmt);
		counter++;
	}
}

