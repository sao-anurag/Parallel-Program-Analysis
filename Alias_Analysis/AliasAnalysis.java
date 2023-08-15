package submit_a1;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;

import soot.Body;
import soot.BodyTransformer;
import soot.RefLikeType;
import soot.RefType;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.DefinitionStmt;
import soot.jimple.InvokeStmt;
import soot.jimple.ParameterRef;
import soot.jimple.Stmt;
import soot.jimple.ThisRef;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JIdentityStmt;
import soot.jimple.internal.JInstanceFieldRef;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JNewExpr;
import soot.jimple.internal.JVirtualInvokeExpr;
import soot.jimple.internal.JimpleLocal;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.UnitGraph;

public class AliasAnalysis extends BodyTransformer{

	@Override
	synchronized protected void internalTransform(Body arg0, String arg1, Map<String, String> arg2) {
		/*
		 * Implement your alias analysis here. A1.answers should include the Yes/No answers for 
		 * the queries
		 */
		
		HashMap<String,JimpleLocal> Jlnametoobj = new HashMap<String,JimpleLocal>();
		
		HashMap<JimpleLocal,LinkedHashSet<Integer>> RhoMap;
		
		HashMap<Integer,HashMap<SootField,LinkedHashSet<Integer>>> SigmaMap;
		
		HashMap<Unit,HashMap<JimpleLocal,LinkedHashSet<Integer>>> Rhoout = new HashMap<Unit,HashMap<JimpleLocal,LinkedHashSet<Integer>>>();
		
		HashMap<Unit,HashMap<Integer,HashMap<SootField,LinkedHashSet<Integer>>>> Sigmaout = new HashMap<Unit,HashMap<Integer,HashMap<SootField,LinkedHashSet<Integer>>>>();
		
		HashMap<Unit,Integer> ObjDecMap = new HashMap<Unit,Integer>();
		
		Integer currObjNum=1;
		
		LinkedHashSet<Unit> worklist = new LinkedHashSet<Unit>();
		
		UnitGraph g = new BriefUnitGraph(arg0);

		for(Unit u:g)
		{
			worklist.add(u);
			RhoMap = new HashMap<JimpleLocal,LinkedHashSet<Integer>>();
			Rhoout.put(u, RhoMap);
			SigmaMap = new HashMap<Integer,HashMap<SootField,LinkedHashSet<Integer>>>();
			Sigmaout.put(u, SigmaMap);
		}
		
		//int itnum=0;
		
		//System.out.println("Initialization Over");
		
		while(!worklist.isEmpty())
		{
			Iterator<Unit> it=worklist.iterator();
			Unit u=it.next();
			it.remove();
			
			//System.out.println(u);
			
			List<Unit> pdc=g.getPredsOf(u);
			
			HashMap<JimpleLocal,LinkedHashSet<Integer>> currRhoMap = new HashMap<JimpleLocal,LinkedHashSet<Integer>>();
			
			HashMap<Integer,HashMap<SootField,LinkedHashSet<Integer>>> currSigmaMap = new HashMap<Integer,HashMap<SootField,LinkedHashSet<Integer>>>();
			
			HashMap<JimpleLocal,LinkedHashSet<Integer>> pRhoMap;
			HashMap<Integer,HashMap<SootField,LinkedHashSet<Integer>>> pSigmaMap;
			
			for(Unit p:pdc)
			{
				pRhoMap = Rhoout.get(p);
				pSigmaMap = Sigmaout.get(p);
				
				for(Map.Entry<JimpleLocal,LinkedHashSet<Integer>> e: pRhoMap.entrySet())
				{
					if(!currRhoMap.containsKey(e.getKey()))
					{
						currRhoMap.put(e.getKey(),new LinkedHashSet<Integer>());	
					}
					
					for(Integer val:e.getValue())
					{
						currRhoMap.get(e.getKey()).add(val);
					}
				}
				
				for(Map.Entry<Integer,HashMap<SootField,LinkedHashSet<Integer>>> e: pSigmaMap.entrySet())
				{
					if(!currSigmaMap.containsKey(e.getKey()))
					{
						currSigmaMap.put(e.getKey(),new HashMap<SootField,LinkedHashSet<Integer>>());	
					}
					
					for(Map.Entry<SootField,LinkedHashSet<Integer>> emap: e.getValue().entrySet())
					{
						if(!currSigmaMap.get(e.getKey()).containsKey(emap.getKey()))
						{
							currSigmaMap.get(e.getKey()).put(emap.getKey(), new LinkedHashSet<Integer>());
						}
						
						
						for(Integer val:emap.getValue())
						{
							currSigmaMap.get(e.getKey()).get(emap.getKey()).add(val);
						}
					}
				}
			}
			
			//Make changes to curr RhoMap and SigmaMap as per statement type and details
			
			if(u instanceof JAssignStmt)
			{
				JAssignStmt st = (JAssignStmt) u;
				
				if(st.getRightOp() instanceof JNewExpr)
				{
					if(!ObjDecMap.containsKey(u))
					{
						ObjDecMap.put(u, currObjNum);
						currObjNum+=1;
					}
					
					if(st.getLeftOp() instanceof JimpleLocal)
					{
						JimpleLocal jl = (JimpleLocal) st.getLeftOp();
						Jlnametoobj.put(jl.getName(), jl);
						
						if(currRhoMap.containsKey(st.getLeftOp()))
						{
							currRhoMap.get(st.getLeftOp()).clear();
						}
						else
						{
							currRhoMap.put((JimpleLocal) st.getLeftOp(),new LinkedHashSet<Integer>());
						}
						
						currRhoMap.get(st.getLeftOp()).add(ObjDecMap.get(u));
					}
				}
				
				else if(st.getRightOp() instanceof JimpleLocal)
				{
					
					JimpleLocal jlr = (JimpleLocal) st.getRightOp();
					Jlnametoobj.put(jlr.getName(), jlr);
					
					if(!currRhoMap.containsKey(st.getRightOp()))
					{
						currRhoMap.put((JimpleLocal) st.getRightOp(),new LinkedHashSet<Integer>());
					}
					
					if(st.getLeftOp() instanceof JimpleLocal)
					{
						JimpleLocal jl = (JimpleLocal) st.getLeftOp();
						Jlnametoobj.put(jl.getName(), jl);
						
						if(currRhoMap.containsKey(st.getLeftOp()))
						{
							currRhoMap.get(st.getLeftOp()).clear();
						}
						else
						{
							currRhoMap.put((JimpleLocal) st.getLeftOp(),new LinkedHashSet<Integer>());
						}
						
						for(Integer val:currRhoMap.get(st.getRightOp()))
						{
							currRhoMap.get(st.getLeftOp()).add(val);
						}
					}
					
					else if(st.getLeftOp() instanceof JInstanceFieldRef)
					{
						JInstanceFieldRef instf = (JInstanceFieldRef) st.getLeftOp();
						JimpleLocal instf_base = (JimpleLocal) instf.getBase();
						SootField instf_field = (SootField) instf.getField();
						
						Jlnametoobj.put(instf_base.getName(), instf_base);
						
						if(currRhoMap.get(instf_base).size()==1) //Strong Update
						{
							//System.out.println("Doing Strong Update");
							Iterator<Integer> objit=currRhoMap.get(instf_base).iterator();
							
							//System.out.println("Step 1");
							Integer objid=objit.next();
							//System.out.println("Step 2");
							if(!currSigmaMap.containsKey(objid))
							{
								currSigmaMap.put(objid, new HashMap<SootField,LinkedHashSet<Integer>>());
								currSigmaMap.get(objid).put(instf_field, new LinkedHashSet<Integer>());
							}
							else if(!currSigmaMap.get(objid).containsKey(instf_field))
							{
								currSigmaMap.get(objid).put(instf_field, new LinkedHashSet<Integer>());
							}
							currSigmaMap.get(objid).get(instf_field).clear();
							//System.out.println("Step 3");
							for(Integer val:currRhoMap.get(st.getRightOp()))
							{
								currSigmaMap.get(objid).get(instf_field).add(val);
							}
						}
						
						else //Weak Update
						{
							//System.out.println("Doing Weak Update");
							for(Integer objid:currRhoMap.get(instf_base))
							{
								if(!currSigmaMap.containsKey(objid))
								{
									currSigmaMap.put(objid, new HashMap<SootField,LinkedHashSet<Integer>>());
									currSigmaMap.get(objid).put(instf_field, new LinkedHashSet<Integer>());
								}
								else if(!currSigmaMap.get(objid).containsKey(instf_field))
								{
									currSigmaMap.get(objid).put(instf_field, new LinkedHashSet<Integer>());
								}
								
								for(Integer val:currRhoMap.get(st.getRightOp()))
								{
									currSigmaMap.get(objid).get(instf_field).add(val);
								}
							}
						}
						
						//System.out.println("Update Finished");
					}
				}
				
				else if(st.getRightOp() instanceof JInstanceFieldRef)
				{
					JInstanceFieldRef instf = (JInstanceFieldRef) st.getRightOp();
					JimpleLocal instf_base = (JimpleLocal) instf.getBase();
					SootField instf_field = (SootField) instf.getField();
					
					Jlnametoobj.put(instf_base.getName(), instf_base);
					
					if(st.getLeftOp() instanceof JimpleLocal)
					{
						JimpleLocal jl = (JimpleLocal) st.getLeftOp();
						Jlnametoobj.put(jl.getName(), jl);
						
						if(currRhoMap.containsKey(st.getLeftOp()))
						{
							currRhoMap.get(st.getLeftOp()).clear();
						}
						else
						{
							currRhoMap.put((JimpleLocal) st.getLeftOp(),new LinkedHashSet<Integer>());
						}
						
						for(Integer objs:currRhoMap.get(instf_base))
						{
							if(!currSigmaMap.containsKey(objs))
							{
								currSigmaMap.put(objs, new HashMap<SootField,LinkedHashSet<Integer>>());
								currSigmaMap.get(objs).put(instf_field, new LinkedHashSet<Integer>());
							}
							else if(!currSigmaMap.get(objs).containsKey(instf_field))
							{
								currSigmaMap.get(objs).put(instf_field, new LinkedHashSet<Integer>());
							}
							
							for(Integer sig_objs:currSigmaMap.get(objs).get(instf_field))
							{
								currRhoMap.get(st.getLeftOp()).add(sig_objs);
							}
						}
					}
				}
				
				else if(st.getRightOp() instanceof JVirtualInvokeExpr)
				{
					JVirtualInvokeExpr invexp = (JVirtualInvokeExpr) st.getRightOp();
					JimpleLocal invexp_base = (JimpleLocal) invexp.getBase();
					
					//System.out.println("Step 1");
					
					for(Integer objs:currRhoMap.get(invexp_base))
					{
						if(!currSigmaMap.containsKey(objs))
						{
							currSigmaMap.put(objs, new HashMap<SootField,LinkedHashSet<Integer>>());
						}
						
						for(Map.Entry<SootField,LinkedHashSet<Integer>> emap: currSigmaMap.get(objs).entrySet())
						{							
							emap.getValue().clear();
							emap.getValue().add(0);
						}
					}
					
					//System.out.println("Step 2");
					
					for(Value v:invexp.getArgs())
					{
						JimpleLocal invexp_arg = (JimpleLocal) v;
						
						for(Integer objs:currRhoMap.get(invexp_arg))
						{
							if(!currSigmaMap.containsKey(objs))
							{
								currSigmaMap.put(objs, new HashMap<SootField,LinkedHashSet<Integer>>());
							}
							
							for(Map.Entry<SootField,LinkedHashSet<Integer>> emap: currSigmaMap.get(objs).entrySet())
							{							
								emap.getValue().clear();
								emap.getValue().add(0);
							}
						}
					}
					
					//System.out.println("Step 3");
					
					JimpleLocal lhs = (JimpleLocal) st.getLeftOp();
					
					Jlnametoobj.put(lhs.getName(), lhs);
					
					if(!currRhoMap.containsKey(lhs))
					{
						currRhoMap.put(lhs,new LinkedHashSet<Integer>());
					}
					
					currRhoMap.get(lhs).clear();
					currRhoMap.get(lhs).add(0);
				}
			}
			
			else if(u instanceof JIdentityStmt)
			{
				JIdentityStmt st = (JIdentityStmt) u;
				
				if(st.getRightOp() instanceof ParameterRef)
				{
					if(st.getLeftOp() instanceof JimpleLocal)
					{
						JimpleLocal lhs = (JimpleLocal) st.getLeftOp();
						
						Jlnametoobj.put(lhs.getName(), lhs);
						
						if(!currRhoMap.containsKey(lhs))
						{
							currRhoMap.put(lhs,new LinkedHashSet<Integer>());
						}
						
						currRhoMap.get(lhs).add(0);
						//System.out.println("Argument Initialized");
					}
				}
				
				if(st.getRightOp() instanceof ThisRef)
				{
					if(st.getLeftOp() instanceof JimpleLocal)
					{
						JimpleLocal lhs = (JimpleLocal) st.getLeftOp();
						
						Jlnametoobj.put(lhs.getName(), lhs);
						
						if(!currRhoMap.containsKey(lhs))
						{
							currRhoMap.put(lhs,new LinkedHashSet<Integer>());
						}
						
						currRhoMap.get(lhs).add(0);
						//System.out.println("This Initialized");
					}
				}
			}
			
			//If curr RhoMap equals Rhoout(u) and curr SigmaMap equals Sigmaout(u) continue to next iteration
			//Else add  successors of u to worklist
			
			if(!currRhoMap.equals(Rhoout.get(u)))
			{
				Rhoout.put(u,currRhoMap);
				if(!currSigmaMap.equals(Sigmaout.get(u)))
				{
					Sigmaout.put(u,currSigmaMap);
				}
				
				List<Unit> scs=g.getSuccsOf(u);
				for(Unit s:scs)
				{
					worklist.add(s);
				}
			}
			else if(!currSigmaMap.equals(Sigmaout.get(u)))
			{
				Sigmaout.put(u,currSigmaMap);
				
				List<Unit> scs=g.getSuccsOf(u);
				for(Unit s:scs)
				{
					worklist.add(s);
				}
			}
			
			//System.out.println(itnum);
			//itnum+=1;
		}
		
		//Merge Rho and Sigma of Tails of Unitgraph
		
		List<Unit> tls=g.getTails();
		
		HashMap<JimpleLocal,LinkedHashSet<Integer>> finRhoMap = new HashMap<JimpleLocal,LinkedHashSet<Integer>>();
		
		HashMap<Integer,HashMap<SootField,LinkedHashSet<Integer>>> finSigmaMap = new HashMap<Integer,HashMap<SootField,LinkedHashSet<Integer>>>();;
		
		HashMap<JimpleLocal,LinkedHashSet<Integer>> pRhoMap;
		HashMap<Integer,HashMap<SootField,LinkedHashSet<Integer>>> pSigmaMap;
		
		for(Unit p:tls)
		{
			pRhoMap = Rhoout.get(p);
			pSigmaMap = Sigmaout.get(p);
			
			for(Map.Entry<JimpleLocal,LinkedHashSet<Integer>> e: pRhoMap.entrySet())
			{
				if(!finRhoMap.containsKey(e.getKey()))
				{
					finRhoMap.put(e.getKey(),new LinkedHashSet<Integer>());	
				}
				
				for(Integer val:e.getValue())
				{
					finRhoMap.get(e.getKey()).add(val);
				}
			}
			
			for(Map.Entry<Integer,HashMap<SootField,LinkedHashSet<Integer>>> e: pSigmaMap.entrySet())
			{
				if(!finSigmaMap.containsKey(e.getKey()))
				{
					finSigmaMap.put(e.getKey(),new HashMap<SootField,LinkedHashSet<Integer>>());	
				}
				
				for(Map.Entry<SootField,LinkedHashSet<Integer>> emap: e.getValue().entrySet())
				{
					if(!finSigmaMap.get(e.getKey()).containsKey(emap.getKey()))
					{
						finSigmaMap.get(e.getKey()).put(emap.getKey(), new LinkedHashSet<Integer>());
					}
					
					
					for(Integer val:emap.getValue())
					{
						finSigmaMap.get(e.getKey()).get(emap.getKey()).add(val);
					}
				}
			}
		}
		
		
		
		//Resolve and answer the queries

		SootMethod currMethod = arg0.getMethod();
		SootClass currClass = currMethod.getDeclaringClass();
		
		for(int i=0; i<A1.queryList.size();i++)
		{
			//System.out.println(A1.queryList.get(i).getMethodName() + " " + currMethod.getName() + " " + A1.queryList.get(i).getClassName() + " " + currClass.getName());
			if(A1.queryList.get(i).getMethodName().equals(currMethod.getName()) && A1.queryList.get(i).getClassName().equals(currClass.getName()))
			{
				String lvar = A1.queryList.get(i).getLeftVar();
				String rvar = A1.queryList.get(i).getRightVar();
				
				JimpleLocal lobj = Jlnametoobj.get(lvar);
				JimpleLocal robj = Jlnametoobj.get(rvar);
				
				if(finRhoMap.get(lobj).contains(0) || finRhoMap.get(robj).contains(0))
				{
					A1.answers[i]="Yes";
					//System.out.println("Setting Query: "+i+" Yes");
				}
				else
				{
					boolean flag=false;
					
					for(Integer objnum:finRhoMap.get(lobj))
					{
						if(finRhoMap.get(robj).contains(objnum))
						{
							flag=true;
							break;
						}
					}
					
					if(flag)
					{
						A1.answers[i]="Yes";
						//System.out.println("Setting Query: "+i+" Yes");
					}
					else
					{
						A1.answers[i]="No";
						//System.out.println("Setting Query: "+i+" No");
					}
				}
			}
		}
	
	}
	
}
