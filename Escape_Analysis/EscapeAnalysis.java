package submit_a2;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;

import soot.Body;
import soot.BodyTransformer;
import soot.RefLikeType;
import soot.RefType;
import soot.Scene;
import soot.SceneTransformer;
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
import soot.jimple.internal.JEnterMonitorStmt;
import soot.jimple.internal.JIdentityStmt;
import soot.jimple.internal.JInstanceFieldRef;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JNewExpr;
import soot.jimple.internal.JVirtualInvokeExpr;
import soot.jimple.internal.JimpleLocal;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.UnitGraph;

public class EscapeAnalysis extends SceneTransformer{

	@Override
	protected void internalTransform(String phaseName, Map<String, String> options) {
		/*
		 * Implement your escape analysis here
		 */
		
		
		Integer Og=0;
		
		HashMap<String,JimpleLocal> Jlnametoobj = new HashMap<String,JimpleLocal>();
		
		HashMap<JimpleLocal,LinkedHashSet<Integer>> RhoMap;
		
		HashMap<Integer,HashMap<SootField,LinkedHashSet<Integer>>> SigmaMap;
		
		HashMap<Unit,HashMap<JimpleLocal,LinkedHashSet<Integer>>> Rhoout = new HashMap<Unit,HashMap<JimpleLocal,LinkedHashSet<Integer>>>();
		
		HashMap<Unit,HashMap<Integer,HashMap<SootField,LinkedHashSet<Integer>>>> Sigmaout = new HashMap<Unit,HashMap<Integer,HashMap<SootField,LinkedHashSet<Integer>>>>();
		
		HashMap<Unit,Integer> ObjDecMap = new HashMap<Unit,Integer>();
		
		LinkedHashSet<Integer> EscapeMap = new LinkedHashSet<Integer>();
		
		EscapeMap.add(Og);
		
		Integer currObjNum=1;
		
		CallGraph cg = Scene.v().getCallGraph();
		
		SootMethod main_method = Scene.v().getMainMethod();
		
		LinkedHashSet<SootMethod> worklist = new LinkedHashSet<SootMethod>();
		
		worklist.add(main_method);
		
		//Algorithm
		
		//Initialize everything to Top
		
		HashMap<SootMethod,String> EM_atsynch = new HashMap<SootMethod,String>();
		
		LinkedHashSet<SootClass> threadclasses = new LinkedHashSet<SootClass>();
		String checkThread = "java.lang.Thread";
		
		LinkedHashSet<SootField> staticFields = new LinkedHashSet<SootField>();
		
		HashMap<SootField,LinkedHashSet<Integer>> RhoMap_Statics = new HashMap<SootField,LinkedHashSet<Integer>>();
		
		HashMap<SootMethod,LinkedHashSet<Integer>> Func_Rho_This_in = new HashMap<SootMethod,LinkedHashSet<Integer>>();
		
		HashMap<SootMethod,HashMap<Integer,HashMap<SootField,LinkedHashSet<Integer>>>> Func_Sigma_Map_in = new HashMap<SootMethod,HashMap<Integer,HashMap<SootField,LinkedHashSet<Integer>>>>();
		
		HashMap<SootMethod,HashMap<Integer,HashMap<SootField,LinkedHashSet<Integer>>>> Func_Sigmaout = new HashMap<SootMethod,HashMap<Integer,HashMap<SootField,LinkedHashSet<Integer>>>>();
		
		LinkedHashSet<String> IgnoreMethods = new LinkedHashSet<String>();
		
		IgnoreMethods.add("<clinit>");
		IgnoreMethods.add("<init>");
		IgnoreMethods.add("start");
		IgnoreMethods.add("join");
		IgnoreMethods.add("wait");
		IgnoreMethods.add("notify");
		IgnoreMethods.add("notifyall");
		
		LinkedHashSet<SootMethod> validMethods = new LinkedHashSet<SootMethod>();
		
		for(SootClass sc: Scene.v().getApplicationClasses())
		{
			if(!sc.isLibraryClass())
			{
				//System.out.println("Analyzing Class: " + sc.toString());
				
				//System.out.println("Has SuperClass: " + sc.getSuperclass().toString());
				
				if(checkThread.equals(sc.getSuperclass().toString()))
				{
					//System.out.println(sc.toString() + " is Thread Class");
					
					threadclasses.add(sc);
				}
				
				for(SootField sf: sc.getFields())
				{
					//System.out.println("Analyzing Field: " + sf.toString() + " Field Type: " + sf.getClass());
					if(sf.isStatic())
					{
						staticFields.add(sf);
					}
				}
				//System.out.println();
				
				for(SootMethod sm : sc.getMethods()) //Add to Func_Rho_This_in Func_Sigmaout
				{
					if(!IgnoreMethods.contains(sm.getName()))
					{
						validMethods.add(sm);
						EM_atsynch.put(sm, new String());
						
						Func_Rho_This_in.put(sm, new LinkedHashSet<Integer>());
						Func_Sigmaout.put(sm, new HashMap<Integer,HashMap<SootField,LinkedHashSet<Integer>>>());
						Func_Sigma_Map_in.put(sm, new HashMap<Integer,HashMap<SootField,LinkedHashSet<Integer>>>());
						
						Body bm = sm.retrieveActiveBody();

						UnitGraph gm = new BriefUnitGraph(bm);

						for(Unit u:gm)
						{
							RhoMap = new HashMap<JimpleLocal,LinkedHashSet<Integer>>();
							Rhoout.put(u, RhoMap);
							SigmaMap = new HashMap<Integer,HashMap<SootField,LinkedHashSet<Integer>>>();
							Sigmaout.put(u, SigmaMap);
						}
					}
				}
			}
		}
		

		while(!worklist.isEmpty())
		{
			Iterator<SootMethod> it=worklist.iterator();
			SootMethod m=it.next();
			it.remove();
			
			//System.out.println("\nAnalyzing Function: " + m + "\n");
			//System.out.println(worklist.contains(m));
			//System.out.println(worklist.isEmpty());
			
			Body bm = m.retrieveActiveBody();

			UnitGraph gm = new BriefUnitGraph(bm);
			
			LinkedHashSet<Unit> worklistbody = new LinkedHashSet<Unit>();

			for(Unit u:gm)
			{
				worklistbody.add(u);
			}
			
			while(!worklistbody.isEmpty())
			{
				
				Iterator<Unit> itunit=worklistbody.iterator();
				Unit u=itunit.next();
				itunit.remove();
				
				//System.out.println("\nAnalyzing Unit: " + u + "\n");
				
				
				HashMap<JimpleLocal,LinkedHashSet<Integer>> currRhoMap = new HashMap<JimpleLocal,LinkedHashSet<Integer>>();
				
				HashMap<Integer,HashMap<SootField,LinkedHashSet<Integer>>> currSigmaMap = (HashMap<Integer, HashMap<SootField, LinkedHashSet<Integer>>>) Func_Sigma_Map_in.get(m).clone(); //Should be outside worklist loop probably
				
				HashMap<JimpleLocal,LinkedHashSet<Integer>> pRhoMap;
				HashMap<Integer,HashMap<SootField,LinkedHashSet<Integer>>> pSigmaMap;
				
				List<Unit> pdc=gm.getPredsOf(u);
				
				
				for(Unit p:pdc)
				{
					pRhoMap = Rhoout.get(p);
					pSigmaMap = Sigmaout.get(p);
					
					for(Map.Entry<JimpleLocal,LinkedHashSet<Integer>> e: pRhoMap.entrySet())
					{
						if(!currRhoMap.containsKey(e.getKey()))
						{
							currRhoMap.put(e.getKey(),new LinkedHashSet<Integer>());
							//System.out.println("Adding currRhoMap " + e.getKey());
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
				
				//Stmt st = (Stmt) u;
				
				////////////////////////////////////////////
				
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
						
						if(st.getLeftOp() instanceof JimpleLocal) //LeftOp can be a Field also??
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
							
							if(!currSigmaMap.containsKey(ObjDecMap.get(u)))
							{
								currSigmaMap.put(ObjDecMap.get(u), new HashMap<SootField,LinkedHashSet<Integer>>());
							}
							
							currRhoMap.get(st.getLeftOp()).add(ObjDecMap.get(u));
							
							JNewExpr rtvar = (JNewExpr) st.getRightOp();
							
							if(threadclasses.contains(rtvar.getBaseType().getSootClass()))
							{
								//System.out.println("Adding RHS of Unit " + u + "to Escape Map");
								EscapeMap.add(ObjDecMap.get(u));
							}
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
						
						if(st.getLeftOp() instanceof JimpleLocal) //Simple Copy
						{
							JimpleLocal jl = (JimpleLocal) st.getLeftOp();
							Jlnametoobj.put(jl.getName(), jl);
							
							if(currRhoMap.containsKey(jl))
							{
								currRhoMap.get(jl).clear();
							}
							else
							{
								currRhoMap.put(jl,new LinkedHashSet<Integer>());
							}
							
							//System.out.println("Adding to Rho of " + jl);
							
							for(Integer val:currRhoMap.get(jlr))
							{
								currRhoMap.get(jl).add(val);
							}
						}
						
						else if(st.getLeftOp() instanceof JInstanceFieldRef) //Verify if this covers static fields also
						{
							JInstanceFieldRef instf = (JInstanceFieldRef) st.getLeftOp();
							
							SootField instf_field = (SootField) instf.getField();
							
							
							if(instf_field.isStatic()) //If instf_field is a static field
							{
								//System.out.println("Static Field Assignment");
								
								//Everything reachable from jlr to be put into escaped
								
								LinkedHashSet<Integer> addtoescaped = new LinkedHashSet<Integer>();
								
								LinkedHashSet<Integer> bfslist = new LinkedHashSet<Integer>();
								
								for(Integer obj:currRhoMap.get(jlr))
								{
									bfslist.add(obj);
								}
								
								while(!bfslist.isEmpty())
								{
									LinkedHashSet<Integer> templist = new LinkedHashSet<Integer>();
									for(Integer objnum:bfslist)
									{
										templist.add(objnum);
									}
									bfslist.clear();
									for(Integer objnum:templist)
									{
										if(!addtoescaped.contains(objnum))
										{
											addtoescaped.add(objnum);
											
											for(Map.Entry<SootField,LinkedHashSet<Integer>> emap: currSigmaMap.get(objnum).entrySet())
											{
												for(Integer val:emap.getValue())
												{
													bfslist.add(val);
												}
											}
										}
									}
									templist.clear();
								}
								
								for(Integer objnum:addtoescaped)
								{
									//System.out.println("Adding Object" + objnum + " Reachable from " + jlr + "to Escape Map");
									EscapeMap.add(objnum);
								}
							}
							
							else 
							{
								JimpleLocal instf_base = (JimpleLocal) instf.getBase(); //May give an error if base is a class type i.e leftop is static field
								
								Jlnametoobj.put(instf_base.getName(), instf_base);
								
								boolean baseescaped=false;
								
								for(Integer objnum:currRhoMap.get(instf_base))
								{
									if(EscapeMap.contains(objnum))
									{
										baseescaped=true;
										break;
									}
								}
								
								if(baseescaped)
								{
									//System.out.println("Escaped Object Field Assignment");
									
									LinkedHashSet<Integer> addtoescaped = new LinkedHashSet<Integer>();
									
									LinkedHashSet<Integer> bfslist = new LinkedHashSet<Integer>();
									
									for(Integer obj:currRhoMap.get(jlr))
									{
										bfslist.add(obj);
									}
									
									while(!bfslist.isEmpty())
									{
										LinkedHashSet<Integer> templist = new LinkedHashSet<Integer>();
										for(Integer objnum:bfslist)
										{
											templist.add(objnum);
										}
										bfslist.clear();
										for(Integer objnum:templist)
										{
											if(!addtoescaped.contains(objnum))
											{
												addtoescaped.add(objnum);
												
												for(Map.Entry<SootField,LinkedHashSet<Integer>> emap: currSigmaMap.get(objnum).entrySet())
												{
													for(Integer val:emap.getValue())
													{
														bfslist.add(val);
													}
												}
											}
										}
										templist.clear();
									}
									
									for(Integer objnum:addtoescaped)
									{
										//System.out.println("Adding Object" + objnum + " Reachable from " + jlr + "to Escape Map");
										EscapeMap.add(objnum);
									}
								}
								
								else //Weak Update
								{
									//System.out.println("Normal Field Assignment Doing Weak Update");
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
							}
							
							//System.out.println("Update Finished");
						}
					}
					
					else if(st.getRightOp() instanceof JInstanceFieldRef)
					{
						JInstanceFieldRef instf = (JInstanceFieldRef) st.getRightOp();
						
						SootField instf_field = (SootField) instf.getField();
						
						if(st.getLeftOp() instanceof JimpleLocal)
						{
							JimpleLocal jl = (JimpleLocal) st.getLeftOp();
							Jlnametoobj.put(jl.getName(), jl);
							
							if(!currRhoMap.containsKey(jl))
							{
								currRhoMap.put(jl, new LinkedHashSet<Integer>());
							}
							
							if(instf_field.isStatic())
							{
								currRhoMap.get(jl).clear();
								currRhoMap.get(jl).add(Og);
							}
							
							else
							{
								JimpleLocal instf_base = (JimpleLocal) instf.getBase();
								Jlnametoobj.put(instf_base.getName(), instf_base);
								
								boolean hasescaped=false;
								
								for(Integer objnum:currRhoMap.get(instf_base))
								{
									if(EscapeMap.contains(objnum))
									{
										hasescaped=true;
										break;
									}
								}
								
								if(hasescaped)
								{
									currRhoMap.get(jl).clear();
									currRhoMap.get(jl).add(Og);
								}
								
								else
								{
									currRhoMap.get(jl).clear();
									
									for(Integer objnum:currRhoMap.get(instf_base))
									{
										for(Map.Entry<SootField,LinkedHashSet<Integer>> emap: currSigmaMap.get(objnum).entrySet())
										{
											for(Integer val:emap.getValue())
											{
												currRhoMap.get(jl).add(val);
											}
										}
									}
								}
								
							}
						}
					}
					
				}
				
				else if(u instanceof JIdentityStmt)
				{
					JIdentityStmt st = (JIdentityStmt) u;
					
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
							
							for(Integer objnum:Func_Rho_This_in.get(m))
							{
								currRhoMap.get(lhs).add(objnum);
							}
							//System.out.println(lhs + " Initialized");
						}
					}
				}
				
				else if (u instanceof JEnterMonitorStmt)
				{
					JEnterMonitorStmt st = (JEnterMonitorStmt) u;
					
					boolean ans=true;
					
					if(st.getOp() instanceof JimpleLocal)
					{
						JimpleLocal var = (JimpleLocal) st.getOp();
						
						for(Integer objnum:currRhoMap.get(var))
						{
							if(EscapeMap.contains(objnum))
							{
								ans=false;
								break;
							}
						}
						
						if(ans)
						{
							EM_atsynch.put(m, "Yes");
						}
						else
						{
							EM_atsynch.put(m, "No");
						}
					}
					
					else if(st.getOp() instanceof JInstanceFieldRef)
					{
						JInstanceFieldRef instf = (JInstanceFieldRef) st.getOp();
						
						SootField instf_field = (SootField) instf.getField();
						
						if(instf_field.isStatic())
						{
							EM_atsynch.put(m, "No");
						}
						
						else
						{
							JimpleLocal instf_base = (JimpleLocal) instf.getBase();
							
							
							for(Integer obj:currRhoMap.get(instf_base))
							{
								if(currSigmaMap.containsKey(obj))
								{
									if(currSigmaMap.get(obj).containsKey(instf_field))
									{
										for(Integer objnum:currSigmaMap.get(obj).get(instf_field))
										{
											if(EscapeMap.contains(objnum))
											{
												ans=false;
												break;
											}
										}
									}
								}	
								if(!ans)
								{
									break;
								}
								
							}
							
							if(ans)
							{
								EM_atsynch.put(m, "Yes");
							}
							else
							{
								EM_atsynch.put(m, "No");
							}
						}
					}
					
				}
				
				else if(u instanceof JInvokeStmt)
				{
					
					JInvokeStmt st = (JInvokeStmt) u;
					
					
					Iterator<Edge> euit=cg.edgesOutOf(u);
					
					HashMap<Integer,HashMap<SootField,LinkedHashSet<Integer>>> Sigma_SummaryUnion = new HashMap<Integer,HashMap<SootField,LinkedHashSet<Integer>>>();
					
					while(euit.hasNext())
					{
						Edge et=euit.next();
						
						SootMethod q = et.getTgt().method();
						//String qName = q.getName();
						
						if(validMethods.contains(q))
						{
							//Check if q's Func_Rho_This_in contains Og '0' skip this alltogether
							
							//System.out.println("Analyzing Function: " + q);
							
							if(st.getInvokeExpr() instanceof JVirtualInvokeExpr) //Verify if this will add run() it maybe JSpecialInvokeExpr
							{
								JVirtualInvokeExpr invexp = (JVirtualInvokeExpr) st.getInvokeExpr();
								JimpleLocal thisvar = (JimpleLocal) invexp.getBase(); //Verify if since getBase() returns Value whether it will always be JimpleLocal
								
								//If Rho(thisvar) contains Og change q's Func_Rho_This_in to Og add it to worklist and skip next parts
								/*
								if(currRhoMap.get(thisvar).contains(Og))
								{
									Func_Rho_This_in.get(q).clear();
									Func_Rho_This_in.get(q).add(Og);
									worklist.add(q);
								}
								*/
								//Else go step by step over Rho(thisvar) if not in q's Func_Rho_This_in add it and at end add q to worklist
								
								boolean changed = false;
								
								//System.out.println("Checking Invocation for thisvar: " + thisvar + " " + currRhoMap.containsKey(thisvar));
								
								for(Integer obj:currRhoMap.get(thisvar))
								{
									if(!Func_Rho_This_in.get(q).contains(obj))
									{
										changed = true;
										Func_Rho_This_in.get(q).add(obj);
									}
								}
								
								if(changed)
								{
									//System.out.println("Adding to Worklist through caller: " + q);
									worklist.add(q);
								}
								
								boolean matches=true;
								
								HashMap<Integer,HashMap<SootField,LinkedHashSet<Integer>>> prev_FuncSigmain = Func_Sigma_Map_in.get(q);
								
								for(Map.Entry<Integer,HashMap<SootField,LinkedHashSet<Integer>>> e: currSigmaMap.entrySet())
								{
									if(!prev_FuncSigmain.containsKey(e.getKey()))
									{
										matches=false;
										break;
									}
									
									else
									{
										for(Map.Entry<SootField,LinkedHashSet<Integer>> emap: e.getValue().entrySet())
										{
											if(!prev_FuncSigmain.get(e.getKey()).containsKey(emap.getKey()))
											{
												matches=false;
												break;
											}
											else
											{
												for(Integer objnum:emap.getValue())
												{
													if(!prev_FuncSigmain.get(e.getKey()).get(emap.getKey()).contains(objnum))
													{
														matches=false;
														break;
													}
												}
											}
											if(!matches)
											{
												break;
											}
										}
									}
									if(!matches)
									{
										break;
									}
								}
								
								if(!matches)
								{
									Func_Sigma_Map_in.replace(q,(HashMap<Integer, HashMap<SootField, LinkedHashSet<Integer>>>) currSigmaMap.clone());
									worklist.add(q);
								}
								
							}
							
							//Take Union of all summaries
							
							HashMap<Integer,HashMap<SootField,LinkedHashSet<Integer>>> qSigmaMap = Func_Sigmaout.get(q);
							
							for(Map.Entry<Integer,HashMap<SootField,LinkedHashSet<Integer>>> e: qSigmaMap.entrySet())
							{
								if(!Sigma_SummaryUnion.containsKey(e.getKey()))
								{
									Sigma_SummaryUnion.put(e.getKey(),new HashMap<SootField,LinkedHashSet<Integer>>());	
								}
								
								for(Map.Entry<SootField,LinkedHashSet<Integer>> emap: e.getValue().entrySet())
								{
									if(!Sigma_SummaryUnion.get(e.getKey()).containsKey(emap.getKey()))
									{
										Sigma_SummaryUnion.get(e.getKey()).put(emap.getKey(), new LinkedHashSet<Integer>());
									}
									
									
									for(Integer val:emap.getValue())
									{
										Sigma_SummaryUnion.get(e.getKey()).get(emap.getKey()).add(val);
									}
								}
							}
						}
						
					}
					
					//Update currSigma using q's Summary
					for(Map.Entry<Integer,HashMap<SootField,LinkedHashSet<Integer>>> e: Sigma_SummaryUnion.entrySet())
					{
						if(!currSigmaMap.containsKey(e.getKey()))
						{
							Sigma_SummaryUnion.put(e.getKey(),new HashMap<SootField,LinkedHashSet<Integer>>());	
						}
						
						for(Map.Entry<SootField,LinkedHashSet<Integer>> emap: e.getValue().entrySet())
						{
							if(!Sigma_SummaryUnion.get(e.getKey()).containsKey(emap.getKey()))
							{
								Sigma_SummaryUnion.get(e.getKey()).put(emap.getKey(), new LinkedHashSet<Integer>());
							}
							/*
							else
							{
								Sigma_SummaryUnion.get(e.getKey()).get(emap.getKey()).clear(); //Do a Strong Update for this SootField
							}
							*/
							for(Integer val:emap.getValue())
							{
								Sigma_SummaryUnion.get(e.getKey()).get(emap.getKey()).add(val);
							}
						}
					}
				}
				
				if(!currRhoMap.equals(Rhoout.get(u)))
				{
					Rhoout.put(u,currRhoMap);
					if(!currSigmaMap.equals(Sigmaout.get(u)))
					{
						Sigmaout.put(u,currSigmaMap);
					}
					
					List<Unit> scs=gm.getSuccsOf(u);
					for(Unit s:scs)
					{
						worklistbody.add(s);
					}
				}
				else if(!currSigmaMap.equals(Sigmaout.get(u)))
				{
					Sigmaout.put(u,currSigmaMap);
					
					List<Unit> scs=gm.getSuccsOf(u);
					for(Unit s:scs)
					{
						worklistbody.add(s);
					}
				}
				
				///////////////////////////////////////////
				
				
			}
			
			
			//Merge Rho and Sigma of Tails of Unitgraph
			List<Unit> tls=gm.getTails();
			
			HashMap<JimpleLocal,LinkedHashSet<Integer>> finRhoMap = new HashMap<JimpleLocal,LinkedHashSet<Integer>>();
			
			HashMap<Integer,HashMap<SootField,LinkedHashSet<Integer>>> finSigmaMap = new HashMap<Integer,HashMap<SootField,LinkedHashSet<Integer>>>();
			
			//HashMap<Integer,HashMap<SootField,LinkedHashSet<Integer>>> finSigmaMap = Func_Sigmaout.get(m);
			
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
				
				for(Map.Entry<Integer,HashMap<SootField,LinkedHashSet<Integer>>> e: pSigmaMap.entrySet()) //Verify Once
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
			
			//Verify if finSigmaMap and Func_Sigma_Out are not equal, if true then add all the callees of m to worklist and update Func_Sigma_Out
			
			boolean matches=true;
			
			HashMap<Integer,HashMap<SootField,LinkedHashSet<Integer>>> prev_FuncSigmaout = Func_Sigmaout.get(m);
			
			for(Map.Entry<Integer,HashMap<SootField,LinkedHashSet<Integer>>> e: finSigmaMap.entrySet())
			{
				if(!prev_FuncSigmaout.containsKey(e.getKey()))
				{
					matches=false;
					break;
				}
				
				else
				{
					for(Map.Entry<SootField,LinkedHashSet<Integer>> emap: e.getValue().entrySet())
					{
						if(!prev_FuncSigmaout.get(e.getKey()).containsKey(emap.getKey()))
						{
							matches=false;
							break;
						}
						else
						{
							for(Integer objnum:emap.getValue())
							{
								if(!prev_FuncSigmaout.get(e.getKey()).get(emap.getKey()).contains(objnum))
								{
									matches=false;
									break;
								}
							}
						}
						if(!matches)
						{
							break;
						}
					}
				}
				if(!matches)
				{
					break;
				}
			}
			
			if(!matches)
			{
				Func_Sigmaout.replace(m,finSigmaMap);
				
				Iterator<Edge> einto=cg.edgesInto(m);
				
				while(einto.hasNext())
				{
					Edge e=einto.next();
					
					SootMethod calleemethod = (SootMethod) e.getSrc();
					
					if(validMethods.contains(calleemethod)&&(!m.equals(calleemethod)))
					{
						//System.out.println("Analyzing Method: " + m);
						//System.out.println("Adding to Worklist through callee: " + calleemethod);
						//System.out.println(calleemethod.equals(m));
						worklist.add(calleemethod);
					}
					
				}
				
			}
			
			//System.out.println("Finished Analyzing Method: " + m);
			
			//Process m's units (u) as Assignment1 except when
			
			// u is a synchronization/monitor statement then remember EM at u else if
			
			// u is a function invoke in which case
			
			// For each argument of function compute current Rho and Sigma arguments including globals/statics, this and fn arguments
			
			// Now for each function call possible (f) using cg.edgesOutOf(u) verify if its arguments Rho and Sigma have changed w.r.t above then change them and add f to worklist
			
			// Update Sigma of arguments, (Rho?? and Sigma of return value acceptor and Static Fields??) as per Summary(results when f was previously analyzed) and Escape Map
			
			//If summary of m (Sigma, Statics) has changed add its callee functions cg.edgesInto(m) to worklist
		}
		
		for(int i=0; i<A2.queryList.size();i++)
		{
			String currClassName = A2.queryList.get(i).getClassName();
			String currMethodName = A2.queryList.get(i).getMethodName();
			
			SootClass currClass = Scene.v().getSootClass(currClassName);
			SootMethod currMethod = currClass.getMethodByName(currMethodName);
			
			A2.answers[i] = EM_atsynch.get(currMethod);
		}
		
	}
	
}
