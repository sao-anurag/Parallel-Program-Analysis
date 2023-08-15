package submit_a3;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import soot.Body;
import soot.BodyTransformer;
import soot.PointsToAnalysis;
import soot.PointsToSet;
import soot.RefType;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JEnterMonitorStmt;
import soot.jimple.internal.JExitMonitorStmt;
import soot.jimple.internal.JInstanceFieldRef;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JVirtualInvokeExpr;
import soot.jimple.internal.JimpleLocal;
import soot.jimple.spark.pag.Node;
import soot.jimple.spark.sets.P2SetVisitor;
import soot.jimple.spark.sets.PointsToSetInternal;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.CompleteUnitGraph;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soot.toolkits.graph.pdg.EnhancedUnitGraph;
import soot.util.Chain;

public class MhpAnalysis extends SceneTransformer{

	@Override
	protected void internalTransform(String phaseName, Map<String, String> options) {
		/*
		 * Implement your mhp analysis here
		 */
		
		LinkedHashSet<Node> SubGraphCreated;
		
		HashMap<Node,PEGNode> SubGraphBase;
		
		HashMap<String,JimpleLocal> VartoRef = new HashMap<String,JimpleLocal>();
		
		HashMap<Integer,LinkedHashSet<PEGNode>> Monitorset = new HashMap<Integer,LinkedHashSet<PEGNode>>();
		
		//HashMap<Unit,SootMethod> getRunMethod = new HashMap<Unit,SootMethod>();
		
		PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
		
		CallGraph cg = Scene.v().getCallGraph();
		
		SootMethod main_method = Scene.v().getMainMethod();
		
		P2SetVisitor vis = new P2SetVisitor()
		{

            @Override
            public void visit(Node n)
            {
             /* Do something with node n*/
            	//System.out.println("Node is " + n + " Hashcode: " +n.hashCode() + " Number: " +n.getNumber() + " Type: " +n.getType());
            }
        };        
        /*
        Iterator<Edge> eit=cg.edgesOutOf(main_method);
		
		while(eit.hasNext())
		{
			Edge e=eit.next();
			//System.out.println("unit is " + e.srcUnit() + " getClass: "+e.srcUnit().getClass());
			//System.out.println("Target Method is " + e.tgt());
			//System.out.println(e.isThreadRunCall());
			if(e.isThreadRunCall())
			{
				getRunMethod.put(e.srcUnit(), e.tgt());
			}
		}
        */
        
        Body bmm = main_method.retrieveActiveBody();

		UnitGraph gmm = new BriefUnitGraph(bmm);
		
		//System.out.println("\nAnalyzing Method: " + main_method.getName());
        
		for(Unit u:gmm)
		{
			//System.out.println(u+"\n");
			
			if(u instanceof JAssignStmt)
			{
				JAssignStmt st = (JAssignStmt) u;
				
				if(st.getRightOp() instanceof JimpleLocal)
				{
					JimpleLocal jr = (JimpleLocal) st.getRightOp();
					
					VartoRef.put(jr.toString(),jr);
					/*
					PointsToSet pts = pta.reachingObjects(jr);
					
					PointsToSetInternal pti = (PointsToSetInternal) pts;
					
					//System.out.println("Printing for RightOp "+ jr +"\n");
					
					pti.forall(vis);
					*/					
				}
					
				if(st.getLeftOp() instanceof JimpleLocal) //LeftOp can be a Field also??
				{
					JimpleLocal jl = (JimpleLocal) st.getLeftOp();
					
					VartoRef.put(jl.toString(),jl);
					/*
					PointsToSet pts = pta.reachingObjects(jl);
					
					PointsToSetInternal pti = (PointsToSetInternal) pts;
					
					//System.out.println("Printing for LeftOp "+ jl +"\n");
					
					pti.forall(vis);
					*/
				}
				
				//System.out.println();
			}
		}
		
		
		Iterator<Edge> eit2=cg.edgesOutOf(main_method);
		
		LinkedHashSet<SootMethod> c2main = new LinkedHashSet<SootMethod>();
		
		while(eit2.hasNext())
		{
			Edge e=eit2.next();
			SootMethod sm = e.tgt();
			
			if(!c2main.contains(sm))
			{
				c2main.add(sm);
				//System.out.println("\nAnalyzing Method: " + sm.getName());
				
				Body bm = sm.retrieveActiveBody();

				UnitGraph gm = new BriefUnitGraph(bm);

				for(Unit u:gm)
				{
					//System.out.println(u+"\n");
					
					if(u instanceof JAssignStmt)
					{
						JAssignStmt st = (JAssignStmt) u;
						
						if(st.getRightOp() instanceof JimpleLocal)
						{
							JimpleLocal jr = (JimpleLocal) st.getRightOp();
							
							VartoRef.put(jr.toString(),jr);
							/*
							PointsToSet pts = pta.reachingObjects(jr);
							
							PointsToSetInternal pti = (PointsToSetInternal) pts;
							
							//System.out.println("Printing for RightOp "+ jr +"\n");
							
							pti.forall(vis);
							*/					
						}
							
						if(st.getLeftOp() instanceof JimpleLocal) //LeftOp can be a Field also??
						{
							JimpleLocal jl = (JimpleLocal) st.getLeftOp();
							
							VartoRef.put(jl.toString(),jl);
							/*
							PointsToSet pts = pta.reachingObjects(jl);
							
							PointsToSetInternal pti = (PointsToSetInternal) pts;
							
							//System.out.println("Printing for LeftOp "+ jl +"\n");
							
							pti.forall(vis);
							*/
						}
						
						//System.out.println();
					}
				}
			}
		}
		
		
		LinkedHashSet<PEGNode> algolist = new LinkedHashSet<PEGNode>();
        
        
        LinkedHashSet<MethodListNode> methodlist = new LinkedHashSet<MethodListNode>();
        
        HashMap<Integer,LinkedHashSet<PEGNode>> Nset = new HashMap<Integer,LinkedHashSet<PEGNode>>();
        
        MethodListNode mainnode = new MethodListNode();
        
        PEGNode PEGmainbasenode = new PEGNode();

        
        PEGmainbasenode.obj = -1;
        PEGmainbasenode.threadobj = 0;
        PEGmainbasenode.nodetype = 2;
        
        mainnode.obj=0;
        mainnode.m=main_method;
        mainnode.basenode = PEGmainbasenode;
        
        methodlist.add(mainnode);
        
        while(!methodlist.isEmpty())
        {
        	Iterator<MethodListNode> it=methodlist.iterator();
        	MethodListNode smnode=it.next();
			it.remove();
			
			PEGNode basenode = smnode.basenode;
			
			SootMethod sm = smnode.m;
			
			Body bm = sm.retrieveActiveBody();

			UnitGraph gm = new BriefUnitGraph(bm);
			
			LinkedHashSet<PEGNode> worklist = new LinkedHashSet<PEGNode>();
			
			LinkedHashSet<Unit> visited = new LinkedHashSet<Unit>();
			
			Nset.put(basenode.threadobj, new LinkedHashSet<PEGNode>());
			
			Nset.get(basenode.threadobj).add(basenode);
			
			List<Unit> hds=gm.getHeads();
			
			for(Unit u:hds)
			{
				//System.out.println("Checking unit: "+u);
				
				if(u instanceof JInvokeStmt)
				{
					JInvokeStmt st = (JInvokeStmt) u;
					InvokeExpr Invexp = st.getInvokeExpr();
					
					SootMethod m = Invexp.getMethod();
					
					//System.out.println("Invoke Method Name: "+m.getName());
					
					if(m.getName().equals("start"))
					{
						/*
						SootClass sc = m.getDeclaringClass();
						
						//System.out.println("Class for Run Method: "+sc.getName());
						
						SootMethod runmethod = sc.getMethodByName("run");
						
						//System.out.println("Run Method Name: "+runmethod);
						
						SootMethod rmethod=runmethod;
						
						Iterator<Edge> edgeit=cg.edgesOutOf(u);
						
						while(edgeit.hasNext())
						{
							Edge e=edgeit.next();
							//System.out.println("unit is " + e.srcUnit() + " getClass: "+e.srcUnit().getClass());
							//System.out.println("Target Method is " + e.tgt());
							//System.out.println(e.isThreadRunCall());
							
							if(e.isThreadRunCall())
							{
								rmethod = e.tgt();
								break;
							}
							
						}
						
						runmethod=rmethod;
						
						//System.out.println("Run Method Name: "+runmethod);
						*/
						if(Invexp instanceof JVirtualInvokeExpr) //Verify if this will add run() it maybe JSpecialInvokeExpr
						{
							JVirtualInvokeExpr jinvexp = (JVirtualInvokeExpr) Invexp;
							JimpleLocal thisvar = (JimpleLocal) jinvexp.getBase(); //Verify if since getBase() returns Value whether it will always be JimpleLocal
							
							PEGNode nodetoadd = new PEGNode();
							
							nodetoadd.obj=basenode.obj;
							nodetoadd.threadobj=basenode.threadobj;
							nodetoadd.u = u;
							nodetoadd.nodetype = 1;
							
							basenode.outEdges_internal.add(nodetoadd);
							nodetoadd.inEdges.add(basenode);
							worklist.add(nodetoadd);
							Nset.get(basenode.threadobj).add(nodetoadd);
							
							if(basenode.threadobj==0)
							{
								algolist.add(nodetoadd);
							}
							
							P2SetVisitor genSubGraph = new P2SetVisitor()
							{

					            @Override
					            public void visit(Node n)
					            {
					             /* Do something with node n*/
					            	MethodListNode addnode = new MethodListNode();
					                
					                PEGNode PEGaddbasenode = new PEGNode();

					                
					                PEGaddbasenode.obj = -1;
					                PEGaddbasenode.threadobj = n.getNumber();
					                PEGaddbasenode.nodetype = 2;
					                
					                //System.out.println("For unit: "+u+" Adding External Edge to "+n.getNumber());
					                
					                nodetoadd.outEdges_external.add(PEGaddbasenode);
					                nodetoadd.GENset.add(PEGaddbasenode);
					                PEGaddbasenode.inEdges_external.add(nodetoadd);
					                
					                addnode.obj=n.getNumber();
					                
					                //addnode.m=getRunMethod.get(u);
					                
					                Iterator<Edge> edgeit=cg.edgesOutOf(u);
									
									while(edgeit.hasNext())
									{
										Edge e=edgeit.next();
										//System.out.println("unit is " + e.srcUnit() + " getClass: "+e.srcUnit().getClass());
										//System.out.println("Target Method is " + e.tgt());
										//System.out.println(e.isThreadRunCall());
										
										if(e.isThreadRunCall())
										{
											addnode.m = e.tgt();
											break;
										}
										
									}
					                
					                addnode.basenode = PEGaddbasenode;
					                
					                methodlist.add(addnode);
					            }
					        };
					        
					        PointsToSet pts = pta.reachingObjects(thisvar);
							
							PointsToSetInternal pti = (PointsToSetInternal) pts;
							
							pti.forall(genSubGraph);
						}
					}
				}
				
				else
				{
					PEGNode nodetoadd = new PEGNode();

					
					nodetoadd.obj=basenode.obj;
					nodetoadd.threadobj=basenode.threadobj;
					nodetoadd.u = u;
					
					basenode.outEdges_internal.add(nodetoadd);
					nodetoadd.inEdges.add(basenode);
					worklist.add(nodetoadd);
					Nset.get(basenode.threadobj).add(nodetoadd);
				}
			}
			
			while(!worklist.isEmpty())
			{
				Iterator<PEGNode> wit=worklist.iterator();
				PEGNode pnode=wit.next();
				wit.remove();
				
				if(pnode.obj!=-1)
				{
					if(!Monitorset.containsKey(pnode.obj))
					{
						Monitorset.put(pnode.obj, new LinkedHashSet<PEGNode>());
					}
					
					Monitorset.get(pnode.obj).add(pnode);
				}
				
				if(!visited.contains(pnode.u))
				{
					visited.add(pnode.u);
					
					List<Unit> succslist=gm.getSuccsOf(pnode.u);
					
					for(Unit u:succslist)
					{
						//System.out.println("Checking unit: "+u);
						
						if(u instanceof JInvokeStmt)
						{
							JInvokeStmt st = (JInvokeStmt) u;
							InvokeExpr Invexp = st.getInvokeExpr();
							
							SootMethod m = Invexp.getMethod();
							
							//System.out.println("Invoke Method Name: "+m.getName());
							
							if(m.getName().equals("start"))
							{
								/*
								SootClass sc = m.getDeclaringClass();
								
								//System.out.println("Class for Run Method: "+sc.getName());
								
								SootMethod runmethod = sc.getMethodByName("run");
								
								//System.out.println("Run Method Name: "+runmethod);
								
								
								Iterator<Edge> edgeit=cg.edgesOutOf(u);
								
								while(edgeit.hasNext())
								{
									Edge e=edgeit.next();
									//System.out.println("unit is " + e.srcUnit() + " getClass: "+e.srcUnit().getClass());
									//System.out.println("Target Method is " + e.tgt());
									//System.out.println(e.isThreadRunCall());
									
									if(e.isThreadRunCall())
									{
										runmethod = e.tgt();
										break;
									}
									
								}
								
								//System.out.println("Run Method Name: "+runmethod);
								*/
								if(Invexp instanceof JVirtualInvokeExpr) //Verify if this will add run() it maybe JSpecialInvokeExpr
								{
									JVirtualInvokeExpr jinvexp = (JVirtualInvokeExpr) Invexp;
									JimpleLocal thisvar = (JimpleLocal) jinvexp.getBase(); //Verify if since getBase() returns Value whether it will always be JimpleLocal
									
									PEGNode nodetoadd = new PEGNode();

									
									nodetoadd.obj=pnode.obj;
									nodetoadd.threadobj=basenode.threadobj;
									nodetoadd.u = u;
									nodetoadd.nodetype = 1;
									
									pnode.outEdges_internal.add(nodetoadd);
									nodetoadd.inEdges.add(pnode);
									worklist.add(nodetoadd);
									Nset.get(basenode.threadobj).add(nodetoadd);
									
									if(basenode.threadobj==0)
									{
										algolist.add(nodetoadd);
									}
									
									P2SetVisitor genSubGraph = new P2SetVisitor()
									{

							            @Override
							            public void visit(Node n)
							            {
							             /* Do something with node n*/
							            	MethodListNode addnode = new MethodListNode();
							                
							                PEGNode PEGaddbasenode = new PEGNode();

							                
							                PEGaddbasenode.obj = -1;
							                PEGaddbasenode.threadobj = n.getNumber();
							                PEGaddbasenode.nodetype = 2;
							                
							                //System.out.println("For unit: "+u+" Adding External Edge to "+n.getNumber());
							                
							                nodetoadd.outEdges_external.add(PEGaddbasenode);
							                nodetoadd.GENset.add(PEGaddbasenode);
							                PEGaddbasenode.inEdges_external.add(nodetoadd);
							                
							                addnode.obj=n.getNumber();
							                
							                //addnode.m=getRunMethod.get(u);
							                
							                Iterator<Edge> edgeit=cg.edgesOutOf(u);
											
											while(edgeit.hasNext())
											{
												Edge e=edgeit.next();
												//System.out.println("unit is " + e.srcUnit() + " getClass: "+e.srcUnit().getClass());
												//System.out.println("Target Method is " + e.tgt());
												//System.out.println(e.isThreadRunCall());
												
												if(e.isThreadRunCall())
												{
													addnode.m = e.tgt();
													break;
												}
												
											}
							                
							                addnode.basenode = PEGaddbasenode;
							                
							                methodlist.add(addnode);
							            }
							        };
							        
							        PointsToSet pts = pta.reachingObjects(thisvar);
									
									PointsToSetInternal pti = (PointsToSetInternal) pts;
									
									pti.forall(genSubGraph);
									
								}
							}
							
							else if(m.getName().equals("wait"))
							{
								PEGNode nodetoadd = new PEGNode();

								
								nodetoadd.obj=pnode.obj;
								nodetoadd.threadobj=basenode.threadobj;
								nodetoadd.u = u;
								nodetoadd.nodetype = 6;
								
								pnode.outEdges_internal.add(nodetoadd);
								nodetoadd.inEdges.add(pnode);
								Nset.get(basenode.threadobj).add(nodetoadd);
								
								PEGNode nodetoadd2 = new PEGNode();

								
								nodetoadd2.obj=pnode.obj;
								nodetoadd2.threadobj=basenode.threadobj;
								nodetoadd2.u = u;
								nodetoadd2.nodetype = 7;
								
								nodetoadd.outEdges_internal.add(nodetoadd2);
								nodetoadd2.inEdges.add(nodetoadd);
								Nset.get(basenode.threadobj).add(nodetoadd2);
								
								PEGNode nodetoadd3 = new PEGNode();

								
								nodetoadd3.obj=pnode.obj;
								nodetoadd3.threadobj=basenode.threadobj;
								nodetoadd3.u = u;
								nodetoadd3.nodetype = 8;
								
								nodetoadd2.outEdges_internal.add(nodetoadd3);
								nodetoadd3.inEdges.add(nodetoadd2);
								
								worklist.add(nodetoadd3);
								Nset.get(basenode.threadobj).add(nodetoadd3);
							}
							
							else if(m.getName().equals("notify"))
							{
								PEGNode nodetoadd = new PEGNode();

								
								nodetoadd.obj=pnode.obj;
								nodetoadd.threadobj=basenode.threadobj;
								nodetoadd.u = u;
								nodetoadd.nodetype = 9;
								
								pnode.outEdges_internal.add(nodetoadd);
								nodetoadd.inEdges.add(pnode);
								worklist.add(nodetoadd);
								Nset.get(basenode.threadobj).add(nodetoadd);
							}
							
							else if(m.getName().equals("notifyall"))
							{
								PEGNode nodetoadd = new PEGNode();

								
								nodetoadd.obj=pnode.obj;
								nodetoadd.threadobj=basenode.threadobj;
								nodetoadd.u = u;
								nodetoadd.nodetype = 10;
								
								pnode.outEdges_internal.add(nodetoadd);
								nodetoadd.inEdges.add(pnode);
								worklist.add(nodetoadd);
								Nset.get(basenode.threadobj).add(nodetoadd);
							}
							
							else if(m.getName().equals("join"))
							{
								PEGNode nodetoadd = new PEGNode();

								
								nodetoadd.obj=pnode.obj;
								nodetoadd.threadobj=basenode.threadobj;
								nodetoadd.u = u;
								nodetoadd.nodetype = 11;
								
								pnode.outEdges_internal.add(nodetoadd);
								nodetoadd.inEdges.add(pnode);
								worklist.add(nodetoadd);
								Nset.get(basenode.threadobj).add(nodetoadd);
							}
							
							else
							{
								PEGNode nodetoadd = new PEGNode();

								
								nodetoadd.obj=pnode.obj;
								nodetoadd.threadobj=basenode.threadobj;
								nodetoadd.u = u;
								nodetoadd.nodetype = 1;
								
								pnode.outEdges_internal.add(nodetoadd);
								nodetoadd.inEdges.add(pnode);
								worklist.add(nodetoadd);
								Nset.get(basenode.threadobj).add(nodetoadd);
							}
						}
						
						else if (u instanceof JEnterMonitorStmt)
						{
							JEnterMonitorStmt st = (JEnterMonitorStmt) u;
							
							if(st.getOp() instanceof JimpleLocal)
							{
								JimpleLocal jl = (JimpleLocal) st.getOp();
								
								P2SetVisitor genSynchNodes = new P2SetVisitor()
								{

						            @Override
						            public void visit(Node n)
						            {
						             /* Do something with node n*/
						            	PEGNode nodetoadd = new PEGNode();

										
										nodetoadd.obj=n.getNumber();
										nodetoadd.threadobj=basenode.threadobj;
										nodetoadd.u = u;
										nodetoadd.nodetype = 4;
										
										pnode.outEdges_internal.add(nodetoadd);
										nodetoadd.inEdges.add(pnode);
										worklist.add(nodetoadd);
										Nset.get(basenode.threadobj).add(nodetoadd);
						            }
						        };
						        
						        PointsToSet pts = pta.reachingObjects(jl);
								
								PointsToSetInternal pti = (PointsToSetInternal) pts;
								
								pti.forall(genSynchNodes);
							}
							
							else if(st.getOp() instanceof JInstanceFieldRef)
    						{
    							JInstanceFieldRef instfa = (JInstanceFieldRef) st.getOp();
    							
    							SootField instf_fielda = (SootField) instfa.getField();
    							
    							JimpleLocal jl = (JimpleLocal) instfa.getBase();
    							
    							P2SetVisitor genSynchNodes = new P2SetVisitor()
								{

						            @Override
						            public void visit(Node n)
						            {
						             /* Do something with node n*/
						            	PEGNode nodetoadd = new PEGNode();

										
										nodetoadd.obj=n.getNumber();
										nodetoadd.threadobj=basenode.threadobj;
										nodetoadd.u = u;
										nodetoadd.nodetype = 4;
										
										pnode.outEdges_internal.add(nodetoadd);
										nodetoadd.inEdges.add(pnode);
										worklist.add(nodetoadd);
										Nset.get(basenode.threadobj).add(nodetoadd);
						            }
						        };
						        
						        PointsToSet pts = pta.reachingObjects(jl,instf_fielda);
								
								PointsToSetInternal pti = (PointsToSetInternal) pts;
								
								pti.forall(genSynchNodes);
    						}
							/*
							PEGNode nodetoadd = new PEGNode();

							
							nodetoadd.obj=pnode.obj;
							nodetoadd.threadobj=basenode.threadobj;
							nodetoadd.u = u;
							nodetoadd.nodetype = 4;
							
							pnode.outEdges_internal.add(nodetoadd);
							nodetoadd.inEdges.add(pnode);
							worklist.add(nodetoadd);
							Nset.get(basenode.threadobj).add(nodetoadd);
							*/
						}
						
						else if (u instanceof JExitMonitorStmt)
						{
							//JExitMonitorStmt st = (JExitMonitorStmt) u;
							
							PEGNode nodetoadd = new PEGNode();

							
							nodetoadd.obj=pnode.obj;
							nodetoadd.threadobj=basenode.threadobj;
							nodetoadd.u = u;
							nodetoadd.nodetype = 5;
							
							pnode.outEdges_internal.add(nodetoadd);
							nodetoadd.inEdges.add(pnode);
							worklist.add(nodetoadd);
							Nset.get(basenode.threadobj).add(nodetoadd);
						}
						
						else
						{
							PEGNode nodetoadd = new PEGNode();
							
							
							nodetoadd.obj=pnode.obj;
							nodetoadd.threadobj=basenode.threadobj;
							nodetoadd.u = u;
							nodetoadd.nodetype = 1;
							
							pnode.outEdges_internal.add(nodetoadd);
							nodetoadd.inEdges.add(pnode);
							worklist.add(nodetoadd);
							Nset.get(basenode.threadobj).add(nodetoadd);
						}
					}
				}
				
			}
        }
        
        LinkedHashSet<PEGNode> dfslist = new LinkedHashSet<PEGNode>();
        
        LinkedHashSet<PEGNode> vislog = new LinkedHashSet<PEGNode>();
        
        dfslist.add(PEGmainbasenode);
        
        while(!dfslist.isEmpty())
        {
        	Iterator<PEGNode> dit=dfslist.iterator();
			PEGNode pnode=dit.next();
			dit.remove();
			
        	if(!vislog.contains(pnode))
        	{
        		vislog.add(pnode);
        		
        		if(pnode.nodetype==11)
        		{
        			JInvokeStmt st = (JInvokeStmt) pnode.u;
        			JVirtualInvokeExpr jinvexp = (JVirtualInvokeExpr) st.getInvokeExpr();
					JimpleLocal thisvar = (JimpleLocal) jinvexp.getBase();
					
					P2SetVisitor updateKill = new P2SetVisitor()
					{

			            @Override
			            public void visit(Node n)
			            {
			             /* Do something with node n*/
			            	
			            	for(PEGNode pn:Nset.get(n.getNumber()))
			            	{
			            		pnode.KILLset.add(pn);
			            	}
			            }
			        };
			        
			        PointsToSet pts = pta.reachingObjects(thisvar);
					
					PointsToSetInternal pti = (PointsToSetInternal) pts;
					
					pti.forall(updateKill);
        			
        		}
        		
        		else if(pnode.nodetype==4)
        		{
        			for(PEGNode pn:Monitorset.get(pnode.obj))
	            	{
	            		pnode.KILLset.add(pn);
	            	}
	            }
        			
        		
        		for(PEGNode n:pnode.outEdges_internal)
        		{
        			dfslist.add(n);
        		}
        		
        		for(PEGNode n:pnode.outEdges_external)
        		{
        			dfslist.add(n);
        		}
        		
        	}
        }
        
        
        while(!algolist.isEmpty())
        {
        	Iterator<PEGNode> ait=algolist.iterator();
			PEGNode pnode=ait.next();
			ait.remove();
			
			LinkedHashSet<PEGNode> Mset_old = new LinkedHashSet<PEGNode>();
			Mset_old = (LinkedHashSet<PEGNode>) pnode.Mset.clone();
			
			if(pnode.obj==2)
			{
				for(PEGNode pn:pnode.inEdges_external)
				{
					for(PEGNode addnode:pn.OUTset)
					{
						pnode.Mset.add(addnode);
					}
				}
				
				for(PEGNode pn:Nset.get(pnode.threadobj))
				{
					pnode.Mset.remove(pn);
				}
			}
			
			else
			{
				for(PEGNode pn:pnode.inEdges)
				{
					for(PEGNode addnode:pn.OUTset)
					{
						pnode.Mset.add(addnode);
					}
				}
			}
			
			for(PEGNode pn:pnode.Mset)
			{
				if(!Mset_old.contains(pn))
				{
					pn.Mset.add(pnode);
					algolist.add(pn);
				}
			}
			
			LinkedHashSet<PEGNode> OUTset_old = new LinkedHashSet<PEGNode>();
			OUTset_old = (LinkedHashSet<PEGNode>) pnode.OUTset.clone();
			
			pnode.OUTset = new LinkedHashSet<PEGNode>();
			
			for(PEGNode pn:pnode.Mset)
			{
				pnode.OUTset.add(pn);
			}
			
			for(PEGNode pn:pnode.GENset)
			{
				pnode.OUTset.add(pn);
			}
			
			for(PEGNode pn:pnode.KILLset)
			{
				if(pnode.OUTset.contains(pn))
				{
					pnode.OUTset.remove(pn);
				}
			}
			
			for(PEGNode pn:pnode.OUTset)
			{
				if(!OUTset_old.contains(pn))
				{
					for(PEGNode addnode:pnode.outEdges_internal)
					{
						algolist.add(addnode);
					}
					
					for(PEGNode addnode:pnode.outEdges_external)
					{
						algolist.add(addnode);
					}
					
					break;
				}
			}
			
			
        }
        
        for(int i=0; i<A3.queryList.size();i++)
		{
        	final String[] ans = new String[1]; 
        	 
        	ans[0] = "No";
        	
        	String currVarName = A3.queryList.get(i).getVar();
			String currFieldName = A3.queryList.get(i).getField();
			
			JimpleLocal currVar = VartoRef.get(currVarName);
			
			RefType rt = (RefType) currVar.getType();
			
			SootField currField = rt.getSootClass().getFieldByName(currFieldName);
			
			P2SetVisitor getAns = new P2SetVisitor()
			{

	            @Override
	            public void visit(Node n)
	            {
	             /* Do something with node n*/
	            	
	            	//System.out.println("Checking "+ n.getNumber() +"\n");
	            	
	            	LinkedHashSet<PEGNode> dfslist2 = new LinkedHashSet<PEGNode>();
	                
	                LinkedHashSet<PEGNode> vislog2 = new LinkedHashSet<PEGNode>();
	                
	                dfslist2.add(PEGmainbasenode);
	                
	                while(!dfslist2.isEmpty())
	                {
	                	Iterator<PEGNode> dit=dfslist2.iterator();
	        			PEGNode pnode=dit.next();
	        			dit.remove();
	        			
	                	if(!vislog2.contains(pnode))
	                	{
	                		vislog2.add(pnode);
	                		
	                		if(pnode.nodetype==1)
	                		{
	                			if(pnode.u instanceof JAssignStmt)
	        					{
	                				//System.out.println("Checking "+ pnode.u +"\n");
	                				
	                				JAssignStmt st = (JAssignStmt) pnode.u;
	        						
	        						if(st.getLeftOp() instanceof JimpleLocal)
	        						{
	        							JimpleLocal jl = (JimpleLocal) st.getLeftOp();
	        							
	        							P2SetVisitor verify = new P2SetVisitor()
	    	        					{

	    	        			            @Override
	    	        			            public void visit(Node num)
	    	        			            {
	    	        			             /* Do something with node n*/
	    	        			            	
	    	        			            	//System.out.println("Checking num "+ num.getNumber() +"\n");
	    	        			            	
	    	        			            	if(num.getNumber()==n.getNumber())
	    	        			            	{
	    	        			            		for(PEGNode compnode:pnode.Mset)
	    	        			            		{
	    	        			            			
	    	        			            			//System.out.println("Checking compnode "+ compnode.u +"\n");
	    	        			            			
	    	        			            			if(compnode.nodetype==1)
	    	        			                		{
	    	        			                			if(compnode.u instanceof JAssignStmt)
	    	        			        					{
	    	        			        						JAssignStmt compst = (JAssignStmt) compnode.u;
	    	        			        						
	    	        			        						if(compst.getLeftOp() instanceof JimpleLocal)
	    	        			        						{
	    	        			        							JimpleLocal jlcomp = (JimpleLocal) compst.getLeftOp();
	    	        			        							
	    	        			        							P2SetVisitor verifyl = new P2SetVisitor()
	    	        			    	        					{

	    	        			    	        			            @Override
	    	        			    	        			            public void visit(Node numl)
	    	        			    	        			            {
	    	        			    	        			             /* Do something with node n*/
	    	        			    	        			            	
	    	        			    	        			            	if(numl.getNumber()==num.getNumber())
	    	        			    	        			            	{
	    	        			    	        			            		ans[0] = "Yes";
	    	        			    	        			            	}
	    	        			    	        			            }
	    	        			    	        			        };
	    	        			    	        			        
	    	        			    	        			        PointsToSet ptsl = pta.reachingObjects(jlcomp);
	    	        			    	        					
	    	        			    	        					PointsToSetInternal ptil = (PointsToSetInternal) ptsl;
	    	        			    	        					
	    	        			    	        					ptil.forall(verifyl);				
	    	        			        						}
	    	        			        						
	    	        			        						else if(compst.getLeftOp() instanceof JInstanceFieldRef)
	    	        			        						{
	    	        			        							JInstanceFieldRef instf = (JInstanceFieldRef) compst.getLeftOp();
	    	        			        							
	    	        			        							SootField instf_field = (SootField) instf.getField();
	    	        			        							
	    	        			        							JimpleLocal jlcomp = (JimpleLocal) instf.getBase();
	    	        			        							
	    	        			        							P2SetVisitor verifyl = new P2SetVisitor()
	    	        			    	        					{

	    	        			    	        			            @Override
	    	        			    	        			            public void visit(Node numl)
	    	        			    	        			            {
	    	        			    	        			             /* Do something with node n*/
	    	        			    	        			            	
	    	        			    	        			            	if(numl.getNumber()==num.getNumber())
	    	        			    	        			            	{
	    	        			    	        			            		ans[0] = "Yes";
	    	        			    	        			            	}
	    	        			    	        			            }
	    	        			    	        			        };
	    	        			    	        			        
	    	        			    	        			        PointsToSet ptsl = pta.reachingObjects(jlcomp,instf_field);
	    	        			    	        					
	    	        			    	        					PointsToSetInternal ptil = (PointsToSetInternal) ptsl;
	    	        			    	        					
	    	        			    	        					ptil.forall(verifyl);				
	    	        			        						}
	    	        			        						
	    	        			        						if(compst.getRightOp() instanceof JimpleLocal)
	    	        			        						{
	    	        			        							JimpleLocal jrcomp = (JimpleLocal) compst.getRightOp();
	    	        			        							
	    	        			        							P2SetVisitor verifyr = new P2SetVisitor()
	    	        			    	        					{

	    	        			    	        			            @Override
	    	        			    	        			            public void visit(Node numr)
	    	        			    	        			            {
	    	        			    	        			             /* Do something with node n*/
	    	        			    	        			            	
	    	        			    	        			            	if(numr.getNumber()==num.getNumber())
	    	        			    	        			            	{
	    	        			    	        			            		ans[0] = "Yes";
	    	        			    	        			            	}
	    	        			    	        			            }
	    	        			    	        			        };
	    	        			    	        			        
	    	        			    	        			        PointsToSet ptsr = pta.reachingObjects(jrcomp);
	    	        			    	        					
	    	        			    	        					PointsToSetInternal ptir = (PointsToSetInternal) ptsr;
	    	        			    	        					
	    	        			    	        					ptir.forall(verifyr);				
	    	        			        						}
	    	        			        						
	    	        			        						else if(compst.getRightOp() instanceof JInstanceFieldRef)
	    	        			        						{
	    	        			        							JInstanceFieldRef instf = (JInstanceFieldRef) compst.getRightOp();
	    	        			        							
	    	        			        							SootField instf_field = (SootField) instf.getField();
	    	        			        							
	    	        			        							JimpleLocal jrcomp = (JimpleLocal) instf.getBase();
	    	        			        							
	    	        			        							P2SetVisitor verifyr = new P2SetVisitor()
	    	        			    	        					{

	    	        			    	        			            @Override
	    	        			    	        			            public void visit(Node numr)
	    	        			    	        			            {
	    	        			    	        			             /* Do something with node n*/
	    	        			    	        			            	
	    	        			    	        			            	if(numr.getNumber()==num.getNumber())
	    	        			    	        			            	{
	    	        			    	        			            		ans[0] = "Yes";
	    	        			    	        			            	}
	    	        			    	        			            }
	    	        			    	        			        };
	    	        			    	        			        
	    	        			    	        			        PointsToSet ptsr = pta.reachingObjects(jrcomp,instf_field);
	    	        			    	        					
	    	        			    	        					PointsToSetInternal ptir = (PointsToSetInternal) ptsr;
	    	        			    	        					
	    	        			    	        					ptir.forall(verifyr);				
	    	        			        						}
	    	        			        						
	    	        			        					}
	    	        			        						
	    	        			                		}
	    	        			            			
	    	        			            		}
	    	        			            	}
	    	        			            }
	    	        			        };
	    	        			        
	    	        			        PointsToSet pts2 = pta.reachingObjects(jl);
	    	        					
	    	        					PointsToSetInternal pti2 = (PointsToSetInternal) pts2;
	    	        					
	    	        					pti2.forall(verify);				
	        						}
	        						
	        						else if(st.getLeftOp() instanceof JInstanceFieldRef)
	        						{
	        							JInstanceFieldRef instfa = (JInstanceFieldRef) st.getLeftOp();
	        							
	        							SootField instf_fielda = (SootField) instfa.getField();
	        							
	        							JimpleLocal jl = (JimpleLocal) instfa.getBase();
	        							
	        							P2SetVisitor verify = new P2SetVisitor()
	    	        					{

	    	        			            @Override
	    	        			            public void visit(Node num)
	    	        			            {
	    	        			             /* Do something with node n*/
	    	        			            	
	    	        			            	//System.out.println("Checking num "+ num.getNumber() +"\n");
	    	        			            	
	    	        			            	if(num.getNumber()==n.getNumber())
	    	        			            	{
	    	        			            		for(PEGNode compnode:pnode.Mset)
	    	        			            		{
	    	        			            			
	    	        			            			//System.out.println("Checking compnode "+ compnode.u +"\n");
	    	        			            			
	    	        			            			if(compnode.nodetype==1)
	    	        			                		{
	    	        			                			if(compnode.u instanceof JAssignStmt)
	    	        			        					{
	    	        			        						JAssignStmt compst = (JAssignStmt) compnode.u;
	    	        			        						
	    	        			        						if(compst.getLeftOp() instanceof JimpleLocal)
	    	        			        						{
	    	        			        							JimpleLocal jlcomp = (JimpleLocal) compst.getLeftOp();
	    	        			        							
	    	        			        							P2SetVisitor verifyl = new P2SetVisitor()
	    	        			    	        					{

	    	        			    	        			            @Override
	    	        			    	        			            public void visit(Node numl)
	    	        			    	        			            {
	    	        			    	        			             /* Do something with node n*/
	    	        			    	        			            	
	    	        			    	        			            	if(numl.getNumber()==num.getNumber())
	    	        			    	        			            	{
	    	        			    	        			            		ans[0] = "Yes";
	    	        			    	        			            	}
	    	        			    	        			            }
	    	        			    	        			        };
	    	        			    	        			        
	    	        			    	        			        PointsToSet ptsl = pta.reachingObjects(jlcomp);
	    	        			    	        					
	    	        			    	        					PointsToSetInternal ptil = (PointsToSetInternal) ptsl;
	    	        			    	        					
	    	        			    	        					ptil.forall(verifyl);				
	    	        			        						}
	    	        			        						
	    	        			        						else if(compst.getLeftOp() instanceof JInstanceFieldRef)
	    	        			        						{
	    	        			        							JInstanceFieldRef instf = (JInstanceFieldRef) compst.getLeftOp();
	    	        			        							
	    	        			        							SootField instf_field = (SootField) instf.getField();
	    	        			        							
	    	        			        							JimpleLocal jlcomp = (JimpleLocal) instf.getBase();
	    	        			        							
	    	        			        							P2SetVisitor verifyl = new P2SetVisitor()
	    	        			    	        					{

	    	        			    	        			            @Override
	    	        			    	        			            public void visit(Node numl)
	    	        			    	        			            {
	    	        			    	        			             /* Do something with node n*/
	    	        			    	        			            	
	    	        			    	        			            	if(numl.getNumber()==num.getNumber())
	    	        			    	        			            	{
	    	        			    	        			            		ans[0] = "Yes";
	    	        			    	        			            	}
	    	        			    	        			            }
	    	        			    	        			        };
	    	        			    	        			        
	    	        			    	        			        PointsToSet ptsl = pta.reachingObjects(jlcomp,instf_field);
	    	        			    	        					
	    	        			    	        					PointsToSetInternal ptil = (PointsToSetInternal) ptsl;
	    	        			    	        					
	    	        			    	        					ptil.forall(verifyl);				
	    	        			        						}
	    	        			        						
	    	        			        						if(compst.getRightOp() instanceof JimpleLocal)
	    	        			        						{
	    	        			        							JimpleLocal jrcomp = (JimpleLocal) compst.getRightOp();
	    	        			        							
	    	        			        							P2SetVisitor verifyr = new P2SetVisitor()
	    	        			    	        					{

	    	        			    	        			            @Override
	    	        			    	        			            public void visit(Node numr)
	    	        			    	        			            {
	    	        			    	        			             /* Do something with node n*/
	    	        			    	        			            	
	    	        			    	        			            	if(numr.getNumber()==num.getNumber())
	    	        			    	        			            	{
	    	        			    	        			            		ans[0] = "Yes";
	    	        			    	        			            	}
	    	        			    	        			            }
	    	        			    	        			        };
	    	        			    	        			        
	    	        			    	        			        PointsToSet ptsr = pta.reachingObjects(jrcomp);
	    	        			    	        					
	    	        			    	        					PointsToSetInternal ptir = (PointsToSetInternal) ptsr;
	    	        			    	        					
	    	        			    	        					ptir.forall(verifyr);				
	    	        			        						}
	    	        			        						
	    	        			        						else if(compst.getRightOp() instanceof JInstanceFieldRef)
	    	        			        						{
	    	        			        							JInstanceFieldRef instf = (JInstanceFieldRef) compst.getRightOp();
	    	        			        							
	    	        			        							SootField instf_field = (SootField) instf.getField();
	    	        			        							
	    	        			        							JimpleLocal jrcomp = (JimpleLocal) instf.getBase();
	    	        			        							
	    	        			        							P2SetVisitor verifyr = new P2SetVisitor()
	    	        			    	        					{

	    	        			    	        			            @Override
	    	        			    	        			            public void visit(Node numr)
	    	        			    	        			            {
	    	        			    	        			             /* Do something with node n*/
	    	        			    	        			            	
	    	        			    	        			            	if(numr.getNumber()==num.getNumber())
	    	        			    	        			            	{
	    	        			    	        			            		ans[0] = "Yes";
	    	        			    	        			            	}
	    	        			    	        			            }
	    	        			    	        			        };
	    	        			    	        			        
	    	        			    	        			        PointsToSet ptsr = pta.reachingObjects(jrcomp,instf_field);
	    	        			    	        					
	    	        			    	        					PointsToSetInternal ptir = (PointsToSetInternal) ptsr;
	    	        			    	        					
	    	        			    	        					ptir.forall(verifyr);				
	    	        			        						}
	    	        			        						
	    	        			        					}
	    	        			        						
	    	        			                		}
	    	        			            			
	    	        			            		}
	    	        			            	}
	    	        			            }
	    	        			        };
	    	        			        
	    	        			        PointsToSet pts2 = pta.reachingObjects(jl,instf_fielda);
	    	        					
	    	        					PointsToSetInternal pti2 = (PointsToSetInternal) pts2;
	    	        					
	    	        					pti2.forall(verify);				
	        						}
	        						
	        					}
	        						
	                		}
	                		
	                		for(PEGNode an:pnode.outEdges_internal)
	                		{
	                			dfslist2.add(an);
	                		}
	                		
	                		for(PEGNode an:pnode.outEdges_external)
	                		{
	                			dfslist2.add(an);
	                		}
	                		
	                	}
	                }
	            }
	        };
	        
	        PointsToSet pts = pta.reachingObjects(currVar,currField);
			
			PointsToSetInternal pti = (PointsToSetInternal) pts;
			
			pti.forall(getAns);
			
			A3.answers[i] = ans[0];
		}
        
		
		
	}	
}

class PEGNode
{
	public int obj; //Self is referred as -1
	public int refers;
	public SootMethod m;
	public int nodetype; //1 is normal, 2 is begin, 3 is start, 4 is entry, 5 is exit, 6 is wait, 7 is waiting, 8 is notified entry, 9 is notify, 10 is notifyall, 11 is join
	public Unit u;
	public int threadobj; //Main Thread has obj_id 0
	public LinkedHashSet<PEGNode> outEdges_internal;
	public LinkedHashSet<PEGNode> outEdges_external;
	public LinkedHashSet<PEGNode> inEdges;
	public LinkedHashSet<PEGNode> inEdges_external;
	
	public LinkedHashSet<PEGNode> Mset;
	public LinkedHashSet<PEGNode> OUTset;
	public LinkedHashSet<PEGNode> GENset;
	public LinkedHashSet<PEGNode> KILLset;
	
	public PEGNode()
	{
		outEdges_internal = new LinkedHashSet<PEGNode>();
		outEdges_external = new LinkedHashSet<PEGNode>();
		inEdges = new LinkedHashSet<PEGNode>();
		inEdges_external = new LinkedHashSet<PEGNode>();
		
		Mset = new LinkedHashSet<PEGNode>();
		OUTset = new LinkedHashSet<PEGNode>();
		GENset = new LinkedHashSet<PEGNode>();
		KILLset = new LinkedHashSet<PEGNode>();
		
		obj=-1;
	}
}

class MethodListNode
{
	public int obj;
	public SootMethod m;
	public PEGNode basenode;
}
