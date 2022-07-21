from __future__ import annotations
from abc import abstractmethod
from re import S
import sys
from typing import Set
from xmlrpc.client import boolean
from pymjc.back import assem, flowgraph, graph
from pymjc.front import frame, temp

from collections import deque #import for nodestack

class RegAlloc (temp.TempMap):
    def __init__(self, frame: frame.Frame, instr_list: assem.InstrList):
        self.frame: frame.Frame = frame
        self.instrs: assem.InstrList = instr_list
        
        self.preColoredNodes: set[graph.Node] = set()
        self.normalColoredNodes: set[graph.Node] = set()
        self.initialNodes: set[graph.Node] = set()
        self.spillNodes: set[graph.Node] = set()
        self.coalesceNodes: set[graph.Node] = set()

        #pilha de nós oara coloração
        self.nodeStack = deque()

        #Worklists
        self.simplifyWorkList: set[graph.Node] = set()
        self.freezeWorkList: set[graph.Node] = set()
        self.spillWorkList: set[graph.Node] = set()

        #nós Move
        self.coalesceMoveNodes: set[graph.Node] = set()
        self.constrainMoveNodes: set[graph.Node] = set()
        self.freezeMoveNodes: set[graph.Node] = set()
        self.worklistMoveNodes: set[graph.Node] = set()
        self.activeMoveNodes: set[graph.Node] = set()


        self.spillCost: dict[graph.Node, int] = {}
        self.adjacenceSets: dict[Edge] = {}
        self.adjacenceList: dict[graph.Node, set[graph.Node] ] ={}

        self.livenessOutput: Liveness = None
        self.assemFlowGraph: flowgraph.AssemFlowGraph = None

        self.moveNodesList: dict[graph.Node, set[graph.Node] ] = {}

        self.nodeDegreeTable: dict[graph.Node, int ] = {}
        self.nodeAliasTable: dict[graph.Node, graph.Node] = {}
        self.nodeColorTable: dict[graph.Node, graph.Node] = {}

        self.generatedSpillTemps: set[temp.Temp] = set()

        self.main_procedure()

    def temp_map(self, temp: temp.Temp) -> str:
        str = self.frame.temp_map(temp)

        if(str is None):
            str = self.frame.temp_map(self.livenessOutput.gtemp(self.nodeColorTable.get(self.livenessOutput.tnode(temp))))
        
        return temp.to_string()

    def main_procedure(self):

        while True:
            shallContinue = False
            self.liveness_analysis()
            self.init()
            self.build()
            self.make_work_list()

            while True:
                if(len(self.simplifyWorkList) != 0):
                    self.simplify()
                elif(len(self.worklistMoveNodes) != 0):
                    self.coalesce()
                elif(len(self.freezeWorkList) != 0):
                    self.freeze()
                elif(len(self.spillWorkList) != 0):
                    self.select_spill()

                if not(len(self.simplifyWorkList) != 0 or len(self.worklistMoveNodes) != 0 or len(self.freezeWorkList) != 0 or len(self.spillWorkList) != 0):
                    break
            self.assign_colors()

            if(len(self.spillNodes) != 0):
                self.rewrite_program() 
                shallContinue = True

            if not shallContinue:
                break 
        self.final_step()    

    def liveness_analysis(self):
        self.assemFlowGraph = self.instrs

        self.livenessOutput = self.assemFlowGraph
    
    def init(self):

        self.preColoredNodes.clear()
        self.normalColoredNodes.clear()

        self.initialNodes.clear()
        self.spillNodes.clear()
        self.coalesceNodes.clear()

        #pilha de nós oara coloração
        self.nodeStack = deque()

        #Worklists
        self.simplifyWorkList.clear()
        self.freezeWorkList.clear()
        self.spillWorkList.clear()

        #nós Move
        self.coalesceMoveNodes.clear()
        self.constrainMoveNodes.clear()
        self.freezeMoveNodes.clear()
        self.activeMoveNodes.clear()

        self.spillCost.clear()

        self.adjacenceSets.clear()
        self.adjacenceList.clear()

        self.moveNodesList.clear()

        self.nodeDegreeTable.clear()
        self.nodeAliasTable.clear()
        self.nodeColorTable.clear()


        counter = 0

        MAX_VALUE: int = sys.maxsize

        while( counter < len(self.frame.registers())):

            temp: temp.Temp = self.frame.registers()[counter]
            node = graph.Node = self.livenessOutput.tnode(temp)

            self.preColoredNodes.add(node)
            self.spillCost[node] = MAX_VALUE

            self.nodeColorTable[node] = node
            self.nodeDegreeTable[node] = 0
            
            counter+=1

        nodeList: graph.NodeList = self.livenessOutput.nodes()

        while(nodeList is not None):
            node: graph.Node = nodeList.head

            if(not(self.preColoredNodes.__contains__(node))):
                self.initialNodes.add(node)

                if(self.generatedSpillTemps.__contains__(self.livenessOutput.gtemp(node))):
                    self.spillCost[node] = MAX_VALUE
                elif(not(self.preColoredNodes.__contains__(node))):
                    self.spillCost[node] = 1    

                self.nodeDegreeTable[node] = 0

            nodeList = nodeList.tail  
    
    def build(self):
        nodeList: graph.NodeList = self.assemFlowGraph.nodes()

        while(nodeList is not None):

            node: graph.Node = nodeList.head

            live : set[temp.Temp] = self.livenessOutput.out(node)

            isMoveInstruction: bool = self.assemFlowGraph.is_move(node)

            if(isMoveInstruction):
                uses: temp.TempList = self.assemFlowGraph.use(node)

                while(uses is not None):
                    live.remove(uses.head)
                    uses = uses.tail
                
                uses: temp.TempList = self.assemFlowGraph.use(node)

                while(uses is not None):
                    self.moveNodesList(self.livenessOutput.tnode(uses.head))[node] = node ##adicionar nó ao hashtable
                    uses = uses.tail

                #...


                self.worklistMoveNodes.add(node)

            defs: temp.TempList = self.assemFlowGraph.deff(node)

            while(defs is not None):
                live.add(defs.head)  

                defs = defs.tail  

            defs: temp.TempList = self.assemFlowGraph.deff(node)

            while(defs is not None):
                
                for live_temp in live:
                    self.add_edge(live_temp, defs.head) #implementar add_edge

                defs = defs.tail 

            nodeList = nodeList.tail

    def make_work_list(self):
        K: int = len(self.preColoredNodes)

        nodeIterator = iter(self.initialNodes)
       

        while(next(nodeIterator, None) is not None):
            n: graph.Node = next(nodeIterator)

            self.initialNodes.remove(nodeIterator)  

            if(self.nodeDegreeTable(n) >= K):
                self.spillWorkList.add(n)
            elif(self.MoveRelated(n)): ##implementar o metodo
                self.freezeWorkList.add(n)
            else:
                self.simplifyWorkList.add(n)    

    def simplify(self):
        temporaryIterator = iter(self.simplifyWorkList)
        n: graph.Node = next(temporaryIterator)

        self.simplifyWorkList.remove(temporaryIterator)
        
        self.nodeStack.appendleft(n)
        
        for no in n.adj:
            self.DecrementDegree(no)

    def freeze(self): 
        pass
    
    def coalesce(self): 
        pass 
    
    def select_spill(self): 
        pass

class Color(temp.TempMap):
    def __init__(self, ig: InterferenceGraph, initial: temp.TempMap, registers: temp.TempList):
        #TODO
        pass
    
    def spills(self) -> temp.TempList:
        #TODO
        return None

    def temp_map(self, temp: temp.Temp) -> str:
        #TODO
        return temp.to_string()

class InterferenceGraph(graph.Graph):
    
    @abstractmethod
    def tnode(self, temp:temp.Temp) -> graph.Node:
        pass

    @abstractmethod
    def gtemp(self, node: graph.Node) -> temp.Temp:
        pass

    @abstractmethod
    def moves(self) -> MoveList:
        pass
    
    def spill_cost(self, node: graph.Node) -> int:
      return 1


class Liveness (InterferenceGraph):

    def __init__(self, flow: flowgraph.FlowGraph):
        self.live_map = {}
        
        #Flow Graph
        self.flowgraph: flowgraph.FlowGraph = flow
        
        #IN, OUT, GEN, and KILL map tables
        #The table maps complies with: <Node, Set[Temp]>
        self.in_node_table = {}
        self.out_node_table = {}
        self.gen_node_table = {}
        self.kill_node_table = {}

        #Util map tables
        #<Node, Temp>
        self.rev_node_table = {}
        #<Temp, Node>
        self.map_node_table = {}
        
        #Move list
        self.move_list: MoveList = None

        self.build_gen_and_kill()
        self.build_in_and_out()
        self.build_interference_graph()
    
    def add_edge(self, source_node: graph.Node, destiny_node: graph.Node):
        if (source_node is not destiny_node and not destiny_node.comes_from(source_node) and not source_node.comes_from(destiny_node)):
            super().add_edge(source_node, destiny_node)

    def show(self, out_path: str) -> None:
        if out_path is not None:
            sys.stdout = open(out_path, 'w')   
        node_list: graph.NodeList = self.nodes()
        while(node_list is not None):
            temp: temp.Temp = self.rev_node_table.get(node_list.head)
            print(temp + ": [ ")
            adjs: graph.NodeList = node_list.head.adj()
            while(adjs is not None):
                print(self.rev_node_table.get(adjs.head) + " ")
                adjs = adjs.tail

            print("]")
            node_list = node_list.tail
    
    def get_node(self, temp: temp.Temp) -> graph.Node:
      requested_node: graph.Node = self.map_node_table.get(temp)
      if (requested_node is None):
          requested_node = self.new_node()
          self.map_node_table[temp] = requested_node
          self.rev_node_table[requested_node] = temp

      return requested_node

    def node_handler(self, node: graph.Node):
        def_temp_list: temp.TempList = self.flowgraph.deff(node)
        while(def_temp_list is not None):
            got_node: graph.Node  = self.get_node(def_temp_list.head)

            for live_out in self.out_node_table.get(node):
                current_live_out = self.get_node(live_out)
                self.add_edge(got_node, current_live_out)

            def_temp_list = def_temp_list.tail

  
    def move_handler(self, node: graph.Node):
        source_node: graph.Node  = self.get_node(self.flowgraph.use(node).head)
        destiny_node: graph.Node = self.get_node(self.flowgraph.deff(node).head)

        self.move_list = MoveList(source_node, destiny_node, self.move_list)
    
        for temp in self.out_node_table.get(node):
            got_node: graph.Node = self.get_node(temp)
            if (got_node is not source_node ):
                self.addEdge(destiny_node, got_node)


    def out(self, node: graph.Node) -> Set[temp.Temp]:
        temp_set = self.out_node_table.get(node)
        return temp_set


    def tnode(self, temp:temp.Temp) -> graph.Node:
        node: graph.Node = self.map_node_table.get(temp)
        if (node is None ):
            node = self.new_node()
            self.map_node_table[temp] = node
            self.rev_node_table[node] = temp
        
        return node

    def gtemp(self, node: graph.Node) -> temp.Temp:
        temp: temp.Temp = self.rev_node_table.get(node)
        return temp

    def moves(self) -> MoveList:
        return self.move_list

    def build_gen_and_kill(self):
        nodeList: temp.TempList = self.flowgraph.nodes()

        while(nodeList is not None):
            # adição a Gen
            aux : temp.TempList = self.flowgraph.use(nodeList.head)
            while(aux is not None):
                temp_gen: temp.Temp = aux.head
                self.get_node(temp_gen)
                aux = aux.tail
            
            # adição a kill
            aux2: temp.TempList = self.flowgraph.deff(nodeList.head)
            while(aux2 is not None):
                temp_kill: temp.Temp = aux.head
                self.get_node(temp_kill)
                aux2 = aux2.tail    

            # atualizando a gen e kill
            self.kill_node_table = [nodeList.head] = temp_kill
            self.gen_node_table = [nodeList.head] = temp_gen
            
            nodeList = nodeList.tail
        

    def build_in_and_out(self):
        #TODO
        pass

    def build_interference_graph(self):
        #TODO
        pass

class Edge():

    edges_table = {}

    def __init__(self):
        super.__init__()
    
    def get_edge(self, origin_node: graph.Node, destiny_node: graph.Node) -> Edge:
        
        origin_table = Edge.edges_table.get(origin_node)
        destiny_table = Edge.edges_table.get(destiny_node)
        
        if (origin_table is None):
            origin_table = {}
            Edge.edges_table[origin_node] = origin_table

        if (destiny_table is None):
            destiny_table = {}
            Edge.edges_table[destiny_node] = destiny_table
        
        requested_edge: Edge  = origin_table.get(destiny_node)

        if(requested_edge is None):
            requested_edge = Edge()
            origin_table[destiny_node] = requested_edge
            destiny_table[origin_node] = requested_edge

        return requested_edge



class MoveList():

   def __init__(self, s: graph.Node, d: graph.Node, t: MoveList):
      self.src: graph.Node = s
      self.dst: graph.Node = d
      self.tail: MoveList = t
