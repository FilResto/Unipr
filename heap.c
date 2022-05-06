#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <math.h>
#include <iostream>
#include <fstream>

using namespace std;

// compilation: g++ -xc++ heap.c 
//
// Target:
// 1) full tree representation analysis <---> array
// 2) heap insert implementation OK
// 3) maximum extraction with function "heapify" (descent of the minimum value from the root)


int ct_swap=0;
int ct_cmp=0;
int ct_op=0;  /// Searching operations

int max_dim=0;
int ntests=1;
int ndiv=1;
int details=0;
int graph=0;


int n=0; /// Array size

/// output file for the graph
ofstream output_graph;
int n_operazione=0; /// operations counter to view the various steps

const int MAX_SIZE=256;  /// static allocation
int heap[MAX_SIZE];
int heap_size=0;   /// current heap size

/// using -1 to indicate a non-existent index
int parent_idx(int n){
  if (n==0)
    return -1;
  return (n-1)/2;
}

int child_L_idx(int n){
  if (2*n+1>=heap_size)
    return -1;
  return 2*n+1;
}

int child_R_idx(int n){
  if (2*n+2>=heap_size)
    return -1;
  return 2*n+2;
}

/// returns 0 if the node in position n is an internal node (at least one child)
/// returns 1 if the node doen't have children
int is_leaf(int n){
  return ( child_L_idx(n)==-1 );  // there is no need to check on son R

  /* equivalent version
  if (child_L_idx(n)==-1)
    return 1;
  return 0;
  */
  
}


/// print the node code for dot
void print_node_code(int n){
  output_graph << "node_" << n << "_" << n_operazione;
}

void node_print_graph(int n){
  if (details)
    printf("Print on graph node %d\n",n);
  print_node_code(n);
  output_graph << "\n[label=<\n<TABLE BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\" CELLPADDING=\"4\" >\n<TR> <TD CELLPADDING=\"3\" BORDER=\"0\"  ALIGN=\"LEFT\" bgcolor=\"#f0f0f0\" PORT=\"id\">";
  output_graph << n << "</TD> </TR><TR>\n<TD PORT=\"val\" bgcolor=\"#a0FFa0\">";
  output_graph << heap[n] << "</TD>\n</TR></TABLE>>];\n";

  /// view children on the same plane
  if (child_L_idx(n)!=-1 && child_R_idx(n)!=-1){
    output_graph << "rank = same; ";
    print_node_code(child_L_idx(n));
    output_graph <<";";
    print_node_code(child_R_idx(n));
    output_graph  <<";\n";
  }

  // I show outgoing arcs
  
  if (child_L_idx(n)!=-1){ /// draw arco left
    print_node_code(n);
    output_graph  << " -> ";
    print_node_code(child_L_idx(n));
    output_graph  <<":id ;\n";
  }

  if (child_R_idx(n)!=-1){ /// draw arco R
    print_node_code(n);
    output_graph << " -> ";
    print_node_code(child_R_idx(n));
    output_graph <<":id ;\n";
  }
  
}

void tree_print_rec_graph(int n){
  if (n!=-1){
    node_print_graph(n);
    tree_print_rec_graph(child_L_idx(n));
    tree_print_rec_graph(child_R_idx(n));
  }
}

void tree_print_graph(int n){
  /// recursive node printing
  tree_print_rec_graph(n);
  n_operazione++;

}


void node_print(int n){
  if (n == -1)
    printf("empty node\n");  
  else
    printf("allocated in %d [Val: %d, L: %d, R: %d]\n",
	   n,
	   heap[n],
	   child_L_idx(n),
	   child_R_idx(n));  
}

void heap_insert_min(int elem){
  if (details)
    printf("Inserting element %d in place %d\n",elem,heap_size);
  
  if (heap_size<MAX_SIZE){
    int i=heap_size;
    heap_size++;
    
    heap[i]=elem;

    while (i!=0){ // I'm not on the root
      if (heap[ parent_idx(i) ] <= heap[i]){ /// property of heap_min is respected -> I quit
	if (details)
	  printf("The parent has value %d >= of the node %d, exit\n",heap[ parent_idx(i) ],heap[i]);
	return;
      }

      if (details)
	printf("The parent has value %d < of the node %d, swap\n",heap[ parent_idx(i) ],heap[i]);
      /// the node definitely has a parent <     ----> swap
      int tmp=heap[i];
      heap[i]= heap[parent_idx(i)];
      heap[parent_idx(i)]=tmp;

      i=parent_idx(i);      
    }
    
  }
  else
    printf("Heap full!\n");
  
}


void decrease_key(int indice_nodo, int key){
  //key = nuovo valore

  if (indice_nodo<0 || indice_nodo>=heap_size){
    printf("Node not exixs\n");
    return;
  }
  
  if (heap[indice_nodo]< key){
    printf("the key is bigger!\n");
    return;
  }

  heap[indice_nodo] = key;

  int i=indice_nodo;
  while (i!=0){ // I'm not on the root
    if (heap[ parent_idx(i) ] <  heap[i]){ /// property of heap is respected -> I quit
      if (details)
	printf("The parent has value %d >= of the node %d, esco\n",heap[ parent_idx(i) ],heap[i]);
      return;
    }

    if (details)
      printf("The parent has value %d < of the node %d, swap\n",heap[ parent_idx(i) ],heap[i]);
    /// the node definitely has a parent <   --> swap
    int t=heap[ parent_idx(i) ];
    heap[ parent_idx(i) ]= heap[i];
    heap[i]=t;

    i=parent_idx(i);      
  }

  
}




int heap_remove_min(){

  if (heap_size<=0){   /// heap empty!
    printf("Errore: heap empty\n");
    return -1;
  }
  
  int minimo = heap[0];

  if (details)
    printf("Minimum identified %d\n",minimo);
  /// I exchange the root with the last leaf on the right
  /// the minimum has been moved to the bottom -> ready for elimination
  int t=heap[0];heap[0]=heap[heap_size-1];heap[heap_size-1]=t;

  // I delete the minimum (now at the bottom of the array)
  heap_size--;

  //    tree_print_graph(0);  // root 
  //  n_operazione++;
  
  
  /// in the root there is a small value (minimum?)
  int i=0; // working index (I start from the root)

  while (!is_leaf(i)){ /// I guarantee to stop at the leaf

    if (details)
      printf("Working with the node in place i = %d, value %d\n",i,heap[i]);
    
    int con_chi_mi_scambio=-1;
    
    /// I check node i with his son L
    if ( heap[child_L_idx(i)] < heap[i]){  // node i is smaller
      /// activate a swap (the heap property is not respected)
      con_chi_mi_scambio = child_L_idx(i);
      if (details)
	printf("Child L is smaller (value %d)\n",heap[child_L_idx(i)]);

      if (child_R_idx(i)>=0 && // right node exists
	  heap[child_R_idx(i)] < heap[child_L_idx(i)]){
	con_chi_mi_scambio = child_R_idx(i);
	if (details)
	  printf("Child R is even smaller (value %d)\n",heap[child_R_idx(i)]);
      }
    }
    else{ // now I check in the son on the right, because the node is smaller than the son L

      if (child_R_idx(i)>=0){ // son R exists
	if (heap[child_R_idx(i)] < heap[i]){  /// Enabling swap
	  con_chi_mi_scambio = child_R_idx(i);
	  if (details)
	    printf("Child R is smaller than the node (value %d)\n",heap[child_R_idx(i)]);
	}
	else
	  break;
      }
      else
	break;
    }

    /// swap between i and con_chi_mi_scambio
    int t=heap[i];heap[i]=heap[con_chi_mi_scambio];heap[con_chi_mi_scambio]=t;

    i=con_chi_mi_scambio;
    
    //tree_print_graph(0);  // root 
    //n_operazione++;
    
  }

  return minimo;
}



int parse_cmd(int argc, char **argv){
  /// check arguments
  int ok_parse=0;
  for (int i=1;i<argc;i++){
    if (argv[i][1]=='v'){
      details=1;
      ok_parse=1;
    }
    if (argv[i][1]=='g'){
      graph=1;
      ok_parse=1;
    }
  }

  if (argc > 1 && !ok_parse) {
    printf("Usage: %s [Options]\n",argv[0]);
    printf("Options:\n");
    printf("  -verbose: Enable printouts when running the algorithm\n");
    printf("  -graph: dot file creation with the execution graph (power d=1 t=1)\n");
    return 1;
  }

  return 0;
}

int main(int argc, char **argv) {
  int i,test;

  if (parse_cmd(argc,argv))
    return 1;

  // init random
  srand((unsigned) time(NULL));

  if (graph){
    output_graph.open("graph.dot");
    /// preparing header
    output_graph << "digraph g"<<endl; 
    output_graph << "{ "<<endl;
    output_graph << "node [shape=none]"<<endl;
    output_graph << "rankdir=\"TB\""<<endl;;
    output_graph << "edge[tailclip=false,arrowtail=dot];"<<endl;    
  }
  
  

  for (int i=0;i<32;i++){
       heap_insert_min(rand()%100);
    // heap_insert_min(10+i);
  }
    
  tree_print_graph(0);  // rooy 
  n_operazione++;

  //increase_key(3,20);
  decrease_key(31,3);

  tree_print_graph(0);  // root 
  n_operazione++;

  
   for (int i=0;i<32;i++){
    int valore = heap_remove_min();
    printf("The min value extracted is %d\n",valore);

    tree_print_graph(0);  // root 
    n_operazione++;
  }
  
  
  
  // Displaying the array --> heapsort!
  for (int i=0;i<32;i++){
    printf("%d ",heap[i]);
  }
  printf("\n");
    
  if (graph){
    /// preparing footer and closing the file
    output_graph << "}"<<endl; 
    output_graph.close();
    cout << " File graph.dot written" << endl<< "Create the graph with: dot graph.dot -Tpdf -o graph.pdf"<<endl;
  }



  return 0;
}
