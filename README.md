//Butterfly counting with new algorithm in c++ programming


#define _CRT_SECURE_NO_WARNINGS
#include <iostream>
#include <string>
#include <cstdlib>
#include <algorithm>
#include <cstring>
#include <time.h>
#include <cstdio>
#include <cassert>
#include <cstdio>
#include <stdio.h>
#include <numeric>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <map>
#include <sstream>
#include <boost/random/mersenne_twister.hpp>
#include <boost/random/uniform_int_distribution.hpp>
#include <boost/random/uniform_real_distribution.hpp>
#include <boost/random/random_device.hpp>
#include <boost/variant.hpp>

using namespace std;
using namespace boost::random;

#define SZ(x) ((int)x.size())
#define ll long long
#define ull unsigned long long
#define ld long double
#define eps 1e-11
#define max(x,y) ((x)>(y)?(x):(y))
#define min(x,y) ((x)<(y)?(x):(y))

const int ITER_VER = 2200;
const ll shift = 1000 * 1000 * 1000LL;
const double TIME_LIMIT = 20;
const int N_WEDGE_ITERATIONS = 2 * 1000 * 1000 * 10;
const int ITERATIONS_SAMPLING = 5;
const int N_SPARSIFICATION_ITERATIONS = 5;
const int TIME_LIMIT_SPARSIFICATION = 10000; // !half an hour
const int N_FAST_EDGE_BFC_ITERATIONS = 2100; // used for fast edge sampling
const int N_FAST_WEDGE_ITERATIONS = 50; // used for fast wedge sampling

char input_address[2000], output_address [2000] ;


set < pair <int, int> > edges;
vector < pair <int, int> > list_of_edges;
map < int, int > vertices [2];
vector <int> index_map;
vector <int> vertices_in_left;
vector <int> vertices_in_right;
vector < vector <int> > adj;
vector < vector < int > > sampled_adj_list;
vector <bool> visited;
vector <int> list_of_vertices;
vector <int> vertex_counter;


ll count_wedge;
ll n_vertices;
ll n_edges;
ld exact_n_bf;
ll n_wedge_in_partition[2];
ll largest_index_in_partition[2];

vector <int> clr;
vector <int> hashmap_C;
vector <ll> sum_wedges;
vector <ll> sum_deg_neighbors;
vector <int> aux_array_two_neighboorhood;

void clear_everything() {
	largest_index_in_partition[0] = largest_index_in_partition[1] = 0;
	n_vertices = 0;
	n_edges = 0;
	edges.clear();
	vertices[0].clear(); vertices[1].clear();
	index_map.clear();
	vertices_in_left.clear();
	vertices_in_right.clear();
	adj.clear();
	sampled_adj_list.clear();
	visited.clear();
	list_of_edges.clear();
	vertex_counter.clear();
	clr.clear();
	hashmap_C.clear();
	sum_wedges.clear();
	sum_deg_neighbors.clear();
	aux_array_two_neighboorhood.clear();
}

void resize_all() {
	clr.resize(n_vertices);
	hashmap_C.resize(n_vertices);
	aux_array_two_neighboorhood.resize(n_vertices);
	sum_wedges.resize(n_vertices);
	visited.resize(n_vertices);
	index_map.resize(n_vertices);
	sum_deg_neighbors.resize(n_vertices);
}



void add_vertex(int A, int side) {
	if (vertices[side].find(A) == vertices[side].end()) {
		if (side == 0) vertices_in_left.push_back(A);
		else vertices_in_right.push_back(A);
		vertices[side][A] = 1;
	}
}

void add_edge(int &A, int &B) {
	add_vertex(A, 0);
	add_vertex(B, 1);
	if (edges.find(make_pair(A, B)) == edges.end()) {
		edges.insert(make_pair(A, B));
		cout<<"
		n_edges++;
	}
}

void get_index(int &A, int side) {
	if (vertices[side].find(A) == vertices[side].end()) {
		vertices[side][A] = largest_index_in_partition[side] ++ ;
		/*print A and vertices[side][A] to get the generated id for the vertex A*/
		
		
		//cout<<"i am A"<<'\t'<<A<<'\n';
		cout<< A << " " << side << " " << vertices[side][A]<<'\n';		
	}
	A = vertices[side][A];
}

bool all_num(string &s) {
	for (int i = 0; i < SZ(s); i++) if ((s[i] >= '0' && s [i] <= '9') == false) return false;
	return true;
}

void get_graph() {
	freopen(input_address, "r", stdin); //tries to open a file with a file stream that is associated with another opened file.
	string s;
	cin.clear(); //clears the error flag on cin 
	while (getline(cin, s)) { //to read a string or a line from an input stream
 		stringstream ss; ss << s; //A stringstream associates a string object with a stream allowing you to read from the string as if it were a stream (like cin). To use stringstream, we need to include sstream header file.
 		
		vector <string> vec_str; 
		for (string z; ss >> z; vec_str.push_back(z));//push elements into a vector from the back
		if (SZ(vec_str) >= 2) {
			bool is_all_num = true;
			for (int i = 0; i < min (2, SZ(vec_str)) ; i++) is_all_num &= all_num(vec_str[i]);
			if (is_all_num) {
				int A, B;
				ss.clear(); ss << vec_str[0]; ss >> A;
				ss.clear(); ss << vec_str[1]; ss >> B;
				add_edge(A, B);
			}
		}
	}
	vertices[0].clear();
	vertices[1].clear();
	largest_index_in_partition[0] = 0;
	largest_index_in_partition[1] = SZ(vertices_in_left);
	n_vertices = SZ(vertices_in_left) + SZ(vertices_in_right);
	adj.resize(n_vertices, vector <int> ());
	for (auto edge : edges) {
		int A = edge.first;
		int B = edge.second;
		get_index(A, 0);
		get_index(B, 1);
		adj[A].push_back(B);
		adj[B].push_back(A);
		list_of_edges.push_back(make_pair(A, B));
	}
	resize_all();

	n_wedge_in_partition[0] = 0;
	for (int i = 0; i < largest_index_in_partition[0]; i++) {
		n_wedge_in_partition[0] += (((ll)SZ(adj[i])) * (SZ(adj[i]) - 1)) >> 1;
	}
	n_wedge_in_partition[1] = 0;
	for (int i = largest_index_in_partition[0]; i < largest_index_in_partition[1]; i++) {
		n_wedge_in_partition[1] += ((ll)SZ(adj[i]) * (SZ(adj[i]) - 1)) >> 1;
	}
	for (int i = 0; i < n_vertices; i++) {
		sort(adj[i].begin(), adj[i].end());
		sum_deg_neighbors[i] = 0;
		for (auto neighbor : adj[i]) {
			sum_deg_neighbors[i] += SZ(adj[neighbor]);
		}
	}
	cerr << " for test # edges :: " << SZ(list_of_edges) << " left :: " << SZ(vertices_in_left) << " right :: "  << SZ(vertices_in_right) << endl;
	sort(list_of_edges.begin(), list_of_edges.end());
	fclose(stdin);
}

/*This function returns 1 if priority(u) < priority(v), otherwise it returns 0*/
//int priority(int u, int v){
//}

void read_the_graph() {
	clear_everything();
	cerr << " Insert the input (bipartite network) file location" << endl;
	cerr << " >>> "; cin >> input_address;
	//cerr << " Insert the output file" << endl;
	//cerr << " >>> "; cin >> output_address;
	//freopen(output_address, "w", stdout);
	cerr << " ---------------------------------------------------------------------------------------------------------------------- \n";
	cerr << "| * Note that edges should be separated line by line.\n\
| In each line, the first integer number is considered as a vertex in the left partition of bipartite network, \n\
| and the second integer number is a vertex in the right partition. \n\
| In addition, multiple edges are removed from the given bipartite network.\n\
| Also, note that in this version of the source code, we did NOT remove vertices with degree zero.\n";
	cerr << " ---------------------------------------------------------------------------------------------------------------------- \n";

	cerr << " Processing the graph ... (please wait) \n";

	get_graph();   //function() from 27th line

	cerr << " -------------------------------------------------------------------------- \n";
	cerr << " The graph is processed - there are " << n_vertices << " vertices and " << n_edges << " edges  \n";
	cerr << " -------------------------------------------------------------------------- \n";
}



ll exact_butterfly_counting(vector < vector <int> > &graph) {
ll res=0;
	for(int u=0; u < n_vertices; u++){
		unordered_map<int, int> count_wedge;
		for(int j = 0; j < SZ(graph[u]); j++){
			int v = graph[u][j];
			if(SZ(graph[v]) < SZ(graph[u]) || ((SZ(graph[v]) == SZ(graph[u])) &&(v<u))){
			
				for(int k=0; k < SZ(graph[v]); k++){
					int w = graph[v][k];
					if(SZ(graph[w]) < SZ(graph[u]) ||  ((SZ(graph[w]) == SZ(graph[u])) &&(w<u))) {
						//printf("%d%d%d",u \t,v \t,w);
						//cout<<"this is u"<<'\t'<<u<<'\n'<<"this is v"<<'\t'<<v<<'\n'<<"this is w"<<'\t'<<w<<'\n'<<'\n';
						//cout<<"this is only u"<<u<<'\n';
						count_wedge[w] += 1;
					}
				}
			}
		}
	
	
		for(auto element : count_wedge)
		{
			if(element.second > 1){
			
				int val = element.second;
				res += val*(val-1)/2;
			}
		}
	}
	/*
	for(int u : vertices_in_left){
		unordered_map<int, int> count_wedge;
		for(int j = 0; j < SZ(graph[u]); j++){
			int v = graph[u][j];
			if(SZ(graph[v]) < SZ(graph[u]) || ((SZ(graph[v]) == SZ(graph[u])) &&(v<u))){
			
				for(int k=0; k < SZ(graph[v]); k++){
					int w = graph[v][k];
					if(SZ(graph[w]) < SZ(graph[u]) ||  ((SZ(graph[w]) == SZ(graph[u])) &&(w<u))) {
						count_wedge[w] += 1;
					}
				}
			}
		}
	
	
		for(auto element : count_wedge)
		{
			if(element.second > 1){
			
				int val = element.second;
				res += val*(val-1)/2;
			}
		}
	}

	for(int u : vertices_in_right){
			unordered_map<int, int> count_wedge;
			for(int j = 0; j < SZ(graph[u]); j++){
				int v = graph[u][j];
				if(SZ(graph[v]) < SZ(graph[u]) || ((SZ(graph[v]) == SZ(graph[u])) &&(v<u))){
				
					for(int k=0; k < SZ(graph[v]); k++){
						int w = graph[v][k];
						if(SZ(graph[w]) < SZ(graph[u]) || ((SZ(graph[w]) == SZ(graph[u])) &&(w<u))) {
							count_wedge[w] += 1;
						}
					}
				}
			}
		
		
		for(auto element : count_wedge)
		{
			if(element.second > 1){
			
				int val = element.second;
				res += val*(val-1)/2;
			}
		}
	}*/

return res;
}
		
		

	
	
	

void exact_algorithm_time_tracker(){
	double beg_clock = clock();
	exact_n_bf = exact_butterfly_counting(adj);
	double end_clock = clock();
	double elapsed_time = (end_clock - beg_clock) / CLOCKS_PER_SEC;
	cout << " Exact algorithm is done in " << elapsed_time << " secs. There are " << exact_n_bf << " butterflies." << endl;
}


int main()
{
	std::ios::sync_with_stdio(false);
	read_the_graph();
	exact_algorithm_time_tracker();
}

