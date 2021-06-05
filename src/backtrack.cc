/**
 * @file backtrack.cc
 *
 */

#include "backtrack.h"

Backtrack::Backtrack() {}
Backtrack::~Backtrack() {}

bool is_error = false;				// did error occur?
size_t count = 0;				// # of matches
size_t error = 0;				// # of entering enumerate function
size_t ERROR_LIMIT;				// limit of mismatch
size_t selected = 0;

typedef std::vector<Vertex> vertexVec;
typedef std::pair<Vertex, size_t> vertexSizePair;
typedef std::pair<Vertex, float> vertexFloatPair;

/* Make a new weighted query graph such that
 * given e(u, v) in V(q), w(u, v) = m/|C(u)| and w(v, u) = m/|C(v)| 
 * where m = # of edges between the data vertices in C(u) and C(v) */
std::vector<std::vector<float>> GenerateWeightedQuery(const Graph &data, const Graph &query, const CandidateSet &cs){
	// initialize the weighted query to 0
	std::vector<std::vector<float>> weighted_query(query.GetNumVertices(),
			                   std::vector<float>(query.GetNumVertices(), 0.0f));
	
	// vector which checks the edge between C(u) and C(v) 
	std::vector<int> edge_check(data.GetNumVertices(), 0);

	// set weight : w(u, v) = m/|C(u)| and w(v, u) = m/|C(v)|
	for(size_t u = 0; u < query.GetNumVertices(); ++u){
		// get offset of u's neighbor in adjacent array and |C(u)|
		size_t start_offset = query.GetNeighborStartOffset(u);
		size_t end_offset = query.GetNeighborEndOffset(u);
		size_t size_cand_u = cs.GetCandidateSize(u);
		
		// set 1 in the place in edge_check corresponding to C(u)'s element
		for(size_t ind = 0; ind < size_cand_u; ++ind)
			edge_check[cs.GetCandidate(u, ind)] = 1;
		
		for(size_t i = start_offset; i < end_offset; ++i){
			// get vertex v which is neighbor of u and |C(v)|
			Vertex v = query.GetNeighbor(i);
			size_t size_cand_v = cs.GetCandidateSize(v);
			
			// calculate m
			size_t m = 0;
			for(size_t ind = 0; ind < size_cand_v; ++ind){
				// get C(v)'s element and its neighbor's offset in adjacent array
				Vertex cand_v = cs.GetCandidate(v, ind);
				size_t cand_start_offset = data.GetNeighborStartOffset(cand_v);
				size_t cand_end_offset = data.GetNeighborEndOffset(cand_v);
				
				// If there is an element of C(u) among the neighbors of C(v), m is increased.
				for(size_t k = cand_start_offset; k < cand_end_offset; ++k){
					Vertex cand_v_neighbor = data.GetNeighbor(k);

					if(edge_check[cand_v_neighbor] == 1)
						++m;
				}
			}

			// set weight
			weighted_query[u][v] = ((float)m / size_cand_u);
			weighted_query[v][u] = ((float)m / size_cand_v);	
		}

		// set 0 edge_check for next iteration
		for(size_t ind = 0; ind < size_cand_u; ++ind)
			edge_check[cs.GetCandidate(u, ind)] = 0;
	}
	return weighted_query;
}	

bool compare_size_t(vertexSizePair &a, vertexSizePair &b){
	return a.second < b.second;
}

bool compare_float(vertexFloatPair &a, vertexFloatPair &b){
	return a.second < b.second;
}

// Make core value table for every query vertex
std::vector<size_t> ComputeCoreValue(const Graph &graph){
  
	std::vector<size_t> core_table(graph.GetNumVertices());
	std::vector<vertexSizePair> degree_table(graph.GetNumVertices());
	std::vector<size_t> index_table(graph.GetNumVertices());

	// set degree_table and sort increasing order
	for(size_t i = 0; i < graph.GetNumVertices(); ++i){
		degree_table[i].first = i;
		degree_table[i].second = graph.GetDegree(i);
	}
	sort(degree_table.begin(), degree_table.end(), compare_size_t);

	for(size_t i = 0; i < graph.GetNumVertices(); ++i){
		core_table[degree_table[i].first] = degree_table[i].second;

		size_t start_offset = graph.GetNeighborStartOffset(degree_table[i].first);
		size_t end_offset = graph.GetNeighborEndOffset(degree_table[i].first);

		for(size_t ind = start_offset; ind < end_offset; ++ind){
			for(size_t j = 0; j < graph.GetNumVertices(); ++j)
				index_table[degree_table[j].first] = j;

			Vertex neighbor = graph.GetNeighbor(ind);
			size_t n_index = index_table[neighbor];
			size_t n_value = degree_table[n_index].second;

			if(n_value > degree_table[i].second){
				degree_table[n_index].second = n_value - 1;
				n_value = n_value - 1;

				// sort
				for(size_t j = n_index - 1; j >= 0; --j){
					if(degree_table[j].second > n_value){
						degree_table[j + 1].first = degree_table[j].first;
						degree_table[j + 1].second = degree_table[j].second;
					}else{
						degree_table[j + 1].first = neighbor;
						degree_table[j + 1].second = n_value;
						break;
					}
				}
			}
		}
	}

	return core_table;
} 

// make core structure and non-core structure
// Vc : core_structure
// Vnc : non_core_structure
std::vector<size_t> core_table;
vertexVec core_structure;                                               // vertices set of core value >= 2
vertexVec non_core_structure;                                           // vertices set of core value < 2
std::vector<int32_t> is_core_structure;				        // ics[i] = a >= 0 : Vn[a] = i
std::vector<int32_t> is_non_core_structure;				// incs[i] = a >= 0 : Vnc[a] = i
// and make CTS : sorted query vertices in descending order based on core value. 
std::vector<vertexSizePair> core_table_sort; 

bool compare_size_t_2(vertexSizePair &a, vertexSizePair &b){
        return a.second > b.second;
}

void MakeCoreStructure(const Graph &query, const CandidateSet &cs){
	core_table = ComputeCoreValue(query);
	core_table_sort = std::vector<vertexSizePair>(core_table.size());
	core_structure.reserve(query.GetNumVertices());
	non_core_structure.reserve(query.GetNumVertices());
	is_core_structure = std::vector<int32_t>(query.GetNumVertices(), -1);
	is_non_core_structure = std::vector<int32_t>(query.GetNumVertices(), -1);

	for(size_t i = 0; i < query.GetNumVertices(); ++i){
		if(core_table[i] >= 2){
			core_structure.push_back(i);
			is_core_structure[i] = core_structure.size() - 1;
		}
        	else{
                	non_core_structure.push_back(i);
                	is_non_core_structure[i] = non_core_structure.size() - 1;
        	}
		core_table_sort[i].first = i;
		core_table_sort[i].second = core_table[i];
	}

	sort(core_table_sort.begin(), core_table_sort.end(), compare_size_t_2);
}

/* Make a matching order ....
 * w : weighted_query
 * P : pivot_dictionary
 * w* : min_backward_neighbor_weight   
 * BN : backward_neighbor_set  
 * Or : matching_order  
 * UN : matching_cand */
void GenerateMatchingOrder(const Graph &data, const Graph &query, const CandidateSet &cs,
                           const std::vector<std::vector<float>> &weighted_query, vertexVec &pivot_dictionary, 
                           std::vector<vertexVec> &backward_neighbor_set,
                           vertexVec &matching_order){

	size_t queryVertexSize = query.GetNumVertices();
	// pivot : given matching order, the pivot of a query vertex u is the vertex v which is preceding order neighbor of u
	// if u is the vertex of the first order, pivot of u does not exsit (P[u] = -1)
	pivot_dictionary = vertexVec(queryVertexSize, -1); 
	// w*[u] : given partial matching order, it is minimum of w(v, u) where v in backward neighbors set of u 
	std::vector<float> min_backward_neighbor_weight(queryVertexSize, data.GetNumVertices());
	// BN[u] : backward neighbors of query vertex u
	backward_neighbor_set = std::vector<vertexVec>(queryVertexSize);
	// matching order of query vertices
	// Or[|V(q)|] = # of constructed partial order
	matching_order = vertexVec(queryVertexSize + 1, -1);			// Or[i] : vertex of the i_th order
	std::vector<int32_t> matching_order_help(queryVertexSize, -1);		// Or[i] : order of vertex i
	// set of candidates that can be included in the Or.
	// if UN[u] is 0 then vertex u is not candidate, else UN[u] is 1 then u is candidate
	std::vector<int> matching_cand(queryVertexSize, 0);
    
	// select first vertex : argmin(u.core), u in Vq
	// if the number of errors exceeds ERROR_LIMIT, the next vertex is selected. 
	Vertex first_vertex = 0;
	if(is_error){
		// first vertex must be selected in core struecture (if core_structre exist)
                if(selected < core_structure.size()){
                        first_vertex = core_table_sort[selected].first;
			++selected;
		// run again
                }else{
			selected = 0;
			ERROR_LIMIT *= 2;
			first_vertex = core_table_sort[selected].first;
			++selected;
		}
        }else{
                        first_vertex = core_table_sort[selected].first;
                        ++selected;
        }

	matching_order[0] = first_vertex;
	matching_order[queryVertexSize] = 1;
	matching_order_help[first_vertex] = 0;
	
        
	// construct matching order
	// 1. first, construct with the vertices of Vc : argmin(w*[u]/|BN[u]|^2 where u in UN and Vc
	// 2. next, construct with the vertices of Vnc : argmin(w*[u]/(u.degree)^2) where u in UN and Vnc
	// 3. tie handling : (1) u.core (2) |C(u)|
	size_t start_offset = query.GetNeighborStartOffset(first_vertex);
	size_t end_offset = query.GetNeighborEndOffset(first_vertex);
	
	// update P, w*, BN, UN
	// consider v which is neighbor of first_vertex
	for(size_t ind = start_offset; ind < end_offset; ++ind){
		Vertex neighbor = query.GetNeighbor(ind);
		backward_neighbor_set[neighbor].push_back(first_vertex);

		min_backward_neighbor_weight[neighbor] = weighted_query[first_vertex][neighbor];
		pivot_dictionary[neighbor] = first_vertex;

		matching_cand[neighbor] = 1;
	}

	// 1. Vc
	// set vector for saving value such that w*[u]/|BN[u]|^2
	std::vector<vertexFloatPair> w_BN_core(core_structure.size());
	for(size_t i = 0; i < w_BN_core.size(); ++i){
		w_BN_core[i].first = core_structure[i];
		w_BN_core[i].second = min_backward_neighbor_weight[core_structure[i]] /
		       		(backward_neighbor_set[core_structure[i]].size() * backward_neighbor_set[core_structure[i]].size());
	}
	// construct Or
	while((size_t)matching_order[queryVertexSize] < core_structure.size()){
		// construct cand = UN intersection Vc
		std::vector<vertexFloatPair> cand;
		cand.reserve(core_structure.size());
		for(size_t i = 0; i < core_structure.size(); ++i){	
			if(matching_cand[core_structure[i]] == 1)
				cand.push_back(std::make_pair(w_BN_core[i].first, w_BN_core[i].second));
		}
		sort(cand.begin(), cand.end(), compare_float);

		// tie handling (1) : argmax u.core
		std::vector<vertexSizePair> cand2;
		cand2.reserve(cand.size());
		cand2.push_back(std::make_pair(cand[0].first, core_table[cand[0].first]));
		for(size_t i = 1; i < cand.size(); ++i){
			if(cand[i].second > cand[0].second)
				break;
			cand2.push_back(std::make_pair(cand[i].first, core_table[cand[i].first]));
		}
		sort(cand2.begin(), cand2.end(), compare_size_t_2);

		// tie handling (2) : argmin |C(u)|
		std::vector<vertexSizePair> cand3;
                cand3.reserve(cand2.size());
                cand3.push_back(std::make_pair(cand2[0].first, cs.GetCandidateSize(cand2[0].first)));
                for(size_t i = 1; i < cand2.size(); ++i){
                        if(cand2[i].second < cand2[0].second)
                                break;
                        cand3.push_back(std::make_pair(cand2[i].first, cs.GetCandidateSize(cand2[i].first)));
                }
                sort(cand3.begin(), cand3.end(), compare_size_t);

		// argmin w*[u]/|BN[u]|^2 where u in cand
		// argmax u.core in cand2
		// argmin |C(u)| in cand3
		Vertex target_vertex = cand3[0].first;
		
		// add Or and delete UN
		matching_order[matching_order[queryVertexSize]] = target_vertex;
		matching_order_help[target_vertex] = matching_order[queryVertexSize];
		++matching_order[queryVertexSize];
		matching_cand[target_vertex] = 0;

		// update P, w*, BN, UN
		// consider v which is Neighbor(target) but not in Or
		size_t start_offset = query.GetNeighborStartOffset(target_vertex);
		size_t end_offset = query.GetNeighborEndOffset(target_vertex);
	
		for(size_t ind = start_offset; ind < end_offset; ++ind){
                	Vertex neighbor = query.GetNeighbor(ind);

			// condition which is not in Or
			if(matching_order_help[neighbor] < 0){
				backward_neighbor_set[neighbor].push_back(target_vertex);
			
				if(weighted_query[target_vertex][neighbor] <= min_backward_neighbor_weight[neighbor]){
					min_backward_neighbor_weight[neighbor] = weighted_query[target_vertex][neighbor];
					pivot_dictionary[neighbor] = target_vertex;
				}
				
				// update w_BN_core
				int32_t core_index = is_core_structure[neighbor];
				if(core_index >= 0){
					w_BN_core[core_index].second = min_backward_neighbor_weight[neighbor] /
						(backward_neighbor_set[neighbor].size() * backward_neighbor_set[neighbor].size());
				}

				matching_cand[neighbor] = 1;
			}
		}
	}

	// 2. Vnc
	// set vector for saving value such that w*[u]/(u.degree)^2
	std::vector<vertexFloatPair> w_D_non_core(non_core_structure.size());
	for(size_t i = 0; i < w_D_non_core.size(); ++i){
			w_D_non_core[i].first = non_core_structure[i];
			w_D_non_core[i].second = min_backward_neighbor_weight[non_core_structure[i]] /
							(query.GetDegree(non_core_structure[i]) * query.GetDegree(non_core_structure[i]));
	}
	// construct Or
	while((size_t)matching_order[queryVertexSize] < queryVertexSize){
		// construct cand = UN intersection Vnc
		std::vector<vertexFloatPair> cand;
		cand.reserve(non_core_structure.size());
		for(size_t i = 0; i < non_core_structure.size(); ++i){
				if(matching_cand[non_core_structure[i]] == 1)
						cand.push_back(std::make_pair(w_D_non_core[i].first, w_D_non_core[i].second));
		}
		sort(cand.begin(), cand.end(), compare_float);

		// argmin w*[u]/(u.degree)^2 where u in cand
		Vertex target_vertex = cand[0].first;
		// add Or and delete UN
		matching_order[matching_order[queryVertexSize]] = target_vertex;
		matching_order_help[target_vertex] = matching_order[queryVertexSize];
		++matching_order[queryVertexSize];
		matching_cand[target_vertex] = 0;
		
		// update P, w*, BN, UN
		// consider v which is Neighbor(target) but not in Or
		size_t start_offset = query.GetNeighborStartOffset(target_vertex);
		size_t end_offset = query.GetNeighborEndOffset(target_vertex);

		for(size_t ind = start_offset; ind < end_offset; ++ind){
				Vertex neighbor = query.GetNeighbor(ind);

			// condition which is not in Or
			if(matching_order_help[neighbor] < 0){
				backward_neighbor_set[neighbor].push_back(target_vertex);

				if(weighted_query[target_vertex][neighbor] <= min_backward_neighbor_weight[neighbor]){
						min_backward_neighbor_weight[neighbor] = weighted_query[target_vertex][neighbor];
						pivot_dictionary[neighbor] = target_vertex;
				}

				// update w_D_non_core
				int32_t core_index = is_non_core_structure[neighbor];
				if(core_index >= 0){
						w_D_non_core[core_index].second = min_backward_neighbor_weight[neighbor] /
								(query.GetDegree(neighbor) * query.GetDegree(neighbor));
				}

				matching_cand[neighbor] = 1;
			}
		}
	}
}

// Construct BI
// BI : candidate information + bigraph information
// BI[u] : information between C(u) and C(P[u]) composed of a bigraph
// BI[u].first : candidate information of P[u] (i.e. C(P[u]))
// BI[u].second : bigraph
// BI[u].second[i] : elements of C(u) among the neighbors of the i_th candidate of P[u]
void ConstructBigraph(const CandidateSet &cs, const vertexVec &pivot_dictionary, const Graph &data,
		                  std::vector<std::pair<vertexVec, std::vector<vertexVec>>> &bigraph){
	// cand_i[j] = 0 : j is not in P[i], 1 : j is in P[i]
	vertexVec cand_i(data.GetNumVertices(), 0);

	for(size_t i = 0; i < pivot_dictionary.size(); ++i){
		// set 1 for j is in P[i]
		for(size_t j = 0; j < cs.GetCandidateSize(i); ++j)
			cand_i[cs.GetCandidate(i, j)] = 1;

		Vertex pivot_i = pivot_dictionary[i];
		size_t cand_pivot_i_size = cs.GetCandidateSize(pivot_i);

		// check vertex which does not have pivot(i.e. Or[0] vertex)
		if(pivot_i != -1){
			bigraph[i].first = vertexVec(data.GetNumVertices(), -1);
			bigraph[i].second = std::vector<vertexVec>(cand_pivot_i_size);

			// BI[i].first[v] = -1 : v is not in C(P[i]), j >= 0 : v is j_th candidate of P[i]
			// BI[i].second[j] : elements vector of C(i) among the neighbors of the j_th candidate of P[i]
			for(size_t j = 0; j < cand_pivot_i_size; ++j){
				Vertex v = cs.GetCandidate(pivot_i, j);
				bigraph[i].first[v] = j;

				size_t start = data.GetNeighborStartOffset(v);
				size_t end = data.GetNeighborEndOffset(v);
				//bigraph[i].second[j].reserve((end - start)) : reduce push_back overhead but waste space

				for(size_t k = start; k < end; ++k){
					Vertex v_neighbor = data.GetNeighbor(k);
					// check v_neighbor is in N(v) and C(i) where v is in C(P[i])
					if(cand_i[v_neighbor] == 1)
						bigraph[i].second[j].push_back(v_neighbor);
				}
			}
		}

		for(size_t j = 0; j < cs.GetCandidateSize(i); ++j)
			cand_i[cs.GetCandidate(i, j)] = 0;
	}
}

// Check embedding condtion (3)
// e(M[u], M[u']) in E(G) for all (u, u') in E(q)
bool Validate(const Graph &data, const vertexVec &match,
	     	  const std::vector<vertexVec> &backward_neighbor_set,
	     	  const Vertex &u, const Vertex &pivot_u, const Vertex &map_u){

	for(size_t i = 0; i < backward_neighbor_set[u].size(); ++i){
		Vertex back_u = backward_neighbor_set[u][i];
		
		// this check is an optimization that pivot_u removes because it already satisfies condition (3).
		if(back_u != pivot_u){
			// check condition (3) : e(M(back_u), M(u)) in E(G) ?
			Vertex map_back_u = match[back_u];
			if(!data.IsNeighbor(map_back_u, map_u))
				return false;	
		}
	}
	return true;
}

// Enumerate match
void Enumerate(const Graph &data, const vertexVec &matching_order, const vertexVec &pivot_dictionary, 
	       const std::vector<vertexVec> &backward_neighbor_set, 
	       const std::vector<std::pair<vertexVec, std::vector<vertexVec>>> &bigraph, 
	       int32_t &q_ind, vertexVec &visited, vertexVec &match){
	if(count >= 100000)
		return;

	if(error > ERROR_LIMIT) {
		return;
	}
	++error;

	// if match index == |Or| then match is complete => print
	if(q_ind == matching_order.back()){
		++count;
		error = 0;

		printf("a ");
		for(size_t i = 0; i < match.size(); ++i)
			printf("%d ", match[i]);
		printf("\n");
		return;
	}

	// get some stuff
	Vertex u = matching_order[q_ind];				// u
	Vertex pivot_u = pivot_dictionary[u];				// u' = P[u]
	Vertex map_pivot_u = match[pivot_u];				// v' = M[u']
	int32_t bigraph_ind = bigraph[u].first[map_pivot_u];		// j : v' is j_th candidate of P[u]
	size_t size_cand = bigraph[u].second[bigraph_ind].size();	// s : # of elements of C(u) among the neighbors of the v' 

	for(size_t i = 0; i < size_cand; ++i){
		Vertex map_u = bigraph[u].second[bigraph_ind][i];	// v = candidate of M[u]

		// check embedding condition (1), (3)
		if(visited[map_u] == 0 && Validate(data, match, backward_neighbor_set, u, pivot_u, map_u)){
			match[u] = map_u;
			visited[map_u] = 1;

			++q_ind;
			Enumerate(data, matching_order, pivot_dictionary, backward_neighbor_set,
               			  bigraph, q_ind, visited, match);

			visited[map_u] = 0;
			--q_ind;
		}
	}
}

void Backtrack::PrintAllMatches(const Graph &data, const Graph &query,
                                const CandidateSet &cs) {
	printf("t %zu\n", query.GetNumVertices());

	// graph analysis component
	vertexVec pivot_dictionary;
	std::vector<vertexVec> backward_neighbor_set;
	vertexVec matching_order;
	std::vector<std::pair<vertexVec, std::vector<vertexVec>>> bigraph(query.GetNumVertices());

	// get w
	std::vector<std::vector<float>> weighted_query = GenerateWeightedQuery(data, query, cs);
	
	// get core structure and FV
        MakeCoreStructure(query, cs);

	// get P, BN, Or, BI
	GenerateMatchingOrder(data, query, cs, weighted_query, pivot_dictionary, backward_neighbor_set, matching_order);
	ConstructBigraph(cs, pivot_dictionary, data, bigraph);
	int32_t q_ind = 0;
	Vertex first_vertex = matching_order[q_ind];
	// M : V(q) -> V(G)
	vertexVec match(query.GetNumVertices(), -1);
	// VI[v] = 0 : v is not visited, 1: v is visited where v is in V(G)
	vertexVec visited(data.GetNumVertices(), 0);

	ERROR_LIMIT = query.GetNumVertices() * 10000;
	if(ERROR_LIMIT < 5000000) ERROR_LIMIT = 5000000;	

	while(true){
		for(size_t i = 0; i < cs.GetCandidateSize(first_vertex); ++i){
			Vertex cand = cs.GetCandidate(first_vertex, i);
			match[first_vertex] = cand;
			visited[cand] = 1;
			
			++q_ind;
			Enumerate(data, matching_order, pivot_dictionary, backward_neighbor_set, bigraph, q_ind, visited, match);

			visited[cand] = 0;
			--q_ind;
		}
		if(error <= ERROR_LIMIT) break;
		is_error = true;

		// regenerate matching order
		GenerateMatchingOrder(data, query, cs, weighted_query, pivot_dictionary, backward_neighbor_set, matching_order);
		ConstructBigraph(cs, pivot_dictionary, data, bigraph);

		q_ind = 0;
		first_vertex = matching_order[q_ind];
		match.assign(query.GetNumVertices(), -1);
		visited.assign(data.GetNumVertices(), 0);
		error = 0;
	}
}