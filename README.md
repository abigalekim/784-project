# Hypergraph
A hypergraph $H$ is defined as a pair:
$$H = (V, E)$$
where:
- $V$ is a set of vertices.
- $E$ is a set of hyperedges, where each hyperedge is a subset of $V$, i.e., $E \subseteq \mathcal{P}(V)$.

# Alpha $\alpha$ Cycle
An **alpha cycle** is a sequence of hyperedges $(E_1, E_2, \ldots, E_k)$ such that:
1. For each pair of consecutive hyperedges $E_i$ and $E_{i+1}$ (we identify $E_{n+1}$ with $E_1$), their intersection is non-empty:
   $$e_i \cap e_{i+1} \neq \emptyset, \quad \forall i \in \{1, 2, \ldots, k\}$$
2. All hyperedges in the cycle are distinct:
   $$e_i \neq e_j \quad\text{for } i \neq j$$

# Beta $\beta$ Cycle
A **beta cycle** is a sequence $(E_1, x_1,\cdots, E_n, x_n) (n\geq 3)$ where the $E_i$ are distinct hyperedges and the $x_i$ are distinct vertices, and satisfying the following properties:
1. for all $i \in [1, n-1]$, $x_i$ belongs to $E_i$ and $E_{i+1}$ and no other $E_i$

# Gamma $\gamma$ Cycle
A **gamma cycle** is a sequence $(E_1, x_1,\cdots, E_n, x_n) (n\geq 3)$ where the $E_i$ are distinct hyperedges and the $x_i$ are distinct vertices, and satisfying the following properties:
1. for all $i \in [1, n-1]$, $x_i$ belongs to $E_i$ and $E_{i+1}$ and no other $E_i$
2. $x_n$ belongs to $E_n$ and $E_1$ (and possibly to other $E_j$)



# Relationships
Cycle striction:
$$\alpha \subset \beta \subset \gamma$$

Acyclicity:
$$\gamma \subset \beta \subset \alpha$$
