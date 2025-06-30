(chap-trees)=
# Trees

Let $A$ be a set. Recall that the set of all finite sequences over $A$
is denoted by $\Astr{A}$, while $A^\Nat$ denotes the set of all
infinite sequences over $A$. Given $\alpha \in A^\N$, $n \in \N$,
$\alpha\Rest{n}$ denotes the initial segment of $\alpha$ of length
$n$. 

```{prf:definition}
:nonumber: true
:label: def-tree

A **tree** on $A$ is a set $T \subseteq \Astr{A}$ that is **closed under prefixes**, that is,

$$
    \forall \sigma, \tau \; [\tau \in T \: \& \: \sigma \Sleq \tau \; \Rightarrow \; \sigma \in T ]
$$	
```

We call the elements of $T$ **nodes**.

A sequence $\alpha \in A^\Nat$ is an **infinite path through** or **infinite branch of** $T$ if for all $n$, $\alpha\Rest{n} = (\alpha_0, \alpha_1, \dots, \alpha_{n-1}) \in T$. We denote the set of infinite paths through $T$ by $[T]$.

An important criterion for a tree to have infinite paths is the following.

```{prf:theorem} König's Lemma
:label: thm-Koenigs-lemma

Any tree $T$ with infinitely many nodes that is **finitely branching** (i.e. each node has at most finitely many immediate extensions) has an infinite path.
```

```{prf:proof}
:class: dropdown
:nonumber: true

We construct an infinite path inductively. 

Let $T_\sigma$ denote the tree "above" ${}\sigma$, i.e. $T_\sigma = \{ \tau \in \Astr{A} \colon \sigma\Conc\tau \in T\}$. If $T$ is finitely branching,  by the **pigeonhole principle**, at least one of the sets $T_\sigma$ for $|\sigma| = 1$ must be infinite. Pick such a ${}\sigma$ and let $\alpha\Rest{1} = \sigma$. 

Repeat the argument for $T = T_\sigma$ and continue inductively. This yields a sequence $\alpha \in [T]$.
```
	
If $[T] = \emptyset$, we call $T$ **well-founded**. The motivation behind this is that $T$ is well-founded if and only if the **inverse prefix** relation 

$$
	\sigma \preceq \tau \quad :\Leftrightarrow \quad \sigma \Sgeq \tau
$$

is well-founded, i.e. it does not have an infinite descending chain.

If $T \neq \emptyset$ is well-founded, we can assign $T$ an ordinal number, its **rank** $\rho(T)$.

- If ${\sigma}$ is a **terminal node**, i.e. ${\sigma}$ has no extensions in $T$, then let $\rho_T(\sigma) = 0$.

- If ${\sigma}$ is not terminal, and $\rho_T(\tau)$ has been defined for all $\tau \Sgr \sigma$, we set $\rho_T(\sigma) = \sup \{\rho_T(\tau)+1 \colon \tau \in T, \tau \Sgr \sigma \}$.

- Finally, set $\rho(T) = \sup\{\rho_T(\sigma) + 1 \colon \sigma\in T \} = \rho_T(\Estr)+1$, where $\Estr$ denotes the empty string.



## Orderings on trees

Now suppose $A$ is linearly ordered by a relation $\leq_A$. 
The **lexicographical ordering** $\leq_{\lex}$ of $\Astr{A}$ is defined as

\begin{equation*}
	\sigma \leq_{\lex} \tau \quad :\Leftrightarrow \quad \\
        \sigma = \tau \; \text{ or } \; \exists i <|\sigma|,|\tau| \: \left( \sigma_i <_A \tau_i \text{ and } \forall j < i \; \sigma_j = \tau_j  \right )  
\end{equation*}

This ordering extends to $A^\Nat$ in a natural way. 

```{prf:proposition}
:label: prop-leftmost-branch

If $\leq_A$ is a well-ordering of $A$ and $T$ is a tree on $A$ with $[T] \neq \emptyset$, then $[T]$ has a $\leq_{\lex}$-minimal element, the **leftmost branch**.
```

```{prf:proof}
:class: dropdown
:nonumber: true

We **prune** the tree $T$ by deleting any node that is not on an infinite branch. This yields a subtree $T' \subseteq T$ with $[T'] = [T]$. 

Let $T'_n = \{\sigma \in T' \colon |\sigma| = n \}$. Since $\leq_A$ is a well-ordering on $A$, $T'_1$ must have a $\leq_{\lex}$-least element. Denote it by $\alpha\Rest{1}$. Since $T'$ is pruned, $\alpha\Rest{1}$ must have an extension in $T$, and we can repeat the argument to obtain $\alpha\Rest{2}$. 

Continuing inductively, we define an infinite path $\alpha$ through $T'$, and it is straightforward to check that $\alpha$ is a  $\leq_{\lex}$-minimal element of $[T']$ and hence of $[T]$.
```

We can combine the $\leq_{\lex}$-ordering with the inverse prefix order to obtain a linear ordering of $\Astr{A}$. This ordering has the nice property that if $A$ is well-ordered and $T$ is well-founded, then the ordering restricted to $T$ is a well-ordering. 

```{prf:definition}
:nonumber: true
:label: def-Kleene-Brouwer

The **Kleene-Brouwer ordering** $\leq_{\KB}$ of $\Astr{A}$ is defined as follows.

$\qquad \sigma \leq_{\KB} \tau$ $\quad :\Leftrightarrow \quad$  $\sigma \Sgeq \tau \;\;$  or $\; \; \sigma \leq_{\lex} \tau$.
```

This means ${\sigma}$ is smaller than ${\tau}$ if it is a proper extension of ${\tau}$ or "to the left" of ${\tau}$.

We now have 
```{prf:proposition}
:label: prop-KB-wellorder

Assume $(A,\leq)$ is a well-ordered set. Then for any tree $T$ on $A$,

$\qquad$ $T$ is well-founded $\quad \Leftrightarrow \quad$  $\leq_{\KB}$ restricted to $T$ is a well-ordering.
```

```{prf:proof}
:class: dropdown
:nonumber: true

Suppose $T$ is not well-founded. Let $\alpha \in [T]$. Then $\alpha\Rest{0}, \alpha\Rest{1}, \dots$ is an infinite descending sequence with respect to $\leq_{\KB}$.

Conversely, suppose $\sigma_0 >_{\KB} \sigma_1 >_{\KB} \dots$ is an infinite descending sequence in $T$. By the definition of $>_{\KB}$, this implies $\sigma_1(0) \geq_A \sigma_2(0) \geq_A \dots$ as a sequence in $A$. Since $A$ is well-ordered, this sequence must eventually be constant, say $\sigma_n(0) = a_0$ for all $n \geq n_0$. 

Since the $\sigma_n$ are descending, by the definition of $\leq_{\KB}$ it follows that $|\sigma_n| \geq 2$ for $n > n_0$. Hence we can consider the sequence $\sigma_{n_0+1}(1) \geq_A \sigma_{n_0+2}(1) \geq_A  \dots$ in $A$. Again, this must be constant $= a_1$ eventually. Inductively, we obtain a sequence $\alpha = (a_0, a_1, a_2, \dots) \in [T]$, that is, $T$ is not well-founded.
```

```{prf:remark}
:nonumber: true

The order type of a well-founded tree under $\leq_{\KB}$ usually is not equal to its rank $\rho(T)$.
```


## Coding trees

We can also define an ordering on $\Astr{A}$ via an injective mapping from $\Astr{A}$ to some linearly ordered set $A$. We will use this repeatedly for the case $A = \Nat$ and $A = \{0,1\}$.

For $A = \Nat$, we can use the standard coding mapping
\begin{equation*}
	\pi: (a_0, a_1, \dots, a_n) \mapsto p_0^{a_0+1}p_1^{a_1+1}\cdots p_n^{a_n+1},
\end{equation*}
where $p_k$ is the $k$th prime number. This embeds $\Nstr$ into $\Nat$, and we can well-order $\Nstr$ by letting $\sigma < \tau$ if and only if $\pi(\sigma) < \pi(\tau)$. 

For $A = \{0,1\}$ we set
\begin{equation*}
	\pi: (b_0,b_1, \dots, b_{n-1}) \mapsto (2^n-1) + \sum_{i=0}^{n-1} b_i 2^i.
\end{equation*}

These two mappings allows us henceforth to see **trees as subsets of the natural numbers**. This will be an important component in exploring the relation between topological and arithmetical complexity.


## Trees and closed sets

Let $A$ be a set with the discrete topology. Consider $A^\Nat$ with the product topology (and compatible metric) defined in [Lecture 2](#polish-product-spaces).

```{prf:proposition}
:label: prop-trees-closed

A set $F \subseteq A^\Nat$ is closed if and only if there exists a tree $T$ on $A$ such that $F = [T]$.
```

```{prf:proof}
:class: dropdown
:nonumber: true

Suppose $F$ is closed. Let 
\begin{equation*}
	T_F = \{\sigma \in \Astr{A} \colon \sigma \Sle \alpha \text{ for some }\alpha \in F\}.
\end{equation*}
Then clearly $F \subseteq [T_F]$. Suppose $\alpha \in [T_F]$. This means for any $n$, $\alpha\Rest{n} \in T_F$, which implies that there exists $\beta_n \in F$ such that $\alpha\Rest{n} \Sle \beta_n$. The sequence $(\beta_n)$ converges to ${\alpha}$, and since $F$ is closed, $\alpha \in F$.

For the other direction, suppose $F = [T]$. Let $\alpha \in A^\Nat \setminus F$. Then there exists an $n$ such that $\alpha\Rest{n} \notin T$. Since a tree is closed under prefixes, no extension of $\alpha\Rest{n}$ can be in $T$. This implies $\Cyl{\alpha\Rest{n}} \subseteq A^\Nat \setminus F$, and hence $A^\Nat \setminus F$ is open.	  
```


