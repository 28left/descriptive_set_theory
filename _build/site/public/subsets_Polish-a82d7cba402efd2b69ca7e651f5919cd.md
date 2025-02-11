(chap-subspace-Polish)=
# Subspaces of Polish Spaces


## Subsets with respect to the subspace topology.

Closed subsets of Polish spaces (with the subspace topology) are Polish ({prf:ref}`properties-polish` in the Section @Polish).

What about other subsets of a Polish space? In a previous exercise, we saw  $(0,1) \subset \Real$ is Polish, but we had to pick a different compatible metric. It turns out we can do this for arbitrary open subsets of a Polish space.

```{prf:lemma}
:label: lem-bounded-metric

If $X$ is a Polish space with compatible metric $d$, then there exists a metric $d'$ that generates the same topology for which 
$$
\forall x,y \in X \; d(x,y) < 1.
$$
```

```{prf:proof}
:nonumber: true
:class:: dropdown

Use 
$$
  d'(x,y) = \frac{d(x,y)}{1+d(x,y)}.
$$
```

```{prf:proposition}
:label: prop-open-subset-Polish

Any open subset of a Polish space $X$ is Polish (with respect to the subspace topology).
```

```{prf:proof}
:class: dropdown
:nonumber: true

For a set $A \subseteq X$ and a metric $d$ on $X$, we define the *distance of $x$ from $A$ as
$$
d(x,A) = \inf \{ d(x,a) \colon a \in A\}
$$
Let $U \subseteq X$ be open. Then $d(x , X \setminus U)$ is strictly positive.


By @lem-bounded-metric, we can choose a compatible metric $d$ on $X$ with $d < 1$.
Let
$$
d_U(x,y) = d(x,y) + \left | \frac{1}{d(x,X\setminus U)} - \frac{1}{d(y,X\setminus U)} \right|.
$$
This is a metric on $U$ compatible with the subspace topology and with respect to which $U$ is complete (exercise!). 
```


```{prf:proposition}
:label: prop-intersection-Polish

Let $X$ be a Polish space, and suppose $(Y_n)$ is a sequence of Polish subspaces of $X$. Then $\bigcap_n Y_n$ is a Polish subspace of $X$.
```

```{prf:proof}
:class: dropdown
:nonumber: true

Consider the mapping $f: X \to X^\Nat$ given by $x \mapsto (x, x, x, \dots)$. The restriction of $f$ to $\bigcap_n Y_n$ is a homeomorphism between $\bigcap_n Y_n$ and the diagonal $\Delta \subseteq \prod_n Y_n$,

$$
    \Delta = \{(x,x,x, \dots) \colon \: x \in Y_n \text{ for all } n \in \Nat \}.
$$

$\Delta$ is closed in the product space $\prod_n Y_n$ and hence Polish, and this property pushes over to $\bigcap_n Y_n$ (see {prf:ref}`properties-polish`).
```

Hence every $G_\delta$ subset of a Polish space is Polish. This is as far as we can get.

```{prf:theorem} Mazurkiewicz
:label: thm-subsets-Polish

A subset of a Polish space is Polish if and only if it is $G_\delta$.
```

We have already established the "if" direction of this result.
For the other direction, we need a lemma that is interesting in its own right.  

```{prf:lemma} Kuratowski extension lemma
:label: lemma-Kuratowski-extension

Suppose $X, Y$ are Polish spaces, $A \subseteq X$, and $f: A \to Y$ continuous. Then there exists a $G_\delta$ set $G$ with $A \subseteq G \subseteq \Cl{A}$ and a continuous extension $g : G \to Y$ of $f$.
``` 

Compare this with the last lecture, where we showed that the points of continuity of a function is always a $G_\delta$ set ({prf:ref}`thm-Young`).

```{prf:proof}
:class: dropdown
:nonumber: true
 
We can adapt the *$\eps$-oscillation set* $C_\eps$ used in the proof of {prf:ref}`thm-Young` to the domain $A$:

\begin{equation*} \tag{$*$}
    C^A_\eps = \left \{ x \in X \colon \exists \delta > 0 \: \forall a,b \in A \; [ a,b \in U_\delta(x) \: \Rightarrow \: d(f(a),f(b)) < \eps  ] \right \}.
\end{equation*}

As before, $C^A_\eps$ is open and hence

$$
G = \Cl{A} \cap \bigcap_n C^A_{1/n}
$$

is $G_\delta$ and since $f$ is continuous, $A \subseteq G \subseteq \Cl{A}$.

To extend $f$ to $G$, let $x \in G$. Since $x \in \Cl{A}$, there exists a sequence $(a_n)_{n \in \N}$ in $A$ with $x = \lim_n a_n$. As $x \in \bigcap_n C^A_{1/n}$, $(f(a_n))_n$ is Cauchy. $Y$ is complete, so there exists $y = \lim_n f(a_n) \in Y$. It is straightforward to verify that $y$ is independent of the choice of $(a_n)$ and agrees with $f(x)$ for $x \in A$. Hence we can put

$$
g(x) = y,
$$

which yields the desired continuous extension.
```

Now assume $Y \subset X$ is Polish but not $G_\delta$. Then, by the previous lemma, the identity mapping $\operatorname{id}: Y \to Y$ has a proper continuous extension $g: G \to Y$ to a $G_\delta$ set $G$ with $Y \subsetneq G \subseteq \Cl{Y}$. Let $x \in G\setminus Y$. $Y$ is dense in $G$, so there exists $(y_n)$ in $Y$ with $x = \lim_n y_n$. By continuity

$$
x = \lim_n y_n = \lim_n g(y_n) = g(x) \in Y,
$$

contradiction. This completes the proof of {prf:ref}`thm-subsets-Polish`.


## Borel set as clopen sets

More complicated Borel sets in Polish spaces are not Polish anymore in the subspace topology, as we just saw. But what if we are allowed to change the topology? In the process, we would like to "preserve" as much as possible of the original space. It turns out we can change the topology so that a given Borel set becomes clopen while inducing the same family of Borel sets overall.  

We start with closed sets.

```{prf:lemma}
:label: lem-closed-clopen
If $X$ is a Polish space with topology $\mathcal{O}$, and $F \subseteq X$ is closed, then there exists a finer Polish topology $\mathcal{O}' \supseteq \mathcal{O}$ such that $\mathcal{O}$ and $\mathcal{O}'$ give rise to the same class of Borel sets in $X$, and $F$ is clopen with respect to $\mathcal{O}'$.
```

```{prf:proof}
:class: dropdown
:nonumber: true

By {prf:ref}`properties-polish` of the section on [Polish spaces](#Polish) and {prf:ref}`prop-open-subset-Polish` above, respectively, $F$ and $X \setminus F$ are Polish spaces with compatible metrics $d_F$ and $d_{X\setminus F}$,  respectively. By @lem-bounded-metric, we may assume $d_F, d_{X\setminus F} < 1$. We form the *disjoint union of the spaces $F$ and $X \setminus F$*: This is the set $X = F \,\sqcup\, X \setminus F$ with the following topology $\mathcal{O}'$: $U \subseteq F \,\sqcup\, X \setminus F$ is in $\mathcal{O}'$ if and only if $U \cap F$ is open (in $F$) and  $U \cap X\setminus F$ is open (in $X\setminus F$).

The disjoint union is Polish, as witnessed by the following metric.

$$
    d_\sqcup(x,y) =  
    \begin{cases}
            d_F(x,y) &\text{if } x,y \in F, \\
            d_{X\setminus F}(x,y) &\text{if } x,y \in X\setminus F, \\
            \;  2  &\text{otherwise}.
    \end{cases}
$$

It is straightforward to check that $d$ is compatible with $\mathcal{O}'$. Furthermore, let $(x_n)$ be Cauchy in $(X,d_\sqcup)$. Then the $x_n$ are completely in $F$ or in $X\setminus F$ from some point on, and hence $(x_n)$ converges.

Under the disjoint union topology, $F$ is is clopen. Moreover, an open set in this topology is a disjoint union of an open set in $X\setminus F$, which also open the original topology $\mathcal{O}$, and an intersection of an open set from $\mathcal{O}$ with $F$. Such sets are Borel in $(X,\mathcal{O})$, hence $(X,\mathcal{O})$ and $(X,\mathcal{O}')$ have the same Borel sets. 
```

```{prf:theorem}
:label: thm-Borel-clopen

Let $X$ be a Polish space with topology $\mathcal{O}$, and suppose $B \subseteq X$ is Borel. Then there exists 
a finer Polish topology $\mathcal{O}' \supseteq \mathcal{O}$ such that $\mathcal{O}$ and $\mathcal{O}'$ give rise to the same class of Borel sets in $X$, and $B$ is clopen with respect to $\mathcal{O}'$.
```

```{prf:proof}
:class: dropdown
:nonumber: true

Let $\mathcal{S}$ be the family of all subsets $A$ of $X$ for which a finer Polish topology exists that has the same Borel sets as $\mathcal{O}$ and in which $A$ is clopen.

We will show that $\mathcal{S}$ is a $\sigma$-algebra, which by the previous Lemma contains the closed sets. Hence $\mathcal{S}$ must contain all Borel sets, and we are done.

$\mathcal{S}$ is clearly closed under complements, since the complement of a clopen set is clopen in any topology.

So assume now that $\{A_n\}$ is a countable family of sets in $\mathcal{S}$. Let $\mathcal{O}_n$ be a Polish topology on $X$ that makes $A_n$ clopen and does not introduce new Borel sets.

Let $\mathcal{O}_\infty$ be the topology generated by $\bigcup_n \mathcal{O}_n$. Then $\bigcup_n A_n$ is open in $(X, \mathcal{O}_\infty)$, and we can apply {prf:ref}`lem-closed-clopen`. For this to work, however, we have to show that $(X, \mathcal{O}_\infty)$ is Polish and does not introduce any new Borel sets.

We know that the product space $\prod (X,\mathcal{O}_n)$ is Polish. Once again we consider the mapping $\phi: X \to \prod_n X$

$$
    x \mapsto (x,x,x, \dots).
$$

Observe that ${}\phi$ is a continuous mapping between $(X,\mathcal{O}_{\infty})$ and $\prod_n X$.  The preimage of a basic open set $U_1 \times U_2 \times \cdots \times U_n \times X \times X \times \cdots$ under $\phi$ is just the intersection of the $U_i$. Furthermore, $\phi$ is clearly one-to-one, and the inverse mapping between $\phi(X)$ and $X$ is continuous, too.

If we can show that $\phi(X)$ is closed in $\prod_n X$, we know it is Polish as a closed subset of a Polish space, and since $(X,\mathcal{O}_\infty)$ is homeomorphic to $\phi(X)$, we can conclude it is Polish.

To see that $\phi(X)$ is closed in $\prod_n X$, let $(y_1,y_2,y_3, \dots) \in \Co{\phi(X)}$. Then there exist $i < j$ such that $y_i \neq y_j$. Since $(X, \mathcal{O})$ is Polish, we can pick $U,V$ open, disjoint such that $y_i \in U$, $y_j \in V$. Since each $\mathcal{O}_n$ refines $\mathcal{O}$, $U$ is open in $\mathcal{O}_i$, and $V$ is open in $\mathcal{O}_j$. Therefore,

$$
    X_1 \times X_2 \times \cdots \times  X_{i-1} \times U \times X_{i+1} \times \cdots \times X_{j_1} \times V \times X_{j+1} \times X_{j+2} \times \cdots 
$$

where $X_k = X$ for $k \neq i,j$, is an open neighborhood of $(y_1,y_2,y_3, \dots)$ completely contained in $\Co{\phi(X)}$.

Finally, too see that the Borel sets of $(X, \mathcal{O}_\infty)$ are the same as the ones of $(X,\mathcal{O})$, for each $n$, let $\{U^{(n)}_i\}_{i \in \Nat}$ be a basis for $\mathcal{O}_n$. By assumption, all sets in $\mathcal{O}_n$ are Borel sets of $(X, \mathcal{O})$. The set $\{U^{(n)}_i\}_{i,n \in \Nat}$ is a subbasis for $\mathcal{O}_\infty$. This means that any open set in $(X, \mathcal{O}_\infty)$ is a countable union of finite intersections of the $U^{(n)}_i$. Since every $U^{(n)}_i$ is Borel in $(X, \mathcal{O})$, this means that any open set in $\mathcal{O}_\infty$ is Borel in $(X, \mathcal{O})$. Since the Borel sets are closed under complementation and countable unions, this in turn implies that every Borel set of $(X, \mathcal{O}_\infty)$ is already Borel in $(X, \mathcal{O})$.
```


```{prf:corollary} Perfect subset property for Borel sets; Alexandroff, Hausdorff
:label: cor-perfect-Borel

In a Polish space, every uncountable Borel set has a perfect subset.
```

```{prf:proof}
:class: dropdown
:nonumber: true

Let $(X,\mathcal{O})$ be Polish, and assume $B \subseteq X$ is Borel. We can choose a finer topology $\mathcal{O}' \supseteq \mathcal{O}$ so that $B$ becomes clopen, but the Borel sets stay the same. By {prf:ref}`thm-subsets-Polish`, $B$ is Polish with respect to the subspace topology $\mathcal{O}'|_B$

Suppose $B$ is uncountable. By {prf:ref}`thm-Cantor-embedding` there exists a continuous injection $f$ from $\Cant$ (with respect to the standard topology) into $(B,\mathcal{O}'|_B)$. 	

Since $\mathcal{O}'$ is finer than $\mathcal{O}$, $f$ is continuous with respect to $\mathcal{O}$, too. Since $\Cant$ is compact, $f(\Cant)$ is closed with respect to $\mathcal{O}$. Finally, $f(\Cant)$ has no isolated points with respect to $\mathcal{O}'$, which then also holds for the coarser topology $\mathcal{O}$. 

Therefore, $B$ has a perfect subset.
```
