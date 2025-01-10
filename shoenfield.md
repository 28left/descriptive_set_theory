# Shoenfield Absoluteness

## Tree representations of $\mathbf{\Sigma}^1_2$ sets

Analytic sets are projections of closed sets. Closed sets are in $\Baire$ are infinite paths through trees on $\Nat$. 
                      
We call a set $A \subseteq \Baire$ **$Y$-Souslin** if $A$ is the projection $\exists^{Y^{\Nat}}[T]$ of some $[T]$, where $T$ is a tree on $\Nat \times Y$, that is  

$$
A = \exists^{Y^\Nat}[T] = \{\alpha \colon \exists y \in Y^\Nat \: (\alpha,y) \in [T] \}.
$$

```{prf:theorem} Shoenfield, 1961 
:label: thm-tree-repr-sig12

Every $\bSigma^1_2$ set is $\omega_1$-Souslin. 
In particular, if $A$ is $\Sigma^1_2$ then there is a tree $T \in L$ on $\Nat \times \omega_1$ such that $A = \exists^{(\omega_1)^\Nat}[T]$. 
```

```{prf:proof}
:class: dropdown
:nonumber: true

Assume first $A$ is $\Pi^1_1$. There is a recursive tree $T$ on $\Nat \times \Nat$ (and hence, in $L$, since "*being recursive*" is definable) such that 

$$
    \alpha \in A \iff T(\alpha) \text{ is well-founded}.
$$

Hence, $\alpha \in A$ if and only if there exists an order preserving map $\pi: T(\alpha) \to \omega_1$. We recast this now in terms of getting an infinite branch through a tree. 

Let $\{\sigma_i \colon i \in \Nat\}$ be a recursive enumeration of $\Nstr$. We may assume for this enumeration that $|\sigma_i| \leq i$. We define a tree $\widetilde{T}$ on $\Nat \times \omega_1$ by 

$$
    \widetilde{T} = \{ (\sigma,\tau) : \: \forall i,j < |\sigma| \: [\sigma_i \supset \sigma_j \: \wedge \: (\sigma\Rest{|\sigma_i|}, \sigma_i) \in T \: \to \: \tau(i) < \tau(j)] \}.
$$

The tree $\widetilde{T}$ is in $L$, since it is definable from $T$ and $\omega_1$. Furthermore, if $\alpha \in A$, then the existence of an order-preserving map $\pi: T(\alpha) \to \omega_1$ implies that there is an infinite path $(\alpha,\eta)$ through $\widetilde{T}$. 

Conversely, if such a path $(\alpha,\eta)$ exists, then there is an order preserving map $\pi: T(\alpha) \to \omega_1$. Hence we have

$$
    \alpha \in A \: \leftrightarrow \: \exists \eta \in (\omega_1)^{\Nat} \: (\alpha,\eta) \in [\widetilde{T}] \: \leftrightarrow \: \alpha \in \exists^{(\omega_1)^\Nat}[\widetilde{T}],
$$

so $A$ is of the desired form. 

Next, we extend the representation to $\Sigma^1_2$. 

If $A$ is $\Sigma^1_2$, then there is a $\Pi^1_1$ set $B \subseteq \Baire\times\Baire$  such that $A = \exists^{\Baire} B$. Since $B \in \Pi^1_1$, we can employ the tree representation of $\Pi^1_1$ to obtain a tree $T$ over $\Nat \times \Nat \times \omega_1$ such that $B = \exists^{(\omega_1)^\Nat} [T]$. 

Now we recast $T$ as a tree $T'$ over $\Nat \times \omega_1$ such that $\exists^{(\omega_1)^\Nat}[T'] = \exists^{(\omega_1)^\Nat} B$. This is done by using a bijection between $\Nat \times \omega_1$ and $\omega_1$. 

This way we can cast the $\Nat \times \omega_1$ component of $T$ into a single $\omega_1$ component, and thus transform the tree $T$ into a tree $T'$ over $\Nat \times \omega_1$ such that $\exists^{(\omega_1)^\Nat}[T'] = \exists^{(\omega_1)^\Nat}[B]$.
```


## $\mathbf{\Sigma}^1_2$ sets as unions of Borel sets
         
We can use Shoenfield's tree representation to extend {prf:ref}`cor-coanal-union-Borel` to $\Sigma^1_2$ sets.

```{prf:theorem} Sierpinski, 1925
:label: thm-sigma12-union-Borel

Every $\Sigma^1_2$ set is a union of $\aleph_1$-many Borel sets.
```

Sierpinski's original proof used $\AC$. The following proof does not make use of choice.

```{prf:proof}
:class: dropdown
:nonumber: true

Let $A \subseteq \Baire$ be $\Sigma^1_2$. By {prf:ref}`thm-tree-repr-sig12` there exists a tree $T$ on $\Nat \times \omega_1$ such that $A = \exists^{(\omega_1)^\Nat}[T]$. For any $\xi < \omega_1$ let 

$$
    T^\xi = \{ (\sigma,\eta) \in T\colon \forall i \leq |\eta|\:  \eta(i) < \xi \}.
$$

Since the cofinality of $\omega_1$ is greater than $\omega$ (this can be proved without using $\AC$), every $d: \omega \to \omega_1$ has its range included in some $\xi < \omega_1$. Thus we have

$$
	A = \bigcup_{\xi < \omega_1} \exists^{(\omega_1)^\Nat}[T^\xi].
$$

For all $\xi < \omega_1$, the set $\exists^{(\omega_1)^\Nat}[T^\xi]$ is $\Sigma^1_1$, because the tree $T^\xi$ is a tree on a product of countable sets and hence is isomorphic to a tree on $\Nat \times \Nat$. By {prf:ref}`cor-aleph-union-intersect`, each $\Sigma^1_1$ set is the union of $\aleph_1$ many Borel sets, from which the result follows.
```

As for co-analytic sets, an immediate consequence of this theorem is (using the perfect set property of Borel sets):

```{prf:corollary}
:label: cor-cardinality-sigma12

Every $\bSigma^1_2$ set has cardinality at most $\aleph_1$ or has a perfect subset and hence cardinality $2^{\aleph_0}$.
```


## Absoluteness of $\Sigma^1_2$ relations
                            
Shoenfield used the tree representation of $\mathbf{\Sigma}^1_2$ sets to establish an important absoluteness result for $\Sigma^1_2$ sets of reals. 

Suppose $A \subseteq \Baire$ is $\Sigma^1_2$. Then, by the Kleene Normal Form there exists a bounded formula of second order arithmetic $\varphi(v_0,v_1,v_2)$ such that 

$$
	\alpha \in A \iff \exists \beta_0 \, \forall \beta_1 \, \exists m \; \varphi(\alpha\Rest{m},\beta_0\Rest{m},\beta_1\Rest{m}).
$$

Let $M$ be an inner model of $\ZF$. Arithmetical formulas can be interpreted in $\ZF$ and we can also relativize them. This allows us to introduce a relativized version of $A$ by identifying, as usual, a set with the predicate that defines it:

$$
	A^M(\alpha) :\iff (\exists \beta_0 \in M\cap \Baire) \, (\forall \beta_1\in M \cap \Baire)  \, (\exists m) \: \varphi(\alpha\Rest{m},\beta_0\Rest{m},\beta_1\Rest{m})
$$

Note that we do not have to relativize the inner natural number quantifier, since $\Nat$ is absolute for inner models, and also not the formula $\varphi$, since a bounded arithmetic formula translates into a bounded set-theoretic formula (with only natural number quantifiers) and is therefore absolute for $M$. 

We can then say that $A$ is **absolute for** $M$ if for any $\alpha\in M$,

$$
	A^M(\alpha) \iff A(\alpha).
$$

Absoluteness can be extended and relativized in a straightforward manner to predicates analytical in some $\gamma \in \Baire \cap M$.

All arithmetic predicates are absolute, since all quantifiers are natural number quantifiers. Shoenfield absoluteness extends this absoluteness to $\Sigma^1_2$ and $\Pi^1_2$ predicates.


```{prf:theorem} Shoenfield absoluteness
:label: thm-Shoenfild-absoluteness

Every $\Sigma^1_2(\gamma)$ predicate and every $\Pi^1_2(\gamma)$ predicate is absolute for all inner models $M$ of $\ZFC$ such that $\gamma \in M$. In particular, all $\Sigma^1_2$ and $\Pi^1_2$ relations are absolute for $L$.
```

```{prf:proof}
:class: dropdown
:nonumber: true

We show the theorem for $\Sigma^1_2$ predicates. For the relativized version, one uses the **relative constructible universe** $L[\gamma]$, see {cite}`jech2003a` or {cite}`Kanamori:2003a`.

Let $A$ be a $\Sigma^1_2$ relation. For simplicity, we assume that $A$ is unary. Fix a tree representation of $A$ as a projection of a $\Pi^1_1$ set. So, let $T$ be a recursive tree on $\Nat \times \Nat \times \Nat$ such that 

$$
     A(\alpha) \iff \exists \beta \;  T(\alpha,\beta) \text{ is well-founded}. 
$$

Note that $T$ is in $M$ (since it is recursive and hence definable).

Now assume $\alpha \in M$ and $A^M(\alpha)$. Hence there is a $\beta \in M$ such that $T(\alpha,\beta)$ is well-founded in $M$. This is equivalent to the fact that in $M$ there exists an order preserving mapping $\pi: T(\alpha,\beta) \to \mathbf{Ord}$. 

Since $M$ is an inner model and $T$ is absolute, the mapping exists also in $V$. Hence $T(\alpha,\beta)$ is well-founded in $V$ and thus $A(\alpha)$.

For the converse assume that $\alpha \in M$ and $A(\alpha)$. Now we use the alternative tree representation of $A$ given by {prf:ref}`thm-tree-repr-sig12`. Let $U \in L \subseteq M$ be a tree on $\Nat \times \omega_1$ such that $A = \exists^{(\omega_1)^\Nat} U$. 

As before, let 

$$
	U(\alpha) = \{ (\alpha\Rest{n}, \tau)\in U \colon n \in \Nat, \tau \in (\omega_1)^n,  \}
$$
 
Then, for any $\alpha \in \Baire$,

\begin{align*}
	A(\alpha)     & \iff    \exists \lambda \in (\omega_1)^\Nat \: (\alpha,\lambda) \text{ infinite path through $U$}. \\
     & \iff    U(\alpha) \text{ not well-founded}. \\
\end{align*}

This means that there exists no order preserving map $U(\alpha) \to \omega_1$. But then such a map cannot exist in $M$ either. Thus, $U(\alpha)$ is a tree in $M$ which is ill-founded in the sense of $M$. Thus, by Shoenfield's Representation Theorem relativized to $M$, $A^M(\alpha)$.

Absoluteness for $\Pi^1_2$ follows by employing the same reasoning, using that the complement is $\Sigma^1_2$.
```

By analyzing the proof one sees that it actually suffices that $M$ is a transitive $\in$-model of a certain finite collection of axioms $\ZF$ such that $\omega_1 \subseteq M$.

The result is the best possible with respect to the analytical hierarchy, since the statement

$$
	\exists \alpha \; [\alpha \not\in L]
$$

is $\Sigma^1_3$, but cannot be absolute for $M = L$.

Shoenfield's absoluteness theorem also holds for sentences rather than predicates, with a similar proof. This means a $\Sigma^1_2$ statement is true in $L$ if and only if it holds in $V$. Many results of classical analysis are $\Sigma^1_2$ statements. The Shoenfield absoluteness theorem says that if they can be established under $\VL$, they can be established in $\ZF$ alone.

On the negative side, as we will soon see, Shoenfield absoluteness also puts strong limits on the use of forcing to establish independence results in analysis. 