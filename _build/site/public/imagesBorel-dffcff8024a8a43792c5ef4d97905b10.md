(imagesBorel)=
# Continuous Images of Borel sets

In 1916, Nikolai Lusin asked his student Mikhail Souslin to study a paper by Henri Lebesgue. Souslin found a number of errors, including a lemma that asserted that the projection of a Borel is again Borel. In this lecture we will study the behavior of Borel sets under continuous functions. We will see that on the one hand every Borel set is the continuous image of a closed set, but that on the other hand continuous images of Borel sets are not always Borel.

This gives rise to a new family of sets, the **analytic** sets, which form a proper superclass of the Borel sets with interesting properties.


## Borel sets as continuous images of closed sets

We have [seen earlier](#thm-polish-cont-image-Baire) that every Polish space is the continuous image of Baire space $\Baire$. As we will see now, we can strengthen this result.

```{prf:theorem} Lusin and Souslin  
:label: thm-Polish-bijection-Baire

Let $X$ be a Polish space. Then there exists a closed subset $F \subseteq \Baire$ and a continuous bijection $f: F \to X$ that can be extended to a continuous surjection $g: \Baire \to X$.
```

We have seen previously that every uncountable Polish space contains a [homeomorphic embedding of Cantor space](#thm-Cantor-embedding). This was achieved by means of a **Cantor scheme**. To prove {prf:ref}`thm-Polish-bijection-Baire`, we take up this idea again and adapt it to Baire space. 

```{prf:definition}
:label: def-Lusin-scheme
:nonumber: true

A **Lusin scheme** on a metric space $X$ is a family $(F_\sigma)_{\sigma \in \Nstr}$ of subsets of $X$ such that

- **(i)** $\sigma \Sleq \tau$ implies $F_\sigma \supseteq F_\tau$,
- **(ii)** for all $\tau \in \Nstr$, $i \neq j \in \Nat$, $F_{\tau\Conc \Tup{i}} \cap F_{\tau\Conc \Tup{j}} = \emptyset$.

If it has the additional property that

- **(iii)** $\diam(F_{\alpha \Rest{n}}) \to 0$  for $n \to \infty$,

then we can, similarly to a Cantor scheme, define the set
\begin{equation*}
    D = \{\alpha \in \Baire \colon \bigcap_{n \in \Nat} F_{\alpha\Rest{n}} \neq \emptyset \}
\end{equation*}
and an **associated map** $f: D \to X$ by
\begin{equation*}
\{f(\alpha)\} = \bigcap_{n \in \Nat} F_{\alpha\Rest{n}}.
\end{equation*}
Properties (i)-(iii) ensure that $f$ is continuous and injective.
```

To prove the theorem we devise a Lusin scheme on $X$ such that $D$ will be closed, and $f$ will be a surjection, too. This is ensured by the following additional properties.

- **(a)** $F_\emptyset = X$,
- **(b)** Each $F_\tau$ is $\BS{2}$,
- **(c)** For each ${}\tau$, $\diam(F_\sigma) \leq 1/2^{|\sigma|}$,
- **(d)** $F_\tau = \bigcup_{i \in \Nat} F_{\tau\Conc \Tup{i}} =  \bigcup_{i \in \Nat} \Cl{F_{\tau\Conc \Tup{i}}}$.

For this we have to show that every $\BS{2}$ set $F \subseteq X$ can be written, for given $\eps > 0$, as  $F= \bigcup_{i \in \Nat} F_i$, where the $F_i$ are pairwise disjoint $\BS{2}$ sets of diameter $< \eps$ so that $\Cl{F_i} \subseteq F$:

Let $F= \bigcup_{i \in \Nat} C_i$, where $C_i$ is closed, and $C_i \subseteq C_{i+1}$. Then $F= \bigcup_{i \in \Nat}(C_{i+1} \setminus C_i)$. 

Let $(U_n)$ be a covering of $X$ with open sets of diameter $< \eps$. Put $D^{(i)}_n = U_n \cap (C_{i+1} \setminus C_i)$. Then $D^{(i)}_n$ is $\bDelta^0_2$. Now let $E^{(i)}_n = D^{(i)}_n \setminus (D^{(i)}_1 \cup \dots \cup D^{(i)}_{n-1})$.

Then $C_{i+1} \setminus C_i = \bigcup_{n \in \Nat} E^{(i)}_n$ where the $E^{(i)}_j$ are $\BS{2}$ sets of diameter $<\eps$. Therefore,

\begin{equation*}
F =  \bigcup_{i,n\in \Nat} E^{(i)}_n \; \text{ and } \;  \Cl{E^{(i)}_n} \subseteq \Cl{C_{i+1} \setminus C_i} \subseteq C_{i+1} \subseteq F.
\end{equation*}

The mapping $f$ associated with this Lusin scheme is surjective due to (a) and (d).

Furthermore, the domain $D$ of $f$ is closed: Suppose $\alpha_n \in D$, $\alpha_n \to \alpha$. Then $f(\alpha_n)$ is Cauchy, since for $\eps > 0$, there exists $N$ with $\diam(F_{\alpha\Rest{N}}) < \eps$ and $n_0$ such that $\alpha_n\Rest{N} = \alpha\Rest{N}$ for all $n \geq n_0$. Therefore, $d(f(\alpha_n),f(\alpha_m)) < \eps$ whenever $n,m \geq n_0$. Since $X$ is Polish $f(\alpha_n) \to y$ for some $y \in X$.
By (d) we have $y \in \bigcap_n \Cl{F_{\alpha\Rest{n}}} = \bigcap_n F_{\alpha\Rest{n}}$, hence $\alpha \in D$ and $f(\alpha) = y$.

It remains to show that we can extend $f$ to a continuous surjection $g: \Baire \to X$. Say a closed subset $C$ of a topological space $Y$ is a **retract** of $Y$ if there exists a continuous surjection $g: Y \to C$ such that $g\Rest{C} = \Op{id}$.

```{prf:lemma}
:label: lem-closed-retract-Baire

Every non-empty closed subset of $\Baire$ is a retract of $\Baire$.
```

```{prf:proof}
:class: dropdown
:nonumber: true

Let $C \subseteq \Baire$ be closed, and let $T$ be a pruned tree such that $[T] = C$. We define a monotone mapping $\phi:\Nstr \to T$ such that $\phi(\sigma) = \sigma$ for all $\sigma \in T$. Then the induced (continuous) mapping $\phi^*: \Baire \to C$ is the desired retract.

Define ${}\phi$ by induction. Let $\phi(\Estr) = \Estr$. Given $\phi(\tau)$, let

$$
    \phi(\tau\Conc\Tup{m}) = \begin{cases}
        \tau\Conc\Tup{m} & \text{ if } \tau\Conc\Tup{m} \in T,\\
        \text{any } \phi(\tau)\Conc\Tup{k} \in T & \text{ otherwise}.
    \end{cases}
$$

Note that $k$ must exist since $T$ is pruned.
```

If we combine the retract function with $f$, we then obtain the desired surjection $\Baire \to X$. This concludes the proof of {prf:ref}`thm-Polish-bijection-Baire`.


[Refining the topology](#thm-Borel-clopen), we can extend the result from Polish spaces to Borel sets.

```{prf:corollary} Lusin and Souslin  
:label: cor-Borel-image-closed

For every Borel subset $B$ of a Polish space $X$ there exists a closed set $F \subseteq \Baire$ and a continuous bijection $f:F \to B$. Furthermore, $f$ can be extended to a continuous surjection $g:\Baire \to B$.
```

```{prf:proof}
:class: dropdown
:nonumber: true
	
Enlarge the topology $\mathcal{O}$ of $X$ to a topology $\mathcal{O}_B$ for which $B$ is clopen. 
By [Mazurkiewicz's Theorem](#thm-subsets-Polish), $(B,\mathcal{O}_B\Rest{B})$ is a Polish space. By the previous theorem, there exists a closed set $F \subset \Baire$ and a continuous bijection $f:\Baire \to (B,\mathcal{O}_B\Rest{B})$. Since $\mathcal{O} \subseteq \mathcal{O}_B$, $f:F \to B$ is continuous for $\mathcal{O}$, too. 
```  

This theorem can be reversed in the following sense.

```{prf:theorem} Lusin and Souslin
:label: thm-Borel-injective

Suppose $X,Y$ are Polish and $f:X \to Y$ is continuous. If $A \subseteq X$ is Borel and $f\Rest{A}$ is injective, then $f(A)$ is Borel.
```

For a proof (which uses facts about analytic sets), see {cite}`Kechris:1995a` (II.15.1).


## Images of Borel sets under arbitrary continuous functions

As announced in the introduction, Borel sets are *not* closed under *arbitrary* continuous mappings.

```{prf:theorem} Souslin
:label: thm-Souslin-Borel-images

The Borel sets are not closed under continuous images.
```

```{prf:proof}
:class: dropdown
:nonumber: true

Let $U \subseteq \Baire \times \Baire \times \Baire$ be $\Baire$-universal for $\BP{1}(\Baire \times \Baire)$.
Define

\begin{equation*}
    F:= \{(\alpha,\beta) \colon \exists \gamma  \; (\alpha,\gamma,\beta) \in U\}.
\end{equation*}

We claim that this set is *$\Baire$-universal for the set of all continuous images of closed subsets of $\Baire$*:	

On the one hand $F$ is a projection of a closed set, and projections are continuous. This implies that all the sets $F_\beta = \{ \alpha \colon (\alpha,\beta) \in F \}$ are continuous images of a closed set.

On the other hand, if $f: C \to \Baire$ is continuous with $C \subseteq \Baire$ closed (possibly empty) and $f(C) = A$, then  
\begin{equation*}
    \alpha \in A \iff \exists \gamma \; (\gamma,\alpha) \in \Op{Graph}(f) \iff \exists \gamma \; (\alpha,\gamma) \in  \Op{Graph}(f^{-1}).
\end{equation*}

Since $f$ is continuous, $\Op{Graph}(f)$ and hence also $\Op{Graph}(f^{-1})$ are closed subsets of $\Baire \times \Baire$. Thus, by the universality of $U$, there exists ${}\beta$ such that 

$$
    \Op{Graph}(f^{-1}) = U_\beta = \{ (\alpha,\gamma) \colon (\alpha,\gamma,\beta) \in U \},
$$

and hence

$$
    A = F_\beta.
$$

$F$ cannot be Borel: Otherwise $D_F = \{\alpha \colon (\alpha,\alpha) \not\in F \}$ were Borel. By {prf:ref}`cor-Borel-image-closed`, every Borel set is the image of a closed set under a continuous mapping. This implies that $D_F = F_\beta$. But then

$$
    \beta \in D_F \iff \beta \in F_\beta \iff (\beta,\beta) \in F \iff \beta \not\in D_F,  
$$

contradiction.
```
