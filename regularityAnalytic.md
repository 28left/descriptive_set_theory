# Regularity Properties of Analytic sets
```{math}
\newcommand{\Nat}{\mathbb{N}}
\newcommand{\Real}{\mathbb{R}}
\newcommand{\Integer}{\mathbb{Z}}
\newcommand{\Rat}{\mathbb{Q}}
\newcommand{\Baire}{\Nat^{\Nat}}
\newcommand{\Cyl}[1]{N_{#1}}
\newcommand{\Cant}{2^{\Nat}}
\newcommand{\Nstr}{\Nat^{<\Nat}}
\newcommand{\Tup}[1]{\langle #1 \rangle}
\newcommand{\Co}[1]{\neg \,#1}
\newcommand{\Cl}[1]{\overline{#1}}
\newcommand{\Op}[1]{\operatorname{#1}}
\newcommand{\Rest}[1]{\mid_{#1}}
\newcommand{\Sle}{\subset}
\newcommand{\Sleq}{\subseteq}
\newcommand{\Estr}{\varnothing}
\newcommand{\eps}{\varepsilon}
\newcommand{\Conc}{\mbox{}^\frown}
\newcommand{\bDelta}{\pmb{\Delta}}
\newcommand{\bPi}{\pmb{\Pi}}
\newcommand{\bSigma}{\pmb{\Sigma}}
\newcommand{\BS}[1][n]{\bSigma^0_{#1}}
\newcommand{\BP}[1][n]{\bPi^0_{#1}}
\newcommand{\PS}[1][n]{\bSigma^1_{#1}}
\newcommand{\PP}[1][n]{\bPi^1_{#1}}
\newcommand{\Op}[1]{\operatorname{#1}}
```


In this lecture we verify that the analytic sets are Lebesgue measurable (LM) and have the Baire property (BP). Since both properties are closed under complements, they also hold for the class of **co-analytic sets** $\PP[1]$.

The analytic sets also have the perfect subset property (PS). 

```{admonition} Exercise
:class: tip

Show that if $A \subseteq \Baire$ is analytic and uncountable, then it contains a perfect subset.

(*Hint: Since $A$ is analytic, there exists a continuous mapping $f:\Baire \to \Baire$ such that $A = f(\Baire)$. Construct an embedding of $\Cant$ into $A$. Show that we can find two disjoint open sets $U_0, U_1$ whose intersection with  $A = f(\Baire)$ is uncountable. The preimages of the $U_i$ are disjoint open subsets with uncountable images. Show that this process can be continued and defines in the limit an injection of $\Cant$ into $A$.*)
```

For Borel sets, one proves (LM) and (BP) by showing that the class of sets having  (LM) (or (BP), respectively)  forms a $\sigma$-algebra and contains the open sets. For the analytic sets, this method is no longer available. We can, however, prove a similar property with respect to the Souslin operation $\mathcal{A}$, which can be seen as an extension of basic set theoretic operations into the uncountable.

More specifically, we will show the following.

- The Souslin operation $\mathcal{A}$ is **idempotent**, i.e. $\mathcal{A}\mathcal{A} \, \Gamma = \mathcal{A}\Gamma$. This implies that the analytic sets are closed under $\mathcal{A}$.
	
- The family of sets with (LM) (or (BP), respectively), is closed under the Souslin operation. Since the closed sets have both properties, and the Souslin operator is clearly monotone on classes, this yields the desired regularity results. 
	

## Idempotence of the Souslin operation

```{prf:theorem}
:label: thm-idempotent-Souslin

For every family $\Gamma$ of subsets of a set $X$,
\begin{equation*}
    \mathcal{A} \mathcal{A} \Gamma = \mathcal{A} \Gamma.
\end{equation*}
```

```{prf:proof}
We clearly have  $ \Gamma \subseteq  \mathcal{A} \Gamma$, so that we only need to prove $\mathcal{A} \mathcal{A} \Gamma \subseteq \mathcal{A} \Gamma$.

Suppose $A = \mathcal{A} P$ with $P_\sigma \in \mathcal{A} \Gamma$, that is, $P_\sigma = \mathcal{A} Q_{\sigma,\tau}$ mit $Q_{\sigma,\tau} \in  \Gamma$. Then
\begin{eqnarray*}
z \in A & \iff & \exists \alpha  \, \forall m \, (z \in P_{\alpha\Rest{m}})\\
    & \iff & \exists \alpha \, \forall m \, \exists \beta \, \forall n \, (z \in Q_{\alpha\Rest{m},\beta\Rest{n} })\\
    &\iff & \exists \alpha \,  \exists \beta \, \forall m \, \forall n \, (z \in Q_{\alpha\Rest{m},(\beta)_m\Rest{n}}),
\end{eqnarray*}
where $(\beta)_m$ denotes the $m$-th column of $\beta$.

Now we contract the two function quantifiers to a single one, using a (computable) homeomorphism $\Baire \times \Baire$, and the two universal number quantifiers into a single one using the paring function $\Tup{.,.}$. Then $A$ can be characterized as 
\begin{equation*}
z \in A \iff \exists \gamma  \; \forall k (z \in R_{\gamma\Rest{k}})
\end{equation*}
where $R_\sigma = Q_{\varphi(\sigma), \psi(\sigma)} \in \Gamma$ for suitable coding functions $\varphi, \psi$. We leave an explicit definition of these coding functions as an exercise.
```


```{prf:corollary}
:label: cor-analytic-Souslin-closed

$$
	\mathcal{A}\PS[1] = \PS[1].
$$
```



## Lebesgue measurability of analytic sets

We start with a lemma that essentially says that we can envelop any
set with a smallest (up to measure $0$) measurable set. 

```{prf:lemma}
:label: lem-approx-measurable

For every set $A \subseteq \Real$ there exists a set $B \subseteq \Real$ so that

- **(i)** $A \subseteq B$ and $B$  is  Lebesgue measurable,
- **(ii)** if $B'$ is such that $A \subseteq B' \subseteq B$  and is Lebesgue measurable, then $B\setminus B'$ has measure $0$.
```

```{prf:proof}
Suppose first that $\lambda^*(A) < \infty$. For every $n \geq 0$, there exists an open set $O_n \supseteq A$ with $\lambda^*(O_n) = \lambda(O_n) < \lambda^*(A) + 1/n$. Then $B = \bigcap_n O_n$ is measurable, and $\lambda(B) = \lambda^*(A)$. Furthermore, if $A \subseteq B' \subseteq B $, then $\lambda^*(A) \leq  \lambda^*(B') \leq \lambda^*(B)$. 

If $B'$ is also measurable, then 

$$
    \lambda^*(B) = \lambda^*(B \cap B') + \lambda^*(B \setminus B') = \lambda^*(B') + \lambda^*(B \setminus B'),  
$$

hence $\lambda^*(B \setminus B') = 0$.

If $\lambda^*(A) = \infty$, let $A_n = A \cap [m,m+1)$ for $m \in \Integer$. Then $\lambda^*(A_m) \leq 1$, and we can choose $B_m \supseteq A_m$ measurable such that $\lambda^*(B_m) = \lambda^*(A_m)$. Then $B = \bigcup_{m \in \Integer} B_m$ has the desired property.
```

We now apply the lemma to show that Lebesgue measurability is closed
under the Souslin operation. The basic idea is to approximate the local
"branches" of the Souslin operation on a Souslin scheme by measurable
sets from outside, in the sense of the lemma. 
It turns out that the total error we make by this approximation is
negligible, and hence the overall result of the Souslin operation
differs from a measurable set only by a nullset and hence is
measurable.


```{prf:proposition}
:label: prop-Souslin-Lebesgue

The class $\mathbf{LM}$ of all Lebesgue measurable sets $\subseteq \Real$ is closed under the Souslin operation, that is,

$$
    \mathcal{A} \; \mathbf{LM} \subseteq  \mathbf{LM}.
$$  
```


```{prf:proof}
Let $ A = (A_\sigma)$ be a Souslin scheme with each $A_\sigma$ measurable. We can assume that $(A_\sigma)$ is regular. For each $\sigma \in \Nstr$ we let
\begin{equation*}
    A^\sigma = \bigcup_{\alpha \supset \sigma} \bigcap_{n \in \Nat} A_{\alpha\Rest{n}} \subseteq A_\sigma.
\end{equation*}

Note that $A^\Estr = \mathcal{A}\, A$.

By the previous lemma, there exist measurable sets $B^\sigma \supseteq A^\sigma$ so that for every measurable $B \supseteq A^\sigma$, $B^\sigma \setminus B$ is null. 

By replacing $B^\sigma$ with $B^\sigma \cap \, A_\sigma$, we can further assume $B^\sigma \subseteq A_\sigma$, and also that $(B^\sigma)$ is a regular Souslin scheme.

Now let $C_\sigma = B^\sigma \setminus \bigcup_{n \in \Nat} B^{\sigma\Conc\Tup{n}}$. Each $C_\sigma$ is a nullset, by the choice of the $B^\sigma$ and the fact that  $A^\sigma = \bigcup_{n \in \Nat} A^{\sigma\Conc\Tup{n}} \subseteq \bigcup_{n \in \Nat} B^{\sigma\Conc\Tup{n}}$ . Hence $C= \bigcup_{\sigma} C_\sigma$ is a nullset, too.

It remains to show that
\begin{equation*}
B^\Estr \setminus C \; \subseteq \;  A^\Estr = \mathcal{A}\, A,
\end{equation*}
for this implies $B^\Estr \setminus A^\Estr \subseteq C$ is null, which in turn implies that $A^\Estr$ is Lebesgue measurable (since it differs from a measurable set by a nullset).

So let $x \in B^\Estr \setminus C$. Since $x \not \in C_\Estr$, there is an $\alpha(0)$ with $x \in B^{\Tup{\alpha(0)}}$.

Given $\alpha\Rest{n}$ with $x \in B^{\alpha\Rest{n}}$, we can choose $\alpha(n)$ so that $x \in B^{\alpha\Rest{n+1}}$. This is possible because $x \not \in C_{\alpha\Rest{n}}$. This way we construct $\alpha \in \Baire$ with
\begin{equation*}
x \in \bigcap_n B^{\alpha\Rest{n}} \subseteq  \bigcap_n A_{\alpha\Rest{n}} \subseteq A^\Estr.
\end{equation*}
```


```{prf:corollary}
:label: cor-analytic-measurable

Every analytic set is Lebesgue measurable.
```

```{prf:proof}
By the idempotence of ${\cal A}$, ${\cal A}\PS[1] = {\cal A}{\cal
  A}\BP[1] = {\cal A}\BP[1] = \PS[1]$. On the other hand, we have ${\cal A}\BP[1] \subseteq
{\cal A}\mathbf{LM} = \mathbf{LM}$, since the Souslin operation is monotone on
classes. This yields $\PS[1] \subseteq \mathbf{LM}$.
```


## Universally measurable sets

The previous proof is general enough to work for other kinds of
measures on arbitrary Polish spaces.

Given a Polish space $X$, a **Borel measure** on $X$ is a
countably additive set function $\mu$ defined on a $\sigma$-algebra of the
Borel sets in $X$. A set is **$\mu$-measurable** if it can be
represented as a union of a Borel set and a $\mu$-nullset. A measure $\mu$
is **$\sigma$-finite** if $X = \bigcup_n X_n$, where $X_n$ is
$\mu$-measurable with $\mu(X_n) < \infty$. Lebesgue
measure is $\sigma$-finite Borel measure on the Polish space $\Real$.

A set $A \subseteq X$ is **universally measurable** if it is
$\mu$-measurable for every $\sigma$-finite Borel measure on $X$.

```{prf:theorem} Lusin
:label: thm-analytic-universally-measurable

In a Polish space, every analytic is universally measurable.
```


## Baire property of analytic sets

Inspecting the proof of {prf:ref}`prop-Souslin-Lebesgue`, we
see that it works for the Baire property as well (with "measure
$0$" replaced by "meager", of course), provided we can
prove a Baire category version of {prf:ref}`lem-approx-measurable`.

```{prf:lemma} 
:label: lem-approx-category
Let $X$ be a Polish space. For every set $A \subseteq X$ there exists a set $B \subseteq X$ so that
- **(i)** $A \subseteq B$ and $B$  has the Baire property,
- **(ii)** if $Z \subseteq B \setminus A$  and $Z$ has the Baire
        property, then $Z$ is meager.
```

```{prf:proof}
Let  $U_1, U_2, \ldots$ be an enumeration of countable base of the
topology for $X$.
Given $A \subseteq \Real$ set
\begin{equation*}
	A^*:= \{x \in \Real \colon \forall i \; ( x \in U_i \Rightarrow U_i \cap A \text{ not meager)}\}.
\end{equation*}

Note that $A^*$ is closed: If $x \not \in A^*$, then there exists $i$ with $x \in U_i \: \& \: U_i \cap A$ null. If $y \in U_i$, then $y \not \in A^*$, since $U_i \cap A$ is null. 
Hence $U_i \subseteq \Co{A^*}$.

We have
 \begin{equation*}
A \setminus A^* = \bigcup \{A \cap U_i \colon A \cap U_i \text{ meager}\},
\end{equation*}
which is a countable union of meager sets and hence meager.

If we let $B = A \cup A^* = A^* \cup (A \setminus A^*)$, then $B$ is a
union of a meager set and a closed set and hence has the Baire
property.

Now assume $B' \supseteq A$ has the Baire property. Then $C= B
\setminus B'$ has the Baire property, too. Suppose $C$ is not meager,
then $U_i \setminus C$ is meager for some $i$, and hence also $U_i
\cap A \subseteq (U_i \setminus C)$. Besides, $U_i \cap C \neq
\emptyset$, for otherwise $U_i \subseteq U_i \setminus C$ would be
meager. Thus there exists $x \in U_i$ with $x \not\in A^*$, which by
definition of $A^*$ implies that $U_i \cap A$ is not meager, a contradiction. 
```

By adapting the proof of {prf:ref}`prop-Souslin-Lebesgue`, we
obtain the Baire category version and hence can deduce that analytic sets
have the Baire property.


```{prf:proposition}
:label: prop-Souslin-Baire

In any Polish space $X$, the class $\mathbf{BP}$ of all sets $\subseteq X$
with the Baire property is closed under the Souslin operation, i.e.

$$
    \mathcal{A} \; \mathbf{BP} \subseteq  \mathbf{BP}.
$$  
```