# Old stuff

## Borel codes

```{prf:lemma} 
:label: lem-Borel-codes-clopen

Suppose ${}\gamma$ is a Borel code of finite order representing a set $B \subseteq \Baire$. Suppose further $C \subseteq \Baire$ is clopen and both $C$ and its complement have computable $\bSigma^0_1$ codes. We can, uniformly in ${}\gamma$, compute Borel codes for $B \cap C$ and $B \cup C$ of the same Borel complexity as ${}\gamma$.
``` 



## Definability in Arithmetic

One of the fundamental insights of computability theory is the close relation between computability and definability in arithmetic. The recursively enumerable subsets of $\Nat$ are precisely the sets $\Sigma_1$-definable over the standard model of arithmetic, $(\Nat,+,\cdot,0,1)$, and **Post's Theorem** uses this result to establish a rigid connection between levels of arithmetical complexity and computational complexity.

As indicated above, we can use this relation to give a characterization of the Borel sets of finite order in terms of definability. Since we are dealing with subsets of $\Baire$, that is, with sets of functions on $\Nat$ rather than just functions on $\Nat$, we will work in the framework of **second order arithmetic**.

The 
**language of second order arithmetic** has two kinds of variables: **number variables** $x,y,z, \dots$ (and sometimes $k,l,m,n$ if they are not used as metavariables), to be interpreted as elements of $\Nat$, and **function variables** $\alpha,\beta,\gamma,\dots$, intended to range over functions from $\Nat$ into $\Nat$, i.e. elements of Baire space, i.e. reals. The non-logical symbols are the binary function symbols $+,\cdot$, the binary relation symbol $<$, the **application function** symbol $\Ap$, and the constants $\underline{0}, \underline{1}$.  **Terms** are defined by closing off number variables under $+,\cdot,\underline{0},\underline{1}$ and $\Ap(\alpha,.)$, where ${}\alpha$ is any function variable. Any numerical term is a **term**, as well as any expression of the form $\Ap(\alpha,t)$, where $\alpha$ is any function variable and $t$ is a numerical term.

```{prf:example} Terms
:nonumber: true
- $\underline{1}+\underline{x}$
- $x+(\underline{1}+\underline{1})\cdot y$
- $\Ap(\alpha, z)$
- $\Ap(\beta, x+(\underline{1}+\underline{1})\cdot y)$
```

**Atomic formulas** are $t_1 = t_2$, $t_1 < t_2$, where $t_1, t_2$ are terms. **Formulas** are obtained as usual by closing atomic formulas under $\wedge, \vee, \neg, \exists, \forall$. 

```{prf:example} Formulas
:nonumber: true
- $\underline{0} = \underline{1}$
- $\neg(x+(\underline{1}+\underline{1})\cdot y < \underline{0})$
- $\Ap(\beta, x+(\underline{1}+\underline{1})\cdot y) = \Ap(\alpha, \underline{0})$
- $\Ap(\alpha, z) = \Ap(\alpha,x) \; \vee \; \neg(\underline{0} = \underline{1})$
```


The 
**standard model of second order arithmetic** is the structure

$$
\mathcal{A}^2 = (\Nat, \Baire, \Ap, +, \cdot, <, 0, 1),
$$

where $+$ and $\cdot$ are the usual operations on natural numbers, $<$ is the standard ordering of $\Nat$. The two domains are connected by the binary operation $\Ap: \Baire \times \Nat \to \Nat$, defined as

$$
\Ap(\alpha,x) = \alpha(x).
$$

A relation $R \subseteq \Nat^m \times (\Baire)^n$ is **definable over $\mathcal{A}^2$** if there exists a formula ${}\varphi$ of second order arithmetic such that for any $x_1, \dots, x_m \in \Nat$ and $\alpha_1, \dots \alpha_n \in \Baire$,

$$
R(x_1, \dots, x_m, \alpha_1, \dots \alpha_n) \quad \text{iff} \quad \mathcal{A}^2 \models \varphi[x_1, \dots, x_m, \alpha_1, \dots \alpha_n].
$$

```{prf:theorem}
:label: lightface-definability
A set $A \subseteq \Baire$ is $\Sigma^0_n$ $(\Pi^0_n)$ if and only if it is definable over $\mathcal{A}^2$ by a $\Sigma^0_n$ $(\Pi^0_n)$ formula. 
```

Here, $\Sigma^0_n$ $(\Pi^0_n)$ formula means that we can **only quantify over number variables**, as opposed to $\Sigma^1_n$ $(\Pi^1_n)$ formulas, where we can also quantify over function variables.

The proof is a straightforward extension of the standard argument for subsets of $\Nat$.

To formulate the fundamental {prf:ref}`thm-fundamental` in terms of definability, we need the concept of **relative definability**. We add a new constant function symbol $\underline{\gamma}$ to the language. Given a function ${}\gamma$, a relation is 
**definable in ${}\gamma$** if it is definable over the structure

$$
\mathcal{A}^2(\gamma) = (\Nat, \Baire, \Ap, +, \cdot, <, 0, 1, \gamma),
$$

where the symbol $\underline{\gamma}$ is interpreted as ${}\gamma$.

Then the following holds.

```{prf:theorem} 
:label: thm-Borel-arith

A set $A \subseteq \Baire$ is $\bSigma^0_n$ $(\bPi^0_n)$ if and only if it is definable in ${}\gamma$ by a $\Sigma^0_n$ $(\Pi^0_n)$ formula, for some $\gamma \in \Baire$.
```

---

## Normal forms

{prf:ref}`thm-Borel-arith` tells us that a set $A \subseteq \Baire$ is $\bSigma^0_n$ if and only if it is definable by a $\Sigma^0_n$ formulas over $\mathcal{A}^2$, relative to some parameter. That means that there exists a **bounded formula** $\phi(x_1, \dots, x_n,\alpha,\underline{\gamma})$ (i.e. all quantifiers are bounded) such that 

$$
A(\alpha) \iff \exists x_1 \: \forall x_2 \: \dots \: \Qu x_n \; \phi(x_1, \dots, x_n, \alpha,\gamma) \text{ holds (in the standard model).}
$$

Here ${}\gamma$ is the parameter, and $\Qu$ is $\exists$ if $n$ is odd, and $\forall$ if $n$ is even. 

Similarly, $A \subseteq \Baire$ is $\bPi^0_n$ if and only if it is definable as

$$
	A(\alpha) \iff \forall x_1 \: \exists x_2 \: \dots \:  \Qu x_n \; \phi(x_1, \dots, x_n, \alpha,\gamma) \text{ holds (in the standard model).}
$$

where $\phi(x_1, \dots, x_n,\alpha,\underline{\gamma})$ is bounded, and $\Qu$ is $\forall$ if $n$ is odd, and $\exists$ if $n$ is even.

What do sets defined by bounded formulas look like? An atomic formula (without parameters) either contains no function variable at all, or it is of the form $\alpha(t_1) = t_2$. This implies that the truth of an atomic formula is determined by *finitely many positions* in ${}\alpha$. This remains true if we consider logical combinations of atomic formulas, or even bounded quantification. Hence a bounded formula defines an open subset of $\Baire$. 

On the other hand, the reals for which a bounded formula does not hold are definable by a bounded formula, too, since the negation of a bounded formula is again a bounded formula. We conclude that **bounded formulas define clopen subsets of $\Baire$**. On the other hand, if we have $\bSigma^0_1$-code for a set $A$ and its complement, we can decide the relation $A(\alpha)$ computably in the code. 

Hence we can formulate the Normal Form above as follows.
$A \subseteq \Baire$ is $\bSigma^0_n$ if and only if there exists a clopen set $R \subseteq \Nat^n\times \Baire$

$$
	A(\alpha) \iff \exists x_1 \: \forall x_2 \: \dots \: \Qu x_n \; R(x_1, \dots, x_n, \alpha),
$$

and similarly for $\bPi^0_n$ sets.



