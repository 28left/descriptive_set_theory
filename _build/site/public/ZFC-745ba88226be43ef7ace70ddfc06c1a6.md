# The Axioms of Set Theory

In the previous chapters, we have repeatedly brought up a metamathematical context, such as the use of the Axiom of Choice, or Solovay's model in which every set of reals is measurable. But we have not really distinguished between results in a formal theory and in the metatheory, mostly because we did not really establish a formal theory to begin with. We have treated descriptive set theory like most other mathematical theories in that we defined our basic objects (Polish spaces, Borel sets, etc.) and then started proving facts about them "the usual way", as we would prove facts about commutative rings or locally compact topological spaces. But in order to make better sense of the metamathematical issues, we have to "pause" and talk a bit about the axioms of set theory.


## Comprehension and Russell Antinomy

To develop set theory formally as a theory of first order logic, we first need to fix the **language**. We want to consider the notion of a *set* as foundational (with the intention to develop everything else from it), we provide only **one binary relation symbol**, $\in$. We will denote this as the **language of set theory**, $\mathcal{L}_\in$.

How can we axiomatize the concept of set?

In his famous 1895 paper "*Beiträge zu Begründung der transfiniten Mengenlehre*" {cite}`Cantor_1895s`, Georg Cantor writes

> Unter einer "*Menge*" verstehen wir jede Zusammenfassung $M$ von bestimmten wohlunterschiedenen Objekten unserer Anschauung oder unseres Denkens (welche die "*Elemente*" von  $M$  genannt werden)  zu einem Ganzen.

This can be translated approximately as: *A set is any collection of certain distinct objects of our intuition or our thought into a whole*.

We can try to make this more precise as follows:

> For every property $P(x)$ exists a set $M$ of all objects $x$ having property $P$:  $M =\{x: M(x) \}$.

This can be formalized in the language of set theory as an **axiom scheme**: For every $\mathcal{L}_\in$-formula $\varphi(x)$,

> (**Comprehension**)$_\varphi$ $\exists y \, \forall x \; ( x \in y \leftrightarrow \varphi(x))$

This axiom, however, is **contradictory**.

```{admonition} Russell's antinomy (1903)
:class: warning

If we choose $\varphi(x) = \neg x \in x$, then the Comprehension axiom yields the existence of a set $r$ with 
\begin{equation*}
\forall x ( x \in  r \leftrightarrow x \not \in x).
\end{equation*} 
In particular, for $x = r$: 
\begin{equation*}
r \in  r \leftrightarrow r \not \in r ,
\end{equation*}
contradiction!
```

We obtain similar contradictions if we choose as $\varphi(x)$ the formula
\begin{align*}
     x = x  &  \text{antinomy of the set of all sets (Cantor)} \\
     x\;\text{is a cardinal} & \text{Cantor, around 1899, published 1932}\\
     x \; \text{is an ordinal} &   \text{antinomy of Burali-Forti}
\end{align*}
These antinomies are, however, not as direct as Russell's and require some further development of the theory in order to derive a contradiction.

Regarding the existence of sets, we have to distinguish between 
- **classes**, which we will denote by capital letters $A,B,\dots$ (for some specific, important classes we will also use boldface) and 
- **sets**, denoted in this context by lower case letters $a,b,\ldots,x,y \ldots$.

An arbitrary property $\varphi(x)$ will define a corresponding class

$$
A = \{x \colon \varphi(x)\}
$$

As we saw above, classes are not necessarily sets: some are "*too large*" to be a set, as for example the **class of all sets**,

$$
\mathbf{V} = \{ x \colon x = x \}
$$


Classes that are not sets are called **proper classes**. 

```{margin}
So when we write $A \subseteq B$ for classes $A,B$ defined by $\varphi, \psi$, respectively, the formal expression would be $\forall x ( \varphi(x) \to \psi(x))$.
```
You should keep in mind that, in the formal theory $\ZF$, we do not have variables for classes, so the definition above is *informal*.  Any class variable, as well as expressions like $a \in A$, should be seen as *abbreviations* for a formal expression using the underlying formula.
There are formal systems (such as **Bernays-Gödel set theory**) that use classes explicitly, but they are used less frequently.  


## The Axioms of $\mathsf{ZFC}$


We begin with the **Axiom of Extensionality**, which is essential for the equality relation between sets.

> (**Extensionality**)  $\qquad \forall x (x \in a  \leftrightarrow x \in b)  \to a=b.$

Consequently, two sets coincide if they have the same elements.

The basic idea of the **Zermelo-Fraenkel** axiom system $\ZF$ is that we avoid introducing sets that are "too large" (and hence would lead to contradictions) by allowing new sets only if they can be **"generated" from a given set** by a number of fixed, well-behaved operations. 

So let us postulate that at least one set exists:

> (**Set Existence**) $\qquad \exists x ( x = x )$

This axiom is not strictly necessary, as the existence of a set also follows from other axioms in $\ZF$ (or usually even from the underlying axioms of first-order logic). But it is good to have it as a starting point here for emphasis.

We have seen we cannot use full comprehension for sets. In its place we introduce the scheme of

> (**Separation**)$_{\varphi}$ $\qquad  \forall a \exists y \forall x (x \in y \leftrightarrow x \in a \wedge \varphi(x,\ldots))$

By Extensionality, the set $y$ is unique.

```{margin}
In particular, the empty set $\emptyset$ exists. (Why?)
```
Separation allows us to select from any class $\{x \colon \varphi(x,\ldots)\}$ those elements that are in a given set $a$ and collect them in a **set**
\begin{equation*}
    \{x \in a \colon \varphi(x,\ldots)\}
\end{equation*}


Next, we have 

> (**Pairing**) $ \qquad \exists y \forall x( x \in y \leftrightarrow  x = a \vee x = b)$.

This axioms allows forming *pairs of sets*, specifically

\begin{align*}
    \{a,b\} & : =  \{x\colon x=a \; \vee \; x=b \} &    \\
    \{a\} &: = \{x\colon x=a  \} &    \text{singleton set}\\
    (a,b) &: =  \{\{a\},\{a,b\}\} &    \text{ordered pair}
\end{align*}

While for the *pair set* $\{a,b\} = \{b,a\}$ the order is not important, we have for the *ordered pair*
\begin{equation*}
(a,b) = (c,d) \leftrightarrow a = c \wedge b = d.
\end{equation*}
Hence, we can introduce **binary relations** as classes of ordered pairs
\begin{gather*}
    \Op{Rel}(R) :\leftrightarrow  \forall u \in R \; \exists x,y  \; (u =(x,y)).
\end{gather*}

As usual, by identifying **functions** with their graphs, we can introduce functions as a special kind of relation:
\begin{gather*}
F: A \to B :\leftrightarrow  \forall x \in A \; \exists ! y \in B \; (x,y) \in F.
\end{gather*}
We write $\Op{Fun}(a)$ to denote that fact that $a$ is a function.

Further elementary axioms:

> (**Union**)   $\qquad \forall a \exists y \forall z (z \in y  \leftrightarrow  \exists x \in a \; z \in x)$

```{margin}
Note that *Replacement* is an axiom scheme: For *any* formula, if that formula defines a function $F$, it asserts the existence of a set (the image set).
```
> (**Replacement**)$_F$ <br>
>  $\qquad \forall a  ((F: a \to \mathbf{V}) \: \rightarrow \: \exists u \forall y (y \in u \leftrightarrow \exists x \in a \; y = F(x)))$

> (**Power Set**) $\qquad \forall a \exists y \forall z (z \in y \leftrightarrow z \subseteq a)$

It follows that, for a given set $a$, the following classes are sets:

\begin{align*}
\bigcup \, a = \bigcup_{x \in a} x & : = \{z \colon \exists x \in a \; z \in x \}  &  \qquad  \text{union}\\
F[a] = \{F(x)|x \in a\} &: = \{y\colon \exists x \in a \; y = F(x) \}  &  \qquad  \text{image set}\\
\mathcal{P}(a) &: = \{x\colon x \subseteq a\} & \qquad  \text{power set}
\end{align*}


> (**Infinity**) $ \qquad \exists x ( \emptyset \in x \wedge \forall y ( y \in x \to y \cup \{y\} \in x))$

The axiom of Infinity is a "pure" set existence axiom, that is, it does not depend on another set already existing. It therefore renders the axiom of Set Existence above redundant.
It also implies the existence of the set $\Nat$ of natural numbers (along with the operation $+$), which we will address in more detail below.

Using $\Nat$, we can introduce the other basic number sets:
- $\Integer = (\Nat\times\Nat)/ \sim_\Integer$, where $(x,y) \sim_\Integer (u,v) :\Leftrightarrow  x+v = y+u$. Multiplication on $\Integer$ can be defined inductively (see below).
- $\Rat = (\Integer\times\Integer)/\sim_\Rat$, where $(x,y) \sim_\Rat (u,v) :\Leftrightarrow xv = yu$. 
- We can extend the linear order $<$ of $\Nat$ to $\Integer$ and then to $\Rat$ in the usual way. Then we can introduce the **real numbers** as the set of **Dedekind cuts**:

$$
\Real = \{ x \in \mathcal{P}(\Rat) \colon x \neq \emptyset \: \wedge \: x \neq \Rat \: \wedge \: \forall z \in x \forall y \in \Rat \: y < z \to y \in x \}.
$$


The final axiom of $\ZF$ is 

> (**Foundation**) $\qquad \forall a \;( a \neq \emptyset \to \exists x \in a \; \forall y \in x \, y \not \in a)$.

Foundation rules out, for example, that a set can be an element of itself. More precisely, the axiom states that $\in$-relation is **well-founded** on any set. 


We can also formalize the **Axiom of Choice**:

> (**Choice**) $\qquad \forall a ( \forall x \in a \; x \neq \emptyset \;\;\; \to \;\;\; \exists f (\Op{Fun}(f) \:\wedge\: \Op{dom}(f) = a \:\wedge\: \forall x \in a \: f(x) \in x))$

We denote the axiom system $\ZF + \AC$ as $\ZFC$ -- **Zermelo-Fraenkel with Choice**.



## Ordinals

The axiom of Foundation facilitates the introduction of **ordinal numbers**. 
An ordinal is defined as

> a transitive set that is well-ordered by $\in$.

```{margin}
**Caution!**
Being transitive does *not* mean the $\in$ relation is transitive on the set. (Counterexample?)
```
```{prf:definition}
:label: def-transitive
A set $x$ is **transitive** if 

$$
    \forall y \in x \forall z ( z \in y \to z \in x)
$$
```

In other words, transitive sets cannot "hide" elements in subsets. All elements of subsets have to be present in the set itself.

Since by Foundation $\in$ is well-founded on any set, it suffices to require that an ordinal is **linearly ordered** by $\in$.

```{prf:definition}
:label: def-ordinal

A set $a$ is an **ordinal** if it is transitive and $\in$ is **connex** on $a$, that is,

\begin{equation*} \tag{con}
\forall x,y \in a \; (x \in y \: \vee \: x=y \: \vee \: y \in x)
\end{equation*}
```

```{admonition} Exercise
:class: tip

Show that the above condition is indeed sufficient to linearly order $a$ by $\in$, i.e. if $a$ is transitive and satisfies ($\Op{con}$), then $\in\Rest{a}$ is a linear order (in particular, it is also *irreflexive* and *transitive*).
```

If we write out the formulas in full, we see {prf:ref}`def-ordinal` is much simpler than the original one. Most notably, in {prf:ref}`def-ordinal` we only use only **bounded quantifiers** (of the form $\forall y \in a$), whereas in the original form we have to quantify over arbitrary subsets of $a$. This is an important difference whose impact will become clear later on.

We can now develop the theory of ordinals based on this definition. We will not do this here (assuming already basic familiarity with this theory -- formal or informal). Here are some of the basic facts:

- *Any element of an ordinal is an ordinal*: $\Op{Ord}(a) \wedge b \in a \to \Op{Ord}(b)$.

- $0 = \emptyset$ is the *smallest ordinal*.

- Every ordinal $\xi$ has an **immediate successor** $\xi' =  \xi+1 = \xi \cup \{\xi\}$

- The *finite ordinals* are exactly the natural numbers:

$$
0 = \emptyset, \quad 1 = 0 + 1 = \emptyset \cup \{\emptyset\} = \{\emptyset\}, \quad 2 = 1+1 = \{\emptyset, \{\emptyset\} \}, \dots
$$   

- By the **axiom of Infinity**, the **set of all finite ordinals** exists. It is transitive, linearly ordered by $\in$ and thus an ordinal itself: $\omega$ the first infinite ordinal and the first **limit ordinal**:

$$
    \omega \neq 0 \: \wedge \: \forall \xi < \omega \; (\xi+1 < \omega).
$$

- Every *set* of ordinals $a$ has a **supremum** $\sup a = \bigcup_{\xi \in a} \xi$ that is itself an ordinal, the least ordinal at least as large as all ordinals in $a$.

- Every well-ordering $(b,<)$ on a set is order-isomorphic to a unique ordinal, the **well-order type** of $(b,<)$

- The $\in$-relation is a well-ordering on the class of all ordinals.

- The ordinals $\mathbf{Ord}$ form a proper class (Burali-Forti antinomy).