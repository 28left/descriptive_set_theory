# The Axioms of Set Theory

In the previous chapters, we have repeatedly brought up a metamathematical context, such as the use of the Axiom of Choice, or Solovay's model in which every set of reals is measurable. But we have not really distinguished between results in a formal theory and in the metatheory, mostly because we did not really establish a formal theory to begin with. We have treated descriptive set theory like most other mathematical theories in that we defined our basic objects (Polish spaces, Borel sets, etc.) and then started proving facts about them "the usual way", as we would prove facts about commutative rings or locally compact topological spaces. But in order to make better sense of the metamathematical issues, we have to "pause" and talk a bit about the axioms of set theory.


## Comprehension and Russell's Antinomy

To develop set theory formally as a theory of first order logic, we first need to fix the **language**. We want to consider the notion of a *set* as foundational (with the intention to develop everything else from it), we provide only **one binary relation symbol**, $\in$. We will denote this as the **language of set theory**, $\mathcal{L}_\in$.

How can we axiomatize the concept of set?

In his famous 1895 paper "*Beiträge zu Begründung der transfiniten Mengenlehre*" {cite}`Cantor_1895s`, Georg Cantor writes

> Unter einer "*Menge*" verstehen wir jede Zusammenfassung $M$ von bestimmten wohlunterschiedenen Objekten unserer Anschauung oder unseres Denkens (welche die "*Elemente*" von  $M$  genannt werden)  zu einem Ganzen.

This can be translated approximately as: *A set is any collection of certain distinct objects of our intuition or our thought into a whole*.

We can try to make this more precise as follows:

> For every property $P(x)$ exists a set $M$ of all objects $x$ having property $P$:  $M =\{x: P(x) \}$.

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
     x = x  \qquad &  \text{antinomy of the set of all sets (Cantor)} \\
     x\;\text{is a cardinal} \qquad & \text{Cantor, around 1899, published 1932}\\
     x \; \text{is an ordinal} \qquad &   \text{antinomy of Burali-Forti}
\end{align*}

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

You should keep in mind that, in the formal theory $\ZF$, we do not have variables for classes, so the definition above is *informal*.  Any class variable, as well as expressions like $a \in A$, should be seen as *abbreviations* for a formal expression using the underlying formula.
There are formal systems (such as **Bernays-Gödel set theory**) that use classes explicitly, but they are used less frequently.  
```{prf:remark}
:nonumber: true
So when we write $A \subseteq B$ for classes $A,B$ defined by $\varphi, \psi$, respectively, the formal expression would be $\forall x ( \varphi(x) \to \psi(x))$.
```


## The Axioms of $\mathsf{ZFC}$


We begin with the **Axiom of Extensionality**, which is essential for the equality relation between sets.

:::{prf:axiom} Extensionality 
:nonumber: true

$\qquad \forall a,b \, (\forall x (x \in a  \leftrightarrow x \in b)  \to a=b)$
:::

Consequently, two sets coincide if they have the same elements.

The basic idea of the **Zermelo-Fraenkel** axiom system $\ZF$ is that we avoid introducing sets that are "too large" (and hence would lead to contradictions) by allowing new sets only if they can be **"generated" from a given set** by a number of fixed, well-behaved operations. 

So let us postulate that at least one set exists:

:::{prf:axiom} Set Existence
:nonumber: true

$\qquad \exists x ( x = x )$
:::

This axiom is not strictly necessary, as the existence of a set also follows from other axioms in $\ZF$ (or usually even from the underlying axioms of first-order logic). But it is good to have it as a starting point here for emphasis.

We have seen we cannot use full comprehension for sets. In its place we introduce the scheme of Separation. Let $\varphi(x, z, w_1, \dots, w_n)$ be a $\mathcal{L}_\in$-formula in which $y$ does not occur as a free variable.

:::{prf:axiom} Separation$_{{}\varphi}$
:nonumber: true

 $\qquad  \forall w_1, \dots, w_n \forall a \exists y \forall x (x \in y \leftrightarrow x \in a \wedge \varphi(x, a, w_1, \dots, w_n))$
:::
```{prf:remark}
:nonumber: true
In particular, the empty set $\emptyset$ exists. (Why?)
```
By Extensionality, the set $y$ is unique. Note that there is one axiom for *every* formula ${}\varphi$, so Separation is an **axiom scheme**.


Separation allows us to select from any class $\{x \colon \varphi(x,\ldots)\}$ those elements that are in a given set $a$ and collect them in a **set**
\begin{equation*}
    \{x \in a \colon \varphi(x,\ldots)\}
\end{equation*}


Next, we have 

:::{prf:axiom} Pairing
:nonumber: true

$ \qquad \forall a,b \, \exists y \forall x( x \in y \leftrightarrow  x = a \vee x = b)$.
:::

This axioms allows to form *pairs of sets*, specifically

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

:::{prf:axiom} Union
:nonumber: true

$\qquad \forall a \, \exists y \forall z (z \in y  \leftrightarrow  \exists x \in a \; z \in x)$
:::

:::{prf:axiom} Replacement$_{{}\varphi}$
:nonumber: true

$\qquad  \forall x,y,z (\varphi(x,y) \wedge \varphi(x,z) \to y=z) \;  \: \rightarrow \; \forall a \exists u \forall y (y \in u \leftrightarrow \exists x \in a \: \varphi(x,y))$
:::

```{prf:remark}
:nonumber: true
Like Separation, Replacement is an *axiom scheme*. 
```
In words, if ${}\varphi$ defines a function, then the image of any set under that function is a set. Note that, as in the case of Separation, ${}\varphi$ is allowed to have *parameters*, which we dropped here to improve readability.

:::{prf:axiom} Power Set
:nonumber: true

$\qquad \forall a \, \exists y \forall z (z \in y \leftrightarrow z \subseteq a)$
:::

It follows that, for a given set $a$, the following classes are sets:

\begin{align*}
\bigcup \, a = \bigcup_{x \in a} x & : = \{z \colon \exists x \in a \; z \in x \}  &  \qquad  \text{union}\\
F[a] = \{F(x)|x \in a\} &: = \{y\colon \exists x \in a \; y = F(x) \}  &  \qquad  \text{image set}\\
\mathcal{P}(a) &: = \{x\colon x \subseteq a\} & \qquad  \text{power set}
\end{align*}

:::{prf:axiom} Infinity
:nonumber: true

$ \qquad \exists x ( \emptyset \in x \wedge \forall y ( y \in x \to y \cup \{y\} \in x))$
:::

The axiom of Infinity is a "pure" set existence axiom, that is, it does not depend on another set already existing. It therefore renders the axiom of Set Existence above redundant.
It also implies the existence of the [set ${}\omega$](#ordinals-basic) (the set theoretic version of the natural numbers), along with the operation $+$.

Using $\Nat$, we can introduce the other basic number sets:
- $\Integer = (\Nat\times\Nat)/ \sim_\Integer$, where $(x,y) \sim_\Integer (u,v) :\Leftrightarrow  x+v = y+u$. Multiplication on $\Integer$ can be defined inductively (see below).
- $\Rat = (\Integer\times\Integer)/\sim_\Rat$, where $(x,y) \sim_\Rat (u,v) :\Leftrightarrow xv = yu$. 
- We can extend the linear order $<$ of $\Nat$ to $\Integer$ and then to $\Rat$ in the usual way. Then we can introduce the **real numbers** as the set of **Dedekind cuts**:

$$
\Real = \{ x \in \mathcal{P}(\Rat) \colon x \neq \emptyset \: \wedge \: x \neq \Rat \: \wedge \: \forall z \in x \forall y \in \Rat \: y < z \to y \in x \}.
$$


We complete the list of $\ZF$ axioms with the Axiom of Foundation:

:::{prf:axiom} Foundation
:nonumber: true

$\qquad \forall a \: ( a \neq \emptyset \to \exists x \in a \; \forall y \in x \, y \not \in a)$.
:::

As we [discussed before](#set-well-founded), Foundation rules out, for example, that a set can be an element of itself. More precisely, the axiom states that $\in$-relation is **well-founded** on any set. 

We can also formalize the **Axiom of Choice** in the language of set theory:

:::{prf:axiom} Choice
:nonumber: true

$\qquad \forall a \: ( \forall x \in a \; x \neq \emptyset \; \to \; \exists f (\Op{Fun}(f) \:\wedge\: \Op{dom}(f) = a \:\wedge\: \forall x \in a \: f(x) \in x))$
:::


We denote the axiom system $\ZF + \AC$ as $\ZFC$, **Zermelo-Fraenkel with Choice**.
