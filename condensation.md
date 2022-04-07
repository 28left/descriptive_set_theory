---
jupytext:
  formats: ipynb,md:myst
  text_representation:
    extension: .md
    format_name: myst
    format_version: 0.13
    jupytext_version: 1.11.5
kernelspec:
  display_name: Python 3 (ipykernel)
  language: python
  name: python3
---

# Guided Study: The Condensation Lemma

+++

## The condensation lemma

```{admonition} Condensation lemma

There is a finite set $T$ of axioms of $\mathsf{ZF} - \text{Power Set}$ so that if $M$ is a transitive set with $M\models T + \mathsf{VL}$, then $M = L_\lambda$ for some limit ordinal $\lambda$.
```

+++

Define: $\varphi_{VL} = $  conjunction of the axioms in $T$ and the axiom $\mathsf{VL}$.

+++

## First application: $\mathsf{VL}$ implies $\mathsf{GCH}$

+++

```{admonition} Key Lemma 

Suppose $V=L$. If $\kappa$ is a cardinal and $x \subseteq \kappa$, then $x \in L_{\kappa^+}$.
```

+++

<!-- Basic idea of the proof:

Since $\mathsf{VL}$, $x$ has to enter $L$ at some stage, say $x \in L_\lambda$. We can assume  $L_\lambda$ satisfies a "suffiently large" fragment of $\mathsf{ZF} + \mathsf{VL}$, in particular  -->

+++

Guide to proof: *Verify each of following steps.*

+++

- There exists limit $\lambda > \kappa$ such that $x \in L_\lambda$ and such that $L_\lambda \models \varphi_{VL}$

<br> 
<br> 
<br> 

- Let $X = \kappa \cup \{x\}$.  
    *What do we know about $X$ at this stage?*
<br> 
<br> 
<br> 


- There exists an **elementary substructure** $N \preceq L_\lambda$ such that
    $X \subseteq N \subseteq L_\lambda$ and  $|N| = |X|$.
  *Use a famous theorem from logic.* 
<br> 
<br> 
<br> 


- Can we apply the condensation lemma to $N$?  
*What are the possible obstacles?*   
<br> 
<br> 
<br> 

- Apply a Mostowski collapse to $N$. This gives us a transitive $M$ isomorphic to $N$.  
*Now we have a new problem. What is it? (Hint: where does $x$ go?)*   
<br> 
<br> 
<br> 

- Argue that the Mostowski isomorphism fixes $x$.    
*Hint: What does it do with ordinals?*  
<br> 
<br> 
<br> 

- Now we can apply condensation. This yields $M = L_\beta$ for some $\beta$.  
*Where does this put $x$ now?*  
<br> 
<br> 
<br> 

- **Key argument**: $|\beta| = \kappa$.  
*Hint: Proposition 53*  
<br> 
<br> 
<br> 

- Finish: $x \in L_{\kappa^+}$  
<br> 
<br> 
<br> 

+++

```{admonition} $\mathsf{VL} \to \mathsf{GCH}$

If $\mathsf{VL}$, then for all cardinals $\kappa$, $2^\kappa = \kappa^+$.
```

<br> 
<br> 
<br> 

+++

```{admonition} Corollary 

If $\mathsf{ZF}$ is consistent, so is $\mathsf{ZF} + \mathsf{GCH}$.
```

<br> 
<br> 
<br> 

+++

## Second application: the complexity of constructible reals

+++

The set of all constructible reals is defined by a $\Sigma_1$ formula over set theory:

$$
   \varphi(x_0)	\; \equiv \; \exists y \; [y \text{ is an ordinal }  \; \wedge \; x_0 \in L_y \; \wedge \; x_0 \text{ is a set of natural numbers }  ].
$$

<br> 
<br> 
<br> 

+++

**Can we "convert" this into a formula of second order arithmetic?**

+++

*How could the condensation lemma help with this?*
<br> 
<br> 
<br> 

+++

**Key ideas**:
    
- every constructible real shows up at a countable stage of $L$.  
*Why?*
<br> 
<br> 
<br> 

- Hence if $\alpha \in L \cap \mathbb{N}^{\mathbb{N}}$, there exists a countable $\xi$ such that $x \in L_\xi$. 
<br> 
<br> 
<br> 

- Then $L_\xi$ is countable, too.  
*Why?*
<br> 
<br> 
<br> 

- Hence we can hope to replace $L_\xi$ by something like 
> "*there exists a real that codes a model that looks like $L_\xi$*"  

<br> 
<br> 
<br> 

+++

**Key ingredients**:

- Condensation lemma and Mostowski collapse  
*Can you think why these are important here?*
<br> 
<br> 
<br> 

+++

**This is the formula:**

\begin{align*} \tag{$**$}
	\alpha \in L \cap \mathbb{N}^{\mathbb{N}} \iff \exists \beta \exists & m \: [E_\beta \text{ is  extensional and well-founded} \\ & \: \wedge \: (\omega,E_\beta) \models \phi_{VL} \: \wedge \: \pi_\beta(m) = \alpha ],
\end{align*}

where $\pi_\beta$ is the Isomorphism of the Mostowski collapse of $E_\beta$.

+++

- *Why does this work?*
- *What do we still need to verfiy to make sure this is in second order arithmetic?*
<br> 
<br> 
<br> 

+++

**Ingredient 1:**

$\quad$  For any $n \in \mathbb{N}$, the following set is $\Sigma^0_1$:
\begin{equation*}
    \{(m,\sigma,\gamma) \in \mathbb{N}\times \mathbb{N}^{<\mathbb{N}}\times \mathbb{N}^{\mathbb{N}} \colon m = \ulcorner\varphi\urcorner \: \wedge \: \varphi \text{ is } \Sigma_1 \: \wedge \: (\omega,E_\gamma) \models \varphi[\sigma] \} 
\end{equation*}

<br> 
<br> 
<br> 

- *You don't need to prove this fully. Just think about **how** you would prove it. In particular, how would you arithmetize the truth relation $(\omega, E_\beta)\models \psi$?*

- *Since we work with relations over $\mathbb{N}$ now instead of arbitrary sets, it is not that easy anymore to keep quantifiers bounded. Think of an example for this difficulty. Why can't we just convert a bounded quantifier $\exists x \in y$ to a bounded quantifier in arithmetic $\exists m < n$?*

- *But since we are only interested in the complexity of $\models$ for $\Sigma_1$-formulas, this helps us bound the overall complexity at $\Sigma^0_1$*
<br> 
<br> 
<br> 

+++

**Ingredient 2:**

If $\alpha \in \mathbb{N}^{\mathbb{N}}$ and $E_\alpha$ is well-founded and extensional, then the following set is arithmetic in $\alpha$:
\begin{equation*}
	\{ (m,\gamma) \in \mathbb{N}\times \mathbb{N}^{\mathbb{N}} \colon \pi_\alpha(m) = \gamma\}
\end{equation*}

- *Again, you do not need to fully prove this, just think about **how** you would do it. In particular, how would you arithmetize $\pi_\alpha$?* 
<br> 
<br> 
<br> 

+++

Now put everything together and show

+++

```{admonition} Theorem

The set $L \cap \mathbb{N}^{\mathbb{N}}$ is $\Sigma^1_2$.
```

<br> 
<br> 
<br> 

+++

In a similar way we can show

```{admonition} Theorem	

The set $\{(\alpha,\beta) \in (L\cap\mathbb{N}^{\mathbb{N}})^2 \colon \alpha <_L \beta\}$ is $\Sigma^1_2$.
```

If $\mathsf{VL}$, then the set is actually $\Delta^1_2$, since then 

$$
	\alpha <_L \beta \iff \alpha \neq \beta \: \wedge \: \neg(\beta <_L \alpha).
$$
<br> 
<br> 
<br> 

+++

*This has consequences for the existence of non-measurable sets. Find or recall the corresponding theorem and formulate a theorem under the hypothesis $\mathsf{VL}$.*

