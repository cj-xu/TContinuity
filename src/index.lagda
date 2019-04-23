
                     An Agda implementation of

         -------------------------------------------------
                A syntactic approach to continuity
             of Gödel's system T definable functionals
         -------------------------------------------------

                          Chuangjie Xu

         February 2018, updated in June and September 2018


We recover the well-known fact that

  all Gödel's system T definable functions (ℕ → ℕ) → ℕ are continuous

via a syntactic approach.  Differing from the usual syntactic method,
we firstly perform a translation of system T into itself where
particularly natural numbers are translated to functions (ℕ → ℕ) → ℕ.
Then we inductively define a continuity predicate on the elements of
translated types and show that the translation of any term in system T
satisfies the continuity predicate.  We obtain the desired result by
relating terms and their translations via a parametrized logical
relation.  We adapt and generalize our method to prove other notions
of continuity.

This Agda development contains the following sections of the paper

  §2. Gödel's system T and the b-translation

  §3. Continuity of T-definable functionals

  §4. T-definable moduli of continuity

  §5.1. Uniform continuity

In addition, we also implement the following

  Appendix I.  Continuity via a monadic interpretation of T

  Appendix II. Dialogue tree representation of T-definable functionals

that are briefly mentioned in the introduction of the paper.


\begin{code}

---------------------------------------------
-- §2. Gödel's system T and the b-translation
---------------------------------------------
import T

\end{code}

The first step of our syntactic method is to perform a translation

                      (t ↦ tᵇ) : ρ → ρᵇ

from system T to itself, which we call b-translation. In particular,
we define ℕᵇ :≡ (ℕ → ℕ) → ℕ.  Using a parametrized logical relation,
we show that any f : (ℕ → ℕ) → ℕ is pointwise equal to fᵇ(Ω), where
fᵇ : (ℕᵇ → ℕᵇ) → ℕᵇ is the b-translation of f and Ω : ℕᵇ → ℕᵇ is a
T-definable generic element.


\begin{code}

--------------------------------------------
-- §3. Continuity of T-definable functionals
--------------------------------------------
import Continuity

\end{code}

We inductively define a continuity predicate

                          C  ⊆  ρᵇ

whose base case C(f) states the continuity of f : (ℕ → ℕ) → ℕ.  By
induction on terms, we show that the b-translation of any term
satisfies C.  Moreover, we have C(Ω) and thus C(fᵇ(Ω)), i.e. fᵇ(Ω) is
continuous, for any f : (ℕ → ℕ) → ℕ in system T.  Because continuity
is preserved under pointwise equality, f is also continuous.


\begin{code}

---------------------------------------
-- §4. T-definable moduli of continuity
---------------------------------------
import TModuli

\end{code}

By restructuring the above proof, we adapt our b-translation to
directly construct T-definable moduli of continuity.  Now natural
numbers are translated to pairs of functions (ℕ → ℕ) → ℕ.  The idea is
that the second component is a modulus of continuity of the first one
which is the b-translation (of some term).  Working with a logical
relation and a predicate that are slightly different from above, we
show that every T-definable function (ℕ → ℕ) → ℕ has a T-definable
modulus of continuity.


\begin{code}

------------------------------------------------------
-- §5.1. Uniform continuity of T-definable functionals
------------------------------------------------------
import UniformContinuity

\end{code}

Working with a predicate UC ⊆ ρᵇ whose base case UC(f) states that the
restriction f↾𝟚ᴺ to the Cantor type ℕ → 𝟚 is uniformly continuous, we
show that if f : (ℕ → ℕ) → ℕ is T-definable then f↾𝟚ᴺ : (ℕ → 𝟚) → ℕ is
uniformly continuous.


\begin{code}

-----------------------------------------------------------
-- Appendix I. Continuity via a monadic interpretation of T
-----------------------------------------------------------
import TContMonad

\end{code}

In the introduction of the paper, we claim that the algorithm of
Coquand and Jaber's operational method can be represented by a monadic
translation of system T into itself.  Here we present such a monadic
interpretation of system T extended with a generic element into Agda.


\begin{code}

-----------------------------------------------------------------------
-- Appendix II. Dialogue tree representation of T-definable functionals
-----------------------------------------------------------------------
import Dialogue

\end{code}

The dialogue tree representing a function f : (ℕ → ℕ) → ℕ can be
considered as a notion of continuity of f which contains more
information than e.g. pointwise continuity.  Instead of building a
model of system T using dialogue trees, here we use our syntactic
method to show that every T-definable function (ℕ → ℕ) → ℕ has a
dialogue tree representation.
