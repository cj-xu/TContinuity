
  ===========================================================
  =                                                         =
  =  Appendix I. Continuity via a monadic translation of T  =
  =                                                         =
  ===========================================================

     Chuangjie Xu, 2018


Coquand and Jaber [CJ12] extend dependent type theory with a new
constant f for a generic element, and then decorate its operational
semantics with forcing information to keep track of approximation
information about f as the computations proceed.  Their algorithm
(restricted to system T) to extract continuity information can be
given by a monadic translation from T (extended with a generic
element) to itself, which is an instance of the monadic translation
introduced in [Pow18].  Instead of a syntactic translation, we have a
monadic interpretation into Agda.  We provide only examples of
computing moduli of continuity but no formal proofs of continuity.


Reference.

[CJ12]  T. Coquand and G. Jaber.  A computational interpretation of
        forcing in type theory.  In Epistemology versus Ontology,
        volume 27, pages 203–213.  Springer Netherlands, 2012.

[Pow18] T. Powell.  A functional interpretation with state.  Accepted
        for Proceedings of Logic in Computer Science (LICS 2018), 2018.

\begin{code}

module TContMonad where

open import Preliminaries
open import T hiding (Num)

\end{code}

■ Extension of system T

We firstly extend system T with a generic element Ω.

\begin{code}

data TΩ (Γ : Cxt) : Ty → Set where
 Var  : {σ : Ty} → ∥ σ ∈ Γ ∥ → TΩ Γ σ
 Lam  : {σ τ : Ty} → TΩ (Γ ₊ σ) τ → TΩ Γ (σ ⇾ τ)
 _·_  : {σ τ : Ty} → TΩ Γ (σ ⇾ τ) → TΩ Γ σ → TΩ Γ τ
 Zero : TΩ Γ ι
 Succ : TΩ Γ (ι ⇾ ι)
 Rec  : {σ : Ty} → TΩ Γ (σ ⇾ (ι ⇾ σ ⇾ σ) ⇾ ι ⇾ σ)
 Ω    : TΩ Γ (ι ⇾ ι)

\end{code}

■ A monadic interpretation of TΩ

\begin{code}

module MonadicModel (M : Set → Set)
                    (η : {A : Set} → A → M A)
                    (_*_ : {A B : Set} → M (A → M B) → M A → M B)
                    ([Ω] : ℕᴺ → ℕ → M ℕ)where

 [_]ʸ : Ty → Set
 [ ι ]ʸ = ℕ
 [ σ ⇾ τ ]ʸ = [ σ ]ʸ → M [ τ ]ʸ

 recᴹ : {ρ : Ty} → [ ρ ]ʸ → [ ι ⇾ ρ ⇾ ρ ]ʸ → ℕ → M [ ρ ]ʸ
 recᴹ b g  0       = η b
 recᴹ b g (succ n) = g n * recᴹ b g n

 [_]ˣ : Cxt → Set
 [ ε ]ˣ     = 𝟙
 [ Γ ₊ σ ]ˣ = [ Γ ]ˣ × [ σ ]ʸ

 varᴹ : {Γ : Cxt} {σ : Ty} → [ Γ ]ˣ → ∥ σ ∈ Γ ∥ → [ σ ]ʸ
 varᴹ (γ , x)  zero    = x
 varᴹ (γ , x) (succ i) = varᴹ γ i

 [_] : {Γ : Cxt} {ρ : Ty} → TΩ Γ ρ → [ Γ ]ˣ → ℕᴺ → M [ ρ ]ʸ
 [ Var i ] ρ _ = η (varᴹ ρ i)
 [ Lam t ] ρ α = η (λ x → [ t ] (ρ , x) α)
 [ f · a ] ρ α = [ f ] ρ α * [ a ] ρ α
 [ Zero ]  _ _ = η 0
 [ Succ ]  _ _ = η (λ n → η (succ n))
 [ Rec ]   _ _ = η (λ b → η (λ g → η (λ n → recᴹ b g n)))
 [ Ω ]     _ α = η ([Ω] α)

\end{code}

■ A combination of the state monad and the list monad

\begin{code}

data List (A : Set) : Set where
 ε    : List A
 _::_ : A → List A → List A

M : Set → Set
M A = List ℕ → A × List ℕ

η : {A : Set} → A → M A
η a = λ u → (a , u)

_*_ : {A B : Set} → M (A → M B) → M A → M B
f * a = λ u → pr₁ (f u) (pr₁ (a (pr₂ (f u)))) (pr₂ (a (pr₂ (f u))))

[Ω] : ℕᴺ → ℕ → M ℕ
[Ω] α n u = (α n , n :: u)

open MonadicModel M η _*_ [Ω]

\end{code}

■ Moduli of continuity

Given a closed term t : ι in TΩ, we have its value "val t" and the
modulus of continuity "mod t" obtained as follows.

\begin{code}

val : TΩ ε ι → ℕᴺ → ℕ
val t α = pr₁ ([ t ] ⋆ α ε)

maxᴸ : List ℕ → ℕ
maxᴸ  ε       = 0
maxᴸ (i :: u) = max i (maxᴸ u)

# : List ℕ → ℕ
#  ε       = 0
# (i :: u) = succ (maxᴸ (i :: u))

mod : TΩ ε ι → ℕᴺ → ℕ
mod t α = # (pr₂ ([ t ] ⋆ α ε))

\end{code}

■ Computation experiments

\begin{code}

Num : ℕ → {Γ : Cxt} → TΩ Γ ι
Num  0       = Zero
Num (succ k) = Succ · Num k

t₀ : TΩ ε ι
t₀ = Num 4

result₀ :  mod t₀ 0ʷ ≡ 0
        ×  mod t₀ δ ≡ 0
        ×  mod t₀ succ ≡ 0
        ×  mod t₀ (12 ✶ 67 ✶ 8 ✶ 99 ✶ 3 ✶ 0ʷ) ≡ 0
result₀ = refl , refl , refl , refl


t₅ : TΩ ε ι
t₅ = Rec · (Ω · (Rec · (Ω · (Rec · (Ω · Num 17) · Lam Ω · (Ω · Num 17)))
                     · Lam Ω
                     · (Rec · (Rec · (Ω · (Ω · Num 2)) · Lam Succ · (Ω · Num 3))
                            · Lam Ω
                            · (Rec · (Ω · Num 1) · Lam Ω
                                   · (Rec · (Ω · Num 2) · Lam Succ · (Ω · Num 3))))))
         · (Lam Ω)
         · (Ω · Num 2)

result₅ :  mod t₅ 0ʷ ≡ 18
        ×  mod t₅ δ ≡ 18
        ×  mod t₅ succ ≡ 58
        ×  mod t₅ (12 ✶ 67 ✶ 8 ✶ 99 ✶ 3 ✶ 0ʷ) ≡ 68
result₅ = refl , refl , refl , refl

\end{code}
