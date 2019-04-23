
  ==========================================================================
  =                                                                        =
  =  Appendix II. Dialogue tree representation of T-definable functionals  =
  =                                                                        =
  ==========================================================================

     Chuangjie Xu, 2018


Escardó [Esc13] employs a dialogue interpretation of system T to show
that all T-definable functions (ℕ → ℕ) → ℕ are continuous.  One
advantage of this semantic approach is that the dialogue tree
interpreting f : (ℕ → ℕ) → ℕ provides more information than the
continuity of f.  Here we use our syntactic method to prove that every
T-definable function (ℕ → ℕ) → ℕ has a dialogue tree representation.


Reference.

[Esc13] M. H. Escardó.  Continuity of Gödel’s system T functionals via
        effectful forcing.  MFPS’2013.  Electronic Notes in
        Theoretical Computer Science, 298:119–141, 2013.

\begin{code}

module Dialogue where

open import Preliminaries
open import T

\end{code}

■ dialogue trees (for natural numbers)

\begin{code}

data DT : Set where
 η : ℕ → DT
 β : (ℕ → DT) → ℕ → DT

--
-- decoding dialogue trees into functions (ℕ → ℕ) → ℕ
--
dialogue : DT → ℕᴺ → ℕ
dialogue (η n)   _ = n
dialogue (β φ n) α = dialogue (φ (α n)) α

--
-- A function f : (ℕ → ℕ) → ℕ is eloquent if it has a dialogue tree representation.
--
eloquent : ((ℕ → ℕ) → ℕ) → Set
eloquent f = Σ \(d : DT) → (α : ℕᴺ) → dialogue d α ≡ f α

eloquent-extensional : {f g : (ℕ → ℕ) → ℕ}
                     → (∀ α → f α ≡ g α)
                     → eloquent f → eloquent g
eloquent-extensional ex (d , p) = d , λ α → trans (p α) (ex α)

\end{code}

■ Extending ℕ → DT to DT → DT

\begin{code}

keᴰᵀ : (ℕ → DT) → DT → DT
keᴰᵀ ξ (η n)   = ξ n
keᴰᵀ ξ (β φ n) = β (λ i → keᴰᵀ ξ (φ i)) n

dialogue-keᴰᵀ : {ξ : ℕ → DT} (d : DT) (α : ℕ → ℕ)
             → dialogue (keᴰᵀ ξ d) α ≡ dialogue (ξ (dialogue d α)) α
dialogue-keᴰᵀ (η n)   α = refl
dialogue-keᴰᵀ (β φ n) α = dialogue-keᴰᵀ (φ (α n)) α

--
-- The Kleisili extension for dialogue trees coincides with the one for b-translation.
--
keᴰᵀ-spec : {g : ℕ → (ℕ → ℕ) → ℕ} {ξ : ℕ → DT} → (∀ i α → dialogue (ξ i) α ≡ g i α)
         → {f : (ℕ → ℕ) → ℕ} (d : DT) → (∀ α → dialogue d α ≡ f α)
         → ∀ α → dialogue (keᴰᵀ ξ d) α ≡ g (f α) α
keᴰᵀ-spec {g} p (η n) q α = trans (p n α) (ap (λ x → g x α) (q α))
keᴰᵀ-spec {g} {ξ} p {f} (β φ n) q α = trans claim₀ (trans claim₁ claim₂)
 where
  claim₀ : dialogue (keᴰᵀ ξ (φ (α n))) α ≡ dialogue (ξ (dialogue (φ (α n)) α)) α
  claim₀ = dialogue-keᴰᵀ (φ (α n)) α
  claim₁ : dialogue (ξ (dialogue (φ (α n)) α)) α ≡ dialogue (ξ (f α)) α
  claim₁ = ap (λ x → dialogue (ξ x) α) (q α)
  claim₂ : dialogue (ξ (f α)) α ≡ g (f α) α
  claim₂ = p (f α) α

\end{code}

■ A dialogue predicate

\begin{code}

D : (ρ : Ty) → ⟦ ⟨ ρ ⟩ᵇ ⟧ʸ → Set
D  ι      f = eloquent f
D (σ ⇾ τ) f = {a : ⟦ ⟨ σ ⟩ᵇ ⟧ʸ} → D σ a → D τ (f a)

--
-- The Kleisli extension preserves the predicate.
--
D[KEᶥ] : (ρ : Ty)
       → {g : ℕ → ⟦ ⟨ ρ ⟩ᵇ ⟧ʸ} → ((i : ℕ) → D ρ (g i))
       → {Γ : Cxt} {γ : ⟦ Γ ⟧ˣ}
       → D (ι ⇾ ρ) (⟦ KEᶥ ρ ⟧ᵐ γ g)
      -- (f : ⟦ σ ⟧ʸ) → D ι f → D ρ (KE ρ f)
D[KEᶥ] ι dg (d , p) = keᴰᵀ (pr₁ ∘ dg) d , keᴰᵀ-spec (pr₂ ∘ dg) d p
D[KEᶥ] (_ ⇾ ρ) dg df = λ da → D[KEᶥ] ρ (λ i → dg i da) df

--
-- Extending the predicate to contexts
--
Dˣ : {Γ : Cxt} → ⟦ ⟪ Γ ⟫ᵇ ⟧ˣ → Set
Dˣ {ε}      ⋆      = 𝟙
Dˣ {Γ ₊ σ} (γ , a) = Dˣ γ × D σ a

--
-- Variables satisfy the predicate.
--
D[Var] : {Γ : Cxt} {ρ : Ty} {γ : ⟦ ⟪ Γ ⟫ᵇ ⟧ˣ}
       → Dˣ γ → (i : ∥ ρ ∈ Γ ∥) → D ρ (γ ₍ ⟨ i ⟩ᵛ ₎)
D[Var] {ε}      _      ()
D[Var] {Γ ₊ ρ} (δ , θ)  zero    = θ
D[Var] {Γ ₊ ρ} (δ , θ) (succ i) = D[Var] δ i

--
-- All T-definable elements satisfy the predicate.
--
Lemma[D] : {Γ : Cxt} {ρ : Ty} (t : T Γ ρ)
         → {γ : ⟦ ⟪ Γ ⟫ᵇ ⟧ˣ} → Dˣ γ → D ρ (⟦ t ᵇ ⟧ᵐ γ)
Lemma[D] (Var i) δ = D[Var] δ i
Lemma[D] (Lam t) δ = λ θ → Lemma[D] t (δ , θ)
Lemma[D] (f · a) δ = Lemma[D] f δ (Lemma[D] a δ)
Lemma[D] Zero _ = η 0 , (λ _ → refl)
Lemma[D] Succ _ = D[KEᶥ] ι (λ i → η (succ i) , λ _ → refl) {ε} {⋆}
Lemma[D] (Rec {ρ}) _ {a} ea {f} ef = D[KEᶥ] ρ er
 where
  er : (i : ℕ) → D ρ (rec a (λ k → f (λ α → k)) i)
  er zero = ea
  er (succ i) = ef (η i , (λ _ → refl)) (er i)

--
-- The generic element Ω satisfies the predicate.
--
D[Ω] : D (ι ⇾ ι) ⟦ Ω ⟧
D[Ω] = D[KEᶥ] ι (λ i → β η i , λ _ → refl) {ε} {⋆}

\end{code}

Theorem: All T-definable functions (ℕ → ℕ) → ℕ are eloquent.

\begin{code}

Theorem[TDT] : (f : ℕᴺ → ℕ) → T-definable f → eloquent f
Theorem[TDT] f (t , refl) = eᶠ
 where
  claim₀ : (α : ℕᴺ) → ⟦ t ᵇ · Ω ⟧ α ≡ ⟦ t ⟧ α
  claim₀ = Theorem[R] t
  claim₁ : eloquent (⟦ t ᵇ · Ω ⟧)
  claim₁ = Lemma[D] t ⋆ D[Ω]
  eᶠ : eloquent f
  eᶠ = eloquent-extensional claim₀ claim₁

\end{code}
