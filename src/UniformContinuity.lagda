
  =========================================================
  =                                                       =
  =  §5.1. Uniform continuity of T-definable functionals  =
  =                                                       =
  =========================================================

     Chuangjie Xu, 2018


Using our syntactic method with a predicate for uniform continuity, we
show that if f : (ℕ → ℕ) → ℕ is T-definable then its restriction
f↑𝟚ᴺ : (ℕ → 𝟚) → ℕ is uniformly continuous.  Our method seems related
to the sheaf model introduced in [Xu15].  For instance, the proof of
UC(Ω) is essentially same as the proof of the Yoneda Lemma in the model,
which plays a key role in the construction of the Fan functional.


Reference.

[Xu15]  C. Xu.  A continuous computational interpretation of type theories.
        PhD thesis, School of Computer Science, University of Birmingham, 2015.

\begin{code}

module UniformContinuity where

open import Preliminaries
open import T

\end{code}

◼ A mini library

\begin{code}

--
-- Booleans
--
data 𝟚 : Set where
 𝟎 𝟏 : 𝟚

Lemma[b≡0∨b≡1] : (b : 𝟚) → (b ≡ 𝟎) ∨ (b ≡ 𝟏)
Lemma[b≡0∨b≡1] 𝟎 = inl refl
Lemma[b≡0∨b≡1] 𝟏 = inr refl

--
-- The Cantor space/type
--
𝟚ᴺ : Set
𝟚ᴺ = 𝟚 ᴺ

𝟎ʷ : 𝟚ᴺ
𝟎ʷ = 𝟎 ʷ

𝟚toℕ : 𝟚 → ℕ
𝟚toℕ 𝟎 = 0
𝟚toℕ 𝟏 = 1

𝟚ᴺtoℕᴺ : 𝟚ᴺ → ℕᴺ
𝟚ᴺtoℕᴺ α i = 𝟚toℕ (α i)

--
-- Restriction of functions from the Baire space to the Cantor space
--
_↾𝟚ᴺ : {A : Set} → (ℕᴺ → A) → 𝟚ᴺ → A
(f ↾𝟚ᴺ) α = f (𝟚ᴺtoℕᴺ α)

\end{code}

■ Continuity of functions ℕᴺ → ℕ

\begin{code}

uniformly-continuous : (𝟚ᴺ → ℕ) → Set
uniformly-continuous f = Σ \(m : ℕ) → (α β : 𝟚ᴺ) → α ≡[ m ] β → f α ≡ f β

uc-extensional : {f g : 𝟚ᴺ → ℕ} → (∀ α → f α ≡ g α)
               → uniformly-continuous f → uniformly-continuous g
uc-extensional {f} {g} e (m , pᶠ) = m , pᵍ
 where
  pᵍ : (α β : 𝟚ᴺ) → α ≡[ m ] β → g α ≡ g β
  pᵍ α β em = trans (sym (e α)) (trans (pᶠ α β em) (e β))

--
-- Lemma: Any uniformly continuous function 𝟚ᴺ → ℕ has a maximun image.
--
-- Proof. By induction on the moduli of uniform continuity.
--
uc-max-image : {f : 𝟚ᴺ → ℕ} (m : ℕ) → ((α β : 𝟚ᴺ) → α ≡[ m ] β → f α ≡ f β)
             → Σ \(n : ℕ) → (α : 𝟚ᴺ) → f α ≤ n
uc-max-image {f}  0       p0  = f 𝟎ʷ , λ α → ≤refl' (p0 α 𝟎ʷ ≡[zero])
uc-max-image {f} (succ m) psm = n , prf
 where
  pm₀ : (α β : 𝟚ᴺ) → α ≡[ m ] β → f (𝟎 ✶ α) ≡ f (𝟎 ✶ β)
  pm₀ α β em = psm (𝟎 ✶ α) (𝟎 ✶ β) (≡[succ] refl em)
  IH₀ : Σ \(n : ℕ) → (α : 𝟚ᴺ) → f (𝟎 ✶ α) ≤ n
  IH₀ = uc-max-image m pm₀
  pm₁ : (α β : 𝟚ᴺ) → α ≡[ m ] β → f (𝟏 ✶ α) ≡ f (𝟏 ✶ β)
  pm₁ α β em = psm (𝟏 ✶ α) (𝟏 ✶ β) (≡[succ] refl em)
  IH₁ : Σ \(n : ℕ) → (α : 𝟚ᴺ) → f (𝟏 ✶ α) ≤ n
  IH₁ = uc-max-image m pm₁
  n₀ n₁ n : ℕ
  n₀ = pr₁ IH₀
  n₁ = pr₁ IH₁
  n  = max n₀ n₁
  prf : (α : 𝟚ᴺ) → f α ≤ n
  prf α with Lemma[b≡0∨b≡1] (head α)
  prf α | inl α0=0 = transport (λ x → x ≤ n) claim₀ claim₂
   where
    esm : (𝟎 ✶ tail α) ≡[ succ m ] α
    esm = ≡[succ] (sym α0=0) ≡[]-refl
    claim₀ : f (𝟎 ✶ tail α) ≡ f α
    claim₀ = psm (𝟎 ✶ tail α) α esm
    claim₁ : f (𝟎 ✶ tail α) ≤ n₀
    claim₁ = pr₂ IH₀ (tail α)
    claim₂ : f (𝟎 ✶ tail α) ≤ n
    claim₂ = ≤trans claim₁ (max-spec₀ n₀ n₁)
  prf α | inr α0=1 = transport (λ x → x ≤ n) claim₀ claim₂
   where
    esm : (𝟏 ✶ tail α) ≡[ succ m ] α
    esm = ≡[succ] (sym α0=1) ≡[]-refl
    claim₀ : f (𝟏 ✶ tail α) ≡ f α
    claim₀ = psm (𝟏 ✶ tail α) α esm
    claim₁ : f (𝟏 ✶ tail α) ≤ n₁
    claim₁ = pr₂ IH₁ (tail α)
    claim₂ : f (𝟏 ✶ tail α) ≤ n
    claim₂ = ≤trans claim₁ (max-spec₁ n₀ n₁)

\end{code}

■ A uniform-continuity predicate UC ⊆ ρᵇ

\begin{code}

UC : (ρ : Ty) → ⟦ ⟨ ρ ⟩ᵇ ⟧ʸ → Set
UC  ι      f = uniformly-continuous (f ↾𝟚ᴺ)
UC (σ ⇾ τ) h = (x : ⟦ ⟨ σ ⟩ᵇ ⟧ʸ) → UC σ x → UC τ (h x)

--
-- The Kleisli extension preserves the predicate.
--
UC[KEᶥ] : (ρ : Ty)
        → {g : ℕ → ⟦ ⟨ ρ ⟩ᵇ ⟧ʸ} → ((i : ℕ) → UC ρ (g i))
        → {Γ : Cxt} {γ : ⟦ Γ ⟧ˣ}
        → UC (ι ⇾ ρ) (⟦ KEᶥ ρ ⟧ᵐ γ g)
UC[KEᶥ] ι {g} ucg {_} {_} f (m , pᶠ) = k , prf
 where
  Max : (ℕ → ℕ) → ℕ → ℕ
  Max φ  0       = φ 0
  Max φ (succ i) = max (Max φ i) (φ (succ i))
  lemma : (f : ℕ → ℕ) → (∀ i → f i ≤ f (succ i)) → (i j : ℕ) → i ≤ j → f i ≤ f j
  lemma f up  0        0       ≤zero = ≤refl
  lemma f up  0       (succ j) ≤zero = ≤trans (lemma f up 0 j ≤zero) (up j)
  lemma f up (succ i)  0       ()
  lemma f up (succ i) (succ j) (≤succ r) = lemma (λ x → f (succ x)) (λ x → up (succ x)) i j r
  Max-spec₁ : {φ : ℕ → ℕ} {i j : ℕ} → i ≤ j → Max φ i ≤ Max φ j
  Max-spec₁ {φ} r = lemma (Max φ) (λ i → max-spec₀ (Max φ i) _) _ _ r
  Max-spec₀ : {φ : ℕ → ℕ} (i : ℕ) → φ i ≤ Max φ i
  Max-spec₀      0       = ≤refl
  Max-spec₀ {φ} (succ i) = max-spec₁ (Max φ i) (φ (succ i))
  Max-spec : {φ : ℕ → ℕ} {i j : ℕ} → i ≤ j → φ i ≤ Max φ j
  Max-spec {φ} {i} r = ≤trans (Max-spec₀ i) (Max-spec₁ r)
  φ : ℕ → ℕ
  φ i = pr₁ (ucg i)
  l : ℕ
  l = pr₁ (uc-max-image m pᶠ)
  n : ℕ
  n = Max φ l
  k : ℕ
  k = max m n
  k-spec : (α : 𝟚ᴺ) → pr₁ (ucg (f (𝟚ᴺtoℕᴺ α))) ≤ k
  k-spec α = ≤trans (Max-spec (pr₂ (uc-max-image m pᶠ) α)) (max-spec₁ m n)
  prf : (α β : 𝟚ᴺ) → α ≡[ k ] β → g (f (𝟚ᴺtoℕᴺ α)) (𝟚ᴺtoℕᴺ α) ≡ g (f (𝟚ᴺtoℕᴺ β)) (𝟚ᴺtoℕᴺ β)
  prf α β ek = trans e₂ e₁
   where
    e₀ : f (𝟚ᴺtoℕᴺ α) ≡ f (𝟚ᴺtoℕᴺ β)
    e₀ = pᶠ α β (≡[≤] ek (max-spec₀ m n))
    e₁ : g (f (𝟚ᴺtoℕᴺ α)) (𝟚ᴺtoℕᴺ β) ≡ g (f (𝟚ᴺtoℕᴺ β)) (𝟚ᴺtoℕᴺ β)
    e₁ = ap (λ i → g i (𝟚ᴺtoℕᴺ β)) e₀
    e₂ : g (f (𝟚ᴺtoℕᴺ α)) (𝟚ᴺtoℕᴺ α) ≡ g (f (𝟚ᴺtoℕᴺ α)) (𝟚ᴺtoℕᴺ β)
    e₂ = pr₂ (ucg (f (𝟚ᴺtoℕᴺ α))) α β (≡[≤] ek (k-spec α))
UC[KEᶥ] (_ ⇾ ρ) cg f cf = λ a ca → UC[KEᶥ] ρ (λ i → cg i a ca) f cf

--
-- Extending the predicate to contexts
--
UCˣ : {Γ : Cxt} → ⟦ ⟪ Γ ⟫ᵇ ⟧ˣ → Set
UCˣ {ε}      ⋆      = 𝟙
UCˣ {Γ ₊ ρ} (γ , a) = UCˣ γ × UC ρ a

--
-- Variables satisfy the predicate.
--
UC[Var] : {Γ : Cxt} {ρ : Ty} {γ : ⟦ ⟪ Γ ⟫ᵇ ⟧ˣ}
        → UCˣ γ → (i : ∥ ρ ∈ Γ ∥) → UC ρ (γ ₍ ⟨ i ⟩ᵛ ₎)
UC[Var] {ε}      _      ()
UC[Var] {Γ ₊ ρ} (δ , θ)  zero    = θ
UC[Var] {Γ ₊ ρ} (δ , θ) (succ i) = UC[Var] δ i

--
-- The b-translation of any T term satisfies the predicate.
--
Lemma[UC] : {Γ : Cxt} {ρ : Ty} (t : T Γ ρ)
          → {γ : ⟦ ⟪ Γ ⟫ᵇ ⟧ˣ} → UCˣ γ → UC ρ (⟦ t ᵇ ⟧ᵐ γ)
Lemma[UC] (Var i) δ = UC[Var] δ i
Lemma[UC] (Lam t) δ = λ _ θ → Lemma[UC] t (δ , θ)
Lemma[UC] (f · a) δ = Lemma[UC] f δ _ (Lemma[UC] a δ)
Lemma[UC] Zero _ = (0 , λ _ _ _ → refl) -- λ α → (0 , λ _ _ → refl)
Lemma[UC] Succ _ f (m , pᶠ) = (m , λ α β em → ap succ (pᶠ α β em))
Lemma[UC] (Rec {ρ}) _ a uca f ucf = UC[KEᶥ] ρ cg
 where
  cg : (i : ℕ) → UC ρ _
  cg  0       = uca
  cg (succ i) = ucf _ ((0 , λ _ _ _ → refl)) _ (cg i) -- ucf _ (0 , (λ _ _ _ → refl)) (cg i)

--
-- The generic element Ω satisfies the predicate.
--
UC[Ω] : UC (ι ⇾ ι) ⟦ Ω ⟧
UC[Ω] f (m , pᶠ) = k , prf
 where
  n : ℕ
  n = succ (pr₁ (uc-max-image m pᶠ))
  k : ℕ
  k = max m n
  k-spec : (α : 𝟚ᴺ) → succ ((f ↾𝟚ᴺ) α) ≤ k
  k-spec α = ≤trans (≤succ (pr₂ (uc-max-image m pᶠ) α)) (max-spec₁ m n)
  prf : (α β : 𝟚ᴺ) → α ≡[ k ] β → (𝟚ᴺtoℕᴺ α) (f (𝟚ᴺtoℕᴺ α)) ≡ (𝟚ᴺtoℕᴺ β) (f (𝟚ᴺtoℕᴺ β))
  prf α β ek = trans e₂ e₁
   where
    e₀ : f (𝟚ᴺtoℕᴺ α) ≡ f (𝟚ᴺtoℕᴺ β)
    e₀ = pᶠ α β (≡[≤] ek (max-spec₀ m n))
    e₁ : (𝟚ᴺtoℕᴺ β) (f (𝟚ᴺtoℕᴺ α)) ≡ (𝟚ᴺtoℕᴺ β) (f (𝟚ᴺtoℕᴺ β))
    e₁ = ap (𝟚ᴺtoℕᴺ β) e₀
    e₂ : (𝟚ᴺtoℕᴺ α) (f (𝟚ᴺtoℕᴺ α)) ≡ (𝟚ᴺtoℕᴺ β) (f (𝟚ᴺtoℕᴺ α))
    e₂ = ap 𝟚toℕ (≡[]-< ek (k-spec α))

\end{code}

■ Theorem: All T-definable functions ℕᴺ → ℕ are continuous.

\begin{code}

Theorem[TUC] : (f : ℕᴺ → ℕ) → T-definable f → uniformly-continuous (f ↾𝟚ᴺ)
Theorem[TUC] f (t , refl) = ucᶠ
 where
  claim₀ : (α : 𝟚ᴺ) → (⟦ t ᵇ · Ω ⟧ ↾𝟚ᴺ) α ≡ (⟦ t ⟧ ↾𝟚ᴺ) α
  claim₀ α = Theorem[R] t (𝟚ᴺtoℕᴺ α)
  claim₁ : uniformly-continuous (⟦ t ᵇ · Ω ⟧ ↾𝟚ᴺ)
  claim₁ = Lemma[UC] t ⋆ ⟦ Ω ⟧ UC[Ω]
  ucᶠ : uniformly-continuous (f ↾𝟚ᴺ)
  ucᶠ = uc-extensional claim₀ claim₁

\end{code}

