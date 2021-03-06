
  ==========================================
  =                                        =
  =  §4. T-definable moduli of continuity  =
  =                                        =
  ==========================================

     Chuangjie Xu, 2018


We combine the construction of moduli of continuity with the
b-translation, similarly to the construction of general-bar-recursion
functionals in [OS18].  For this, we have to extend system T with
cartesian products.  In specific, natural numbers are interpreted as
pairs of functions (ℕ → ℕ) → ℕ.  The idea is that the second component
of such a pair is a modulus of continuity of the first component.
Working with a logical relation and a predicate that are slightly
different from the ones in §2 and §3, we show that every T-definable
function (ℕ → ℕ) → ℕ has a T-definable modulus of continuity.


Reference.

[OS18]  P. Oliva and S. Steila.  A direct proof of Schwichtenberg’s bar
        recursion closure theorem.  The Journal of Symbolic Logic,
        83(1):70–83, 2018.

\begin{code}

module TModuli where

open import Preliminaries

\end{code}

■ Extending system T with cartesian products 

\begin{code}

infixr 40 _⊠_
infixr 30 _⇾_
infixl 20 _₊_
infixl 20 _·_

--
-- types
--
data Ty : Set where
 ι       : Ty
 _⊠_ _⇾_ : Ty → Ty → Ty

--
-- contexts
--
data Cxt : Set where
 ε   : Cxt
 _₊_ : Cxt → Ty → Cxt

--
-- indices of types (i.e. variables in context)
--
data ∥_∈_∥ (σ : Ty) : Cxt → Set where
 zero : {Γ : Cxt} → ∥ σ ∈ (Γ ₊ σ) ∥
 succ : {τ : Ty} {Γ : Cxt} → ∥ σ ∈ Γ ∥ → ∥ σ ∈ Γ ₊ τ ∥

--
-- terms
--
data T (Γ : Cxt) : Ty → Set where
 Var  : {σ : Ty} → ∥ σ ∈ Γ ∥ → T Γ σ
 Lam  : {σ τ : Ty} → T (Γ ₊ σ) τ → T Γ (σ ⇾ τ)
 _·_  : {σ τ : Ty} → T Γ (σ ⇾ τ) → T Γ σ → T Γ τ
 Pair : {σ τ : Ty} → T Γ (σ ⇾ τ ⇾ σ ⊠ τ)
 Pr1  : {σ τ : Ty} → T Γ (σ ⊠ τ ⇾ σ)
 Pr2  : {σ τ : Ty} → T Γ (σ ⊠ τ ⇾ τ)
 Zero : T Γ ι
 Succ : T Γ (ι ⇾ ι)
 Rec  : {σ : Ty} → T Γ (σ ⇾ (ι ⇾ σ ⇾ σ) ⇾ ι ⇾ σ)

\end{code}

■ The standard interpretation of T into Agda

\begin{code}

⟦_⟧ʸ : Ty → Set
⟦ ι ⟧ʸ     = ℕ
⟦ σ ⊠ τ ⟧ʸ = ⟦ σ ⟧ʸ × ⟦ τ ⟧ʸ
⟦ σ ⇾ τ ⟧ʸ = ⟦ σ ⟧ʸ → ⟦ τ ⟧ʸ

⟦_⟧ˣ : Cxt → Set
⟦ ε ⟧ˣ     = 𝟙
⟦ Γ ₊ ρ ⟧ˣ = ⟦ Γ ⟧ˣ × ⟦ ρ ⟧ʸ

_₍_₎ : {Γ : Cxt} {ρ : Ty} → ⟦ Γ ⟧ˣ → ∥ ρ ∈ Γ ∥ → ⟦ ρ ⟧ʸ
(_ , a) ₍ zero ₎   = a
(γ , _) ₍ succ i ₎ = γ ₍ i ₎

⟦_⟧ᵐ : {Γ : Cxt} {σ : Ty} → T Γ σ → ⟦ Γ ⟧ˣ → ⟦ σ ⟧ʸ
⟦ Var i ⟧ᵐ γ = γ ₍ i ₎
⟦ Lam t ⟧ᵐ γ = λ a → ⟦ t ⟧ᵐ (γ , a)
⟦ f · a ⟧ᵐ γ = ⟦ f ⟧ᵐ γ (⟦ a ⟧ᵐ γ)
⟦ Pair ⟧ᵐ  _ = _,_
⟦ Pr1 ⟧ᵐ   _ = pr₁
⟦ Pr2 ⟧ᵐ   _ = pr₂
⟦ Zero ⟧ᵐ  _ = 0
⟦ Succ ⟧ᵐ  _ = succ
⟦ Rec ⟧ᵐ   _ = rec

⟦_⟧ : {ρ : Ty} → T ε ρ → ⟦ ρ ⟧ʸ
⟦ t ⟧ = ⟦ t ⟧ᵐ ⋆

--
-- An (Agda) element a is "T-definable" if one can find a closed T
-- term whose standard interpretation is a.
--
T-definable : {ρ : Ty} → ⟦ ρ ⟧ʸ → Set
T-definable {ρ} a = Σ \(t : T ε ρ) → ⟦ t ⟧ ≡ a

\end{code}

■ Some auxiliaries

\begin{code}

ν₀ : {Γ : Cxt} {ρ : Ty} → T (Γ ₊ ρ) ρ
ν₀ = Var zero

ν₁ : {Γ : Cxt} {ρ σ : Ty} → T (Γ ₊ ρ ₊ σ) ρ
ν₁ = Var (succ zero)

ν₂ : {Γ : Cxt} {ρ σ₀ σ₁ : Ty} → T (Γ ₊ ρ ₊ σ₀ ₊ σ₁) ρ
ν₂ = Var (succ (succ zero))

ν₃ : {Γ : Cxt} {ρ σ₀ σ₁ σ₂ : Ty} → T (Γ ₊ ρ ₊ σ₀ ₊ σ₁ ₊ σ₂) ρ
ν₃ = Var (succ (succ (succ zero)))

Max : {Γ : Cxt} → T Γ (ι ⇾ ι ⇾ ι)
Max = Rec · Lam ν₀ · Lam (Lam (Rec · (Succ · ν₁) · Lam (Lam (Succ · (ν₂ · ν₁)))))

Max-spec₀ : (n m : ℕ) → n ≤ ⟦ Max ⟧ n m
Max-spec₀  0        m       = ≤zero
Max-spec₀ (succ n)  0       = ≤refl
Max-spec₀ (succ n) (succ m) = ≤succ (Max-spec₀ n m)

Max-spec₁ : (n m : ℕ) → m ≤ ⟦ Max ⟧ n m
Max-spec₁  0        m       = ≤refl
Max-spec₁ (succ n)  0       = ≤zero
Max-spec₁ (succ n) (succ m) = ≤succ (Max-spec₁ n m)

\end{code}

■ Continuity of functions ℕᴺ → ℕ

\begin{code}

_is-a-modulus-of-continuity-of_ : (ℕᴺ → ℕ) → (ℕᴺ → ℕ) → Set
M is-a-modulus-of-continuity-of f = (α β : ℕᴺ) → α ≡[ M α ] β → f α ≡ f β

MoC-extensional : {f g M : ℕᴺ → ℕ}
                → ((α : ℕᴺ) → f α ≡ g α) → M is-a-modulus-of-continuity-of f
                → M is-a-modulus-of-continuity-of g
MoC-extensional ex cf α β em = trans (sym (ex α)) (trans (cf α β em) (ex β))

\end{code}

■ A variant of b-translation of T into itself

\begin{code}

⟨_⟩ᵇ : Ty → Ty
⟨ ι ⟩ᵇ     = ((ι ⇾ ι) ⇾ ι) ⊠ ((ι ⇾ ι) ⇾ ι)
⟨ σ ⊠ τ ⟩ᵇ = ⟨ σ ⟩ᵇ ⊠ ⟨ τ ⟩ᵇ
⟨ σ ⇾ τ ⟩ᵇ = ⟨ σ ⟩ᵇ ⇾ ⟨ τ ⟩ᵇ

⟪_⟫ᵇ : Cxt → Cxt
⟪ ε ⟫ᵇ     = ε
⟪ Γ ₊ ρ ⟫ᵇ = ⟪ Γ ⟫ᵇ ₊ ⟨ ρ ⟩ᵇ

⟨_⟩ᵛ : {Γ : Cxt} {ρ : Ty} → ∥ ρ ∈ Γ ∥ → ∥ ⟨ ρ ⟩ᵇ ∈ ⟪ Γ ⟫ᵇ ∥
⟨ zero ⟩ᵛ   = zero
⟨ succ i ⟩ᵛ = succ ⟨ i ⟩ᵛ

KEᶥ : {Γ : Cxt} (ρ : Ty)
    → T Γ ((ι ⇾ ⟨ ρ ⟩ᵇ) ⇾ ⟨ ι ⟩ᵇ ⇾ ⟨ ρ ⟩ᵇ)
KEᶥ  ι      = Lam (Lam (Pair · Lam (Pr1 · (ν₂ · (Pr1 · ν₁ · ν₀)) · ν₀)
                             · Lam (Max · (Pr2 · (ν₂ · (Pr1 · ν₁ · ν₀)) · ν₀) · (Pr2 · ν₁ · ν₀))))
KEᶥ (σ ⊠ τ) = Lam (Lam (Pair · (KEᶥ σ · Lam (Pr1 · (ν₂ · ν₀)) · ν₀)
                             · (KEᶥ τ · Lam (Pr2 · (ν₂ · ν₀)) · ν₀)))
KEᶥ (_ ⇾ ρ) = Lam (Lam (Lam (KEᶥ ρ · Lam (ν₃ · ν₀ · ν₁) · ν₁)))

infix 60 _ᵇ

_ᵇ : {Γ : Cxt} {ρ : Ty} → T Γ ρ → T ⟪ Γ ⟫ᵇ ⟨ ρ ⟩ᵇ
Var i ᵇ   = Var ⟨ i ⟩ᵛ
Lam t ᵇ   = Lam (t ᵇ)
(f · a) ᵇ   = f ᵇ · a ᵇ
Pair ᵇ    = Pair
Pr1 ᵇ     = Pr1
Pr2 ᵇ     = Pr2
Zero ᵇ    = Pair · Lam Zero · Lam Zero
Succ ᵇ    = Lam (Pair · Lam (Succ · (Pr1 · ν₁ · ν₀)) · (Pr2 · ν₀))
Rec {ρ} ᵇ = Lam (Lam (KEᶥ ρ · (Rec · ν₁ · Lam (ν₁ · (Pair · Lam ν₁ · Lam Zero)))))

\end{code}

■ Generic element Ω

\begin{code}

Ω : {Γ : Cxt} → T Γ (⟨ ι ⟩ᵇ ⇾ ⟨ ι ⟩ᵇ)
Ω = Lam (Pair · Lam (ν₀ · (Pr1 · ν₁ · ν₀)) · Lam (Max · (Pr2 · ν₁ · ν₀) · (Succ · (Pr1 · ν₁ · ν₀))))

\end{code}

■ Relating the T terms and their b-translation

We define a parametrised logical relation R between (the standard
interpretations of) T terms and their b-translation.

\begin{code}

R : {ρ : Ty} → ℕᴺ → ⟦ ⟨ ρ ⟩ᵇ ⟧ʸ → ⟦ ρ ⟧ʸ → Set
R {ι    } α f n = pr₁ f α ≡ n
R {σ ⊠ τ} α f g = R α (pr₁ f) (pr₁ g) × R α (pr₂ f) (pr₂ g)
R {σ ⇾ τ} α f g = {x : ⟦ ⟨ σ ⟩ᵇ ⟧ʸ} {y : ⟦ σ ⟧ʸ} → R α x y → R α (f x) (g y)

--
-- The Kleisli extension preserves R.
--
R[KEᶥ] : (ρ : Ty) (α : ℕᴺ) {f : ℕ → ⟦ ⟨ ρ ⟩ᵇ ⟧ʸ} {g : ℕ → ⟦ ρ ⟧ʸ}
       → ((i : ℕ) → R α (f i) (g i))
       → {Γ : Cxt} {γ : ⟦ Γ ⟧ˣ}
       → R α (⟦ KEᶥ ρ ⟧ᵐ γ f) g
R[KEᶥ]  ι      α ζ χ = trans (ζ _) (ap _ χ)
R[KEᶥ] (σ ⊠ τ) α ζ χ = R[KEᶥ] σ α (pr₁ ∘ ζ) χ , R[KEᶥ] τ α (pr₂ ∘ ζ) χ
R[KEᶥ] (_ ⇾ ρ) α ζ χ = λ η → R[KEᶥ] ρ α (λ i → ζ i η) χ

--
-- Extending the logical relation to contexts
--
Rˣ : {Γ : Cxt} → ℕᴺ → ⟦ ⟪ Γ ⟫ᵇ ⟧ˣ → ⟦ Γ ⟧ˣ → Set
Rˣ {ε}     _  _       _      = 𝟙
Rˣ {Γ ₊ ρ} α (γ , a) (ξ , b) = Rˣ α γ ξ × R α a b

--
-- Variables in related contexts are related.
--
R[Var] : {Γ : Cxt} {ρ : Ty} {γ : ⟦ ⟪ Γ ⟫ᵇ ⟧ˣ} {ξ : ⟦ Γ ⟧ˣ} (α : ℕᴺ)
       → Rˣ α γ ξ → (i : ∥ ρ ∈ Γ ∥) → R α (γ ₍ ⟨ i ⟩ᵛ ₎) (ξ ₍ i ₎)
R[Var] {ε}     α  _      ()
R[Var] {Γ ₊ ρ} α (_ , θ)  zero    = θ
R[Var] {Γ ₊ ρ} α (ζ , _) (succ i) = R[Var] α ζ i

--
-- Any T term and its b-translation are related.
--
Lemma[R] : {Γ : Cxt} {ρ : Ty} (t : T Γ ρ) (α : ℕᴺ)
         → {γ : ⟦ ⟪ Γ ⟫ᵇ ⟧ˣ} {ξ : ⟦ Γ ⟧ˣ} → Rˣ α γ ξ
         → R α (⟦ t ᵇ ⟧ᵐ γ) (⟦ t ⟧ᵐ ξ)
Lemma[R] (Var i)  α ζ = R[Var] α ζ i
Lemma[R] (Lam t)  α ζ = λ χ → Lemma[R] t α (ζ , χ)
Lemma[R] (f · a)  α ζ = Lemma[R] f α ζ (Lemma[R] a α ζ)
Lemma[R] Pair     _ _ = λ χ₀ χ₁ → χ₀ , χ₁
Lemma[R] Pr1      _ _ = pr₁
Lemma[R] Pr2      _ _ = pr₂
Lemma[R] Zero     _ _ = refl
Lemma[R] Succ     α _ = ap succ
Lemma[R] (Rec{ρ}) α _ {x} {y} χ {f} {g} η = R[KEᶥ] ρ α claim
 where
  claim : (i : ℕ) → R α (rec x (λ k → f ((λ _ → k) , (λ _ → 0))) i) (rec y g i)
  claim  0       = χ
  claim (succ i) = η refl (claim i)

--
-- In particular, any t : (ℕ → ℕ) → ℕ is pointwise equal to the first
-- component of tᵇ(Ω).
--
Theorem[R] : (t : T ε ((ι ⇾ ι) ⇾ ι))
           → (α : ℕᴺ) → pr₁ (⟦ t ᵇ · Ω ⟧) α ≡ ⟦ t ⟧ α
Theorem[R] t α = Lemma[R] t α ⋆ (ap α)

\end{code}

■ A continuity predicate

\begin{code}

C : (ρ : Ty) → ⟦ ⟨ ρ ⟩ᵇ ⟧ʸ → Set
C  ι      (f , M) = M is-a-modulus-of-continuity-of f
C (σ ⊠ τ) (f , g) = C σ f × C τ g
C (σ ⇾ τ)  f      = {a : ⟦ ⟨ σ ⟩ᵇ ⟧ʸ} → C σ a → C τ (f a)

--
-- The Kleisli extension preserves the predicate.
--
C[KEᶥ] : (ρ : Ty)
       → {g : ℕ → ⟦ ⟨ ρ ⟩ᵇ ⟧ʸ} → ((i : ℕ) → C ρ (g i))
       → {Γ : Cxt} {γ : ⟦ Γ ⟧ˣ}
       → C (ι ⇾ ρ) (⟦ KEᶥ ρ ⟧ᵐ γ g)
C[KEᶥ]  ι {g} cg {_} {_} {f , M} cf α β em = trans e₂ e₁
 where
  e₀ : f α ≡ f β
  e₀ = cf α β (≡[≤] em (Max-spec₁ (pr₂ (g (f α)) α) (M α)))
  e₁ : pr₁ (g (f α)) β ≡ pr₁ (g (f β)) β
  e₁ = ap (λ i → pr₁ (g i) β) e₀
  e₂ : pr₁ (g (f α)) α ≡ pr₁ (g (f α)) β
  e₂ = cg (f α) α β (≡[≤] em (Max-spec₀ _ _))
C[KEᶥ] (σ ⊠ τ) cg cf = C[KEᶥ] σ (pr₁ ∘ cg) cf , C[KEᶥ] τ (pr₂ ∘ cg) cf
C[KEᶥ] (_ ⇾ ρ) cg cf = λ ca → C[KEᶥ] ρ (λ i → cg i ca) cf

--
-- Extending the predicate to contexts
--
Cˣ : {Γ : Cxt} → ⟦ ⟪ Γ ⟫ᵇ ⟧ˣ → Set
Cˣ {ε}      ⋆      = 𝟙
Cˣ {Γ ₊ ρ} (γ , a) = Cˣ γ × C ρ a

--
-- Variables satisfy the predicate.
--
C[Var] : {Γ : Cxt} {ρ : Ty} {γ : ⟦ ⟪ Γ ⟫ᵇ ⟧ˣ}
       → Cˣ γ → (i : ∥ ρ ∈ Γ ∥) → C ρ (γ ₍ ⟨ i ⟩ᵛ ₎)
C[Var] {ε}      _      ()
C[Var] {Γ ₊ ρ} (δ , θ)  zero    = θ
C[Var] {Γ ₊ ρ} (δ , θ) (succ i) = C[Var] δ i

--
-- The b-translation of any T term satisfies the predicate.
--
Lemma[C] : {Γ : Cxt} {ρ : Ty} (t : T Γ ρ)
         → {γ : ⟦ ⟪ Γ ⟫ᵇ ⟧ˣ} → Cˣ γ → C ρ (⟦ t ᵇ ⟧ᵐ γ)
Lemma[C] (Var i)  δ = C[Var] δ i
Lemma[C] (Lam t)  δ = λ θ → Lemma[C] t (δ , θ)
Lemma[C] (f · a)  δ = Lemma[C] f δ (Lemma[C] a δ)
Lemma[C] Pair     _ = λ θ₀ θ₁ → θ₀ , θ₁
Lemma[C] Pr1      _ = pr₁
Lemma[C] Pr2      _ = pr₂
Lemma[C] Zero     _ = λ _ _ _ → refl
Lemma[C] Succ     _ = λ p α β e → ap succ (p α β e)
Lemma[C] (Rec{ρ}) _ {a} ca {f} cf = C[KEᶥ] ρ cr
 where
  cr : (i : ℕ) → C ρ (rec a (λ k → f ((λ _ → k) , λ _ → 0)) i)
  cr  0       = ca
  cr (succ i) = cf (λ _ _ _ → refl) (cr i)

--
-- The generic element also satisfies the predicate.
--
C[Ω] : C (ι ⇾ ι) ⟦ Ω ⟧
C[Ω] {f , M} p α β em = trans e₂ e₁
 where
  e₀ : f α ≡ f β
  e₀ = p α β (≡[≤] em (Max-spec₀ (M α) _))
  e₁ : β (f α) ≡ β (f β)
  e₁ = ap β e₀
  e₂ : α (f α) ≡ β (f α)
  e₂ = ≡[]-< em (Max-spec₁ (M α) _)

\end{code}

■ Theorem: Every T-definable function (ℕ → ℕ) → ℕ has a T-definable
           modulus of continuity.

\begin{code}

Theorem[TModCont] : ∀ (f : ℕᴺ → ℕ) → T-definable f
                    → Σ \(M : ℕᴺ → ℕ) → T-definable M
                                      × M is-a-modulus-of-continuity-of f
Theorem[TModCont] f (t , refl) = M , defᴹ , mcf
 where
  M : ℕᴺ → ℕ
  M = pr₂ (⟦ t ᵇ · Ω ⟧)
  defᴹ : T-definable M
  defᴹ = Pr2 · (t ᵇ · Ω) , refl
  g : ℕᴺ → ℕ
  g = pr₁ (⟦ t ᵇ · Ω ⟧)
  mcg : M is-a-modulus-of-continuity-of g
  mcg = Lemma[C] t ⋆ C[Ω]
  ex  : (α : ℕᴺ) → g α ≡ f α
  ex  = Theorem[R] t
  mcf : M is-a-modulus-of-continuity-of f
  mcf = MoC-extensional ex mcg

\end{code}

■ Moduli of continuity

\begin{code}

mod : T ε ((ι ⇾ ι) ⇾ ι) → ℕᴺ → ℕ
mod t = pr₁ (Theorem[TModCont] ⟦ t ⟧ (t , refl))

modⁱⁿᵗ : T ε ((ι ⇾ ι) ⇾ ι) → T ε ((ι ⇾ ι) ⇾ ι)
modⁱⁿᵗ t = pr₁ (pr₁ (pr₂ (Theorem[TModCont] ⟦ t ⟧ (t , refl))))

\end{code}

■ Computation experiment

\begin{code}

Num : ℕ → {Γ : Cxt} → T Γ ι
Num  0       = Zero
Num (succ k) = Succ · Num k

Plus : {Γ : Cxt} → T Γ ι → T Γ ι → T Γ ι
Plus N M = Rec · N · Lam Succ · M

t₃ : T ε ((ι ⇾ ι) ⇾ ι)
t₃ = Lam (Rec · Num 0 · Lam ν₁ · (ν₀ · Num 0))

t₃-interpretation : ⟦ t₃ ⟧ ≡ λ α → rec 0 (λ _ → α) (α 0)
t₃-interpretation = refl

result₃ :  mod t₃ 0ʷ ≡ 1
        ×  mod t₃ δ ≡ 1
        ×  mod t₃ succ ≡ 1
        ×  mod t₃ (12 ✶ 67 ✶ 8 ✶ 99 ✶ 3 ✶ 0ʷ) ≡ 13
result₃ = refl , refl , refl , refl

\end{code}
