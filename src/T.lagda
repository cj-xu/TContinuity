
  ================================================
  =                                              =
  =  §2. Gödel's system T and the b-translation  =
  =                                              =
  ================================================

     Chuangjie Xu, 2018


We define (the term language of) Gödel's system T in a lambda-calculus
form with de Bruijn indices instead of variables.  Then we embed T
into Agda by providing a standard interpretation of T in Agda.  As a
preliminary step of the syntactic method, we introduce a (generalized)
b-translation of system T into itself.  This is inspired by Oliva and
Steila's proof of the bar recursion closure theorem [OS18].  We relate
terms and their b-translation via a parametrized logical relation that
was introduced in one version of the Agda implementation of [Esc13].


Reference.

[Esc13] M. H. Escardó.  Continuity of Gödel’s system T functionals via
        effectful forcing.  MFPS’2013.  Electronic Notes in
        Theoretical Computer Science, 298:119–141, 2013.

[OS18]  P. Oliva and S. Steila.  A direct proof of Schwichtenberg’s bar
        recursion closure theorem.  The Journal of Symbolic Logic,
        83(1):70–83, 2018.

\begin{code}

module T where

open import Preliminaries

\end{code}

■ Gödel's system T

Here we work with the lambda-calculus version of system T, and with de
Bruijn indices instead of variables.

\begin{code}

infixr 30 _⇾_
infixl 20 _₊_
infixl 20 _·_

--
-- finite types
--
data Ty : Set where
 ι   : Ty
 _⇾_ : Ty → Ty → Ty

--
-- contexts as finite lists of types
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
 Zero : T Γ ι
 Succ : T Γ (ι ⇾ ι)
 Rec  : {σ : Ty} → T Γ (σ ⇾ (ι ⇾ σ ⇾ σ) ⇾ ι ⇾ σ)

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

Num : ℕ → {Γ : Cxt} → T Γ ι
Num  0       = Zero
Num (succ k) = Succ · Num k

Plus : {Γ : Cxt} → T Γ ι → T Γ ι → T Γ ι
Plus N M = Rec · N · Lam Succ · M

\end{code}

■ The standard interpretation of T into Agda

\begin{code}

⟦_⟧ʸ : Ty → Set
⟦ ι ⟧ʸ     = ℕ
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
⟦ Zero ⟧ᵐ  _ = 0
⟦ Succ ⟧ᵐ  _ = succ
⟦ Rec ⟧ᵐ   _ = rec

⟦_⟧ : {ρ : Ty} → T ε ρ → ⟦ ρ ⟧ʸ
⟦ t ⟧ = ⟦ t ⟧ᵐ ⋆

--
-- An (Agda) element a is "T-definable" if one can find a closed term
-- in T whose standard interpretation is a.
--
T-definable : {ρ : Ty} → ⟦ ρ ⟧ʸ → Set
T-definable {ρ} a = Σ \(t : T ε ρ) → ⟦ t ⟧ ≡ a

\end{code}

■ (Generalized) b-translation

Suppose the goal is to use the usual syntactic method to prove certain
property of functions □ → ℕ, where □ is a finite type.  The first step
is to perform a syntactic translation from system T to itself where
the base type ℕ is translated to □ → ℕ, so that the base case of the
predicate to work with is the targeting property of functions □ → ℕ.
Then we can achieve the goal by showing that the translation of any
term in T satisfies the predicate by induction on terms.

\begin{code}

module Translation (□ : Ty) where

 ⟨_⟩ᵇ : Ty → Ty
 ⟨ ι ⟩ᵇ     = □ ⇾ ι
 ⟨ σ ⇾ τ ⟩ᵇ = ⟨ σ ⟩ᵇ ⇾ ⟨ τ ⟩ᵇ

 ⟪_⟫ᵇ : Cxt → Cxt
 ⟪ ε ⟫ᵇ     = ε
 ⟪ Γ ₊ ρ ⟫ᵇ = ⟪ Γ ⟫ᵇ ₊ ⟨ ρ ⟩ᵇ

 ⟨_⟩ᵛ : {Γ : Cxt} {ρ : Ty} → ∥ ρ ∈ Γ ∥ → ∥ ⟨ ρ ⟩ᵇ ∈ ⟪ Γ ⟫ᵇ ∥
 ⟨ zero ⟩ᵛ   = zero
 ⟨ succ i ⟩ᵛ = succ ⟨ i ⟩ᵛ

 KEᶥ : {Γ : Cxt} (ρ : Ty)
     → T Γ ((ι ⇾ ⟨ ρ ⟩ᵇ) ⇾ ⟨ ι ⟩ᵇ ⇾ ⟨ ρ ⟩ᵇ)
 KEᶥ  ι      = Lam (Lam (Lam (ν₂ · (ν₁ · ν₀) · ν₀)))
 KEᶥ (_ ⇾ ρ) = Lam (Lam (Lam (KEᶥ ρ · Lam (ν₃ · ν₀ · ν₁) · ν₁)))

 infix 60 _ᵇ

 _ᵇ : {Γ : Cxt} {ρ : Ty} → T Γ ρ → T ⟪ Γ ⟫ᵇ ⟨ ρ ⟩ᵇ
 (Var i) ᵇ   = Var ⟨ i ⟩ᵛ
 (Lam t) ᵇ   = Lam (t ᵇ)
 (f · a) ᵇ   = f ᵇ · a ᵇ
 Zero ᵇ      = Lam Zero  -- λα.0
 Succ ᵇ      = Lam (Lam (Succ · (ν₁ · ν₀)))  -- λfx.succ(fx)
 (Rec {ρ}) ᵇ = Lam (Lam (KEᶥ ρ · (Rec · ν₁ · Lam (ν₁ · Lam ν₁))))  -- λaf.KE(rec(a,(λk.f(λα.k))))

\end{code}

■ Relating terms and their b-translations

Following Escardó [Esc13], we use a parametrized logical relation that
is introduced in one version of the Agda implementation of [Esc13] to
relate (the standard interpretations of) terms and their b-translations.

\begin{code}

 R : {ρ : Ty} → ⟦ □ ⟧ʸ → ⟦ ⟨ ρ ⟩ᵇ ⟧ʸ → ⟦ ρ ⟧ʸ → Set
 R {ι    } α f n = f α ≡ n
 R {σ ⇾ τ} α f g = {x : ⟦ ⟨ σ ⟩ᵇ ⟧ʸ} {y : ⟦ σ ⟧ʸ} → R α x y → R α (f x) (g y)

 Rˣ : {Γ : Cxt} → ⟦ □ ⟧ʸ → ⟦ ⟪ Γ ⟫ᵇ ⟧ˣ → ⟦ Γ ⟧ˣ → Set
 Rˣ {ε}     _  _       _      = 𝟙
 Rˣ {Γ ₊ ρ} α (γ , a) (ξ , b) = Rˣ α γ ξ × R α a b

 --
 -- The Kleisli extension preserves R.
 --
 R[KEᶥ] : (ρ : Ty) (α : ⟦ □ ⟧ʸ) {f : ℕ → ⟦ ⟨ ρ ⟩ᵇ ⟧ʸ} {g : ℕ → ⟦ ρ ⟧ʸ}
        → ((i : ℕ) → R α (f i) (g i))
        → {Γ : Cxt} {γ : ⟦ Γ ⟧ˣ}
        → R α (⟦ KEᶥ ρ ⟧ᵐ γ f) g
 R[KEᶥ]  ι      α ζ χ = trans (ζ _) (ap _ χ)
 R[KEᶥ] (_ ⇾ ρ) α ζ χ = λ η → R[KEᶥ] ρ α (λ i → ζ i η) χ

 --
 -- Variables in related contexts are related.
 --
 R[Var] : {Γ : Cxt} {ρ : Ty} {γ : ⟦ ⟪ Γ ⟫ᵇ ⟧ˣ} {ξ : ⟦ Γ ⟧ˣ} (α : ⟦ □ ⟧ʸ)
        → Rˣ α γ ξ → (i : ∥ ρ ∈ Γ ∥) → R α (γ ₍ ⟨ i ⟩ᵛ ₎) (ξ ₍ i ₎)
 R[Var] {ε}     α  _      ()
 R[Var] {Γ ₊ ρ} α (_ , θ)  zero    = θ
 R[Var] {Γ ₊ ρ} α (ζ , _) (succ i) = R[Var] α ζ i

 --
 -- Terms are related to their b-translations.
 --
 Lemma[R] : {Γ : Cxt} {ρ : Ty} (t : T Γ ρ) (α : ⟦ □ ⟧ʸ)
          → {γ : ⟦ ⟪ Γ ⟫ᵇ ⟧ˣ} {ξ : ⟦ Γ ⟧ˣ} → Rˣ α γ ξ
          → R α (⟦ t ᵇ ⟧ᵐ γ) (⟦ t ⟧ᵐ ξ)
 Lemma[R] (Var i)  α ζ = R[Var] α ζ i
 Lemma[R] (Lam t)  α ζ = λ χ → Lemma[R] t α (ζ , χ)
 Lemma[R] (f · a)  α ζ = Lemma[R] f α ζ (Lemma[R] a α ζ)
 Lemma[R] Zero     _ _ = refl
 Lemma[R] Succ     α _ = ap succ
 Lemma[R] (Rec{ρ}) α _ {x} {y} χ {f} {g} η = R[KEᶥ] ρ α claim
  where
   claim : (i : ℕ) → R α (rec x (λ k → f (λ _ → k)) i) (rec y g i)
   claim  0       = χ
   claim (succ i) = η refl (claim i)

\end{code}

◼ Take □ ≡ ι ⇾ ι

Because our goal is to prove continuity of functions (ℕ → ℕ) → ℕ,
here we take □ ≡ ι ⇾ ι.

\begin{code}

open Translation (ι ⇾ ι) public

--
-- a T-definable generic element ℕᵇ → ℕᵇ
--
Ω : {Γ : Cxt} → T Γ (⟨ ι ⇾ ι ⟩ᵇ) -- ((ℕ → ℕ) → ℕ) → (ℕ → ℕ) → ℕ
Ω = Lam (Lam (ν₀ · (ν₁ · ν₀)))   -- λfα.α(fα)

--
-- Theorem: Any f : (ℕ → ℕ) → ℕ is pointwise equal to fᵇ(Ω).
--
Theorem[R] : (t : T ε ((ι ⇾ ι) ⇾ ι))
           → (α : ℕᴺ) → ⟦ t ᵇ · Ω ⟧ α ≡ ⟦ t ⟧ α
Theorem[R] t α = Lemma[R] t α ⋆ (ap α)

\end{code}
