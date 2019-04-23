
  ===============================================
  =                                             =
  =  §3. Continuity of T-definable functionals  =
  =                                             =
  ===============================================

     Chuangjie Xu, 2018


We carry out the usual steps of the syntactic method on the
b-translation of system T:

(1) Define a continuity predicate C ⊆ ρᵇ inductively on ρ
    where the base case C(f) is the continuity of f.

(2) Show C(tᵇ) for all t in T by induction on t.

Moreover we prove C(Ω) and thus have C(fᵇ(Ω)), i.e. fᵇ(Ω) is
continuous, for any f : (ℕ → ℕ) → ℕ in T.  Then f is also
continuous because it is pointwise equal to fᵇ(Ω).


Reference.

[Esc13] M. H. Escardó.  Continuity of Gödel’s system T functionals via
        effectful forcing.  MFPS’2013.  Electronic Notes in
        Theoretical Computer Science, 298:119–141, 2013.

[OS18]  P. Oliva and S. Steila.  A direct proof of Schwichtenberg’s bar
        recursion closure theorem.  The Journal of Symbolic Logic,
        83(1):70–83, 2018.

\begin{code}

module Continuity where

open import Preliminaries
open import T

\end{code}

■ Continuity of functions ℕᴺ → ℕ

\begin{code}

continuous : (ℕᴺ → ℕ) → Set
continuous f = (α : ℕᴺ) → Σ \(m : ℕ) → (β : ℕᴺ) → α ≡[ m ] β → f α ≡ f β

--
-- Continuity is preserved under pointwise equality.
--
continuity-extensional : {f g : ℕᴺ → ℕ} → (∀ α → f α ≡ g α)
                       → continuous f → continuous g
continuity-extensional {f} {g} e cf α = m , prf
 where
  m : ℕ
  m = pr₁ (cf α)
  prf : (β : ℕᴺ) → α ≡[ m ] β → g α ≡ g β
  prf β em = trans (sym (e α)) (trans (pr₂ (cf α) β em) (e β))

\end{code}

■ A continuity predicate C ⊆ ρᵇ

\begin{code}

C : (ρ : Ty) → ⟦ ⟨ ρ ⟩ᵇ ⟧ʸ → Set
C  ι      f = continuous f
C (σ ⇾ τ) f = {a : ⟦ ⟨ σ ⟩ᵇ ⟧ʸ} → C σ a → C τ (f a)

--
-- The Kleisli extension preserves the predicate.
--
C[KEᶥ] : (ρ : Ty)
       → {g : ℕ → ⟦ ⟨ ρ ⟩ᵇ ⟧ʸ} → ((i : ℕ) → C ρ (g i))
       → {Γ : Cxt} {γ : ⟦ Γ ⟧ˣ}
       → C (ι ⇾ ρ) (⟦ KEᶥ ρ ⟧ᵐ γ g)
C[KEᶥ] ι {g} cg {_} {_} {f} cf = goal
 where
  goal : continuous (λ α → g (f α) α)
  goal α = m , prf
   where
    n₀ n₁ : ℕ
    n₀ = pr₁ (cg (f α) α)
    n₁ = pr₁ (cf α)
    m : ℕ
    m = max n₀ n₁
    prf : (β : ℕᴺ) → α ≡[ m ] β → g (f α) α ≡ g (f β) β
    prf β em = trans e₂ e₁
     where
      e₀ : f α ≡ f β
      e₀ = pr₂ (cf α) β (≡[≤] em (max-spec₁ n₀ n₁))
      e₁ : g (f α) β ≡ g (f β) β
      e₁ = ap (λ i → g i β) e₀
      e₂ : g (f α) α ≡ g (f α) β
      e₂ = pr₂ (cg (f α) α) β (≡[≤] em (max-spec₀ n₀ n₁))
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
Lemma[C] (Var i) δ = C[Var] δ i
Lemma[C] (Lam t) δ = λ θ → Lemma[C] t (δ , θ)
Lemma[C] (f · a) δ = Lemma[C] f δ (Lemma[C] a δ)
Lemma[C] Zero _ = λ α → (0 , λ _ _ → refl)
Lemma[C] Succ _ {f} cf α = m , prf
 where
  m : ℕ
  m = pr₁ (cf α)
  prf : (β : ℕᴺ) → α ≡[ m ] β → succ (f α) ≡ succ (f β)
  prf β em = ap succ (pr₂ (cf α) β em)
Lemma[C] (Rec {ρ}) _ {a} ca {f} cf = C[KEᶥ] ρ cr
 where
  cr : (i : ℕ) → C ρ (rec a (λ k → f λ _ → k) i)
  cr  0       = ca
  cr (succ i) = cf (λ _ → 0 , (λ _ _ → refl)) (cr i)

--
-- The generic element Ω satisfies the predicate.
--
C[Ω] : C (ι ⇾ ι) ⟦ Ω ⟧
C[Ω] {f} cf α = m , prf
 where
  n₀ : ℕ
  n₀ = pr₁ (cf α)
  n₁ : ℕ
  n₁ = succ (f α)
  m : ℕ
  m = max n₀ n₁
  prf : (β : ℕᴺ) → α ≡[ m ] β → α (f α) ≡ β (f β)
  prf β em = trans e₂ e₁
   where
    e₀ : f α ≡ f β
    e₀ = pr₂ (cf α) β (≡[≤] em (max-spec₀ n₀ n₁))
    e₁ : β (f α) ≡ β (f β)
    e₁ = ap β e₀
    e₂ : α (f α) ≡ β (f α)
    e₂ = ≡[]-< em (max-spec₁ n₀ n₁)

\end{code}

■ Theorem: All T-definable functions ℕᴺ → ℕ are continuous.

\begin{code}

Theorem[TCont] : (f : ℕᴺ → ℕ) → T-definable f → continuous f
Theorem[TCont] f (t , refl) = contᶠ
 where
  claim₀ : (α : ℕᴺ) → ⟦ t ᵇ · Ω ⟧ α ≡ ⟦ t ⟧ α
  claim₀ = Theorem[R] t
  claim₁ : continuous (⟦ t ᵇ · Ω ⟧)
  claim₁ = Lemma[C] t ⋆ C[Ω]
  contᶠ : continuous f
  contᶠ = continuity-extensional claim₀ claim₁

\end{code}


================================
=                              =
=  Experiments of computation  =
=                              =
================================


Because MLTT/Agda proofs are programs, we can run the main theorem to
compute moduli of continuity of T-definable functions.  We develop
some experiments to illustrate this.


■ (External) modulus-of-continuity functional M

\begin{code}

M : T ε ((ι ⇾ ι) ⇾ ι) → ℕᴺ → ℕ
M t α = pr₁ (Theorem[TCont] ⟦ t ⟧ (t , refl) α)

M-spec : (t : T ε ((ι ⇾ ι) ⇾ ι))
       → (α β : ℕᴺ) → α ≡[ M t α ] β → ⟦ t ⟧ α ≡ ⟦ t ⟧ β
M-spec t α = pr₂ (Theorem[TCont] ⟦ t ⟧ (t , refl) α)

\end{code}

■ Examples of closed T terms

t₀ is a constant function

\begin{code}

t₀ : T ε ((ι ⇾ ι) ⇾ ι)
t₀ = Lam (Num 4)

t₀-interpretation : ⟦ t₀ ⟧ ≡ λ α → 4
t₀-interpretation = refl

result₀ :  M t₀ 0ʷ ≡ 0
        ×  M t₀ δ ≡ 0
        ×  M t₀ succ ≡ 0
        ×  M t₀ (12 ✶ 67 ✶ 8 ✶ 99 ✶ 3 ✶ 0ʷ) ≡ 0
result₀ = refl , refl , refl , refl

\end{code}

t₁ is a non-trivial constant function: it applies the identity
function α₁₇ (the 18th bit of α) times on value 4.

\begin{code}

t₁ : T ε ((ι ⇾ ι) ⇾ ι)
t₁ = Lam (Rec · Num 4 · Lam (Lam ν₀) · (ν₀ · Num 17))

t₁-interpretation : ⟦ t₁ ⟧ ≡ λ α → rec 4 (λ _ k → k) (α 17)
t₁-interpretation = refl

result₁ :  M t₁ 0ʷ ≡ 18
        ×  M t₁ δ ≡ 18
        ×  M t₁ succ ≡ 18
        ×  M t₁ (12 ✶ 67 ✶ 8 ✶ 99 ✶ 3 ✶ 0ʷ) ≡ 18
result₁ = refl , refl , refl , refl

\end{code}

t₂ is a simple function returning the 18th bit of the input.

\begin{code}

t₂ : T ε ((ι ⇾ ι) ⇾ ι)
t₂ = Lam (ν₀ · Num 17)

t₂-interpretation : ⟦ t₂ ⟧ ≡ λ α → α 17
t₂-interpretation = refl

result₂ :  M t₂ 0ʷ ≡ 18
        ×  M t₂ δ ≡ 18
        ×  M t₂ succ ≡ 18
        ×  M t₂ (12 ✶ 67 ✶ 8 ✶ 99 ✶ 3 ✶ 0ʷ) ≡ 18
result₂ = refl , refl , refl , refl

\end{code}

t₃ is taken from [OS18]:  λα.α(α(…(α0)…))  with α0 applications of α.

\begin{code}

t₃ : T ε ((ι ⇾ ι) ⇾ ι)
t₃ = Lam (Rec · Num 0 · Lam ν₁ · (ν₀ · Num 0))

t₃-interpretation : ⟦ t₃ ⟧ ≡ λ α → rec 0 (λ _ → α) (α 0)
t₃-interpretation = refl

result₃ :  M t₃ 0ʷ ≡ 1
        ×  M t₃ δ ≡ 1
        ×  M t₃ succ ≡ 1
        ×  M t₃ (12 ✶ 67 ✶ 8 ✶ 99 ✶ 3 ✶ 0ʷ) ≡ 13
result₃ = refl , refl , refl , refl

\end{code}

t₄ is taken from [Esc13] in which is named t₃.

\begin{code}

t₄ : T ε ((ι ⇾ ι) ⇾ ι)
t₄ = Lam (Rec · (ν₀ · Num 1) · (Lam ν₁) · (Plus (ν₀ · Num 2) (ν₀ · Num 3)))

t₄-interpretation : ⟦ t₄ ⟧ ≡ λ α → rec (α 1) (λ _ → α) (α 2 + α 3)
t₄-interpretation = refl

result₄ :  M t₄ 0ʷ ≡ 4
        ×  M t₄ δ ≡ 4
        ×  M t₄ succ ≡ 9
        ×  M t₄ (12 ✶ 67 ✶ 8 ✶ 99 ✶ 3 ✶ 0ʷ) ≡ 68
result₄ = refl , refl , refl , refl

\end{code}

t₅ is also taken from [Esc13]. The evaluations of this complicated
example are instantaneous.

\begin{code}

t₅ : T ε ((ι ⇾ ι) ⇾ ι)
t₅ = Lam (Rec · (ν₀ · (Rec · (ν₀ · (Rec · (ν₀ · Num 17) · Lam ν₁ · (ν₀ · Num 17)))
                           · Lam ν₁
                           · (Rec · (Plus (ν₀ · (ν₀ · Num 2)) (ν₀ · Num 3))
                                  · Lam ν₁
                                  · (Rec · (ν₀ · Num 1) · Lam ν₁ · (Plus (ν₀ · Num 2) (ν₀ · Num 3))))))
              · (Lam ν₁)
              · (ν₀ · Num 2))

t₅-interpretation : ⟦ t₅ ⟧ ≡ λ α → rec (α (rec (α (rec (α 17) (λ _ → α) (α 17)))
                                               (λ _ → α)
                                               (rec (α (α 2) + α 3)
                                                    (λ _ → α)
                                                    (rec (α 1) (λ _ → α) (α 2 + α 3)))))
                                       (λ _ → α)
                                       (α 2)
t₅-interpretation = refl

result₅ :  M t₅ 0ʷ ≡ 18
        ×  M t₅ δ ≡ 18
        ×  M t₅ succ ≡ 58
        ×  M t₅ (12 ✶ 67 ✶ 8 ✶ 99 ✶ 3 ✶ 0ʷ) ≡ 68
result₅ = refl , refl , refl , refl

\end{code}
