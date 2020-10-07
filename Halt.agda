module Halt where

open import Data.List 
  using (List; []; _∷_)
open import Relation.Nullary
   using (¬_)
open import Data.Empty 
  using (⊥; ⊥-elim)
open import Data.Product 
  using (Σ; Σ-syntax)

data Type : Set where
  𝔹  :  Type
  _⇒_ : Type → Type → Type

infix 4 _∈_
data _∈_ {ty : Set} (t : ty) : List ty → Set where
  z : ∀ {ts} → t ∈ (t ∷ ts)
  s : ∀ {r} {ts} → (t ∈ ts) → t ∈ (r ∷ ts)

data _+_ (a : Set) (b : Set) : Set where
  Left  : a → a + b
  Right : b → a + b

Con = List Type

nil : Con
nil = []


infixl 6 _,_
_,_ : Con → Type → Con
_,_ con ty = ty ∷ con

data Expr (Γ : Con) : Type → Set where
  var  : ∀ {a : Type} → a ∈ Γ → Expr Γ a
  app  : ∀ {a b} → Expr Γ (a ⇒ b) → Expr Γ a → Expr Γ b
  lam  : ∀ {a b} → Expr (a ∷ Γ) b → Expr Γ (a ⇒ b)
  tt   : Expr Γ 𝔹
  ff   : Expr Γ 𝔹
  bool : ∀ {a} → Expr Γ 𝔹 → Expr Γ a → Expr Γ a → Expr Γ a
  fix  : ∀ {a} → Expr (Γ , a) a → Expr Γ a


ext : ∀ {Γ Δ : Con}
  → (∀ {A : Type} →       A ∈ Γ →     A ∈ Δ)
    ---------------------------------
  → (∀ {A B : Type} → A ∈ (Γ , B) → A ∈ (Δ , B))
ext ρ z = z
ext ρ (s x) = s (ρ x)


rename : ∀ {Γ Δ}
  → (∀ {A} → A ∈ Γ → A ∈ Δ)
    -----------------------
  → (∀ {A} → Expr Γ A → Expr Δ A)
rename ρ (var x) = var (ρ x)
rename ρ (app rator rand) = app (rename ρ rator) (rename ρ rand)
rename ρ (lam body) = lam (rename (ext ρ) body)
rename ρ tt = tt
rename ρ ff = ff
rename ρ (bool b th el) = bool (rename ρ b) (rename ρ th) (rename ρ el)
rename ρ (fix body) = fix (rename (ext ρ) body)

exts : ∀ {Γ Δ}
  → (∀ {A} →       A ∈ Γ →     Expr Δ A)
    ---------------------------------
  → (∀ {A B} → A ∈ (Γ , B) → Expr (Δ , B) A)
exts ρ z = var z
exts ρ (s x) = rename s (ρ x)

subst : ∀ {Γ Δ}
  → (∀ {A} → A ∈ Γ → Expr Δ A)
    -----------------------
  → (∀ {A} → Expr Γ A → Expr Δ A)
subst ρ (var x) = ρ x
subst ρ (app rator rand) = app (subst ρ rator) (subst ρ rand)
subst ρ (lam body) = lam (subst (exts ρ) body)
subst ρ tt = tt
subst ρ ff = ff
subst ρ (bool b th el) = bool (subst ρ b) (subst ρ th) (subst ρ el)
subst ρ (fix body) = fix (subst (exts ρ) body)



_[_] : ∀ {Γ A B}
        → Expr (Γ , B) A
        → Expr Γ B
        → Expr Γ A
_[_] {Γ} {A} {B} body term = subst {Γ , B} {Γ} sub body
  where
  sub : ∀ {A} → A ∈ (Γ , B) → Expr Γ A
  sub z      = term
  sub (s pf) = var pf

data Value : ∀ {Γ} {A} → Expr Γ A → Set where

  V-↦ : ∀ {Γ } {A B} {body : Expr (Γ , B) A }
    → Value (lam body)

  V-tt : ∀ {Γ} → Value {Γ} {𝔹} tt
  V-ff : ∀ {Γ} → Value {Γ} {𝔹} ff

data _↓_ : ∀ {Γ} {A} → Expr Γ A -> Expr Γ A -> Set where

  l-↓ : ∀ {Γ A B} {L L' : Expr Γ (A ⇒ B)} {M : Expr Γ A}
    -> L ↓ L'
    -> app L M ↓ app L' M

  r-↓ : ∀ {Γ A B} {V : Expr Γ (A ⇒ B)} { M M' : Expr Γ A}
    -> (Value V)
    -> M ↓ M'
    -> app V M ↓ app V M'


  β-↓ : ∀ {Γ} {A B} {N : Expr (Γ , A) B} {V : Expr Γ A}
    -> (app (lam N) V) ↓ (N [ V ])

  if-↓ : ∀ {Γ} {A} {b b' : Expr Γ 𝔹} {t e : Expr Γ A}
    -> b ↓ b'
    -> (bool b t e) ↓ (bool b' t e)

  if-tt-↓ : ∀ {Γ} {A} {t e : Expr Γ A}
    -> (bool tt t e) ↓ t

  if-ff-↓ : ∀ {Γ} {A} {t e : Expr Γ A}
    -> (bool ff t e) ↓ e


  fix-↓ : ∀ {Γ A} {expr : Expr (Γ , A) A}
    -> fix expr ↓ (expr [ fix expr ])


data _⇓_ : ∀ {Γ A} → Expr Γ A → Expr Γ A → Set where

  _∎ : ∀ {Γ A} (M : Expr Γ A)
      ------
    → M ⇓ M

  _→⟨_⟩_ : ∀ {Γ A} (L : Expr Γ A) {M N : Expr Γ A}
    → L ↓ M
    → M ⇓ N
    → L ⇓ N


data Dec A : Set where
  yes : A   → Dec A
  no  : ¬ A → Dec A


data Halt {Γ a} (e :  Expr Γ a) : Set where
  halts : ∀ {v : Expr Γ a} → (Value v) → (e ⇓ v) → Halt e

postulate
  halt     : ∀ {Γ} {a} → Expr Γ (a ⇒ 𝔹)
  halt-ret : ∀ {Γ} {a} (e : Expr Γ a) → ((app halt e) ⇓ tt) + (app halt e ⇓ ff)
  halt-tt  : ∀ {Γ a} (e : Expr Γ a)   → ((app halt e) ⇓ tt) →    Halt e
  halt-ff  : ∀ {Γ a} (e : Expr Γ a)   → ((app halt e) ⇓ ff) → ¬ (Halt e)

bot : ∀ {a Γ} → Expr Γ a
bot = fix (var z)

bot-non-term : ∀ {Γ} →  ¬ (Halt {Γ} {𝔹} bot)
bot-non-term (halts v (.(fix (var z)) →⟨ fix-↓ ⟩ st)) = bot-non-term (halts v st)


problem : ∀ {Γ} → Expr (Γ , 𝔹) 𝔹
problem = (bool (app halt (var z)) bot tt)

fix-problem : ∀ {Γ} → Expr Γ 𝔹
fix-problem = fix problem

bool-stepper : ∀ {Γ} {th el} (b : Expr Γ 𝔹) → b ⇓ tt → (bool b th el) ⇓ th
bool-stepper {_} {th} {el} .tt (.tt ∎) = bool tt th el →⟨ if-tt-↓ ⟩ (th ∎)
bool-stepper {_} {th} {el} b (_→⟨_⟩_ .b {M} x st) 
  = _→⟨_⟩_ (bool b th el) (if-↓ x) (bool-stepper M st)

contradiction : ⊥
contradiction with halt-ret fix-problem 
contradiction | Left ⇓tt with halt-tt fix-problem ⇓tt 
contradiction | Left _ | halts val st = {!!}

contradiction | Right ⇓ff with halt-ff fix-problem ⇓ff 
... | h  = {!!}

