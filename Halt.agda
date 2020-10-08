module Halt where

open import Data.List 
  using (List; []; _∷_)
open import Relation.Nullary
   using (¬_)
open import Data.Empty 
  using (⊥; ⊥-elim)
open import Data.Product 
  using (Σ; Σ-syntax; _×_) renaming (_,_ to sg)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; _≢_; cong; trans; sym)

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
exts ρ z     = var z
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



sub : ∀ {Γ} {A B} → Expr Γ B → A ∈ (Γ , B) → Expr Γ A
sub term z      = term
sub _ (s pf) = var pf

_[_] : ∀ {Γ A B}
        → Expr (Γ , B) A
        → Expr Γ B
        → Expr Γ A
_[_] {Γ} {A} {B} body term = subst {Γ , B} {Γ} (sub term) body


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

⇓-∘ : ∀ {Γ} {a} {L M N : Expr Γ a} → L ⇓ M → M ⇓ N → L ⇓ N
⇓-∘ (_ ∎) p2 = p2
⇓-∘ (_ →⟨ x ⟩ p1) p2 = _ →⟨ x ⟩ ⇓-∘ p1 p2


data Halt {Γ a} (e :  Expr Γ a) : Set where
  halts : ∀ {v : Expr Γ a} → (Value v) → (e ⇓ v) → Halt e

-- to do
--   - postulate confluence
--   - show that if e' halts and e ⇓ e' then e halts too.
--   - 
postulate
  confluence : ∀ {Γ} {a} →
    {e e1 e2 : Expr Γ a} → e ⇓ e1 → e ⇓ e2 → Σ[ e3 ∈ Expr Γ a ] ((e1 ⇓ e3) × (e2 ⇓ e3))

⇓-val : ∀ {Γ a} {e e' : Expr Γ a} → Value e → e ⇓ e' → e' ≡ e
⇓-val val   (_ ∎) = refl
⇓-val V-↦  (_ →⟨ () ⟩ st)
⇓-val V-tt (_ →⟨ () ⟩ st)
⇓-val V-ff (_ →⟨ () ⟩ st)

⇓-val-uniq : ∀ {Γ a} {e e' v : Expr Γ a} → Value v → e ⇓ v → e ⇓ e' → e' ⇓ v
⇓-val-uniq pf e⇓v e⇓e' with confluence e⇓v e⇓e'
... | sg e3 (sg v⇓e3 e'⇓e3) with ⇓-val pf v⇓e3 
... | refl = e'⇓e3

halt-ext : ∀ {Γ a} {e1 e2 : Expr Γ a} → e1 ⇓ e2 → Halt e2 → Halt e1
halt-ext e1⇓e2 (halts v steps) = halts v (⇓-∘ e1⇓e2 steps)

halt-⊥ : ∀ {Γ a} {e1 e2 : Expr Γ a} → e1 ⇓ e2 → ¬ (Halt e2) → ¬ (Halt e1)
halt-⊥ e1⇓e2 e2-⊥ (halts v-e1 st) with ⇓-val-uniq v-e1 st e1⇓e2
... | e2⇓v = e2-⊥ (halts v-e1 e2⇓v)


postulate
  halt     : ∀ {Γ} {a} → Expr Γ (a ⇒ 𝔹)
  halt-sub : 
    ∀ {Γ Δ} {a} →
    (ρ : ∀ {A} → A ∈ Γ → Expr Δ A)
    → subst {Γ} {Δ} ρ (halt {Γ} {a}) ≡ (halt {Δ})
  halt-ret : ∀ {Γ} {a} (e : Expr Γ a) → ((app halt e) ⇓ tt) + (app halt e ⇓ ff)
  halt-tt  : ∀ {Γ a} (e : Expr Γ a)   → ((app halt e) ⇓ tt) →    Halt e
  halt-ff  : ∀ {Γ a} (e : Expr Γ a)   → ((app halt e) ⇓ ff) → ¬ (Halt e)

bot : ∀ {a Γ} → Expr Γ a
bot = fix (var z)

bot-non-term : ∀ {Γ} →  ¬ (Halt {Γ} {𝔹} bot)
bot-non-term (halts v (.(fix (var z)) →⟨ fix-↓ ⟩ st)) = bot-non-term (halts v st)

⇓-bot-⊥ : ∀ {Γ} → (e : Expr Γ 𝔹) → e ⇓ bot → ¬ Halt e
⇓-bot-⊥ e st = halt-⊥ st bot-non-term

problem : ∀ {Γ} → Expr (Γ , 𝔹) 𝔹
problem = (bool (app halt (var z)) bot tt)

fix-problem : ∀ {Γ} → Expr Γ 𝔹
fix-problem = fix problem

bool-stepper-tt 
  : ∀ {Γ} {th el} (b : Expr Γ 𝔹) → b ⇓ tt → (bool {Γ} {𝔹} b th el) ⇓ th
bool-stepper-tt {_} {th} {el} .tt (.tt ∎) = bool tt th el →⟨ if-tt-↓ ⟩ (th ∎)
bool-stepper-tt {_} {th} {el} b (_→⟨_⟩_ .b {M} x st) 
  = _→⟨_⟩_ (bool b th el) (if-↓ x) (bool-stepper-tt M st)

bool-stepper-ff : ∀ {Γ} {th el} (b : Expr Γ 𝔹) → b ⇓ ff → (bool {Γ} {𝔹} b th el) ⇓ el
bool-stepper-ff {_} {th} {el} .ff (.ff ∎) = bool ff th el →⟨ if-ff-↓ ⟩ (el ∎)
bool-stepper-ff {_} {th} {el} b (_→⟨_⟩_ .b {M} x st) 
  = _→⟨_⟩_ (bool b th el) (if-↓ x) (bool-stepper-ff M st)

≡-↓ 
  : ∀ {Γ} {e e' e'' : Expr Γ 𝔹} 
  → e ↓ e'
  → e' ≡ e''
  → e ↓ e''
≡-↓ e↓e' refl = e↓e'

fp-step1
   : ∀ {Γ} {e : Expr Γ 𝔹} 
   → (fix-problem {Γ}) ↓ e 
   → e ≡ (bool (app halt (fix-problem)) bot tt)
fp-step1 {Γ} fix-↓ rewrite (halt-sub {Γ , 𝔹} {Γ} {𝔹} (sub {Γ} fix-problem))  = refl

fp-step2
   : ∀ {Γ}
   → (fix-problem {Γ}) ↓ (bool (app halt (fix-problem)) bot tt)
fp-step2 {Γ} = ≡-↓ (fix-↓ {Γ} {𝔹} {problem}) (fp-step1 (fix-↓ {Γ} {𝔹} {problem}))

fp-step3
   : ∀ {Γ}
   → (app (halt {Γ}) fix-problem) ⇓ tt
   → (bool (app (halt {Γ}) fix-problem) bot tt) ⇓ bot
fp-step3 ⇓-tt = bool-stepper-tt _  ⇓-tt

fp-step4
   : ∀ {Γ}
   → (app (halt {Γ}) fix-problem) ⇓ tt
   → (fix-problem {Γ}) ⇓ bot
fp-step4 {Γ} ⇓-tt = fix-problem →⟨ fp-step2 ⟩ fp-step3 ⇓-tt

fp-step5 
   : ∀ {Γ}
   → (app (halt {Γ}) fix-problem) ⇓ ff
   → (bool (app (halt {Γ}) fix-problem) bot tt) ⇓ tt
fp-step5 ⇓-ff = bool-stepper-ff _ ⇓-ff

fp-step6
   : ∀ {Γ}
   → (app (halt {Γ}) fix-problem) ⇓ ff
   → fix-problem ⇓ tt
fp-step6 ⇓-ff = fix-problem →⟨ fp-step2 ⟩ fp-step5 ⇓-ff


fix-problem-tt : ∀ {Γ} → (app (halt {Γ}) fix-problem) ⇓ tt → Halt {Γ} fix-problem → ⊥
fix-problem-tt ⇓-tt h = ⇓-bot-⊥ _ (fp-step4 ⇓-tt) h

fix-problem-ff : ∀ {Γ} → (app (halt {Γ}) fix-problem) ⇓ ff → (¬ Halt {Γ} fix-problem) → ⊥
fix-problem-ff ⇓-ff ¬h = ¬h (halts V-tt (fp-step6 ⇓-ff)) 

contradiction : ⊥
contradiction with halt-ret {nil} fix-problem
contradiction | Left ⇓tt  = fix-problem-tt ⇓tt (halt-tt fix-problem ⇓tt)
contradiction | Right ⇓ff = fix-problem-ff ⇓ff (halt-ff fix-problem ⇓ff)


