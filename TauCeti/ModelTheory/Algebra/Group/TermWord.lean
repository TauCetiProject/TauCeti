/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Algebra.Group.Basic
public import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Group terms and free-group words

A term in the group language with named coefficients determines a word in the free group on
its variables and coefficient letters. Reading a reduced word from left to right gives a
term. These constructions agree after evaluation in any group, and converting the term of a
word back to a word recovers the original element. This supplies the atomic step for turning
group formulas into systems of equations and inequations.

The correspondence follows Kharlampovich and Myasnikov, *Implicit function theorem over free
groups*, §2.3. We use Mathlib's `FreeGroup.toWord` for the reduced representative.
-/

public section

namespace FirstOrder.Language.Term

open FirstOrder.Language TauCeti.Group

variable {X A : Type*}

/-- The free-group word represented by a term with variables `X` and coefficient letters `A`. -/
def toWord (t : FirstOrder.Language.group[[A]].Term X) : FreeGroup (X ⊕ A) := by
  letI : FirstOrder.Language.group.Structure (FreeGroup (X ⊕ A)) :=
    TauCeti.Group.structureOfGroup _
  letI : (FirstOrder.Language.constantsOn A).Structure (FreeGroup (X ⊕ A)) :=
    FirstOrder.Language.constantsOn.structure (FreeGroup.of ∘ Sum.inr)
  exact FirstOrder.Language.Term.realize (FreeGroup.of ∘ Sum.inl) t

@[simp] theorem toWord_var (x : X) :
    toWord (FirstOrder.Language.Term.var x : FirstOrder.Language.group[[A]].Term X) =
      FreeGroup.of (Sum.inl x) := by simp [toWord]

@[simp] theorem toWord_one :
    toWord (1 : FirstOrder.Language.group[[A]].Term X) = 1 := by
  simp [toWord]

@[simp] theorem toWord_inv (t : FirstOrder.Language.group[[A]].Term X) :
    toWord t⁻¹ = (toWord t)⁻¹ := by
  simp [toWord]

@[simp] theorem toWord_mul (t s : FirstOrder.Language.group[[A]].Term X) :
    toWord (t * s) = toWord t * toWord s := by
  simp [toWord]

/-- The coefficient constant `a` represents the generator indexed by `Sum.inr a`. -/
@[simp] theorem toWord_coeff (a : A) :
    toWord (FirstOrder.Language.Constants.term (Sum.inr a) :
      FirstOrder.Language.group[[A]].Term X) = FreeGroup.of (Sum.inr a) := by
  rfl

/-- Turn a signed letter into a variable or coefficient term, inverting it if necessary. -/
private def ofLetter (l : (X ⊕ A) × Bool) : FirstOrder.Language.group[[A]].Term X :=
  let t := match l.1 with
    | .inl x => FirstOrder.Language.Term.var x
    | .inr a => FirstOrder.Language.Constants.term (Sum.inr a)
  if l.2 then t else t⁻¹

private theorem toWord_ofLetter (l : (X ⊕ A) × Bool) :
    toWord (ofLetter l) = FreeGroup.mk [l] := by
  rcases l with ⟨x, b⟩
  cases x <;> cases b <;> simp [ofLetter, FreeGroup.of, FreeGroup.inv_mk,
    FreeGroup.invRev]

end FirstOrder.Language.Term

namespace FreeGroup

open scoped FirstOrder
open FirstOrder.Language FirstOrder.Language.Term

variable {X A : Type*}

/-- Read the reduced word of a free-group element as a left-associated product of terms. -/
noncomputable def ofWord (w : FreeGroup (X ⊕ A)) :
    FirstOrder.Language.group[[A]].Term X := by
  classical
  exact w.toWord.foldl (fun t l => t * ofLetter l) 1

private theorem toWord_foldl (ls : List ((X ⊕ A) × Bool))
    (t : FirstOrder.Language.group[[A]].Term X) :
    (ls.foldl (fun s l => s * ofLetter l) t).toWord = t.toWord * FreeGroup.mk ls := by
  induction ls generalizing t with
  | nil => simp [FreeGroup.one_eq_mk]
  | cons l ls ih =>
    rw [List.foldl_cons, ih, FirstOrder.Language.Term.toWord_mul,
      FirstOrder.Language.Term.toWord_ofLetter, mul_assoc,
      FreeGroup.mul_mk]
    rfl

/-- Converting a free-group element to a term and back recovers that element. -/
@[simp] theorem toWord_ofWord (w : FreeGroup (X ⊕ A)) :
    (ofWord w).toWord = w := by
  classical
  simpa [ofWord, toWord_foldl, FreeGroup.one_eq_mk] using
    (FreeGroup.mk_toWord (x := w))

end FreeGroup

namespace FirstOrder.Language.Term

variable {X A : Type*}
variable {G : Type*}

/-- Evaluate a group term with variables `v` and named coefficients `c`. -/
def realizeGroup [Group G] (t : FirstOrder.Language.group[[A]].Term X)
    (v : X → G) (c : A → G) : G := by
  letI : FirstOrder.Language.group.Structure G := TauCeti.Group.structureOfGroup G
  letI : (FirstOrder.Language.constantsOn A).Structure G :=
    FirstOrder.Language.constantsOn.structure c
  exact FirstOrder.Language.Term.realize v t

/-- Group-term realization is Mathlib term realization with the canonical group and
coefficient interpretations. -/
theorem realizeGroup_def [Group G] (t : FirstOrder.Language.group[[A]].Term X)
    (v : X → G) (c : A → G) :
    realizeGroup t v c =
      (letI : FirstOrder.Language.group.Structure G := TauCeti.Group.structureOfGroup G
       letI : (FirstOrder.Language.constantsOn A).Structure G :=
         FirstOrder.Language.constantsOn.structure c
       FirstOrder.Language.Term.realize v t) := by
  unfold realizeGroup
  rfl

section Realize

variable [Group G] (v : X → G) (c : A → G)

/-- Realizing a group term agrees with evaluating its word at the variable and coefficient
assignments. -/
theorem realize_eq_lift (t : FirstOrder.Language.group[[A]].Term X) :
    realizeGroup t v c = FreeGroup.lift (Sum.elim v c) (toWord t) := by
  let φ : FreeGroup (X ⊕ A) →* G := FreeGroup.lift (Sum.elim v c)
  have hc : ∀ a : A, φ (FreeGroup.of (Sum.inr a)) = c a := by simp [φ]
  let : FirstOrder.Language.group.Structure (FreeGroup (X ⊕ A)) :=
    TauCeti.Group.structureOfGroup _
  let : (FirstOrder.Language.constantsOn A).Structure (FreeGroup (X ⊕ A)) :=
    FirstOrder.Language.constantsOn.structure (FreeGroup.of ∘ Sum.inr)
  let : FirstOrder.Language.group.Structure G := TauCeti.Group.structureOfGroup G
  let : (FirstOrder.Language.constantsOn A).Structure G :=
    FirstOrder.Language.constantsOn.structure c
  have h := FirstOrder.Language.HomClass.realize_term
    (MonoidHom.coeffGroupLanguageHom φ (FreeGroup.of ∘ Sum.inr) c hc)
    (t := t) (v := FreeGroup.of ∘ Sum.inl)
  have hv : (fun x : X => φ (FreeGroup.of (Sum.inl x))) = v := by
    funext x
    simp [φ]
  simpa only [realizeGroup_def, toWord, Function.comp_def,
    MonoidHom.coeffGroupLanguageHom_apply, hv] using h

/-- Reading a word as a term does not change its value under an assignment. -/
@[simp] theorem realizeGroup_ofWord (w : FreeGroup (X ⊕ A)) :
    realizeGroup w.ofWord v c = FreeGroup.lift (Sum.elim v c) w := by
  rw [realize_eq_lift, FreeGroup.toWord_ofWord]

/-- Equality of two group terms is the corresponding word equation. -/
theorem realizeGroup_equal_iff (t s : FirstOrder.Language.group[[A]].Term X) :
    realizeGroup t v c = realizeGroup s v c ↔
      FreeGroup.lift (Sum.elim v c) (toWord t * (toWord s)⁻¹) = 1 := by
  rw [realize_eq_lift v c t, realize_eq_lift v c s, map_mul, map_inv]
  exact mul_inv_eq_one.symm

end Realize

end FirstOrder.Language.Term
