/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.MonomialOrder.DegLex
public import TauCeti.Data.Finsupp.Colex

/-!
# Graded reverse lexicographic monomial ordering

This file constructs the graded reverse lexicographic order (grevlex) on `σ →₀ ℕ` as a
`MonomialOrder`, alongside Mathlib's `MonomialOrder.lex` and `MonomialOrder.degLex`.

Monomials are first compared by total degree. Two monomials of the same degree are compared
at the *largest* index of `σ` where their exponents differ: the larger monomial is the one with
the *smaller* exponent there. With the antitone variable convention of `MonomialOrder.degLex`,
the largest index is the smallest variable, so this is the usual textbook rule: for variables
`X 0 > X 1 > ⋯ > X n`, the larger of two monomials of equal degree is the one whose rightmost
nonzero entry of the exponent difference is negative. On `Fin 3`, for instance,
`X 0 * X 2 < X 1 ^ 2` for grevlex, whereas `X 1 ^ 2 < X 0 * X 2` for deglex.

Equal-degree comparison is the reverse of the colexicographic order `Colex (σ →₀ ℕ)`.
Well-foundedness therefore rests on `Finsupp.wellFoundedOn_setOf_degree_le_toColex_gt`: when
`σ` has no infinite ascending chains, there is no infinite strictly increasing colexicographic
chain of exponents of bounded degree. The bound on the degree is necessary, since
`X 0, X 0 ^ 2, X 0 ^ 3, …` is colexicographically increasing.

## Main declarations

* `TauCeti.DegRevLex`: a type synonym carrying the graded reverse lexicographic order.
* `TauCeti.DegRevLex.lt_iff`, `TauCeti.DegRevLex.le_iff`: the order in terms of the degree and
  `Colex (σ →₀ ℕ)`.
* `TauCeti.DegRevLex.lt_iff_exists`: the textbook description by the largest differing index.
* `TauCeti.MonomialOrder.degRevLex`: the graded reverse lexicographic `MonomialOrder σ`, for
  `σ` linearly ordered with `WellFoundedGT σ` (automatic when `σ` is finite).
* `TauCeti.MonomialOrder.degRevLex_single_le_iff`: variables are ordered antitonely,
  `X i ≤ X j ↔ j ≤ i`, as for `MonomialOrder.degLex`.

## References

* [Cox, Little and O'Shea, *Ideals, varieties, and algorithms*][coxlittleoshea1997], Chapter 2,
  §2, Definition 6 (graded reverse lex order).
* [Becker and Weispfenning, *Gröbner bases*][Becker-Weispfenning1993]

The type-synonym interface follows Mathlib's `DegLex` (`Mathlib/Data/Finsupp/MonomialOrder/DegLex`,
by Antoine Chambert-Loir).
-/

@[expose] public section

namespace TauCeti

/-- A type synonym to equip a type with its graded reverse lexicographic order. -/
def DegRevLex (α : Type*) := α

variable {α : Type*}

/-- `toDegRevLex` is the identity function to the `DegRevLex` of a type. -/
@[match_pattern] def toDegRevLex : α ≃ DegRevLex α := Equiv.refl _

theorem toDegRevLex_injective : Function.Injective (toDegRevLex (α := α)) := fun _ _ ↦ _root_.id

theorem toDegRevLex_inj {a b : α} : toDegRevLex a = toDegRevLex b ↔ a = b := Iff.rfl

/-- `ofDegRevLex` is the identity function from the `DegRevLex` of a type. -/
@[match_pattern] def ofDegRevLex : DegRevLex α ≃ α := Equiv.refl _

theorem ofDegRevLex_injective : Function.Injective (ofDegRevLex (α := α)) := fun _ _ ↦ _root_.id

theorem ofDegRevLex_inj {a b : DegRevLex α} : ofDegRevLex a = ofDegRevLex b ↔ a = b := Iff.rfl

@[simp] theorem ofDegRevLex_symm_eq : (@ofDegRevLex α).symm = toDegRevLex := rfl

@[simp] theorem toDegRevLex_symm_eq : (@toDegRevLex α).symm = ofDegRevLex := rfl

@[simp] theorem ofDegRevLex_toDegRevLex (a : α) : ofDegRevLex (toDegRevLex a) = a := rfl

@[simp] theorem toDegRevLex_ofDegRevLex (a : DegRevLex α) : toDegRevLex (ofDegRevLex a) = a := rfl

/-- A recursor for `DegRevLex`. Use as `induction x`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
protected def DegRevLex.rec {β : DegRevLex α → Sort*} (h : ∀ a, β (toDegRevLex a)) :
    ∀ a, β a := fun a ↦ h (ofDegRevLex a)

@[simp] lemma DegRevLex.forall_iff {p : DegRevLex α → Prop} :
    (∀ a, p a) ↔ ∀ a, p (toDegRevLex a) := Iff.rfl

@[simp] lemma DegRevLex.exists_iff {p : DegRevLex α → Prop} :
    (∃ a, p a) ↔ ∃ a, p (toDegRevLex a) := Iff.rfl

noncomputable instance [AddCommMonoid α] : AddCommMonoid (DegRevLex α) :=
  ofDegRevLex.addCommMonoid

theorem toDegRevLex_add [AddCommMonoid α] (a b : α) :
    toDegRevLex (a + b) = toDegRevLex a + toDegRevLex b := rfl

theorem ofDegRevLex_add [AddCommMonoid α] (a b : DegRevLex α) :
    ofDegRevLex (a + b) = ofDegRevLex a + ofDegRevLex b := rfl

end TauCeti

end

public section

namespace TauCeti

namespace DegRevLex

open Finsupp

variable [LinearOrder α]

/-- The graded reverse lexicographic order on `α →₀ ℕ`: compare total degrees, then compare
monomials of equal degree by the reverse of the colexicographic order. -/
noncomputable instance : LinearOrder (DegRevLex (α →₀ ℕ)) :=
  LinearOrder.lift'
    (fun f ↦ toLex ((ofDegRevLex f).degree, OrderDual.toDual (toColex (ofDegRevLex f))))
    fun f g h ↦ by simpa using congr_arg (fun p ↦ ofColex (OrderDual.ofDual (ofLex p).2)) h

/-- The graded reverse lexicographic order compares degrees first, then reverses the
colexicographic order. -/
theorem lt_iff {a b : DegRevLex (α →₀ ℕ)} :
    a < b ↔ (ofDegRevLex a).degree < (ofDegRevLex b).degree ∨
      (ofDegRevLex a).degree = (ofDegRevLex b).degree ∧
        toColex (ofDegRevLex b) < toColex (ofDegRevLex a) :=
  Prod.Lex.toLex_lt_toLex

/-- The non-strict form of `TauCeti.DegRevLex.lt_iff`. -/
theorem le_iff {a b : DegRevLex (α →₀ ℕ)} :
    a ≤ b ↔ (ofDegRevLex a).degree < (ofDegRevLex b).degree ∨
      (ofDegRevLex a).degree = (ofDegRevLex b).degree ∧
        toColex (ofDegRevLex b) ≤ toColex (ofDegRevLex a) :=
  Prod.Lex.toLex_le_toLex

/-- The textbook description of the graded reverse lexicographic order: among monomials of equal
degree, `a < b` when `a` has the larger exponent at the largest index where they differ. -/
theorem lt_iff_exists {a b : DegRevLex (α →₀ ℕ)} :
    a < b ↔ (ofDegRevLex a).degree < (ofDegRevLex b).degree ∨
      (ofDegRevLex a).degree = (ofDegRevLex b).degree ∧
        ∃ i, (∀ j, i < j → ofDegRevLex a j = ofDegRevLex b j) ∧
          ofDegRevLex b i < ofDegRevLex a i := by
  rw [lt_iff, Colex.lt_iff]
  refine or_congr_right (and_congr_right fun _ ↦ exists_congr fun i ↦ and_congr_left fun _ ↦ ?_)
  exact forall_congr' fun j ↦ imp_congr_right fun _ ↦ eq_comm

instance : IsOrderedCancelAddMonoid (DegRevLex (α →₀ ℕ)) where
  le_of_add_le_add_left a b c h := by
    rw [le_iff] at h ⊢
    simpa only [ofDegRevLex_add, map_add, add_lt_add_iff_left, add_right_inj, toColex_add,
      add_le_add_iff_left] using h
  add_le_add_left a b h c := by
    rw [le_iff] at h ⊢
    simpa only [ofDegRevLex_add, map_add, add_lt_add_iff_right, add_left_inj, toColex_add,
      add_le_add_iff_right] using h

theorem single_strictAnti : StrictAnti (fun a : α ↦ toDegRevLex (single a 1)) := fun _ _ h ↦
  lt_iff.2 (Or.inr ⟨by simp, Colex.single_lt_iff.2 h⟩)

theorem single_antitone : Antitone (fun a : α ↦ toDegRevLex (single a 1)) :=
  single_strictAnti.antitone

@[simp]
theorem single_lt_iff {a b : α} :
    toDegRevLex (single b 1) < toDegRevLex (single a 1) ↔ a < b :=
  single_strictAnti.lt_iff_gt

@[simp]
theorem single_le_iff {a b : α} :
    toDegRevLex (single b 1) ≤ toDegRevLex (single a 1) ↔ a ≤ b :=
  single_strictAnti.le_iff_ge

theorem monotone_degree :
    Monotone (fun x : DegRevLex (α →₀ ℕ) ↦ (ofDegRevLex x).degree) := fun _ _ h ↦ by
  rcases le_iff.1 h with h | h
  exacts [h.le, h.1.le]

/-- The graded reverse lexicographic order is well-founded when the indices have no infinite
ascending chains, for instance when there are finitely many of them. -/
instance wellFoundedLT [WellFoundedGT α] : WellFoundedLT (DegRevLex (α →₀ ℕ)) := by
  have hfib (n : ℕ) : ((fun x : DegRevLex (α →₀ ℕ) ↦ (ofDegRevLex x).degree) ⁻¹' {n}).WellFoundedOn
      (Function.onFun (· < ·) fun x ↦ OrderDual.toDual (toColex (ofDegRevLex x))) := by
    refine Set.wellFoundedOn_image.1 (((wellFoundedOn_setOf_degree_le_toColex_gt n).subset ?_))
    rintro _ ⟨x, hx, rfl⟩
    exact le_of_eq hx
  exact (WellFounded.prod_lex_of_wellFoundedOn_fiber wellFounded_lt.onFun hfib).mono
    fun a b (h : a < b) ↦ Prod.lex_def.2 <| by
      simpa only [OrderDual.toDual_lt_toDual] using lt_iff.1 h

end DegRevLex

namespace MonomialOrder

open Finsupp DegRevLex

variable {σ : Type*} [LinearOrder σ] [WellFoundedGT σ]

/-- The graded reverse lexicographic order on `σ →₀ ℕ`, as a `MonomialOrder`. Variables are
ordered antitonely, `X i ≤ X j ↔ j ≤ i`, so on `Fin n` the variable `X 0` is the largest. -/
noncomputable def degRevLex : MonomialOrder σ where
  syn := DegRevLex (σ →₀ ℕ)
  toSyn := { toEquiv := toDegRevLex, map_add' := toDegRevLex_add }
  toSyn_monotone a b h := by
    simp only [AddEquiv.coe_mk, DegRevLex.le_iff, ofDegRevLex_toDegRevLex]
    obtain ⟨c, rfl⟩ := exists_add_of_le h
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    · exact Or.inl (by simpa [map_add, Nat.pos_iff_ne_zero, degree_eq_zero_iff] using hc)

open scoped _root_.MonomialOrder

theorem degRevLex_le_iff {a b : σ →₀ ℕ} :
    a ≼[degRevLex] b ↔ toDegRevLex a ≤ toDegRevLex b :=
  Iff.rfl

theorem degRevLex_lt_iff {a b : σ →₀ ℕ} :
    a ≺[degRevLex] b ↔ toDegRevLex a < toDegRevLex b :=
  Iff.rfl

@[simp]
theorem degRevLex_single_le_iff {a b : σ} :
    single a 1 ≼[degRevLex] single b 1 ↔ b ≤ a := by
  rw [degRevLex_le_iff, DegRevLex.single_le_iff]

@[simp]
theorem degRevLex_single_lt_iff {a b : σ} :
    single a 1 ≺[degRevLex] single b 1 ↔ b < a := by
  rw [degRevLex_lt_iff, DegRevLex.single_lt_iff]

end MonomialOrder

section Examples

open Finsupp _root_.TauCeti.MonomialOrder DegRevLex
open scoped _root_.MonomialOrder

/-- For the graded reverse lexicographic ordering, `X 1 < X 0`. -/
example : single (1 : Fin 2) 1 ≺[degRevLex] single 0 1 := by
  rw [degRevLex_single_lt_iff]
  exact Fin.zero_lt_one

/-- For the graded reverse lexicographic ordering, `X 0 * X 2 < X 1 ^ 2`. -/
example : single (0 : Fin 3) 1 + single 2 1 ≺[degRevLex] single 1 2 := by
  rw [degRevLex_lt_iff, lt_iff_exists]
  refine Or.inr ⟨by simp, 2, fun j hj ↦ ?_, by simp⟩
  exact absurd hj (Fin.not_lt.2 (Fin.le_last j))

/-- For the graded lexicographic ordering the comparison is the opposite: `X 1 ^ 2 < X 0 * X 2`. -/
example : single (1 : Fin 3) 2 ≺[_root_.MonomialOrder.degLex] single 0 1 + single 2 1 := by
  rw [_root_.MonomialOrder.degLex_lt_iff, Finsupp.DegLex.lt_iff]
  refine Or.inr ⟨by simp, ⟨0, fun j hj ↦ absurd hj (Fin.not_lt_zero j), by simp⟩⟩

/-- For the graded reverse lexicographic ordering, `X 0 < X 1 ^ 2`. -/
example : single (0 : Fin 2) 1 ≺[degRevLex] single 1 2 := by
  simp [degRevLex_lt_iff, lt_iff]

end Examples

end TauCeti
