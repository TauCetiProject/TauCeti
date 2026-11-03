/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.HopfAlgebra
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Antipode

/-!
# The order filtration of a Kostant integral form

Intersecting the rational PBW filtration with a Kostant integral form gives an exhaustive
multiplicative filtration by integral submodules. The integral Hopf antipode preserves order;
on order `n` its leading action is multiplication by `(-1)^n`.

This is the inherited order filtration, not the word filtration in the divided-power generators
(which would put every divided power in degree one). No integral PBW basis, freeness of the
filtration quotients, or identification of the associated graded with a divided-power algebra
is asserted here. The families of root and Cartan vectors are arbitrary, so the construction
also retains any central toral directions supplied among the Cartan vectors.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26–27.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]
variable {I J : Type*} (e : I → L) (h : J → L)

attribute [local instance] TauCeti.moduleNNRat

local notation "U" => _root_.UniversalEnvelopingAlgebra ℚ L
local notation "K" => kostantForm e h

/-- The elements of a Kostant integral form of rational PBW order at most `n`. -/
noncomputable def kostantFiltration (n : ℕ) : Submodule ℤ K :=
  ((pbwFiltration ℚ L n).restrictScalars ℤ).comap
    (kostantForm e h).subtype.toIntAlgHom.toLinearMap

/-- An integral element has order at most `n` exactly when its rational image has PBW degree
at most `n`. -/
@[simp]
theorem mem_kostantFiltration {n : ℕ} {a : K} :
    a ∈ kostantFiltration e h n ↔ (a : U) ∈ pbwFiltration ℚ L n :=
  Iff.rfl

/-- The preceding order step, with zero in degree zero. -/
noncomputable def kostantFiltrationPrevious : ℕ → Submodule ℤ K
  | 0 => ⊥
  | n + 1 => kostantFiltration e h n

/-- There is no order step strictly below zero. -/
@[simp]
theorem kostantFiltrationPrevious_zero : kostantFiltrationPrevious e h 0 = ⊥ :=
  (rfl)

/-- The step strictly below successor order is the previous order step. -/
@[simp]
theorem kostantFiltrationPrevious_succ (n : ℕ) :
    kostantFiltrationPrevious e h (n + 1) = kostantFiltration e h n :=
  (rfl)

/-- The integral order filtration is increasing. -/
theorem kostantFiltration_mono : Monotone (kostantFiltration e h) :=
  fun _ _ hij _ ha ↦ (mem_kostantFiltration e h).mpr
    (pbwFiltration_mono ℚ L hij ((mem_kostantFiltration e h).mp ha))

/-- Multiplication adds integral order bounds. -/
theorem mul_mem_kostantFiltration {i j : ℕ} {a b : K}
    (ha : a ∈ kostantFiltration e h i) (hb : b ∈ kostantFiltration e h j) :
    a * b ∈ kostantFiltration e h (i + j) := by
  rw [mem_kostantFiltration] at ha hb ⊢
  exact mul_mem_pbwFiltration ℚ L ha hb

/-- The inherited order filtration is a ring filtration with its preceding-step family. -/
instance : IsRingFiltration (kostantFiltration e h) (kostantFiltrationPrevious e h) where
  mono := kostantFiltration_mono e h
  is_le := by
    intro i j hij
    cases j with
    | zero => omega
    | succ j => exact kostantFiltration_mono e h (Nat.le_of_lt_succ hij)
  is_sup := by
    intro B j hB
    cases j with
    | zero => exact bot_le
    | succ j => exact hB j (Nat.lt_succ_self j)
  one_mem := (mem_kostantFiltration e h).mpr (one_mem_pbwFiltration ℚ L 0)
  mul_mem := fun {i j} {a b} ha hb ↦ mul_mem_kostantFiltration e h ha hb

/-- Every integral element has finite order. -/
theorem exists_mem_kostantFiltration (a : K) : ∃ n, a ∈ kostantFiltration e h n := by
  simpa only [mem_kostantFiltration] using exists_mem_pbwFiltration ℚ L (a : U)

/-- The order filtration exhausts the Kostant integral form. -/
@[simp]
theorem iSup_kostantFiltration_eq_top : ⨆ n, kostantFiltration e h n = ⊤ := by
  apply top_unique
  intro a _
  obtain ⟨n, hn⟩ := exists_mem_kostantFiltration e h a
  exact Submodule.mem_iSup_of_mem n hn

/-- The integral Hopf antipode preserves each order step, in both directions.
Use this equivalence explicitly: the membership simp rule instead reduces to rational PBW order. -/
theorem antipode_mem_kostantFiltration_iff (a : K) (n : ℕ) :
    HopfAlgebra.antipode ℤ a ∈ kostantFiltration e h n ↔ a ∈ kostantFiltration e h n := by
  rw [mem_kostantFiltration, mem_kostantFiltration, coe_antipode_kostantForm,
    antipode_mem_pbwFiltration_iff]

/-- On integral order `n + 1`, the antipode has leading sign `(-1)^(n + 1)`; the difference
has order at most `n`. In particular this is an integral lower-order error, not just a
rational congruence. -/
theorem antipode_sub_neg_one_pow_smul_mem_kostantFiltration {n : ℕ} {a : K}
    (ha : a ∈ kostantFiltration e h (n + 1)) :
    HopfAlgebra.antipode ℤ a - (-1 : ℤ) ^ (n + 1) • a ∈ kostantFiltration e h n := by
  have hs := antipode_sub_neg_one_pow_smul_mem_pbwFiltrationPrevious ℚ L
    ((mem_kostantFiltration e h).mp ha)
  rw [pbwFiltrationPrevious_succ] at hs
  rw [mem_kostantFiltration, AddSubgroupClass.coe_sub, coe_antipode_kostantForm,
    AddSubgroupClass.coe_zsmul, ← Int.cast_smul_eq_zsmul ℚ]
  simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one] using hs

end TauCeti.UniversalEnvelopingAlgebra
