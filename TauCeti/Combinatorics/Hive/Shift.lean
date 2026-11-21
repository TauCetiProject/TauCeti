/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.Fibre
import Mathlib.Tactic.FinCases

/-!
# Determinant-shift equivalences on fixed-boundary integer hives

Adding the slack-free normalized affine hive `Hive.affine n a (a + b)` translates a clockwise
product boundary `(lam, μ, γ*)` to `(lam.shift a, μ.shift b, (γ.shift (a + b))*)`, giving an
explicit equivalence of fixed-boundary integer hive fibres
(`TauCeti.Hive.fixedIntegerHiveShiftEquiv`) and invariance of `hiveCount` under simultaneous
determinant shifts (`TauCeti.Hive.hiveCount_productBoundary_shift`).

## Main definitions

* `TauCeti.Hive.fixedIntegerHiveShiftEquiv`: equivalence of fixed-boundary integer hive fibres
  under simultaneous determinant shifts `(lam, μ, γ) ↦ (lam.shift a, μ.shift b, γ.shift (a + b))`.

## Main results

* `TauCeti.Hive.productBoundary_shift`, `TauCeti.Hive.hiveCount_productBoundary_shift`,
  `TauCeti.Hive.hiveCount_productBoundary_shift_left`,
  `TauCeti.Hive.hiveCount_productBoundary_shift_right`: behaviour of `productBoundary` and
  `hiveCount` under determinant shifts.

## References

* A. Knutson and T. Tao, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor products I:
  proof of the saturation conjecture*, J. Amer. Math. Soc. **12** (1999), 1055–1090, Appendix 2.
-/

public section

namespace TauCeti.Hive

section Shift

variable {n : ℕ}

/-- Shifting `λ` by `a`, `μ` by `b`, and `γ` by `a + b` adds the boundary of
`affine n a (a + b)` to `productBoundary lam μ γ`. -/
theorem productBoundary_shift (lam μ γ : DominantWeight n) (a b : ℤ) :
    productBoundary (lam.shift a) (μ.shift b) (γ.shift (a + b)) =
      productBoundary lam μ γ + (affine n a (a + b)).boundary := by
  ext s i
  fin_cases s <;> simp [productBoundary_zero, productBoundary_one, productBoundary_two]

/-- Adding `affine n a (a + b)` to an integer hive with boundary `(lam, μ, γ*)` shifts its boundary
to `(lam.shift a, μ.shift b, (γ.shift (a + b))*)`. -/
theorem boundary_add_affine_eq_productBoundary_shift {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ) (a b : ℤ) :
    (h + affine n a (a + b)).boundary =
      productBoundary (lam.shift a) (μ.shift b) (γ.shift (a + b)) := by
  rw [boundary_add, hb, productBoundary_shift]

/-- Equivalence of fixed-boundary integer hive fibres induced by simultaneous determinant shifts
`lam ↦ lam.shift a`, `μ ↦ μ.shift b`, `γ ↦ γ.shift (a + b)`. -/
def fixedIntegerHiveShiftEquiv (lam μ γ : DominantWeight n) (a b : ℤ) :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      FixedIntegerHive (productBoundary (lam.shift a) (μ.shift b) (γ.shift (a + b))) where
  toFun h :=
    ⟨h.val + affine n a (a + b), boundary_add_affine_eq_productBoundary_shift h.property a b⟩
  invFun h := ⟨h.val + affine n (-a) (-(a + b)), by
    have hb := boundary_add_affine_eq_productBoundary_shift h.property (-a) (-b)
    have hneg : -a + -b = -(a + b) := by omega
    have hab : (a + b) + (-a + -b) = 0 := by omega
    simpa only [hneg, DominantWeight.shift_shift, hab, add_neg_cancel,
      DominantWeight.shift_zero] using hb⟩
  left_inv h := Subtype.ext <| by
    dsimp only
    rw [add_assoc, affine_add_affine, add_neg_cancel, add_neg_cancel, affine_zero, add_zero]
  right_inv h := Subtype.ext <| by
    dsimp only
    rw [add_assoc, affine_add_affine, neg_add_cancel, neg_add_cancel, affine_zero, add_zero]

/-- Shifting a fixed-boundary hive adds `affine n a (a + b)` to the underlying hive. -/
@[simp] theorem coe_fixedIntegerHiveShiftEquiv_apply (lam μ γ : DominantWeight n) (a b : ℤ)
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    ((fixedIntegerHiveShiftEquiv lam μ γ a b h).val : IntegerHive n) = h.val + affine n a (a + b) :=
  (rfl)

/-- Unshifting a fixed-boundary hive adds `affine n (-a) (-(a + b))` to the underlying hive. -/
@[simp] theorem coe_fixedIntegerHiveShiftEquiv_symm_apply (lam μ γ : DominantWeight n) (a b : ℤ)
    (h : FixedIntegerHive (productBoundary (lam.shift a) (μ.shift b) (γ.shift (a + b)))) :
    (((fixedIntegerHiveShiftEquiv lam μ γ a b).symm h).val : IntegerHive n) =
      h.val + affine n (-a) (-(a + b)) :=
  (rfl)

/-- Simultaneous determinant shifts of the input weights shift the output weight by their sum
without changing `hiveCount`. -/
theorem hiveCount_productBoundary_shift (lam μ γ : DominantWeight n) (a b : ℤ) :
    hiveCount (productBoundary (lam.shift a) (μ.shift b) (γ.shift (a + b))) =
      hiveCount (productBoundary lam μ γ) := by
  rw [← card_fixedIntegerHive, ← card_fixedIntegerHive]
  exact (Fintype.card_congr (fixedIntegerHiveShiftEquiv lam μ γ a b)).symm

/-- Shifting the first input weight and the output weight by the same integer preserves
`hiveCount`. -/
@[simp] theorem hiveCount_productBoundary_shift_left (lam μ γ : DominantWeight n) (a : ℤ) :
    hiveCount (productBoundary (lam.shift a) μ (γ.shift a)) =
      hiveCount (productBoundary lam μ γ) := by
  simpa using hiveCount_productBoundary_shift lam μ γ a 0

/-- Shifting the second input weight and the output weight by the same integer preserves
`hiveCount`. -/
@[simp] theorem hiveCount_productBoundary_shift_right (lam μ γ : DominantWeight n) (b : ℤ) :
    hiveCount (productBoundary lam (μ.shift b) (γ.shift b)) =
      hiveCount (productBoundary lam μ γ) := by
  simpa using hiveCount_productBoundary_shift lam μ γ 0 b

end Shift

end TauCeti.Hive
