/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Covolume
public import TauCeti.Algebra.Module.ZLattice.Integral

/-!
# The determinant and the discriminant group of a lattice

Let `L` be a full `ℤ`-lattice in a finite-dimensional real inner product space `E`, with the
volume measure of the inner product. This file defines the determinant and the discriminant
group of `L`, using that the covolume of the dual lattice `L^∨ = ZLattice.dual L` is the inverse
of the covolume of `L` (`ZLattice.covolume_dual`).

The *determinant* of `L` is `ZLattice.det L = covolume L ^ 2`, the Gram determinant of any
`ℤ`-basis of `L` (`ZLattice.det_eq_det_gram`). The *discriminant group* is the quotient
`ZLattice.DiscriminantGroup L = L^∨ ⧸ (L ∩ L^∨)`; it is defined for every lattice, and for an
integral lattice, where `L ≤ L^∨`, it is the quotient `L^∨ ⧸ L`. For an integral lattice the
discriminant group is finite of order `det L = [L^∨ : L]`
(`ZLattice.IsIntegral.det_eq_card_discriminantGroup`); in particular `det L` is then a positive
integer. Without integrality the discriminant group need not be finite: for `L = 2^{1/4} ℤ ⊆ ℝ`,
the dual is `2^{-1/4} ℤ` and `L ∩ L^∨ = 0`.

For an integral lattice, unimodularity `L = L^∨` is equivalent to each of `covolume L = 1`,
`det L = 1` and the triviality of the discriminant group. Unimodular lattices have covolume one
whether or not they are assumed integral (`ZLattice.IsUnimodular.covolume_eq_one`).

## Main definitions

* `ZLattice.det L`: the determinant `covolume L ^ 2` of a lattice.
* `ZLattice.DiscriminantGroup L`: the discriminant group `L^∨ ⧸ (L ∩ L^∨)`.

## Main statements

* `ZLattice.det_eq_det_gram`: `det L` is the Gram determinant of any `ℤ`-basis of `L`.
* `ZLattice.det_dual`: `det L^∨ = (det L)⁻¹`.
* `ZLattice.IsIntegral.det_eq_card_discriminantGroup`: for integral `L`, `det L = |L^∨ ⧸ L|`.
* `ZLattice.IsIntegral.finite_discriminantGroup`: for integral `L`, `L^∨ ⧸ L` is finite.
* `ZLattice.IsIntegral.isUnimodular_iff_covolume_eq_one`,
  `ZLattice.IsIntegral.isUnimodular_iff_det_eq_one`,
  `ZLattice.IsIntegral.isUnimodular_iff_subsingleton_discriminantGroup`: the forms of
  unimodularity for an integral lattice.

## References

* W. Ebeling, *Lattices and Codes*, 3rd ed., Springer, 2013, Chapter 1.
-/

public section

open Module Submodule MeasureTheory

namespace ZLattice

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-! ### The discriminant group -/

section DiscriminantGroup

/-- The discriminant group `L^∨ ⧸ (L ∩ L^∨)` of a lattice `L`, as the quotient of the dual lattice
by the vectors of `L` in it. For an integral lattice, where `L ≤ L^∨`, this is `L^∨ ⧸ L`, a finite
group of order `det L` (`IsIntegral.det_eq_card_discriminantGroup`). -/
abbrev DiscriminantGroup (L : Submodule ℤ E) : Type _ :=
  dual L ⧸ L.submoduleOf (dual L)

variable {L : Submodule ℤ E}

/-- A vector of the dual lattice represents the zero class of the discriminant group exactly when
it lies in `L`. -/
theorem discriminantGroup_mk_eq_zero_iff (x : dual L) :
    (Submodule.Quotient.mk x : DiscriminantGroup L) = 0 ↔ (x : E) ∈ L := by
  rw [Submodule.Quotient.mk_eq_zero, submoduleOf, Submodule.mem_comap, subtype_apply]

/-- Two vectors of the dual lattice represent the same class of the discriminant group exactly
when their difference lies in `L`. -/
@[simp]
theorem discriminantGroup_mk_eq_mk_iff (x y : dual L) :
    (Submodule.Quotient.mk x : DiscriminantGroup L) = Submodule.Quotient.mk y ↔
      (x : E) - y ∈ L := by
  rw [Submodule.Quotient.eq, submoduleOf, Submodule.mem_comap, subtype_apply,
    AddSubgroupClass.coe_sub]

/-- The order of the discriminant group is the index of `L ∩ L^∨` in `L^∨`. -/
theorem card_discriminantGroup :
    Nat.card (DiscriminantGroup L) = L.toAddSubgroup.relIndex (dual L).toAddSubgroup :=
  -- A quotient by a submodule is by definition the quotient by its underlying additive subgroup,
  -- and `relIndex` is the order of that quotient.
  (rfl)

/-- The discriminant group is trivial exactly when the dual lattice is contained in `L`. -/
theorem subsingleton_discriminantGroup_iff : Subsingleton (DiscriminantGroup L) ↔ dual L ≤ L := by
  rw [Submodule.Quotient.subsingleton_iff, submoduleOf_eq_top]

/-- An integral lattice is unimodular exactly when its discriminant group is trivial. -/
theorem IsIntegral.isUnimodular_iff_subsingleton_discriminantGroup (h : IsIntegral L) :
    IsUnimodular L ↔ Subsingleton (DiscriminantGroup L) := by
  rw [h.isUnimodular_iff, subsingleton_discriminantGroup_iff]

end DiscriminantGroup

/-! ### The determinant -/

section Determinant

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The determinant of a lattice `L`: the square of its covolume. For a full lattice it is the Gram
determinant of any `ℤ`-basis of `L` (`det_eq_det_gram`), and for an integral lattice it is the
order of the discriminant group (`IsIntegral.det_eq_card_discriminantGroup`). -/
noncomputable def det (L : Submodule ℤ E) : ℝ :=
  covolume L ^ 2

/-- The determinant of a lattice is the square of its covolume. -/
theorem det_def (L : Submodule ℤ E) : det L = covolume L ^ 2 :=
  (rfl)

variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- The determinant of a full lattice is positive. -/
theorem det_pos : 0 < det L :=
  pow_pos (covolume_pos L volume) 2

/-- The determinant of a full lattice is the determinant of the Gram matrix of any of its
`ℤ`-bases. -/
theorem det_eq_det_gram {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L) :
    det L = (Matrix.gram ℝ fun i ↦ (b i : E)).det :=
  covolume_sq_eq_det_gram L b

/-- The determinant of the dual of a full lattice is the inverse of its determinant. -/
@[simp]
theorem det_dual : det (dual L) = (det L)⁻¹ := by
  rw [det_def, det_def, covolume_dual, inv_pow]

variable [MeasurableSpace F] [FiniteDimensional ℝ F] [BorelSpace F] in
/-- The determinant is invariant under linear isometry equivalences. -/
@[simp]
theorem det_comap (e : F ≃ₗᵢ[ℝ] E) :
    det (ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap) = det L := by
  rw [det_def, det_def,
    ← covolume_comap L volume volume (e := e.toContinuousLinearEquiv) e.measurePreserving]
  -- Both sides pull `L` back along the linear map underlying `e`, reached through
  -- `toLinearEquiv` on the left and `toContinuousLinearEquiv` on the right; the two coercion
  -- paths agree by definition, and Mathlib states no rewrite lemma between them.
  rfl

variable {L}

/-- For an integral lattice `L`, the determinant is the index of `L` in its dual. -/
theorem IsIntegral.det_eq_relIndex (h : IsIntegral L) :
    det L = L.toAddSubgroup.relIndex (dual L).toAddSubgroup := by
  rw [← covolume_div_covolume_eq_relIndex' L (dual L) (isIntegral_iff_le_dual.mp h),
    covolume_dual, div_inv_eq_mul, det_def, sq]

/-- For an integral lattice `L`, the determinant is the order of the discriminant group
`L^∨ ⧸ L`. In particular it is a positive integer. -/
theorem IsIntegral.det_eq_card_discriminantGroup (h : IsIntegral L) :
    det L = Nat.card (DiscriminantGroup L) := by
  rw [h.det_eq_relIndex, card_discriminantGroup]

/-- The discriminant group of an integral lattice is finite. -/
theorem IsIntegral.finite_discriminantGroup (h : IsIntegral L) : Finite (DiscriminantGroup L) :=
  Nat.finite_of_card_ne_zero <| by
    exact_mod_cast h.det_eq_card_discriminantGroup ▸ (det_pos L).ne'

/-! ### Unimodular lattices -/

/-- A unimodular lattice has covolume one. -/
theorem IsUnimodular.covolume_eq_one (h : IsUnimodular L) : covolume L = 1 := by
  have hdet : det L * det L = 1 := by
    conv_lhs => enter [1]; rw [isUnimodular_iff_eq_dual.mp h, det_dual]
    exact inv_mul_cancel₀ (det_pos L).ne'
  rwa [← sq, pow_eq_one_iff_of_nonneg (det_pos L).le two_ne_zero, det_def,
    pow_eq_one_iff_of_nonneg (covolume_pos L volume).le two_ne_zero] at hdet

/-- A unimodular lattice has determinant one. -/
theorem IsUnimodular.det_eq_one (h : IsUnimodular L) : det L = 1 := by
  rw [det_def, h.covolume_eq_one, one_pow]

/-- An integral lattice is unimodular exactly when its determinant is one. -/
theorem IsIntegral.isUnimodular_iff_det_eq_one (h : IsIntegral L) :
    IsUnimodular L ↔ det L = 1 := by
  rw [h.isUnimodular_iff, h.det_eq_relIndex, Nat.cast_eq_one, AddSubgroup.relIndex_eq_one,
    toAddSubgroup_le]

/-- An integral lattice is unimodular exactly when its covolume is one. -/
theorem IsIntegral.isUnimodular_iff_covolume_eq_one (h : IsIntegral L) :
    IsUnimodular L ↔ covolume L = 1 := by
  rw [h.isUnimodular_iff_det_eq_one, det_def,
    pow_eq_one_iff_of_nonneg (covolume_pos L volume).le two_ne_zero]

end Determinant

end ZLattice
