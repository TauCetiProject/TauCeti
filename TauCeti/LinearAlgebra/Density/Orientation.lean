/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Density.Basic
public import TauCeti.LinearAlgebra.Orientation.Basis

/-!
# The density of an oriented top form

On an `m`-dimensional real vector space with an orientation `o`, a top-degree alternating
form `φ` determines the density `φ.toDensity o`. It agrees with `φ` on positively oriented
bases and with `-φ` on negatively oriented ones. On an arbitrary tuple `v` it is
`|b.det v| * φ b` for any positively oriented basis `b`. Reversing the orientation negates the
density, and for a fixed orientation `φ ↦ φ.toDensity o` is a linear equivalence between top
forms and densities (`Orientation.densityEquiv`).

This is the pointwise half of the passage from oriented integration of top forms to the
orientation-free integration of densities.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 16,
  Densities.
-/

public section

open TauCeti Module

namespace AlternatingMap

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {m : ℕ}

variable [FiniteDimensional ℝ V] [Fact (finrank ℝ V = m)]

variable (V m) in
/-- The reference basis used to define densities of top forms. -/
private noncomputable def refBasis : Basis (Fin m) ℝ V :=
  finBasisOfFinrankEq ℝ V Fact.out

/-- The density of a top form `φ` with respect to an orientation `o`: on a positively oriented
basis it takes the value of `φ`, and on a negatively oriented basis the value of `-φ`. -/
noncomputable def toDensity (φ : V [⋀^Fin m]→ₗ[ℝ] ℝ) (o : Orientation ℝ V (Fin m)) :
    Density V m :=
  (refBasis V m).density ((o.signBasis (refBasis V m) : ℝ) * φ (refBasis V m))

private theorem toDensity_apply_basis (φ : V [⋀^Fin m]→ₗ[ℝ] ℝ) (o : Orientation ℝ V (Fin m))
    (b : Basis (Fin m) ℝ V) : φ.toDensity o b = (o.signBasis b : ℝ) * φ b := by
  rw [toDensity, Basis.density_apply]
  rcases (refBasis V m).orientation_eq_or_eq_neg o with rfl | rfl
  · rw [Orientation.signBasis_orientation, Units.val_one, Int.cast_one, one_mul,
      φ.signBasis_mul_apply_eq_abs_det_mul]
  · simp only [Orientation.signBasis_neg, Orientation.signBasis_orientation, Units.val_neg,
      Units.val_one, Int.cast_neg, Int.cast_one, one_mul, neg_mul, mul_neg,
      φ.signBasis_mul_apply_eq_abs_det_mul]

/-- On a positively oriented basis, the density of a top form is the form itself. -/
@[simp]
theorem toDensity_apply_of_orientation_eq (φ : V [⋀^Fin m]→ₗ[ℝ] ℝ)
    {o : Orientation ℝ V (Fin m)} {b : Basis (Fin m) ℝ V} (hb : b.orientation = o) :
    φ.toDensity o b = φ b := by
  rw [toDensity_apply_basis, ← hb, Orientation.signBasis_orientation, Units.val_one, Int.cast_one,
    one_mul]

/-- On a negatively oriented basis, the density of a top form is the negated form. -/
@[simp]
theorem toDensity_apply_of_orientation_eq_neg (φ : V [⋀^Fin m]→ₗ[ℝ] ℝ)
    {o : Orientation ℝ V (Fin m)} {b : Basis (Fin m) ℝ V} (hb : b.orientation = -o) :
    φ.toDensity o b = -φ b := by
  rw [toDensity_apply_basis, ← neg_neg o, ← hb, Orientation.signBasis_neg,
    Orientation.signBasis_orientation, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one,
    neg_one_mul]

/-- The density of a top form on a basis: the value of the form, negated when the basis is
negatively oriented. -/
theorem toDensity_apply (φ : V [⋀^Fin m]→ₗ[ℝ] ℝ) (o : Orientation ℝ V (Fin m))
    (b : Basis (Fin m) ℝ V) [Decidable (b.orientation = o)] :
    φ.toDensity o b = if b.orientation = o then φ b else -φ b := by
  split_ifs with hb
  · exact toDensity_apply_of_orientation_eq φ hb
  · exact toDensity_apply_of_orientation_eq_neg φ
      (neg_eq_iff_eq_neg (a := o) (b := b.orientation) |>.2
        ((b.orientation_ne_iff_eq_neg o).1 (Ne.symm hb))).symm

/-- The density of a top form on an arbitrary tuple is the absolute determinant of the tuple
in any positively oriented basis, times the value of the form on that basis. -/
theorem toDensity_apply_eq_abs_det_mul (φ : V [⋀^Fin m]→ₗ[ℝ] ℝ)
    {o : Orientation ℝ V (Fin m)} {b : Basis (Fin m) ℝ V} (hb : b.orientation = o)
    (v : Fin m → V) : φ.toDensity o v = |b.det v| * φ b := by
  rw [(φ.toDensity o).apply_eq_abs_det_mul b, toDensity_apply_of_orientation_eq φ hb]

/-- Reversing the orientation negates the density of a top form. -/
@[simp]
theorem toDensity_neg_orientation (φ : V [⋀^Fin m]→ₗ[ℝ] ℝ) (o : Orientation ℝ V (Fin m)) :
    φ.toDensity (-o) = -φ.toDensity o := by
  apply (refBasis V m).density_ext
  rw [Density.neg_apply, toDensity_apply_basis, toDensity_apply_basis, Orientation.signBasis_neg,
    Units.val_neg, Int.cast_neg, neg_mul]

/-- The density of a sum of top forms is the sum of their densities. -/
@[simp]
theorem toDensity_add (φ ψ : V [⋀^Fin m]→ₗ[ℝ] ℝ) (o : Orientation ℝ V (Fin m)) :
    (φ + ψ).toDensity o = φ.toDensity o + ψ.toDensity o := by
  apply (refBasis V m).density_ext
  rw [Density.add_apply, toDensity_apply_basis, toDensity_apply_basis, toDensity_apply_basis,
    add_apply, mul_add]

/-- The density of a scalar multiple of a top form is the scalar multiple of its density. -/
@[simp]
theorem toDensity_smul (c : ℝ) (φ : V [⋀^Fin m]→ₗ[ℝ] ℝ) (o : Orientation ℝ V (Fin m)) :
    (c • φ).toDensity o = c • φ.toDensity o := by
  apply (refBasis V m).density_ext
  rw [Density.smul_apply, toDensity_apply_basis, toDensity_apply_basis, smul_apply, smul_eq_mul,
    smul_eq_mul, mul_left_comm]

/-- The density of the zero top form is zero. -/
@[simp]
theorem toDensity_zero (o : Orientation ℝ V (Fin m)) :
    (0 : V [⋀^Fin m]→ₗ[ℝ] ℝ).toDensity o = 0 := by
  rw [← zero_smul ℝ (0 : V [⋀^Fin m]→ₗ[ℝ] ℝ), toDensity_smul, zero_smul]

/-- The density of a negated top form is the negated density. -/
@[simp]
theorem toDensity_neg (φ : V [⋀^Fin m]→ₗ[ℝ] ℝ) (o : Orientation ℝ V (Fin m)) :
    (-φ).toDensity o = -φ.toDensity o := by
  rw [← neg_one_smul ℝ φ, toDensity_smul, neg_one_smul]

end AlternatingMap

namespace Orientation

open AlternatingMap

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] {m : ℕ}
  [Fact (finrank ℝ V = m)]

omit [FiniteDimensional ℝ V] [Fact (finrank ℝ V = m)] in
private theorem signBasis_cast_mul_self (o : Orientation ℝ V (Fin m)) (b : Basis (Fin m) ℝ V) :
    (o.signBasis b : ℝ) * o.signBasis b = 1 := by
  exact_mod_cast Int.isUnit_mul_self (o.signBasis b).isUnit

/-- For a fixed orientation, passing from a top form to its density is a linear equivalence:
a density is the density of exactly one top form. -/
noncomputable def densityEquiv (o : Orientation ℝ V (Fin m)) :
    (V [⋀^Fin m]→ₗ[ℝ] ℝ) ≃ₗ[ℝ] Density V m where
  toFun φ := φ.toDensity o
  invFun μ := ((o.signBasis (refBasis V m) : ℝ) * μ (refBasis V m)) • (refBasis V m).det
  map_add' φ ψ := toDensity_add φ ψ o
  map_smul' c φ := toDensity_smul c φ o
  left_inv φ := by
    dsimp only
    rw [toDensity_apply_basis, ← mul_assoc, signBasis_cast_mul_self, one_mul, ← φ.eq_smul_basis_det]
  right_inv μ := by
    apply (refBasis V m).density_ext
    rw [toDensity_apply_basis, smul_apply, Basis.det_self, smul_eq_mul, mul_one, ← mul_assoc,
      signBasis_cast_mul_self, one_mul]

@[simp]
theorem densityEquiv_apply (o : Orientation ℝ V (Fin m)) (φ : V [⋀^Fin m]→ₗ[ℝ] ℝ) :
    o.densityEquiv φ = φ.toDensity o := (rfl)

end Orientation
