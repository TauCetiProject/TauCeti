/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Density.Basic
public import Mathlib.LinearAlgebra.Orientation

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

/-- The value of a top form on a basis, with the sign flipped when the basis is negatively
oriented. -/
private noncomputable def signedValue (φ : V [⋀^Fin m]→ₗ[ℝ] ℝ) (o : Orientation ℝ V (Fin m))
    (e : Basis (Fin m) ℝ V) : ℝ :=
  haveI := Classical.propDecidable (e.orientation = o)
  if e.orientation = o then φ e else -φ e

private theorem signedValue_neg (φ : V [⋀^Fin m]→ₗ[ℝ] ℝ) (o : Orientation ℝ V (Fin m))
    (e : Basis (Fin m) ℝ V) : signedValue φ (-o) e = -signedValue φ o e := by
  unfold signedValue
  by_cases h : e.orientation = o
  · rw [ite_eq_right fun h' ↦ Module.Ray.ne_neg_self o (h.symm.trans h'), ite_eq_left h]
  · have h' : -o = e.orientation := neg_eq_iff_eq_neg (a := o) (b := e.orientation) |>.2
      ((e.orientation_ne_iff_eq_neg o).1 (Ne.symm h))
    rw [ite_eq_left h'.symm, ite_eq_right h, neg_neg]

/-- The signed value transforms between bases by the absolute determinant, when the target
basis is positively oriented. -/
private theorem signedValue_orientation_eq_abs_det_mul (φ : V [⋀^Fin m]→ₗ[ℝ] ℝ)
    (e b : Basis (Fin m) ℝ V) :
    signedValue φ b.orientation b = |e.det b| * signedValue φ b.orientation e := by
  have hφ : φ b = e.det b * φ e := by
    simpa [mul_comm] using DFunLike.congr_fun (φ.eq_smul_basis_det e) ⇑b
  have hpos : e.orientation = b.orientation ↔ 0 < e.det b := e.orientation_eq_iff_det_pos b
  unfold signedValue
  rw [ite_eq_left rfl, hφ]
  by_cases he : e.orientation = b.orientation
  · rw [ite_eq_left he, abs_of_pos (hpos.1 he)]
  · have hlt : e.det b < 0 :=
      lt_of_le_of_ne (not_lt.1 (mt hpos.2 he)) (e.isUnit_det b).ne_zero
    rw [ite_eq_right he, abs_of_neg hlt]
    ring

/-- The signed value transforms between bases by the absolute determinant. -/
private theorem signedValue_eq_abs_det_mul (φ : V [⋀^Fin m]→ₗ[ℝ] ℝ)
    (o : Orientation ℝ V (Fin m)) (e b : Basis (Fin m) ℝ V) :
    signedValue φ o b = |e.det b| * signedValue φ o e := by
  rcases b.orientation_eq_or_eq_neg o with rfl | rfl
  · exact signedValue_orientation_eq_abs_det_mul φ e b
  · rw [signedValue_neg, signedValue_neg, signedValue_orientation_eq_abs_det_mul φ e b, mul_neg]

private theorem signedValue_add (φ ψ : V [⋀^Fin m]→ₗ[ℝ] ℝ) (o : Orientation ℝ V (Fin m))
    (e : Basis (Fin m) ℝ V) :
    signedValue (φ + ψ) o e = signedValue φ o e + signedValue ψ o e := by
  unfold signedValue
  split_ifs <;> simp only [add_apply, neg_add]

private theorem signedValue_smul (c : ℝ) (φ : V [⋀^Fin m]→ₗ[ℝ] ℝ) (o : Orientation ℝ V (Fin m))
    (e : Basis (Fin m) ℝ V) : signedValue (c • φ) o e = c * signedValue φ o e := by
  unfold signedValue
  split_ifs <;> simp only [smul_apply, smul_eq_mul, mul_neg]

variable [FiniteDimensional ℝ V] [Fact (finrank ℝ V = m)]

variable (V m) in
/-- The reference basis used to define densities of top forms. -/
private noncomputable def refBasis : Basis (Fin m) ℝ V :=
  finBasisOfFinrankEq ℝ V Fact.out

/-- The density of a top form `φ` with respect to an orientation `o`: on a positively oriented
basis it takes the value of `φ`, and on a negatively oriented basis the value of `-φ`. -/
noncomputable def toDensity (φ : V [⋀^Fin m]→ₗ[ℝ] ℝ) (o : Orientation ℝ V (Fin m)) :
    Density V m :=
  (refBasis V m).density (signedValue φ o (refBasis V m))

private theorem toDensity_apply_basis (φ : V [⋀^Fin m]→ₗ[ℝ] ℝ) (o : Orientation ℝ V (Fin m))
    (b : Basis (Fin m) ℝ V) : φ.toDensity o b = signedValue φ o b := by
  rw [toDensity, Basis.density_apply, signedValue_eq_abs_det_mul φ o _ b]

/-- On a positively oriented basis, the density of a top form is the form itself. -/
theorem toDensity_apply_of_orientation_eq (φ : V [⋀^Fin m]→ₗ[ℝ] ℝ)
    {o : Orientation ℝ V (Fin m)} {b : Basis (Fin m) ℝ V} (hb : b.orientation = o) :
    φ.toDensity o b = φ b := by
  rw [toDensity_apply_basis, signedValue, ite_eq_left hb]

/-- On a negatively oriented basis, the density of a top form is the negated form. -/
theorem toDensity_apply_of_orientation_eq_neg (φ : V [⋀^Fin m]→ₗ[ℝ] ℝ)
    {o : Orientation ℝ V (Fin m)} {b : Basis (Fin m) ℝ V} (hb : b.orientation = -o) :
    φ.toDensity o b = -φ b := by
  rw [toDensity_apply_basis, signedValue,
    ite_eq_right fun h ↦ Module.Ray.ne_neg_self o (h.symm.trans hb)]

/-- The density of a top form on a basis: the value of the form, negated when the basis is
negatively oriented. -/
theorem toDensity_apply (φ : V [⋀^Fin m]→ₗ[ℝ] ℝ) (o : Orientation ℝ V (Fin m))
    (b : Basis (Fin m) ℝ V) [Decidable (b.orientation = o)] :
    φ.toDensity o b = if b.orientation = o then φ b else -φ b := by
  rw [toDensity_apply_basis, signedValue]
  congr

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
  rw [Density.neg_apply, toDensity_apply_basis, toDensity_apply_basis, signedValue_neg]

/-- The density of a sum of top forms is the sum of their densities. -/
@[simp]
theorem toDensity_add (φ ψ : V [⋀^Fin m]→ₗ[ℝ] ℝ) (o : Orientation ℝ V (Fin m)) :
    (φ + ψ).toDensity o = φ.toDensity o + ψ.toDensity o := by
  apply (refBasis V m).density_ext
  rw [Density.add_apply, toDensity_apply_basis, toDensity_apply_basis, toDensity_apply_basis,
    signedValue_add]

/-- The density of a scalar multiple of a top form is the scalar multiple of its density. -/
@[simp]
theorem toDensity_smul (c : ℝ) (φ : V [⋀^Fin m]→ₗ[ℝ] ℝ) (o : Orientation ℝ V (Fin m)) :
    (c • φ).toDensity o = c • φ.toDensity o := by
  apply (refBasis V m).density_ext
  rw [Density.smul_apply, toDensity_apply_basis, toDensity_apply_basis, signedValue_smul,
    smul_eq_mul]

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

/-- For a fixed orientation, passing from a top form to its density is a linear equivalence:
a density is the density of exactly one top form. -/
noncomputable def densityEquiv (o : Orientation ℝ V (Fin m)) :
    (V [⋀^Fin m]→ₗ[ℝ] ℝ) ≃ₗ[ℝ] Density V m where
  toFun φ := φ.toDensity o
  invFun μ := (signedValue (refBasis V m).det o (refBasis V m) * μ (refBasis V m)) •
    (refBasis V m).det
  map_add' φ ψ := toDensity_add φ ψ o
  map_smul' c φ := toDensity_smul c φ o
  left_inv φ := by
    have hs : signedValue (refBasis V m).det o (refBasis V m) *
        signedValue φ o (refBasis V m) = φ (refBasis V m) := by
      unfold signedValue
      split_ifs <;> simp [Basis.det_self]
    dsimp only
    rw [toDensity_apply_basis, hs, ← φ.eq_smul_basis_det]
  right_inv μ := by
    apply (refBasis V m).density_ext
    rw [toDensity_apply_basis, signedValue_smul]
    unfold signedValue
    split_ifs <;> simp [Basis.det_self]

@[simp]
theorem densityEquiv_apply (o : Orientation ℝ V (Fin m)) (φ : V [⋀^Fin m]→ₗ[ℝ] ℝ) :
    o.densityEquiv φ = φ.toDensity o := (rfl)

end Orientation
