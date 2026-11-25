/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Compatible
public import TauCeti.Geometry.Symplectic.Cotangent.Liouville
public import TauCeti.Geometry.Symplectic.Liouville.Radial.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The doubled inner product space as a cotangent space

Let `V` be a finite-dimensional real inner product space. Identifying the second factor of
`V × V` with the continuous dual by the Riesz map `y ↦ ⟪y, ·⟫` gives the continuous linear
equivalence

`(x, y) ↦ (x, ⟪y, ·⟫)` (`TauCeti.cotangentInnerEquiv`)

of `V × V` with the continuous-dual cotangent space `V × V*`, in which `x` is the position `q` and
`⟪y, ·⟫` the momentum `p`. It carries the standard symplectic form `⟪x₁, y₂⟫ - ⟪y₁, x₂⟫` of `V × V`
to the canonical form `ω_can = -dλ_can` of the cotangent space
(`TauCeti.isSymplectomorphism_cotangentInnerEquiv`), where `λ_can = p dq` is the Liouville form
`TauCeti.cotangentLiouvilleForm`. For `V = ℝⁿ` with coordinates `q = x`, `p = y`, this is
`ω₀ = Σ_j dx_j ∧ dy_j = ω_can`; composed with `(x, y) ↦ x + i y`, it identifies `ℂⁿ` with the
cotangent space of `ℝⁿ` in the sign convention of the cotangent theory.

The two natural primitives of the standard form differ by an exact form. The radial primitive
`α_z(v) = ω₀(z, v) / 2 = (⟪x, v_y⟫ - ⟪y, v_x⟫) / 2` of `V × V`
(`TauCeti.SymplecticForm.radialPrimitive`), which on `ℝⁿ × ℝⁿ` is
`(1/2) Σ_j (x_j dy_j - y_j dx_j)`, is

`α = -λ_can + (1/2) d⟪x, y⟫`

after reading `λ_can = Σ_j y_j dx_j` on `V × V` through the identification, which is its own
differential (`TauCeti.radialPrimitive_stdSymplecticForm_apply`, stated on each tangent vector).
So `α` and `-λ_can` have the same periods along closed curves, and a submanifold is exact for one
primitive exactly when it is exact for the other.

## Main declarations

* `TauCeti.cotangentInnerEquiv`: the identification `(x, y) ↦ (x, ⟪y, ·⟫)` of `V × V` with
  `V × V*`.
* `TauCeti.isSymplectomorphism_cotangentInnerEquiv`: it is a symplectomorphism from the standard
  form to the canonical cotangent form.
* `TauCeti.radialPrimitive_stdSymplecticForm_apply`: `α = -λ_can + (1/2) d⟪x, y⟫`.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Sections 3.1 and 3.2 (the canonical form of a cotangent bundle and the standard form of `ℝ²ⁿ`).
-/

public section

open scoped InnerProductSpace

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The identification `(x, y) ↦ (x, ⟪y, ·⟫)` of the doubled inner product space `V × V` with the
continuous-dual cotangent space `V × V*`, through the Riesz map in the second factor. -/
noncomputable def cotangentInnerEquiv : (V × V) ≃L[ℝ] (V × StrongDual ℝ V) :=
  (cotangentModelEquiv.trans strongDualCotangentEquiv.symm).toContinuousLinearEquiv

/-- The identification `TauCeti.cotangentInnerEquiv` keeps the position. -/
@[simp]
theorem cotangentInnerEquiv_apply_fst (z : V × V) : (cotangentInnerEquiv z).1 = z.1 := by
  simp [cotangentInnerEquiv]

/-- The identification `TauCeti.cotangentInnerEquiv` sends `y` to the momentum `⟪y, ·⟫`. -/
@[simp]
theorem cotangentInnerEquiv_apply_snd_apply (z : V × V) (w : V) :
    (cotangentInnerEquiv z).2 w = ⟪z.2, w⟫_ℝ := by
  simp [cotangentInnerEquiv]

/-- **The standard form is the canonical cotangent form.** The identification
`(x, y) ↦ (x, ⟪y, ·⟫)` is a symplectomorphism from the standard symplectic form of `V × V` to the
canonical symplectic form `-dλ_can` of `V × V*`. -/
theorem isSymplectomorphism_cotangentInnerEquiv :
    SymplecticForm.IsSymplectomorphism (stdSymplecticForm (V := V))
      (strongDualCotangentSymplecticForm (V := V)) cotangentInnerEquiv.toLinearEquiv :=
  isSymplectomorphism_cotangentModelEquiv.trans isSymplectomorphism_strongDualCotangentEquiv.symm

/-- **The radial primitive and the Liouville form.** The radial primitive
`α = (⟪x, dy⟫ - ⟪y, dx⟫) / 2` of the standard symplectic form of `V × V` is
`-λ_can + (1/2) d⟪x, y⟫`, where `λ_can = ⟪y, dx⟫` is the Liouville form `p dq` read through
`(x, y) ↦ (x, ⟪y, ·⟫)`: at every point `z` and on every tangent vector `v`,
`α_z(v) = -λ_can(ψ z)(ψ v) + (1/2) d⟪x, y⟫_z(v)` for `ψ = TauCeti.cotangentInnerEquiv`, which is its
own differential. -/
theorem radialPrimitive_stdSymplecticForm_apply (z v : V × V) :
    (stdSymplecticForm (V := V)).radialPrimitive.val z ![v] =
      -cotangentLiouvilleForm (cotangentInnerEquiv z) ![cotangentInnerEquiv v] +
        2⁻¹ * fderiv ℝ (fun z : V × V ↦ ⟪z.1, z.2⟫_ℝ) z v := by
  -- The radial primitive is stated on tangent vectors of the model space, which are the vectors
  -- of `V × V` only up to definitional unfolding; `Eq.trans` bridges the two types.
  have hα : (stdSymplecticForm (V := V)).radialPrimitive.val z ![v] =
      2⁻¹ * (⟪z.1, v.2⟫_ℝ - ⟪z.2, v.1⟫_ℝ) :=
    (SymplecticForm.radialPrimitive_apply _ z v).trans (congrArg _ (stdSymplecticForm_apply z v))
  have hd : fderiv ℝ (fun z : V × V ↦ ⟪z.1, z.2⟫_ℝ) z v = ⟪z.1, v.2⟫_ℝ + ⟪v.1, z.2⟫_ℝ := by
    rw [fderiv_inner_apply ℝ (differentiableAt_fst (𝕜 := ℝ)) (differentiableAt_snd (𝕜 := ℝ)),
      fderiv_fst, fderiv_snd]
    simp only [ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  rw [hα, hd, cotangentLiouvilleForm_apply]
  simp only [Matrix.cons_val_zero, cotangentInnerEquiv_apply_fst,
    cotangentInnerEquiv_apply_snd_apply, real_inner_comm v.1]
  ring

end TauCeti
