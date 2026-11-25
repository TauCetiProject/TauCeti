/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.NormalizedDeterminant
public import TauCeti.Geometry.Symplectic.Complex.ImInner.Basis
public import TauCeti.Geometry.Symplectic.ConleyZehnder.FrameChange

/-!
# The Maslov index of a loop of unitary maps

Let `G` be a finite-dimensional complex inner product space, regarded as a real symplectic vector
space with the form `ω₀ = Im ⟪·, ·⟫_ℂ` (`TauCeti.imInnerSymplecticForm`). A real-linear map of `G`
which is complex linear and preserves `ω₀` is unitary, so a loop `g` of such maps is a loop in the
unitary group of `G`. This file computes its Maslov index
(`TauCeti.SymplecticForm.maslovIndex`) from the complex determinants of the maps: for every
continuous lift `θ` of the normalized complex determinant `t ↦ det_ℂ (g t) / |det_ℂ (g t)|`
through `Circle.exp`,

`2π μ(g) = θ 0 - θ 1`

(`TauCeti.SymplecticForm.maslovIndex_imInnerSymplecticForm_mul_two_pi_eq`). So the Maslov index
is minus the winding number of the complex determinant around the circle.

The sign comes from the orientation conventions. The Maslov index is read in a symplectic basis,
one in which `ω₀` has the matrix `Matrix.J = !![0, -1; 1, 0]`, and for an orthonormal basis `e`
of `G` the real basis `(i e, e)` (`OrthonormalBasis.imInnerSymplecticBasis`) is one; but
multiplication by `i` sends `i e_j` to `-e_j`, so in this basis the matrix of a complex-linear map
with complex matrix `U` is the realification of the conjugate matrix `Ū`, not of `U`. On realified
unitary matrices the Maslov index is the winding number of the complex determinant
(`TauCeti.GLSymplectic.maslovIndex_map_ofUnitary`), and the determinant of `Ū` is the complex
conjugate of that of `U`, which winds the other way around the circle.

This is the form in which the Maslov index enters the change of trivialization along a capped
periodic orbit: trivializations over two caps that are unitary for a compatible almost complex
structure differ along the orbit by a loop of unitary maps, and the winding number of its
determinant is a clutching number, the first Chern number of the sphere glued from the two caps.

## Main results

* `TauCeti.SymplecticForm.maslovIndex_imInnerSymplecticForm_mul_two_pi_eq`: the Maslov index of a
  loop of complex-linear maps preserving `Im ⟪·, ·⟫_ℂ` is minus the winding number of their
  complex determinants.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Theorem 2.2.12 (the normalization of the Maslov index of loops of symplectic matrices on the
  unitary group).
-/

public section

noncomputable section

open Module Matrix
open scoped InnerProductSpace unitInterval

namespace TauCeti.SymplecticForm

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-! ### The Maslov index of a loop of unitary maps -/

/-- On a complex-linear map preserving `Im ⟪·, ·⟫_ℂ`, read in the symplectic basis `(i e, e)`, the
map `ρ` of the Maslov index is the inverse of the normalized complex determinant. -/
private theorem maslovPhase_toGLSymplectic_imInnerSymplecticBasis {m : ℕ}
    (e : OrthonormalBasis (Fin m) ℂ G) (k : G ≃L[ℂ] G)
    (hk : ∀ u v, imInnerSymplecticForm G
      (((k.toLinearEquiv : G →ₗ[ℂ] G).restrictScalars ℝ) u)
      (((k.toLinearEquiv : G →ₗ[ℂ] G).restrictScalars ℝ) v) = imInnerSymplecticForm G u v) :
    GLSymplectic.maslovPhase ((imInnerSymplecticForm G).toGLSymplectic
      e.toMatrix_imInnerSymplecticForm ((k.toLinearEquiv : G →ₗ[ℂ] G).restrictScalars ℝ) hk) =
      k.normalizedDet⁻¹ := by
  set U := LinearMap.toMatrix e.toBasis e.toBasis (k.toLinearEquiv : G →ₗ[ℂ] G)
  -- The conjugate matrix `Ū` is unitary, since its realification is symplectic.
  have hV : U.map (starRingEnd ℂ) ∈ unitaryGroup (Fin m) ℂ := by
    rw [← realify_mem_symplecticGroup_iff, ← e.toMatrix_imInnerSymplecticBasis_restrictScalars]
    exact (imInnerSymplecticForm G).toMatrix_mem_symplecticGroup
      e.toMatrix_imInnerSymplecticForm hk
  have hA : (imInnerSymplecticForm G).toGLSymplectic e.toMatrix_imInnerSymplecticForm
      ((k.toLinearEquiv : G →ₗ[ℂ] G).restrictScalars ℝ) hk = GLSymplectic.ofUnitary ⟨_, hV⟩ :=
    Subtype.ext (Units.ext (by
      rw [coe_toGLSymplectic, GLSymplectic.coe_ofUnitary,
        e.toMatrix_imInnerSymplecticBasis_restrictScalars]))
  -- The determinant of `Ū` is the conjugate of `det U = det_ℂ k`, a point of the circle.
  have hdet : (U.map (starRingEnd ℂ)).det =
      starRingEnd ℂ (LinearMap.det (k.toLinearEquiv : G →ₗ[ℂ] G)) := by
    rw [← LinearMap.det_toMatrix e.toBasis, RingHom.map_det, RingHom.mapMatrix_apply]
  have hnorm : ‖LinearMap.det (k.toLinearEquiv : G →ₗ[ℂ] G)‖ = 1 := by
    have h := Circle.norm_coe (Matrix.UnitaryGroup.detCircle (⟨_, hV⟩ : unitaryGroup (Fin m) ℂ))
    rwa [Matrix.UnitaryGroup.coe_detCircle, hdet, Complex.norm_conj] at h
  rw [hA, GLSymplectic.maslovPhase_ofUnitary]
  refine Circle.ext ?_
  rw [Matrix.UnitaryGroup.coe_detCircle, Circle.coe_inv_eq_conj,
    ContinuousLinearEquiv.coe_normalizedDet, hnorm, Complex.ofReal_one, div_one]
  exact hdet

/-- **The Maslov index of a loop of unitary maps.** Let `G` be a finite-dimensional complex inner
product space with the symplectic form `Im ⟪·, ·⟫_ℂ`, and `g` a loop of real-linear maps of `G`
preserving it which are complex linear, `g t = k t` for complex-linear automorphisms `k t`. Then
for every continuous lift `θ` of the normalized complex determinant
`t ↦ det_ℂ (k t) / |det_ℂ (k t)|` through `Circle.exp`, `2π` times the Maslov index of `g` is
`θ 0 - θ 1`: the Maslov index is minus the winding number of the complex determinant. -/
theorem maslovIndex_imInnerSymplecticForm_mul_two_pi_eq [FiniteDimensional ℂ G] {A : G →L[ℝ] G}
    (g : Path A A)
    (hg : ∀ t u v, imInnerSymplecticForm G (g t u) (g t v) = imInnerSymplecticForm G u v)
    {k : I → G ≃L[ℂ] G} (hgk : ∀ t v, g t v = k t v) {θ : I → ℝ} (hθ : Continuous θ)
    (hθk : ∀ t, Circle.exp (θ t) = (k t).normalizedDet) :
    ((imInnerSymplecticForm G).maslovIndex g hg : ℝ) * (2 * Real.pi) = θ 0 - θ 1 := by
  set e := stdOrthonormalBasis ℂ G
  have hb := e.toMatrix_imInnerSymplecticForm
  have hgk' (t : I) : (g t : G →ₗ[ℝ] G) = (((k t).toLinearEquiv : G →ₗ[ℂ] G).restrictScalars ℝ) :=
    LinearMap.ext (hgk t)
  -- In the basis `(i e, e)` the map `ρ` along the loop is the inverse of the determinant, which
  -- `-θ` lifts.
  have hlift (t : I) : Circle.exp (-θ t) =
      ((imInnerSymplecticForm G).matrixPath hb g hg).map GLSymplectic.continuous_maslovPhase t := by
    rw [Path.map_coe, Function.comp_apply, matrixPath_apply,
      (imInnerSymplecticForm G).toGLSymplectic_congr hb (hgk' t) _ fun u v ↦ hgk' t ▸ hg t u v,
      maslovPhase_toGLSymplectic_imInnerSymplecticBasis, Circle.exp_neg, hθk]
  rw [(imInnerSymplecticForm G).maslovIndex_eq hb, GLSymplectic.maslovIndex_def,
    ← Circle.sub_eq_degree_mul _ hθ.neg hlift, Pi.neg_apply, Pi.neg_apply]
  ring

end TauCeti.SymplecticForm
