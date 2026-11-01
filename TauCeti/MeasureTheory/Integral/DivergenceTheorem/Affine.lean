/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import TauCeti.Topology.Algebra.Module.Determinant

/-!
# The divergence theorem on affine parallelepipeds

Let `L` be a real continuous linear automorphism of `ι → ℝ`, let `p : ι → ℝ` and write
`A u = p + L u`, so that `A` maps the unit cube `[0, 1]^ι` onto a parallelepiped. A flux field
`F : ι → (ι → ℝ) → E` (component `i` of the field is `F i`) is transported to the unit cube by
the *cofactor pullback*

`H j u = det L • ∑ i, (L⁻¹)ⱼᵢ • F i (A u)`,

where `(L⁻¹)ⱼᵢ = L.symm (Pi.single i 1) j` is the `(j, i)` entry of the matrix of `L⁻¹`. The
matrix `det L • L⁻¹` is the adjugate of `L`. The field `H` is the contravariant Piola transform
of `F` along `A`: it is the coordinate expression of the pullback along `A` of the flux form
`∑ i, (-1)^i F i dx₀ ∧ ⋯ ∧ dxₙ` (with `dxᵢ` omitted from the `i`-th product). Its divergence is
the signed determinant times the divergence of `F`:

`∑ j, ∂ⱼ H j (u) = det L • ∑ i, ∂ᵢ F i (A u)`,

whenever every `F i` is differentiable at `A u`, because the coefficient of `∂ₖ F i` is
`det L • ∑ j, (L⁻¹)ⱼᵢ Lₖⱼ = det L • δₖᵢ` (`ContinuousLinearEquiv.sum_cofactor_comp_apply_single`).
Unlike the absolute value in the change of variables formula, the determinant here is signed.

Applying Mathlib's divergence theorem on the unit cube,
`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'`, to `H` gives the divergence
theorem on the parallelepiped `A '' [0, 1]^ι`, with the boundary integrals of `H` over the faces
of the unit cube on one side. As in Mathlib, only continuity on the closed parallelepiped,
differentiability at the interior points off a countable set and integrability of the divergence
are assumed; no continuity of the derivative is needed.

## Main declarations

* `ContinuousLinearEquiv.affineFluxPullback`: the cofactor pullback `H` of a flux field.
* `ContinuousLinearEquiv.hasFDerivAt_affineFluxPullback`: the derivative of `H j` at `u`.
* `ContinuousLinearEquiv.sum_fderiv_affineFluxPullback`: the divergence of `H` at `u` is
  `det L` times the divergence of `F` at `A u`.
* `ContinuousLinearEquiv.integral_divergence_affineFluxPullback`: **the divergence theorem on an
  affine parallelepiped**, in cofactor form on the unit cube.

## References

* P. G. Ciarlet, *Mathematical Elasticity, Vol. I: Three-Dimensional Elasticity*, North-Holland
  (1988), §1.7, for the Piola transform and the Piola identity, of which the cofactor pullback
  and its divergence formula are the affine case.
-/

public section

open MeasureTheory Set

namespace ContinuousLinearEquiv

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The cofactor pullback of a flux field `F` along the affine map `u ↦ p + L u`:
`H j u = det L • ∑ i, (L⁻¹)ⱼᵢ • F i (p + L u)`, where `(L⁻¹)ⱼᵢ = L.symm (Pi.single i 1) j`.
When every `F i` is differentiable at `p + L u`, its divergence at `u` is `det L` times the
divergence of `F` at `p + L u` (`ContinuousLinearEquiv.sum_fderiv_affineFluxPullback`). -/
noncomputable def affineFluxPullback (L : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (p : ι → ℝ)
    (F : ι → (ι → ℝ) → E) (j : ι) (u : ι → ℝ) : E :=
  LinearMap.det (L : (ι → ℝ) →ₗ[ℝ] ι → ℝ) • ∑ i, L.symm (Pi.single i 1) j • F i (p + L u)

variable (L : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (p : ι → ℝ) (F : ι → (ι → ℝ) → E)

theorem affineFluxPullback_apply (j : ι) (u : ι → ℝ) :
    L.affineFluxPullback p F j u =
      LinearMap.det (L : (ι → ℝ) →ₗ[ℝ] ι → ℝ) • ∑ i, L.symm (Pi.single i 1) j • F i (p + L u) := by
  rw [affineFluxPullback]

/-- For `L` the identity the cofactor pullback is the translated field `u ↦ F j (p + u)`. -/
@[simp]
theorem affineFluxPullback_refl (j : ι) (u : ι → ℝ) :
    (ContinuousLinearEquiv.refl ℝ (ι → ℝ)).affineFluxPullback p F j u = F j (p + u) := by
  have h : LinearMap.det
      (ContinuousLinearEquiv.refl ℝ (ι → ℝ) : (ι → ℝ) →ₗ[ℝ] ι → ℝ) = 1 := LinearMap.det_id
  simp [affineFluxPullback_apply, Pi.single_apply, h]

/-- The cofactor pullback of a field continuous on the parallelepiped `A '' s` is continuous on
`s`, where `A u = p + L u`. -/
theorem continuousOn_affineFluxPullback {s : Set (ι → ℝ)}
    (hF : ∀ i, ContinuousOn (F i) ((fun u ↦ p + L u) '' s)) (j : ι) :
    ContinuousOn (L.affineFluxPullback p F j) s := by
  have hA : ContinuousOn (fun u ↦ p + L u) s := (continuous_const.add L.continuous).continuousOn
  refine continuousOn_const.smul (continuousOn_finsetSum _ fun i _ ↦ continuousOn_const.smul ?_)
  exact (hF i).comp hA (mapsTo_image _ s)

/-- The derivative of a component of the cofactor pullback: if each `F i` has derivative `F' i`
at `p + L u`, then `H j` has derivative `det L • ∑ i, (L⁻¹)ⱼᵢ • (F' i ∘ L)` at `u`. -/
theorem hasFDerivAt_affineFluxPullback {F' : ι → (ι → ℝ) →L[ℝ] E} {u : ι → ℝ}
    (hF : ∀ i, HasFDerivAt (F i) (F' i) (p + L u)) (j : ι) :
    HasFDerivAt (L.affineFluxPullback p F j)
      (LinearMap.det (L : (ι → ℝ) →ₗ[ℝ] ι → ℝ) •
        ∑ i, L.symm (Pi.single i 1) j • (F' i).comp (L : (ι → ℝ) →L[ℝ] ι → ℝ)) u := by
  have hA : HasFDerivAt (fun u ↦ p + L u) (L : (ι → ℝ) →L[ℝ] ι → ℝ) u :=
    (L : (ι → ℝ) →L[ℝ] ι → ℝ).hasFDerivAt.const_add p
  unfold affineFluxPullback
  exact (HasFDerivAt.fun_sum fun i _ ↦
    ((hF i).comp u hA).const_smul (L.symm (Pi.single i 1) j)).const_smul
      (LinearMap.det (L : (ι → ℝ) →ₗ[ℝ] ι → ℝ))

/-- **The divergence of the cofactor pullback.** If every component of the field `F` is
differentiable at `p + L u`, then the divergence of the cofactor pullback at `u` is `det L` times
the divergence of `F` at `p + L u`. -/
theorem sum_fderiv_affineFluxPullback {u : ι → ℝ}
    (hF : ∀ i, DifferentiableAt ℝ (F i) (p + L u)) :
    ∑ j, fderiv ℝ (L.affineFluxPullback p F j) u (Pi.single j 1) =
      LinearMap.det (L : (ι → ℝ) →ₗ[ℝ] ι → ℝ) •
        ∑ i, fderiv ℝ (F i) (p + L u) (Pi.single i 1) := by
  have h j := (L.hasFDerivAt_affineFluxPullback p F (fun i ↦ (hF i).hasFDerivAt) j).fderiv
  simp_rw [h]
  exact L.sum_cofactor_comp_apply_single _

/-- **The divergence theorem on an affine parallelepiped.** Let `A u = p + L u` and let `F` be a
flux field continuous on the parallelepiped `A '' [0, 1]ⁿ⁺¹`, differentiable with derivatives
`F' i` at `A u` for every interior point `u` of the unit cube off a countable set, and with
`u ↦ div F (A u)` integrable on the unit cube. Then `det L` times the integral of `div F ∘ A` over
the unit cube is the boundary sum of the cofactor pullback `H = L.affineFluxPullback p F`: the sum
over `j` of the integral of `H j` over the front face `u j = 1` minus that over the back face
`u j = 0`. The determinant is signed. -/
theorem integral_divergence_affineFluxPullback {n : ℕ}
    (L : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ)) (p : Fin (n + 1) → ℝ)
    (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E)
    (F' : Fin (n + 1) → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] E)
    (s : Set (Fin (n + 1) → ℝ)) (hs : s.Countable)
    (Hc : ∀ i, ContinuousOn (F i) ((fun u ↦ p + L u) '' Icc 0 1))
    (Hd : ∀ u ∈ (univ.pi fun _ ↦ Ioo 0 1) \ s, ∀ i,
      HasFDerivAt (F i) (F' i (p + L u)) (p + L u))
    (Hi : IntegrableOn (fun u ↦ ∑ i, F' i (p + L u) (Pi.single i 1)) (Icc 0 1)) :
    LinearMap.det (L : (Fin (n + 1) → ℝ) →ₗ[ℝ] Fin (n + 1) → ℝ) •
        ∫ u in Icc 0 1, ∑ i, F' i (p + L u) (Pi.single i 1) =
      ∑ j, ((∫ x in Icc (0 : Fin n → ℝ) 1, L.affineFluxPullback p F j (j.insertNth 1 x)) -
        ∫ x in Icc (0 : Fin n → ℝ) 1, L.affineFluxPullback p F j (j.insertNth 0 x)) := by
  -- The explicit derivative of the cofactor pullback, defined at every point of the cube.
  let H' : Fin (n + 1) → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] E := fun j u ↦
    LinearMap.det (L : (Fin (n + 1) → ℝ) →ₗ[ℝ] Fin (n + 1) → ℝ) •
      ∑ i, L.symm (Pi.single i 1) j •
        (F' i (p + L u)).comp (L : (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → ℝ)
  have hdiv : ∀ u, ∑ j, H' j u (Pi.single j 1) =
      LinearMap.det (L : (Fin (n + 1) → ℝ) →ₗ[ℝ] Fin (n + 1) → ℝ) •
        ∑ i, F' i (p + L u) (Pi.single i 1) :=
    fun u ↦ L.sum_cofactor_comp_apply_single fun i ↦ F' i (p + L u)
  have h := integral_divergence_of_hasFDerivAt_off_countable' 0 1 zero_le_one
    (L.affineFluxPullback p F) H' s hs (L.continuousOn_affineFluxPullback p F Hc)
    (fun u hu j ↦ L.hasFDerivAt_affineFluxPullback p F (Hd u hu) j)
    (by simp only [hdiv]; exact Hi.smul _)
  simpa only [hdiv, integral_smul, Pi.zero_comp, Pi.one_comp, Pi.zero_apply, Pi.one_apply]
    using h

end ContinuousLinearEquiv
