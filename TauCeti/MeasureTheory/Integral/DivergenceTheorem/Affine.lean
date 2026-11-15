/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import TauCeti.MeasureTheory.Integral.DivergenceTheorem.Box
public import TauCeti.Topology.Algebra.Module.Determinant
import TauCeti.MeasureTheory.Integral.Bochner.Affine

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
theorem on the parallelepiped `A '' [0, 1]^ι`, with the boundary flux
`L.affineFluxBoundary p F = TauCeti.boxBoundarySum 0 1 H` over the faces of the unit cube on one
side. When `L` is the positive diagonal scaling `diag(b - a)` from `a` to `b` (`a < b`
coordinatewise), `L.affineFluxBoundary a F` recovers `TauCeti.boxBoundarySum a b F` unconditionally.

## Main declarations

* `ContinuousLinearEquiv.affineFluxPullback`: the cofactor pullback `H` of a flux field.
* `ContinuousLinearEquiv.hasFDerivAt_affineFluxPullback`: the derivative of `H j` at `u`.
* `ContinuousLinearEquiv.sum_fderiv_affineFluxPullback`: the divergence of `H` at `u` is
  `det L` times the divergence of `F` at `A u`.
* `ContinuousLinearEquiv.integral_divergence_affineFluxPullback`: **the divergence theorem on an
  affine parallelepiped**, in cofactor form on the unit cube.
* `ContinuousLinearEquiv.affineFluxBoundary`: the signed cofactor boundary flux on `[0, 1]ⁿ⁺¹`.
* `ContinuousLinearEquiv.affineFluxBoundary_piCongrRight_smulLeft`: positive diagonal scaling from
  `a` by `b - a` identifies `affineFluxBoundary` with `TauCeti.boxBoundarySum a b F`.

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

@[simp]
theorem affineFluxPullback_zero :
    L.affineFluxPullback p (fun _ _ ↦ (0 : E)) = fun _ _ ↦ 0 := by
  ext j u
  simp [affineFluxPullback_apply]

theorem affineFluxPullback_smul (r : ℝ) :
    L.affineFluxPullback p (fun i x ↦ r • F i x) = fun j u ↦ r • L.affineFluxPullback p F j u := by
  ext j u
  simp only [affineFluxPullback_apply, smul_comm _ r, Finset.smul_sum]

theorem affineFluxPullback_neg :
    L.affineFluxPullback p (fun i x ↦ -F i x) = fun j u ↦ -L.affineFluxPullback p F j u := by
  ext j u
  simpa using congr_fun₂ (L.affineFluxPullback_smul p F (-1 : ℝ)) j u

theorem affineFluxPullback_add (G : ι → (ι → ℝ) → E) :
    L.affineFluxPullback p (fun i x ↦ F i x + G i x) =
      fun j u ↦ L.affineFluxPullback p F j u + L.affineFluxPullback p G j u := by
  ext j u
  simp [affineFluxPullback_apply, smul_add, Finset.sum_add_distrib]

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

section Boundary

variable {n : ℕ} (L : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ)) (p : Fin (n + 1) → ℝ)
  (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E)

/-- The signed cofactor boundary flux of `F` on the affine parallelepiped `u ↦ p + L u`: the unit-
cube `TauCeti.boxBoundarySum` of the cofactor pullback `L.affineFluxPullback p F`. -/
noncomputable def affineFluxBoundary : E :=
  TauCeti.boxBoundarySum 0 1 (L.affineFluxPullback p F)

theorem affineFluxBoundary_def :
    L.affineFluxBoundary p F = TauCeti.boxBoundarySum 0 1 (L.affineFluxPullback p F) :=
  (rfl)

theorem affineFluxBoundary_eq_sum :
    L.affineFluxBoundary p F =
      ∑ j, ((∫ x in Icc (0 : Fin n → ℝ) 1, L.affineFluxPullback p F j (j.insertNth 1 x)) -
        ∫ x in Icc (0 : Fin n → ℝ) 1, L.affineFluxPullback p F j (j.insertNth 0 x)) :=
  TauCeti.boxBoundarySum_zero_one _

@[simp]
theorem affineFluxBoundary_zero :
    L.affineFluxBoundary p (fun _ _ ↦ (0 : E)) = 0 := by
  simp [affineFluxBoundary_def]

/-- Constant field families have zero cofactor boundary flux, for either sign of `det L`. -/
@[simp]
theorem affineFluxBoundary_const (c : Fin (n + 1) → E) :
    L.affineFluxBoundary p (fun i _ ↦ c i) = 0 := by
  have h : L.affineFluxPullback p (fun i _ ↦ c i) = fun j _ ↦
      LinearMap.det (L : (Fin (n + 1) → ℝ) →ₗ[ℝ] Fin (n + 1) → ℝ) •
        ∑ i, L.symm (Pi.single i 1) j • c i := (rfl)
  rw [affineFluxBoundary_def, h, TauCeti.boxBoundarySum_const]

/-- On the identity chart at the origin, `affineFluxBoundary` is `TauCeti.boxBoundarySum 0 1`. -/
@[simp]
theorem affineFluxBoundary_refl_zero :
    (ContinuousLinearEquiv.refl ℝ (Fin (n + 1) → ℝ)).affineFluxBoundary 0 F =
      TauCeti.boxBoundarySum 0 1 F := by
  have h : (ContinuousLinearEquiv.refl ℝ (Fin (n + 1) → ℝ)).affineFluxPullback 0 F = F := by
    ext j u
    simp
  rw [affineFluxBoundary_def, h]

theorem affineFluxBoundary_smul (r : ℝ) :
    L.affineFluxBoundary p (fun i x ↦ r • F i x) = r • L.affineFluxBoundary p F := by
  rw [affineFluxBoundary_def, affineFluxPullback_smul, TauCeti.boxBoundarySum_smul,
    ← affineFluxBoundary_def]

theorem affineFluxBoundary_neg :
    L.affineFluxBoundary p (fun i x ↦ -F i x) = -L.affineFluxBoundary p F := by
  simpa using L.affineFluxBoundary_smul p F (-1 : ℝ)

/-- Additivity of `affineFluxBoundary` for fields continuous on the closed parallelepiped. -/
theorem affineFluxBoundary_add_of_continuousOn {G : Fin (n + 1) → (Fin (n + 1) → ℝ) → E}
    (hF : ∀ i, ContinuousOn (F i) ((fun u ↦ p + L u) '' Icc 0 1))
    (hG : ∀ i, ContinuousOn (G i) ((fun u ↦ p + L u) '' Icc 0 1)) :
    L.affineFluxBoundary p (fun i x ↦ F i x + G i x) =
      L.affineFluxBoundary p F + L.affineFluxBoundary p G := by
  rw [affineFluxBoundary_def, affineFluxPullback_add]
  exact TauCeti.boxBoundarySum_add_of_continuousOn zero_le_one
    (L.continuousOn_affineFluxPullback p F hF) (L.continuousOn_affineFluxPullback p G hG)

/-- The affine divergence theorem written directly in terms of `L.affineFluxBoundary p F`. -/
theorem integral_divergence_eq_affineFluxBoundary
    (F' : Fin (n + 1) → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] E)
    (s : Set (Fin (n + 1) → ℝ)) (hs : s.Countable)
    (Hc : ∀ i, ContinuousOn (F i) ((fun u ↦ p + L u) '' Icc 0 1))
    (Hd : ∀ u ∈ (univ.pi fun _ ↦ Ioo 0 1) \ s, ∀ i,
      HasFDerivAt (F i) (F' i (p + L u)) (p + L u))
    (Hi : IntegrableOn (fun u ↦ ∑ i, F' i (p + L u) (Pi.single i 1)) (Icc 0 1)) :
    LinearMap.det (L : (Fin (n + 1) → ℝ) →ₗ[ℝ] Fin (n + 1) → ℝ) •
        ∫ u in Icc 0 1, ∑ i, F' i (p + L u) (Pi.single i 1) =
      L.affineFluxBoundary p F := by
  rw [affineFluxBoundary_eq_sum]
  exact L.integral_divergence_affineFluxPullback p F F' s hs Hc Hd Hi

/-- A continuous field on the closed parallelepiped with pointwise interior derivatives of zero
divergence has vanishing signed cofactor boundary flux, for either orientation of `L`. -/
theorem affineFluxBoundary_eq_zero_of_hasFDerivAt
    {F' : Fin (n + 1) → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] E}
    (Hc : ∀ i, ContinuousOn (F i) ((fun u ↦ p + L u) '' Icc 0 1))
    (Hd : ∀ u ∈ univ.pi fun _ ↦ Ioo 0 1, ∀ i,
      HasFDerivAt (F i) (F' i (p + L u)) (p + L u))
    (Hzero : ∀ u ∈ univ.pi fun _ ↦ Ioo 0 1, ∑ i, F' i (p + L u) (Pi.single i 1) = 0) :
    L.affineFluxBoundary p F = 0 := by
  have hae : (fun u ↦ ∑ i, F' i (p + L u) (Pi.single i 1)) =ᵐ[
      volume.restrict (Icc (0 : Fin (n + 1) → ℝ) 1)] 0 := by
    rw [volume_pi, ← Measure.restrict_congr_set Measure.univ_pi_Ioo_ae_eq_Icc]
    exact (ae_restrict_mem (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioo)).mono Hzero
  have h := L.integral_divergence_eq_affineFluxBoundary p F F' ∅ countable_empty Hc
    (fun u hu ↦ Hd u hu.1) ((integrable_zero _ _ _).congr hae.symm)
  rw [integral_congr_ae hae] at h
  simpa only [Pi.zero_apply, integral_zero, smul_zero] using h.symm

end Boundary

section Diagonal

variable {n : ℕ}

/-- For the diagonal scaling `L = diag(b - a)` of a nondegenerate box `a < b`, the `j`-th component
of `L.affineFluxPullback a F` scales `F j` by the `n`-dimensional face volume
`∏ r, (b (j.succAbove r) - a (j.succAbove r))`. -/
theorem affineFluxPullback_piCongrRight_smulLeft {a b : Fin (n + 1) → ℝ} (hab : ∀ i, a i < b i)
    (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E) (j : Fin (n + 1)) (u : Fin (n + 1) → ℝ) :
    affineFluxPullback (piCongrRight fun i ↦
        (smulLeft (Units.mk0 (b i - a i) (sub_ne_zero.mpr (hab i).ne')) : ℝ ≃L[ℝ] ℝ))
      a F j u =
      (∏ r : Fin n, (b (j.succAbove r) - a (j.succAbove r))) •
        F j (fun i ↦ a i + (b i - a i) * u i) := by
  set e : Fin (n + 1) → ℝ ≃L[ℝ] ℝ :=
    fun i ↦ smulLeft (Units.mk0 (b i - a i) (sub_ne_zero.mpr (hab i).ne'))
  have hdet : LinearMap.det (piCongrRight e : (Fin (n + 1) → ℝ) →ₗ[ℝ] Fin (n + 1) → ℝ) =
      ∏ i, (b i - a i) := by
    simp [e, det_piCongrRight]
  have hsymm : (e j).symm 1 = (b j - a j)⁻¹ := by
    have hne : b j - a j ≠ 0 := sub_ne_zero.mpr (hab j).ne'
    apply mul_left_cancel₀ hne
    have happ : e j ((e j).symm 1) = 1 := apply_symm_apply (e j) 1
    simp only [e, smulLeft_apply_apply, Units.smul_def, Units.val_mk0, smul_eq_mul] at happ
    rw [happ, mul_inv_cancel₀ hne]
  have hsum : ∑ i, (piCongrRight e).symm (Pi.single i 1) j • F i (a + piCongrRight e u) =
      (b j - a j)⁻¹ • F j (fun i ↦ a i + (b i - a i) * u i) := by
    rw [Finset.sum_eq_single j]
    · have hfun : a + piCongrRight e u = fun i ↦ a i + (b i - a i) * u i := by
        ext i
        simp [e]
      simp [hsymm, hfun]
    · intro _ _ hij
      simp [Pi.single_eq_of_ne hij.symm]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  rw [affineFluxPullback_apply, hdet, hsum, smul_smul, Fin.prod_univ_succAbove _ j,
    mul_right_comm, mul_inv_cancel₀ (sub_ne_zero.mpr (hab j).ne'), one_mul]

/-- Positive diagonal scaling `L = diag(b - a)` from `a` (`a < b` coordinatewise) identifies the
cofactor boundary flux `L.affineFluxBoundary a F` with `TauCeti.boxBoundarySum a b F`, without
continuity, measurability or completeness hypotheses. -/
theorem affineFluxBoundary_piCongrRight_smulLeft {a b : Fin (n + 1) → ℝ} (hab : ∀ i, a i < b i)
    (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E) :
    affineFluxBoundary (piCongrRight fun i ↦
        (smulLeft (Units.mk0 (b i - a i) (sub_ne_zero.mpr (hab i).ne')) : ℝ ≃L[ℝ] ℝ))
      a F = TauCeti.boxBoundarySum a b F := by
  rw [affineFluxBoundary_eq_sum, TauCeti.boxBoundarySum_def]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp_rw [affineFluxPullback_piCongrRight_smulLeft hab F j, integral_smul]
  have hface : a ∘ j.succAbove ≤ b ∘ j.succAbove := fun r ↦ (hab (j.succAbove r)).le
  have hfront (x : Fin n → ℝ) :
      (fun i ↦ a i + (b i - a i) * j.insertNth (α := fun _ ↦ ℝ) 1 x i) =
        j.insertNth (b j)
          (fun r ↦ a (j.succAbove r) + (b (j.succAbove r) - a (j.succAbove r)) * x r) := by
    ext i
    exact j.succAboveCases (by simp) (fun r ↦ by simp) i
  have hback (x : Fin n → ℝ) :
      (fun i ↦ a i + (b i - a i) * j.insertNth (α := fun _ ↦ ℝ) 0 x i) =
        j.insertNth (a j)
          (fun r ↦ a (j.succAbove r) + (b (j.succAbove r) - a (j.succAbove r)) * x r) := by
    ext i
    exact j.succAboveCases (by simp) (fun r ↦ by simp) i
  simp_rw [hfront, hback]
  rw [setIntegral_Icc_eq_smul_integral_unitCube hface (fun y ↦ F j (j.insertNth (b j) y)),
    setIntegral_Icc_eq_smul_integral_unitCube hface (fun y ↦ F j (j.insertNth (a j) y))]
  simp only [Function.comp_apply]

end Diagonal

end ContinuousLinearEquiv
