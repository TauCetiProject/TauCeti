/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Quaternion.Cauchy.CutoffField
public import TauCeti.Analysis.Quaternion.AffineFace
import TauCeti.MeasureTheory.Integral.Bochner.Affine

/-!
# The left Cauchy–Fueter formula on affine parallelepipeds

The cofactor divergence theorem applied to the cut-off field gives the integral of
`cauchyFueterCutoffDensity ε q q₀ • f q` over an affine parallelepiped. As the cutoff
shrinks to an interior pole, this integral tends to `2π² • f q₀`. The cutoff eventually
leaves every face unchanged, yielding the left representation formula, both as a
cofactor boundary sum and as the raw affine integral of `G * Dq * f`.

The affine chart has positive determinant, so the parameter orientation is the outward
orientation. Only continuity on the closed parallelepiped and pointwise left Fueter
regularity in its punctured interior are assumed. No continuity of the derivative is
needed, and no measure on the quaternion carrier is introduced.

## References

* I. Frenkel and M. Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, Theorem 9.
* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979), 199–225.
-/

public section

open MeasureTheory Set Filter
open scoped Quaternion Topology

namespace TauCeti

open TauCeti.Quaternion _root_.Quaternion

variable {L : (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ)} {p x₀ : Fin 4 → ℝ} {f : ℍ → ℍ}

/-- The signed cofactor flux of the cut-off field is its density integral over the
physical parallelepiped when the affine chart has positive determinant. -/
theorem affineFlux_cauchyFueterCutoffField {ε : ℝ} (hε : 0 < ε)
    (hL : 0 < LinearMap.det (L : (Fin 4 → ℝ) →ₗ[ℝ] Fin 4 → ℝ))
    (hc : ContinuousOn f (dq '' ((fun u ↦ p + L u) '' Icc 0 1)))
    (hf : ∀ u ∈ pi univ (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1),
      dq (p + L u) ≠ dq x₀ → LeftFueterAt f (dq (p + L u))) :
    boxBoundarySum 0 1 (L.affineFluxPullback p
      (fun i x ↦ cauchyFueterCutoffField ε (dq x₀) f i (dq x))) =
      ∫ x in (fun u ↦ p + L u) '' Icc 0 1,
        cauchyFueterCutoffDensity ε (dq x) (dq x₀) • f (dq x) := by
  let F i x := cauchyFueterCutoffField ε (dq x₀) f i (dq x)
  let D i x := (fderiv ℝ (cauchyFueterCutoffField ε (dq x₀) f i) (dq x)).comp dq
  have hdiv u (hu : u ∈ pi univ (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1)) :
      ∑ i, D i (p + L u) (Pi.single i 1) =
        cauchyFueterCutoffDensity ε (dq (p + L u)) (dq x₀) • f (dq (p + L u)) :=
    sum_fderiv_cauchyFueterCutoffField hε (hf u hu)
  -- Interior differentiability suffices because the cube boundary has measure zero.
  have hae : (fun u ↦ ∑ i, D i (p + L u) (Pi.single i 1)) =ᵐ[
      volume.restrict (Icc (0 : Fin 4 → ℝ) 1)]
      (fun u ↦ cauchyFueterCutoffDensity ε (dq (p + L u)) (dq x₀) • f (dq (p + L u))) := by
    rw [volume_pi, ← Measure.restrict_congr_set Measure.univ_pi_Ioo_ae_eq_Icc]
    exact (ae_restrict_mem (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioo)).mono hdiv
  have hfc := hc.comp dq.continuous.continuousOn (fun _ hx ↦ mem_image_of_mem _ hx)
  have hi := (integrable_cauchyFueterCutoffDensity hε (dq x₀)).integrableOn.smul_continuousOn
    hfc (isCompact_Icc.image (continuous_const.add L.continuous))
  -- Transport integrability to the parameter cube before applying the cofactor theorem.
  have hip := (L.integrableOn_image_affine_iff p _ (Icc 0 1) volume).mp hi
  have h := L.integral_divergence_affineFluxPullback p F D ∅ countable_empty
    (fun i ↦ (continuousOn_cauchyFueterCutoffField hε (hc.mono sdiff_subset) i).comp
      dq.continuous.continuousOn (fun _ hx ↦ mem_image_of_mem _ hx))
    (fun u hu i ↦ (differentiableAt_cauchyFueterCutoffField hε
      (fun hp ↦ (hf u hu.1 hp).differentiableAt) i).hasFDerivAt.comp _ dq.hasFDerivAt)
    (hip.congr hae.symm)
  rw [integral_congr_ae hae] at h
  rw [L.integral_image_affine p _ (Icc 0 1) volume, abs_of_pos hL, integral_smul]
  simpa only [boxBoundarySum_zero_one] using h.symm

/-- The cut-off affine boundary flux tends to `2π²` times the coefficient at an
interior pole. Regularity at the pole itself is unnecessary. -/
theorem tendsto_affineFlux_cauchyFueterCutoffField
    (hL : 0 < LinearMap.det (L : (Fin 4 → ℝ) →ₗ[ℝ] Fin 4 → ℝ))
    (hc : ContinuousOn f (dq '' ((fun u ↦ p + L u) '' Icc 0 1)))
    (hf : ∀ u ∈ pi univ (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1),
      dq (p + L u) ≠ dq x₀ → LeftFueterAt f (dq (p + L u)))
    (hx₀ : L.symm (x₀ - p) ∈ pi univ (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1)) :
    Tendsto (fun ε : ℝ ↦ boxBoundarySum 0 1 (L.affineFluxPullback p
      (fun i x ↦ cauchyFueterCutoffField ε (dq x₀) f i (dq x))))
      (𝓝[>] 0) (𝓝 ((2 * Real.pi ^ 2) • f (dq x₀))) := by
  let A := L.toHomeomorph.trans (Homeomorph.addLeft p)
  have hu : Icc (0 : Fin 4 → ℝ) 1 ∈ 𝓝 (L.symm (x₀ - p)) :=
    pi_Icc_mem_nhds (fun i ↦ (mem_pi.mp hx₀ i (mem_univ i)).1)
      (fun i ↦ (mem_pi.mp hx₀ i (mem_univ i)).2)
  have hA : ⇑A = (fun u ↦ p + L u) := rfl
  have hs : (fun u ↦ p + L u) '' Icc 0 1 ∈ 𝓝 x₀ := by
    simpa only [hA, L.apply_symm_apply, add_sub_cancel] using A.isOpenMap.image_mem_nhds hu
  have hcomp := hc.comp dq.continuous.continuousOn (fun _ hx ↦ mem_image_of_mem _ hx)
  have hcompact : IsCompact ((fun u ↦ p + L u) '' Icc 0 1) :=
    isCompact_Icc.image (continuous_const.add L.continuous)
  have h := tendsto_setIntegral_cauchyFueterCutoff_density hcompact.measurableSet hs
    (hcomp.integrableOn_compact hcompact) (hcomp _ (mem_of_mem_nhds hs))
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (affineFlux_cauchyFueterCutoffField hε hL hc hf).symm

/-- Sufficiently small radial cutoffs do not change the affine boundary flux of an
interior pole. This holds without any continuity or regularity assumption on `f`. -/
theorem eventually_affineFlux_cauchyFueterCutoffField (f : ℍ → ℍ)
    (hx₀ : L.symm (x₀ - p) ∈ pi univ (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1)) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      boxBoundarySum 0 1 (L.affineFluxPullback p
        (fun i x ↦ cauchyFueterCutoffField ε (dq x₀) f i (dq x))) =
      boxBoundarySum 0 1 (L.affineFluxPullback p
        (fun i x ↦ cauchyFueterKernel (dq x) (dq x₀) * dq (Pi.single i 1) * f (dq x))) := by
  let e := (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1)).symm.toContinuousLinearEquiv
  let A := L.toHomeomorph.trans (Homeomorph.addLeft p)
  let U := pi univ (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1)
  have he (x : Fin 4 → ℝ) : dq x = e x := congrFun coe_dq x
  have hU : IsOpen U := isOpen_set_pi finite_univ fun _ _ ↦ isOpen_Ioo
  have hpole : x₀ ∈ A '' U :=
    ⟨L.symm (x₀ - p), hx₀, by simp [A]⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (e.isOpenMap _ (A.isOpenMap _ hU))
    (e x₀) (mem_image_of_mem e hpole)
  -- Every affine face lies outside an open ball about the pole, even on its extended plane.
  have hdist (j : Fin 4) (c : ℝ) (hc : c = 0 ∨ c = 1) (x : Fin 3 → ℝ) :
      δ ≤ ‖dq (p + L (j.insertNth c x)) - dq x₀‖ := by
    by_contra hn
    obtain ⟨y, hy, hyq⟩ := hball
      (by simpa only [Metric.mem_ball, dist_eq_norm, he] using lt_of_not_ge hn)
    have hy' : y = p + L (j.insertNth c x) := e.injective hyq
    obtain ⟨v, hv, hvq⟩ := hy
    have hv' : v = j.insertNth c x := A.injective (by simpa [A, hy'] using hvq)
    have hj := mem_pi.mp hv j (mem_univ j)
    rw [hv', Fin.insertNth_apply_same] at hj
    rcases hc with rfl | rfl
    · exact lt_irrefl _ hj.1
    · exact lt_irrefl _ hj.2
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with ε hε hεδ
  have heq (j : Fin 4) (c : ℝ) (hc : c = 0 ∨ c = 1) (x : Fin 3 → ℝ) :
      L.affineFluxPullback p
          (fun i y ↦ cauchyFueterCutoffField ε (dq x₀) f i (dq y)) j (j.insertNth c x) =
        L.affineFluxPullback p (fun i y ↦
          cauchyFueterKernel (dq y) (dq x₀) * dq (Pi.single i 1) * f (dq y)) j
          (j.insertNth c x) := by
    simp only [ContinuousLinearEquiv.affineFluxPullback_apply,
      cauchyFueterCutoffField_of_le hε (hεδ.le.trans (hdist j c hc x))]
  simp only [boxBoundarySum_zero_one, heq _ 1 (Or.inr rfl), heq _ 0 (Or.inl rfl)]

/-- The left Cauchy–Fueter representation in positive affine cofactor coordinates.
The pole lies in the open parameter cube; the three factors retain the order `G * eᵢ * f`. -/
theorem left_cauchyFueter_affine_cofactor
    (hL : 0 < LinearMap.det (L : (Fin 4 → ℝ) →ₗ[ℝ] Fin 4 → ℝ))
    (hc : ContinuousOn f (dq '' ((fun u ↦ p + L u) '' Icc 0 1)))
    (hf : ∀ u ∈ pi univ (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1),
      dq (p + L u) ≠ dq x₀ → LeftFueterAt f (dq (p + L u)))
    (hx₀ : L.symm (x₀ - p) ∈ pi univ (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1)) :
    f (dq x₀) = (1 / (2 * Real.pi ^ 2)) • boxBoundarySum 0 1
      (L.affineFluxPullback p (fun i x ↦
        cauchyFueterKernel (dq x) (dq x₀) * dq (Pi.single i 1) * f (dq x))) := by
  have h := tendsto_affineFlux_cauchyFueterCutoffField hL hc hf hx₀
  have heq := tendsto_nhds_unique
    (h.congr' (eventually_affineFlux_cauchyFueterCutoffField f hx₀)) tendsto_const_nhds
  have hm : (2 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
  rw [← heq, smul_smul, one_div, inv_mul_cancel₀ hm, one_smul]

/-- The left Cauchy–Fueter formula as the actual affine face integral of `G * Dq * f`,
with outward orientation and normalization `1 / (2π²)`. -/
theorem left_cauchyFueter_affine
    (hL : 0 < LinearMap.det (L : (Fin 4 → ℝ) →ₗ[ℝ] Fin 4 → ℝ))
    (hc : ContinuousOn f (dq '' ((fun u ↦ p + L u) '' Icc 0 1)))
    (hf : ∀ u ∈ pi univ (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1),
      dq (p + L u) ≠ dq x₀ → LeftFueterAt f (dq (p + L u)))
    (hx₀ : L.symm (x₀ - p) ∈ pi univ (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1)) :
    f (dq x₀) = (1 / (2 * Real.pi ^ 2)) •
      ContinuousLinearMap.rawAffineBoundary L.toContinuousLinearMap p
        (fun x ↦ ContinuousLinearMap.mulLeftRight ℝ ℍ
          (cauchyFueterKernel (dq x) (dq x₀)) (f (dq x))) := by
  rw [L.rawAffineBoundary_eq_cofactor, ← boxBoundarySum_zero_one]
  simpa only [ContinuousLinearMap.mulLeftRight_apply] using
    left_cauchyFueter_affine_cofactor hL hc hf hx₀

end TauCeti
