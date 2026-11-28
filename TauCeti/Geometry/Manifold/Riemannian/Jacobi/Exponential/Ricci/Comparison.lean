/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Exponential.Ricci.Basic
public import TauCeti.Analysis.ODE.Jacobi.Comparison
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Upper comparison for exponential density under a Ricci lower bound

On a normal ray, the lower radial Ricci bound gives an upper bound for the actual norm
determinant of the exponential differential. The Jacobi operators and their transverse space
are constructed from the Riemannian exponential map and radial parallel transport.
In dimension at least two, a positive radial Ricci bound with parameter `κ` bounds
normal-domain vector lengths and the radii of balls in that domain by the first model zero
`π / √κ`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 11.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public noncomputable section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff InnerProductSpace Manifold Topology

namespace TauCeti.Manifold.IsNormalDomain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {p : M} {U : Set (TangentSpace I p)}

/-- A lower bound on the actual radial Ricci tensor gives upper comparison for the actual
exponential density. The curvature parameter is measured in the given ray parameter. -/
private theorem normDet_mfderiv_riemannianExp_smul_le_of_ricci_of_ne_zero
    (h : IsNormalDomain I M p U)
    {v : TangentSpace I p} (hv : v ≠ 0) {r κ : ℝ}
    (hseg : ∀ s ∈ Icc 0 r, s • v ∈ U)
    (hRic : ∀ s ∈ Ioo 0 r,
      ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * κ ≤
        (leviCivitaConnection I M).ricciTensor (riemannianExp I M p (s • v))
          (curveVelocity I (fun t : ℝ ↦ riemannianExp I M p (t • v)) s)
          (curveVelocity I (fun t : ℝ ↦ riemannianExp I M p (t • v)) s))
    {t : ℝ} (ht : t ∈ Ioc 0 r) :
    LinearMap.normDet (U := TangentSpace I p)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v)).toLinearMap ≤
      (curvatureSine κ t / t) ^ (Module.finrank ℝ E - 1) := by
  have hr : 0 < r := ht.1.trans_le ht.2
  let b := stdOrthonormalBasis ℝ (TangentSpace I p)
  let W := (ℝ ∙ v)ᗮ
  let J := fun s ↦ (h.radialJacobiPosition b v hr.le hseg s).compression W.subtypeL
  let V := fun s ↦ (h.radialJacobiVelocity b v hr.le hseg s).compression W.subtypeL
  let K := fun s ↦ (h.radialJacobiCurvature b v hr.le hseg s).compression W.subtypeL
  have h0 : 0 ∈ Icc 0 r := ⟨le_rfl, hr.le⟩
  have hdim : Module.finrank ℝ W = Module.finrank ℝ E - 1 :=
    (Submodule.finrank_orthogonal_span_singleton_eq_finrank_sub_one hv).trans
      (by rw [finrank_tangentSpace])
  have hvel : V 0 = ContinuousLinearMap.id ℝ W := by
    dsimp only [V]
    rw [h.radialJacobiVelocity_zero]
    simpa only [ContinuousLinearMap.one_def, Submodule.subtypeₗᵢ_toContinuousLinearMap] using
      ContinuousLinearMap.compression_one W.subtypeₗᵢ
  have hcomp := TauCeti.normDet_le_curvatureSine_pow_of_jacobi
    (J := J) (V := V) (K := K)
    (fun s hs ↦
      (h.hasDerivAt_compression_radialJacobiPosition b v hr.le hseg hs).hasDerivWithinAt)
    (fun s hs ↦
      let hd := h.hasDerivAt_compression_radialJacobiVelocity b v hr hseg h0 hs
      hd.continuousAt.continuousWithinAt)
    (fun s hs ↦
      (h.hasDerivAt_compression_radialJacobiVelocity b v hr hseg h0
        (Ioo_subset_Icc_self hs)).hasDerivWithinAt)
    (fun s hs ↦ ContinuousLinearMap.isSymmetric_compression W.subtypeL
      (h.isSymmetric_radialJacobiCurvature b v hr hseg h0 (Ioo_subset_Icc_self hs)))
    (by simp only [J, h.radialJacobiPosition_zero, ContinuousLinearMap.compression_zero]) hvel
    (fun s hs ↦ h.isInvertible_compression_radialJacobiPosition b v hr hseg
      ⟨hs.1, hs.2.le⟩)
    (fun s hs ↦ by
      dsimp only [K]
      rw [h.trace_compression_radialJacobiCurvature b v hr hseg h0
        (Ioo_subset_Icc_self hs), hdim]
      exact hRic s hs)
    ⟨ht.1.le, ht.2⟩
  dsimp only [J] at hcomp
  rw [h.normDet_compression_radialJacobiPosition b v hr hseg ht, hdim] at hcomp
  rw [div_pow]
  exact (le_div_iff₀ (pow_pos ht.1 _)).mpr (by simpa only [mul_comm] using hcomp)

/-- A lower radial Ricci bound gives upper comparison for the exponential density, including
constant rays and manifolds of dimension at most one. -/
theorem normDet_mfderiv_riemannianExp_smul_le_of_ricci
    (h : IsNormalDomain I M p U) (v : TangentSpace I p) {r κ : ℝ}
    (hseg : ∀ s ∈ Icc 0 r, s • v ∈ U)
    (hRic : ∀ s ∈ Ioo 0 r,
      ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * κ ≤
        (leviCivitaConnection I M).ricciTensor (riemannianExp I M p (s • v))
          (curveVelocity I (fun t : ℝ ↦ riemannianExp I M p (t • v)) s)
          (curveVelocity I (fun t : ℝ ↦ riemannianExp I M p (t • v)) s))
    {t : ℝ} (ht : t ∈ Ioc 0 r) :
    LinearMap.normDet (U := TangentSpace I p)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v)).toLinearMap ≤
      (curvatureSine κ t / t) ^ (Module.finrank ℝ E - 1) := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [smul_zero, normDet_mfderiv_riemannianExp_zero]
    by_cases hn : Module.finrank ℝ E ≤ 1
    · simp only [Nat.sub_eq_zero_of_le hn, pow_zero, le_refl]
    have hr : 0 < r := ht.1.trans_le ht.2
    have hRic0 := hRic (r / 2) ⟨by linarith, by linarith⟩
    have hRic0' : ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * κ ≤ 0 := by
      rw [curveVelocity_riemannianExp_smul
        (h.subset_expDomain (hseg (r / 2) ⟨by linarith, by linarith⟩))] at hRic0
      let L : TangentSpace I p →L[ℝ] TangentSpace I
          (riemannianExp I M p ((r / 2) • 0)) :=
        mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) ((r / 2) • 0)
      -- Identify the tangent domain of the vector space with the initial tangent space.
      change ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * κ ≤
        (leviCivitaConnection I M).ricciTensor _ (L 0) (L 0) at hRic0
      simpa only [map_zero, LinearMap.zero_apply] using hRic0
    have hκ : κ ≤ 0 := nonpos_of_mul_nonpos_right hRic0'
      (by exact_mod_cast Nat.sub_pos_of_lt (Nat.lt_of_not_ge hn) :
        (0 : ℝ) < ((Module.finrank ℝ E - 1 : ℕ) : ℝ))
    have hs : t ≤ curvatureSine κ t := by
      simpa only [curvatureSine_zero_left] using
        curvatureSine_le_curvatureSine_of_ge (κ := 0) hκ ht.1.le (by simp)
    exact one_le_pow₀ ((le_div_iff₀ ht.1).mpr (by simpa only [one_mul] using hs))
  exact h.normDet_mfderiv_riemannianExp_smul_le_of_ricci_of_ne_zero hv hseg hRic ht

/-- In dimension at least two, a positive radial Ricci lower bound forces every vector in a
normal domain to lie within the first model conjugate radius. -/
theorem norm_le_pi_div_sqrt_of_ricci
    (h : IsNormalDomain I M p U) (hdim : 1 < Module.finrank ℝ E)
    {v : TangentSpace I p} (hv : v ∈ U) {κ : ℝ} (hκ : 0 < κ)
    (hRic : ∀ t ∈ Ioo (0 : ℝ) 1,
      ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * κ * ‖v‖ ^ 2 ≤
        (leviCivitaConnection I M).ricciTensor (riemannianExp I M p (t • v))
          (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) v)
          (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) v)) :
    ‖v‖ ≤ Real.pi / Real.sqrt κ := by
  rcases eq_or_ne v 0 with rfl | hv0
  · simpa only [norm_zero] using (div_pos Real.pi_pos (Real.sqrt_pos.mpr hκ)).le
  have hnorm := norm_pos_iff.mpr hv0
  have hseg (t : ℝ) (ht : t ∈ Icc 0 1) : t • v ∈ U := h.smul_mem hv ht.1 ht.2
  let c := Real.pi / Real.sqrt (κ * ‖v‖ ^ 2)
  have hk : 0 < κ * ‖v‖ ^ 2 := mul_pos hκ (sq_pos_of_pos hnorm)
  have hc : 0 < c := div_pos Real.pi_pos (Real.sqrt_pos.mpr hk)
  have hsqrt : Real.sqrt (κ * ‖v‖ ^ 2) = Real.sqrt κ * ‖v‖ := by
    rw [Real.sqrt_mul hκ.le, Real.sqrt_sq hnorm.le]
  by_contra! hlarge
  have hc1 : c < 1 := by
    dsimp only [c]
    rw [div_lt_one (Real.sqrt_pos.mpr hk), hsqrt]
    simpa only [mul_comm] using (div_lt_iff₀ (Real.sqrt_pos.mpr hκ)).mp hlarge
  have hcI : c ∈ Ioc (0 : ℝ) 1 := ⟨hc, hc1.le⟩
  have hdensity := h.normDet_mfderiv_riemannianExp_smul_le_of_ricci v hseg
    (κ := κ * ‖v‖ ^ 2)
    (fun s hs ↦ by
      rw [curveVelocity_riemannianExp_smul (h.subset_expDomain (hseg s
        (Ioo_subset_Icc_self hs)))]
      simpa only [mul_assoc] using hRic s hs)
    hcI
  have hzero : curvatureSine (κ * ‖v‖ ^ 2) c = 0 := curvatureSine_pi_div_sqrt _
  rw [hzero, zero_div, zero_pow (by omega : Module.finrank ℝ E - 1 ≠ 0)] at hdensity
  have hne : 0 < LinearMap.normDet (U := TangentSpace I p)
      (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (c • v)).toLinearMap := by
    apply ContinuousLinearMap.IsInvertible.normDet_pos
    exact (h.isLocalDiffeomorphOn ⟨c • v, hseg c ⟨hc.le, hc1.le⟩⟩).isInvertible_mfderiv
      (by simp)
  exact (not_le_of_gt hne) hdensity

/-- In dimension at least two, a ball contained in a normal domain under a positive radial
Ricci lower bound cannot extend beyond the first model conjugate radius. -/
theorem le_pi_div_sqrt_of_ball_of_ricci
    (h : IsNormalDomain I M p U) (hdim : 1 < Module.finrank ℝ E) {r κ : ℝ}
    (hsub : Metric.ball (0 : TangentSpace I p) r ⊆ U)
    (hRic : ∀ v ∈ Metric.ball (0 : TangentSpace I p) r, ∀ t ∈ Ioo (0 : ℝ) 1,
      ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * κ * ‖v‖ ^ 2 ≤
        (leviCivitaConnection I M).ricciTensor (riemannianExp I M p (t • v))
          (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) v)
          (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) v))
    (hκ : 0 < κ) : r ≤ Real.pi / Real.sqrt κ := by
  by_contra! hlarge
  obtain ⟨ρ, hρc, hρr⟩ := exists_between hlarge
  have hρ : 0 < ρ := (div_pos Real.pi_pos (Real.sqrt_pos.mpr hκ)).trans hρc
  have : Nontrivial (TangentSpace I p) := Module.nontrivial_of_finrank_pos
    ((finrank_tangentSpace (I := I) p).symm ▸ (zero_lt_one.trans hdim))
  obtain ⟨v, hv⟩ := exists_norm_eq (TangentSpace I p) hρ.le
  have hball : v ∈ Metric.ball (0 : TangentSpace I p) r := by
    rwa [mem_ball_zero_iff, hv]
  have hcap := h.norm_le_pi_div_sqrt_of_ricci hdim (hsub hball) hκ (hRic v hball)
  exact (not_le_of_gt hρc) (hv ▸ hcap)

/-- **Exponential density upper comparison under a Ricci lower bound.** Along the radial
geodesic ending at `v`, assume `Ric(γ',γ') ≥ (n - 1) κ ‖v‖²`. Its actual exponential density
is at most the constant-curvature model density. -/
theorem normDet_mfderiv_riemannianExp_le_curvatureSine_pow
    (h : IsNormalDomain I M p U) {v : TangentSpace I p} (hv : v ∈ U) {κ : ℝ}
    (hRic : ∀ t ∈ Ioo (0 : ℝ) 1,
      ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * κ * ‖v‖ ^ 2 ≤
        (leviCivitaConnection I M).ricciTensor (riemannianExp I M p (t • v))
          (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) v)
          (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) v)) :
    LinearMap.normDet (U := TangentSpace I p)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v).toLinearMap ≤
      curvatureSine (κ * ‖v‖ ^ 2) 1 ^ (Module.finrank ℝ E - 1) := by
  have hseg (t : ℝ) (ht : t ∈ Icc 0 1) : t • v ∈ U := h.smul_mem hv ht.1 ht.2
  have hcomp := h.normDet_mfderiv_riemannianExp_smul_le_of_ricci
    v hseg
    (κ := κ * ‖v‖ ^ 2)
    (fun t ht ↦ by
      rw [curveVelocity_riemannianExp_smul (h.subset_expDomain (hseg t
        (Ioo_subset_Icc_self ht)))]
      simpa only [mul_assoc] using hRic t ht)
    (right_mem_Ioc.mpr zero_lt_one)
  convert hcomp using 1
  · rw [one_smul]
  · rw [div_one]

end TauCeti.Manifold.IsNormalDomain
