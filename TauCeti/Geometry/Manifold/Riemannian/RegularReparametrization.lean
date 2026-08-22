/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon (claude+codex), Axel Delaval, Chunlei Liu,
  Jinxuan Chen, Wanxu Yang, Zekun Sheng, Yuxuan Liao, Jie Xu
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# Regular C¹ curves admit unit-speed reparametrizations

This file expresses the speed of a curve using the norm of Mathlib's manifold
derivative and proves the regular-reparametrization target in Layer 0 of the
Hopf--Rinow roadmap. A globally C¹ curve whose speed is nowhere zero on a
nondegenerate compact interval has a C¹ arclength inverse. The resulting
curve preserves endpoints and total Manifold.pathELength, and its length on
every parameter subinterval [s, t] is exactly t - s.

No separate length functional is introduced: the auxiliary integral of speed
is identified with Manifold.pathELength and the final statements use that
canonical API.

## Provenance

Adapted from
formalized-sources/Petersen/PetersenLib/Ch05/ArclengthReparametrization.lean
in the Poincare-Conjecture development at revision
e6bc8cb66a83e50afa2b4507db664c9370bd4ac4. The source proves a smooth
version using its private squared-speed and curve-length API. This file lowers
the curve hypothesis to the roadmap's required C¹ regularity and uses
Mathlib's Riemannian bundle and pathELength APIs directly.
-/

public section

namespace Manifold

open Bundle Filter Manifold Set
open scoped Bundle ContDiff Manifold Topology

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- The pointwise Riemannian speed of a real-parameterized curve, measured by
the norm on the tangent bundle. -/
def riemannianSpeed (gamma : ℝ → M) (t : ℝ) : ℝ :=
  ‖mfderiv 𝓘(ℝ, ℝ) I gamma t 1‖

/-- The Riemannian speed of a globally `C¹` curve is continuous. -/
theorem continuous_riemannianSpeed {gamma : ℝ → M}
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) I 1 gamma) :
    Continuous (riemannianSpeed (I := I) gamma) := by
  have hv : Continuous (fun t : ℝ ↦
      tangentMap 𝓘(ℝ, ℝ) I gamma
        ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm (t, 1))) :=
    (hgamma.continuous_tangentMap (by norm_num)).comp
      ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
        (continuous_id.prodMk continuous_const))
  have hinner : Continuous (fun t : ℝ ↦
      @inner ℝ (TangentSpace I (gamma t)) _
        (mfderiv 𝓘(ℝ, ℝ) I gamma t 1)
        (mfderiv 𝓘(ℝ, ℝ) I gamma t 1)) := by
    exact hv.inner_bundle hv
  change Continuous (fun t ↦ √(inner ℝ
    (mfderiv 𝓘(ℝ, ℝ) I gamma t 1) (mfderiv 𝓘(ℝ, ℝ) I gamma t 1)))
  exact hinner.sqrt

/-- On an ordered interval, Mathlib's `pathELength` is the extended-real
image of the integral of Riemannian speed. -/
theorem pathELength_eq_ofReal_integral_riemannianSpeed {gamma : ℝ → M} {a b : ℝ}
    (hab : a ≤ b)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) I 1 gamma) :
    pathELength I gamma a b =
      ENNReal.ofReal (∫ t in a..b, riemannianSpeed (I := I) gamma t) := by
  have hc := continuous_riemannianSpeed (I := I) hgamma
  have hint : MeasureTheory.IntegrableOn (riemannianSpeed (I := I) gamma) (Icc a b) :=
    hc.continuousOn.integrableOn_Icc
  rw [pathELength_eq_lintegral_mfderiv_Icc]
  have heq : (fun t ↦ ‖mfderiv 𝓘(ℝ, ℝ) I gamma t 1‖ₑ) =
      fun t ↦ ENNReal.ofReal (riemannianSpeed (I := I) gamma t) := by
    funext t
    simp [riemannianSpeed, enorm]
  rw [heq, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint]
  · rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hab]
  · exact Filter.Eventually.of_forall fun t ↦ norm_nonneg _

/-- A regular `C¹` curve admits a `C¹` unit-speed reparametrization by its
accumulated Riemannian length. The inverse maps the full arclength interval
back to `[a, b]`; the reparametrized curve has length `t - s` on every
subinterval and exactly preserves the original total `pathELength`. -/
theorem exists_unitSpeed_reparametrization_of_regular {gamma : ℝ → M}
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) I 1 gamma)
    {a b : ℝ} (hab : a < b)
    (hreg : ∀ t ∈ Icc a b, riemannianSpeed (I := I) gamma t ≠ 0) :
    ∃ psi : ℝ → ℝ,
      let L := ∫ t in a..b, riemannianSpeed (I := I) gamma t
      0 < L ∧
      (∀ t ∈ Icc a b,
        psi (∫ s in a..t, riemannianSpeed (I := I) gamma s) = t) ∧
      MapsTo psi (Icc 0 L) (Icc a b) ∧
      ContDiffOn ℝ 1 psi (Icc 0 L) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 (gamma ∘ psi) (Icc 0 L) ∧
      (gamma ∘ psi) 0 = gamma a ∧
      (gamma ∘ psi) L = gamma b ∧
      (∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, s ≤ t →
        pathELength I (gamma ∘ psi) s t = ENNReal.ofReal (t - s)) ∧
      pathELength I (gamma ∘ psi) 0 L = pathELength I gamma a b := by
  have hspeed_cont := continuous_riemannianSpeed (I := I) hgamma
  have hVopen : IsOpen {t | riemannianSpeed (I := I) gamma t ≠ 0} := by
    change IsOpen ((riemannianSpeed (I := I) gamma) ⁻¹' ({0}ᶜ))
    exact isOpen_compl_singleton.preimage hspeed_cont
  have haV : a ∈ {t | riemannianSpeed (I := I) gamma t ≠ 0} :=
    hreg a (left_mem_Icc.mpr hab.le)
  have hbV : b ∈ {t | riemannianSpeed (I := I) gamma t ≠ 0} :=
    hreg b (right_mem_Icc.mpr hab.le)
  obtain ⟨epsa, hepsa, hballa⟩ := Metric.isOpen_iff.mp hVopen a haV
  obtain ⟨epsb, hepsb, hballb⟩ := Metric.isOpen_iff.mp hVopen b hbV
  set delta : ℝ := min epsa epsb / 2 with hdelta_def
  have hdelta_pos : 0 < delta := by
    rw [hdelta_def]
    positivity
  set J : Set ℝ := Ioo (a - delta) (b + delta) with hJ_def
  have hJ_open : IsOpen J := isOpen_Ioo
  have hJ_sub : J ⊆ {t | riemannianSpeed (I := I) gamma t ≠ 0} := by
    intro t ht
    have hdelta_ea : delta ≤ epsa := by
      rw [hdelta_def]
      exact (half_le_self (lt_min hepsa hepsb).le).trans (min_le_left _ _)
    have hdelta_eb : delta ≤ epsb := by
      rw [hdelta_def]
      exact (half_le_self (lt_min hepsa hepsb).le).trans (min_le_right _ _)
    rcases lt_or_ge t a with hta | hta
    · apply hballa
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith [ht.1]
    rcases le_or_gt t b with htb | htb
    · exact hreg t ⟨hta, htb⟩
    · apply hballb
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith [ht.2]
  have hIccJ : Icc a b ⊆ J := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have haJ : a ∈ J := hIccJ (left_mem_Icc.mpr hab.le)
  have hbJ : b ∈ J := hIccJ (right_mem_Icc.mpr hab.le)
  have hJ_ord : ∀ s ∈ J, ∀ t ∈ J, Icc s t ⊆ J := by
    intro s hs t ht r hr
    exact ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  have hspeed_pos : ∀ t ∈ J, 0 < riemannianSpeed (I := I) gamma t := by
    intro t ht
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm (hJ_sub ht))
  set phi : ℝ → ℝ := fun t ↦ ∫ s in a..t, riemannianSpeed (I := I) gamma s with hphi_def
  have hphi_deriv : ∀ t, HasDerivAt phi (riemannianSpeed (I := I) gamma t) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_right
      (hspeed_cont.intervalIntegrable a t)
      (hspeed_cont.stronglyMeasurableAtFilter MeasureTheory.volume (𝓝 t))
      hspeed_cont.continuousAt
  have hphi_add : ∀ s t, phi t = phi s +
      ∫ r in s..t, riemannianSpeed (I := I) gamma r := by
    intro s t
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hspeed_cont.intervalIntegrable a s) (hspeed_cont.intervalIntegrable s t)
    simpa [phi] using hadd.symm
  have hphi_mono : StrictMonoOn phi J := by
    intro s hs t ht hst
    have hpos : 0 < ∫ r in s..t, riemannianSpeed (I := I) gamma r :=
      intervalIntegral.intervalIntegral_pos_of_pos_on
        (hspeed_cont.intervalIntegrable s t)
        (fun r hr ↦ hspeed_pos r (hJ_ord s hs t ht (Ioo_subset_Icc_self hr))) hst
    rw [hphi_add s t]
    linarith
  have hphi_C1 : ContDiff ℝ 1 phi := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun t ↦ (hphi_deriv t).differentiableAt, ?_⟩
    convert hspeed_cont using 1
    funext t
    exact (hphi_deriv t).deriv
  have hphi_inj : InjOn phi J := hphi_mono.injOn
  set psi : ℝ → ℝ := Function.invFunOn phi J with hpsi_def
  have hleft : ∀ t ∈ J, psi (phi t) = t := fun t ht ↦
    hphi_inj.leftInvOn_invFunOn ht
  set W : Set ℝ := phi '' J with hW_def
  have hpsi_deriv_local : ∀ t ∈ J,
      HasDerivAt psi (riemannianSpeed (I := I) gamma t)⁻¹ (phi t) ∧ W ∈ 𝓝 (phi t) := by
    intro t ht
    have hne : riemannianSpeed (I := I) gamma t ≠ 0 := (hspeed_pos t ht).ne'
    have hstrict : HasStrictDerivAt phi (riemannianSpeed (I := I) gamma t) t := by
      have h := (hphi_C1.contDiffAt (x := t)).hasStrictDerivAt (by norm_num)
      rwa [(hphi_deriv t).deriv] at h
    set zeta : ℝ → ℝ := hstrict.localInverse phi _ t hne with hzeta_def
    have hzeta_strict : HasStrictDerivAt zeta
        (riemannianSpeed (I := I) gamma t)⁻¹ (phi t) :=
      hstrict.to_localInverse hne
    have hzeta_cont : ContinuousAt zeta (phi t) := hzeta_strict.hasDerivAt.continuousAt
    have hzeta_t : zeta (phi t) = t :=
      (hstrict.eventually_left_inverse hne).self_of_nhds
    have hzeta_mem : ∀ᶠ s in 𝓝 (phi t), zeta s ∈ J := by
      apply hzeta_cont.eventually_mem
      simpa [hzeta_t] using hJ_open.mem_nhds ht
    have heq : psi =ᶠ[𝓝 (phi t)] zeta := by
      filter_upwards [hstrict.eventually_right_inverse hne, hzeta_mem]
        with s hrs hsJ
      have hex : ∃ u ∈ J, phi u = s := ⟨zeta s, hsJ, hrs⟩
      have h1 : phi (Function.invFunOn phi J s) = s := Function.invFunOn_eq hex
      have h2 : Function.invFunOn phi J s ∈ J := Function.invFunOn_mem hex
      exact hphi_inj h2 hsJ (h1.trans hrs.symm)
    refine ⟨hzeta_strict.hasDerivAt.congr_of_eventuallyEq heq, ?_⟩
    have hmap := hstrict.map_nhds_eq hne
    rw [← hmap]
    exact mem_map.mpr (mem_of_superset (hJ_open.mem_nhds ht)
      (subset_preimage_image phi J))
  have hW_open : IsOpen W := by
    rw [isOpen_iff_mem_nhds]
    rintro s ⟨t, ht, rfl⟩
    exact (hpsi_deriv_local t ht).2
  have hpsi_mem : ∀ s ∈ W, psi s ∈ J := by
    rintro s ⟨t, ht, rfl⟩
    rw [hleft t ht]
    exact ht
  have hpsi_hasDeriv : ∀ s ∈ W,
      HasDerivAt psi (riemannianSpeed (I := I) gamma (psi s))⁻¹ s := by
    rintro s ⟨t, ht, rfl⟩
    rw [hleft t ht]
    exact (hpsi_deriv_local t ht).1
  have hpsi_diff : DifferentiableOn ℝ psi W := fun s hs ↦
    (hpsi_hasDeriv s hs).differentiableAt.differentiableWithinAt
  have hpsi_cont : ContinuousOn psi W := fun s hs ↦
    (hpsi_hasDeriv s hs).continuousAt.continuousWithinAt
  have hpsi_deriv_eq : EqOn (deriv psi)
      (fun s ↦ (riemannianSpeed (I := I) gamma (psi s))⁻¹) W :=
    fun s hs ↦ (hpsi_hasDeriv s hs).deriv
  have hpsi_C1 : ContDiffOn ℝ 1 psi W := by
    rw [contDiffOn_one_iff_derivWithin hW_open.uniqueDiffOn]
    refine ⟨hpsi_diff, ?_⟩
    have hc : ContinuousOn (fun s ↦ (riemannianSpeed (I := I) gamma (psi s))⁻¹) W :=
      (hspeed_cont.comp_continuousOn hpsi_cont).inv₀ fun s hs ↦
        (hspeed_pos (psi s) (hpsi_mem s hs)).ne'
    refine hc.congr fun s hs ↦ ?_
    rw [derivWithin_of_isOpen hW_open hs, hpsi_deriv_eq hs]
  have hphi_a : phi a = 0 := by simp [phi]
  set L : ℝ := ∫ t in a..b, riemannianSpeed (I := I) gamma t with hL_def
  have hphi_b : phi b = L := rfl
  have hL_pos : 0 < L := by
    exact intervalIntegral.intervalIntegral_pos_of_pos_on
      (hspeed_cont.intervalIntegrable a b)
      (fun t ht ↦ hspeed_pos t (hIccJ (Ioo_subset_Icc_self ht))) hab
  have himage : phi '' Icc a b = Icc 0 L := by
    rw [hphi_C1.continuous.continuousOn.image_Icc_of_monotoneOn hab.le
      (hphi_mono.monotoneOn.mono hIccJ), hphi_a, hphi_b]
  have hIccW : Icc 0 L ⊆ W := by
    rw [← himage]
    exact image_mono hIccJ
  have hmaps : MapsTo psi (Icc 0 L) (Icc a b) := by
    intro s hs
    rw [← himage] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    rw [hleft t (hIccJ ht)]
    exact ht
  have hpsi_C1_Icc : ContDiffOn ℝ 1 psi (Icc 0 L) := hpsi_C1.mono hIccW
  have hcomp_C1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (gamma ∘ psi) (Icc 0 L) := by
    intro s hs
    exact (hgamma.contMDiffAt.comp s
      ((hpsi_C1.contDiffAt (hW_open.mem_nhds (hIccW hs))).contMDiffAt)).contMDiffWithinAt
  have hpsi_mono : MonotoneOn psi (Icc 0 L) := by
    intro x hx y hy hxy
    rw [← himage] at hx hy
    obtain ⟨tx, htx, rfl⟩ := hx
    obtain ⟨ty, hty, rfl⟩ := hy
    rw [hleft tx (hIccJ htx), hleft ty (hIccJ hty)]
    by_contra hnot
    have hyx : ty < tx := lt_of_not_ge hnot
    exact (not_lt_of_ge hxy) (hphi_mono (hIccJ hty) (hIccJ htx) hyx)
  have hright : ∀ s ∈ W, phi (psi s) = s := by
    rintro s ⟨t, ht, rfl⟩
    rw [hleft t ht]
  have hunitLength : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, s ≤ t →
      pathELength I (gamma ∘ psi) s t = ENNReal.ofReal (t - s) := by
    intro s hs t ht hst
    have hpsi_st : psi s ≤ psi t := hpsi_mono hs ht hst
    have hcomp := pathELength_comp_of_monotoneOn (I := I) hst
      (hpsi_mono.mono (Icc_subset_Icc hs.1 ht.2))
      ((hpsi_C1_Icc.differentiableOn (by norm_num)).mono
        (Icc_subset_Icc hs.1 ht.2))
      ((hgamma.mdifferentiable (by norm_num)).mdifferentiableOn)
    rw [hcomp, pathELength_eq_ofReal_integral_riemannianSpeed hpsi_st hgamma]
    congr 1
    have hadd := hphi_add (psi s) (psi t)
    rw [hright s (hIccW hs), hright t (hIccW ht)] at hadd
    linarith
  refine ⟨psi, ?_⟩
  dsimp only
  refine ⟨hL_pos, ?_, hmaps, hpsi_C1_Icc, hcomp_C1, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact hleft t (hIccJ ht)
  · change gamma (psi 0) = gamma a
    rw [← hphi_a, hleft a haJ]
  · change gamma (psi L) = gamma b
    rw [← hphi_b, hleft b hbJ]
  · exact hunitLength
  · have hlen := pathELength_comp_of_monotoneOn (I := I) hL_pos.le hpsi_mono
      (hpsi_C1_Icc.differentiableOn (by norm_num))
      ((hgamma.mdifferentiable (by norm_num)).mdifferentiableOn)
    have hpsi_zero : psi 0 = a := by rw [← hphi_a, hleft a haJ]
    have hpsi_L : psi L = b := by rw [← hphi_b, hleft b hbJ]
    simpa only [hpsi_zero, hpsi_L] using hlen

end

end Manifold
