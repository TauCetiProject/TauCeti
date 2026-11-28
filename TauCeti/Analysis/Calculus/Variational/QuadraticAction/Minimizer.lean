/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Analysis.Calculus.Variational.QuadraticAction.FirstVariation
public import TauCeti.Analysis.Calculus.Variational.QuadraticAction.Force
public import TauCeti.Analysis.Sobolev.WeakDeriv.Interval.Momentum
public import TauCeti.Analysis.Calculus.ParametricFDeriv
public import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Smoothness of weak minimizers of positive quadratic actions

Minimality of the actual quadratic integral gives its first variation. Its weak momentum is
an integrable primitive; inversion of the positive kinetic form first gives a continuous
velocity. The smooth phase equation then bootstraps the same path, including its endpoint
jets within the closed interval.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Lemma 7.2.
* The reduced-action development in `frenzymath/lean-eval-submissions` and
  `frenzymath/PoincareConjecture`.
-/

public section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped intervalIntegral ContDiff

namespace TauCeti

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

-- Cache the canonical nested operator-space instances for the spatial kinetic derivative.
/-- The canonical normed additive structure on the operator coefficient space. -/
local instance quadraticMinimizerDualNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
/-- The canonical real normed-space structure on the operator coefficient space. -/
local instance quadraticMinimizerDualNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
/-- The canonical normed additive structure on the operator coefficient space. -/
local instance quadraticMinimizerBilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
/-- The canonical real normed-space structure on the operator coefficient space. -/
local instance quadraticMinimizerBilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
/-- The canonical normed additive structure on the operator coefficient space. -/
local instance quadraticMinimizerTrilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
/-- The canonical real normed-space structure on the operator coefficient space. -/
local instance quadraticMinimizerTrilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

variable {G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ} {V : ℝ × E → ℝ}
  {J : Set ℝ} {U : Set E} {u w : ℝ → E} {a b : ℝ}

omit [FiniteDimensional ℝ E] in
private theorem contDiffOn_spatialFDerivs {m n : ℕ∞ω}
    (hΩ : IsOpen (J ×ˢ U)) (hmn : m + 1 ≤ n)
    (hG : ContDiffOn ℝ n G (J ×ˢ U)) (hV : ContDiffOn ℝ n V (J ×ˢ U)) :
    ContDiffOn ℝ m (fun z ↦ spatialFDeriv (𝕜 := ℝ) G z.2 z.1) (J ×ˢ U) ∧
      ContDiffOn ℝ m (fun z ↦ spatialFDeriv (𝕜 := ℝ) V z.2 z.1) (J ×ˢ U) :=
  ⟨hG.spatialFDeriv_of_isOpen hΩ hmn, hV.spatialFDeriv_of_isOpen hΩ hmn⟩

/-- Minimality against all weak competitors gives a local minimum along an admissible
endpoint-fixed affine variation, before any coefficient regularity is used. -/
private theorem IsQuadraticActionMinimizerOn.isLocalMin_affine
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {G : ℝ × F → F →L[ℝ] F →L[ℝ] ℝ} {V : ℝ × F → ℝ}
    {U : Set F} {u w : ℝ → F} {a b δ : ℝ}
    (hmin : IsQuadraticActionMinimizerOn G V U u w a b)
    (η : ℝ → F) (hη : ContDiff ℝ 1 η) (hηa : η a = 0) (hηb : η b = 0)
    (hδ : 0 < δ)
    (hmem : ∀ ε ∈ Ioo (-δ) δ, MapsTo (fun s ↦ u s + ε • η s) (Icc a b) U) :
    IsLocalMin (fun ε : ℝ ↦ quadraticAction G V (fun s ↦ u s + ε • η s)
      (fun s ↦ w s + ε • deriv η s) a b) 0 := by
  have hν : Continuous (deriv η) := hη.continuous_deriv le_rfl
  filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hδ) hδ] with ε hε
  have hνLp : MemLp (deriv η) 2 (volume.restrict (Icc a b)) :=
    (hν.continuousOn.memLp_top_restrict_of_subset_isCompact isCompact_Icc
      measurableSet_Icc Subset.rfl).mono_exponent le_top
  have hvar := hmin.quadraticAction_le (z := fun s ↦ w s + ε • deriv η s)
    (hmin.memLp.add (hνLp.const_smul ε)) (hmem ε hε)
    (by simp [hηa]) (by simp [hηb]) ?_
  · simpa only [quadraticAction_def, zero_smul, add_zero] using hvar
  intro s hs
  have hsub' : uIcc a s ⊆ Icc a b := by
    rw [uIcc_of_le hs.1]
    exact Icc_subset_Icc_right hs.2
  have hwint : IntervalIntegrable w volume a s :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hmin.le).mpr
      (hmin.memLp.integrable (by norm_num))).mono_set (by rw [uIcc_of_le hmin.le]; exact hsub')
  have hνint : IntervalIntegrable (deriv η) volume a s := hν.intervalIntegrable _ _
  have hεν : IntervalIntegrable (fun r ↦ ε • deriv η r) volume a s := hνint.smul ε
  rw [intervalIntegral.integral_add hwint hεν,
    intervalIntegral.integral_smul,
    intervalIntegral.integral_deriv_eq_sub (fun r _ ↦ (hη.differentiable one_ne_zero) r)
      hνint, hmin.eq_add_integral hs]
  simp only [hηa, sub_zero, smul_zero, add_zero, add_assoc]

/-- An actual weak quadratic minimizer has zero affine first variation against every smooth
endpoint-vanishing vector field. No Euler equation is an input. -/
theorem IsQuadraticActionMinimizerOn.integral_firstVariation_eq_zero
    (hmin : IsQuadraticActionMinimizerOn G V U u w a b)
    (hJ : IsOpen J) (hU : IsOpen U) (htime : Icc a b ⊆ J)
    (hG : ContDiffOn ℝ 1 G (J ×ˢ U)) (hV : ContDiffOn ℝ 1 V (J ×ˢ U))
    (hsym : ∀ z ∈ J ×ˢ U, ∀ v v' : E, G z v v' = G z v' v)
    (η : ℝ → E) (hη : ContDiff ℝ 1 η) (hηa : η a = 0) (hηb : η b = 0) :
    (∫ s in a..b, spatialFDeriv (𝕜 := ℝ) G (u s) s (η s) (w s) (w s) / 2 +
      G (s, u s) (w s) (deriv η s) + spatialFDeriv (𝕜 := ℝ) V (u s) s (η s)) = 0 := by
  let DG := fun z : ℝ × E ↦ spatialFDeriv (𝕜 := ℝ) G z.2 z.1
  let DV := fun z : ℝ × E ↦ spatialFDeriv (𝕜 := ℝ) V z.2 z.1
  have hΩ : IsOpen (J ×ˢ U) := hJ.prod hU
  obtain ⟨hDG, hDV⟩ := contDiffOn_spatialFDerivs (m := 0) hΩ (by simp) hG hV
  obtain ⟨K, hK, hKU, δ, hδ, hδ1, hδK⟩ :=
    exists_affine_compact_buffer hU u η hmin.continuousOn hη.continuous.continuousOn hmin.mapsTo
  have hsub : Icc a b ×ˢ K ⊆ J ×ˢ U := fun z hz ↦ ⟨htime hz.1, hKU hz.2⟩
  have hcompact : IsCompact (Icc a b ×ˢ K) := isCompact_Icc.prod hK
  obtain ⟨C₀, hC₀⟩ := hcompact.exists_bound_of_continuousOn
    (((hG.continuousOn.mono hsub).prodMk (hDG.continuousOn.mono hsub)).prodMk
      (hDV.continuousOn.mono hsub))
  let C := |C₀|
  have hcoeff : ∀ s ∈ Icc a b, ∀ x ∈ K,
      ‖G (s, x)‖ ≤ C ∧ ‖DG (s, x)‖ ≤ C ∧ ‖DV (s, x)‖ ≤ C := by
    intro s hs x hx
    have hb := (hC₀ (s, x) ⟨hs, hx⟩).trans (le_abs_self C₀)
    simpa only [Prod.norm_def, max_le_iff, C, and_assoc] using hb
  have hν : Continuous (deriv η) := hη.continuous_deriv le_rfl
  obtain ⟨D₁, hD₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hη.continuous.continuousOn
  obtain ⟨D₂, hD₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hν.continuousOn
  let D := |D₁| + |D₂|
  have hdir : ∀ s ∈ Icc a b, ‖η s‖ ≤ D ∧ ‖deriv η s‖ ≤ D := by
    intro s hs
    have h₁ := hD₁ s hs
    have h₂ := hD₂ s hs
    dsimp only [D]
    constructor <;> linarith [le_abs_self D₁, le_abs_self D₂, abs_nonneg D₁, abs_nonneg D₂]
  have hd := (hasDerivAt_quadraticAction_affine hmin.le hδ hδ1 K u w η (deriv η)
    hmin.continuousOn hmin.memLp hη.continuous.continuousOn hν.continuousOn
    G V
    DG DV
    (hG.continuousOn.mono hsub) (hV.continuousOn.mono hsub)
    (hDG.continuousOn.mono hsub) (hDV.continuousOn.mono hsub)
    (fun ε hε s hs ↦ hδK ε (abs_lt.mpr hε) hs)
    (fun s hs x hx ↦ hasFDerivAt_timeSlice
      ((hG.contDiffAt (hΩ.mem_nhds (hsub ⟨hs, hx⟩))).differentiableAt (by simp)))
    (fun s hs x hx ↦ hasFDerivAt_timeSlice
      ((hV.contDiffAt (hΩ.mem_nhds (hsub ⟨hs, hx⟩))).differentiableAt (by simp)))
    (fun s hs x hx ↦ hsym (s, x) (hsub ⟨hs, hx⟩)) hcoeff hdir).2
  have hlocal := hmin.isLocalMin_affine η hη hηa hηb hδ
    (fun ε hε s hs ↦ hKU (hδK ε (abs_lt.mpr hε) hs))
  exact hlocal.hasDerivAt_eq_zero (by simpa only [quadraticAction_def] using hd)

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ} {V : ℝ × E → ℝ}
  {J : Set ℝ} {U : Set E} {u w : ℝ → E} {a b : ℝ}

-- Cache the canonical nested operator-space instances for the spatial kinetic derivative.
/-- The canonical normed additive structure on the operator coefficient space. -/
local instance quadraticMomentumDualNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
/-- The canonical real normed-space structure on the operator coefficient space. -/
local instance quadraticMomentumDualNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
/-- The canonical normed additive structure on the operator coefficient space. -/
local instance quadraticMomentumBilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
/-- The canonical real normed-space structure on the operator coefficient space. -/
local instance quadraticMomentumBilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
/-- The canonical normed additive structure on the operator coefficient space. -/
local instance quadraticMomentumTrilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
/-- The canonical real normed-space structure on the operator coefficient space. -/
local instance quadraticMomentumTrilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace


/-- A continuous position/velocity pair with its actual momentum primitive solves the smooth
quadratic phase equation and therefore has smooth position. -/
private theorem contDiffOn_of_quadraticMomentum_primitive (hab : a < b)
    (hJ : IsOpen J) (hU : IsOpen U) (htime : Icc a b ⊆ J)
    (hG : ContDiffOn ℝ ∞ G (J ×ˢ U)) (hV : ContDiffOn ℝ ∞ V (J ×ˢ U))
    (hB : ContDiffOn ℝ ∞
      (fun z ↦ Ring.inverse (InnerProductSpace.continuousLinearMapOfBilin (G z))) (J ×ˢ U))
    (hinv : ∀ z ∈ J ×ˢ U, ∀ v : E, Ring.inverse
      (InnerProductSpace.continuousLinearMapOfBilin (G z))
        (InnerProductSpace.continuousLinearMapOfBilin (G z) v) = v)
    (huU : MapsTo u (Icc a b) U) (q : ℝ → E) (hq : ContinuousOn q (Icc a b))
    (hprimq : ∀ s ∈ Icc a b, u s = u a + ∫ r in a..s, q r)
    (hPQ : ∀ s ∈ Icc a b,
      InnerProductSpace.continuousLinearMapOfBilin (G (s, u s)) (q s) =
        InnerProductSpace.continuousLinearMapOfBilin (G (a, u a)) (q a) +
          ∫ r in a..s, quadraticForceVector (spatialFDeriv (𝕜 := ℝ) G (u r) r)
            (spatialFDeriv (𝕜 := ℝ) V (u r) r) (q r)) :
    ContDiffOn ℝ ∞ u (Icc a b) := by
  let DG := fun z : ℝ × E ↦ spatialFDeriv (𝕜 := ℝ) G z.2 z.1
  let DV := fun z : ℝ × E ↦ spatialFDeriv (𝕜 := ℝ) V z.2 z.1
  let A := fun z : ℝ × E ↦ InnerProductSpace.continuousLinearMapOfBilin (G z)
  let B := fun z : ℝ × E ↦ Ring.inverse (A z)
  obtain ⟨hDG, hDV⟩ := contDiffOn_spatialFDerivs (m := ∞) (hJ.prod hU) (by simp) hG hV
  have hdu := (intervalIntegral.hasDerivWithinAt_and_contDiffOn_of_forall_eq_add_integral
    hab u q hq hprimq).1
  have hu : ContinuousOn u (Icc a b) := HasDerivWithinAt.continuousOn hdu
  have hpair : ContinuousOn (fun s ↦ (s, u s)) (Icc a b) := continuousOn_id.prodMk hu
  have hdom : MapsTo (fun s ↦ (s, u s)) (Icc a b) (J ×ˢ U) :=
    fun s hs ↦ ⟨htime hs, huU hs⟩
  let P := fun s ↦ A (s, u s) (q s)
  let Qq := fun s ↦ quadraticForceVector (DG (s, u s)) (DV (s, u s)) (q s)
  have hQq : ContinuousOn Qq (Icc a b) :=
    (contDiff_quadraticForceVector (n := ∞)).continuous.comp_continuousOn
      (((hDG.continuousOn.comp hpair hdom).prodMk
        (hDV.continuousOn.comp hpair hdom)).prodMk hq)
  have hdP := (intervalIntegral.hasDerivWithinAt_and_contDiffOn_of_forall_eq_add_integral
    hab P Qq hQq hPQ).1
  let phase := fun (s : ℝ) (z : E × E) ↦
    let v := B (s, z.1) z.2
    (v, quadraticForceVector (DG (s, z.1)) (DV (s, z.1)) v)
  have hphase : ContDiffOn ℝ ∞ (Function.uncurry phase) (Icc a b ×ˢ (U ×ˢ univ)) := by
    let k := fun z : ℝ × (E × E) ↦ (z.1, z.2.1)
    have hk : ContDiffOn ℝ ∞ k (Icc a b ×ˢ (U ×ˢ univ)) :=
      contDiffOn_fst.prodMk contDiffOn_snd.fst
    have hkdom : MapsTo k (Icc a b ×ˢ (U ×ˢ univ)) (J ×ˢ U) :=
      fun z hz ↦ ⟨htime hz.1, hz.2.1⟩
    have hv := (hB.comp hk hkdom).clm_apply contDiffOn_snd.snd
    have hforce := contDiff_quadraticForceVector.comp_contDiffOn
      (((hDG.comp hk hkdom).prodMk (hDV.comp hk hkdom)).prodMk hv)
    exact hv.prodMk hforce
  have hsolve : ∀ s ∈ Icc a b,
      HasDerivWithinAt (fun r ↦ (u r, P r)) (phase s (u s, P s)) (Icc a b) s := by
    intro s hs
    simpa only [phase, P, B, A, hinv (s, u s) (hdom hs), Qq] using
      HasDerivWithinAt.prodMk (hdu s hs) (hdP s hs)
  exact (ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt (n := ⊤) hphase hsolve
    (fun s hs ↦ ⟨huU hs, mem_univ _⟩)).fst

/-- The first variation tests of an actual minimizer give its vector momentum identity. -/
private theorem IsQuadraticActionMinimizerOn.integral_momentum_test
    (hmin : IsQuadraticActionMinimizerOn G V U u w a b)
    (hJ : IsOpen J) (hU : IsOpen U) (htime : Icc a b ⊆ J)
    (hG : ContDiffOn ℝ 1 G (J ×ˢ U)) (hV : ContDiffOn ℝ 1 V (J ×ˢ U))
    (hsym : ∀ z ∈ J ×ˢ U, ∀ v v' : E, G z v v' = G z v' v)
    (hPint : IntervalIntegrable (fun s ↦
      InnerProductSpace.continuousLinearMapOfBilin (G (s, u s)) (w s)) volume a b)
    (hQint : IntervalIntegrable (fun s ↦ quadraticForceVector
      (spatialFDeriv (𝕜 := ℝ) G (u s) s) (spatialFDeriv (𝕜 := ℝ) V (u s) s) (w s))
      volume a b)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hsupp : tsupport φ ⊆ Ioo a b) :
    (∫ s in a..b, deriv φ s • InnerProductSpace.continuousLinearMapOfBilin
      (G (s, u s)) (w s)) = -(∫ s in a..b, φ s • quadraticForceVector
        (spatialFDeriv (𝕜 := ℝ) G (u s) s) (spatialFDeriv (𝕜 := ℝ) V (u s) s) (w s)) := by
  have hφa : φ a = 0 := image_eq_zero_of_notMem_tsupport
    (fun h ↦ (lt_irrefl a) (hsupp h).1)
  have hφb : φ b = 0 := image_eq_zero_of_notMem_tsupport
    (fun h ↦ (lt_irrefl b) (hsupp h).2)
  apply integral_deriv_smul_eq_neg_integral_smul_of_forall_inner
    _ _ hPint hQint φ (hφ.of_le (by norm_num))
  intro z
  have hstat := hmin.integral_firstVariation_eq_zero hJ hU htime
    hG hV hsym (fun s ↦ φ s • z) ((hφ.smul contDiff_const).of_le (by simp))
    (by simp [hφa]) (by simp [hφb])
  calc
    _ = ∫ s in a..b, spatialFDeriv (𝕜 := ℝ) G (u s) s (φ s • z) (w s) (w s) / 2 +
        G (s, u s) (w s) (deriv φ s • z) + spatialFDeriv (𝕜 := ℝ) V (u s) s (φ s • z) := by
      apply intervalIntegral.integral_congr
      intro s _
      dsimp only
      have hp : inner ℝ z (InnerProductSpace.continuousLinearMapOfBilin (G (s, u s)) (w s)) =
          G (s, u s) (w s) z := by
        rw [real_inner_comm]
        exact InnerProductSpace.continuousLinearMapOfBilin_apply _ _ _
      rw [hp, inner_quadraticForceVector]
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    _ = 0 := by
      have hderiv (s : ℝ) := ((hφ.differentiable (by simp) s).hasDerivAt.smul_const z).deriv
      simpa only [hderiv] using hstat

/-- The actual weak momentum of a minimizer has a continuous velocity representative and
an integral primitive, before the smooth phase bootstrap. -/
private theorem IsQuadraticActionMinimizerOn.exists_continuous_quadraticMomentum
    (hmin : IsQuadraticActionMinimizerOn G V U u w a b) (hab : a < b)
    (hJ : IsOpen J) (hU : IsOpen U) (htime : Icc a b ⊆ J)
    (hG : ContDiffOn ℝ ∞ G (J ×ˢ U)) (hV : ContDiffOn ℝ ∞ V (J ×ˢ U))
    (hsym : ∀ z ∈ J ×ˢ U, ∀ v v' : E, G z v v' = G z v' v)
    (hB : ContDiffOn ℝ ∞
      (fun z ↦ Ring.inverse (InnerProductSpace.continuousLinearMapOfBilin (G z))) (J ×ˢ U))
    (hinv : ∀ z ∈ J ×ˢ U, ∀ v : E, Ring.inverse
      (InnerProductSpace.continuousLinearMapOfBilin (G z))
        (InnerProductSpace.continuousLinearMapOfBilin (G z) v) = v) :
    ∃ (c : E) (q : ℝ → E), ContinuousOn q (Icc a b) ∧
      w =ᵐ[volume.restrict (Icc a b)] q ∧
      (∀ s ∈ Icc a b, InnerProductSpace.continuousLinearMapOfBilin (G (s, u s)) (q s) =
        c + ∫ r in a..s, quadraticForceVector (spatialFDeriv (𝕜 := ℝ) G (u r) r)
          (spatialFDeriv (𝕜 := ℝ) V (u r) r) (w r)) ∧
      ∀ s ∈ Icc a b, u s = u a + ∫ r in a..s, q r := by
  let DG := fun z : ℝ × E ↦ spatialFDeriv (𝕜 := ℝ) G z.2 z.1
  let DV := fun z : ℝ × E ↦ spatialFDeriv (𝕜 := ℝ) V z.2 z.1
  let A := fun z : ℝ × E ↦ InnerProductSpace.continuousLinearMapOfBilin (G z)
  let B := fun z : ℝ × E ↦ Ring.inverse (A z)
  obtain ⟨hDG, hDV⟩ := contDiffOn_spatialFDerivs (m := ∞) (hJ.prod hU) (by simp) hG hV
  have hA : ContDiffOn ℝ ∞ A (J ×ˢ U) :=
    InnerProductSpace.contDiff_continuousLinearMapOfBilin.comp_contDiffOn hG
  have hpair : ContinuousOn (fun s ↦ (s, u s)) (Icc a b) :=
    continuousOn_id.prodMk hmin.continuousOn
  have hdom : MapsTo (fun s ↦ (s, u s)) (Icc a b) (J ×ˢ U) :=
    fun s hs ↦ ⟨htime hs, hmin.mapsTo hs⟩
  let G₀ := fun s ↦ G (s, u s)
  let DG₀ := fun s ↦ DG (s, u s)
  let DV₀ := fun s ↦ DV (s, u s)
  have hG₀ : ContinuousOn G₀ (Icc a b) := hG.continuousOn.comp hpair hdom
  have hDG₀ : ContinuousOn DG₀ (Icc a b) := hDG.continuousOn.comp hpair hdom
  have hDV₀ : ContinuousOn DV₀ (Icc a b) := hDV.continuousOn.comp hpair hdom
  let Q := fun s ↦ quadraticForceVector (DG₀ s) (DV₀ s) (w s)
  obtain ⟨hPint, hQint⟩ := intervalIntegrable_quadraticMomentum_force hmin.le w hmin.memLp
    G₀ DG₀ DV₀ hG₀ hDG₀ hDV₀
  have hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ s in a..b, deriv φ s • A (s, u s) (w s)) = -(∫ s in a..b, φ s • Q s) :=
    fun φ hφ _ hsupp ↦ hmin.integral_momentum_test hJ hU htime
      (hG.of_le (by simp)) (hV.of_le (by simp)) hsym hPint hQint φ hφ hsupp
  obtain ⟨c, q, _, hq, hwq, hmomentum, hprimq, _, _⟩ :=
    exists_continuous_velocity_of_weak_momentum hab u w (fun _ hs ↦ hmin.eq_add_integral hs)
      (fun s ↦ A (s, u s)) (fun s ↦ B (s, u s))
      (hA.continuousOn.comp hpair hdom) (hB.continuousOn.comp hpair hdom)
      (fun s hs ↦ hinv (s, u s) (hdom hs)) Q hQint hPint hweak
  exact ⟨c, q, hq, hwq, hmomentum, hprimq⟩

private theorem IsQuadraticActionMinimizerOn.contDiffOn_of_lt
    (hmin : IsQuadraticActionMinimizerOn G V U u w a b) (hab : a < b)
    (hJ : IsOpen J) (hU : IsOpen U) (htime : Icc a b ⊆ J)
    (hG : ContDiffOn ℝ ∞ G (J ×ˢ U)) (hV : ContDiffOn ℝ ∞ V (J ×ˢ U))
    (hsym : ∀ z ∈ J ×ˢ U, ∀ v v' : E, G z v v' = G z v' v)
    (hpos : ∀ z ∈ J ×ˢ U, ∀ v : E, v ≠ 0 → 0 < G z v v) :
    ContDiffOn ℝ ∞ u (Icc a b) := by
  have hB := InnerProductSpace.contDiffOn_ringInverse_continuousLinearMapOfBilin hG hpos
  have hinv (z : ℝ × E) (hz : z ∈ J ×ˢ U) (v : E) :=
    InnerProductSpace.ringInverse_continuousLinearMapOfBilin_apply_self (hpos z hz) v
  obtain ⟨c, q, hq, hwq, hmomentum, hprimq⟩ :=
    hmin.exists_continuous_quadraticMomentum hab hJ hU htime hG hV hsym hB hinv
  let A := fun z : ℝ × E ↦ InnerProductSpace.continuousLinearMapOfBilin (G z)
  let DG₀ := fun s ↦ spatialFDeriv (𝕜 := ℝ) G (u s) s
  let DV₀ := fun s ↦ spatialFDeriv (𝕜 := ℝ) V (u s) s
  let Q := fun s ↦ quadraticForceVector (DG₀ s) (DV₀ s) (w s)
  let P := fun s ↦ A (s, u s) (q s)
  let Qq := fun s ↦ quadraticForceVector (DG₀ s) (DV₀ s) (q s)
  have hPQ : ∀ s ∈ Icc a b, P s = P a + ∫ r in a..s, Qq r := by
    intro s hs
    have hca : P a = c := by
      simpa only [P, intervalIntegral.integral_same, add_zero] using
        hmomentum a (left_mem_Icc.mpr hab.le)
    rw [hca]
    calc
      P s = c + ∫ r in a..s, Q r := hmomentum s hs
      _ = c + ∫ r in a..s, Qq r := ?_
    congr 1
    apply intervalIntegral.integral_eq_of_ae_eq_Icc (s := s) _ hs
    filter_upwards [hwq] with r hr
    simp only [Q, Qq, hr]
  exact contDiffOn_of_quadraticMomentum_primitive hab hJ hU htime hG hV hB hinv hmin.mapsTo q hq
    hprimq hPQ

/-- Every weak minimizer of a smooth positive quadratic action is smooth within its closed
ordered parameter segment, including singleton segments. -/
theorem IsQuadraticActionMinimizerOn.contDiffOn
    (hmin : IsQuadraticActionMinimizerOn G V U u w a b)
    (hJ : IsOpen J) (hU : IsOpen U) (htime : Icc a b ⊆ J)
    (hG : ContDiffOn ℝ ∞ G (J ×ˢ U)) (hV : ContDiffOn ℝ ∞ V (J ×ˢ U))
    (hsym : ∀ z ∈ J ×ˢ U, ∀ v v' : E, G z v v' = G z v' v)
    (hpos : ∀ z ∈ J ×ˢ U, ∀ v : E, v ≠ 0 → 0 < G z v v) :
    ContDiffOn ℝ ∞ u (Icc a b) := by
  by_cases hab : a < b
  · exact hmin.contDiffOn_of_lt hab hJ hU htime hG hV hsym hpos
  intro x hx
  apply contDiffWithinAt_singleton.mono
  intro y hy
  exact mem_singleton_iff.mpr (subsingleton_Icc_of_ge (le_of_not_gt hab) hy hx)

end InnerProduct

end TauCeti
