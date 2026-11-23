/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Analysis.ODE.ParameterJets
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Parameter-jet estimates for second-order linear equations

For `y' = v` and `v' = -R y`, parameter derivatives of the position and velocity
are controlled by the parameter derivatives of `R` and the initial data. The same
estimate applies to operator-valued Jacobi solutions using continuous composition.
The time interval and reference time are explicit; no completeness or dimension
assumption is needed.

These are the ODE estimates used for the radial coframe in normal-coordinate
compactness arguments (Morgan–Tian, Lemma 5.7).

Formalization references: https://github.com/frenzymath/lean-eval-submissions and
https://github.com/frenzymath/PoincareConjecture.
-/

public noncomputable section

open Set ContinuousLinearMap
open scoped ContDiff

namespace ContinuousLinearMap

section Coefficient

variable {𝕜 P F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The first-order coefficient of the Jacobi equation `y'' + R y = 0`. -/
def jacobiODECoeff (R : F →L[𝕜] F) : (F × F) →L[𝕜] (F × F) :=
  (ContinuousLinearMap.snd 𝕜 F F).prod (-(R.comp (ContinuousLinearMap.fst 𝕜 F F)))

@[simp]
theorem jacobiODECoeff_apply (R : F →L[𝕜] F) (z : F × F) :
    jacobiODECoeff R z = (z.2, -R z.1) := by
  simp [jacobiODECoeff]

/-- The product norm controls the second-order coefficient without dimension constants. -/
theorem norm_jacobiODECoeff_le (R : F →L[𝕜] F) :
    ‖jacobiODECoeff R‖ ≤ max 1 ‖R‖ := by
  rw [jacobiODECoeff, ContinuousLinearMap.opNorm_prod, Prod.norm_def, norm_neg]
  exact max_le_max (ContinuousLinearMap.norm_snd_le 𝕜 F F)
    ((R.opNorm_comp_le _).trans (mul_le_of_le_one_right (norm_nonneg R)
      (ContinuousLinearMap.norm_fst_le 𝕜 F F)))

/-- The part of the first-order Jacobi system that depends linearly on curvature. -/
private def jacobiODECoeffVariation :
    (F →L[𝕜] F) →L[𝕜] ((F × F) →L[𝕜] (F × F)) :=
  -((LinearIsometry.inr 𝕜 F F).postcomp.toContinuousLinearMap.comp
    ((ContinuousLinearMap.compL 𝕜 (F × F) F F).flip (ContinuousLinearMap.fst 𝕜 F F)))

@[simp] private theorem jacobiODECoeffVariation_apply (R : F →L[𝕜] F) (z : F × F) :
    jacobiODECoeffVariation R z = (0, -R z.1) := by
  simp [jacobiODECoeffVariation, LinearIsometry.postcomp]

/-- The curvature-to-Jacobi variation operator has norm at most one. -/
private theorem norm_jacobiODECoeffVariation_le :
    ‖jacobiODECoeffVariation (𝕜 := 𝕜) (F := F)‖ ≤ 1 := by
  let : NormedAddCommGroup ((F × F) →L[𝕜] F) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace 𝕜 ((F × F) →L[𝕜] F) := ContinuousLinearMap.toNormedSpace
  let K := (ContinuousLinearMap.compL 𝕜 (F × F) F F).flip
    (ContinuousLinearMap.fst 𝕜 F F)
  -- The local normed-map instances and K are definitionally the coefficient's operator factors.
  change ‖-((LinearIsometry.inr 𝕜 F F).postcomp.toContinuousLinearMap.comp K)‖ ≤ 1
  rw [norm_neg, LinearIsometry.norm_toContinuousLinearMap_comp]
  refine ((ContinuousLinearMap.compL 𝕜 (F × F) F F).flip.le_opNorm _).trans ?_
  rw [ContinuousLinearMap.opNorm_flip]
  exact (mul_le_mul_of_nonneg_right
    (ContinuousLinearMap.norm_compL_le 𝕜 (F × F) F F) (norm_nonneg _)).trans
    (by simpa only [one_mul] using ContinuousLinearMap.norm_fst_le 𝕜 F F)

/-- The Jacobi coefficient is a fixed free system plus its linear curvature variation. -/
private theorem jacobiODECoeff_eq_jacobiODECoeff_zero_add (R : F →L[𝕜] F) :
    jacobiODECoeff R = jacobiODECoeff (0 : F →L[𝕜] F) + jacobiODECoeffVariation R := by
  ext z <;> simp [jacobiODECoeff_apply]

/-- The first-order Jacobi coefficient depends smoothly on its curvature operator. -/
theorem contDiff_jacobiODECoeff {n : ℕ∞ω} :
    ContDiff 𝕜 n (jacobiODECoeff (𝕜 := 𝕜) (F := F)) := by
  have heq : jacobiODECoeff (𝕜 := 𝕜) (F := F) =
      (fun R : F →L[𝕜] F ↦ jacobiODECoeff (0 : F →L[𝕜] F) + jacobiODECoeffVariation R) := by
    funext R
    exact jacobiODECoeff_eq_jacobiODECoeff_zero_add R
  rw [heq]
  exact contDiff_const.add (jacobiODECoeffVariation (𝕜 := 𝕜) (F := F)).contDiff

end Coefficient

end ContinuousLinearMap

namespace TauCeti

section CoefficientJets

variable {𝕜 P F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A Jacobi coefficient jet is bounded by the corresponding curvature jet and the
fixed free coefficient. -/
theorem norm_iteratedFDeriv_jacobiODECoeff_le
    {R : P → F →L[𝕜] F} {p : P} (k : ℕ) (hR : ContDiffAt 𝕜 k R p) :
    ‖iteratedFDeriv 𝕜 k (fun q ↦ jacobiODECoeff (R q)) p‖ ≤
      max 1 ‖iteratedFDeriv 𝕜 k R p‖ := by
  by_cases hk : k = 0
  · subst k
    simp only [norm_iteratedFDeriv_zero]
    exact norm_jacobiODECoeff_le (R p)
  have hkn : (k : ℕ∞ω) ≤ k := le_rfl
  have heq : (fun q ↦ jacobiODECoeff (R q)) =
      (fun _ ↦ jacobiODECoeff (0 : F →L[𝕜] F)) + (jacobiODECoeffVariation (F := F) ∘ R) := by
    funext q; exact jacobiODECoeff_eq_jacobiODECoeff_zero_add (R q)
  rw [heq, iteratedFDeriv_add_apply (contDiffAt_const.of_le hkn)
    (((jacobiODECoeffVariation (F := F)).contDiff.contDiffAt.comp p hR).of_le hkn)]
  simp only [iteratedFDeriv_const_of_ne hk, Pi.zero_apply, zero_add]
  have h := (jacobiODECoeffVariation (F := F)).norm_iteratedFDeriv_comp_left hR hkn
  have hb := mul_le_mul_of_nonneg_right (norm_jacobiODECoeffVariation_le (𝕜 := 𝕜) (F := F))
    (norm_nonneg (iteratedFDeriv 𝕜 k R p))
  rw [one_mul] at hb
  exact (h.trans hb).trans (le_max_right _ _)

end CoefficientJets

variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The position and velocity jets of a vector Jacobi equation satisfy a common
exponential estimate. Initial data may depend on the parameter. -/
theorem norm_iteratedFDeriv_le_exp_of_jacobiODE
    (n : ℕ) {a b t₀ C D : ℝ} (ht₀ : t₀ ∈ Icc a b)
    {p : P} {W : Set (ℝ × P)} (hW : IsOpen W)
    (hpW : ∀ s ∈ Icc a b, (s, p) ∈ W)
    {R : ℝ × P → F →L[ℝ] F} {y v : ℝ × P → F}
    (hR : ContDiffOn ℝ n R W) (hy : ContDiffOn ℝ (n + 1) y W)
    (hv : ContDiffOn ℝ (n + 1) v W)
    (hyode : ∀ z ∈ W, timeFDeriv y z.1 z.2 = v z)
    (hvode : ∀ z ∈ W, timeFDeriv v z.1 z.2 = -(R z) (y z))
    (hinit : ∀ j ≤ n,
      ‖iteratedFDeriv ℝ j (fun q ↦ (y (t₀, q), v (t₀, q))) p‖ ≤ D)
    (hbound : ∀ j ≤ n, ∀ s ∈ Icc a b,
      ‖iteratedFDeriv ℝ j (fun q ↦ R (s, q)) p‖ ≤ C)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖iteratedFDeriv ℝ n (fun q ↦ (y (t, q), v (t, q))) p‖ ≤
      D * Real.exp ((2 : ℝ) ^ n * max 1 C * |t - t₀|) := by
  let A : ℝ × P → (F × F) →L[ℝ] (F × F) := fun z ↦ jacobiODECoeff (R z)
  have hA : ContDiffOn ℝ n A W :=
    (contDiff_jacobiODECoeff (𝕜 := ℝ) (F := F)).comp_contDiffOn hR
  have hode : ∀ z ∈ W, timeFDeriv (fun w ↦ (y w, v w)) z.1 z.2 = A z (y z, v z) := by
    intro z hz
    have hyd := ((hy z hz).contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp)
    have hvd := ((hv z hz).contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp)
    rw [timeFDeriv_apply]
    rw [(hyd.hasFDerivAt.prodMk hvd.hasFDerivAt).fderiv]
    rw [ContinuousLinearMap.prod_apply, ← timeFDeriv_apply, ← timeFDeriv_apply,
      hyode z hz, hvode z hz]
    simp only [A, jacobiODECoeff_apply]
  have hAbound : ∀ j ≤ n, ∀ s ∈ Icc a b,
      ‖iteratedFDeriv ℝ j (fun q ↦ A (s, q)) p‖ ≤ max 1 C := by
    intro j hj s hs
    have hRq := (hR.contDiffAt_timeSlice hW (hpW s hs)).of_le
      (m := (j : ℕ∞ω)) (by exact_mod_cast hj)
    exact (norm_iteratedFDeriv_jacobiODECoeff_le j hRq).trans
      (max_le_max le_rfl (hbound j hj s hs))
  exact norm_iteratedFDeriv_le_exp_of_linearODE n ht₀ hW hpW hA (hy.prodMk hv)
    hode hinit hAbound ht

/-- The operator-valued Jacobi equation obeys the same parameter-jet estimate. Operator
composition has norm at most one, so lifting the curvature coefficient to its action
on operators introduces no extra constant. -/
theorem norm_iteratedFDeriv_le_exp_of_operatorJacobiODE
    (n : ℕ) {a b t₀ C D : ℝ} (ht₀ : t₀ ∈ Icc a b)
    {p : P} {W : Set (ℝ × P)} (hW : IsOpen W)
    (hpW : ∀ s ∈ Icc a b, (s, p) ∈ W)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ × P → F →L[ℝ] F} {J V : ℝ × P → E →L[ℝ] F}
    (hR : ContDiffOn ℝ n R W) (hJ : ContDiffOn ℝ (n + 1) J W)
    (hV : ContDiffOn ℝ (n + 1) V W)
    (hJode : ∀ z ∈ W, timeFDeriv J z.1 z.2 = V z)
    (hVode : ∀ z ∈ W, timeFDeriv V z.1 z.2 = -(R z).comp (J z))
    (hinit : ∀ j ≤ n,
      ‖iteratedFDeriv ℝ j (fun q ↦ (J (t₀, q), V (t₀, q))) p‖ ≤ D)
    (hbound : ∀ j ≤ n, ∀ s ∈ Icc a b,
      ‖iteratedFDeriv ℝ j (fun q ↦ R (s, q)) p‖ ≤ C)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖iteratedFDeriv ℝ n (fun q ↦ (J (t, q), V (t, q))) p‖ ≤
      D * Real.exp ((2 : ℝ) ^ n * max 1 C * |t - t₀|) := by
  -- Pin the canonical structures for composition on the rectangular operator space.
  let : NormedAddCommGroup (F →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (F →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
  let L : (F →L[ℝ] F) →L[ℝ] ((E →L[ℝ] F) →L[ℝ] (E →L[ℝ] F)) :=
    ContinuousLinearMap.compL ℝ E F F
  have hLR : ContDiffOn ℝ n (fun z ↦ L (R z)) W := L.contDiff.comp_contDiffOn hR
  have hLbound : ∀ j ≤ n, ∀ s ∈ Icc a b,
      ‖iteratedFDeriv ℝ j (fun q ↦ L (R (s, q))) p‖ ≤ C := by
    intro j hj s hs
    have hRq := hR.contDiffAt_timeSlice hW (hpW s hs)
    exact (L.norm_iteratedFDeriv_comp_left hRq (by exact_mod_cast hj)).trans
      ((mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_compL_le ℝ E F F)
        (norm_nonneg _)).trans (by simpa only [one_mul] using hbound j hj s hs))
  exact norm_iteratedFDeriv_le_exp_of_jacobiODE n ht₀ hW hpW hLR hJ hV
    hJode (fun z hz ↦ by simpa only [L, ContinuousLinearMap.compL_apply] using hVode z hz)
    hinit hLbound ht

end TauCeti
