/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Analysis.ODE.ParameterJets

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

open Set
open scoped ContDiff

namespace TauCeti

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
  refine ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans (le_max_left _ _)) ?_
  intro z
  rw [jacobiODECoeff_apply, Prod.norm_def, norm_neg]
  exact max_le ((norm_snd_le z).trans
    (le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _)))
    ((R.le_opNorm z.1).trans (mul_le_mul (le_max_right _ _) (norm_fst_le z)
      (norm_nonneg _) (zero_le_one.trans (le_max_left _ _))))

/-- The part of the first-order Jacobi system that depends linearly on curvature. -/
def jacobiODECoeffVariation : (F →L[𝕜] F) →L[𝕜] ((F × F) →L[𝕜] (F × F)) := by
  let L : (F →L[𝕜] F) →ₗ[𝕜] ((F × F) →L[𝕜] (F × F)) :=
    { toFun := fun R ↦ (0 : (F × F) →L[𝕜] F).prod
        (-(R.comp (ContinuousLinearMap.fst 𝕜 F F)))
      map_add' := by intros; ext z <;> simp [add_comm]
      map_smul' := by intros; ext z <;> simp }
  refine LinearMap.mkContinuous (𝕜 := 𝕜) (𝕜₂ := 𝕜) L 1 ?_
  intro R
  rw [one_mul]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg R) ?_
  intro z
  change ‖(0, -(R z.1))‖ ≤ _
  simp only [Prod.norm_def, norm_zero, norm_neg, max_eq_right (norm_nonneg _)]
  exact (R.le_opNorm z.1).trans
    (mul_le_mul_of_nonneg_left (norm_fst_le z) (norm_nonneg R))

@[simp] theorem jacobiODECoeffVariation_apply (R : F →L[𝕜] F) (z : F × F) :
    jacobiODECoeffVariation R z = (0, -R z.1) := by
  simp [jacobiODECoeffVariation, LinearMap.mkContinuous_apply]

/-- The curvature-to-Jacobi variation operator has norm at most one. -/
theorem norm_jacobiODECoeffVariation_le : ‖jacobiODECoeffVariation (𝕜 := 𝕜) (F := F)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro R
  rw [one_mul]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg R) ?_
  intro z
  rw [jacobiODECoeffVariation_apply, Prod.norm_def, norm_zero, norm_neg,
    max_eq_right (norm_nonneg _)]
  exact (R.le_opNorm z.1).trans
    (mul_le_mul_of_nonneg_left (norm_fst_le z) (norm_nonneg R))

/-- The Jacobi coefficient is the sum of a fixed free system and its curvature variation. -/
theorem jacobiODECoeff_eq_affine (R : F →L[𝕜] F) :
    jacobiODECoeff R = jacobiODECoeff (0 : F →L[𝕜] F) + jacobiODECoeffVariation R := by
  ext z <;> simp [jacobiODECoeff_apply]

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
    funext q; exact jacobiODECoeff_eq_affine (R q)
  rw [heq, iteratedFDeriv_add_apply (contDiffAt_const.of_le hkn)
    (((jacobiODECoeffVariation (F := F)).contDiff.contDiffAt.comp p hR).of_le hkn)]
  simp only [iteratedFDeriv_const_of_ne hk, Pi.zero_apply, zero_add]
  have h := (jacobiODECoeffVariation (F := F)).norm_iteratedFDeriv_comp_left hR hkn
  have hb := mul_le_mul_of_nonneg_right (norm_jacobiODECoeffVariation_le (𝕜 := 𝕜) (F := F))
    (norm_nonneg (iteratedFDeriv 𝕜 k R p))
  rw [one_mul] at hb
  exact (h.trans hb).trans (le_max_right _ _)


end Coefficient

variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The position and velocity jets of a second-order linear system satisfy a common
exponential estimate. Initial data may depend on the parameter. -/
theorem norm_iteratedFDeriv_le_exp_of_secondOrderODE
    (n : ℕ) {a b t₀ C D : ℝ} (ht₀ : t₀ ∈ Icc a b)
    {U : Set P} {W : Set (ℝ × P)} (hW : IsOpen W) (hUW : Icc a b ×ˢ U ⊆ W)
    {R : ℝ × P → F →L[ℝ] F} {y v : ℝ × P → F}
    (hR : ContDiffOn ℝ n R W) (hy : ContDiffOn ℝ (n + 1) y W)
    (hv : ContDiffOn ℝ (n + 1) v W)
    (hyode : ∀ z ∈ W, timeFDeriv y z.1 z.2 = v z)
    (hvode : ∀ z ∈ W, timeFDeriv v z.1 z.2 = -(R z) (y z))
    (hinit : ∀ j ≤ n, ∀ q ∈ U,
      ‖iteratedFDeriv ℝ j (fun q ↦ (y (t₀, q), v (t₀, q))) q‖ ≤ D)
    (hbound : ∀ j ≤ n, ∀ s ∈ Icc a b, ∀ q ∈ U,
      ‖iteratedFDeriv ℝ j (fun q ↦ R (s, q)) q‖ ≤ C)
    {t : ℝ} (ht : t ∈ Icc a b) {p : P} (hp : p ∈ U) :
    ‖iteratedFDeriv ℝ n (fun q ↦ (y (t, q), v (t, q))) p‖ ≤
      D * Real.exp ((2 : ℝ) ^ n * max 1 C * |t - t₀|) := by
  let A : ℝ × P → (F × F) →L[ℝ] (F × F) := fun z ↦ jacobiODECoeff (R z)
  have hA : ContDiffOn ℝ n A W := by
    have heq : A = (fun _ ↦ jacobiODECoeff (0 : F →L[ℝ] F)) +
        (jacobiODECoeffVariation (F := F) ∘ R) := by
      funext z
      exact jacobiODECoeff_eq_affine (R z)
    rw [heq]
    exact contDiffOn_const.add ((jacobiODECoeffVariation (F := F)).contDiff.comp_contDiffOn hR)
  have hode : ∀ z ∈ W, timeFDeriv (fun w ↦ (y w, v w)) z.1 z.2 = A z (y z, v z) := by
    intro z hz
    have hyd := ((hy z hz).contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp)
    have hvd := ((hv z hz).contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp)
    rw [timeFDeriv_apply]
    rw [(hyd.hasFDerivAt.prodMk hvd.hasFDerivAt).fderiv]
    rw [ContinuousLinearMap.prod_apply, ← timeFDeriv_apply, ← timeFDeriv_apply,
      hyode z hz, hvode z hz]
    simp only [A, jacobiODECoeff_apply]
  have hAbound : ∀ j ≤ n, ∀ s ∈ Icc a b, ∀ q ∈ U,
      ‖iteratedFDeriv ℝ j (fun q ↦ A (s, q)) q‖ ≤ max 1 C := by
    intro j hj s hs q hq
    have hRq : ContDiffAt ℝ j (fun q ↦ R (s, q)) q :=
      (((hR _ (hUW ⟨hs, hq⟩)).contDiffAt (hW.mem_nhds (hUW ⟨hs, hq⟩))).comp q
        (contDiffAt_const.prodMk contDiffAt_id)).of_le (by exact_mod_cast hj)
    exact (norm_iteratedFDeriv_jacobiODECoeff_le j hRq).trans
      (max_le_max le_rfl (hbound j hj s hs q hq))
  exact norm_iteratedFDeriv_le_exp_of_linearODE n ht₀ hW hUW hA (hy.prodMk hv)
    hode hinit hAbound ht hp

/-- The matrix Jacobi equation obeys the same parameter-jet estimate. Operator
composition has norm at most one, so lifting the curvature coefficient to its action
on operators introduces no extra constant. -/
theorem norm_iteratedFDeriv_le_exp_of_matrixJacobiODE
    (n : ℕ) {a b t₀ C D : ℝ} (ht₀ : t₀ ∈ Icc a b)
    {U : Set P} {W : Set (ℝ × P)} (hW : IsOpen W) (hUW : Icc a b ×ˢ U ⊆ W)
    {R J V : ℝ × P → F →L[ℝ] F}
    (hR : ContDiffOn ℝ n R W) (hJ : ContDiffOn ℝ (n + 1) J W)
    (hV : ContDiffOn ℝ (n + 1) V W)
    (hJode : ∀ z ∈ W, timeFDeriv J z.1 z.2 = V z)
    (hVode : ∀ z ∈ W, timeFDeriv V z.1 z.2 = -(R z).comp (J z))
    (hinit : ∀ j ≤ n, ∀ q ∈ U,
      ‖iteratedFDeriv ℝ j (fun q ↦ (J (t₀, q), V (t₀, q))) q‖ ≤ D)
    (hbound : ∀ j ≤ n, ∀ s ∈ Icc a b, ∀ q ∈ U,
      ‖iteratedFDeriv ℝ j (fun q ↦ R (s, q)) q‖ ≤ C)
    {t : ℝ} (ht : t ∈ Icc a b) {p : P} (hp : p ∈ U) :
    ‖iteratedFDeriv ℝ n (fun q ↦ (J (t, q), V (t, q))) p‖ ≤
      D * Real.exp ((2 : ℝ) ^ n * max 1 C * |t - t₀|) := by
  let L := ContinuousLinearMap.compL ℝ F F F
  have hLR : ContDiffOn ℝ n (fun z ↦ L (R z)) W := L.contDiff.comp_contDiffOn hR
  have hLbound : ∀ j ≤ n, ∀ s ∈ Icc a b, ∀ q ∈ U,
      ‖iteratedFDeriv ℝ j (fun q ↦ L (R (s, q))) q‖ ≤ C := by
    intro j hj s hs q hq
    have hRq : ContDiffAt ℝ n (fun q ↦ R (s, q)) q :=
      ((hR _ (hUW ⟨hs, hq⟩)).contDiffAt (hW.mem_nhds (hUW ⟨hs, hq⟩))).comp q
        (contDiffAt_const.prodMk contDiffAt_id)
    exact (L.norm_iteratedFDeriv_comp_left hRq (by exact_mod_cast hj)).trans
      ((mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_compL_le ℝ F F F)
        (norm_nonneg _)).trans (by simpa only [one_mul] using hbound j hj s hs q hq))
  exact norm_iteratedFDeriv_le_exp_of_secondOrderODE n ht₀ hW hUW hLR hJ hV
    hJode hVode hinit hLbound ht hp

end TauCeti
