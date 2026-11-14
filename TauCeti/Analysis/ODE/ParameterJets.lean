/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Analysis.Calculus.ParametricFDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import TauCeti.Analysis.ODE.Gronwall.TwoSided

import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Quantitative parameter derivatives of linear ODEs

The solution and its spatial derivative form a linear system on
`F × (P →L[ℝ] F)`. Iterating this construction bounds the parameter jets of a linear
ODE by the corresponding coefficient jets and initial jets. The estimates hold in
both time directions from any reference time, with finite differentiability and
without completeness or finite-dimensionality assumptions.

These estimates apply to the matrix Jacobi equation in a parallel frame, used in the
normal-coordinate estimates for pointed smooth compactness.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Lemma 5.7.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace TauCeti

section Coefficient

variable {𝕜 P F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

-- Pin the canonical operator-space structures for the augmented-system induction.
/-- The canonical normed group structure on endomorphisms. -/
local instance jetEndGroup : NormedAddCommGroup (F →L[𝕜] F) :=
  ContinuousLinearMap.toNormedAddCommGroup
/-- The canonical scalar action on endomorphisms. -/
local instance jetEndSpace : NormedSpace 𝕜 (F →L[𝕜] F) := ContinuousLinearMap.toNormedSpace
/-- The canonical normed group structure on parameter derivatives. -/
local instance jetDerivativeGroup : NormedAddCommGroup (P →L[𝕜] F) :=
  ContinuousLinearMap.toNormedAddCommGroup
/-- The canonical scalar action on parameter derivatives. -/
local instance jetDerivativeSpace : NormedSpace 𝕜 (P →L[𝕜] F) := ContinuousLinearMap.toNormedSpace

/-- The linear system for a solution together with its parameter derivative. -/
def linearODEJetCoeff (A : F →L[𝕜] F) (B : P →L[𝕜] F →L[𝕜] F) :
    (F × (P →L[𝕜] F)) →L[𝕜] (F × (P →L[𝕜] F)) :=
  (A.comp (ContinuousLinearMap.fst 𝕜 F (P →L[𝕜] F))).prod
    (((ContinuousLinearMap.compL 𝕜 P F F A).comp (ContinuousLinearMap.snd 𝕜 F (P →L[𝕜] F))) +
      B.flip.comp (ContinuousLinearMap.fst 𝕜 F (P →L[𝕜] F)))

@[simp] theorem linearODEJetCoeff_apply (A : F →L[𝕜] F)
    (B : P →L[𝕜] F →L[𝕜] F) (z : F × (P →L[𝕜] F)) :
    linearODEJetCoeff A B z = (A z.1, A.comp z.2 + B.flip z.1) := by
  simp [linearODEJetCoeff]

/-- The augmented coefficient is bounded by the sum of the two coefficient norms. -/
theorem norm_linearODEJetCoeff_le (A : F →L[𝕜] F) (B : P →L[𝕜] F →L[𝕜] F) :
    ‖linearODEJetCoeff A B‖ ≤ ‖A‖ + ‖B‖ := by
  refine (linearODEJetCoeff A B).opNorm_le_bound (add_nonneg (norm_nonneg A) (norm_nonneg B)) ?_
  intro z
  rw [linearODEJetCoeff_apply, Prod.norm_def]
  apply max_le
  · exact (A.le_opNorm z.1).trans
      (mul_le_mul (le_add_of_nonneg_right (norm_nonneg B)) (norm_fst_le z)
        (norm_nonneg z.1) (add_nonneg (norm_nonneg A) (norm_nonneg B)))
  · calc
      ‖A.comp z.2 + B.flip z.1‖ ≤ ‖A.comp z.2‖ + ‖B.flip z.1‖ := norm_add_le _ _
      _ ≤ ‖A‖ * ‖z.2‖ + ‖B‖ * ‖z.1‖ := by
        apply add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
        simpa using B.flip.le_opNorm z.1
      _ ≤ ‖A‖ * ‖z‖ + ‖B‖ * ‖z‖ := add_le_add
        (mul_le_mul_of_nonneg_left (norm_snd_le z) (norm_nonneg A))
        (mul_le_mul_of_nonneg_left (norm_fst_le z) (norm_nonneg B))
      _ = (‖A‖ + ‖B‖) * ‖z‖ := by ring

/-- The augmented coefficient depends continuously and linearly on its two inputs. -/
def linearODEJetCoeffL :
    ((F →L[𝕜] F) × (P →L[𝕜] F →L[𝕜] F)) →L[𝕜]
      ((F × (P →L[𝕜] F)) →L[𝕜] (F × (P →L[𝕜] F))) := by
  let L : ((F →L[𝕜] F) × (P →L[𝕜] F →L[𝕜] F)) →ₗ[𝕜]
      ((F × (P →L[𝕜] F)) →L[𝕜] (F × (P →L[𝕜] F))) :=
    { toFun := fun z ↦ linearODEJetCoeff z.1 z.2
      map_add' := by
        intro z w
        ext v q <;> simp only [add_apply, Prod.fst_add, Prod.snd_add,
          linearODEJetCoeff_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
          ContinuousLinearMap.flip_apply] <;> abel
      map_smul' := by intro c z; ext v q <;> simp [linearODEJetCoeff_apply] }
  refine LinearMap.mkContinuous (𝕜 := 𝕜) (𝕜₂ := 𝕜)
    (E := (F →L[𝕜] F) × (P →L[𝕜] F →L[𝕜] F))
    (F := (F × (P →L[𝕜] F)) →L[𝕜] (F × (P →L[𝕜] F))) L 2 ?_
  intro z
  exact (norm_linearODEJetCoeff_le z.1 z.2).trans (by
    calc ‖z.1‖ + ‖z.2‖ ≤ ‖z‖ + ‖z‖ := add_le_add (norm_fst_le z) (norm_snd_le z)
      _ = 2 * ‖z‖ := by ring)

@[simp] theorem linearODEJetCoeffL_apply (z : (F →L[𝕜] F) × (P →L[𝕜] F →L[𝕜] F)) :
    linearODEJetCoeffL z = linearODEJetCoeff z.1 z.2 := by
  simp [linearODEJetCoeffL, LinearMap.mkContinuous_apply]

/-- The coefficient augmentation operator has norm at most two. -/
theorem norm_linearODEJetCoeffL_le :
    ‖linearODEJetCoeffL (𝕜 := 𝕜) (P := P) (F := F)‖ ≤ 2 := by
  refine (linearODEJetCoeffL (𝕜 := 𝕜) (P := P) (F := F)).opNorm_le_bound (by norm_num) ?_
  intro z
  exact (norm_linearODEJetCoeff_le z.1 z.2).trans (by
    have hfst := norm_fst_le z
    have hsnd := norm_snd_le z
    linarith)

end Coefficient

variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The canonical real normed group structure on endomorphisms. -/
local instance realJetEndGroup : NormedAddCommGroup (F →L[ℝ] F) :=
  ContinuousLinearMap.toNormedAddCommGroup
/-- The canonical real scalar action on endomorphisms. -/
local instance realJetEndSpace : NormedSpace ℝ (F →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
/-- The canonical real normed group structure on parameter derivatives. -/
local instance realJetDerivativeGroup : NormedAddCommGroup (P →L[ℝ] F) :=
  ContinuousLinearMap.toNormedAddCommGroup
/-- The canonical real scalar action on parameter derivatives. -/
local instance realJetDerivativeSpace : NormedSpace ℝ (P →L[ℝ] F) :=
  ContinuousLinearMap.toNormedSpace

/-- Differentiating a linear ODE in a parameter gives the augmented linear system. -/
theorem hasDerivAt_linearODEJet
    {A : ℝ × P → F →L[ℝ] F} {y : ℝ × P → F} {W : Set (ℝ × P)}
    (hW : IsOpen W) (hy : ContDiffOn ℝ 2 y W)
    (hode : ∀ z ∈ W, timeFDeriv y z.1 z.2 = A z (y z))
    {t : ℝ} {p : P} (hz : (t, p) ∈ W) (hA : DifferentiableAt ℝ A (t, p)) :
    HasDerivAt (fun s ↦ (y (s, p), spatialFDeriv (𝕜 := ℝ) y p s))
      (linearODEJetCoeff (A (t, p)) (spatialFDeriv (𝕜 := ℝ) A p t)
        (y (t, p), spatialFDeriv (𝕜 := ℝ) y p t)) t := by
  have hyz := (hy _ hz).contDiffAt (hW.mem_nhds hz)
  have heq : timeFDeriv y t =ᶠ[𝓝 p] fun q ↦ A (t, q) (y (t, q)) := by
    filter_upwards [(continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (hW.mem_nhds hz)] with q hq
    exact hode _ hq
  have hprod := (hA.hasFDerivAt.comp p (hasFDerivAt_prodMk_right t p)).clm_apply
    (hasFDerivAt_timeSlice (hyz.differentiableAt (by norm_num)))
  have hD := hasDerivAt_spatialFDeriv
    (by simpa using hyz : ContDiffAt ℝ (minSmoothness ℝ 2) y (t, p))
  simp only [Function.comp_apply] at hprod
  rw [heq.fderiv_eq, hprod.fderiv] at hD
  simpa only [linearODEJetCoeff_apply, spatialFDeriv_def]
    using (((hasDerivAt_parameterCurve (hyz.differentiableAt (by norm_num))).congr_deriv
      (hode (t, p) hz)).prodMk hD)

/-- Coefficient jets of the augmented system use two adjacent coefficient jets. -/
private theorem norm_iteratedFDeriv_linearODEJetCoeff_le
    {n : ℕ} {k : ℕ} (hk : k ≤ n) {A : ℝ × P → F →L[ℝ] F}
    {W : Set (ℝ × P)} (hW : IsOpen W) (hA : ContDiffOn ℝ (n + 1) A W)
    {t : ℝ} {p : P} (hz : (t, p) ∈ W) :
    ‖iteratedFDeriv ℝ k
      (fun q ↦ linearODEJetCoeff (A (t, q)) (spatialFDeriv (𝕜 := ℝ) A q t)) p‖ ≤
      2 * max ‖iteratedFDeriv ℝ k (fun q ↦ A (t, q)) p‖
        ‖iteratedFDeriv ℝ (k + 1) (fun q ↦ A (t, q)) p‖ := by
  have hAp := ((hA _ hz).contDiffAt (hW.mem_nhds hz)).comp p
    (contDiffAt_const.prodMk contDiffAt_id)
  have hDp := (((contDiffOn_spatialFDeriv hW hA) _ hz).contDiffAt
    (hW.mem_nhds hz)).comp p (contDiffAt_const.prodMk contDiffAt_id)
  simp only [Function.comp_def] at hAp hDp
  have hkn : (k : ℕ∞ω) ≤ n := by exact_mod_cast hk
  have h := (linearODEJetCoeffL (𝕜 := ℝ) (P := P) (F := F)).norm_iteratedFDeriv_comp_left
    ((hAp.of_le (show (n : ℕ∞ω) ≤ n + 1 from le_self_add)).prodMk hDp) hkn
  have hb := mul_le_mul_of_nonneg_right (norm_linearODEJetCoeffL_le (𝕜 := ℝ) (P := P) (F := F))
    (norm_nonneg (iteratedFDeriv ℝ k
      (fun q ↦ (A (t, q), spatialFDeriv (𝕜 := ℝ) A q t)) p))
  have heq : ‖iteratedFDeriv ℝ k
      (fun q ↦ (A (t, q), spatialFDeriv (𝕜 := ℝ) A q t)) p‖ =
      max ‖iteratedFDeriv ℝ k (fun q ↦ A (t, q)) p‖
        ‖iteratedFDeriv ℝ (k + 1) (fun q ↦ A (t, q)) p‖ := by
    rw [iteratedFDeriv_prodMk (hAp.of_le (show (n : ℕ∞ω) ≤ n + 1 from le_self_add)) hDp hkn,
      ContinuousMultilinearMap.opNorm_prod,
      norm_iteratedFDeriv_spatialFDeriv hW (hA.differentiableOn (by simp)) hz]
  simpa only [Function.comp_def, linearODEJetCoeffL_apply, heq] using h.trans hb

universe u v

/-- The induction takes place in a universe containing the parameter space, so that
`F × (P →L[ℝ] F)` is another admissible target. -/
private theorem norm_iteratedFDeriv_le_exp_of_linearODE_aux
    {P : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) {a b t₀ C D : ℝ} (ht₀ : t₀ ∈ Icc a b)
    {U : Set P} {W : Set (ℝ × P)} (hW : IsOpen W) (hUW : Icc a b ×ˢ U ⊆ W)
    {A : ℝ × P → F →L[ℝ] F} {y : ℝ × P → F}
    (hA : ContDiffOn ℝ n A W) (hy : ContDiffOn ℝ (n + 1) y W)
    (hode : ∀ z ∈ W, timeFDeriv y z.1 z.2 = A z (y z))
    (hinit : ∀ j ≤ n, ∀ q ∈ U, ‖iteratedFDeriv ℝ j (fun q ↦ y (t₀, q)) q‖ ≤ D)
    (hbound : ∀ j ≤ n, ∀ s ∈ Icc a b, ∀ q ∈ U,
      ‖iteratedFDeriv ℝ j (fun q ↦ A (s, q)) q‖ ≤ C)
    {t : ℝ} (ht : t ∈ Icc a b) {p : P} (hp : p ∈ U) :
    ‖iteratedFDeriv ℝ n (fun q ↦ y (t, q)) p‖ ≤
      D * Real.exp ((2 : ℝ) ^ n * C * |t - t₀|) := by
  induction n generalizing F C with
  | zero =>
    have hd (s : ℝ) (hs : s ∈ Icc a b) :
        HasDerivAt (fun r ↦ y (r, p)) (A (s, p) (y (s, p))) s :=
      (hasDerivAt_parameterCurve (((hy _ (hUW ⟨hs, hp⟩)).contDiffAt
        (hW.mem_nhds (hUW ⟨hs, hp⟩))).differentiableAt (by simp))).congr_deriv
        (hode (s, p) (hUW ⟨hs, hp⟩))
    have h := norm_le_gronwallBound_of_norm_derivWithin_le ht₀
      (fun s hs ↦ (hd s hs).hasDerivWithinAt)
      (by simpa only [norm_iteratedFDeriv_zero] using hinit 0 le_rfl p hp)
      (K := C) (ε := 0) (fun s hs ↦ by
        simpa only [add_zero] using ((A (s, p)).le_opNorm (y (s, p))).trans
          (mul_le_mul_of_nonneg_right
            (by simpa only [norm_iteratedFDeriv_zero] using hbound 0 le_rfl s hs p hp)
            (norm_nonneg _))) t ht
    simpa only [norm_iteratedFDeriv_zero, pow_zero, one_mul, gronwallBound_ε0] using h
  | succ n ih =>
    let Y : ℝ × P → F × (P →L[ℝ] F) := fun z ↦ (y z, spatialFDeriv (𝕜 := ℝ) y z.2 z.1)
    let Q : ℝ × P → (F × (P →L[ℝ] F)) →L[ℝ] (F × (P →L[ℝ] F)) :=
      fun z ↦ linearODEJetCoeff (A z) (spatialFDeriv (𝕜 := ℝ) A z.2 z.1)
    have hAn : ContDiffOn ℝ (n + 1) A W := by simpa only [Nat.cast_add, Nat.cast_one] using hA
    have hyn : ContDiffOn ℝ ((n : ℕ∞ω) + 1 + 1) y W := by
      simpa only [Nat.cast_add, Nat.cast_one] using hy
    have hY : ContDiffOn ℝ (n + 1) Y W :=
      (hyn.of_le (show (n : ℕ∞ω) + 1 ≤ n + 1 + 1 from le_self_add)).prodMk
        (contDiffOn_spatialFDeriv (n := (n : ℕ∞ω) + 1) hW hyn)
    have hQ : ContDiffOn ℝ n Q W := by
      simpa only [Q, Function.comp_def, linearODEJetCoeffL_apply] using
        (linearODEJetCoeffL (𝕜 := ℝ) (P := P) (F := F)).contDiff.comp_contDiffOn
        ((hAn.of_le (show (n : ℕ∞ω) ≤ n + 1 from le_self_add)).prodMk
          (contDiffOn_spatialFDeriv (n := (n : ℕ∞ω)) hW hAn))
    have hQY : ∀ z ∈ W, timeFDeriv Y z.1 z.2 = Q z (Y z) := by
      intro z hz
      have hd := hasDerivAt_linearODEJet hW
        (hyn.of_le (by norm_cast; omega)) hode hz
        (((hAn _ hz).contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp))
      have hdy := hasDerivAt_parameterCurve
        (((hY _ hz).contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp))
      exact hdy.unique hd
    have hYbound (s : ℝ) (hs : s ∈ Icc a b) (q : P) (hq : q ∈ U) (j : ℕ) (hj : j ≤ n) :
        ‖iteratedFDeriv ℝ j (fun q ↦ Y (s, q)) q‖ =
          max ‖iteratedFDeriv ℝ j (fun q ↦ y (s, q)) q‖
            ‖iteratedFDeriv ℝ (j + 1) (fun q ↦ y (s, q)) q‖ := by
      have hz : (s, q) ∈ W := hUW ⟨hs, hq⟩
      have hyp := ((hyn _ hz).contDiffAt (hW.mem_nhds hz)).comp q
        (contDiffAt_const.prodMk contDiffAt_id)
      have hdp := (((contDiffOn_spatialFDeriv (n := (n : ℕ∞ω) + 1) hW hyn) _ hz).contDiffAt
        (hW.mem_nhds hz)).comp q (contDiffAt_const.prodMk contDiffAt_id)
      change ‖iteratedFDeriv ℝ j (fun q ↦ (y (s, q), spatialFDeriv (𝕜 := ℝ) y q s)) q‖ = _
      simp only [Function.comp_def] at hyp hdp
      rw [iteratedFDeriv_prodMk (hyp.of_le (show (n : ℕ∞ω) + 1 ≤ n + 1 + 1 from le_self_add)) hdp
        (show (j : ℕ∞ω) ≤ (n : ℕ∞ω) + 1 by exact_mod_cast hj.trans (Nat.le_succ n)),
        ContinuousMultilinearMap.opNorm_prod,
        norm_iteratedFDeriv_spatialFDeriv hW (hyn.differentiableOn (by simp)) hz]
    have hYinit : ∀ j ≤ n, ∀ q ∈ U,
        ‖iteratedFDeriv ℝ j (fun q ↦ Y (t₀, q)) q‖ ≤ D := by
      intro j hj q hq
      rw [hYbound t₀ ht₀ q hq j hj]
      exact max_le (hinit j (hj.trans (Nat.le_succ n)) q hq)
        (hinit (j + 1) (Nat.add_le_add_right hj 1) q hq)
    have hQbound : ∀ j ≤ n, ∀ s ∈ Icc a b, ∀ q ∈ U,
        ‖iteratedFDeriv ℝ j (fun q ↦ Q (s, q)) q‖ ≤ 2 * C := by
      intro j hj s hs q hq
      exact (norm_iteratedFDeriv_linearODEJetCoeff_le hj hW hAn (hUW ⟨hs, hq⟩)).trans
        (mul_le_mul_of_nonneg_left
          (max_le (hbound j (hj.trans (Nat.le_succ n)) s hs q hq)
            (hbound (j + 1) (Nat.add_le_add_right hj 1) s hs q hq)) (by norm_num))
    have h := ih hQ hY hQY hYinit hQbound
    rw [hYbound t ht p hp n le_rfl] at h
    exact (le_max_right _ _).trans (by simpa only [pow_succ, mul_assoc] using h)

/-- Parameter jets of a linear ODE are bounded by coefficient jets and initial jets.
The coefficient is `C^n` and the solution `C^(n+1)` on an open joint domain containing
`[a,b] × U`. The reference time may lie anywhere in the interval. No sign,
completeness or dimension hypotheses are needed, and the parameter and target universes
are independent. -/
theorem norm_iteratedFDeriv_le_exp_of_linearODE
    {P : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) {a b t₀ C D : ℝ} (ht₀ : t₀ ∈ Icc a b)
    {U : Set P} {W : Set (ℝ × P)} (hW : IsOpen W) (hUW : Icc a b ×ˢ U ⊆ W)
    {A : ℝ × P → F →L[ℝ] F} {y : ℝ × P → F}
    (hA : ContDiffOn ℝ n A W) (hy : ContDiffOn ℝ (n + 1) y W)
    (hode : ∀ z ∈ W, timeFDeriv y z.1 z.2 = A z (y z))
    (hinit : ∀ j ≤ n, ∀ q ∈ U, ‖iteratedFDeriv ℝ j (fun q ↦ y (t₀, q)) q‖ ≤ D)
    (hbound : ∀ j ≤ n, ∀ s ∈ Icc a b, ∀ q ∈ U,
      ‖iteratedFDeriv ℝ j (fun q ↦ A (s, q)) q‖ ≤ C)
    {t : ℝ} (ht : t ∈ Icc a b) {p : P} (hp : p ∈ U) :
    ‖iteratedFDeriv ℝ n (fun q ↦ y (t, q)) p‖ ≤
      D * Real.exp ((2 : ℝ) ^ n * C * |t - t₀|) := by
  -- Only the target needs lifting to a universe closed under spatial differentiation.
  let G := ULift.{u} F
  let e : F ≃ₗᵢ[ℝ] G := (LinearIsometryEquiv.ulift ℝ F).symm
  let : NormedAddCommGroup (G →L[ℝ] G) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (G →L[ℝ] G) := ContinuousLinearMap.toNormedSpace
  let L : (F →L[ℝ] F) →L[ℝ] (G →L[ℝ] G) :=
    (ContinuousLinearMap.compL ℝ G F G e.toLinearIsometry.toContinuousLinearMap).comp
      ((ContinuousLinearMap.compL ℝ G F F).flip e.symm.toLinearIsometry.toContinuousLinearMap)
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro A
    rw [one_mul]
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
    intro v
    change ‖e (A (e.symm v))‖ ≤ ‖A‖ * ‖v‖
    simpa only [LinearIsometryEquiv.norm_map] using A.le_opNorm (e.symm v)
  let Y : ℝ × P → G := e ∘ y
  let Q : ℝ × P → G →L[ℝ] G := L ∘ A
  have hY : ContDiffOn ℝ (n + 1) Y W := e.contDiff.comp_contDiffOn hy
  have hQ : ContDiffOn ℝ n Q W := by simpa only [Q] using L.contDiff.comp_contDiffOn hA
  have hQY : ∀ z ∈ W, timeFDeriv Y z.1 z.2 = Q z (Y z) := by
    intro z hz
    have hd := (hasDerivAt_parameterCurve
      (((hy _ hz).contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp))).congr_deriv
        (hode _ hz)
    have he := e.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt
      z.1 hd
    have hdY := hasDerivAt_parameterCurve
      (((hY _ hz).contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp))
    change timeFDeriv Y z.1 z.2 = e (A z (e.symm (e (y z))))
    rw [e.symm_apply_apply]
    exact hdY.unique he
  have hYinit : ∀ j ≤ n, ∀ q ∈ U,
      ‖iteratedFDeriv ℝ j (fun q ↦ Y (t₀, q)) q‖ ≤ D := by
    intro j hj q hq
    exact (e.norm_iteratedFDeriv_comp_left _ q j).trans_le (hinit j hj q hq)
  have hQbound : ∀ j ≤ n, ∀ s ∈ Icc a b, ∀ q ∈ U,
      ‖iteratedFDeriv ℝ j (fun q ↦ Q (s, q)) q‖ ≤ C := by
    intro j hj s hs q hq
    have hAp := ((hA _ (hUW ⟨hs, hq⟩)).contDiffAt
      (hW.mem_nhds (hUW ⟨hs, hq⟩))).comp q (contDiffAt_const.prodMk contDiffAt_id)
    exact (L.norm_iteratedFDeriv_comp_left hAp
      (by exact_mod_cast hj)).trans ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans
        (by simpa only [one_mul, Function.comp_def, id_eq] using hbound j hj s hs q hq))
  have h := norm_iteratedFDeriv_le_exp_of_linearODE_aux n ht₀ hW hUW
    hQ hY hQY hYinit hQbound ht hp
  exact (e.norm_iteratedFDeriv_comp_left _ p n).symm.trans_le h

end TauCeti
