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

The solution and its parameter derivative form a linear system on
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

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

-- Cache canonical operator structures privately across the augmented-system induction.
/-- The canonical normed group on an operator space. -/
private local instance operatorGroup {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] :
    NormedAddCommGroup (E →L[𝕜] F) := ContinuousLinearMap.toNormedAddCommGroup

/-- The canonical scalar action on an operator space. -/
private local instance operatorSpace {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] :
    NormedSpace 𝕜 (E →L[𝕜] F) := ContinuousLinearMap.toNormedSpace

namespace ContinuousLinearMap

section Coefficient

variable {𝕜 P F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

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
private def linearODEJetCoeffL :
    ((F →L[𝕜] F) × (P →L[𝕜] F →L[𝕜] F)) →L[𝕜]
      ((F × (P →L[𝕜] F)) →L[𝕜] (F × (P →L[𝕜] F))) := by
  let L : ((F →L[𝕜] F) × (P →L[𝕜] F →L[𝕜] F)) →ₗ[𝕜]
      ((F × (P →L[𝕜] F)) →L[𝕜] (F × (P →L[𝕜] F))) :=
    { toFun := fun z ↦ linearODEJetCoeff z.1 z.2
      map_add' := by
        intro z w
        ext v q <;> simp
      map_smul' := by intro c z; ext v q <;> simp [linearODEJetCoeff_apply] }
  refine LinearMap.mkContinuous (𝕜 := 𝕜) (𝕜₂ := 𝕜)
    (E := (F →L[𝕜] F) × (P →L[𝕜] F →L[𝕜] F))
    (F := (F × (P →L[𝕜] F)) →L[𝕜] (F × (P →L[𝕜] F))) L 2 ?_
  intro z
  exact (norm_linearODEJetCoeff_le z.1 z.2).trans (by
    calc ‖z.1‖ + ‖z.2‖ ≤ ‖z‖ + ‖z‖ := add_le_add (norm_fst_le z) (norm_snd_le z)
      _ = 2 * ‖z‖ := by ring)

@[simp] private theorem linearODEJetCoeffL_apply (z : (F →L[𝕜] F) × (P →L[𝕜] F →L[𝕜] F)) :
    linearODEJetCoeffL z = linearODEJetCoeff z.1 z.2 := by
  simp [linearODEJetCoeffL, LinearMap.mkContinuous_apply]

/-- The coefficient augmentation operator has norm at most two.
The inline canonical structure keeps the nested operator norm within instance-search depth. -/
private theorem norm_linearODEJetCoeffL_le :
    letI : NormedAddCommGroup ((F × (P →L[𝕜] F)) →L[𝕜] (F × (P →L[𝕜] F))) :=
      ContinuousLinearMap.toNormedAddCommGroup
    letI : NormedSpace 𝕜 ((F × (P →L[𝕜] F)) →L[𝕜] (F × (P →L[𝕜] F))) :=
      ContinuousLinearMap.toNormedSpace
    ‖linearODEJetCoeffL (𝕜 := 𝕜) (P := P) (F := F)‖ ≤ 2 := by
  unfold linearODEJetCoeffL
  exact LinearMap.mkContinuous_norm_le _ zero_le_two _

/-- The augmented coefficient is smooth whenever both coefficient inputs are smooth. -/
theorem _root_.ContDiffOn.linearODEJetCoeff {Q : Type*} [NormedAddCommGroup Q]
    [NormedSpace 𝕜 Q] {n : ℕ∞ω} {s : Set Q}
    {A : Q → F →L[𝕜] F} {B : Q → P →L[𝕜] F →L[𝕜] F}
    (hA : ContDiffOn 𝕜 n A s) (hB : ContDiffOn 𝕜 n B s) :
    ContDiffOn 𝕜 n (fun q ↦ linearODEJetCoeff (A q) (B q)) s := by
  simpa only [Function.comp_def, linearODEJetCoeffL_apply] using
    (linearODEJetCoeffL (𝕜 := 𝕜) (P := P) (F := F)).contDiff.comp_contDiffOn (hA.prodMk hB)

end Coefficient

end ContinuousLinearMap

namespace TauCeti

section JetDerivative

variable {𝕜 P F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Differentiating a linear ODE in a parameter gives the augmented linear system. -/
theorem hasDerivAt_linearODEJet
    {A : 𝕜 × P → F →L[𝕜] F} {y : 𝕜 × P → F} {t : 𝕜} {p : P}
    (hy : ContDiffAt 𝕜 (minSmoothness 𝕜 2) y (t, p))
    (hode : ∀ᶠ q in 𝓝 p, timeFDeriv y t q = A (t, q) (y (t, q)))
    (hA : DifferentiableAt 𝕜 A (t, p)) :
    HasDerivAt (fun s ↦ (y (s, p), spatialFDeriv (𝕜 := 𝕜) y p s))
      (linearODEJetCoeff (A (t, p)) (spatialFDeriv (𝕜 := 𝕜) A p t)
        (y (t, p), spatialFDeriv (𝕜 := 𝕜) y p t)) t := by
  have hy' := hy.differentiableAt (lt_of_lt_of_le (by norm_num) le_minSmoothness).ne'
  have hprod := (hA.hasFDerivAt.comp p (hasFDerivAt_prodMk_right t p)).clm_apply
    (hasFDerivAt_timeSlice hy')
  have hD := hasDerivAt_spatialFDeriv hy
  have heq : timeFDeriv y t =ᶠ[𝓝 p] fun q ↦ A (t, q) (y (t, q)) := hode
  simp only [Function.comp_apply] at hprod
  rw [heq.fderiv_eq, hprod.fderiv] at hD
  simpa only [linearODEJetCoeff_apply, spatialFDeriv_def] using
    (((hasDerivAt_parameterCurve hy').congr_deriv heq.eq_of_nhds).prodMk hD)

end JetDerivative

variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Coefficient jets of the augmented system use two adjacent coefficient jets. -/
private theorem norm_iteratedFDeriv_linearODEJetCoeff_le
    {k : ℕ} {A : ℝ × P → F →L[ℝ] F}
    {W : Set (ℝ × P)} (hW : IsOpen W) (hA : ContDiffOn ℝ (k + 1) A W)
    {t : ℝ} {p : P} (hz : (t, p) ∈ W) :
    ‖iteratedFDeriv ℝ k
      (fun q ↦ linearODEJetCoeff (A (t, q)) (spatialFDeriv (𝕜 := ℝ) A q t)) p‖ ≤
      2 * max ‖iteratedFDeriv ℝ k (fun q ↦ A (t, q)) p‖
        ‖iteratedFDeriv ℝ (k + 1) (fun q ↦ A (t, q)) p‖ := by
  have hAp := hA.contDiffAt_timeSlice hW hz
  have hDp := (hA.spatialFDeriv_of_isOpen hW le_rfl).contDiffAt_timeSlice hW hz
  have h := (linearODEJetCoeffL (𝕜 := ℝ) (P := P) (F := F)).norm_iteratedFDeriv_comp_left
    ((hAp.of_le le_self_add).prodMk hDp) le_rfl
  have hb := mul_le_mul_of_nonneg_right (norm_linearODEJetCoeffL_le (𝕜 := ℝ) (P := P) (F := F))
    (norm_nonneg (iteratedFDeriv ℝ k
      (fun q ↦ (A (t, q), spatialFDeriv (𝕜 := ℝ) A q t)) p))
  simpa only [Function.comp_def, linearODEJetCoeffL_apply,
    hA.norm_iteratedFDeriv_prodMk_spatialFDeriv hW hz] using h.trans hb

/-- Regularity and the ODE identity for the augmented solution/coefficient pair. -/
private theorem linearODEJet_contDiffOn_and_timeFDeriv
    {n : ℕ} {A : ℝ × P → F →L[ℝ] F} {y : ℝ × P → F} {W : Set (ℝ × P)}
    (hW : IsOpen W) (hA : ContDiffOn ℝ (n + 1) A W)
    (hy : ContDiffOn ℝ ((n : ℕ∞ω) + 1 + 1) y W)
    (hode : ∀ z ∈ W, timeFDeriv y z.1 z.2 = A z (y z)) :
    let Y : ℝ × P → F × (P →L[ℝ] F) := fun z ↦ (y z, spatialFDeriv y z.2 z.1)
    let Q : ℝ × P → (F × (P →L[ℝ] F)) →L[ℝ] (F × (P →L[ℝ] F)) :=
      fun z ↦ linearODEJetCoeff (A z) (spatialFDeriv A z.2 z.1)
    ContDiffOn ℝ n Q W ∧ ContDiffOn ℝ (n + 1) Y W ∧
      ∀ z ∈ W, timeFDeriv Y z.1 z.2 = Q z (Y z) := by
  dsimp only
  have hY : ContDiffOn ℝ (n + 1)
      (fun z ↦ (y z, spatialFDeriv (𝕜 := ℝ) y z.2 z.1)) W :=
    (hy.of_le le_self_add).prodMk (hy.spatialFDeriv_of_isOpen hW le_rfl)
  refine ⟨?_, hY, ?_⟩
  · exact (hA.of_le le_self_add).linearODEJetCoeff
      (hA.spatialFDeriv_of_isOpen hW le_rfl)
  · intro z hz
    have hyz := (hy _ hz).contDiffAt (hW.mem_nhds hz)
    have heq : ∀ᶠ q in 𝓝 z.2, timeFDeriv y z.1 q = A (z.1, q) (y (z.1, q)) := by
      filter_upwards [(continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
        (hW.mem_nhds hz)] with q hq
      exact hode _ hq
    have hd := hasDerivAt_linearODEJet (hyz.of_le (by simp; norm_cast; omega)) heq
      (((hA _ hz).contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp))
    have hdy := hasDerivAt_parameterCurve
      (((hY _ hz).contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp))
    exact hdy.unique hd

universe u v

/-- The induction takes place in a universe containing the parameter space, so that
`F × (P →L[ℝ] F)` is another admissible target. -/
private theorem norm_iteratedFDeriv_le_exp_of_linearODE_aux
    {P : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) {a b t₀ C D : ℝ} (ht₀ : t₀ ∈ Icc a b)
    {p : P} {W : Set (ℝ × P)} (hW : IsOpen W)
    (hpW : ∀ s ∈ Icc a b, (s, p) ∈ W)
    {A : ℝ × P → F →L[ℝ] F} {y : ℝ × P → F}
    (hA : ContDiffOn ℝ n A W) (hy : ContDiffOn ℝ (n + 1) y W)
    (hode : ∀ z ∈ W, timeFDeriv y z.1 z.2 = A z (y z))
    (hinit : ∀ j ≤ n, ‖iteratedFDeriv ℝ j (fun q ↦ y (t₀, q)) p‖ ≤ D)
    (hbound : ∀ j ≤ n, ∀ s ∈ Icc a b,
      ‖iteratedFDeriv ℝ j (fun q ↦ A (s, q)) p‖ ≤ C)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖iteratedFDeriv ℝ n (fun q ↦ y (t, q)) p‖ ≤
      D * Real.exp ((2 : ℝ) ^ n * C * |t - t₀|) := by
  induction n generalizing F C with
  | zero =>
    -- Grönwall controls the zeroth jet along the selected parameter.
    have hd (s : ℝ) (hs : s ∈ Icc a b) :
        HasDerivAt (fun r ↦ y (r, p)) (A (s, p) (y (s, p))) s :=
      (hasDerivAt_parameterCurve (((hy _ (hpW s hs)).contDiffAt
        (hW.mem_nhds (hpW s hs))).differentiableAt (by simp))).congr_deriv
        (hode (s, p) (hpW s hs))
    have h := norm_le_gronwallBound_of_norm_derivWithin_le ht₀
      (fun s hs ↦ (hd s hs).hasDerivWithinAt)
      (by simpa only [norm_iteratedFDeriv_zero] using hinit 0 le_rfl)
      (K := C) (ε := 0) (fun s hs ↦ by
        simpa only [add_zero] using ((A (s, p)).le_opNorm (y (s, p))).trans
          (mul_le_mul_of_nonneg_right
            (by simpa only [norm_iteratedFDeriv_zero] using hbound 0 le_rfl s hs)
            (norm_nonneg _))) t ht
    simpa only [norm_iteratedFDeriv_zero, pow_zero, one_mul, gronwallBound_ε0] using h
  | succ n ih =>
    -- Augment by the spatial derivative and apply the induction to the joint system.
    let Y : ℝ × P → F × (P →L[ℝ] F) := fun z ↦ (y z, spatialFDeriv (𝕜 := ℝ) y z.2 z.1)
    let Q : ℝ × P → (F × (P →L[ℝ] F)) →L[ℝ] (F × (P →L[ℝ] F)) :=
      fun z ↦ linearODEJetCoeff (A z) (spatialFDeriv (𝕜 := ℝ) A z.2 z.1)
    have hAn : ContDiffOn ℝ (n + 1) A W := by simpa only [Nat.cast_add, Nat.cast_one] using hA
    have hyn : ContDiffOn ℝ ((n : ℕ∞ω) + 1 + 1) y W := by
      simpa only [Nat.cast_add, Nat.cast_one] using hy
    obtain ⟨hQ, hY, hQY⟩ := linearODEJet_contDiffOn_and_timeFDeriv hW hAn hyn hode
    have hYbound (s : ℝ) (hs : s ∈ Icc a b) (j : ℕ) (hj : j ≤ n) :
        ‖iteratedFDeriv ℝ j (fun q ↦ Y (s, q)) p‖ =
          max ‖iteratedFDeriv ℝ j (fun q ↦ y (s, q)) p‖
            ‖iteratedFDeriv ℝ (j + 1) (fun q ↦ y (s, q)) p‖ :=
      (hyn.of_le (by
        exact_mod_cast ((Nat.add_le_add_right hj 1).trans
          (Nat.le_succ (n + 1))))).norm_iteratedFDeriv_prodMk_spatialFDeriv hW (hpW s hs)
    have hYinit : ∀ j ≤ n, ‖iteratedFDeriv ℝ j (fun q ↦ Y (t₀, q)) p‖ ≤ D := by
      intro j hj
      rw [hYbound t₀ ht₀ j hj]
      exact max_le (hinit j (hj.trans (Nat.le_succ n)))
        (hinit (j + 1) (Nat.add_le_add_right hj 1))
    have hQbound : ∀ j ≤ n, ∀ s ∈ Icc a b,
        ‖iteratedFDeriv ℝ j (fun q ↦ Q (s, q)) p‖ ≤ 2 * C := by
      intro j hj s hs
      exact (norm_iteratedFDeriv_linearODEJetCoeff_le hW
        (hAn.of_le (by exact_mod_cast Nat.add_le_add_right hj 1)) (hpW s hs)).trans
        (mul_le_mul_of_nonneg_left
          (max_le (hbound j (hj.trans (Nat.le_succ n)) s hs)
            (hbound (j + 1) (Nat.add_le_add_right hj 1) s hs)) (by norm_num))
    have h := ih hQ hY hQY hYinit hQbound
    rw [hYbound t ht n le_rfl] at h
    exact (le_max_right _ _).trans (by simpa only [pow_succ, mul_assoc] using h)

/-- Parameter jets of a linear ODE are bounded by coefficient jets and initial jets.
The coefficient is `C^n` and the solution `C^(n+1)` on an open joint domain containing
`[a,b] × {p}`. The reference time may lie anywhere in the interval. No sign,
completeness or dimension hypotheses are needed, and the parameter and target universes
are independent. -/
theorem norm_iteratedFDeriv_le_exp_of_linearODE
    {P : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) {a b t₀ C D : ℝ} (ht₀ : t₀ ∈ Icc a b)
    {p : P} {W : Set (ℝ × P)} (hW : IsOpen W)
    (hpW : ∀ s ∈ Icc a b, (s, p) ∈ W)
    {A : ℝ × P → F →L[ℝ] F} {y : ℝ × P → F}
    (hA : ContDiffOn ℝ n A W) (hy : ContDiffOn ℝ (n + 1) y W)
    (hode : ∀ z ∈ W, timeFDeriv y z.1 z.2 = A z (y z))
    (hinit : ∀ j ≤ n, ‖iteratedFDeriv ℝ j (fun q ↦ y (t₀, q)) p‖ ≤ D)
    (hbound : ∀ j ≤ n, ∀ s ∈ Icc a b,
      ‖iteratedFDeriv ℝ j (fun q ↦ A (s, q)) p‖ ≤ C)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖iteratedFDeriv ℝ n (fun q ↦ y (t, q)) p‖ ≤
      D * Real.exp ((2 : ℝ) ^ n * C * |t - t₀|) := by
  -- Only the target needs lifting to a universe closed under spatial differentiation.
  let G := ULift.{u} F
  let e : F ≃ₗᵢ[ℝ] G := (LinearIsometryEquiv.ulift ℝ F).symm
  let : NormedAddCommGroup (G →L[ℝ] G) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (G →L[ℝ] G) := ContinuousLinearMap.toNormedSpace
  let L : (F →L[ℝ] F) ≃ₗᵢ[ℝ] (G →L[ℝ] G) :=
    { toLinearEquiv := e.toContinuousLinearEquiv.conjContinuousAlgEquiv.toLinearEquiv
      norm_map' := fun A ↦ by
        have hconj : e.toContinuousLinearEquiv.conjContinuousAlgEquiv.toAlgEquiv A =
            (e : F →L[ℝ] G).comp (A.comp (e.symm : G →L[ℝ] F)) :=
          e.toContinuousLinearEquiv.conjContinuousAlgEquiv_apply A
        exact (congrArg norm hconj).trans (by
          rw [ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
            ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]) }
  have hL_apply (T : F →L[ℝ] F) (v : G) : L T v = e (T (e.symm v)) := by
    rfl
  let Y : ℝ × P → G := e ∘ y
  let Q : ℝ × P → G →L[ℝ] G := L ∘ A
  have hY : ContDiffOn ℝ (n + 1) Y W := e.contDiff.comp_contDiffOn hy
  have hQ : ContDiffOn ℝ n Q W := by simpa only [Q] using L.contDiff.comp_contDiffOn hA
  have hQY : ∀ z ∈ W, timeFDeriv Y z.1 z.2 = Q z (Y z) := by
    intro z hz
    have hd := (hasDerivAt_parameterCurve
      (((hy _ hz).contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp))).congr_deriv
        (hode _ hz)
    have he := e.hasFDerivAt.comp_hasDerivAt z.1 hd
    have hdY := hasDerivAt_parameterCurve
      (((hY _ hz).contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp))
    simpa [Q, Y, hL_apply] using hdY.unique he
  have hYinit : ∀ j ≤ n, ‖iteratedFDeriv ℝ j (fun q ↦ Y (t₀, q)) p‖ ≤ D := by
    intro j hj
    exact (e.norm_iteratedFDeriv_comp_left _ p j).trans_le (hinit j hj)
  have hQbound : ∀ j ≤ n, ∀ s ∈ Icc a b,
      ‖iteratedFDeriv ℝ j (fun q ↦ Q (s, q)) p‖ ≤ C := by
    intro j hj s hs
    exact (L.norm_iteratedFDeriv_comp_left _ p j).trans_le (hbound j hj s hs)
  have h := norm_iteratedFDeriv_le_exp_of_linearODE_aux n ht₀ hW hpW
    hQ hY hQY hYinit hQbound ht
  exact (e.norm_iteratedFDeriv_comp_left _ p n).symm.trans_le h

end TauCeti
