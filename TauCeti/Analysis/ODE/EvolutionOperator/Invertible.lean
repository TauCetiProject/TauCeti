/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.ODE.EvolutionOperator.Basic
import TauCeti.Analysis.InnerProductSpace.L2.HilbertBasis
import TauCeti.Analysis.InnerProductSpace.Spectrum
import TauCeti.Analysis.Normed.Operator.Banach
import TauCeti.Analysis.Normed.Operator.CompactFamily
import TauCeti.Analysis.ODE.EnergyEstimate.Index
import TauCeti.Analysis.ODE.EnergyEstimate.Sobolev
import TauCeti.MeasureTheory.Function.Lp.Basic
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Invertibility of stationary first-order evolution operators

Let `ι : D →L[ℝ] H` be a bounded linear map from a real normed space `D` into a real Hilbert space
`H`, and let `A : D →L[ℝ] H` be symmetric with respect to `ι` (`⟪A x, ι y⟫ = ⟪ι x, A y⟫`). This
file establishes the exact Pythagorean energy identity, invertibility, sharp inverse norm bound,
and compact-family perturbation stability for `∂s + A : L²(ℝ; D) ∩ W^{1,2}(ℝ; H) → L²(ℝ; H)`.

## Main declarations

* Eigenbasis level (assuming a Hilbert basis `b` of `H` with `ι (a i) = b i` and
  `A (a i) = lam i • b i`, plus `A.IsInvertible` for invertibility/bounds):
  `norm_weakFDeriv_sq_add_norm_compLp_sq_eq_norm_stationaryEvolutionOperator_sq_of_hilbertBasis`,
  `norm_le_max_norm_inverse_one_mul_norm_stationaryEvolutionOperator_of_hilbertBasis`,
  `bijective_stationaryEvolutionOperator_of_hilbertBasis`,
  `isInvertible_stationaryEvolutionOperator_of_hilbertBasis`,
  `norm_inverse_stationaryEvolutionOperator_le_of_hilbertBasis`.
* Compact-resolvent level (assuming `IsCompactOperator ι`, `Function.Injective ι`, `ι`-symmetry,
  and `A.IsInvertible`): `isInvertible_stationaryEvolutionOperator_of_isCompactOperator`,
  `isInvertible_stationaryEvolutionOperator_neg_of_isCompactOperator`,
  `norm_inverse_stationaryEvolutionOperator_le_of_isCompactOperator`, and the Pythagorean identity
`norm_weakFDeriv_sq_add_norm_compLp_sq_eq_norm_stationaryEvolutionOperator_sq_of_isCompactOperator`.
* Compact-family perturbation stability (for arbitrary Banach `H` and `(mu, Omega, p)`):
  `exists_pos_isInvertible_stationaryEvolutionOperator_sub_smul_norm_inverse_le`.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc. 27
  (1995), 1–33.
* D. Salamon, *Lectures on Floer homology*, IAS/Park City Math. Ser. 7 (1999), Lecture 2.
-/

public section

noncomputable section

namespace TauCeti.WeakDerivStep

open MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology InnerProductSpace

/-! ### Eigenbasis energy identity, invertibility, and sharp inverse bound -/

section HilbertBasis

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem inner_apply_eq_mul_inner {ι A : D →L[ℝ] H} {s : Type*}
    (b : HilbertBasis s ℝ H) (a : s → D) (lam : s → ℝ)
    (hsym : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (haι : ∀ i : s, ι (a i) = b i) (haA : ∀ i : s, A (a i) = lam i • b i)
    (i : s) (x : D) :
    ⟪b i, A x⟫_ℝ = lam i * ⟪b i, ι x⟫_ℝ := by
  calc ⟪b i, A x⟫_ℝ = ⟪A x, ι (a i)⟫_ℝ := by rw [real_inner_comm, haι i]
    _ = ⟪ι x, lam i • b i⟫_ℝ := by rw [hsym x (a i), haA i]
    _ = lam i * ⟪b i, ι x⟫_ℝ := by rw [inner_smul_right, real_inner_comm]

private theorem norm_mode_sq_add_sq_eq {ι A : D →L[ℝ] H} {s : Type*}
    (b : HilbertBasis s ℝ H) (a : s → D) (lam : s → ℝ)
    (hsym : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (haι : ∀ i : s, ι (a i) = b i) (haA : ∀ i : s, A (a i) = lam i • b i)
    (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))
    (i : s) :
    ‖(innerSL ℝ (b i)).compLp ((ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLp
        (weakFDeriv (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) u))‖ ^ 2 +
      ‖(innerSL ℝ (b i)).compLp
        (A.compLp (prev (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) u))‖ ^ 2 =
      ‖(innerSL ℝ (b i)).compLp
        (stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2) ι A u)‖ ^ 2 := by
  let μ : Measure ℝ := volume.restrict ((⊤ : Opens ℝ) : Set ℝ)
  let ui := postcompBaseL (ι.compLpL 2 μ) (innerSL ℝ (b i)) u
  let AL : Lp (ℝ →L[ℝ] ℝ) ∞ μ :=
    (memLp_top_const (μ := μ) (lam i • ContinuousLinearMap.id ℝ ℝ)).toLp
  have hAL : AL =ᵐ[μ] fun _ ↦ lam i • ContinuousLinearMap.id ℝ ℝ := MemLp.coeFn_toLp _
  have htraj : trajectoryOperator AL ui =
      (innerSL ℝ (b i)).compLp
        (stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2) ι A u) :=
    trajectoryOperator_postcompBaseL ι A (innerSL ℝ (b i)) (lam i • ContinuousLinearMap.id ℝ ℝ)
      (inner_apply_eq_mul_inner b a lam hsym haι haA i) AL hAL u
  have hderiv : ‖weakFDeriv _ ui‖ = ‖(innerSL ℝ (b i)).compLp
      ((ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLp (weakFDeriv (ι.compLpL 2 μ) u))‖ := by
    rw [← ContinuousLinearMap.norm_compLp_apply_one (weakFDeriv _ ui)]
    exact congrArg norm (compLp_apply_weakFDeriv_postcompBaseL _ _ (1 : ℝ) u)
  have hAproj : (innerSL ℝ (b i)).compLp (A.compLp (prev (ι.compLpL 2 μ) u)) =
      lam i • prev _ ui := by
    rw [← ContinuousLinearMap.comp_compLp,
      show (innerSL ℝ (b i)).comp A = lam i • ((innerSL ℝ (b i)).comp ι) from
        ContinuousLinearMap.ext (inner_apply_eq_mul_inner b a lam hsym haι haA i),
      ContinuousLinearMap.smul_compLp, ContinuousLinearMap.comp_compLp, prev_postcompBaseL,
      ContinuousLinearMap.compLpL_apply]
  have hnormA : ‖(innerSL ℝ (b i)).compLp (A.compLp (prev (ι.compLpL 2 μ) u))‖ ^ 2 =
      (lam i) ^ 2 * ‖prev _ ui‖ ^ 2 := by
    rw [hAproj, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← hderiv, hnormA, ← htraj]
  exact norm_weakFDeriv_sq_add_mul_norm_prev_sq_eq_trajectoryOperator_sq (lam i) AL hAL ui

/-- **Pythagorean energy identity for a diagonalizable symmetric stationary operator.**
If `A : D →L[ℝ] H` is symmetric with respect to `ι : D →L[ℝ] H` and `H` has a Hilbert basis `b`
of eigenvectors `ι (a i) = b i`, `A (a i) = λ i • b i`, then every `u ∈ L²(ℝ; D) ∩ W^{1,2}(ℝ; H)`
satisfies `‖(ι u)'‖² + ‖A u‖² = ‖(∂s + A) u‖²`. Neither invertibility nor compactness is
required. -/
theorem norm_weakFDeriv_sq_add_norm_compLp_sq_eq_norm_stationaryEvolutionOperator_sq_of_hilbertBasis
    {ι A : D →L[ℝ] H} {s : Type*} (b : HilbertBasis s ℝ H) (a : s → D) (lam : s → ℝ)
    (hsym : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (haι : ∀ i : s, ι (a i) = b i) (haA : ∀ i : s, A (a i) = lam i • b i)
    (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    ‖weakFDeriv (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) u‖ ^ 2 +
      ‖A.compLp (prev (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) u)‖ ^ 2 =
      ‖stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2) ι A u‖ ^ 2 := by
  let w := (ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLp (weakFDeriv _ u)
  have h1 : HasSum (fun i ↦ ‖(innerSL ℝ (b i)).compLp w‖ ^ 2) (‖weakFDeriv _ u‖ ^ 2) := by
    rw [← ContinuousLinearMap.norm_compLp_apply_one (weakFDeriv _ u)]
    exact b.hasSum_norm_sq_compLp_innerSL w
  have h2 := b.hasSum_norm_sq_compLp_innerSL (A.compLp (prev _ u))
  have h3 := b.hasSum_norm_sq_compLp_innerSL
    (stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2) ι A u)
  rw [← funext (norm_mode_sq_add_sq_eq b a lam hsym haι haA u)] at h3
  exact (h1.add h2).unique h3

/-- **Sharp coercive lower bound for a diagonalizable invertible stationary operator.**
Under the eigenbasis hypotheses together with `hA : A.IsInvertible`, the graph norm is controlled
by `‖u‖ ≤ max ‖A.inverse‖ 1 * ‖(∂s + A) u‖`. -/
theorem norm_le_max_norm_inverse_one_mul_norm_stationaryEvolutionOperator_of_hilbertBasis
    {ι A : D →L[ℝ] H} {s : Type*} (b : HilbertBasis s ℝ H) (a : s → D) (lam : s → ℝ)
    (hsym : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (haι : ∀ i : s, ι (a i) = b i) (haA : ∀ i : s, A (a i) = lam i • b i)
    (hA : A.IsInvertible)
    (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    ‖u‖ ≤ max ‖A.inverse‖ 1 *
      ‖stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2) ι A u‖ := by
  set M : ℝ := max ‖A.inverse‖ 1
  have hprev_eq : prev _ u = A.inverse.compLp (A.compLp (prev _ u)) := by
    rw [← ContinuousLinearMap.comp_compLp,
      show A.inverse.comp A = ContinuousLinearMap.id ℝ D from
        ContinuousLinearMap.ext hA.inverse_apply_self, ContinuousLinearMap.id_compLp]
  have hprev_le : ‖prev _ u‖ ≤ M * ‖A.compLp (prev _ u)‖ :=
    (congrArg norm hprev_eq).trans_le <|
      (A.inverse.norm_compLp_le _).trans (by gcongr; exact le_max_left _ _)
  have hprev_sq : ‖prev _ u‖ ^ 2 ≤ M ^ 2 * ‖A.compLp (prev _ u)‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hprev_le 2
  have h1M2 : 1 ≤ M ^ 2 := by nlinarith [le_max_right ‖A.inverse‖ (1 : ℝ)]
  have hpyth :=
    norm_weakFDeriv_sq_add_norm_compLp_sq_eq_norm_stationaryEvolutionOperator_sq_of_hilbertBasis
      b a lam hsym haι haA u
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  rw [norm_sq_eq_norm_prev_sq_add_norm_weakFDeriv_sq, mul_pow, ← hpyth]
  nlinarith [sq_nonneg ‖weakFDeriv _ u‖]

/-- **Bijectivity of a diagonalizable invertible stationary evolution operator.**
If `A : D →L[ℝ] H` is invertible and symmetric with respect to `ι : D →L[ℝ] H`, and `H` has a
Hilbert basis of eigenvectors of `A`, then `∂s + A : L²(ℝ; D) ∩ W^{1,2}(ℝ; H) → L²(ℝ; H)` is
bijective. -/
theorem bijective_stationaryEvolutionOperator_of_hilbertBasis
    {ι A : D →L[ℝ] H} {s : Type*} (b : HilbertBasis s ℝ H) (a : s → D) (lam : s → ℝ)
    (hsym : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (haι : ∀ i : s, ι (a i) = b i) (haA : ∀ i : s, A (a i) = lam i • b i)
    (hA : A.IsInvertible) :
    Function.Bijective
      (stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2) ι A) := by
  let μ : Measure ℝ := volume.restrict ((⊤ : Opens ℝ) : Set ℝ)
  refine ⟨(injective_iff_map_eq_zero _).mpr fun u hu ↦ norm_le_zero_iff.mp <| by
    simpa only [hu, norm_zero, mul_zero] using
      norm_le_max_norm_inverse_one_mul_norm_stationaryEvolutionOperator_of_hilbertBasis
        b a lam hsym haι haA hA u, fun f ↦ ?_⟩
  obtain ⟨e, he⟩ := hA
  have hAe (x : D) : A x = e x := (congrArg (fun L ↦ L x) he).symm
  have hlam0 (i : s) : lam i ≠ 0 := fun h0 ↦ by
    have ha0 : a i = 0 := e.injective <| by rw [← hAe, haA i, h0, zero_smul, map_zero]
    have h1 := b.orthonormal.1 i
    rw [← haι i, ha0, map_zero, norm_zero] at h1
    exact zero_ne_one h1
  have hιe (i : s) : ι (e.symm (b i)) = (lam i)⁻¹ • b i := by
    have hesymm : e.symm (b i) = (lam i)⁻¹ • a i := e.injective <| by
      rw [e.apply_symm_apply, map_smul, ← hAe, haA i, smul_smul, inv_mul_cancel₀ (hlam0 i),
        one_smul]
    rw [hesymm, map_smul, haι i]
  -- Solve each scalar mode `u_i' + λ_i u_i = ⟪b_i, f⟫`.
  let fi (i : s) : Lp ℝ 2 μ := (innerSL ℝ (b i)).compLp f
  let AL (i : s) : Lp (ℝ →L[ℝ] ℝ) ∞ μ :=
    (memLp_top_const (μ := μ) (lam i • ContinuousLinearMap.id ℝ ℝ)).toLp
  have hAL (i : s) : AL i =ᵐ[μ] fun _ ↦ lam i • ContinuousLinearMap.id ℝ ℝ := MemLp.coeFn_toLp _
  have hsol (i : s) : ∃ u : WeakDerivStep volume ⊤ 2 (ContinuousLinearMap.id ℝ (Lp ℝ 2 μ)),
      trajectoryOperator (AL i) u = fi i :=
    (bijective_trajectoryOperator_const (A₀ := lam i • ContinuousLinearMap.id ℝ ℝ)
      (LinearMap.IsSymmetric.id.smul (conj_trivial _)) (abs_pos.mpr (hlam0 i))
      (fun v ↦ by simp) (AL i) (hAL i)).2 (fi i)
  choose ui hui using hsol
  let wi (i : s) : Lp ℝ 2 μ := (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).compLp (weakFDeriv _ (ui i))
  let vi (i : s) : Lp ℝ 2 μ := lam i • prev _ (ui i)
  have hadd_i (i : s) : wi i + vi i = fi i := by
    rw [← hui i]
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_add (wi i) (vi i),
      (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).coeFn_compLp (weakFDeriv _ (ui i)),
      Lp.coeFn_smul (lam i) (prev _ (ui i)), trajectoryOperator_apply_ae (AL i) (ui i),
      hAL i] with t hadd h1 h2 htraj hALt
    simp only [hadd, Pi.add_apply, wi, vi, h1, h2, Pi.smul_apply, htraj, hALt,
      ContinuousLinearMap.apply_apply, smul_apply, ContinuousLinearMap.id_apply]
    rfl
  have hpyth_i (i : s) : ‖wi i‖ ^ 2 + ‖vi i‖ ^ 2 = ‖fi i‖ ^ 2 := by
    rw [show ‖wi i‖ = ‖weakFDeriv _ (ui i)‖ from ContinuousLinearMap.norm_compLp_apply_one _,
      show ‖vi i‖ ^ 2 = (lam i) ^ 2 * ‖prev _ (ui i)‖ ^ 2 by
        simp only [vi, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs], ← hui i]
    exact norm_weakFDeriv_sq_add_mul_norm_prev_sq_eq_trajectoryOperator_sq (lam i) (AL i) (hAL i) _
  -- Both mode sequences are square-summable, synthesizing `w, v ∈ L²(ℝ; H)` with `w + v = f`.
  have hfi_sum : Summable fun i ↦ ‖fi i‖ ^ 2 := (b.hasSum_norm_sq_compLp_innerSL f).summable
  have hw_sum : HasSum (fun i ↦ (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLp (wi i))
      (∑' i, (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLp (wi i)) :=
    ((b.summable_compLp_toSpanSingleton_iff wi).mpr <| hfi_sum.of_nonneg_of_le (fun _ ↦ sq_nonneg _)
      fun i ↦ by linarith [hpyth_i i, sq_nonneg ‖vi i‖]).hasSum
  have hv_sum : HasSum (fun i ↦ (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLp (vi i))
      (∑' i, (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLp (vi i)) :=
    ((b.summable_compLp_toSpanSingleton_iff vi).mpr <| hfi_sum.of_nonneg_of_le (fun _ ↦ sq_nonneg _)
      fun i ↦ by linarith [hpyth_i i, sq_nonneg ‖wi i‖]).hasSum
  set w := ∑' i, (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLp (wi i)
  set v := ∑' i, (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLp (vi i)
  have hwv_eq : w + v = f := by
    have hsum : HasSum (fun i ↦ (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLp (fi i))
        (w + v) := by
      simpa only [← ContinuousLinearMap.compLpL_apply (p := 2) (μ := μ), ← map_add, hadd_i] using
        hw_sum.add hv_sum
    exact hsum.unique (b.hasSum_compLp_toSpanSingleton_innerSL f)
  -- Lift `v` via `A⁻¹`, lift `w` to `L²(ℝ; ℝ →L[ℝ] H)`, and pass to the closed weak-deriv graph.
  let uD : Lp D 2 μ := (e.symm : H →L[ℝ] D).compLp v
  let lift : H →L[ℝ] (ℝ →L[ℝ] H) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ H).toLinearIsometry.toContinuousLinearMap
  let wDer : Lp (ℝ →L[ℝ] H) 2 μ := lift.compLp w
  let modeLift (i : s) : WeakDerivStep volume ⊤ 2 (ContinuousLinearMap.id ℝ (Lp H 2 μ)) :=
    postcompBaseL (ContinuousLinearMap.id ℝ (Lp ℝ 2 μ))
      (ContinuousLinearMap.toSpanSingleton ℝ (b i)) (ui i)
  have hx_sum : HasSum (fun i ↦ prev _ (modeLift i)) (ι.compLp uD) := by
    have hterm (i : s) : (ι.comp (e.symm : H →L[ℝ] D)).compLp
        ((ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLp (vi i)) = prev _ (modeLift i) := by
      have hcomp : (ι.comp (e.symm : H →L[ℝ] D)).comp
          (ContinuousLinearMap.toSpanSingleton ℝ (b i)) =
          (lam i)⁻¹ • ContinuousLinearMap.toSpanSingleton ℝ (b i) := by ext; simp [hιe i]
      rw [← ContinuousLinearMap.comp_compLp, hcomp, ContinuousLinearMap.smul_compLp]
      dsimp only [vi, modeLift]
      rw [prev_postcompBaseL, ContinuousLinearMap.id_apply,
        ← ContinuousLinearMap.compLpL_apply (p := 2) (μ := μ), map_smul,
        ContinuousLinearMap.compLpL_apply, smul_smul, inv_mul_cancel₀ (hlam0 i), one_smul]
    simpa only [ContinuousLinearMap.compLpL_apply, hterm, ContinuousLinearMap.comp_compLp] using
      ((ι.comp (e.symm : H →L[ℝ] D)).compLpL 2 μ).hasSum hv_sum
  have hy_sum : HasSum (fun i ↦ weakFDeriv _ (modeLift i)) wDer := by
    have hterm (i : s) : lift.compLp
        ((ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLp (wi i)) =
        weakFDeriv _ (modeLift i) := by
      dsimp only [wi, modeLift]
      rw [weakFDeriv_postcompBaseL, ← ContinuousLinearMap.comp_compLp,
        ← ContinuousLinearMap.comp_compLp]
      congr 1; ext; simp [lift]
    simpa only [ContinuousLinearMap.compLpL_apply, hterm] using (lift.compLpL 2 μ).hasSum hw_sum
  have hweak : HasWeakFDerivOn volume ⊤ (ι.compLpL 2 μ uD) wDer :=
    hasWeakFDerivOn_of_hasSum (ContinuousLinearMap.id ℝ (Lp H 2 μ)) modeLift hx_sum hy_sum
  refine ⟨mk (ι.compLpL 2 μ) uD wDer hweak, ?_⟩
  rw [stationaryEvolutionOperator_apply, prev_mk, weakFDeriv_mk,
    show (ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLp wDer = w by
      rw [← ContinuousLinearMap.comp_compLp,
        show (ContinuousLinearMap.apply ℝ H (1 : ℝ)).comp lift = ContinuousLinearMap.id ℝ H by
          ext; simp [lift], ContinuousLinearMap.id_compLp],
    show A.compLp uD = v by
      rw [← ContinuousLinearMap.comp_compLp,
        show A.comp (e.symm : H →L[ℝ] D) = ContinuousLinearMap.id ℝ H by
          ext x; simp [hAe], ContinuousLinearMap.id_compLp],
    hwv_eq]

/-- **Invertibility of a diagonalizable symmetric stationary evolution operator.**
If `A : D →L[ℝ] H` is invertible and symmetric with respect to `ι : D →L[ℝ] H` and `H` has a
Hilbert basis of eigenvectors `ι (a i) = b i`, `A (a i) = lam i • b i`, then `∂s + A` is
invertible. Completeness of `D` is inferred from `hA : A.IsInvertible`. -/
theorem isInvertible_stationaryEvolutionOperator_of_hilbertBasis
    {ι A : D →L[ℝ] H} {s : Type*} (b : HilbertBasis s ℝ H) (a : s → D) (lam : s → ℝ)
    (hsym : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (haι : ∀ i : s, ι (a i) = b i) (haA : ∀ i : s, A (a i) = lam i • b i)
    (hA : A.IsInvertible) :
    (stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2) ι A).IsInvertible := by
  have : CompleteSpace D := ContinuousLinearMap.completeSpace_of_isInvertible hA
  exact ContinuousLinearMap.isInvertible_iff_bijective.mpr
    (bijective_stationaryEvolutionOperator_of_hilbertBasis b a lam hsym haι haA hA)

/-- **Sharp operator-norm bound on `(∂s + A)⁻¹` in an eigenbasis.**
If `A : D →L[ℝ] H` is invertible and symmetric with respect to `ι : D →L[ℝ] H` and `H` has a
Hilbert basis of eigenvectors `ι (a i) = b i`, `A (a i) = lam i • b i`, then
`‖(∂s + A)⁻¹‖ ≤ max ‖A.inverse‖ 1`. -/
theorem norm_inverse_stationaryEvolutionOperator_le_of_hilbertBasis
    {ι A : D →L[ℝ] H} {s : Type*} (b : HilbertBasis s ℝ H) (a : s → D) (lam : s → ℝ)
    (hsym : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (haι : ∀ i : s, ι (a i) = b i) (haA : ∀ i : s, A (a i) = lam i • b i)
    (hA : A.IsInvertible) :
    ‖(stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2) ι A).inverse‖ ≤
      max ‖A.inverse‖ 1 := by
  have hinv := isInvertible_stationaryEvolutionOperator_of_hilbertBasis b a lam hsym haι haA hA
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun f ↦ ?_
  simpa only [hinv.self_apply_inverse f] using
    norm_le_max_norm_inverse_one_mul_norm_stationaryEvolutionOperator_of_hilbertBasis
      b a lam hsym haι haA hA
      ((stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2) ι A).inverse f)

end HilbertBasis

/-! ### Coordinate-free compact-resolvent theorems -/

section CompactResolvent

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Pythagorean energy identity under compact resolvent.** If `ι : D →L[ℝ] H` is compact and
injective and `A : D →L[ℝ] H` is invertible and symmetric with respect to `ι`, then every
`u ∈ L²(ℝ; D) ∩ W^{1,2}(ℝ; H)` satisfies `‖(ι u)'‖² + ‖A u‖² = ‖(∂s + A) u‖²`. -/
theorem
  norm_weakFDeriv_sq_add_norm_compLp_sq_eq_norm_stationaryEvolutionOperator_sq_of_isCompactOperator
    {ι A : D →L[ℝ] H} (hιc : IsCompactOperator ι) (hιi : Function.Injective ι)
    (hsym : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) (hA : A.IsInvertible)
    (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    ‖weakFDeriv (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) u‖ ^ 2 +
      ‖A.compLp (prev (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) u)‖ ^ 2 =
      ‖stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2) ι A u‖ ^ 2 := by
  obtain ⟨_, b, a, lam, _, _, haι, _, haA⟩ :=
    ContinuousLinearMap.exists_hilbertBasis_of_isCompactOperator hιc hιi hsym hA
  exact norm_weakFDeriv_sq_add_norm_compLp_sq_eq_norm_stationaryEvolutionOperator_sq_of_hilbertBasis
    b a lam hsym haι haA u

/-- **Invertibility of `∂s + A` under compact resolvent.** If `ι : D →L[ℝ] H` is compact and
injective and `A : D →L[ℝ] H` is invertible and symmetric with respect to `ι`, then `∂s + A` is
invertible on `L²(ℝ; D) ∩ W^{1,2}(ℝ; H)`. -/
theorem isInvertible_stationaryEvolutionOperator_of_isCompactOperator {ι A : D →L[ℝ] H}
    (hιc : IsCompactOperator ι) (hιi : Function.Injective ι)
    (hsym : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) (hA : A.IsInvertible) :
    (stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2) ι A).IsInvertible := by
  obtain ⟨_, b, a, lam, _, _, haι, _, haA⟩ :=
    ContinuousLinearMap.exists_hilbertBasis_of_isCompactOperator hιc hιi hsym hA
  exact isInvertible_stationaryEvolutionOperator_of_hilbertBasis b a lam hsym haι haA hA

/-- **Invertibility of `∂s - A` under compact resolvent.** If `ι : D →L[ℝ] H` is compact and
injective and `A : D →L[ℝ] H` is invertible and symmetric with respect to `ι`, then `∂s - A` is
invertible on `L²(ℝ; D) ∩ W^{1,2}(ℝ; H)`. -/
theorem isInvertible_stationaryEvolutionOperator_neg_of_isCompactOperator {ι A : D →L[ℝ] H}
    (hιc : IsCompactOperator ι) (hιi : Function.Injective ι)
    (hsym : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) (hA : A.IsInvertible) :
    (stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2) ι (-A)).IsInvertible :=
  (isInvertible_stationaryEvolutionOperator_neg_iff (mu := volume) (p := 2) ι A).mpr
    (isInvertible_stationaryEvolutionOperator_of_isCompactOperator hιc hιi hsym hA)

/-- **Sharp inverse norm bound for `∂s + A` under compact resolvent.** If `ι : D →L[ℝ] H` is
compact and injective and `A : D →L[ℝ] H` is invertible and symmetric with respect to `ι`, then
`‖(∂s + A)⁻¹‖ ≤ max ‖A.inverse‖ 1`. -/
theorem norm_inverse_stationaryEvolutionOperator_le_of_isCompactOperator {ι A : D →L[ℝ] H}
    (hιc : IsCompactOperator ι) (hιi : Function.Injective ι)
    (hsym : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) (hA : A.IsInvertible) :
    ‖(stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2) ι A).inverse‖ ≤
      max ‖A.inverse‖ 1 := by
  obtain ⟨_, b, a, lam, _, _, haι, _, haA⟩ :=
    ContinuousLinearMap.exists_hilbertBasis_of_isCompactOperator hιc hιi hsym hA
  exact norm_inverse_stationaryEvolutionOperator_le_of_hilbertBasis b a lam hsym haι haA hA

end CompactResolvent

/-! ### Stability on compact families and small shifts -/

section CompactFamily

variable {P D H : Type*} [TopologicalSpace P]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- **Uniform invertibility and inverse bounds for small perturbations on a compact family.**
For `ι : D →L[ℝ] H` into a Banach space `H` and `A, B` continuous on a compact set `K` with each
`∂s + A q` invertible, there exist `ε > 0` and `C ≥ 0` such that `∂s + (A q - δ • B q)` is
invertible with inverse norm at most `C` for all `q ∈ K` and `|δ| ≤ ε`. -/
theorem exists_pos_isInvertible_stationaryEvolutionOperator_sub_smul_norm_inverse_le
    {mu : Measure ℝ} [IsFiniteMeasureOnCompacts mu] {Omega : Opens ℝ}
    {p : ENNReal} [Fact (1 ≤ p)]
    (ι : D →L[ℝ] H) {K : Set P} (hK : IsCompact K) (A B : P → D →L[ℝ] H)
    (hAcont : ContinuousOn A K) (hBcont : ContinuousOn B K)
    (hinv : ∀ q ∈ K,
      (stationaryEvolutionOperator (mu := mu) (Omega := Omega) (p := p) ι (A q)).IsInvertible) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ q ∈ K, ∀ δ : ℝ, |δ| ≤ ε →
      (stationaryEvolutionOperator (mu := mu) (Omega := Omega) (p := p) ι
          (A q - δ • B q)).IsInvertible ∧
        ‖(stationaryEvolutionOperator (mu := mu) (Omega := Omega) (p := p) ι
          (A q - δ • B q)).inverse‖ ≤ C := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨q₀, hq₀⟩
  · exact ⟨1, zero_lt_one, 0, le_rfl, fun _ hq ↦ False.elim hq⟩
  have : CompleteSpace (WeakDerivStep mu Omega p (ι.compLpL p (mu.restrict Omega))) :=
    ContinuousLinearMap.completeSpace_of_isInvertible (hinv q₀ hq₀)
  exact hK.exists_pos_isInvertible_sub_smul_norm_inverse_le
    (stationaryEvolutionOperator (mu := mu) (Omega := Omega) (p := p) ι)
    (continuous_stationaryEvolutionOperator (mu := mu) (Omega := Omega) (p := p) ι)
    A B hAcont hBcont hinv

end CompactFamily

end TauCeti.WeakDerivStep
