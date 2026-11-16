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
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Invertibility of stationary first-order evolution operators

Let `ι : D →L[ℝ] H` be a bounded linear map from a real normed space `D` into a real Hilbert space
`H`, and let `A : D →L[ℝ] H` be a bounded operator that is symmetric with respect to `ι`, meaning
`⟪A x, ι y⟫ = ⟪ι x, A y⟫` for all `x, y ∈ D`. This file establishes the exact energy identity,
invertibility, sharp inverse norm bound, and perturbation stability on compact families for the
stationary evolution operator

`∂s + A : L²(ℝ; D) ∩ W^{1,2}(ℝ; H) → L²(ℝ; H)`

realized by `TauCeti.WeakDerivStep.stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2)
ι A`.

## Method

1. **Eigenbasis diagonalization.** When `H` has a Hilbert basis `b` of eigenvectors `ι (a i) = b i`
   with `A (a i) = λ i • b i`, projecting along `⟪b i, ·⟫` via
   `TauCeti.WeakDerivStep.postcompBaseL` intertwines `∂s + A` with the scalar trajectory operators
   `d/ds + λ i` on `W^{1,2}(ℝ, ℝ)`. Applying the scalar Pythagorean identity mode by mode and
   summing via `HilbertBasis.hasSum_norm_sq_compLpL_innerSL` yields the exact energy identity
   `‖(ι u)'‖² + ‖A u‖² = ‖(∂s + A) u‖²`
   (`norm_weakFDeriv_sq_add_norm_compLpL_sq_eq_of_hilbertBasis`), without any invertibility or
   compactness hypothesis on `A` or `ι`.
2. **Sharp inverse bound and surjectivity.** When `A` is invertible, `‖u‖_{L²(ℝ; D)} ≤ ‖A⁻¹‖ ‖A u‖`
   combines with the energy identity to give the sharp lower bound
   `‖u‖ ≤ max ‖A⁻¹‖ 1 * ‖(∂s + A) u‖`, hence injectivity and `‖(∂s + A)⁻¹‖ ≤ max ‖A⁻¹‖ 1`.
   For surjectivity, each scalar equation `u_i' + λ_i u_i = ⟪b_i, f⟫` is solved by
   `bijective_trajectoryOperator_const`; the mode energy identities ensure `L²`-summability of the
   derivative and zero-order components, which synthesize `w, v ∈ L²(ℝ; H)` with `w + v = f` via
   `HilbertBasis.summable_compLpL_toSpanSingleton_iff`. Applying `A⁻¹` to `v` gives the `D`-valued
   path, and closedness of the weak-derivative graph shows `(ι (A⁻¹ v))' = w`.
3. **Compact-resolvent formulation and compact families.** When `ι` is compact and injective and `A`
   is invertible and symmetric with respect to `ι`, the resolvent `K = ι ∘ A⁻¹` is compact,
   symmetric, and injective on `H`, so the spectral theorem produces the required eigenbasis.
   Invertibility of `∂s - A` follows by time reflection
   (`isInvertible_stationaryEvolutionOperator_neg_of_isCompactOperator`), and
   `IsCompact.exists_mem_nhds_isInvertible_norm_inverse_le` yields uniform invertibility and inverse
   bounds for small perturbations `A p - δ • B p` along any compact family `p ∈ K`
   (`exists_pos_isInvertible_stationaryEvolutionOperator_sub_smul_norm_inverse_le`).

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc. 27
  (1995), 1–33 (invertibility and energy estimate for `d/ds + A` on `W^{1,2}(ℝ, H) ∩ L²(ℝ, D)`).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2.
-/

public section

noncomputable section

namespace TauCeti.WeakDerivStep

open MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology InnerProductSpace

/-! ### Scalar Pythagorean identity on the line -/

section Scalar

/-- On `W^{1,2}(ℝ, ℝ)`, a constant scalar coefficient `c` satisfies the exact Pythagorean identity
`‖u'‖² + c² ‖u‖² = ‖u' + c u‖²`. -/
private theorem norm_weakFDeriv_sq_add_mul_norm_prev_sq_eq_trajectoryOperator_sq (c : ℝ)
    (AL : Lp (ℝ →L[ℝ] ℝ) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun _ ↦ c • ContinuousLinearMap.id ℝ ℝ)
    (u : WeakDerivStep volume ⊤ 2
      (ContinuousLinearMap.id ℝ (Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    ‖weakFDeriv _ u‖ ^ 2 + c ^ 2 * ‖prev _ u‖ ^ 2 = ‖trajectoryOperator AL u‖ ^ 2 := by
  have hsym : ((c • ContinuousLinearMap.id ℝ ℝ) : ℝ →L[ℝ] ℝ).toLinearMap.IsSymmetric :=
    fun x y ↦ by
      simp only [ContinuousLinearMap.coe_coe, smul_apply, ContinuousLinearMap.id_apply,
        smul_eq_mul, RCLike.inner_apply, conj_trivial]
      ring
  have htest : ∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫ s, ‖deriv φ s‖ ^ 2) + c ^ 2 * (∫ s, ‖φ s‖ ^ 2) =
        ∫ s, ‖deriv φ s + (c • ContinuousLinearMap.id ℝ ℝ) (φ s)‖ ^ 2 := fun φ hφ hφc ↦ by
    have h := integral_norm_deriv_add_sq_eq (A := fun _ : ℝ ↦ c • ContinuousLinearMap.id ℝ ℝ)
      contDiff_const (fun _ _ ↦ hsym) hφ hφc
    have hA : (∫ s, ‖(c • ContinuousLinearMap.id ℝ ℝ) (φ s)‖ ^ 2) =
        c ^ 2 * ∫ s, ‖φ s‖ ^ 2 := by
      rw [← integral_const_mul]
      refine integral_congr_ae (.of_forall fun s ↦ ?_)
      simp only [smul_apply, ContinuousLinearMap.id_apply, norm_smul,
        Real.norm_eq_abs, mul_pow, sq_abs]
    simp only [deriv_const, zero_apply, inner_zero_right, integral_zero,
      sub_zero, hA] at h
    exact h.symm
  have hle := mul_norm_weakFDeriv_sq_add_mul_norm_prev_sq_le_of_forall_contDiff AL hAL
    (a := 1) (b := c ^ 2) (c := 1) (d := 0) (R := 0) (R' := 1) le_rfl zero_lt_one
    (fun φ hφ hφc ↦ by simp only [one_mul, zero_mul, add_zero, htest φ hφ hφc, le_rfl]) u
  have hge := mul_norm_weakFDeriv_sq_add_mul_norm_prev_sq_le_of_forall_contDiff AL hAL
    (a := -1) (b := -(c ^ 2)) (c := -1) (d := 0) (R := 0) (R' := 1) le_rfl zero_lt_one
    (fun φ hφ hφc ↦ by
      simp only [neg_mul, one_mul, zero_mul, add_zero]
      linarith [htest φ hφ hφc]) u
  simp only [one_mul, zero_mul, add_zero, neg_mul] at hle hge
  linarith

end Scalar

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
  calc ⟪b i, A x⟫_ℝ = ⟪A x, b i⟫_ℝ := real_inner_comm _ _
    _ = ⟪A x, ι (a i)⟫_ℝ := by rw [haι i]
    _ = ⟪ι x, A (a i)⟫_ℝ := hsym x (a i)
    _ = ⟪ι x, lam i • b i⟫_ℝ := by rw [haA i]
    _ = lam i * ⟪b i, ι x⟫_ℝ := by rw [inner_smul_right, real_inner_comm]

/-- **Pythagorean energy identity for a diagonalizable symmetric stationary operator.**
If `A : D →L[ℝ] H` is symmetric with respect to `ι : D →L[ℝ] H` and `H` has a Hilbert basis `b`
of eigenvectors `ι (a i) = b i`, `A (a i) = λ i • b i`, then every `u ∈ L²(ℝ; D) ∩ W^{1,2}(ℝ; H)`
satisfies `‖(ι u)'‖² + ‖A u‖² = ‖(∂s + A) u‖²`. Neither invertibility nor compactness is
required. -/
theorem norm_weakFDeriv_sq_add_norm_compLpL_sq_eq_of_hilbertBasis
    {ι A : D →L[ℝ] H} {s : Type*} (b : HilbertBasis s ℝ H) (a : s → D) (lam : s → ℝ)
    (hsym : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (haι : ∀ i : s, ι (a i) = b i) (haA : ∀ i : s, A (a i) = lam i • b i)
    (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    ‖weakFDeriv (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) u‖ ^ 2 +
      ‖A.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))
        (prev (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) u)‖ ^ 2 =
      ‖stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2) ι A u‖ ^ 2 := by
  let μ : Measure ℝ := volume.restrict ((⊤ : Opens ℝ) : Set ℝ)
  let w : Lp H 2 μ :=
    (ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL 2 μ (weakFDeriv (ι.compLpL 2 μ) u)
  have hw : ‖w‖ = ‖weakFDeriv (ι.compLpL 2 μ) u‖ := norm_compLpL_apply_one_weakFDeriv _ u
  have h1 : HasSum (fun i ↦ ‖(innerSL ℝ (b i)).compLpL 2 μ w‖ ^ 2)
      (‖weakFDeriv (ι.compLpL 2 μ) u‖ ^ 2) := by
    rw [← hw]
    exact b.hasSum_norm_sq_compLpL_innerSL w
  have h2 := b.hasSum_norm_sq_compLpL_innerSL (A.compLpL 2 μ (prev (ι.compLpL 2 μ) u))
  have h3 := b.hasSum_norm_sq_compLpL_innerSL
    (stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2) ι A u)
  have hmode : ∀ i : s,
      ‖(innerSL ℝ (b i)).compLpL 2 μ w‖ ^ 2 +
        ‖(innerSL ℝ (b i)).compLpL 2 μ (A.compLpL 2 μ (prev (ι.compLpL 2 μ) u))‖ ^ 2 =
      ‖(innerSL ℝ (b i)).compLpL 2 μ
        (stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2) ι A u)‖ ^ 2 := by
    intro i
    let ui := postcompBaseL (ι.compLpL 2 μ) (innerSL ℝ (b i)) u
    let AL : Lp (ℝ →L[ℝ] ℝ) ∞ μ :=
      (memLp_top_const (μ := μ) (lam i • ContinuousLinearMap.id ℝ ℝ)).toLp
    have hAL : AL =ᵐ[μ] fun _ ↦ lam i • ContinuousLinearMap.id ℝ ℝ := MemLp.coeFn_toLp _
    have hinter : ∀ x : D,
        innerSL ℝ (b i) (A x) =
          (lam i • ContinuousLinearMap.id ℝ ℝ) (innerSL ℝ (b i) (ι x)) :=
      fun x ↦ inner_apply_eq_mul_inner b a lam hsym haι haA i x
    have htraj : trajectoryOperator AL ui =
        (innerSL ℝ (b i)).compLpL 2 μ
          (stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2) ι A u) :=
      trajectoryOperator_postcompBaseL ι A (innerSL ℝ (b i))
        (lam i • ContinuousLinearMap.id ℝ ℝ) hinter AL hAL u
    have hderiv : ‖weakFDeriv _ ui‖ = ‖(innerSL ℝ (b i)).compLpL 2 μ w‖ := by
      rw [← norm_compLpL_apply_one_weakFDeriv _ ui]
      exact congrArg norm (compLpL_apply_one_weakFDeriv_postcompBaseL _ _ u)
    have hAproj : (innerSL ℝ (b i)).compLpL 2 μ (A.compLpL 2 μ (prev (ι.compLpL 2 μ) u)) =
        lam i • prev _ ui := by
      apply Lp.ext
      dsimp only [ui]
      rw [prev_postcompBaseL]
      filter_upwards [(innerSL ℝ (b i)).coeFn_compLpL (A.compLpL 2 μ (prev (ι.compLpL 2 μ) u)),
        A.coeFn_compLpL (prev (ι.compLpL 2 μ) u),
        Lp.coeFn_smul (lam i)
          ((innerSL ℝ (b i)).compLpL 2 μ (ι.compLpL 2 μ (prev (ι.compLpL 2 μ) u))),
        (innerSL ℝ (b i)).coeFn_compLpL (ι.compLpL 2 μ (prev (ι.compLpL 2 μ) u)),
        ι.coeFn_compLpL (prev (ι.compLpL 2 μ) u)] with t h1t h2t h3t h4t h5t
      rw [h1t, h2t, h3t, Pi.smul_apply, h4t, h5t]
      exact inner_apply_eq_mul_inner b a lam hsym haι haA i _
    have hnormA : ‖(innerSL ℝ (b i)).compLpL 2 μ
        (A.compLpL 2 μ (prev (ι.compLpL 2 μ) u))‖ ^ 2 = (lam i) ^ 2 * ‖prev _ ui‖ ^ 2 := by
      rw [hAproj, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [← hderiv, hnormA, ← htraj]
    exact norm_weakFDeriv_sq_add_mul_norm_prev_sq_eq_trajectoryOperator_sq (lam i) AL hAL ui
  have h3' : HasSum (fun i ↦ ‖(innerSL ℝ (b i)).compLpL 2 μ w‖ ^ 2 +
      ‖(innerSL ℝ (b i)).compLpL 2 μ (A.compLpL 2 μ (prev (ι.compLpL 2 μ) u))‖ ^ 2)
      (‖stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2) ι A u‖ ^ 2) := by
    have heq : (fun i ↦ ‖(innerSL ℝ (b i)).compLpL 2 μ w‖ ^ 2 +
        ‖(innerSL ℝ (b i)).compLpL 2 μ (A.compLpL 2 μ (prev (ι.compLpL 2 μ) u))‖ ^ 2) =
      fun i ↦ ‖(innerSL ℝ (b i)).compLpL 2 μ
        (stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2) ι A u)‖ ^ 2 :=
      funext hmode
    rw [heq]
    exact h3
  exact (h1.add h2).unique h3'

/-- **Sharp coercive lower bound for a diagonalizable invertible stationary operator.**
Under the hypotheses of `norm_weakFDeriv_sq_add_norm_compLpL_sq_eq_of_hilbertBasis` together with
`hA : A.IsInvertible`, the graph norm is controlled by
`‖u‖ ≤ max ‖A.inverse‖ 1 * ‖(∂s + A) u‖`. -/
theorem norm_le_max_norm_inverse_one_mul_stationaryEvolutionOperator_of_hilbertBasis
    {ι A : D →L[ℝ] H} {s : Type*} (b : HilbertBasis s ℝ H) (a : s → D) (lam : s → ℝ)
    (hsym : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (haι : ∀ i : s, ι (a i) = b i) (haA : ∀ i : s, A (a i) = lam i • b i)
    (hA : A.IsInvertible)
    (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    ‖u‖ ≤ max ‖A.inverse‖ 1 *
      ‖stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2) ι A u‖ := by
  let μ : Measure ℝ := volume.restrict ((⊤ : Opens ℝ) : Set ℝ)
  set M : ℝ := max ‖A.inverse‖ 1
  have hM1 : 1 ≤ M := le_max_right _ _
  have hMA : ‖A.inverse‖ ≤ M := le_max_left _ _
  have hprev_eq : prev (ι.compLpL 2 μ) u =
      A.inverse.compLpL 2 μ (A.compLpL 2 μ (prev (ι.compLpL 2 μ) u)) := by
    apply Lp.ext
    filter_upwards [A.inverse.coeFn_compLpL (A.compLpL 2 μ (prev (ι.compLpL 2 μ) u)),
      A.coeFn_compLpL (prev (ι.compLpL 2 μ) u)] with t h1 h2
    rw [h1, h2, hA.inverse_apply_self]
  have hprev_le : ‖prev (ι.compLpL 2 μ) u‖ ≤ M * ‖A.compLpL 2 μ (prev (ι.compLpL 2 μ) u)‖ := by
    calc ‖prev (ι.compLpL 2 μ) u‖
        = ‖A.inverse.compLpL 2 μ (A.compLpL 2 μ (prev (ι.compLpL 2 μ) u))‖ :=
          congrArg norm hprev_eq
      _ ≤ ‖A.inverse.compLpL 2 μ‖ * ‖A.compLpL 2 μ (prev (ι.compLpL 2 μ) u)‖ :=
          (A.inverse.compLpL 2 μ).le_opNorm _
      _ ≤ ‖A.inverse‖ * ‖A.compLpL 2 μ (prev (ι.compLpL 2 μ) u)‖ :=
          mul_le_mul_of_nonneg_right A.inverse.norm_compLpL_le (norm_nonneg _)
      _ ≤ M * ‖A.compLpL 2 μ (prev (ι.compLpL 2 μ) u)‖ :=
          mul_le_mul_of_nonneg_right hMA (norm_nonneg _)
  have hprev_sq : ‖prev (ι.compLpL 2 μ) u‖ ^ 2 ≤
      M ^ 2 * ‖A.compLpL 2 μ (prev (ι.compLpL 2 μ) u)‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hprev_le 2
  have hderiv_sq : ‖weakFDeriv (ι.compLpL 2 μ) u‖ ^ 2 ≤
      M ^ 2 * ‖weakFDeriv (ι.compLpL 2 μ) u‖ ^ 2 := by
    have h1M2 : 1 ≤ M ^ 2 := by nlinarith
    nlinarith [sq_nonneg ‖weakFDeriv (ι.compLpL 2 μ) u‖]
  have hpyth := norm_weakFDeriv_sq_add_norm_compLpL_sq_eq_of_hilbertBasis
    b a lam hsym haι haA u
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  rw [norm_sq_eq_norm_prev_sq_add_norm_weakFDeriv_sq, mul_pow, ← hpyth]
  linarith

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
  constructor
  · -- Injectivity from the coercive lower bound.
    refine (injective_iff_map_eq_zero _).mpr fun u hu ↦ ?_
    have hle := norm_le_max_norm_inverse_one_mul_stationaryEvolutionOperator_of_hilbertBasis
      b a lam hsym haι haA hA u
    rw [hu, norm_zero, mul_zero] at hle
    exact norm_le_zero_iff.mp hle
  · -- Surjectivity by mode-by-mode ODE solution and orthogonal synthesis.
    obtain ⟨e, he⟩ := hA
    have hAe : ∀ x : D, A x = e x := fun x ↦ (congrArg (fun L ↦ L x) he).symm
    have hlam0 : ∀ i : s, lam i ≠ 0 := fun i h0 ↦ by
      have ha0 : a i = 0 := e.injective <| by rw [← hAe, haA i, h0, zero_smul, map_zero]
      have hb0 : b i = 0 := by rw [← haι i, ha0, map_zero]
      have h1 : ‖b i‖ = 1 := b.orthonormal.1 i
      rw [hb0, norm_zero] at h1
      exact zero_ne_one h1
    have hιe : ∀ i : s, ι (e.symm (b i)) = (lam i)⁻¹ • b i := fun i ↦ by
      have hesymm : e.symm (b i) = (lam i)⁻¹ • a i := e.injective <| by
        rw [e.apply_symm_apply, map_smul, ← hAe, haA i, smul_smul, inv_mul_cancel₀ (hlam0 i),
          one_smul]
      rw [hesymm, map_smul, haι i]
    intro f
    -- Solve each scalar mode `u_i' + λ_i u_i = ⟪b_i, f⟫`.
    let fi : s → Lp ℝ 2 μ := fun i ↦ (innerSL ℝ (b i)).compLpL 2 μ f
    let AL : s → Lp (ℝ →L[ℝ] ℝ) ∞ μ :=
      fun i ↦ (memLp_top_const (μ := μ) (lam i • ContinuousLinearMap.id ℝ ℝ)).toLp
    have hAL : ∀ i : s, AL i =ᵐ[μ] fun _ ↦ lam i • ContinuousLinearMap.id ℝ ℝ :=
      fun i ↦ MemLp.coeFn_toLp _
    have hsol : ∀ i : s, ∃ u : WeakDerivStep volume ⊤ 2 (ContinuousLinearMap.id ℝ (Lp ℝ 2 μ)),
        trajectoryOperator (AL i) u = fi i := fun i ↦ by
      have hbij := bijective_trajectoryOperator_const
        (A₀ := lam i • ContinuousLinearMap.id ℝ ℝ)
        (fun x y ↦ by
          simp only [ContinuousLinearMap.coe_coe, smul_apply, ContinuousLinearMap.id_apply,
            smul_eq_mul, RCLike.inner_apply, conj_trivial]
          ring)
        (abs_pos.mpr (hlam0 i))
        (fun v ↦ by
          simp only [smul_apply, ContinuousLinearMap.id_apply, norm_smul,
            Real.norm_eq_abs, le_rfl])
        (AL i) (hAL i)
      exact hbij.2 (fi i)
    choose ui hui using hsol
    let wi : s → Lp ℝ 2 μ :=
      fun i ↦ (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).compLpL 2 μ (weakFDeriv _ (ui i))
    let vi : s → Lp ℝ 2 μ := fun i ↦ lam i • prev _ (ui i)
    have hadd_i : ∀ i : s, wi i + vi i = fi i := fun i ↦ by
      rw [← hui i]
      apply Lp.ext
      filter_upwards [Lp.coeFn_add (wi i) (vi i),
        (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).coeFn_compLpL (weakFDeriv _ (ui i)),
        Lp.coeFn_smul (lam i) (prev _ (ui i)),
        trajectoryOperator_apply_ae (AL i) (ui i),
        hAL i] with t hadd h1 h2 htraj hALt
      rw [hadd, Pi.add_apply, h1, h2, Pi.smul_apply, htraj, hALt]
      rfl
    have hpyth_i : ∀ i : s, ‖wi i‖ ^ 2 + ‖vi i‖ ^ 2 = ‖fi i‖ ^ 2 := fun i ↦ by
      have hw : ‖wi i‖ = ‖weakFDeriv _ (ui i)‖ := norm_compLpL_apply_one_weakFDeriv _ (ui i)
      have hv : ‖vi i‖ ^ 2 = (lam i) ^ 2 * ‖prev _ (ui i)‖ ^ 2 := by
        simp only [vi, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      rw [hw, hv, ← hui i]
      exact norm_weakFDeriv_sq_add_mul_norm_prev_sq_eq_trajectoryOperator_sq
        (lam i) (AL i) (hAL i) (ui i)
    -- Both mode sequences are square-summable, hence synthesize `w, v ∈ L²(ℝ; H)` with `w + v = f`.
    have hfi_sum : Summable fun i ↦ ‖fi i‖ ^ 2 := (b.hasSum_norm_sq_compLpL_innerSL f).summable
    have hwi_sum : Summable fun i ↦ ‖wi i‖ ^ 2 :=
      hfi_sum.of_nonneg_of_le (fun _ ↦ sq_nonneg _)
        (fun i ↦ by linarith [hpyth_i i, sq_nonneg ‖vi i‖])
    have hvi_sum : Summable fun i ↦ ‖vi i‖ ^ 2 :=
      hfi_sum.of_nonneg_of_le (fun _ ↦ sq_nonneg _)
        (fun i ↦ by linarith [hpyth_i i, sq_nonneg ‖wi i‖])
    let w : Lp H 2 μ := ∑' i, (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL 2 μ (wi i)
    let v : Lp H 2 μ := ∑' i, (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL 2 μ (vi i)
    have hw_sum : HasSum
        (fun i ↦ (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL 2 μ (wi i)) w :=
      ((b.summable_compLpL_toSpanSingleton_iff wi).mpr hwi_sum).hasSum
    have hv_sum : HasSum
        (fun i ↦ (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL 2 μ (vi i)) v :=
      ((b.summable_compLpL_toSpanSingleton_iff vi).mpr hvi_sum).hasSum
    have hwv_eq : w + v = f := by
      have hsum_add : HasSum
          (fun i ↦ (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL 2 μ (fi i)) (w + v) := by
        simpa only [← map_add, hadd_i] using hw_sum.add hv_sum
      exact hsum_add.unique (b.hasSum_compLpL_toSpanSingleton_innerSL f)
    -- Lift `v` to `L²(ℝ; D)` via `A⁻¹` and `w` to `L²(ℝ; ℝ →L[ℝ] H)`.
    let uD : Lp D 2 μ := (e.symm : H →L[ℝ] D).compLpL 2 μ v
    let lift : H →L[ℝ] (ℝ →L[ℝ] H) :=
      (ContinuousLinearMap.toSpanSingletonLIE ℝ H).toLinearIsometry.toContinuousLinearMap
    let wDer : Lp (ℝ →L[ℝ] H) 2 μ := lift.compLpL 2 μ w
    -- Show `HasWeakFDerivOn` via closedness of `weakDerivStepSubmodule`.
    let modeLift : s → WeakDerivStep volume ⊤ 2 (ContinuousLinearMap.id ℝ (Lp H 2 μ)) :=
      fun i ↦ postcompBaseL (ContinuousLinearMap.id ℝ (Lp ℝ 2 μ))
        (ContinuousLinearMap.toSpanSingleton ℝ (b i)) (ui i)
    have hx_sum : HasSum (fun i ↦ prev _ (modeLift i)) (ι.compLpL 2 μ uD) := by
      have hmap := ((ι.comp (e.symm : H →L[ℝ] D)).compLpL 2 μ).hasSum hv_sum
      have hlim : (ι.comp (e.symm : H →L[ℝ] D)).compLpL 2 μ v = ι.compLpL 2 μ uD := by
        apply Lp.ext
        filter_upwards [(ι.comp (e.symm : H →L[ℝ] D)).coeFn_compLpL v,
          ι.coeFn_compLpL uD, (e.symm : H →L[ℝ] D).coeFn_compLpL v] with t h1 h2 h3
        rw [h1, h2, h3, ContinuousLinearMap.comp_apply]
      have hterm : ∀ i : s,
          (ι.comp (e.symm : H →L[ℝ] D)).compLpL 2 μ
            ((ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL 2 μ (vi i)) =
          prev _ (modeLift i) := fun i ↦ by
        apply Lp.ext
        dsimp only [modeLift]
        rw [prev_postcompBaseL]
        filter_upwards [(ι.comp (e.symm : H →L[ℝ] D)).coeFn_compLpL
            ((ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL 2 μ (vi i)),
          (ContinuousLinearMap.toSpanSingleton ℝ (b i)).coeFn_compLpL (vi i),
          Lp.coeFn_smul (lam i) (prev _ (ui i)),
          (ContinuousLinearMap.toSpanSingleton ℝ (b i)).coeFn_compLpL (prev _ (ui i))]
          with t h1 h2 h3 h4
        rw [h1, h2, h3, Pi.smul_apply, ContinuousLinearMap.id_apply, h4,
          ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.toSpanSingleton_apply,
          ContinuousLinearMap.comp_apply, map_smul, map_smul, ContinuousLinearEquiv.coe_coe,
          hιe i, smul_smul, smul_eq_mul]
        rw [mul_assoc, mul_comm (prev _ (ui i) t), ← mul_assoc, mul_inv_cancel₀ (hlam0 i), one_mul]
      simpa only [hterm, hlim] using hmap
    have hy_sum : HasSum (fun i ↦ weakFDeriv _ (modeLift i)) wDer := by
      have hmap := (lift.compLpL 2 μ).hasSum hw_sum
      have hterm : ∀ i : s,
          lift.compLpL 2 μ ((ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL 2 μ (wi i)) =
            weakFDeriv _ (modeLift i) := fun i ↦ by
        apply Lp.ext
        dsimp only [modeLift]
        rw [weakFDeriv_postcompBaseL]
        filter_upwards [lift.coeFn_compLpL
            ((ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL 2 μ (wi i)),
          (ContinuousLinearMap.toSpanSingleton ℝ (b i)).coeFn_compLpL (wi i),
          (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).coeFn_compLpL (weakFDeriv _ (ui i)),
          (ContinuousLinearMap.compL ℝ ℝ ℝ H
            (ContinuousLinearMap.toSpanSingleton ℝ (b i))).coeFn_compLpL (weakFDeriv _ (ui i))]
          with t h1 h2 h3 h4
        rw [h1, h2, h3, h4]
        ext
        simp only [lift, LinearIsometry.coe_toContinuousLinearMap,
          LinearIsometryEquiv.coe_toLinearIsometry, ContinuousLinearMap.toSpanSingletonLIE_apply,
          ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.apply_apply,
          ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply, one_smul]
      simpa only [hterm] using hmap
    have hJ_sum : HasSum (fun i ↦ (modeLift i).1)
        (WithLp.toLp 2 (ι.compLpL 2 μ uD, wDer)) := by
      have hprod := (WithLp.prodContinuousLinearEquiv 2 ℝ (Lp H 2 μ)
        (Lp (ℝ →L[ℝ] H) 2 μ)).symm.toContinuousLinearMap.hasSum (hx_sum.prodMk hy_sum)
      have hterm : (fun i ↦ (modeLift i).1) = fun i ↦
          (WithLp.prodContinuousLinearEquiv 2 ℝ (Lp H 2 μ) (Lp (ℝ →L[ℝ] H) 2 μ)).symm
            (prev _ (modeLift i), weakFDeriv _ (modeLift i)) :=
        funext fun i ↦ WithLp.ofLp_injective 2
          (Prod.ext (by simp [prev_coe]) (by simp [weakFDeriv_coe]))
      rw [hterm]
      exact hprod
    have hmem : WithLp.toLp 2 (ι.compLpL 2 μ uD, wDer) ∈
        weakDerivStepSubmodule volume ⊤ 2 (ContinuousLinearMap.id ℝ (Lp H 2 μ)) :=
      (weakDerivStepSubmodule volume ⊤ 2 (ContinuousLinearMap.id ℝ (Lp H 2 μ))).isClosed
        |>.mem_of_tendsto hJ_sum
        (Eventually.of_forall fun t ↦ Submodule.sum_mem _ fun i _ ↦ (modeLift i).2)
    have hweak : HasWeakFDerivOn volume ⊤ (ι.compLpL 2 μ uD) wDer :=
      (mem_weakDerivStepSubmodule_iff_hasWeakFDerivOn
        (ContinuousLinearMap.id ℝ (Lp H 2 μ)) _).mp hmem
    refine ⟨mk (ι.compLpL 2 μ) uD wDer hweak, ?_⟩
    rw [stationaryEvolutionOperator_apply, prev_mk, weakFDeriv_mk]
    have hw_eq : (ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL 2 μ wDer = w := by
      apply Lp.ext
      filter_upwards [(ContinuousLinearMap.apply ℝ H (1 : ℝ)).coeFn_compLpL wDer,
        lift.coeFn_compLpL w] with t h1 h2
      rw [h1, h2]
      simp only [lift, LinearIsometry.coe_toContinuousLinearMap,
        LinearIsometryEquiv.coe_toLinearIsometry, ContinuousLinearMap.apply_apply,
        ContinuousLinearMap.toSpanSingletonLIE_apply, ContinuousLinearMap.toSpanSingleton_apply,
        one_smul]
    have hv_eq : A.compLpL 2 μ uD = v := by
      apply Lp.ext
      filter_upwards [A.coeFn_compLpL uD, (e.symm : H →L[ℝ] D).coeFn_compLpL v] with t h1 h2
      rw [h1, h2, hAe, ContinuousLinearEquiv.coe_coe, e.apply_symm_apply]
    rw [hw_eq, hv_eq, hwv_eq]

/-- **Invertibility of a diagonalizable symmetric stationary evolution operator.**
Completeness of `D` is inferred automatically from `hA : A.IsInvertible` and completeness of `H`. -/
theorem isInvertible_stationaryEvolutionOperator_of_hilbertBasis
    {ι A : D →L[ℝ] H} {s : Type*} (b : HilbertBasis s ℝ H) (a : s → D) (lam : s → ℝ)
    (hsym : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (haι : ∀ i : s, ι (a i) = b i) (haA : ∀ i : s, A (a i) = lam i • b i)
    (hA : A.IsInvertible) :
    (stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2) ι A).IsInvertible := by
  have : CompleteSpace D := ContinuousLinearMap.completeSpace_of_isInvertible hA
  exact ContinuousLinearMap.isInvertible_iff_bijective.mpr
    (bijective_stationaryEvolutionOperator_of_hilbertBasis b a lam hsym haι haA hA)

/-- **Sharp operator-norm bound on `(∂s + A)⁻¹` in an eigenbasis.** -/
theorem norm_inverse_stationaryEvolutionOperator_le_of_hilbertBasis
    {ι A : D →L[ℝ] H} {s : Type*} (b : HilbertBasis s ℝ H) (a : s → D) (lam : s → ℝ)
    (hsym : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ)
    (haι : ∀ i : s, ι (a i) = b i) (haA : ∀ i : s, A (a i) = lam i • b i)
    (hA : A.IsInvertible) :
    ‖(stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2) ι A).inverse‖ ≤
      max ‖A.inverse‖ 1 := by
  have hinv := isInvertible_stationaryEvolutionOperator_of_hilbertBasis b a lam hsym haι haA hA
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun f ↦ ?_
  have hle := norm_le_max_norm_inverse_one_mul_stationaryEvolutionOperator_of_hilbertBasis
    b a lam hsym haι haA hA
    ((stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2) ι A).inverse f)
  rwa [hinv.self_apply_inverse f] at hle

end HilbertBasis

/-! ### Coordinate-free compact-resolvent theorems -/

section CompactResolvent

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Spectral theorem for an invertible operator symmetric with respect to a compact injection.**
If `ι : D →L[ℝ] H` is compact and injective and `A : D →L[ℝ] H` is invertible and symmetric with
respect to `ι`, then the resolvent `K = ι ∘ A⁻¹` is compact, symmetric, and injective on `H`,
yielding a Hilbert basis `b` of `H` consisting of eigenvectors `ι (a i) = b i`,
`A (a i) = λ i • b i`. -/
private theorem exists_hilbertBasis_of_isCompactOperator {ι A : D →L[ℝ] H}
    (hιc : IsCompactOperator ι) (hιi : Function.Injective ι)
    (hsym : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) (hA : A.IsInvertible) :
    ∃ (s : Set H) (b : HilbertBasis s ℝ H) (a : s → D) (lam : s → ℝ),
      (∀ i, ι (a i) = b i) ∧ (∀ i, A (a i) = lam i • b i) := by
  obtain ⟨e, he⟩ := hA
  have hAe : ∀ x : D, A x = e x := fun x ↦ (congrArg (fun L ↦ L x) he).symm
  set K : H →L[ℝ] H := ι.comp (e.symm : H →L[ℝ] D) with hK
  have hKc : IsCompactOperator K := hιc.comp_clm (e.symm : H →L[ℝ] D)
  have hKs : (K : H →ₗ[ℝ] H).IsSymmetric := fun x y ↦ by
    have h := hsym (e.symm x) (e.symm y)
    simp only [hAe, e.apply_symm_apply] at h
    simpa only [hK, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe] using h.symm
  have hKi : LinearMap.ker (K : H →ₗ[ℝ] H) = ⊥ := by
    refine LinearMap.ker_eq_bot'.mpr fun x hx ↦ ?_
    have he0 : e.symm x = 0 := hιi (by simpa [hK] using hx)
    rw [← e.apply_symm_apply x, he0, map_zero]
  obtain ⟨s, b, nu, hb, hnu0, hev⟩ :=
    ContinuousLinearMap.exists_hilbertBasis_forall_hasEigenvector_ne_zero hKc hKs hKi
  refine ⟨s, b, fun i ↦ (nu i)⁻¹ • e.symm i, fun i ↦ (nu i)⁻¹, fun i ↦ ?_, fun i ↦ ?_⟩
  · have h : K i = nu i • (i : H) := (hev i).apply_eq_smul
    rw [hb]
    calc ι ((nu i)⁻¹ • e.symm i) = (nu i)⁻¹ • K i := by
          rw [map_smul, hK, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
      _ = i := by rw [h, smul_smul, inv_mul_cancel₀ (hnu0 i), one_smul]
  · rw [map_smul, hAe, e.apply_symm_apply, hb]

/-- **Pythagorean energy identity under compact resolvent.** -/
theorem norm_weakFDeriv_sq_add_norm_compLpL_sq_eq_of_isCompactOperator {ι A : D →L[ℝ] H}
    (hιc : IsCompactOperator ι) (hιi : Function.Injective ι)
    (hsym : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) (hA : A.IsInvertible)
    (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    ‖weakFDeriv (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) u‖ ^ 2 +
      ‖A.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))
        (prev (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) u)‖ ^ 2 =
      ‖stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2) ι A u‖ ^ 2 := by
  obtain ⟨s, b, a, lam, haι, haA⟩ := exists_hilbertBasis_of_isCompactOperator hιc hιi hsym hA
  exact norm_weakFDeriv_sq_add_norm_compLpL_sq_eq_of_hilbertBasis b a lam hsym haι haA u

/-- **Invertibility of `∂s + A` under compact resolvent.** -/
theorem isInvertible_stationaryEvolutionOperator_of_isCompactOperator {ι A : D →L[ℝ] H}
    (hιc : IsCompactOperator ι) (hιi : Function.Injective ι)
    (hsym : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) (hA : A.IsInvertible) :
    (stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2) ι A).IsInvertible := by
  obtain ⟨s, b, a, lam, haι, haA⟩ := exists_hilbertBasis_of_isCompactOperator hιc hιi hsym hA
  exact isInvertible_stationaryEvolutionOperator_of_hilbertBasis b a lam hsym haι haA hA

/-- **Invertibility of `∂s - A` under compact resolvent.** -/
theorem isInvertible_stationaryEvolutionOperator_neg_of_isCompactOperator {ι A : D →L[ℝ] H}
    (hιc : IsCompactOperator ι) (hιi : Function.Injective ι)
    (hsym : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) (hA : A.IsInvertible) :
    (stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2) ι (-A)).IsInvertible :=
  (isInvertible_stationaryEvolutionOperator_neg_iff (p := 2) ι A).mpr
    (isInvertible_stationaryEvolutionOperator_of_isCompactOperator hιc hιi hsym hA)

/-- **Sharp inverse norm bound for `∂s + A` under compact resolvent.** -/
theorem norm_inverse_stationaryEvolutionOperator_le_of_isCompactOperator {ι A : D →L[ℝ] H}
    (hιc : IsCompactOperator ι) (hιi : Function.Injective ι)
    (hsym : ∀ x y : D, ⟪A x, ι y⟫_ℝ = ⟪ι x, A y⟫_ℝ) (hA : A.IsInvertible) :
    ‖(stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2) ι A).inverse‖ ≤
      max ‖A.inverse‖ 1 := by
  obtain ⟨s, b, a, lam, haι, haA⟩ := exists_hilbertBasis_of_isCompactOperator hιc hιi hsym hA
  exact norm_inverse_stationaryEvolutionOperator_le_of_hilbertBasis b a lam hsym haι haA hA

end CompactResolvent

/-! ### Stability on compact families and small shifts -/

section CompactFamily

variable {P D H : Type*} [TopologicalSpace P]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Uniform invertibility and inverse bounds for small perturbations on a compact family.**
Let `ι : D →L[ℝ] H` be a compact injection and `K : Set P` a compact parameter set on which `A` and
`B` are continuous, with each `A p` invertible and symmetric with respect to `ι`. Then there exist
`ε > 0` and `C ≥ 0` such that for all `p ∈ K` and `|δ| ≤ ε`, the perturbed stationary evolution
operator `∂s + (A p - δ • B p)` is invertible with inverse norm at most `C`. Taking `B _ = ι` gives
uniform invertibility of exponentially weighted shifts `∂s + A p - δ ι`. -/
theorem exists_pos_isInvertible_stationaryEvolutionOperator_sub_smul_norm_inverse_le
    (ι : D →L[ℝ] H) (hιc : IsCompactOperator ι) (hιi : Function.Injective ι)
    {K : Set P} (hK : IsCompact K) (A B : P → D →L[ℝ] H)
    (hAcont : ContinuousOn A K) (hBcont : ContinuousOn B K)
    (hsym : ∀ p ∈ K, ∀ x y : D, ⟪A p x, ι y⟫_ℝ = ⟪ι x, A p y⟫_ℝ)
    (hAinv : ∀ p ∈ K, (A p).IsInvertible) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ p ∈ K, ∀ δ : ℝ, |δ| ≤ ε →
      (stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2) ι
          (A p - δ • B p)).IsInvertible ∧
        ‖(stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2) ι
          (A p - δ • B p)).inverse‖ ≤ C := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · exact ⟨1, zero_lt_one, 0, le_rfl, fun _ hp ↦ False.elim hp⟩
  have : CompleteSpace D := ContinuousLinearMap.completeSpace_of_isInvertible (hAinv p₀ hp₀)
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let L : K × ℝ →
      WeakDerivStep volume ⊤ 2 (ι.compLpL 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) →L[ℝ]
        Lp H 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
    fun q ↦ stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2) ι
      (A q.1 - q.2 • B q.1)
  have hL : Continuous L :=
    (continuous_stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2) ι).comp
      ((hAcont.domRestrict.comp continuous_fst).sub
        (continuous_snd.smul (hBcont.domRestrict.comp continuous_fst)))
  have hLinv : ∀ p ∈ (Set.univ : Set K), (L (p, (0 : ℝ))).IsInvertible := fun p _ ↦ by
    simpa only [L, zero_smul, sub_zero] using
      isInvertible_stationaryEvolutionOperator_of_isCompactOperator hιc hιi
        (hsym p p.2) (hAinv p p.2)
  obtain ⟨V, hV, C, hC, hVC⟩ :=
    isCompact_univ.exists_mem_nhds_isInvertible_norm_inverse_le L 0
      (fun _ _ ↦ hL.continuousAt) hLinv
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨r / 2, half_pos hr, C, hC, fun p hp δ hδ ↦ hVC ⟨p, hp⟩ (Set.mem_univ _) δ (hball ?_)⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero]
  linarith

end CompactFamily

end TauCeti.WeakDerivStep
