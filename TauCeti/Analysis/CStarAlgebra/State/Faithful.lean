/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.State.Space
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.CStarAlgebra.State.Spectrum

/-!
# Weighted sums of positive functionals and faithful states on separable C⋆-algebras

Norm-convergent nonnegative weighted sums of positive continuous linear functionals yield positive
continuous linear functionals with additive operator norms on C⋆-algebras, supplying faithful
states on nontrivial separable C⋆-algebras (and hence faithful separable GNS representations):

* `PositiveContinuousLinearMap.weightedSum`: given nonnegative weights `w : ι → ℝ` and
  `ω : ι → A →P[ℂ] ℂ` with `Summable fun i => w i * ‖(ω i : A →L[ℂ] ℂ)‖`, packages
  `∑' i, w i • ω i` as a positive continuous linear functional `A →P[ℂ] ℂ`, with evaluation lemmas
  `coe_weightedSum`, `hasSum_weightedSum_apply`, and `weightedSum_apply`.
* `PositiveContinuousLinearMap.weightedSum_apply_eq_zero_iff`: on any `0 ≤ a`, the weighted sum
  vanishes at `a` if and only if `w i = 0` or `ω i a = 0` for every `i`.
* `PositiveContinuousLinearMap.norm_weightedSum`: on a possibly nonunital C⋆-algebra, the operator
  norm of `weightedSum w ω hw hω` equals `∑' i, w i * ‖(ω i : A →L[ℂ] ℂ)‖`.
* `TauCeti.CStarAlgebra.exists_faithful_positiveContinuousLinearMap`,
  `TauCeti.exists_mem_stateSpace_faithful`: every nontrivial separable (possibly nonunital)
  C⋆-algebra admits a faithful state (strictly positive on nonzero positive elements, equivalently
  satisfying `φ (star a * a) = 0 → a = 0`).

## References

* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Theorem 3.4.2 and Exercise 3.7.
* B. Blackadar, *Operator Algebras*, II.6.2.4.
-/

public section

open Filter Finset Set WeakDual
open scoped CStarAlgebra ComplexOrder Topology

namespace PositiveContinuousLinearMap

section WeightedSum

variable {A ι : Type*} [SeminormedAddCommGroup A] [NormedSpace ℂ A] [PartialOrder A]

private theorem summable_weighted_smul {w : ι → ℝ} {ω : ι → A →P[ℂ] ℂ} (hw : ∀ i, 0 ≤ w i)
    (hω : Summable fun i => w i * ‖(ω i : A →L[ℂ] ℂ)‖) :
    Summable fun i : ι => w i • (ω i : A →L[ℂ] ℂ) :=
  .of_norm_bounded hω fun i => (norm_smul_of_nonneg (hw i) (ω i : A →L[ℂ] ℂ)).le

private theorem hasSum_clm_weighted_apply {w : ι → ℝ} {ω : ι → A →P[ℂ] ℂ} (hw : ∀ i, 0 ≤ w i)
    (hω : Summable fun i => w i * ‖(ω i : A →L[ℂ] ℂ)‖) (a : A) :
    HasSum (fun i : ι => w i • ω i a) ((∑' i : ι, w i • (ω i : A →L[ℂ] ℂ)) a) := by
  let ev : (A →L[ℂ] ℂ) →L[ℝ] ℂ := (ContinuousLinearMap.apply ℂ ℂ a).restrictScalars ℝ
  simpa [ev] using ev.hasSum (summable_weighted_smul hw hω).hasSum

/-- **Weighted sum of positive functionals.** Given nonnegative weights `w : ι → ℝ` and positive
continuous linear functionals `ω : ι → A →P[ℂ] ℂ` with `Summable (fun i => w i * ‖ω i‖)`,
`weightedSum w ω hw hω` is the norm-convergent sum `∑' i, w i • ω i` as a positive continuous
linear functional. -/
noncomputable def weightedSum (w : ι → ℝ) (ω : ι → A →P[ℂ] ℂ) (hw : ∀ i, 0 ≤ w i)
    (hω : Summable fun i => w i * ‖(ω i : A →L[ℂ] ℂ)‖) : A →P[ℂ] ℂ where
  toContinuousLinearMap := ∑' i : ι, w i • (ω i : A →L[ℂ] ℂ)
  monotone' a b hab := by
    have hclosed : IsClosed {z : ℂ | 0 ≤ z} := by
      have hset : {z : ℂ | 0 ≤ z} = Complex.re ⁻¹' Ici 0 ∩ Complex.im ⁻¹' {0} :=
        Set.ext fun _ => by simp [Complex.le_def, eq_comm]
      rw [hset]
      exact (isClosed_Ici.preimage Complex.continuous_re).inter
        (isClosed_singleton.preimage Complex.continuous_im)
    have hsub : 0 ≤ (∑' i : ι, w i • (ω i : A →L[ℂ] ℂ)) (b - a) := by
      refine hclosed.mem_of_tendsto (hasSum_clm_weighted_apply hw hω (b - a)) ?_
      exact .of_forall fun s => Set.mem_ofPred.2 <| sum_nonneg fun i _ =>
        smul_nonneg (hw i) (by rw [map_sub, sub_nonneg]; exact (ω i).monotone' hab)
    rwa [map_sub, sub_nonneg] at hsub

/-- The underlying continuous linear map of `weightedSum` is the norm-convergent sum of the scaled
functionals. -/
@[simp]
theorem coe_weightedSum (w : ι → ℝ) (ω : ι → A →P[ℂ] ℂ) (hw : ∀ i, 0 ≤ w i)
    (hω : Summable fun i => w i * ‖(ω i : A →L[ℂ] ℂ)‖) :
    (weightedSum w ω hw hω : A →L[ℂ] ℂ) = ∑' i : ι, w i • (ω i : A →L[ℂ] ℂ) := by
  rfl

/-- Pointwise `HasSum` expansion of `weightedSum`. -/
theorem hasSum_weightedSum_apply (w : ι → ℝ) (ω : ι → A →P[ℂ] ℂ) (hw : ∀ i, 0 ≤ w i)
    (hω : Summable fun i => w i * ‖(ω i : A →L[ℂ] ℂ)‖) (a : A) :
    HasSum (fun i : ι => w i • ω i a) (weightedSum w ω hw hω a) :=
  hasSum_clm_weighted_apply hw hω a

/-- Pointwise `tsum` formula for `weightedSum`. -/
theorem weightedSum_apply (w : ι → ℝ) (ω : ι → A →P[ℂ] ℂ) (hw : ∀ i, 0 ≤ w i)
    (hω : Summable fun i => w i * ‖(ω i : A →L[ℂ] ℂ)‖) (a : A) :
    weightedSum w ω hw hω a = ∑' i : ι, w i • ω i a :=
  (hasSum_weightedSum_apply w ω hw hω a).tsum_eq.symm

/-- On a nonnegative element `a`, `weightedSum w ω hw hω a = 0` if and only if `w i = 0` or
`ω i a = 0` for every `i`. -/
theorem weightedSum_apply_eq_zero_iff (w : ι → ℝ) (ω : ι → A →P[ℂ] ℂ) (hw : ∀ i, 0 ≤ w i)
    (hω : Summable fun i => w i * ‖(ω i : A →L[ℂ] ℂ)‖) {a : A} (ha : 0 ≤ a) :
    weightedSum w ω hw hω a = 0 ↔ ∀ i, w i = 0 ∨ ω i a = 0 := by
  refine ⟨fun h0 i => ?_, fun h => ?_⟩
  · have hre : HasSum (fun k : ι => w k * (ω k a).re) 0 := by
      simpa only [Function.comp_def, Complex.reCLM_apply, Complex.smul_re, smul_eq_mul, h0,
        Complex.zero_re] using Complex.reCLM.hasSum (hasSum_weightedSum_apply w ω hw hω a)
    have hterm_nonneg (k : ι) : 0 ≤ w k * (ω k a).re :=
      mul_nonneg (hw k) (Complex.le_def.1 ((ω k).map_nonneg ha)).1
    have hle : w i * (ω i a).re ≤ 0 := le_hasSum hre i fun k _ => hterm_nonneg k
    exact (mul_eq_zero.1 (le_antisymm hle (hterm_nonneg i))).imp_right fun hre_zero =>
      Complex.ext hre_zero (Complex.le_def.1 ((ω i).map_nonneg ha)).2.symm
  · rw [weightedSum_apply]
    convert tsum_zero with i
    rcases h i with hi | hi <;> simp [hi]

end WeightedSum

section CStarAlgebra

variable {A ι : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- On a C⋆-algebra, the operator norm of `weightedSum w ω hw hω` is the weighted sum of the
operator norms `‖ω i‖`. -/
theorem norm_weightedSum (w : ι → ℝ) (ω : ι → A →P[ℂ] ℂ) (hw : ∀ i, 0 ≤ w i)
    (hω : Summable fun i => w i * ‖(ω i : A →L[ℂ] ℂ)‖) :
    ‖(weightedSum w ω hw hω : A →L[ℂ] ℂ)‖ = ∑' i : ι, w i * ‖(ω i : A →L[ℂ] ℂ)‖ := by
  have hnorm_eq (i : ι) :
      ‖w i • (ω i : A →L[ℂ] ℂ)‖ = w i * ‖(ω i : A →L[ℂ] ℂ)‖ :=
    norm_smul_of_nonneg (hw i) (ω i : A →L[ℂ] ℂ)
  refine le_antisymm ?_ ?_
  · rw [coe_weightedSum]
    exact (norm_tsum_le_tsum_norm (by simpa only [hnorm_eq] using hω)).trans_eq
      (tsum_congr hnorm_eq)
  · refine le_of_tendsto hω.hasSum (.of_forall fun s => ?_)
    have hl := _root_.CStarAlgebra.increasingApproximateUnit A
    have := hl.neBot
    have hlhs : Tendsto (fun e => ∑ i ∈ s, w i * (ω i e).re)
        (_root_.CStarAlgebra.approximateUnit A)
        (𝓝 (∑ i ∈ s, w i * ‖(ω i : A →L[ℂ] ℂ)‖)) :=
      tendsto_finsetSum s fun i _ => tendsto_const_nhds.mul <| by
        simpa [Function.comp_def] using
          Complex.continuous_re.continuousAt.tendsto.comp ((ω i).tendsto_nhds_opNorm hl)
    have hrhs : Tendsto (fun e => (weightedSum w ω hw hω e).re)
        (_root_.CStarAlgebra.approximateUnit A) (𝓝 ‖(weightedSum w ω hw hω : A →L[ℂ] ℂ)‖) := by
      simpa [Function.comp_def] using Complex.continuous_re.continuousAt.tendsto.comp
        ((weightedSum w ω hw hω).tendsto_nhds_opNorm hl)
    refine le_of_tendsto_of_tendsto hlhs hrhs ?_
    filter_upwards [hl.eventually_nonneg] with e he
    have hre : HasSum (fun k : ι => w k * (ω k e).re) (weightedSum w ω hw hω e).re := by
      simpa only [Function.comp_def, Complex.reCLM_apply, Complex.smul_re, smul_eq_mul] using
        Complex.reCLM.hasSum (hasSum_weightedSum_apply w ω hw hω e)
    exact sum_le_hasSum s
      (fun k _ => mul_nonneg (hw k) (Complex.le_def.1 ((ω k).map_nonneg he)).1) hre

end CStarAlgebra

end PositiveContinuousLinearMap

namespace TauCeti

namespace CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- On a C⋆-algebra `A`, a map `f : A → α` has trivial zero locus on the positive cone if and only
if `f (star a * a) = 0` forces `a = 0`. -/
theorem forall_nonneg_apply_eq_zero_iff {α : Type*} [Zero α] (f : A → α) :
    (∀ a, 0 ≤ a → f a = 0 → a = 0) ↔ ∀ a, f (star a * a) = 0 → a = 0 := by
  refine ⟨fun h a hfa => star_mul_self_eq_zero.1 (h (star a * a) (star_mul_self_nonneg a) hfa),
    fun h a ha hfa => ?_⟩
  have hsq : star (CFC.sqrt a) * CFC.sqrt a = a := by
    rw [(CFC.sqrt_nonneg a).star_eq, CFC.sqrt_mul_sqrt_self a ha]
  have h0 : CFC.sqrt a = 0 := h (CFC.sqrt a) (hsq.symm ▸ hfa)
  rw [← hsq, h0, mul_zero]

/-- **Existence of a faithful norm-one positive functional on a separable C⋆-algebra.** Every
nontrivial separable (possibly nonunital) C⋆-algebra `A` admits `ψ : A →P[ℂ] ℂ` of norm `1` such
that `ψ a = 0 → a = 0` for `0 ≤ a` and `ψ (star a * a) = 0 → a = 0` for all `a : A`. -/
theorem exists_faithful_positiveContinuousLinearMap [TopologicalSpace.SeparableSpace A]
    [Nontrivial A] :
    ∃ ψ : A →P[ℂ] ℂ, ‖(ψ : A →L[ℂ] ℂ)‖ = 1 ∧
      (∀ a, 0 ≤ a → ψ a = 0 → a = 0) ∧ (∀ a, ψ (star a * a) = 0 → a = 0) := by
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq A
  choose ω hω_norm hω_val _ using fun n : ℕ =>
    exists_positiveContinuousLinearMap_apply_mul_self_eq_norm_sq (star_mul_self_nonneg (u n))
  let w : ℕ → ℝ := fun n => 1 / 2 / 2 ^ n
  have hw_pos (n : ℕ) : 0 < w n := by positivity
  have hsum : Summable fun n : ℕ => w n * ‖(ω n : A →L[ℂ] ℂ)‖ := by
    simpa [w, hω_norm] using summable_geometric_two' (1 : ℝ)
  let ψ := PositiveContinuousLinearMap.weightedSum w ω (fun n => (hw_pos n).le) hsum
  have hψ_norm : ‖(ψ : A →L[ℂ] ℂ)‖ = 1 := by
    rw [PositiveContinuousLinearMap.norm_weightedSum]
    simpa [w, hω_norm] using tsum_geometric_two' (1 : ℝ)
  have hstar (a : A) (hψa : ψ (star a * a) = 0) : a = 0 := by
    by_contra ha0
    have hall (n : ℕ) : ω n (star a * a) = 0 :=
      ((PositiveContinuousLinearMap.weightedSum_apply_eq_zero_iff w ω _ hsum
        (star_mul_self_nonneg a)).1 hψa n).resolve_left (hw_pos n).ne'
    have hpos : 0 < ‖star a * a‖ := norm_pos_iff.2 (star_mul_self_eq_zero.not.2 ha0)
    have hopen : IsOpen {b : A | ‖star a * a - star b * b‖ < ‖star a * a‖ / 3} :=
      isOpen_lt (by fun_prop) continuous_const
    obtain ⟨n, hn⟩ := hu.exists_mem_open hopen ⟨a, by simp [div_pos hpos three_pos]⟩
    have hn' : ‖star a * a - star (u n) * u n‖ < ‖star a * a‖ / 3 := hn
    have htri1 : ‖star a * a‖ ≤ ‖star (u n) * u n‖ + ‖star a * a - star (u n) * u n‖ := by
      simpa [sub_eq_add_neg, add_comm] using norm_add_le (star (u n) * u n)
        (star a * a - star (u n) * u n)
    have hdiff : ‖ω n (star (u n) * u n) - ω n (star a * a)‖ ≤
        ‖star a * a - star (u n) * u n‖ := by
      rw [← map_sub, norm_sub_rev (star a * a)]
      simpa [hω_norm n] using (ω n : A →L[ℂ] ℂ).le_opNorm (star (u n) * u n - star a * a)
    have hval_norm : ‖ω n (star (u n) * u n)‖ = ‖star (u n) * u n‖ := by
      rw [hω_val n, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    have hzero_n : ‖ω n (star a * a)‖ = 0 := by simp [hall n]
    have htri2 : ‖ω n (star (u n) * u n)‖ ≤
        ‖ω n (star a * a)‖ + ‖ω n (star (u n) * u n) - ω n (star a * a)‖ := by
      simpa [sub_eq_add_neg, add_comm] using
        norm_add_le (ω n (star a * a)) (ω n (star (u n) * u n) - ω n (star a * a))
    linarith
  exact ⟨ψ, hψ_norm, (forall_nonneg_apply_eq_zero_iff ψ).2 hstar, hstar⟩

end CStarAlgebra

/-- **Existence of a faithful state on a separable C⋆-algebra.** Every nontrivial separable
(possibly nonunital) C⋆-algebra `A` admits a state `φ ∈ stateSpace A` that is strictly positive on
nonzero positive elements, equivalently satisfying `φ (star a * a) = 0 → a = 0`. -/
theorem exists_mem_stateSpace_faithful {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [TopologicalSpace.SeparableSpace A] [Nontrivial A] :
    ∃ φ ∈ stateSpace A, (∀ a, 0 ≤ a → φ a = 0 → a = 0) ∧ (∀ a, φ (star a * a) = 0 → a = 0) := by
  obtain ⟨ψ, hnorm, hpos, hstar⟩ :=
    CStarAlgebra.exists_faithful_positiveContinuousLinearMap (A := A)
  exact ⟨StrongDual.toWeakDual (ψ : A →L[ℂ] ℂ), ψ.toWeakDual_mem_stateSpace_iff.2 hnorm,
    hpos, hstar⟩

end TauCeti
