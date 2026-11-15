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
# Geometric series of positive functionals and faithful states on separable C⋆-algebras

A uniformly norm-bounded sequence `ω : ℕ → A →P[ℂ] ℂ` of positive continuous linear functionals on
a possibly nonunital C⋆-algebra `A` can be summed with geometric weights `2⁻¹ ^ (n + 1)` in the
operator norm of `A →L[ℂ] ℂ`:

* `PositiveContinuousLinearMap.geometricSeries`: the weighted sum
  `∑' n : ℕ, (1 / 2 / 2 ^ n : ℝ) • ω n : A →P[ℂ] ℂ`.
* `PositiveContinuousLinearMap.norm_geometricSeries`: its operator norm equals
  `∑' n : ℕ, (1 / 2 / 2 ^ n) * ‖ω n‖`; in particular it is `1` when every `ω n` has norm `1`
  (`PositiveContinuousLinearMap.norm_geometricSeries_eq_one`).
* `PositiveContinuousLinearMap.geometricSeries_apply_eq_zero_iff`: on any `0 ≤ a`, the series
  vanishes at `a` if and only if every `ω n a = 0`.

Choosing a dense sequence `u : ℕ → A` in a nontrivial separable C⋆-algebra `A` and norm-one
positive functionals `ω n` attaining `‖star (u n) * u n‖` at `star (u n) * u n` yields a faithful
state (`TauCeti.CStarAlgebra.exists_faithful_positiveContinuousLinearMap`,
`TauCeti.exists_mem_stateSpace_faithful`).

## References

* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Theorem 3.4.2 and Exercise 3.7.
* B. Blackadar, *Operator Algebras*, II.6.2.4.
-/

public section

open Filter Finset Set WeakDual
open scoped CStarAlgebra ComplexOrder Topology

namespace PositiveContinuousLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private theorem geomWeight_pos (n : ℕ) : (0 : ℝ) < 1 / 2 / 2 ^ n := by positivity

omit [StarOrderedRing A] in
private theorem summable_geometricWeight_mul_norm {ω : ℕ → A →P[ℂ] ℂ}
    (hω : ∃ C, ∀ n, ‖(ω n : A →L[ℂ] ℂ)‖ ≤ C) :
    Summable fun n : ℕ => (1 / 2 / 2 ^ n : ℝ) * ‖(ω n : A →L[ℂ] ℂ)‖ := by
  obtain ⟨C, hC⟩ := hω
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_geometric_two' (max C 0))
  calc
    (1 / 2 / 2 ^ n : ℝ) * ‖(ω n : A →L[ℂ] ℂ)‖ ≤ (1 / 2 / 2 ^ n : ℝ) * max C 0 :=
      mul_le_mul_of_nonneg_left ((hC n).trans (le_max_left C 0)) (geomWeight_pos n).le
    _ = max C 0 / 2 / 2 ^ n := by ring

omit [StarOrderedRing A] in
/-- For any uniformly norm-bounded sequence `ω : ℕ → A →P[ℂ] ℂ`, the geometric series
`∑' n, (1 / 2 / 2 ^ n : ℝ) • ω n` converges in the operator norm of `A →L[ℂ] ℂ`. -/
theorem summable_geometricWeight_smul {ω : ℕ → A →P[ℂ] ℂ}
    (hω : ∃ C, ∀ n, ‖(ω n : A →L[ℂ] ℂ)‖ ≤ C) :
    Summable fun n : ℕ => (1 / 2 / 2 ^ n : ℝ) • (ω n : A →L[ℂ] ℂ) :=
  .of_norm_bounded (summable_geometricWeight_mul_norm hω) fun n =>
    (norm_smul_of_nonneg (geomWeight_pos n).le (ω n : A →L[ℂ] ℂ)).le

omit [StarOrderedRing A] in
private theorem hasSum_clm_geometricWeight_apply {ω : ℕ → A →P[ℂ] ℂ}
    (hω : ∃ C, ∀ n, ‖(ω n : A →L[ℂ] ℂ)‖ ≤ C) (a : A) :
    HasSum (fun n : ℕ => (1 / 2 / 2 ^ n : ℝ) • ω n a)
      ((∑' n : ℕ, (1 / 2 / 2 ^ n : ℝ) • (ω n : A →L[ℂ] ℂ)) a) := by
  let ev : (A →L[ℂ] ℂ) →L[ℝ] ℂ := (ContinuousLinearMap.apply ℂ ℂ a).restrictScalars ℝ
  simpa [ev] using ev.hasSum (summable_geometricWeight_smul hω).hasSum

/-- **Geometric series of positive functionals.** Given a uniformly norm-bounded sequence
`ω : ℕ → A →P[ℂ] ℂ`, `geometricSeries ω hω` is the norm-convergent series
`∑' n, (1 / 2 / 2 ^ n : ℝ) • ω n` as a positive continuous linear functional. -/
noncomputable def geometricSeries (ω : ℕ → A →P[ℂ] ℂ)
    (hω : ∃ C, ∀ n, ‖(ω n : A →L[ℂ] ℂ)‖ ≤ C) : A →P[ℂ] ℂ :=
  .mk₀ (∑' n : ℕ, (1 / 2 / 2 ^ n : ℝ) • (ω n : A →L[ℂ] ℂ)) fun a ha => by
    have hclosed : IsClosed {z : ℂ | 0 ≤ z} := by
      have hset : {z : ℂ | 0 ≤ z} = Complex.re ⁻¹' Ici 0 ∩ Complex.im ⁻¹' {0} :=
        Set.ext fun _ => by simp [Complex.le_def, eq_comm]
      rw [hset]
      exact (isClosed_Ici.preimage Complex.continuous_re).inter
        (isClosed_singleton.preimage Complex.continuous_im)
    refine hclosed.mem_of_tendsto (hasSum_clm_geometricWeight_apply hω a).tendsto_sum_nat ?_
    exact .of_forall fun s =>
      sum_nonneg fun n _ => smul_nonneg (geomWeight_pos n).le ((ω n).map_nonneg ha)

@[simp]
theorem coe_geometricSeries (ω : ℕ → A →P[ℂ] ℂ) (hω : ∃ C, ∀ n, ‖(ω n : A →L[ℂ] ℂ)‖ ≤ C) :
    (geometricSeries ω hω : A →L[ℂ] ℂ) = ∑' n : ℕ, (1 / 2 / 2 ^ n : ℝ) • (ω n : A →L[ℂ] ℂ) :=
  toContinuousLinearMap_mk₀ _ _

/-- Pointwise `HasSum` expansion of `geometricSeries`. -/
theorem hasSum_geometricSeries_apply (ω : ℕ → A →P[ℂ] ℂ)
    (hω : ∃ C, ∀ n, ‖(ω n : A →L[ℂ] ℂ)‖ ≤ C) (a : A) :
    HasSum (fun n : ℕ => (1 / 2 / 2 ^ n : ℝ) • ω n a) (geometricSeries ω hω a) := by
  simpa only [geometricSeries, mk₀_apply] using hasSum_clm_geometricWeight_apply hω a

/-- Pointwise `tsum` formula for `geometricSeries`. -/
theorem geometricSeries_apply (ω : ℕ → A →P[ℂ] ℂ)
    (hω : ∃ C, ∀ n, ‖(ω n : A →L[ℂ] ℂ)‖ ≤ C) (a : A) :
    geometricSeries ω hω a = ∑' n : ℕ, (1 / 2 / 2 ^ n : ℝ) • ω n a :=
  (hasSum_geometricSeries_apply ω hω a).tsum_eq.symm

/-- On a nonnegative element `a`, `geometricSeries ω hω a = 0` if and only if `ω n a = 0` for all
`n : ℕ`. -/
theorem geometricSeries_apply_eq_zero_iff (ω : ℕ → A →P[ℂ] ℂ)
    (hω : ∃ C, ∀ n, ‖(ω n : A →L[ℂ] ℂ)‖ ≤ C) {a : A} (ha : 0 ≤ a) :
    geometricSeries ω hω a = 0 ↔ ∀ n, ω n a = 0 := by
  refine ⟨fun h0 n => ?_, fun h => by simp [geometricSeries_apply, h]⟩
  have hre : HasSum (fun k : ℕ => (1 / 2 / 2 ^ k : ℝ) * (ω k a).re) 0 := by
    simpa only [Function.comp_def, Complex.reCLM_apply, Complex.smul_re, smul_eq_mul, h0,
      Complex.zero_re] using Complex.reCLM.hasSum (hasSum_geometricSeries_apply ω hω a)
  have hterm_nonneg (k : ℕ) : 0 ≤ (1 / 2 / 2 ^ k : ℝ) * (ω k a).re :=
    mul_nonneg (geomWeight_pos k).le (Complex.le_def.1 ((ω k).map_nonneg ha)).1
  have hle : (1 / 2 / 2 ^ n : ℝ) * (ω n a).re ≤ 0 :=
    le_hasSum hre n fun k _ => hterm_nonneg k
  have hre_zero : (ω n a).re = 0 :=
    (mul_eq_zero.1 (le_antisymm hle (hterm_nonneg n))).resolve_left (geomWeight_pos n).ne'
  exact Complex.ext hre_zero (Complex.le_def.1 ((ω n).map_nonneg ha)).2.symm

/-- The operator norm of `geometricSeries ω hω` is the weighted sum of the norms `‖ω n‖`. -/
theorem norm_geometricSeries (ω : ℕ → A →P[ℂ] ℂ) (hω : ∃ C, ∀ n, ‖(ω n : A →L[ℂ] ℂ)‖ ≤ C) :
    ‖(geometricSeries ω hω : A →L[ℂ] ℂ)‖ =
      ∑' n : ℕ, (1 / 2 / 2 ^ n : ℝ) * ‖(ω n : A →L[ℂ] ℂ)‖ := by
  have hsum_norm := summable_geometricWeight_mul_norm hω
  have hnorm_eq (n : ℕ) :
      ‖(1 / 2 / 2 ^ n : ℝ) • (ω n : A →L[ℂ] ℂ)‖ = (1 / 2 / 2 ^ n : ℝ) * ‖(ω n : A →L[ℂ] ℂ)‖ :=
    norm_smul_of_nonneg (geomWeight_pos n).le (ω n : A →L[ℂ] ℂ)
  refine le_antisymm ?_ ?_
  · rw [coe_geometricSeries]
    exact (norm_tsum_le_tsum_norm (by simpa only [hnorm_eq] using hsum_norm)).trans_eq
      (tsum_congr hnorm_eq)
  · refine le_of_tendsto hsum_norm.hasSum (.of_forall fun s => ?_)
    have hl := _root_.CStarAlgebra.increasingApproximateUnit A
    have := hl.neBot
    have hlhs : Tendsto (fun e => ∑ n ∈ s, (1 / 2 / 2 ^ n : ℝ) * (ω n e).re)
        (_root_.CStarAlgebra.approximateUnit A)
        (𝓝 (∑ n ∈ s, (1 / 2 / 2 ^ n : ℝ) * ‖(ω n : A →L[ℂ] ℂ)‖)) :=
      tendsto_finsetSum s fun n _ => tendsto_const_nhds.mul <| by
        simpa [Function.comp_def] using
          Complex.continuous_re.continuousAt.tendsto.comp ((ω n).tendsto_nhds_opNorm hl)
    have hrhs : Tendsto (fun e => (geometricSeries ω hω e).re)
        (_root_.CStarAlgebra.approximateUnit A) (𝓝 ‖(geometricSeries ω hω : A →L[ℂ] ℂ)‖) := by
      simpa [Function.comp_def] using Complex.continuous_re.continuousAt.tendsto.comp
        ((geometricSeries ω hω).tendsto_nhds_opNorm hl)
    refine le_of_tendsto_of_tendsto hlhs hrhs ?_
    filter_upwards [hl.eventually_nonneg] with e he
    have hre : HasSum (fun k : ℕ => (1 / 2 / 2 ^ k : ℝ) * (ω k e).re)
        (geometricSeries ω hω e).re := by
      simpa only [Function.comp_def, Complex.reCLM_apply, Complex.smul_re, smul_eq_mul] using
        Complex.reCLM.hasSum (hasSum_geometricSeries_apply ω hω e)
    exact sum_le_hasSum s
      (fun k _ => mul_nonneg (geomWeight_pos k).le (Complex.le_def.1 ((ω k).map_nonneg he)).1) hre

/-- When every `ω n` has norm `1`, `geometricSeries ω` has norm `1` (hence is a state). -/
theorem norm_geometricSeries_eq_one (ω : ℕ → A →P[ℂ] ℂ) (hω : ∀ n, ‖(ω n : A →L[ℂ] ℂ)‖ = 1) :
    ‖(geometricSeries ω ⟨1, fun n => (hω n).le⟩ : A →L[ℂ] ℂ)‖ = 1 := by
  rw [norm_geometricSeries]
  simpa [hω] using tsum_geometric_two' (1 : ℝ)

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
  let ψ := PositiveContinuousLinearMap.geometricSeries ω ⟨1, fun n => (hω_norm n).le⟩
  have hstar (a : A) (hψa : ψ (star a * a) = 0) : a = 0 := by
    by_contra ha0
    have hall := (PositiveContinuousLinearMap.geometricSeries_apply_eq_zero_iff ω _
      (star_mul_self_nonneg a)).1 hψa
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
  exact ⟨ψ, PositiveContinuousLinearMap.norm_geometricSeries_eq_one ω hω_norm,
    (forall_nonneg_apply_eq_zero_iff ψ).2 hstar, hstar⟩

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
