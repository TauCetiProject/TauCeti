/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Data.Finsupp.Encodable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Instances.RealVectorSpace
import TauCeti.Analysis.Normed.Operator.Extend

/-!
# Almost-everywhere additive families as dual-valued functions

Let `X` be a real normed space and let `g x : S → ℝ`, for `x : X`, be a family of functions
that is additive in `x` and bounded by `C ‖x‖`, but only up to null sets that depend on `x`.
This file shows that such a family is the family of evaluations of a single function with values
in the dual of `X`.

* `TauCeti.ae_eq_apply_of_denseRange`: a dual-valued function whose evaluations agree with the
  family on a dense set, off a single null set, has every evaluation `s ↦ φ s x` almost everywhere
  equal to `g x`.
* `TauCeti.exists_strongDual_ae_eq_apply`: if `X` is separable and the functions `g x` are
  measurable, there is a dual-valued function `φ` with measurable evaluations and `‖φ s‖ ≤ C`
  everywhere whose evaluations are almost everywhere equal to the `g x`.

For the second statement, a countable dense additive subgroup of `X` gives a single null set
off which `x ↦ g x s` is additive and bounded on that subgroup. There it extends by continuity to
a continuous additive map, which is real-linear. This is the lifting step in the proof that
separable dual spaces have the Radon–Nikodým property.

## References

* J. Diestel and J. J. Uhl, Jr., *Vector Measures*, Mathematical Surveys 15, American Mathematical
  Society, 1977, Chapter III, §3, Theorem 1.
-/

public section

open MeasureTheory Filter Set TopologicalSpace Topology
open scoped NNReal

namespace TauCeti

variable {S X : Type*} [MeasurableSpace S] [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A family `g x` of real functions that is additive in `x` and bounded by `C ‖x‖` up to null
sets, with exceptional sets depending on `x`, is determined almost everywhere by its values on a
dense set: a function `φ` with values in the dual whose evaluations agree with `g` on that set off
a single null set has evaluations `φ · x` equal to `g x` almost everywhere, for every `x`. -/
theorem ae_eq_apply_of_denseRange {ν : Measure S} {g : X → S → ℝ}
    (hadd : ∀ x y, g (x + y) =ᵐ[ν] g x + g y) {C : ℝ}
    (hbound : ∀ x, ∀ᵐ s ∂ν, |g x s| ≤ C * ‖x‖) {ι : Type*} {e : ι → X} (he : DenseRange e)
    {φ : S → StrongDual ℝ X} (hφ : ∀ᵐ s ∂ν, ∀ i, φ s (e i) = g (e i) s) (x : X) :
    (fun s ↦ φ s x) =ᵐ[ν] g x := by
  obtain ⟨y, hy, hyx⟩ := mem_closure_iff_seq_limit.1 (he x)
  choose l hl using hy
  have hlx : Tendsto (fun n ↦ e (l n)) atTop (𝓝 x) := by simpa only [hl] using hyx
  filter_upwards [hφ, ae_all_iff.2 fun n ↦ hadd (e (l n)) (x - e (l n)),
    ae_all_iff.2 fun n ↦ hbound (x - e (l n))] with s hs h₁ h₂
  -- The bound controls `g x - g (e (l n))`, which tends to zero.
  have hdist (n : ℕ) : ‖φ s (e (l n)) - g x s‖ ≤ C * ‖x - e (l n)‖ := by
    have h := h₁ n
    rw [add_sub_cancel, Pi.add_apply] at h
    rw [hs, h, Real.norm_eq_abs, sub_add_cancel_left, abs_neg]
    exact h₂ n
  refine tendsto_nhds_unique (((φ s).continuous.tendsto x).comp hlx) ?_
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ ↦ norm_nonneg _) hdist ?_)
  simpa using ((tendsto_const_nhds (x := x)).sub hlx).norm.const_mul C

/-- On a separable space, a family `g x` of real functions that is additive in `x` and bounded by
`C ‖x‖` up to null sets, with exceptional sets depending on `x`, is the family of evaluations of a
single function with values in the dual ball of radius `C`. -/
theorem exists_strongDual_ae_eq_apply [SeparableSpace X] {ν : Measure S}
    {g : X → S → ℝ} (hg : ∀ x, Measurable (g x)) (hadd : ∀ x y, g (x + y) =ᵐ[ν] g x + g y)
    {C : ℝ≥0} (hbound : ∀ x, ∀ᵐ s ∂ν, |g x s| ≤ C * ‖x‖) :
    ∃ φ : S → StrongDual ℝ X, (∀ x, Measurable fun s ↦ φ s x) ∧ (∀ s, ‖φ s‖ ≤ C) ∧
      ∀ x, (fun s ↦ φ s x) =ᵐ[ν] g x := by
  obtain ⟨u, hu⟩ := exists_dense_seq X
  -- The integer combinations of a dense sequence form a countable dense additive subgroup.
  let e : (ℕ →₀ ℤ) →ₗ[ℤ] X := (Finsupp.linearCombination ℤ u).toAddMonoidHom.toIntLinearMap
  have he : DenseRange e := hu.mono <| by
    rintro _ ⟨n, rfl⟩
    exact ⟨Finsupp.single n 1, by simp [e]⟩
  -- The set where additivity and the bound hold on that subgroup has full measure.
  let G : Set S := (⋂ l, ⋂ l', {s | g (e l + e l') s = g (e l) s + g (e l') s}) ∩
    ⋂ l, {s | |g (e l) s| ≤ C * ‖e l‖}
  have hGm : MeasurableSet G :=
    (MeasurableSet.iInter fun _ ↦ MeasurableSet.iInter fun _ ↦
      measurableSet_eq_fun (hg _) ((hg _).add (hg _))).inter
      (MeasurableSet.iInter fun _ ↦
        measurableSet_le (continuous_abs.measurable.comp (hg _)) measurable_const)
  have hG : ∀ᵐ s ∂ν, s ∈ G := by
    filter_upwards [ae_all_iff.2 fun l ↦ ae_all_iff.2 fun l' ↦ hadd (e l) (e l'),
      ae_all_iff.2 fun l ↦ hbound (e l)] with s h₁ h₂
    exact ⟨mem_iInter.2 fun l ↦ mem_iInter.2 fun l' ↦ h₁ l l', mem_iInter.2 h₂⟩
  -- On `G` the values on the subgroup are additive and bounded; off `G` they are set to zero.
  let F (s : S) : (ℕ →₀ ℤ) →+ ℝ := AddMonoidHom.mk' (fun l ↦ G.indicator (g (e l)) s)
    fun l l' ↦ by
      by_cases hs : s ∈ G
      · simp only [indicator_of_mem hs, map_add]
        exact mem_iInter.1 (mem_iInter.1 hs.1 l) l'
      · simp [hs]
  have hF (s : S) (l : ℕ →₀ ℤ) : ‖F s l‖ ≤ C * ‖e l‖ := by
    by_cases hs : s ∈ G
    · simpa [F, indicator_of_mem hs, Real.norm_eq_abs] using mem_iInter.1 hs.2 l
    · simp only [F, AddMonoidHom.mk'_apply, indicator_of_notMem hs, norm_zero]
      positivity
  -- Extend by continuity and upgrade the resulting continuous additive map to a real-linear one.
  let Φ (s : S) : X →L[ℤ] ℝ := (F s).toIntLinearMap.extendOfBound e C (hF s)
  let φ (s : S) : StrongDual ℝ X :=
    (Φ s).toLinearMap.toAddMonoidHom.toRealLinearMap (Φ s).continuous
  have hφe (s : S) (l : ℕ →₀ ℤ) : φ s (e l) = G.indicator (g (e l)) s :=
    LinearMap.extendOfBound_apply _ _ _ _ he l
  have hφle (s : S) (x : X) : ‖φ s x‖ ≤ C * ‖x‖ :=
    LinearMap.norm_extendOfBound_apply_le _ _ _ _ he x
  refine ⟨φ, fun x ↦ ?_, fun s ↦ (φ s).opNorm_le_bound C.coe_nonneg (hφle s),
    ae_eq_apply_of_denseRange hadd hbound he ?_⟩
  · -- Measurability holds on the dense subgroup and passes to pointwise limits.
    refine he.induction_on x (IsSeqClosed.isClosed fun y x hy hyx ↦ ?_) fun l ↦ ?_
    · exact measurable_of_tendsto_metrizable hy
        (tendsto_pi_nhds.2 fun s ↦ ((φ s).continuous.tendsto x).comp hyx)
    · simpa only [hφe] using (hg _).indicator hGm
  · filter_upwards [hG] with s hs l
    rw [hφe, indicator_of_mem hs]

end TauCeti
