/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.HeisenbergModel.Model
import TauCeti.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Wiener's bound for the reproducing model

Let `T` be a bounded map from the reproducing model `M(β, e)` to a Banach space and `u` an element
with `u 0 ≠ 0`. Suppose that along a continuous homomorphism `κ : W₁ → W` from a locally compact
group, the norms `‖T (ϱ (z + κ x) u)‖` are those of the translates of one integrable function `g`
on `W₁`. Then the sum of `‖T (ϱ (κ (φ i)) v)‖` over a homomorphism `φ : I → W₁` is bounded by
`#φ⁻¹(B) * M * ‖v‖`, for a compact `B ⊂ W₁` and a constant `M` that do not depend on `I`, `φ` or
`v` (`TauCeti.ReproducingModel.exists_isCompact_tsum_enorm_le`). This is a bound of the type of
Wiener's amalgam bound: superposition writes `v` as an integral of translates of `u`, and the
translates of a compact neighbourhood of `0` by the points of `φ` meet in at most `#φ⁻¹(B)` points.

## Provenance

Adapted from `New.Heisenberg.IsVacuum.wiener_bound` in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Weil/Construction/WeilOperators.lean`. Its counting step (`h_encard_le` there) is
`Set.encard_setOf_sub_mem_le` in `TauCeti/Algebra/Group/Pointwise/Set/Card.lean`.

## References

* N. Wiener, *Tauberian theorems*, Ann. of Math. 33 (1932), 1–100.
* H. G. Feichtinger, *Banach convolution algebras of Wiener type*, in *Functions, series,
  operators* (Budapest, 1980), Colloq. Math. Soc. János Bolyai 35, North-Holland (1983), 509–524.
-/

public section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace TauCeti.ReproducingModel

variable {W W₁ : Type*} [AddCommGroup W] [TopologicalSpace W] [MeasurableSpace W]
  [IsTopologicalAddGroup W] [BorelSpace W] [SecondCountableTopology W]
  [AddCommGroup W₁] [TopologicalSpace W₁]
  {β : HeisenbergDatum W} {μ : Measure W} {e : W → ℂ} [μ.IsAddHaarMeasure] [β.IsVacuum μ e]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Superposition bounds one term: `‖u (-κ s)‖ * ‖T (ϱ (κ x) v)‖` is at most
`∫ ‖v z‖ * ‖T (ϱ (z + κ (x + s)) u)‖ dμ(z)`. -/
private theorem enorm_mul_enorm_le (T : ReproducingModel β μ e →L[ℂ] X)
    (u v : ReproducingModel β μ e) (κ : W₁ →ₜ+ W) (x s : W₁) :
    ‖u (-κ s)‖ₑ * ‖T (heisenbergRep (κ x) v)‖ₑ ≤
      ∫⁻ z, ‖v z‖ₑ * ‖T (heisenbergRep (z + κ (x + s)) u)‖ₑ ∂μ := by
  -- `∫ v z • ϱ z (ϱ (κ s) u) dμ(z) = (ϱ (κ s) u) 0 • v`, and `(ϱ (κ s) u) 0 = u (-κ s)`.
  set T' := T ∘L heisenbergRep (κ x)
  have h_eq : T' ((heisenbergRep (β := β) (μ := μ) (e := e)).integrated μ e v
      (heisenbergRep (κ s) u)) = u (-κ s) • T (heisenbergRep (κ x) v) := by
    rw [integrated_eq_smul, map_smul, heisenbergRep_apply, β.apply_zero, one_mul, zero_sub]
    rfl
  calc ‖u (-κ s)‖ₑ * ‖T (heisenbergRep (κ x) v)‖ₑ
    _ = ‖∫ z, v z • T' (heisenbergRep z (heisenbergRep (κ s) u)) ∂μ‖ₑ := by
      rw [← HeisenbergDatum.Representation.map_integrated, h_eq, eNorm_smul]
    _ ≤ ∫⁻ z, ‖v z • T' (heisenbergRep z (heisenbergRep (κ s) u))‖ₑ ∂μ :=
      eNorm_integral_le_lintegral_eNorm _
    _ = ∫⁻ z, ‖v z‖ₑ * ‖T (heisenbergRep (z + κ (x + s)) u)‖ₑ ∂μ := by
      refine lintegral_congr fun z ↦ ?_
      have h_arg : κ x + (z + κ s) = z + κ (x + s) := by rw [map_add]; abel
      simp only [T', eNorm_smul, ContinuousLinearMap.comp_apply,
        HeisenbergDatum.Representation.apply_apply, map_smul, h_arg, HeisenbergDatum.enorm_apply,
        one_mul]

variable [MeasurableSpace W₁] [IsTopologicalAddGroup W₁] [BorelSpace W₁]
  [SecondCountableTopology W₁] {μ₁ : Measure W₁} [μ₁.IsAddHaarMeasure] [LocallyCompactSpace W₁]
  [LocallyCompactSpace W]

omit [CompleteSpace X] in
/-- The integral over `W₁` of `s ↦ ∫ ‖v z‖ * ‖T (ϱ (z + κ s) u)‖ dμ(z)` is `‖g‖₁ * ‖v‖`. -/
private theorem lintegral_lintegral_enorm_eq (T : ReproducingModel β μ e →L[ℂ] X)
    (u v : ReproducingModel β μ e) (κ : W₁ →ₜ+ W) {g : W₁ → X} (t : W → W₁)
    (h_enorm : ∀ z x, ‖T (heisenbergRep (z + κ x) u)‖ₑ = ‖g (t z + x)‖ₑ) :
    ∫⁻ s, ∫⁻ z, ‖v z‖ₑ * ‖T (heisenbergRep (z + κ s) u)‖ₑ ∂μ ∂μ₁ =
      (∫⁻ x, ‖g x‖ₑ ∂μ₁) * ‖v‖ₑ := by
  have h_cont := v.continuous
  rw [lintegral_lintegral_swap (by fun_prop)]
  simp_rw [h_enorm, lintegral_const_mul' _ _ eNorm_ne_top, lintegral_add_left_eq_self (‖g ·‖ₑ)]
  rw [lintegral_mul_const _ (by fun_prop), mul_comm]
  congr 1
  rw [← ofReal_norm, norm_eq_integral_norm,
    ofReal_integral_eq_lintegral_ofReal v.integrable.norm (.of_forall fun _ ↦ norm_nonneg _)]
  simp

omit [SecondCountableTopology W₁] [LocallyCompactSpace W₁] [LocallyCompactSpace W] in
/-- Averaging the bound of `enorm_mul_enorm_le` over a set `K` of positive mass:
`‖T (ϱ (κ a) v)‖ ≤ r * ∫_{a + K} ∫ ‖v z‖ * ‖T (ϱ (z + κ s) u)‖ dμ(z) dμ₁(s)` when
`1 < r * ∫_K ‖u (-κ s)‖ dμ₁(s)`. -/
private theorem enorm_le_mul_setLIntegral (T : ReproducingModel β μ e →L[ℂ] X)
    (u v : ReproducingModel β μ e) (κ : W₁ →ₜ+ W) {K : Set W₁} {r : ℕ}
    (hr : 1 < r * ∫⁻ s in K, ‖u (-κ s)‖ₑ ∂μ₁) (a : W₁) :
    ‖T (heisenbergRep (κ a) v)‖ₑ ≤ r * ∫⁻ s in (· - a) ⁻¹' K,
      ∫⁻ z, ‖v z‖ₑ * ‖T (heisenbergRep (z + κ s) u)‖ₑ ∂μ ∂μ₁ := by
  rw [← (measurePreserving_add_left μ₁ a).setLIntegral_comp_preimage_emb
    (measurableEmbedding_addLeft a)]
  calc ‖T (heisenbergRep (κ a) v)‖ₑ
    _ ≤ r * (∫⁻ s in K, ‖u (-κ s)‖ₑ ∂μ₁) * ‖T (heisenbergRep (κ a) v)‖ₑ :=
      le_mul_of_one_le_left zero_le hr.le
    _ ≤ r * ∫⁻ s in K, ∫⁻ z, ‖v z‖ₑ * ‖T (heisenbergRep (z + κ (a + s)) u)‖ₑ ∂μ ∂μ₁ := by
      rw [mul_assoc, ← lintegral_mul_const' _ _ (by finiteness)]
      gcongr with s
      exact enorm_mul_enorm_le T u v κ a s
    _ = _ := by simp [preimage]

/-- *Wiener's bound*. Let `T` be a bounded map from the model to a Banach space, `u` an element of
the model with `u 0 ≠ 0`, `κ : W₁ → W` a continuous homomorphism from a locally compact Hausdorff
group, `g` an integrable function on `W₁` and `t : W → W₁` a function with
`‖T (ϱ (z + κ x) u)‖ = ‖g (t z + x)‖` for all `z` and `x`. There are a compact `B ⊂ W₁` and a
constant `M` such that, for every additive group `I`, every homomorphism `φ : I → W₁` and every
`v`, `∑ ‖T (ϱ (κ (φ i)) v)‖ ≤ #φ⁻¹(B) * M * ‖v‖`. -/
theorem exists_isCompact_tsum_enorm_le [T2Space W₁] (T : ReproducingModel β μ e →L[ℂ] X)
    {u : ReproducingModel β μ e} (hu : u 0 ≠ 0) (κ : W₁ →ₜ+ W) {g : W₁ → X}
    (hg : Integrable g μ₁) (t : W → W₁)
    (h_enorm : ∀ z x, ‖T (heisenbergRep (z + κ x) u)‖ₑ = ‖g (t z + x)‖ₑ) :
    ∃ B : Set W₁, IsCompact B ∧ ∃ M : NNReal, ∀ {I : Type*} [AddGroup I] (φ : I →+ W₁)
      (v : ReproducingModel β μ e),
      ∑' i, ‖T (heisenbergRep (κ (φ i)) v)‖ₑ ≤ (φ ⁻¹' B).encard * M * ‖v‖ₑ := by
  obtain ⟨K, hK, hK₀⟩ : ∃ K : Set W₁, IsCompact K ∧ K ∈ nhds 0 := exists_compact_mem_nhds 0
  refine ⟨-K + K, hK.neg.add hK, ?_⟩
  have u_cont : Continuous fun s ↦ ‖u (-κ s)‖ₑ := (continuous u).eNorm.comp (map_continuous κ).neg
  -- `u (-κ s) ≠ 0` for `s` near `0`, so the integral of its norm over `K` is positive.
  obtain ⟨r, hr⟩ : ∃ r : ℕ, 1 < r * ∫⁻ s in K, ‖u (-κ s)‖ₑ ∂μ₁ := by
    refine ENNReal.exists_nat_mul_gt ((setLIntegral_pos_iff u_cont.measurable).mpr ?_).ne'
      ENNReal.one_ne_top
    have hu_zero : ‖u (-κ 0)‖ₑ ≠ 0 := by simpa using hu
    exact μ₁.measure_pos_of_mem_nhds ((u_cont.continuousAt.eventually_ne hu_zero).and hK₀)
  obtain ⟨M, hM⟩ : ∃ M : NNReal, ∫⁻ x, ‖g x‖ₑ ∂μ₁ = M :=
    ⟨_, (ENNReal.coe_toNNReal hg.hasFiniteIntegral.ne).symm⟩
  -- The constant is nonzero, so that the bound is trivial when `φ ⁻¹' B` is infinite.
  refine ⟨r * M + 1, fun {I} _ φ v ↦ ?_⟩
  obtain hN | ⟨N, hN⟩ : (φ ⁻¹' (-K + K)).encard = ⊤ ∨ ∃ N : ℕ, (φ ⁻¹' (-K + K)).encard = N := by
    cases (φ ⁻¹' (-K + K)).encard <;> simp
  · by_cases hv : v = 0 <;> simp [hN, hv]
  set G := fun s ↦ ∫⁻ z, ‖v z‖ₑ * ‖T (heisenbergRep (z + κ s) u)‖ₑ ∂μ
  have h_term (i : I) :
      ‖T (heisenbergRep (κ (φ i)) v)‖ₑ ≤ r * ∫⁻ s in (· - φ i) ⁻¹' K, G s ∂μ₁ :=
    enorm_le_mul_setLIntegral T u v κ hr (φ i)
  calc ∑' i, ‖T (heisenbergRep (κ (φ i)) v)‖ₑ
    _ ≤ ∑' i, r * ∫⁻ s in (· - φ i) ⁻¹' K, G s ∂μ₁ := tsum_le_tsum h_term
    _ = r * ∫⁻ s, G s ∂(Measure.sum fun i ↦ μ₁.restrict ((· - φ i) ⁻¹' K)) := by
      rw [lintegral_sum_measure, ENNReal.tsum_mul_left]
    _ ≤ r * ∫⁻ s, G s ∂(N • μ₁) := by
      gcongr
      refine (Measure.sum_restrict_le (fun i ↦ measurable_sub_const (φ i) hK.measurableSet)
        fun y ↦ ?_).trans (by gcongr; exact μ₁.restrict_le_self)
      simpa [hN] using Set.encard_setOf_sub_mem_le φ K y
    _ = N * (r * M) * ‖v‖ₑ := by
      rw [lintegral_smul_measure, lintegral_lintegral_enorm_eq T u v κ t h_enorm, hM]
      simp only [nsmul_eq_mul]
      ring
    _ ≤ (φ ⁻¹' (-K + K)).encard * (r * M + 1 : NNReal) * ‖v‖ₑ := by
      rw [hN]
      gcongr
      · simp
      · push_cast
        exact le_self_add

end TauCeti.ReproducingModel
