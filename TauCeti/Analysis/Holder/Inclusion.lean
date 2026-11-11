/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Normed
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import TauCeti.Analysis.Normed.Operator.Compact.Basic
import TauCeti.Topology.MetricSpace.Bounded
import TauCeti.Topology.MetricSpace.Holder
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.Equicontinuity

/-!
# Inclusions between Hölder spaces of different exponents

On a bounded metric space `X`, a function which is `α`-Hölder is `β`-Hölder for every `β ≤ α`:
if `d(x, y) ≤ D` on `X` then `d(x, y)^α ≤ D^(α - β) d(x, y)^β`. This file packages the resulting
inclusion `C^{0,α}(X) → C^{0,β}(X)` as a bounded linear map, of norm at most
`max 1 (D^(α - β))` with `D` the diameter of `X`.

For `β < α`, compact `X` and a proper codomain `Y` the inclusion is a compact operator. A bounded
set of `C^{0,α}(X, Y)` is uniformly bounded and equicontinuous. Since `Y` is proper, uniform
boundedness puts the values at each point in a compact ball of `Y`, which is the pointwise relative
compactness needed by the Arzelà–Ascoli theorem, so the set is totally bounded for the supremum
norm. For an infinite-dimensional codomain both this and the compactness of the inclusion fail.
The interpolation inequality

`[f]_β ≤ [f]_α^(β/α) (2 ‖f‖_∞)^(1 - β/α)`

then shows that on a bounded set of `C^{0,α}(X)` the `C^{0,β}` norm is small whenever the
supremum norm is, so the set is also totally bounded in `C^{0,β}(X)`. The exponent gap is needed:
the identity of an infinite-dimensional Banach space is never compact.

## Main declarations

* `TauCeti.HolderSpace.inclusionL`: the inclusion `C^{0,α}(X) → C^{0,β}(X)` for `β ≤ α` on a
  bounded space.
* `TauCeti.HolderSpace.norm_inclusionL_le`: the inclusion has norm at most `max 1 (D^(α - β))`.
* `TauCeti.HolderSpace.nnHolderNorm_le_interpolate`: the interpolation inequality for the Hölder
  seminorms.
* `TauCeti.HolderSpace.isCompactOperator_inclusionL`: the inclusion is compact for `β < α` on a
  compact space with proper codomain.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 6.33.
-/

public section

noncomputable section

namespace TauCeti

open Filter Metric Set Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace HolderSpace

variable {α β : ℝ≥0} {X Y : Type*} [MetricSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

section Inclusion

variable [BoundedSpace X]

/-- On a bounded space, an `α`-Hölder function is `β`-Hölder for every `β ≤ α`, with the
seminorm growing by at most the factor `D^(α - β)` for `D` the diameter. -/
theorem nnHolderNorm_le_of_le (hβα : β ≤ α) (f : HolderSpace α X Y) :
    nnHolderNorm β (f : X → Y) ≤
      nnHolderNorm α (f : X → Y) * (diam (univ : Set X)).toNNReal ^ ((α : ℝ) - β) :=
  (f.holderWith.of_le Metric.edist_le_diam_univ hβα).nnholderNorm_le

/-- **The inclusion of Hölder spaces.** On a bounded space, a bounded `α`-Hölder function is
`β`-Hölder for every `β ≤ α`, and the inclusion is a bounded linear map. -/
def inclusionL (hβα : β ≤ α) : HolderSpace α X Y →L[ℝ] HolderSpace β X Y :=
  LinearMap.mkContinuous
    { toFun f := ofBoundedContinuousFunction f.toBoundedContinuousFunction (by
        simpa only [coe_toBoundedContinuousFunction] using
          (f.holderWith.of_le Metric.edist_le_diam_univ hβα).memHolder)
      map_add' f g := ext fun x ↦ by simp
      map_smul' c f := ext fun x ↦ by simp }
    (max 1 (((diam (univ : Set X)).toNNReal : ℝ) ^ ((α : ℝ) - β))) fun f ↦ by
      have hD := nnHolderNorm_le_of_le hβα f
      have hD' : (nnHolderNorm β (f : X → Y) : ℝ) ≤
          nnHolderNorm α (f : X → Y) * ((diam (univ : Set X)).toNNReal : ℝ) ^ ((α : ℝ) - β) := by
        exact_mod_cast hD
      have h₁ : (1 : ℝ) ≤ max 1 (((diam (univ : Set X)).toNNReal : ℝ) ^ ((α : ℝ) - β)) :=
        le_max_left _ _
      have h₂ : ((diam (univ : Set X)).toNNReal : ℝ) ^ ((α : ℝ) - β) ≤
          max 1 (((diam (univ : Set X)).toNNReal : ℝ) ^ ((α : ℝ) - β)) := le_max_right _ _
      have hH : (0 : ℝ) ≤ nnHolderNorm α (f : X → Y) := NNReal.coe_nonneg _
      rw [LinearMap.coe_mk, AddHom.coe_mk, norm_def, norm_def f,
        toBoundedContinuousFunction_ofBoundedContinuousFunction,
        coe_toBoundedContinuousFunction]
      nlinarith [norm_nonneg f.toBoundedContinuousFunction]

/-- The inclusion of Hölder spaces has norm at most `max 1 (D^(α - β))`, with `D` the diameter of
the space. -/
theorem norm_inclusionL_le (hβα : β ≤ α) :
    ‖inclusionL (X := X) (Y := Y) hβα‖ ≤
      max 1 (((diam (univ : Set X)).toNNReal : ℝ) ^ ((α : ℝ) - β)) :=
  LinearMap.mkContinuous_norm_le _ (zero_le_one.trans (le_max_left _ _)) _

@[simp]
theorem inclusionL_apply (hβα : β ≤ α) (f : HolderSpace α X Y) (x : X) :
    inclusionL hβα f x = f x := by
  simp [inclusionL]

@[simp]
theorem toBoundedContinuousFunction_inclusionL (hβα : β ≤ α) (f : HolderSpace α X Y) :
    (inclusionL hβα f).toBoundedContinuousFunction = f.toBoundedContinuousFunction := by
  simp [inclusionL]

/-- The inclusion of Hölder spaces is injective. -/
theorem inclusionL_injective (hβα : β ≤ α) :
    Function.Injective (inclusionL (X := X) (Y := Y) hβα) := fun f g h ↦
  ext fun x ↦ by simpa using congrArg (fun k : HolderSpace β X Y ↦ k x) h

end Inclusion

/-- **Interpolation of Hölder seminorms.** For `β ≤ α` with `α ≠ 0`, the `β`-Hölder seminorm of a
bounded `α`-Hölder function is at most `[f]_α^(β/α) (2 ‖f‖_∞)^(1 - β/α)`. -/
theorem nnHolderNorm_le_interpolate (hβα : β ≤ α) (hα : α ≠ 0) (f : HolderSpace α X Y) :
    nnHolderNorm β (f : X → Y) ≤ nnHolderNorm α (f : X → Y) ^ ((β / α : ℝ≥0) : ℝ) *
      (2 * ‖f.toBoundedContinuousFunction‖₊) ^ ((1 - β / α : ℝ≥0) : ℝ) := by
  have h₀ : HolderWith (2 * ‖f.toBoundedContinuousFunction‖₊) 0 (f : X → Y) :=
    holderWith_zero_of_nnnorm_le fun x ↦ by
      simpa using f.toBoundedContinuousFunction.nnnorm_coe_le_nnnorm x
  have hθ : β / α + (1 - β / α) = 1 := add_tsub_cancel_of_le (div_le_one_of_le₀ hβα α.coe_nonneg)
  have hexp : α * (β / α) + 0 * (1 - β / α) = β := by
    rw [zero_mul, add_zero, mul_div_cancel₀ _ hα]
  have h := f.holderWith.interpolate h₀ hθ
  rw [hexp] at h
  exact h.nnholderNorm_le

/-- The interpolation bound in the form used for compactness: if `‖f‖_[C^α] ≤ 2`, then the
`C^{0,β}` norm of `f` is at most `s + 2^θ (2 s)^(1 - θ)` with `s = ‖f‖_∞` and `θ = β / α`. -/
private theorem norm_inclusionL_le_of_norm_le_two [BoundedSpace X] (hβα : β ≤ α) (hα : α ≠ 0)
    {f : HolderSpace α X Y} (hf : ‖f‖ ≤ 2) :
    ‖inclusionL hβα f‖ ≤ ‖f.toBoundedContinuousFunction‖ +
      (2 : ℝ) ^ ((β / α : ℝ≥0) : ℝ) *
        (2 * ‖f.toBoundedContinuousFunction‖) ^ ((1 - β / α : ℝ≥0) : ℝ) := by
  have h := nnHolderNorm_le_interpolate hβα hα f
  have hR : (nnHolderNorm β (f : X → Y) : ℝ) ≤
      (nnHolderNorm α (f : X → Y) : ℝ) ^ ((β / α : ℝ≥0) : ℝ) *
        (2 * ‖f.toBoundedContinuousFunction‖) ^ ((1 - β / α : ℝ≥0) : ℝ) := by
    have := NNReal.coe_le_coe.2 h
    simpa only [NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_ofNat, coe_nnnorm] using this
  have hA : (nnHolderNorm α (f : X → Y) : ℝ) ^ ((β / α : ℝ≥0) : ℝ) ≤
      (2 : ℝ) ^ ((β / α : ℝ≥0) : ℝ) :=
    Real.rpow_le_rpow (NNReal.coe_nonneg _)
      ((by simpa using f.nnHolderNorm_le : (nnHolderNorm α (f : X → Y) : ℝ) ≤ ‖f‖).trans hf)
      (NNReal.coe_nonneg _)
  rw [norm_def, toBoundedContinuousFunction_inclusionL]
  have hB : 0 ≤ (2 * ‖f.toBoundedContinuousFunction‖) ^ ((1 - β / α : ℝ≥0) : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  rw [coe_toBoundedContinuousFunction]
  nlinarith [mul_le_mul_of_nonneg_right hA hB]

/-- **Compactness of the Hölder inclusion.** On a compact space, with values in a proper space,
the inclusion `C^{0,α}(X) → C^{0,β}(X)` is a compact operator for every `β < α`. -/
theorem isCompactOperator_inclusionL [CompactSpace X] [ProperSpace Y] (hβα : β < α) :
    IsCompactOperator (inclusionL (X := X) (Y := Y) hβα.le) := by
  have hα : α ≠ 0 := (pos_of_gt hβα).ne'
  have hθ : (0 : ℝ) < ((1 - β / α : ℝ≥0) : ℝ) := by
    rw [NNReal.coe_pos, tsub_pos_iff_lt, div_lt_one (pos_of_gt hβα)]
    exact hβα
  refine (isCompactOperator_iff_totallyBounded_image_closedBall
    (inclusionL (X := X) (Y := Y) hβα.le : HolderSpace α X Y →ₗ[ℝ] HolderSpace β X Y)
    one_pos).2 ?_
  set B : Set (HolderSpace α X Y) := closedBall 0 1
  set A : Set (X →ᵇ Y) := toBoundedContinuousFunction '' B
  -- The closed unit ball is totally bounded in the supremum norm by Arzelà–Ascoli.
  have hA : TotallyBounded A := by
    refine (BoundedContinuousFunction.arzela_ascoli (closedBall (0 : Y) 1)
      (isCompact_closedBall _ _) A ?_ ?_).totallyBounded.subset subset_closure
    · rintro _ x ⟨f, hf, rfl⟩
      exact mem_closedBall_zero_iff.2 (by
        simpa using (f.norm_apply_le x).trans (mem_closedBall_zero_iff.1 hf))
    · refine Metric.equicontinuous_of_continuity_modulus (fun t ↦ t ^ (α : ℝ)) ?_ _ ?_
      · simpa [Real.zero_rpow (NNReal.coe_ne_zero.2 hα)] using
          (Real.continuousAt_rpow_const 0 (α : ℝ) (Or.inr (NNReal.coe_nonneg α))).tendsto
      · rintro x y ⟨_, f, hf, rfl⟩
        have h := f.holderWith_nnnorm.dist_le x y
        have hf1 : ‖f‖ ≤ 1 := mem_closedBall_zero_iff.1 hf
        calc dist (f.toBoundedContinuousFunction x) (f.toBoundedContinuousFunction y)
            ≤ ‖f‖ * dist x y ^ (α : ℝ) := by simpa using h
          _ ≤ 1 * dist x y ^ (α : ℝ) := by gcongr
          _ = dist x y ^ (α : ℝ) := one_mul _
  -- The interpolation bound tends to zero with the supremum norm.
  set Φ : ℝ → ℝ := fun s ↦ s + (2 : ℝ) ^ ((β / α : ℝ≥0) : ℝ) * (2 * s) ^ ((1 - β / α : ℝ≥0) : ℝ)
  have hΦ : ContinuousAt Φ 0 := by
    refine continuousAt_id.add (continuousAt_const.mul ?_)
    exact (Real.continuousAt_rpow_const _ _ (Or.inr hθ.le)).comp
      (continuousAt_const.mul continuousAt_id)
  have hΦ0 : Φ 0 = 0 := by simp [Φ, Real.zero_rpow hθ.ne']
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨δ, hδ, hΦδ⟩ := Metric.continuousAt_iff.1 hΦ ε hε
  obtain ⟨t, htA, htfin, hcover⟩ := Metric.finite_approx_of_totallyBounded hA δ hδ
  refine ⟨inclusionL hβα.le '' (B ∩ toBoundedContinuousFunction ⁻¹' t),
    ((htfin.preimage toBoundedContinuousFunction_injective.injOn).subset
      inter_subset_right).image _, ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨y, hyt, hy⟩ := mem_iUnion₂.1 (hcover (mem_image_of_mem _ hf))
  obtain ⟨g, hg, rfl⟩ := htA hyt
  refine mem_iUnion₂.2 ⟨inclusionL hβα.le g, mem_image_of_mem _ ⟨hg, hyt⟩, ?_⟩
  have hfg : ‖f - g‖ ≤ 2 := by
    have := norm_sub_le f g
    rw [mem_closedBall_zero_iff] at hf hg
    linarith
  have hsup : ‖(f - g).toBoundedContinuousFunction‖ < δ := by
    rw [toBoundedContinuousFunction_sub, ← dist_eq_norm]
    exact hy
  have hlt := hΦδ (x := ‖(f - g).toBoundedContinuousFunction‖)
    (by rwa [Real.dist_eq, sub_zero, abs_norm])
  rw [hΦ0, Real.dist_eq, sub_zero] at hlt
  rw [mem_ball, dist_eq_norm, ContinuousLinearMap.coe_coe, ← map_sub]
  exact (norm_inclusionL_le_of_norm_le_two hβα.le hα hfg).trans_lt ((le_abs_self _).trans_lt hlt)

end HolderSpace

end TauCeti
