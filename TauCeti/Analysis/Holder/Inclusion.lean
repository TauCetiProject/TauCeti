/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Normed
public import TauCeti.Analysis.Holder.OpenSet
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import TauCeti.Algebra.Order.Ring.MaxOneMul
import TauCeti.Analysis.Normed.Operator.Compact.Basic
import TauCeti.Topology.MetricSpace.Bounded
import TauCeti.Topology.MetricSpace.Holder
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.Equicontinuity

/-!
# Inclusions between Hölder spaces of different exponents

A bounded function which is `α`-Hölder is `β`-Hölder for every `β ≤ α`, on every metric space:
for `d(x, y) < 1` the quotient is controlled by `d(x, y)^α ≤ d(x, y)^β`, and for `d(x, y) ≥ 1` by
`‖f(x) - f(y)‖ ≤ 2 ‖f‖_∞`, so `[f]_β ≤ max (2 ‖f‖_∞) [f]_α`. This file packages the resulting
inclusion `C^{0,α}(X) → C^{0,β}(X)` as a bounded linear map, of norm at most `3`. On a bounded
space of diameter `D` the bound `d(x, y)^α ≤ D^(α - β) d(x, y)^β` gives the norm bound
`max 1 (D^(α - β))` instead, which is smaller on small spaces. The constant `3` cannot be
improved: on `ℝ`, with `0 < α` and `β = 0`, the functions `sin (ε x)` have `C^{0,0}` norm `3`,
while their `C^{0,α}` norm tends to `1` as `ε → 0`. The global supremum bound is what makes the
inclusion hold on unbounded spaces: on `ℝ`, the unbounded function `x` is Lipschitz but not
`β`-Hölder for any `β < 1`.

The same holds for the spaces of higher order. On an open set `Ω` of a normed space, the norm of
`C^{k,α}(Ω)` bounds the supremum of the `k`-th derivative field, so `C^{k,α}(Ω) → C^{k,β}(Ω)` is
a continuous linear map of norm at most `3`, and of norm at most `max 1 (D^(α - β))` when `Ω` is
bounded of diameter `D`. Likewise for the bounded `C^{k,α}` maps on the whole space. These also
include into the space of one order less: for `α ≤ 1` the `k`-th derivative of a bounded
`C^{k+1,α}` map is bounded with bounded derivative, hence `α`-Hölder.

For `β < α`, compact `X` and a proper codomain `Y` the inclusion `C^{0,α}(X) → C^{0,β}(X)` is a
compact operator. A bounded set of `C^{0,α}(X, Y)` is uniformly bounded and equicontinuous. Since
`Y` is proper, uniform boundedness puts the values at each point in a compact ball of `Y`, which is
the pointwise relative compactness needed by the Arzelà–Ascoli theorem, so the set is totally
bounded for the supremum norm. For an infinite-dimensional codomain both this and the compactness
of the inclusion fail. The interpolation inequality

`[f]_β ≤ [f]_α^(β/α) (2 ‖f‖_∞)^(1 - β/α)`

then shows that on a bounded set of `C^{0,α}(X)` the `C^{0,β}` norm is small whenever the
supremum norm is, so the set is also totally bounded in `C^{0,β}(X)`. The exponent gap is needed:
the identity of an infinite-dimensional Banach space is never compact.

## Main declarations

* `TauCeti.HolderSpace.holderWith_of_le`: a bounded `α`-Hölder function is `β`-Hölder with
  constant `max (2 ‖f‖_∞) [f]_α`, for every `β ≤ α`.
* `TauCeti.HolderSpace.inclusionL`: the inclusion `C^{0,α}(X) → C^{0,β}(X)` for `β ≤ α`, of norm
  at most `3` (`TauCeti.HolderSpace.norm_inclusionL_le_three`), and at most `max 1 (D^(α - β))` on
  a bounded space (`TauCeti.HolderSpace.norm_inclusionL_le`).
* `TauCeti.CkHolderSpaceOn.inclusionL`: the inclusion `C^{k,α}(Ω) → C^{k,β}(Ω)` for `β ≤ α` on an
  open set, with the same two norm bounds `TauCeti.CkHolderSpaceOn.norm_inclusionL_le_three` and,
  for bounded `Ω`, `TauCeti.CkHolderSpaceOn.norm_inclusionL_le`.
* `TauCeti.CkHolderSpace.inclusionL`: the inclusion of bounded `C^{k,α}` maps on the whole space
  into bounded `C^{k,β}` maps, of norm at most `3`.
* `TauCeti.CkHolderSpace.inclusionSuccL`: for `α ≤ 1`, the inclusion of bounded `C^{k+1,α}` maps
  on the whole space into bounded `C^{k,α}` maps, of norm at most `k + 4`.
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

/-- The scalar inequality behind the bound `3` on the exponent inclusions: if the top seminorm is
replaced by `max (2 s) H`, with `s` a part of the sum `a`, the sum `a + H` grows by at most the
factor `3`. -/
private theorem add_max_le_three_mul {a s H : ℝ} (hs : 0 ≤ s) (hsa : s ≤ a) (hH : 0 ≤ H) :
    a + max (2 * s) H ≤ 3 * (a + H) := by
  have := max_le_add_of_nonneg (by positivity : 0 ≤ 2 * s) hH
  linarith

namespace HolderSpace

variable {α β : ℝ≥0} {X Y : Type*} [MetricSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

section Inclusion

/-- An element of a Hölder space is Hölder of exponent `0` with constant `2 ‖f‖_∞`: its values
differ by at most twice its supremum norm. -/
theorem holderWith_zero (f : HolderSpace α X Y) :
    HolderWith (2 * ‖f.toBoundedContinuousFunction‖₊) 0 (f : X → Y) :=
  holderWith_zero_of_nnnorm_le fun x ↦ by
    simpa using f.toBoundedContinuousFunction.nnNorm_coe_le_nnNorm x

/-- On every space, a bounded `α`-Hölder function is `β`-Hölder for every `β ≤ α`, with constant
`max (2 ‖f‖_∞) [f]_α`: nearby points are controlled by the `α`-Hölder bound and distant ones by the
supremum norm. -/
theorem holderWith_of_le (hβα : β ≤ α) (f : HolderSpace α X Y) :
    HolderWith (max (2 * ‖f.toBoundedContinuousFunction‖₊) (nnHolderNorm α (f : X → Y))) β f :=
  f.holderWith_zero.of_le_of_le f.holderWith zero_le hβα

/-- On every space, the `β`-Hölder seminorm of a bounded `α`-Hölder function is at most
`max (2 ‖f‖_∞) [f]_α` for every `β ≤ α`. -/
theorem nnHolderNorm_le_max (hβα : β ≤ α) (f : HolderSpace α X Y) :
    nnHolderNorm β (f : X → Y) ≤
      max (2 * ‖f.toBoundedContinuousFunction‖₊) (nnHolderNorm α (f : X → Y)) :=
  (f.holderWith_of_le hβα).nnholderNorm_le

/-- The `C^{0,β}` norm of a bounded `α`-Hölder function is at most three times its `C^{0,α}`
norm, for every `β ≤ α`. -/
private theorem norm_le_three_mul (hβα : β ≤ α) (f : HolderSpace α X Y)
    (g : HolderSpace β X Y) (hg : g.toBoundedContinuousFunction = f.toBoundedContinuousFunction) :
    ‖g‖ ≤ 3 * ‖f‖ := by
  have h := NNReal.coe_le_coe.2 (nnHolderNorm_le_max hβα f)
  rw [NNReal.coe_max, NNReal.coe_mul, NNReal.coe_ofNat, coe_nnNorm] at h
  rw [norm_def, norm_def f, hg, coe_toBoundedContinuousFunction]
  exact (add_le_add_right h _).trans
    (add_max_le_three_mul (norm_nonneg _) le_rfl (NNReal.coe_nonneg _))

/-- **The inclusion of Hölder spaces.** A bounded `α`-Hölder function is `β`-Hölder for every
`β ≤ α`, and the inclusion is a bounded linear map, of norm at most `3` on every space
(`TauCeti.HolderSpace.norm_inclusionL_le_three`) and at most `max 1 (D^(α - β))` on a space of
diameter `D` (`TauCeti.HolderSpace.norm_inclusionL_le`). -/
def inclusionL (hβα : β ≤ α) : HolderSpace α X Y →L[ℝ] HolderSpace β X Y :=
  LinearMap.mkContinuous
    { toFun f := ofBoundedContinuousFunction f.toBoundedContinuousFunction (by
        simpa only [coe_toBoundedContinuousFunction] using (f.holderWith_of_le hβα).memHolder)
      map_add' f g := ext fun x ↦ by simp
      map_smul' c f := ext fun x ↦ by simp }
    3 fun f ↦
      norm_le_three_mul hβα f _ (toBoundedContinuousFunction_ofBoundedContinuousFunction _ _)

@[simp]
theorem inclusionL_apply (hβα : β ≤ α) (f : HolderSpace α X Y) (x : X) :
    inclusionL hβα f x = f x := by
  simp [inclusionL]

@[simp]
theorem toBoundedContinuousFunction_inclusionL (hβα : β ≤ α) (f : HolderSpace α X Y) :
    (inclusionL hβα f).toBoundedContinuousFunction = f.toBoundedContinuousFunction := by
  simp [inclusionL]

/-- The inclusion of Hölder spaces has norm at most `3`. -/
theorem norm_inclusionL_le_three (hβα : β ≤ α) :
    ‖inclusionL (X := X) (Y := Y) hβα‖ ≤ 3 :=
  LinearMap.mkContinuous_norm_le _ zero_le_three _

/-- The inclusion of Hölder spaces is injective. -/
theorem inclusionL_injective (hβα : β ≤ α) :
    Function.Injective (inclusionL (X := X) (Y := Y) hβα) := fun f g h ↦
  ext fun x ↦ by simpa using congrArg (fun k : HolderSpace β X Y ↦ k x) h

section BoundedSpace

variable [BoundedSpace X]

/-- On a bounded space, an `α`-Hölder function is `β`-Hölder for every `β ≤ α`, with the
seminorm growing by at most the factor `D^(α - β)` for `D` the diameter. -/
theorem nnHolderNorm_le_of_le (hβα : β ≤ α) (f : HolderSpace α X Y) :
    nnHolderNorm β (f : X → Y) ≤
      nnHolderNorm α (f : X → Y) * (diam (univ : Set X)).toNNReal ^ ((α : ℝ) - β) :=
  (f.holderWith.of_le Metric.edist_le_diam_univ hβα).nnholderNorm_le

/-- On a bounded space, the inclusion of Hölder spaces has norm at most `max 1 (D^(α - β))`, with
`D` the diameter of the space. -/
theorem norm_inclusionL_le (hβα : β ≤ α) :
    ‖inclusionL (X := X) (Y := Y) hβα‖ ≤
      max 1 (((diam (univ : Set X)).toNNReal : ℝ) ^ ((α : ℝ) - β)) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans (le_max_left _ _)) fun f ↦ ?_
  have hD' : (nnHolderNorm β (f : X → Y) : ℝ) ≤
      ((diam (univ : Set X)).toNNReal : ℝ) ^ ((α : ℝ) - β) * nnHolderNorm α (f : X → Y) := by
    rw [mul_comm]
    exact_mod_cast nnHolderNorm_le_of_le hβα f
  rw [norm_def, norm_def f, toBoundedContinuousFunction_inclusionL,
    coe_toBoundedContinuousFunction]
  exact (add_le_add_right hD' _).trans
    (add_mul_le_max_one_mul_add (norm_nonneg _) (NNReal.coe_nonneg _))

end BoundedSpace

end Inclusion

/-- **Interpolation of Hölder seminorms.** For `β ≤ α` with `α ≠ 0`, the `β`-Hölder seminorm of a
bounded `α`-Hölder function is at most `[f]_α^(β/α) (2 ‖f‖_∞)^(1 - β/α)`. -/
theorem nnHolderNorm_le_interpolate (hβα : β ≤ α) (hα : α ≠ 0) (f : HolderSpace α X Y) :
    nnHolderNorm β (f : X → Y) ≤ nnHolderNorm α (f : X → Y) ^ ((β / α : ℝ≥0) : ℝ) *
      (2 * ‖f.toBoundedContinuousFunction‖₊) ^ ((1 - β / α : ℝ≥0) : ℝ) := by
  have hθ : β / α + (1 - β / α) = 1 := add_tsub_cancel_of_le (div_le_one_of_le₀ hβα α.coe_nonneg)
  have hexp : α * (β / α) + 0 * (1 - β / α) = β := by
    rw [zero_mul, add_zero, mul_div_cancel₀ _ hα]
  have h := f.holderWith.interpolate f.holderWith_zero hθ
  rw [hexp] at h
  exact h.nnholderNorm_le

/-- The interpolation bound in the form used for compactness: if `‖f‖_[C^α] ≤ 2`, then the
`C^{0,β}` norm of `f` is at most `s + 2^θ (2 s)^(1 - θ)` with `s = ‖f‖_∞` and `θ = β / α`. -/
private theorem norm_inclusionL_le_of_norm_le_two (hβα : β ≤ α) (hα : α ≠ 0)
    {f : HolderSpace α X Y} (hf : ‖f‖ ≤ 2) :
    ‖inclusionL hβα f‖ ≤ ‖f.toBoundedContinuousFunction‖ +
      (2 : ℝ) ^ ((β / α : ℝ≥0) : ℝ) *
        (2 * ‖f.toBoundedContinuousFunction‖) ^ ((1 - β / α : ℝ≥0) : ℝ) := by
  have h := nnHolderNorm_le_interpolate hβα hα f
  have hR : (nnHolderNorm β (f : X → Y) : ℝ) ≤
      (nnHolderNorm α (f : X → Y) : ℝ) ^ ((β / α : ℝ≥0) : ℝ) *
        (2 * ‖f.toBoundedContinuousFunction‖) ^ ((1 - β / α : ℝ≥0) : ℝ) := by
    have := NNReal.coe_le_coe.2 h
    simpa only [NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_ofNat, coe_nnNorm] using this
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

namespace CkHolderSpaceOn

open TopologicalSpace

variable {k : ℕ} {α β : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E}

/-- The `C^{k,β}(Ω)` norm of an element with the derivative fields of an element `f` of
`C^{k,α}(Ω)` is at most `3 ‖f‖`, for every `β ≤ α`. -/
private theorem norm_le_three_mul (hβα : β ≤ α) (f : CkHolderSpaceOn k α Ω F)
    (g : CkHolderSpaceOn k β Ω F) (hg : ∀ i x, g.iteratedFDeriv i x = f.iteratedFDeriv i x) :
    ‖g‖ ≤ 3 * ‖f‖ := by
  have hH := f.iteratedFDerivHolder.holderWith_of_le hβα
  rw [toBoundedContinuousFunction_iteratedFDerivHolder, coe_iteratedFDerivHolder] at hH
  have hfun : (g.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F) =
      f.iteratedFDeriv (Fin.last k) := funext (hg _)
  refine (norm_le_sum_add_of_norm_iteratedFDeriv_le_of_holderWith
    (M := fun i ↦ ‖f.iteratedFDeriv i‖) (fun i ↦ norm_nonneg (f.iteratedFDeriv i))
    (fun i x ↦ by rw [hg]; exact (f.iteratedFDeriv i).norm_coe_le_norm x)
    (by rw [hfun]; exact hH)).trans ?_
  rw [norm_eq f]
  push_cast
  exact add_max_le_three_mul (norm_nonneg _)
    (Finset.single_le_sum (fun i _ ↦ norm_nonneg (f.iteratedFDeriv i)) (Finset.mem_univ _))
    (NNReal.coe_nonneg _)

/-- **The exponent inclusion of Hölder spaces on an open set.** For `β ≤ α`, every element of
`C^{k,α}(Ω)` lies in `C^{k,β}(Ω)`, and the inclusion is a continuous linear map, of norm at most
`3` on every open set (`TauCeti.CkHolderSpaceOn.norm_inclusionL_le_three`) and at most
`max 1 (D^(α - β))` on a bounded open set of diameter `D`
(`TauCeti.CkHolderSpaceOn.norm_inclusionL_le`). No boundedness of `Ω` is needed, since the norm
already bounds the `k`-th derivative field: for points at distance at least `1` its supremum
controls the `β`-Hölder quotient. -/
def inclusionL (hβα : β ≤ α) : CkHolderSpaceOn k α Ω F →L[ℝ] CkHolderSpaceOn k β Ω F :=
  LinearMap.mkContinuous
    { toFun f := ofContDiffOn f.extend f.contDiffOn_extend
        (fun i hi ↦ ⟨‖f‖, f.norm_iteratedFDeriv_extend_le hi⟩) (by
          have h := (f.iteratedFDerivHolder.holderWith_of_le hβα).memHolder
          rw [coe_iteratedFDerivHolder] at h
          convert h using 1
          exact funext fun x ↦ f.iteratedFDeriv_extend (Fin.last k) x)
      map_add' f g := by ext x; simp
      map_smul' c f := by ext x; simp }
    3 fun f ↦ norm_le_three_mul hβα f _ fun i x ↦ by simp [iteratedFDeriv_extend]

/-- The exponent inclusion does not change values. -/
@[simp]
theorem inclusionL_apply (hβα : β ≤ α) (f : CkHolderSpaceOn k α Ω F) (x : Ω) :
    inclusionL hβα f x = f x := by
  simp [inclusionL]

/-- The exponent inclusion keeps the derivative fields. -/
@[simp]
theorem iteratedFDeriv_inclusionL (hβα : β ≤ α) (f : CkHolderSpaceOn k α Ω F) (i : Fin (k + 1))
    (x : Ω) : (inclusionL hβα f).iteratedFDeriv i x = f.iteratedFDeriv i x := by
  simp [inclusionL, iteratedFDeriv_extend]

/-- The exponent inclusion is injective. -/
theorem inclusionL_injective (hβα : β ≤ α) :
    Function.Injective (inclusionL (k := k) (Ω := Ω) (F := F) hβα) := fun f g h ↦
  ext fun x ↦ by simpa using congrArg (fun u : CkHolderSpaceOn k β Ω F ↦ u x) h

/-- The exponent inclusion `C^{k,α}(Ω) → C^{k,β}(Ω)` has norm at most `3`. -/
theorem norm_inclusionL_le_three (hβα : β ≤ α) :
    ‖inclusionL (k := k) (Ω := Ω) (F := F) hβα‖ ≤ 3 :=
  LinearMap.mkContinuous_norm_le _ zero_le_three _

/-- On a bounded open set `Ω` of diameter `D`, the exponent inclusion `C^{k,α}(Ω) → C^{k,β}(Ω)`
has norm at most `max 1 (D^(α - β))`. -/
theorem norm_inclusionL_le (hΩ : Bornology.IsBounded (Ω : Set E)) (hβα : β ≤ α) :
    ‖inclusionL (k := k) (Ω := Ω) (F := F) hβα‖ ≤
      max 1 (((diam (Ω : Set E)).toNNReal : ℝ) ^ ((α : ℝ) - β)) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans (le_max_left _ _)) fun f ↦ ?_
  set D : ℝ≥0 := (diam (Ω : Set E)).toNNReal
  set H := nnHolderNorm α (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F)
  have hH : HolderWith (H * D ^ ((α : ℝ) - β)) β
      ((inclusionL hβα f).iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F) := by
    convert f.memHolder_iteratedFDeriv.holderWith.of_le
      (fun x y : Ω ↦ edist_le_diam_of_mem hΩ x.property y.property) hβα using 1
    exact funext fun x ↦ iteratedFDeriv_inclusionL hβα f _ x
  have hM0 : ∀ i, 0 ≤ ‖f.iteratedFDeriv i‖ := fun i ↦ norm_nonneg (f.iteratedFDeriv i)
  refine (norm_le_sum_add_of_norm_iteratedFDeriv_le_of_holderWith
    (M := fun i ↦ ‖f.iteratedFDeriv i‖) hM0 (fun i x ↦ by
      rw [iteratedFDeriv_inclusionL]
      exact (f.iteratedFDeriv i).norm_coe_le_norm x) hH).trans ?_
  have hsum : ∑ i, ‖f.iteratedFDeriv i‖ + H = ‖f‖ := (norm_eq f).symm
  rw [← hsum, NNReal.coe_mul, NNReal.coe_rpow, mul_comm (H : ℝ)]
  exact add_mul_le_max_one_mul_add (Finset.sum_nonneg fun i _ ↦ hM0 i) (NNReal.coe_nonneg H)

end CkHolderSpaceOn

namespace CkHolderSpace

variable {k : ℕ} {α β : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A bounded `C^{k,β}` map with the same underlying function as an element `f` of the bounded
`C^{k,α}` maps has norm at most `3 ‖f‖`, for every `β ≤ α`. -/
private theorem norm_le_three_mul (hβα : β ≤ α) (f : CkHolderSpace k α E F)
    (g : CkHolderSpace k β E F) (hg : ⇑g = ⇑f) : ‖g‖ ≤ 3 * ‖f‖ := by
  have hfield : ∀ i, g.iteratedFDeriv i = f.iteratedFDeriv i := fun i ↦ by
    ext1 x
    rw [← iteratedFDeriv_eq, ← iteratedFDeriv_eq, hg]
  have hH := NNReal.coe_le_coe.2 (f.iteratedFDerivHolder.nnHolderNorm_le_max hβα)
  simp only [toBoundedContinuousFunction_iteratedFDerivHolder, coe_iteratedFDerivHolder,
    NNReal.coe_max, NNReal.coe_mul, NNReal.coe_ofNat, coe_nnNorm] at hH
  rw [norm_eq, norm_eq f, hg]
  simp only [hfield]
  exact (add_le_add_right hH _).trans (add_max_le_three_mul (norm_nonneg _)
    (Finset.single_le_sum (fun i _ ↦ norm_nonneg (f.iteratedFDeriv i)) (Finset.mem_univ _))
    (NNReal.coe_nonneg _))

/-- **The exponent inclusion of bounded Hölder spaces.** For `β ≤ α`, every bounded `C^{k,α}` map
on `E` is a bounded `C^{k,β}` map, and the inclusion is a continuous linear map of norm at most
`3` (`TauCeti.CkHolderSpace.norm_inclusionL_le_three`). -/
def inclusionL (hβα : β ≤ α) : CkHolderSpace k α E F →L[ℝ] CkHolderSpace k β E F :=
  LinearMap.mkContinuous
    { toFun f := ofContDiff f f.contDiff (fun i hi ↦ ⟨‖f‖, f.norm_iteratedFDeriv_apply_le hi⟩)
        (by simpa using (f.iteratedFDerivHolder.holderWith_of_le hβα).memHolder)
      map_add' f g := by ext x; simp
      map_smul' c f := by ext x; simp }
    3 fun f ↦ norm_le_three_mul hβα f _ (by rw [LinearMap.coe_mk, AddHom.coe_mk, coe_ofContDiff])

/-- The exponent inclusion does not change the underlying function. -/
@[simp]
theorem coe_inclusionL (hβα : β ≤ α) (f : CkHolderSpace k α E F) :
    ⇑(inclusionL hβα f) = ⇑f := by
  simp [inclusionL]

/-- The exponent inclusion keeps the derivative fields. -/
@[simp]
theorem iteratedFDeriv_inclusionL (hβα : β ≤ α) (f : CkHolderSpace k α E F) (i : Fin (k + 1)) :
    (inclusionL hβα f).iteratedFDeriv i = f.iteratedFDeriv i := by
  ext1 x
  rw [← iteratedFDeriv_eq, ← iteratedFDeriv_eq, coe_inclusionL]

/-- The exponent inclusion is injective. -/
theorem inclusionL_injective (hβα : β ≤ α) :
    Function.Injective (inclusionL (k := k) (E := E) (F := F) hβα) := fun f g h ↦
  ext fun x ↦ by simpa using congrFun (congrArg DFunLike.coe h) x

/-- The exponent inclusion of bounded `C^{k,α}` maps has norm at most `3`. -/
theorem norm_inclusionL_le_three (hβα : β ≤ α) :
    ‖inclusionL (k := k) (E := E) (F := F) hβα‖ ≤ 3 :=
  LinearMap.mkContinuous_norm_le _ zero_le_three _

/-- **The order inclusion of bounded Hölder spaces.** For `α ≤ 1`, every bounded `C^{k+1,α}` map
on `E` is a bounded `C^{k,α}` map: its `k`-th derivative is bounded with bounded derivative, hence
`α`-Hölder. The inclusion is a continuous linear map of norm at most `k + 4`
(`TauCeti.CkHolderSpace.norm_inclusionSuccL_le`). -/
def inclusionSuccL (hα : α ≤ 1) : CkHolderSpace (k + 1) α E F →L[ℝ] CkHolderSpace k α E F :=
  LinearMap.mkContinuous
    { toFun f := ofContDiff f (f.contDiff.of_le (by exact_mod_cast k.le_succ))
        (fun _ hi ↦ ⟨‖f‖, f.norm_iteratedFDeriv_apply_le (by omega)⟩)
        (f.holderWith_iteratedFDeriv_of_le hα k.le_succ).memHolder
      map_add' f g := by ext x; simp
      map_smul' c f := by ext x; simp }
    (k + 4) fun f ↦ by
      have h := norm_le_of_norm_iteratedFDeriv_le_of_holderWith (M := ‖f‖) (K := 3 * ‖f‖₊)
        (f := ofContDiff (k := k) (α := α) f (f.contDiff.of_le (by exact_mod_cast k.le_succ))
          (fun _ hi ↦ ⟨‖f‖, f.norm_iteratedFDeriv_apply_le (by omega)⟩)
          (f.holderWith_iteratedFDeriv_of_le hα k.le_succ).memHolder)
        (fun i hi x ↦ by
          rw [coe_ofContDiff]
          exact f.norm_iteratedFDeriv_apply_le (by omega) x)
        (by
          rw [coe_ofContDiff]
          exact f.holderWith_iteratedFDeriv_of_le hα k.le_succ)
      simp only [LinearMap.coe_mk, AddHom.coe_mk, NNReal.coe_mul, NNReal.coe_ofNat,
        coe_nnNorm] at h ⊢
      linarith

/-- The order inclusion does not change the underlying function. -/
@[simp]
theorem coe_inclusionSuccL (hα : α ≤ 1) (f : CkHolderSpace (k + 1) α E F) :
    ⇑(inclusionSuccL hα f) = ⇑f := by
  simp [inclusionSuccL]

/-- The order inclusion has norm at most `k + 4`. -/
theorem norm_inclusionSuccL_le (hα : α ≤ 1) :
    ‖inclusionSuccL (k := k) (E := E) (F := F) hα‖ ≤ k + 4 :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

end CkHolderSpace

end TauCeti
