/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Tactic.FieldSimp

/-!
# Uniform positivity of continuous functions

The continuous real-valued functions bounded below by a positive constant form a convex set.
On a compact domain this set is open for the uniform topology. These facts apply, for example,
to separating positive continuous functions in the proof of Pietsch domination.

A linear functional on `C(X, ℝ)` that is bounded above on the uniformly positive functions is
nonpositive on them, since they form a cone, and hence nonpositive on every nonnegative function:
adding a small positive constant to a nonnegative function makes it uniformly positive. This is the
positivity of the functional produced by separating the uniformly positive functions from a cone.

A continuous map from a compact space into a metric space (or normed additive group) stays at a
uniform positive distance from every point outside its range.

## Main results

* `ContinuousMap.convex_uniformlyPositive`: the uniformly positive functions form a convex set.
* `ContinuousMap.isOpen_uniformlyPositive`: on a compact space they form an open set.
* `ContinuousMap.exists_pos_le_dist_of_notMem_range`: a continuous map from a compact space into a
  metric space has `dist (f x) y` bounded below by a positive constant when `y ∉ Set.range f`.
* `ContinuousMap.exists_pos_le_norm_sub_of_notMem_range`: the normed-group form `δ ≤ ‖f x - y‖`.
* `ContinuousMap.exists_factor_lipschitzWith_one`: a continuous map from a product of compact spaces
  into a pseudometric space factors through continuous surjections onto compact pseudometric spaces
  as a continuous map whose slices in each variable are `1`-Lipschitz.
* `LinearMap.apply_nonpos_of_forall_uniformlyPositive_lt`: a functional bounded above on the
  uniformly positive functions is nonpositive on the nonnegative functions.
-/

public section

open Metric
open scoped BoundedContinuousFunction

namespace ContinuousMap

/-- The continuous real functions uniformly bounded below by a positive constant form a
convex set. -/
theorem convex_uniformlyPositive {X : Type*} [TopologicalSpace X] :
    Convex ℝ {h : C(X, ℝ) | ∃ δ > 0, ∀ x, δ ≤ h x} := by
  rintro h₁ ⟨δ₁, hδ₁, h₁δ⟩ h₂ ⟨δ₂, hδ₂, h₂δ⟩ a b ha hb hab
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun f ↦ ?_⟩
  have e₁ := (min_le_left δ₁ δ₂).trans (h₁δ f)
  have e₂ := (min_le_right δ₁ δ₂).trans (h₂δ f)
  simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
  calc
    min δ₁ δ₂ = a * min δ₁ δ₂ + b * min δ₁ δ₂ := by rw [← add_mul, hab, one_mul]
    _ ≤ a * h₁ f + b * h₂ f := by gcongr

/-- Uniform positivity is open in the uniform topology on continuous functions
on a compact space. -/
theorem isOpen_uniformlyPositive {X : Type*} [TopologicalSpace X] [CompactSpace X] :
    IsOpen {h : C(X, ℝ) | ∃ δ > 0, ∀ x, δ ≤ h x} := by
  refine Metric.isOpen_iff.2 ?_
  rintro h ⟨δ, hδ, hhδ⟩
  refine ⟨δ / 2, half_pos hδ, fun h' hh' ↦ ⟨δ / 2, half_pos hδ, fun f ↦ ?_⟩⟩
  have := (ContinuousMap.dist_apply_le_dist (f := h') (g := h) f).trans (mem_ball.1 hh').le
  rw [Real.dist_eq] at this
  linarith [hhδ f, (abs_le.1 this).1]

/-- A continuous map from a compact space into a metric space stays at a uniform positive distance
from every point outside its range. -/
theorem exists_pos_le_dist_of_notMem_range {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [MetricSpace Y] (f : C(X, Y)) {y : Y} (hy : y ∉ Set.range f) :
    ∃ δ > 0, ∀ x, δ ≤ dist (f x) y := by
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨1, zero_lt_one, isEmptyElim⟩
  · obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
      (f.continuous.dist continuous_const).continuousOn
    exact ⟨dist (f x₀) y, dist_pos.2 fun h ↦ hy ⟨x₀, h⟩, fun x ↦ hx₀ trivial⟩

/-- A continuous map from a compact space into a normed additive group has `‖f x - y‖` uniformly
bounded below by a positive constant whenever `y ∉ Set.range f`. -/
theorem exists_pos_le_norm_sub_of_notMem_range {X E : Type*} [TopologicalSpace X] [CompactSpace X]
    [NormedAddCommGroup E] (f : C(X, E)) {y : E} (hy : y ∉ Set.range f) :
    ∃ δ > 0, ∀ x, δ ≤ ‖f x - y‖ := by
  simpa only [dist_eq_norm] using f.exists_pos_le_dist_of_notMem_range hy

section

universe u v w

/-- **Compact double-currying factorisation.** Any continuous map `f : C(X × Y, Z)` from a product
of compact topological spaces into a pseudometric space factors as `f (x, y) = g (Φ x, Ψ y)`
through continuous surjections `Φ : X → K` and `Ψ : Y → L` onto compact pseudometric spaces, where
`g : K × L → Z` is continuous and `1`-Lipschitz in each variable separately. -/
theorem exists_factor_lipschitzWith_one {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y] [CompactSpace Y]
    [PseudoMetricSpace Z] (f : C(X × Y, Z)) :
    ∃ (K L : Type max v w) (_ : PseudoMetricSpace K) (_ : PseudoMetricSpace L),
      CompactSpace K ∧ CompactSpace L ∧
      ∃ (Φ : X → K) (Ψ : Y → L) (g : K × L → Z),
        Continuous Φ ∧ Function.Surjective Φ ∧
        Continuous Ψ ∧ Function.Surjective Ψ ∧
        Continuous g ∧
        (∀ l : L, LipschitzWith 1 fun k : K ↦ g (k, l)) ∧
        (∀ k : K, LipschitzWith 1 fun l : L ↦ g (k, l)) ∧
        ∀ x y, g (Φ x, Ψ y) = f (x, y) := by
  -- Currying `f` embeds `X` onto a compact subset `K ⊆ C(Y, Z)`.
  let K := Set.range f.curry
  have hKc : CompactSpace K := isCompact_iff_compactSpace.1 (isCompact_range f.curry.continuous)
  -- Evaluating on `Y × K` and currying again embeds `Y` onto a compact subset `L ⊆ C(K, Z)`.
  let evalYK : C(Y × K, Z) := ⟨fun p ↦ p.2.1 p.1,
    (continuous_eval : Continuous fun p : (Y →ᵇ Z) × Y ↦ p.1 p.2).comp
      (((ContinuousMap.isometryEquivBoundedOfCompact Y Z).continuous.comp
        (continuous_subtype_val.comp continuous_snd)).prodMk continuous_fst)⟩
  let L := Set.range evalYK.curry
  have hLc : CompactSpace L :=
    isCompact_iff_compactSpace.1 (isCompact_range evalYK.curry.continuous)
  let Φ : X → K := Set.rangeFactorization f.curry
  let Ψ : Y → L := Set.rangeFactorization evalYK.curry
  let g : K × L → Z := fun w ↦ w.2.1 w.1
  have evalYK_apply (y : Y) (k : K) : evalYK (y, k) = k.1 y := rfl
  have hgc : Continuous g :=
    (continuous_eval : Continuous fun p : (K →ᵇ Z) × K ↦ p.1 p.2).comp
      (((ContinuousMap.isometryEquivBoundedOfCompact K Z).continuous.comp
        (continuous_subtype_val.comp continuous_snd)).prodMk continuous_fst)
  refine ⟨K, L, inferInstance, inferInstance, hKc, hLc, Φ, Ψ, g,
    f.curry.continuous.rangeFactorization, Set.rangeFactorization_surjective,
    evalYK.curry.continuous.rangeFactorization, Set.rangeFactorization_surjective,
    hgc, fun l ↦ ?_, fun k ↦ ?_, fun x y ↦ ?_⟩
  · obtain ⟨y, hy⟩ := l.2
    refine LipschitzWith.of_dist_le_mul fun k₁ k₂ ↦ ?_
    have h₁ : g (k₁, l) = k₁.1 y := by
      dsimp only [g]
      rw [← hy, ContinuousMap.curry_apply, evalYK_apply]
    have h₂ : g (k₂, l) = k₂.1 y := by
      dsimp only [g]
      rw [← hy, ContinuousMap.curry_apply, evalYK_apply]
    simpa only [NNReal.coe_one, one_mul, h₁, h₂, Subtype.dist_eq] using
      ContinuousMap.dist_apply_le_dist (f := k₁.1) (g := k₂.1) y
  · refine LipschitzWith.of_dist_le_mul fun l₁ l₂ ↦ ?_
    simpa only [NNReal.coe_one, one_mul, g, Subtype.dist_eq] using
      ContinuousMap.dist_apply_le_dist (f := l₁.1) (g := l₂.1) k
  · dsimp only [g, Φ, Ψ]
    rw [Set.rangeFactorization_coe, ContinuousMap.curry_apply, evalYK_apply,
      Set.rangeFactorization_coe, ContinuousMap.curry_apply]

end

end ContinuousMap

namespace LinearMap

/-- A linear functional on `C(X, ℝ)` that is bounded above on the functions bounded below by a
positive constant is nonpositive on the nonnegative functions. -/
theorem apply_nonpos_of_forall_uniformlyPositive_lt {X : Type*} [TopologicalSpace X]
    (L : C(X, ℝ) →ₗ[ℝ] ℝ) {u : ℝ}
    (hL : ∀ h ∈ {h : C(X, ℝ) | ∃ δ > 0, ∀ x, δ ≤ h x}, L h < u) {h : C(X, ℝ)} (hh : 0 ≤ h) :
    L h ≤ 0 := by
  -- The uniformly positive functions form a cone, so `L` is nonpositive on them: if `L g > 0`,
  -- then `t • g` with `t = |u| / L g + 1` is uniformly positive and `L (t • g) = |u| + L g > u`.
  have hL' (g : C(X, ℝ)) (hg : g ∈ {h : C(X, ℝ) | ∃ δ > 0, ∀ x, δ ≤ h x}) : L g ≤ 0 := by
    obtain ⟨δ, hδ, hgδ⟩ := hg
    by_contra! hpos
    have ht : 0 < |u| / L g + 1 := by
      have := div_nonneg (abs_nonneg u) hpos.le
      linarith
    have hlt := hL ((|u| / L g + 1) • g) ⟨_, mul_pos ht hδ, fun x ↦ by
      simpa using mul_le_mul_of_nonneg_left (hgδ x) ht.le⟩
    rw [map_smul, smul_eq_mul, add_mul, div_mul_cancel₀ _ hpos.ne', one_mul] at hlt
    linarith [le_abs_self u]
  have hL1 : L 1 ≤ 0 := hL' 1 ⟨1, one_pos, fun _ ↦ le_rfl⟩
  have h1 : 0 < 1 - L 1 := by linarith
  -- If `0 < L h`, then `h + ε • 1` with `ε = L h / (1 - L 1)` is uniformly positive, and
  -- `L (h + ε • 1) = L h / (1 - L 1)` is positive.
  by_contra! hpos
  have hε : 0 < L h / (1 - L 1) := div_pos hpos h1
  have hle := hL' (h + (L h / (1 - L 1)) • 1) ⟨_, hε, fun x ↦ by simpa using hh x⟩
  rw [map_add, map_smul, smul_eq_mul] at hle
  have heq : L h + L h / (1 - L 1) * L 1 = L h / (1 - L 1) := by
    field_simp
    ring
  linarith

end LinearMap
