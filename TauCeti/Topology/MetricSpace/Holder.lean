/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.MetricSpace.HolderNorm
public import Mathlib.Topology.MetricSpace.Thickening

import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.ExtendFrom
import Mathlib.Topology.Instances.ENNReal.Lemmas
import TauCeti.Analysis.SpecificLimits.DyadicSum

/-!
# Hölder functions: a `dist` criterion, extension from a dense set, sums, and the seminorm

A Hölder bound stated with `dist` is equivalent to `HolderOnWith`, which Mathlib phrases with
`edist`. A function with bounded oscillation which satisfies a Hölder bound between nearby points
is Hölder, which turns Hölder bounds on the pieces of a cover into one on the whole set, and is
Hölder with every smaller exponent, with a constant depending on the scale; in particular, so is a
function which is Lipschitz between nearby points, and a locally Lipschitz function is Hölder of
every exponent at most one on each compact subset of its domain. Local Hölder bounds around the
points of a compact set are uniform on a thickening of the set.

A function which is Hölder continuous on a dense subset `s` of a pseudo-emetric space and takes
values in a complete emetric space extends to a function which is Hölder continuous on the whole
space, with the same constant and exponent.

For a positive exponent, the extension at a point of the closure of `s` is the limit of the
function along `s` (Mathlib's `extendFrom`), and the Hölder inequality passes from `s × s` to its
closure because both of its sides are continuous; the closure of a dense set is the whole space.
For exponent zero the Hölder condition only bounds the distances by the
constant, and the extension is the function itself on `s` and a constant off `s`, which need not
be continuous.

This is how an almost-everywhere Hölder estimate becomes a Hölder continuous representative: a set
of full measure for a measure that is positive on open sets is dense.

Sums, differences and finite sums of Hölder functions, also with natural multiplicities, are
Hölder, with the sum of the constants, so a sum over a finite type with a common constant `C` is
Hölder with constant `card ι * C`; a scalar multiple `a • f` is Hölder with the constant
multiplied by `‖a‖₊`; the reciprocal of a Hölder function bounded away from zero is Hölder; the
second differences `f (x + h) + f (x - h) - 2 f x` of a Hölder function on a normed group are
bounded by twice its constant times `‖h‖ ^ r`; and a pointwise limit of Hölder functions with a
common constant is Hölder with that constant.
For `0 < α < 1`, a series of pieces bounded by `a 2^{-jα}` and Lipschitz with constants
`b 2^{j(1-α)}` is `α`-Hölder; this is the dyadic summation behind the Hölder regularity of
Littlewood–Paley series.
Postcomposition with an isometry keeps the constant and the exponent, and postcomposition with a
`K`-Lipschitz map keeps the exponent and multiplies the constant by `K`. A function bounded by `M`
is Hölder of exponent zero with constant `2 M`.

Finally, on a metric space the infimum defining Mathlib's extended Hölder seminorm `eHolderNorm r f`
is attained, so the seminorm is the best constant in the Hölder inequality. Equivalently, it is the
supremum of the difference quotients `edist (f x) (f y) / edist x y ^ r` over pairs of distinct
points, the form in which Hölder seminorms are written in analysis texts.
Its truncation `nnHolderNorm r f` is homogeneous in scalar multiples of `f`, whether or not `f` is
Hölder. For `r = 1` it is the Lipschitz seminorm, the least Lipschitz constant. The seminorm is
lower semicontinuous for pointwise convergence, unchanged by postcomposition with an isometry (in
particular by an isometric star), and satisfies the Leibniz estimate
`[f g]_r ≤ ‖f‖_∞ [g]_r + ‖g‖_∞ [f]_r` for products of bounded maps into a seminormed ring.

By subadditivity of `t ↦ t ^ α`, the cusp `x ↦ ‖x‖ ^ α` is `α`-Hölder with constant `1` for
`α ≤ 1`.

For an `α`-Hölder `f` and a `β`-Hölder `g` between pseudo-extended metric spaces, the
`α β`-Hölder seminorm of `f ∘ g` is at most the seminorm of `f` times the `α`-th power of the
seminorm of `g`.

A family of maps that are Hölder near each point of a set, with a common constant and a common
positive exponent, is equicontinuous on that set
(`TauCeti.equicontinuousOn_of_forall_holderOnWith`).

## Main declarations

* `HolderOnWith.of_dist_le`: a Hölder bound stated with `dist` gives `HolderOnWith`; the converse
  is Mathlib's `HolderOnWith.dist_le`.
* `HolderOnWith.sub`: differences preserve the exponent and add the Hölder constants.
* `MemHolder.sub`: the difference of two `r`-Hölder functions is `r`-Hölder.
* `holderOnWith_iff_dist_le`: `HolderOnWith` is equivalent to the Hölder bound stated with `dist`.
* `HolderOnWith.isBounded_image`: a function Hölder on a bounded set has bounded image.
* `HolderOnWith.of_le_of_dist_le`: a function satisfying a `β`-Hölder bound between points at
  distance less than `δ > 0`, with values within distance `D` of each other, is `γ`-Hölder for
  `γ ≤ β`, with constant `K δ^(β - γ) + D δ^(-γ)`.
* `LipschitzOnWith.holderOnWith_of_norm_le`: a bounded `L`-Lipschitz function with norm bound
  `M` is Hölder of any exponent at most one with constant `L + 2 M`.
* `LocallyLipschitzOn.exists_holderOnWith_of_isCompact`: a function locally Lipschitz on `s` is
  Hölder of any exponent at most one on each compact subset of `s`.
* `HolderOnWith.of_dist_lt_of_dist_le`: a function satisfying a Hölder bound with constant `K`
  between points at distance less than `δ`, with values within distance `D` of each other, is
  Hölder with constant `K + D δ^(-r)`.
* `HolderOnWith.comp_const_smul`: precomposing with a rescaling `z ↦ a • z` multiplies the Hölder
  constant by `‖a‖ ^ r`.
* `HolderOnWith.dist_le_mul_rpow_of_mem_ball`: on a ball of radius `ρ`, a Hölder function with
  constant `C` and exponent `r` stays within `C ρ^r` of its value at the centre.
* `HolderOnWith.extend_of_dense`: a Hölder function on a dense set extends to a Hölder
  function on the whole space.
* `Isometry.comp_holderOnWith`, `Isometry.comp_holderWith`: postcomposition with an isometry
  preserves Hölder bounds.
* `Isometry.holderWith_comp_iff`: postcomposition with an isometry preserves global Hölder bounds
  in both directions.
* `LipschitzWith.comp_holderOnWith`, `LipschitzWith.comp_holderWith`: postcomposition with a
  `K`-Lipschitz map keeps the exponent and multiplies the Hölder constant by `K`.
* `HolderWith.comp_lipschitzWith_one`: precomposition with a `1`-Lipschitz map keeps the Hölder
  constant and exponent.
* `HolderWith.sum`: a finite sum of Hölder functions is Hölder.
* `HolderOnWith.congr`: Hölder continuity on a set transfers to a function agreeing there.
* `HolderOnWith.prodMk`: a pair of Hölder functions with a common exponent is Hölder.
* `HolderOnWith.add`: sums of Hölder functions on a set.
* `HolderOnWith.smul`: scalar multiples of Hölder functions on a set.
* `HolderWith.norm_add_add_sub_two_nsmul_le`: the second differences of an `r`-Hölder function
  with constant `C` are at most `2 C ‖h‖ ^ r`.
* `HolderOnWith.inv₀`: the reciprocal of a Hölder function bounded away from zero is Hölder.
* `HolderOnWith.of_tendsto`, `HolderWith.of_tendsto`: a pointwise limit of Hölder functions with
  a common constant is Hölder with that constant.
* `HolderOnWith.of_subset_closure`: a Hölder bound on `s` holds on every `t ⊆ closure s` at whose
  points the function is continuous within `s`.
* `HolderOnWith.exists_eqOn_holderOnWith_closure`: a function Hölder on `s` with a positive
  exponent and complete values extends to a function Hölder on the closure of `s`.
* `holderWith_zero_of_nnnorm_le`: a function bounded by `M` is Hölder of exponent zero with
  constant `2 M`.
* `TauCeti.exists_holderWith_tsum_of_rpow_mul_le`: for `0 < α < 1`, a series `∑ⱼ fⱼ` whose terms
  satisfy `‖fⱼ‖_∞ ≤ a 2^{-jα}` and are `b 2^{j(1-α)}`-Lipschitz is `α`-Hölder with constant
  `C (a + b)`.
* `IsCompact.exists_holderOnWith_thickening_and_norm_le`: a function which is Hölder on a ball
  around each point of a compact set `K` is Hölder with one constant, and bounded, on a thickening
  of `K`.
* `le_mul_edist_rpow_iff`: between distinct points, a bound by a multiple of `edist x y ^ r` is a
  bound on the difference quotient.
* `eHolderNorm_le_iff`: `eHolderNorm r f ≤ C` if and only if the Hölder inequality holds with the
  extended constant `C`.
* `edist_le_eHolderNorm_mul`: the Hölder inequality holds with the Hölder seminorm as constant.
* `MemHolder.eHolderNorm_comp_le`, `MemHolder.nnHolderNorm_comp_le`: the Hölder seminorm of a
  composition of Hölder functions.
* `eHolderNorm_eq_iSup`, `eHolderNorm_eq_iSup_dist`: the Hölder seminorm is the supremum of the
  difference quotients.
* `TauCeti.eHolderNorm_of_subsingleton`, `TauCeti.eHolderNorm_eq_edist_div_of_forall_eq_or_eq`:
  the Hölder seminorm on a space with at most one point is `0`, and on a space with at most two
  points it is the single difference quotient.
* `nnHolderNorm_smul`: scalar homogeneity of Mathlib's `nnHolderNorm`, without assuming that the
  map is Hölder.
* `TauCeti.eHolderNorm_one_le_coe_iff`: `eHolderNorm 1 f ≤ K` if and only if `f` is
  `K`-Lipschitz.
* `TauCeti.lowerSemicontinuous_eHolderNorm`: the Hölder seminorm is lower semicontinuous for
  pointwise convergence.
* `Isometry.eHolderNorm_comp`, `TauCeti.eHolderNorm_star`: postcomposition with an isometry, such
  as an isometric star, does not change the Hölder seminorm.
* `TauCeti.eHolderNorm_mul_le`: the Leibniz estimate for the Hölder seminorm of a product.
* `TauCeti.holderWith_norm_rpow`: the cusp `x ↦ ‖x‖ ^ α` is `α`-Hölder with constant `1` for
  `α ≤ 1`.
-/

public section

open Set Filter Topology
open scoped NNReal ENNReal

/-- A Hölder bound stated with `dist` gives `HolderOnWith`, which is phrased with `edist`. This is
the converse of `HolderOnWith.dist_le`. -/
theorem HolderOnWith.of_dist_le {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {C r : ℝ≥0} {f : X → Y} {s : Set X}
    (h : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ C * dist x y ^ (r : ℝ)) :
    HolderOnWith C r f s := by
  intro x hx y hy
  rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg r.coe_nonneg,
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal (h x hx y hy)

/-- The difference of two Hölder functions on a set has the same exponent and the sum
of their Hölder constants. -/
theorem HolderOnWith.sub {X Y : Type*} [PseudoMetricSpace X] [SeminormedAddCommGroup Y]
    {C D r : ℝ≥0} {f g : X → Y} {s : Set X}
    (hf : HolderOnWith C r f s) (hg : HolderOnWith D r g s) :
    HolderOnWith (C + D) r (f - g) s := by
  refine HolderOnWith.of_dist_le fun x hx y hy => ?_
  calc
    dist (f x - g x) (f y - g y) ≤ dist (f x) (f y) + dist (g x) (g y) :=
      dist_sub_sub_le _ _ _ _
    _ ≤ (C : ℝ) * dist x y ^ (r : ℝ) + (D : ℝ) * dist x y ^ (r : ℝ) :=
      add_le_add (hf.dist_le hx hy) (hg.dist_le hx hy)
    _ = _ := by rw [NNReal.coe_add, add_mul]

/-- The negation of a function Hölder on `s` is Hölder on `s` with the same constant and
exponent. -/
theorem HolderOnWith.neg {X Y : Type*} [PseudoEMetricSpace X] [SeminormedAddCommGroup Y]
    {C r : ℝ≥0} {f : X → Y} {s : Set X} (hf : HolderOnWith C r f s) :
    HolderOnWith C r (-f) s := fun x hx y hy => by
  simpa only [Pi.neg_apply, edist_neg_neg] using hf x hx y hy

/-- The negation of a Hölder function is Hölder with the same constant and exponent. -/
theorem HolderWith.neg {X Y : Type*} [PseudoEMetricSpace X] [SeminormedAddCommGroup Y]
    {C r : ℝ≥0} {f : X → Y} (hf : HolderWith C r f) : HolderWith C r (-f) :=
  holderOnWith_univ.1 ((hf.holderOnWith univ).neg)

/-- The difference of two `r`-Hölder functions is `r`-Hölder. Compare `MemHolder.add`. -/
theorem MemHolder.sub {X Y : Type*} [PseudoMetricSpace X] [SeminormedAddCommGroup Y] {r : ℝ≥0}
    {f g : X → Y} (hf : MemHolder r f) (hg : MemHolder r g) : MemHolder r (f - g) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  -- `HolderWith` is `HolderOnWith` on `univ`, where `HolderOnWith.sub` applies.
  exact ⟨C + D, holderOnWith_univ.1 ((hC.holderOnWith univ).sub (hD.holderOnWith univ))⟩

/-- `HolderOnWith` is equivalent to the Hölder bound stated with `dist`. Compare
`lipschitzOnWith_iff_dist_le_mul`. -/
theorem holderOnWith_iff_dist_le {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {C r : ℝ≥0} {f : X → Y} {s : Set X} :
    HolderOnWith C r f s ↔ ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ C * dist x y ^ (r : ℝ) :=
  ⟨fun hf _ hx _ hy => hf.dist_le hx hy, HolderOnWith.of_dist_le⟩

/-- A function Hölder on a bounded set has bounded image. Compare
`LipschitzWith.isBounded_image`. -/
theorem HolderOnWith.isBounded_image {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {C r : ℝ≥0} {f : X → Y} {s : Set X} (hf : HolderOnWith C r f s)
    (hs : Bornology.IsBounded s) : Bornology.IsBounded (f '' s) := by
  rw [Metric.isBounded_iff_ediam_ne_top] at hs ⊢
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
    (ENNReal.rpow_ne_top_of_nonneg r.coe_nonneg hs)) hf.ediam_image_le

/-- Postcomposition with an isometry preserves a Hölder bound on a set, with the same constant
and exponent. -/
theorem Isometry.comp_holderOnWith {X Y Z : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    [PseudoEMetricSpace Z] {g : Y → Z} (hg : Isometry g) {C r : ℝ≥0} {f : X → Y} {s : Set X}
    (hf : HolderOnWith C r f s) : HolderOnWith C r (g ∘ f) s := fun x hx y hy => by
  simpa only [Function.comp_apply, hg.edist_eq] using hf x hx y hy

/-- Postcomposition with an isometry preserves a global Hölder bound, with the same constant and
exponent. -/
theorem Isometry.comp_holderWith {X Y Z : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    [PseudoEMetricSpace Z] {g : Y → Z} (hg : Isometry g) {C r : ℝ≥0} {f : X → Y}
    (hf : HolderWith C r f) : HolderWith C r (g ∘ f) :=
  holderOnWith_univ.mp (hg.comp_holderOnWith (hf.holderOnWith univ))

/-- Postcomposition with a `K`-Lipschitz map preserves a Hölder bound on a set with the same
exponent, multiplying the constant by `K`. -/
theorem LipschitzWith.comp_holderOnWith {X Y Z : Type*} [PseudoEMetricSpace X]
    [PseudoEMetricSpace Y] [PseudoEMetricSpace Z] {K : ℝ≥0} {g : Y → Z} (hg : LipschitzWith K g)
    {C r : ℝ≥0} {f : X → Y} {s : Set X} (hf : HolderOnWith C r f s) :
    HolderOnWith (K * C) r (g ∘ f) s := by
  have h := hg.holderWith.comp_holderOnWith hf
  rwa [NNReal.coe_one, NNReal.rpow_one, one_mul] at h

/-- Postcomposition with a `K`-Lipschitz map preserves a global Hölder bound with the same
exponent, multiplying the constant by `K`. -/
theorem LipschitzWith.comp_holderWith {X Y Z : Type*} [PseudoEMetricSpace X]
    [PseudoEMetricSpace Y] [PseudoEMetricSpace Z] {K : ℝ≥0} {g : Y → Z} (hg : LipschitzWith K g)
    {C r : ℝ≥0} {f : X → Y} (hf : HolderWith C r f) : HolderWith (K * C) r (g ∘ f) :=
  holderOnWith_univ.mp (hg.comp_holderOnWith (hf.holderOnWith univ))

/-- Precomposition with a `1`-Lipschitz map preserves a global Hölder bound, with the same constant
and exponent. -/
theorem HolderWith.comp_lipschitzWith_one {X Y Z : Type*} [PseudoEMetricSpace X]
    [PseudoEMetricSpace Y] [PseudoEMetricSpace Z] {C r : ℝ≥0} {g : Y → Z} {f : X → Y}
    (hg : HolderWith C r g) (hf : LipschitzWith 1 f) : HolderWith C r (g ∘ f) := by
  have h := hg.comp (holderWith_one.2 hf)
  rwa [mul_one, NNReal.one_rpow, mul_one] at h

/-- Postcomposition with an isometry neither creates nor destroys a global Hölder bound: `g ∘ f`
is Hölder with constant `C` and exponent `r` exactly when `f` is. -/
theorem Isometry.holderWith_comp_iff {X Y Z : Type*} [PseudoEMetricSpace X]
    [PseudoEMetricSpace Y] [PseudoEMetricSpace Z] {g : Y → Z} (hg : Isometry g) {C r : ℝ≥0}
    {f : X → Y} : HolderWith C r (g ∘ f) ↔ HolderWith C r f := by
  simp only [HolderWith, Function.comp_apply, hg.edist_eq]

/-- A function that satisfies the Hölder bound with constant `K` and exponent `r` between points of
`s` at distance less than `δ > 0`, and whose values on `s` lie within distance `D` of each other,
is Hölder on `s` with constant `K + D δ^(-r)`. This passes from Hölder bounds on the pieces of a
cover of `s` to a Hölder bound on `s`, with `δ` a Lebesgue number of the cover
(`lebesgue_number_lemma_of_metric`). -/
theorem HolderOnWith.of_dist_lt_of_dist_le {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] {K D δ r : ℝ≥0} {f : X → Y} {s : Set X} (hδ : 0 < δ)
    (hf : ∀ x ∈ s, ∀ y ∈ s, dist x y < δ → dist (f x) (f y) ≤ K * dist x y ^ (r : ℝ))
    (hD : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ D) :
    HolderOnWith (K + D * δ ^ (-(r : ℝ))) r f s := by
  have hδ' : (0 : ℝ) < δ := hδ
  refine HolderOnWith.of_dist_le fun x hx y hy => ?_
  have hK : 0 ≤ (K : ℝ) * dist x y ^ (r : ℝ) := by positivity
  have hD' : 0 ≤ (D : ℝ) * (δ : ℝ) ^ (-(r : ℝ)) * dist x y ^ (r : ℝ) := by positivity
  push_cast
  rw [add_mul]
  rcases lt_or_ge (dist x y) δ with h | h
  · exact (hf x hx y hy h).trans (le_add_of_nonneg_right hD')
  · calc dist (f x) (f y) ≤ D := hD x hx y hy
      _ = D * (δ : ℝ) ^ (-(r : ℝ)) * (δ : ℝ) ^ (r : ℝ) := by
        rw [mul_assoc, ← Real.rpow_add hδ', neg_add_cancel, Real.rpow_zero, mul_one]
      _ ≤ D * (δ : ℝ) ^ (-(r : ℝ)) * dist x y ^ (r : ℝ) := by gcongr
      _ ≤ _ := le_add_of_nonneg_left hK

/-- A function that satisfies the `β`-Hölder bound with constant `K` between points of `s` at
distance less than `δ > 0`, and whose values on `s` lie within distance `D` of each other, is
`γ`-Hölder on `s` for every `γ ≤ β`, with constant `K δ^(β - γ) + D δ^(-γ)`: the `β`-Hölder bound
is used at distances less than `δ` and the bound `D` at larger distances. A small scale makes the
coefficient of `K` small at the price of a large coefficient of `D`. For `β = 1` the hypothesis is
a Lipschitz bound between nearby points, as given by a derivative bound on balls of radius `δ`.
Compare Mathlib's `HolderOnWith.of_le`, which bounds the domain instead of the values. -/
theorem HolderOnWith.of_le_of_dist_le {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {K D δ β γ : ℝ≥0} {f : X → Y} {s : Set X}
    (hf : ∀ x ∈ s, ∀ y ∈ s, dist x y < δ → dist (f x) (f y) ≤ K * dist x y ^ (β : ℝ))
    (hD : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ D) (hγβ : γ ≤ β) (hδ : 0 < δ) :
    HolderOnWith (K * δ ^ ((β : ℝ) - γ) + D * δ ^ (-(γ : ℝ))) γ f s := by
  have hγβ' : (γ : ℝ) ≤ β := hγβ
  refine HolderOnWith.of_dist_lt_of_dist_le hδ (fun x hx y hy h => ?_) hD
  push_cast
  calc dist (f x) (f y) ≤ K * dist x y ^ (β : ℝ) := hf x hx y hy h
    _ = K * dist x y ^ ((β : ℝ) - γ) * dist x y ^ (γ : ℝ) := by
      rw [mul_assoc, ← Real.rpow_add_of_nonneg dist_nonneg (sub_nonneg.2 hγβ') γ.coe_nonneg,
        sub_add_cancel]
    _ ≤ K * (δ : ℝ) ^ ((β : ℝ) - γ) * dist x y ^ (γ : ℝ) := by gcongr

/-- A function that is `β`-Hölder on `s` with constant `K` and bounded in norm by `D` there is
`γ`-Hölder on `s` for every `γ ≤ β`, with constant `K δ^(β - γ) + 2 D δ^(-γ)` for every scale
`δ > 0`. This is `HolderOnWith.of_le_of_dist_le` with the oscillation bounded by `2 D`. -/
theorem HolderOnWith.of_le_of_norm_le {X Y : Type*} [PseudoMetricSpace X]
    [SeminormedAddCommGroup Y] {K D δ β γ : ℝ≥0} {f : X → Y} {s : Set X}
    (hf : HolderOnWith K β f s) (hD : ∀ x ∈ s, ‖f x‖ ≤ D) (hγβ : γ ≤ β) (hδ : 0 < δ) :
    HolderOnWith (K * δ ^ ((β : ℝ) - γ) + 2 * D * δ ^ (-(γ : ℝ))) γ f s :=
  HolderOnWith.of_le_of_dist_le (fun x hx y hy _ => hf.dist_le hx hy)
    (fun x hx y hy => (dist_le_norm_add_norm _ _).trans (by
      push_cast; linarith [hD x hx, hD y hy])) hγβ hδ

/-- A `β`-Hölder function with constant `K` bounded in norm by `D` is `γ`-Hölder for every
`γ ≤ β`, with constant `K δ^(β - γ) + 2 D δ^(-γ)` for every scale `δ > 0`. -/
theorem HolderWith.of_le_of_norm_le {X Y : Type*} [PseudoMetricSpace X]
    [SeminormedAddCommGroup Y] {K D δ β γ : ℝ≥0} {f : X → Y} (hf : HolderWith K β f)
    (hD : ∀ x, ‖f x‖ ≤ D) (hγβ : γ ≤ β) (hδ : 0 < δ) :
    HolderWith (K * δ ^ ((β : ℝ) - γ) + 2 * D * δ ^ (-(γ : ℝ))) γ f :=
  holderOnWith_univ.1 ((hf.holderOnWith univ).of_le_of_norm_le (fun x _ => hD x) hγβ hδ)

/-- A function that is Hölder continuous with constant `C` and exponent `r` on the ball
`ball x₀ ρ` stays within `C ρ^r` of its value at the centre. -/
theorem HolderOnWith.dist_le_mul_rpow_of_mem_ball {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] {C r : ℝ≥0} {f : X → Y} {x₀ x : X} {ρ : ℝ}
    (hf : HolderOnWith C r f (Metric.ball x₀ ρ)) (hx : x ∈ Metric.ball x₀ ρ) :
    dist (f x) (f x₀) ≤ C * ρ ^ (r : ℝ) :=
  hf.dist_le_of_le hx (Metric.mem_ball_self (dist_nonneg.trans_lt (Metric.mem_ball.1 hx)))
    (Metric.mem_ball.1 hx).le

/-- A bounded Lipschitz map is Hölder for every exponent at most one, without a bounded-domain
assumption. The scale-one estimate uses the Lipschitz constant plus twice the value bound. -/
theorem LipschitzOnWith.holderOnWith_of_norm_le {X F : Type*}
    [PseudoMetricSpace X] [SeminormedAddCommGroup F]
    {s : Set X} {f : X → F}
    {L M α : ℝ≥0} (h : LipschitzOnWith L f s) (hb : ∀ x ∈ s, ‖f x‖ ≤ M) (hα : α ≤ 1) :
    HolderOnWith (L + 2 * M) α f s := by
  have hdiam : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ ((2 * M : ℝ≥0) : ℝ) := by
    intro x hx y hy
    rw [dist_eq_norm]
    exact (_root_.norm_sub_le _ _).trans (by push_cast; linarith [hb x hx, hb y hy])
  simpa using HolderOnWith.of_le_of_dist_le (K := L) (β := 1)
    (fun x hx y hy _ => by simpa using h.dist_le_mul x hx y hy) hdiam hα
    (by norm_num : (0 : ℝ≥0) < 1)

/-- A function locally Lipschitz on `s` is `α`-Hölder on each compact subset of `s`, for every
`α ≤ 1`. -/
theorem LocallyLipschitzOn.exists_holderOnWith_of_isCompact {X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y] {s K : Set X} {f : X → Y} {α : ℝ≥0}
    (hf : LocallyLipschitzOn s f) (hα : α ≤ 1) (hK : IsCompact K) (hKs : K ⊆ s) :
    ∃ C, HolderOnWith C α f K := by
  obtain ⟨L, hL⟩ := (hf.mono hKs).exists_lipschitzOnWith_of_compact hK
  obtain ⟨D, hD⟩ := Metric.isBounded_iff.1
    (hK.image_of_continuousOn (hf.mono hKs).continuousOn).isBounded
  exact ⟨_, HolderOnWith.of_le_of_dist_le (K := L) (D := D.toNNReal) (β := 1)
    (fun x hx y hy _ ↦ by simpa using hL.dist_le_mul x hx y hy)
    (fun x hx y hy ↦ (hD (mem_image_of_mem f hx) (mem_image_of_mem f hy)).trans
      (Real.le_coe_toNNReal D)) hα one_pos⟩

/-- If `g` is `r`-Hölder with constant `C` on `t` and rescaling by `a` maps `s` into `t`, then
`z ↦ g (a • z)` is `r`-Hölder on `s` with constant `C ‖a‖ ^ r`. -/
theorem HolderOnWith.comp_const_smul {𝕜 E X : Type*} [SeminormedRing 𝕜] [SeminormedAddGroup E]
    [SMulZeroClass 𝕜 E] [IsBoundedSMul 𝕜 E] [PseudoMetricSpace X] {g : E → X} {C r : ℝ≥0}
    {s t : Set E} (hg : HolderOnWith C r g t) (a : 𝕜) (hst : MapsTo (a • ·) s t) :
    HolderOnWith (C * ‖a‖₊ ^ (r : ℝ)) r (fun z ↦ g (a • z)) s := by
  have h := hg.comp ((lipschitzWith_smul a).holderWith.holderOnWith s) hst
  rw [mul_one] at h
  exact h

/-- A finite sum of Hölder functions with a common exponent is Hölder, with the sum of the
constants. -/
theorem HolderWith.sum {ι X Y : Type*} [PseudoMetricSpace X] [SeminormedAddCommGroup Y]
    {s : Finset ι} {C : ι → ℝ≥0} {r : ℝ≥0} {f : ι → X → Y}
    (hf : ∀ i ∈ s, HolderWith (C i) r (f i)) :
    HolderWith (∑ i ∈ s, C i) r (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact HolderWith.const
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)) (g := fun x => ∑ i ∈ s, f i x)

/-- A natural multiple `n • f` of an `r`-Hölder map `f` with constant `C` is `r`-Hölder with
constant `n C`. Compare Mathlib's `HolderWith.smul`, which needs a normed scalar group. -/
theorem HolderWith.nsmul {X Y : Type*} [PseudoMetricSpace X] [SeminormedAddCommGroup Y]
    {C r : ℝ≥0} {f : X → Y} (n : ℕ) (hf : HolderWith C r f) :
    HolderWith (n * C) r (n • f) := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, zero_smul]
    exact HolderWith.const
  | succ n ih =>
    simp only [succ_nsmul, Nat.cast_succ, add_mul, one_mul]
    exact ih.add hf

/-- A sum of `cᵢ` copies of maps `fᵢ` which are `r`-Hölder with constants `Cᵢ` is `r`-Hölder
with constant `∑ cᵢ Cᵢ`. -/
theorem HolderWith.sum_nsmul {ι X Y : Type*} [PseudoMetricSpace X] [SeminormedAddCommGroup Y]
    {C : ι → ℝ≥0} {r : ℝ≥0} (s : Finset ι) (c : ι → ℕ) {f : ι → X → Y}
    (hf : ∀ i ∈ s, HolderWith (C i) r (f i)) :
    HolderWith (∑ i ∈ s, c i * C i) r fun x ↦ ∑ i ∈ s, c i • f i x :=
  HolderWith.sum fun i hi ↦ (hf i hi).nsmul (c i)

/-- A function that agrees on `s` with a function Hölder on `s` is Hölder on `s`, with the same
constant and exponent. -/
theorem HolderOnWith.congr {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    {C r : ℝ≥0} {f g : X → Y} {s : Set X} (hf : HolderOnWith C r f s) (h : EqOn f g s) :
    HolderOnWith C r g s := fun x hx y hy => by
  rw [← h hx, ← h hy]
  exact hf x hx y hy

/-- Two functions that are Hölder on `s` with a common exponent give a pair that is Hölder on `s`
with that exponent, with the larger of the two constants: the extended distance on a product is
the maximum of the distances of the components. -/
theorem HolderOnWith.prodMk {X Y Z : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    [PseudoEMetricSpace Z] {C D r : ℝ≥0} {f : X → Y} {g : X → Z} {s : Set X}
    (hf : HolderOnWith C r f s) (hg : HolderOnWith D r g s) :
    HolderOnWith (max C D) r (fun x => (f x, g x)) s := fun x hx y hy => by
  rw [Prod.edist_eq]
  exact max_le ((hf x hx y hy).trans (by gcongr; exact le_max_left C D))
    ((hg x hx y hy).trans (by gcongr; exact le_max_right C D))

/-- The sum of two functions that are Hölder on `s` with a common exponent is Hölder on `s`, with
the sum of the constants. Compare Mathlib's `HolderWith.add`. -/
theorem HolderOnWith.add {X Y : Type*} [PseudoMetricSpace X] [SeminormedAddCommGroup Y]
    {C C' r : ℝ≥0} {f g : X → Y} {s : Set X} (hf : HolderOnWith C r f s)
    (hg : HolderOnWith C' r g s) : HolderOnWith (C + C') r (f + g) s :=
  HolderOnWith.of_dist_le fun x hx y hy => by
    simp only [Pi.add_apply, NNReal.coe_add]
    linarith [dist_add_add_le (f x) (g x) (f y) (g y), hf.dist_le hx hy, hg.dist_le hx hy]

/-- A finite sum of functions that are Hölder on `t` with a common exponent is Hölder on `t`, with
the sum of the constants. Compare `HolderWith.sum`. -/
theorem HolderOnWith.sum {ι X Y : Type*} [PseudoMetricSpace X] [SeminormedAddCommGroup Y]
    {s : Finset ι} {C : ι → ℝ≥0} {r : ℝ≥0} {f : ι → X → Y} {t : Set X}
    (hf : ∀ i ∈ s, HolderOnWith (C i) r (f i) t) :
    HolderOnWith (∑ i ∈ s, C i) r (fun x => ∑ i ∈ s, f i x) t :=
  HolderWith.restrict_iff.1 (HolderWith.sum fun i hi => (hf i hi).holderWith)

/-- A sum over a finite type of functions that are Hölder on `t` with a common constant `C` is
Hölder on `t` with constant `card ι * C`. -/
theorem HolderOnWith.fintype_sum {ι X Y : Type*} [Fintype ι] [PseudoMetricSpace X]
    [SeminormedAddCommGroup Y] {C r : ℝ≥0} {f : ι → X → Y} {t : Set X}
    (hf : ∀ i, HolderOnWith C r (f i) t) :
    HolderOnWith (Fintype.card ι * C) r (fun x => ∑ i, f i x) t := by
  simpa using HolderOnWith.sum (s := Finset.univ) fun i _ => hf i

/-- A scalar multiple `a • f` of a function that is Hölder on `s` is Hölder on `s`, with the
constant multiplied by `‖a‖₊`. Compare Mathlib's `HolderWith.smul`. -/
theorem HolderOnWith.smul {X Y 𝕜 : Type*} [PseudoMetricSpace X] [SeminormedAddCommGroup Y]
    [SeminormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 Y] [IsBoundedSMul 𝕜 Y] {C r : ℝ≥0} {f : X → Y}
    {s : Set X} (a : 𝕜) (hf : HolderOnWith C r f s) : HolderOnWith (C * ‖a‖₊) r (a • f) s :=
  HolderWith.restrict_iff.1 (hf.holderWith.smul a)

/-- The second differences of an `r`-Hölder function with constant `C` on a normed group are at
most `2 C ‖h‖ ^ r`. -/
theorem HolderWith.norm_add_add_sub_two_nsmul_le {X Y : Type*} [SeminormedAddCommGroup X]
    [SeminormedAddCommGroup Y] {C r : ℝ≥0} {f : X → Y} (hf : HolderWith C r f) (x h : X) :
    ‖f (x + h) + f (x - h) - 2 • f x‖ ≤ 2 * C * ‖h‖ ^ (r : ℝ) := by
  have h₁ : ‖f (x + h) - f x‖ ≤ C * ‖h‖ ^ (r : ℝ) := by
    simpa [dist_eq_norm] using hf.dist_le (x + h) x
  have h₂ : ‖f (x - h) - f x‖ ≤ C * ‖h‖ ^ (r : ℝ) := by
    simpa [dist_eq_norm] using hf.dist_le (x - h) x
  have heq : f (x + h) + f (x - h) - 2 • f x = (f (x + h) - f x) + (f (x - h) - f x) := by
    rw [two_nsmul]
    abel
  rw [heq]
  linarith [norm_add_le (f (x + h) - f x) (f (x - h) - f x)]

/-- The reciprocal of a function that is Hölder on `s` and bounded away from `0` there, by
`‖f x‖ ≥ m > 0`, is Hölder on `s` with the same exponent and constant `C / m ^ 2`. -/
theorem HolderOnWith.inv₀ {X 𝕜 : Type*} [PseudoMetricSpace X] [NormedDivisionRing 𝕜]
    {C r m : ℝ≥0} {f : X → 𝕜} {s : Set X} (hf : HolderOnWith C r f s) (hm : 0 < m)
    (hfm : ∀ x ∈ s, m ≤ ‖f x‖₊) : HolderOnWith (C / m ^ 2) r (fun x ↦ (f x)⁻¹) s := by
  refine HolderOnWith.of_dist_le fun x hx y hy => ?_
  have hm' : (0 : ℝ) < m := hm
  have hmx : (m : ℝ) ≤ ‖f x‖ := hfm x hx
  have hmy : (m : ℝ) ≤ ‖f y‖ := hfm y hy
  have hx0 : f x ≠ 0 := norm_pos_iff.1 (hm'.trans_le hmx)
  have hy0 : f y ≠ 0 := norm_pos_iff.1 (hm'.trans_le hmy)
  rw [dist_eq_norm, inv_sub_inv' hx0 hy0]
  simp only [norm_mul, norm_inv, ← dist_eq_norm', NNReal.coe_div, NNReal.coe_pow]
  calc ‖f x‖⁻¹ * dist (f x) (f y) * ‖f y‖⁻¹
      ≤ (m : ℝ)⁻¹ * (C * dist x y ^ (r : ℝ)) * (m : ℝ)⁻¹ := by
        gcongr
        exact hf.dist_le hx hy
    _ = C / m ^ 2 * dist x y ^ (r : ℝ) := by
        field_simp

/-- A pointwise limit on `s` of maps that are `r`-Hölder on `s` with a common constant `C` is
`r`-Hölder on `s` with constant `C`. -/
theorem HolderOnWith.of_tendsto {ι X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    {l : Filter ι} [l.NeBot] {C r : ℝ≥0} {u : ι → X → Y} {v : X → Y} {s : Set X}
    (hu : ∀ x ∈ s, Tendsto (fun n ↦ u n x) l (𝓝 (v x)))
    (hC : ∀ᶠ n in l, HolderOnWith C r (u n) s) :
    HolderOnWith C r v s := fun x hx y hy ↦
  le_of_tendsto ((hu x hx).edist (hu y hy)) (hC.mono fun _ hn ↦ hn x hx y hy)

/-- A function that is Hölder on `s` and continuous within `s` at the points of `t ⊆ closure s`
is Hölder on `t` with the same constant and exponent: the Hölder inequality passes to the closure
of `s × s` by continuity within that product. -/
theorem HolderOnWith.of_subset_closure {X Y : Type*} [PseudoEMetricSpace X]
    [PseudoEMetricSpace Y] {C r : ℝ≥0} {f : X → Y} {s t : Set X} (h : HolderOnWith C r f s)
    (hts : t ⊆ closure s) (hf : ∀ x ∈ t, ContinuousWithinAt f s x) : HolderOnWith C r f t := by
  intro a ha b hb
  have hab : (a, b) ∈ closure (s ×ˢ s) := by
    rw [closure_prod_eq]
    exact ⟨hts ha, hts hb⟩
  have h1 : ContinuousWithinAt (fun q : X × X => edist (f q.1) (f q.2)) (s ×ˢ s) (a, b) :=
    ((hf a ha).comp continuousWithinAt_fst mapsTo_fst_prod).edist
      ((hf b hb).comp continuousWithinAt_snd mapsTo_snd_prod)
  have h2 : Continuous fun q : X × X => (C : ℝ≥0∞) * edist q.1 q.2 ^ (r : ℝ) :=
    (ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp
      (ENNReal.continuous_rpow_const.comp continuous_edist)
  exact ContinuousWithinAt.closure_le hab h1 h2.continuousWithinAt
    fun q hq => h q.1 hq.1 q.2 hq.2

/-- **Hölder functions extend to the closure.** A function which is Hölder continuous on `s`, with
a positive exponent and values in a complete space, agrees on `s` with a function which is Hölder
continuous on the closure of `s`, with the same constant and exponent. The extension at a point of
the closure is the limit of `f` along `s`, which is Mathlib's `extendFrom s f`. Compare
`HolderOnWith.extend_of_dense`, which extends from a dense set to the whole space. -/
theorem HolderOnWith.exists_eqOn_holderOnWith_closure {X Y : Type*} [PseudoEMetricSpace X]
    [EMetricSpace Y] [CompleteSpace Y] {C r : ℝ≥0} {f : X → Y} {s : Set X}
    (hf : HolderOnWith C r f s) (hr : 0 < r) :
    ∃ g : X → Y, EqOn g f s ∧ HolderOnWith C r g (closure s) := by
  have hlim (x : X) (hx : x ∈ closure s) : ∃ y, Tendsto f (𝓝[s] x) (𝓝 y) := by
    have := mem_closure_iff_nhdsWithin_neBot.1 hx
    exact CompleteSpace.complete
      ((cauchy_nhds.mono nhdsWithin_le_nhds).map_of_le (hf.uniformContinuousOn hr) inf_le_right)
  have heq : EqOn (extendFrom s f) f s := extendFrom_extends (hf.continuousOn hr)
  refine ⟨extendFrom s f, heq, (hf.congr heq.symm).of_subset_closure subset_rfl fun x hx ↦ ?_⟩
  exact (tendsto_extendFrom (hlim x hx)).congr'
    (eventually_nhdsWithin_of_forall fun y hy ↦ (heq hy).symm)

/-- **Hölder functions extend from dense sets.** If `f` is Hölder continuous with constant `C` and
exponent `r` on a dense set `s`, and the target is complete, then some function which is Hölder
continuous with constant `C` and exponent `r` on the whole space agrees with `f` on `s`. For
`r = 0` the Hölder condition only bounds the distances by `C`, so the extension need not be
continuous.
Compare `LipschitzOnWith.extend_real`, which needs no density but only applies to real values. -/
theorem HolderOnWith.extend_of_dense {X Y : Type*} [PseudoEMetricSpace X] [EMetricSpace Y]
    [CompleteSpace Y] {C r : ℝ≥0} {f : X → Y} {s : Set X} (hf : HolderOnWith C r f s)
    (hs : Dense s) : ∃ g : X → Y, HolderWith C r g ∧ EqOn f g s := by
  classical
  rcases eq_or_ne r 0 with rfl | hr
  · -- Exponent zero: the condition says `edist ≤ C`; extend by a constant off `s`.
    have key : ∀ x ∈ s, ∀ y ∈ s, edist (f x) (f y) ≤ C := fun x hx y hy => by
      simpa using hf x hx y hy
    rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
    · have hX : IsEmpty X := ⟨fun x => by simpa using hs.nonempty_iff.2 ⟨x⟩⟩
      exact ⟨f, fun x => (hX.false x).elim, by simp⟩
    · refine ⟨fun x => if x ∈ s then f x else f x₀, fun x y => ?_, fun x hx => by simp [hx]⟩
      have h0 : edist x y ^ (((0 : ℝ≥0) : ℝ)) = 1 := by simp
      rw [h0, mul_one]
      by_cases hx : x ∈ s <;> by_cases hy : y ∈ s <;> simp only [hx, hy, ite_true, ite_false]
      · exact key _ hx _ hy
      · exact key _ hx _ hx₀
      · exact key _ hx₀ _ hy
      · simp
  obtain ⟨g, hgf, hg⟩ := hf.exists_eqOn_holderOnWith_closure (pos_iff_ne_zero.2 hr)
  rw [hs.closure_eq, holderOnWith_univ] at hg
  exact ⟨g, hg, hgf.symm⟩

/-- A pointwise limit of maps that are `r`-Hölder with a common constant `C` is `r`-Hölder with
constant `C`. -/
theorem HolderWith.of_tendsto {ι X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    {l : Filter ι} [l.NeBot] {C r : ℝ≥0} {u : ι → X → Y} {v : X → Y}
    (hu : ∀ x, Tendsto (fun n ↦ u n x) l (𝓝 (v x))) (hC : ∀ᶠ n in l, HolderWith C r (u n)) :
    HolderWith C r v :=
  holderOnWith_univ.mp <| HolderOnWith.of_tendsto (fun x _ ↦ hu x)
    (hC.mono fun _ hn ↦ holderOnWith_univ.mpr hn)

/-- A function bounded by `M` has oscillation at most `2 M`, which is its Hölder bound of
exponent zero. Compare Mathlib's `HolderWith.holderWith_zero_of_bounded`, which bounds the
oscillation of a Hölder function on a bounded space instead. -/
theorem holderWith_zero_of_nnnorm_le {X Y : Type*} [PseudoEMetricSpace X]
    [SeminormedAddCommGroup Y] {f : X → Y} {M : ℝ≥0} (hf : ∀ x, ‖f x‖₊ ≤ M) :
    HolderWith (2 * M) 0 f := fun x y ↦ by
  rw [NNReal.coe_zero, ENNReal.rpow_zero, mul_one, edist_nndist, ENNReal.coe_le_coe,
    nnDist_eq_nnNorm, two_mul]
  exact (nnNorm_sub_le _ _).trans (add_le_add (hf x) (hf y))

/-- **Local Hölder bounds near a compact set are uniform on a thickening.** If `f` is `α`-Hölder on
a ball around each point of a compact set `K`, with radii and constants depending on the point, then
on some open thickening of `K` the function `f` is `α`-Hölder with one constant and is bounded. -/
theorem IsCompact.exists_holderOnWith_thickening_and_norm_le {X Y : Type*} [PseudoMetricSpace X]
    [SeminormedAddCommGroup Y] {K : Set X} (hK : IsCompact K) {α : ℝ≥0} {f : X → Y}
    (hf : ∀ x ∈ K, ∃ r > 0, ∃ L : ℝ≥0, HolderOnWith L α f (Metric.ball x r)) :
    ∃ δ > 0, ∃ L M : ℝ≥0, HolderOnWith L α f (Metric.thickening δ K) ∧
      ∀ y ∈ Metric.thickening δ K, ‖f y‖ ≤ M := by
  choose! r hr L hL using hf
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover (fun x => Metric.ball x (r x)) fun x hx =>
    Metric.ball_mem_nhds x (hr x hx)
  -- A Lebesgue number `δ₀` of the finite cover by the balls `B(z, r z)`, `z ∈ t`.
  obtain ⟨δ₀, hδ₀, hδ₀K⟩ := lebesgue_number_lemma_of_metric hK
    (c := fun z : t => Metric.ball (z : X) (r z)) (fun _ => Metric.isOpen_ball) fun y hy => by
      obtain ⟨z, hzt, hyz⟩ := mem_iUnion₂.1 (hcover hy)
      exact mem_iUnion.2 ⟨⟨z, hzt⟩, hyz⟩
  -- Two points of the `δ₀ / 2`-thickening at distance less than `δ₀ / 2` lie in one ball `B(x, δ₀)`
  -- about a point `x ∈ K`, hence in one ball `B(z, r z)` of the cover.
  have hball : ∀ y ∈ Metric.thickening (δ₀ / 2) K, ∀ y', dist y y' < δ₀ / 2 →
      ∃ z ∈ t, y ∈ Metric.ball z (r z) ∧ y' ∈ Metric.ball z (r z) := by
    intro y hy y' hyy'
    obtain ⟨x, hxK, hyx⟩ := Metric.mem_thickening_iff.1 hy
    obtain ⟨⟨z, hzt⟩, hz⟩ := hδ₀K x hxK
    refine ⟨z, hzt, hz (Metric.mem_ball.2 (by linarith)), hz (Metric.mem_ball.2 ?_)⟩
    linarith [dist_triangle y' y x, dist_comm y y']
  set M : ℝ≥0 := ∑ z ∈ t, (‖f z‖₊ + L z * (r z).toNNReal ^ (α : ℝ))
  have hM : ∀ y ∈ Metric.thickening (δ₀ / 2) K, ‖f y‖ ≤ M := by
    intro y hy
    obtain ⟨z, hzt, hyz, -⟩ := hball y hy y (by rw [dist_self]; positivity)
    calc ‖f y‖ ≤ ‖f z‖ + dist (f y) (f z) := by
          linarith [norm_le_norm_add_norm_sub' (f y) (f z), dist_eq_norm (f y) (f z)]
      _ ≤ ‖f z‖ + L z * (r z) ^ (α : ℝ) := by
          gcongr
          exact (hL z (htK z hzt)).dist_le_mul_rpow_of_mem_ball hyz
      _ = ((‖f z‖₊ + L z * (r z).toNNReal ^ (α : ℝ) : ℝ≥0) : ℝ) := by
          rw [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_rpow,
            Real.coe_toNNReal _ (hr z (htK z hzt)).le, coe_nnNorm]
      _ ≤ M := by
          exact_mod_cast Finset.single_le_sum
            (f := fun z => ‖f z‖₊ + L z * (r z).toNNReal ^ (α : ℝ)) (fun _ _ => zero_le) hzt
  set δ : ℝ≥0 := ⟨δ₀ / 2, by positivity⟩
  have hδ : 0 < δ := by rw [← NNReal.coe_pos]; exact half_pos hδ₀
  refine ⟨δ₀ / 2, half_pos hδ₀, ∑ z ∈ t, L z + 2 * M * δ ^ (-(α : ℝ)), M, ?_, hM⟩
  refine HolderOnWith.of_dist_lt_of_dist_le hδ (fun y hy y' _ hyy' => ?_) fun y hy y' hy' => ?_
  · obtain ⟨z, hzt, hyz, hy'z⟩ := hball y hy y' hyy'
    refine ((hL z (htK z hzt)).dist_le hyz hy'z).trans ?_
    gcongr
    exact_mod_cast Finset.single_le_sum (fun _ _ => zero_le) hzt
  · push_cast
    linarith [dist_le_norm_add_norm (f y) (f y'), hM y hy, hM y' hy']

namespace TauCeti

/-- **Dyadic sums of smooth pieces are Hölder.** For `0 < α < 1` there is `C` such that, if the
functions `fⱼ`, `j ∈ ℕ`, satisfy `‖fⱼ‖_∞ ≤ a 2^{-jα}` and are Lipschitz with constants
`b 2^{j(1-α)}`, then `∑ⱼ fⱼ` is `α`-Hölder with constant `C (a + b)`. This is how the
Littlewood–Paley pieces of a Hölder–Zygmund distribution reassemble into a Hölder function. -/
theorem exists_holderWith_tsum_of_rpow_mul_le {X Y : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup Y] [CompleteSpace Y] {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ≥0, ∀ (f : ℕ → X → Y) (a b : ℝ≥0),
      (∀ (j : ℕ) x, 2 ^ ((α : ℝ) * j) * ‖f j x‖ ≤ a) →
      (∀ (j : ℕ) x y, 2 ^ ((α : ℝ) * j) * dist (f j x) (f j y) ≤ b * 2 ^ j * dist x y) →
      HolderWith (C * (a + b)) α fun x ↦ ∑' j, f j x := by
  obtain ⟨C, hC0, hC⟩ := exists_tsum_le_mul_rpow_of_rpow_mul_le (α := α) hα0 hα1
  refine ⟨(2 * C).toNNReal, fun f a b ha hb ↦ ?_⟩
  -- Each `f · x` is summable: its terms satisfy both bounds with `b = a` and `d = 1`.
  have hsum : ∀ x, Summable fun j ↦ f j x := fun x ↦
    (hC (fun j ↦ ‖f j x‖) a.coe_nonneg a.coe_nonneg zero_le_one (fun _ ↦ norm_nonneg _)
      (ha · x) fun j ↦ (ha j x).trans (by
        rw [mul_one]
        exact le_mul_of_one_le_right a.coe_nonneg (one_le_pow₀ one_le_two))).1.of_norm
  rw [← holderOnWith_univ]
  refine HolderOnWith.of_dist_le fun x _ y _ ↦ ?_
  -- The increments `dist (f j x) (f j y)` satisfy both bounds with `2 a`, `b` and `d = dist x y`.
  obtain ⟨hgs, hg⟩ := hC (fun j ↦ dist (f j x) (f j y)) (a := 2 * a) (by positivity)
    b.coe_nonneg dist_nonneg (fun _ ↦ dist_nonneg) (fun j ↦ by
      have := dist_le_norm_add_norm (f j x) (f j y)
      nlinarith [ha j x, ha j y, Real.rpow_nonneg zero_le_two ((α : ℝ) * j)])
    (hb · x y)
  calc dist (∑' j, f j x) (∑' j, f j y) ≤ ∑' j, dist (f j x) (f j y) := by
        rw [dist_eq_norm, ← (hsum x).tsum_sub (hsum y)]
        simp only [dist_eq_norm] at hgs ⊢
        exact norm_tsum_le_tsum_norm hgs
    _ ≤ C * (2 * a + b) * dist x y ^ (α : ℝ) := hg
    _ ≤ ((2 * C).toNNReal * (a + b) : ℝ≥0) * dist x y ^ (α : ℝ) := by
        rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity), NNReal.coe_add]
        exact mul_le_mul_of_nonneg_right (by nlinarith [a.coe_nonneg, b.coe_nonneg])
          (by positivity)

end TauCeti

/-- Between distinct points `x ≠ y` of a metric space, a bound `a ≤ C * edist x y ^ r` is
equivalent to the bound `a / edist x y ^ r ≤ C` on the difference quotient. -/
theorem le_mul_edist_rpow_iff {X : Type*} [MetricSpace X] {r : ℝ≥0} {a C : ℝ≥0∞}
    {x y : X} (hxy : x ≠ y) :
    a ≤ C * edist x y ^ (r : ℝ) ↔ a / edist x y ^ (r : ℝ) ≤ C :=
  (ENNReal.div_le_iff (ENNReal.rpow_pos (edist_pos.2 hxy) (edist_ne_top x y)).ne'
    (ENNReal.rpow_ne_top_of_nonneg r.coe_nonneg (edist_ne_top x y))).symm

/-- The Hölder seminorm is bounded by an extended constant `C` exactly when the Hölder inequality
holds with constant `C`. -/
theorem eHolderNorm_le_iff {X Y : Type*} [MetricSpace X] [PseudoEMetricSpace Y] {r : ℝ≥0}
    {f : X → Y} {C : ℝ≥0∞} :
    eHolderNorm r f ≤ C ↔ ∀ x y, edist (f x) (f y) ≤ C * edist x y ^ (r : ℝ) := by
  constructor
  · intro h x y
    rcases eq_or_ne x y with rfl | hxy
    · simp
    rw [le_mul_edist_rpow_iff hxy]
    exact (le_iInf₂ fun c hc => ENNReal.div_le_of_le_mul (hc x y)).trans h
  · intro h
    rcases eq_or_ne C ∞ with rfl | hC
    · exact le_top
    lift C to ℝ≥0 using hC
    exact HolderWith.eHolderNorm_le h

/-- The Hölder inequality with the Hölder seminorm as constant. -/
theorem edist_le_eHolderNorm_mul {X Y : Type*} [MetricSpace X] [PseudoEMetricSpace Y] (r : ℝ≥0)
    (f : X → Y) (x y : X) :
    edist (f x) (f y) ≤ eHolderNorm r f * edist x y ^ (r : ℝ) :=
  eHolderNorm_le_iff.1 le_rfl x y

/-- **The extended Hölder seminorm of a composition.** If `f` is `α`-Hölder and `g` is `β`-Hölder,
then the `α β`-Hölder seminorm of `f ∘ g` is at most `eHolderNorm α f * eHolderNorm β g ^ α`.

The spaces `X'`, `X` and `Z` may be pseudo-extended metric spaces: no separation is needed. -/
theorem MemHolder.eHolderNorm_comp_le {X' X Z : Type*} [PseudoEMetricSpace X']
    [PseudoEMetricSpace X] [PseudoEMetricSpace Z] {α β : ℝ≥0} {f : X → Z} (hf : MemHolder α f)
    {g : X' → X} (hg : MemHolder β g) :
    eHolderNorm (α * β) (f ∘ g) ≤ eHolderNorm α f * eHolderNorm β g ^ (α : ℝ) := by
  -- The infimum defining `eHolderNorm` need not be attained, so bound the seminorm of `f ∘ g` by
  -- `C * D ^ α` for every pair of Hölder constants `C` of `f` and `D` of `g` (`HolderWith.comp`)
  -- and pass to the infimum.
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  have : Nonempty {D // HolderWith D β g} := ⟨⟨D, hD⟩⟩
  conv_rhs => rw [eHolderNorm, eHolderNorm, iInf_subtype', iInf_subtype',
    ENNReal.iInf_rpow_of_nonneg α.coe_nonneg]
  refine ENNReal.le_iInf_mul_iInf ⟨⟨C, hC⟩, ENNReal.coe_ne_top⟩
    ⟨⟨D, hD⟩, ENNReal.rpow_ne_top_of_nonneg α.coe_nonneg ENNReal.coe_ne_top⟩
    fun C D ↦ ?_
  rw [← ENNReal.coe_rpow_of_nonneg _ α.coe_nonneg, ← ENNReal.coe_mul]
  exact (C.property.comp D.property).eHolderNorm_le

/-- **The Hölder seminorm of a composition.** If `f` is `α`-Hölder and `g` is `β`-Hölder, then the
`α β`-Hölder seminorm of `f ∘ g` is at most `nnHolderNorm α f * nnHolderNorm β g ^ α`. For a
`K`-Lipschitz `g` (`β = 1`) the factor is at most `K ^ α`.

The spaces `X'`, `X` and `Z` may be pseudo-extended metric spaces: no separation is needed. -/
theorem MemHolder.nnHolderNorm_comp_le {X' X Z : Type*} [PseudoEMetricSpace X']
    [PseudoEMetricSpace X] [PseudoEMetricSpace Z] {α β : ℝ≥0} {f : X → Z} (hf : MemHolder α f)
    {g : X' → X} (hg : MemHolder β g) :
    nnHolderNorm (α * β) (f ∘ g) ≤ nnHolderNorm α f * nnHolderNorm β g ^ (α : ℝ) := by
  have hf' : (nnHolderNorm α f : ℝ≥0∞) = eHolderNorm α f :=
    ENNReal.coe_toNNReal hf.eHolderNorm_ne_top
  have hg' : (nnHolderNorm β g : ℝ≥0∞) = eHolderNorm β g :=
    ENNReal.coe_toNNReal hg.eHolderNorm_ne_top
  rw [← ENNReal.coe_le_coe, ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg _ α.coe_nonneg, hf', hg']
  exact coe_nnHolderNorm_le_eHolderNorm.trans (hf.eHolderNorm_comp_le hg)

/-- The Hölder seminorm is the supremum of the difference quotients
`edist (f x) (f y) / edist x y ^ r` over pairs of distinct points. -/
theorem eHolderNorm_eq_iSup {X Y : Type*} [MetricSpace X] [PseudoEMetricSpace Y] {r : ℝ≥0}
    {f : X → Y} :
    eHolderNorm r f = ⨆ (x) (y) (_ : x ≠ y), edist (f x) (f y) / edist x y ^ (r : ℝ) := by
  refine le_antisymm (eHolderNorm_le_iff.2 fun x y => ?_)
    (iSup_le fun x => iSup_le fun y => iSup_le fun hxy => ?_)
  · rcases eq_or_ne x y with rfl | hxy
    · simp
    rw [le_mul_edist_rpow_iff hxy]
    exact le_iSup₂_of_le x y (le_iSup_of_le hxy le_rfl)
  · exact (le_mul_edist_rpow_iff hxy).1 (edist_le_eHolderNorm_mul r f x y)

/-- The Hölder seminorm is the supremum of the real difference quotients
`dist (f x) (f y) / dist x y ^ r` over pairs of distinct points. -/
theorem eHolderNorm_eq_iSup_dist {X Y : Type*} [MetricSpace X] [PseudoMetricSpace Y] {r : ℝ≥0}
    {f : X → Y} :
    eHolderNorm r f =
      ⨆ (x) (y) (_ : x ≠ y), ENNReal.ofReal (dist (f x) (f y) / dist x y ^ (r : ℝ)) := by
  rw [eHolderNorm_eq_iSup]
  refine iSup_congr fun x => iSup_congr fun y => iSup_congr fun hxy => ?_
  rw [ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos (dist_pos.2 hxy) _), edist_dist,
    edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg r.coe_nonneg]

/-- Scalar homogeneity of the Hölder seminorm, for every map, whether or not it is `r`-Hölder.
Mathlib's `MemHolder.nnHolderNorm_smul` assumes `MemHolder`; without it, both sides take the junk
value `0` when `c ≠ 0`. -/
theorem nnHolderNorm_smul {X Y 𝕜 : Type*} [MetricSpace X] [NormedAddCommGroup Y] [NormedRing 𝕜]
    [Module 𝕜 Y] [NormSMulClass 𝕜 Y] {r : ℝ≥0} (c : 𝕜) (f : X → Y) :
    nnHolderNorm r (c • f) = ‖c‖₊ * nnHolderNorm r f := by
  -- `nnHolderNorm` is the truncation of `eHolderNorm`, which is unconditionally homogeneous.
  rw [nnHolderNorm, nnHolderNorm, eHolderNorm_smul, ENNReal.toNNReal_mul, ENNReal.toNNReal_coe]

/-- Postcomposition with an isometry does not change the Hölder seminorm. -/
theorem Isometry.eHolderNorm_comp {X Y Z : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    [PseudoEMetricSpace Z] {g : Y → Z} (hg : Isometry g) (r : ℝ≥0) (f : X → Y) :
    eHolderNorm r (g ∘ f) = eHolderNorm r f := by
  simp only [eHolderNorm, hg.holderWith_comp_iff]

namespace TauCeti

/-- On a metric space, `eHolderNorm 1 f` is the Lipschitz seminorm: it is at most `K` exactly
when `f` is `K`-Lipschitz, so it is the least Lipschitz constant of `f`. -/
theorem eHolderNorm_one_le_coe_iff {X Y : Type*} [MetricSpace X] [PseudoEMetricSpace Y]
    {f : X → Y} {K : ℝ≥0} : eHolderNorm 1 f ≤ K ↔ LipschitzWith K f := by
  simp [eHolderNorm_le_iff, LipschitzWith]

/-- On a subsingleton space every pair of points is equal, so every map is Hölder with constant `0`
and its Hölder seminorm is `0`. This extends Mathlib's `eHolderNorm_of_isEmpty` to singletons. -/
@[simp]
theorem eHolderNorm_of_subsingleton {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    [Subsingleton X] (r : ℝ≥0) (f : X → Y) : eHolderNorm r f = 0 :=
  nonpos_iff_eq_zero.1 <|
    (show HolderWith 0 r f from fun x y ↦ by simp [Subsingleton.elim x y]).eHolderNorm_le

/-- On a metric space with at most the two points `x` and `y`, the Hölder seminorm of `f` is the
single difference quotient `edist (f x) (f y) / edist x y ^ r`; for `x = y` both sides are `0`.
For `r = 1` and `X = {0, 1}` this is the Lipschitz seminorm `edist (f 0) (f 1) / edist 0 1`. -/
theorem eHolderNorm_eq_edist_div_of_forall_eq_or_eq {X Y : Type*} [MetricSpace X]
    [PseudoEMetricSpace Y] {r : ℝ≥0} {x y : X} (h : ∀ z, z = x ∨ z = y) (f : X → Y) :
    eHolderNorm r f = edist (f x) (f y) / edist x y ^ (r : ℝ) := by
  rcases eq_or_ne x y with rfl | hxy
  · have : Subsingleton X := ⟨fun a b ↦ ((h a).elim id id).trans ((h b).elim id id).symm⟩
    simp
  refine le_antisymm (eHolderNorm_le_iff.2 fun a b ↦ ?_) ?_
  · have hle : edist (f x) (f y) ≤ edist (f x) (f y) / edist x y ^ (r : ℝ) * edist x y ^ (r : ℝ) :=
      (le_mul_edist_rpow_iff hxy).2 le_rfl
    rcases h a with rfl | rfl <;> rcases h b with rfl | rfl
    · simp
    · exact hle
    · rwa [edist_comm (f a), edist_comm a b]
    · simp
  · rw [eHolderNorm_eq_iSup]
    exact le_iSup₂_of_le x y (le_iSup_of_le hxy le_rfl)

/-- The Hölder seminorm is lower semicontinuous for the topology of pointwise convergence: its
sublevel sets are closed. Composing with the continuous coercion, it is also lower semicontinuous
on spaces of continuous or bounded continuous maps. -/
theorem lowerSemicontinuous_eHolderNorm {X Y : Type*} [MetricSpace X] [PseudoEMetricSpace Y]
    (r : ℝ≥0) : LowerSemicontinuous (eHolderNorm r : (X → Y) → ℝ≥0∞) := by
  refine lowerSemicontinuous_iff_isClosed_preimage.2 fun C ↦ ?_
  simp only [preimage, mem_Iic, eHolderNorm_le_iff, ofPred_forall]
  exact isClosed_iInter fun x ↦ isClosed_iInter fun y ↦
    isClosed_le ((continuous_apply x).edist (continuous_apply y)) continuous_const

/-- The Hölder seminorm is invariant under an isometric star operation, such as complex
conjugation of scalar functions. -/
@[simp]
theorem eHolderNorm_star {X E : Type*} [PseudoEMetricSpace X] [SeminormedAddCommGroup E]
    [StarAddMonoid E] [NormedStarGroup E] (r : ℝ≥0) (f : X → E) :
    eHolderNorm r (star f) = eHolderNorm r f := by
  simpa only [Function.comp_def, Pi.star_def] using star_isometry.eHolderNorm_comp r f

/-- **The Leibniz estimate.** For maps `f` and `g` into a seminormed ring with `‖f‖ ≤ A` and
`‖g‖ ≤ B` pointwise, the Hölder seminorm of the product satisfies
`eHolderNorm r (f * g) ≤ A * eHolderNorm r g + B * eHolderNorm r f`. -/
theorem eHolderNorm_mul_le {X R : Type*} [MetricSpace X] [NonUnitalSeminormedRing R]
    {r A B : ℝ≥0} {f g : X → R} (hf : ∀ x, ‖f x‖₊ ≤ A) (hg : ∀ x, ‖g x‖₊ ≤ B) :
    eHolderNorm r (f * g) ≤ A * eHolderNorm r g + B * eHolderNorm r f := by
  refine eHolderNorm_le_iff.2 fun x y ↦ ?_
  calc edist ((f * g) x) ((f * g) y) ≤ A * edist (g x) (g y) + B * edist (f x) (f y) := by
        simp only [Pi.mul_apply, edist_nndist, nnDist_eq_nnNorm]
        norm_cast
        calc ‖f x * g x - f y * g y‖₊ = ‖f x * (g x - g y) + (f x - f y) * g y‖₊ := by
              congr 1
              noncomm_ring
          _ ≤ ‖f x‖₊ * ‖g x - g y‖₊ + ‖f x - f y‖₊ * ‖g y‖₊ :=
              (nnNorm_add_le _ _).trans (add_le_add (nnNorm_mul_le _ _) (nnNorm_mul_le _ _))
          _ ≤ A * ‖g x - g y‖₊ + B * ‖f x - f y‖₊ := by
              rw [mul_comm _ ‖g y‖₊]
              gcongr
              exacts [hf x, hg y]
    _ ≤ A * (eHolderNorm r g * edist x y ^ (r : ℝ)) +
          B * (eHolderNorm r f * edist x y ^ (r : ℝ)) := by
        gcongr <;> exact edist_le_eHolderNorm_mul r _ x y
    _ = (A * eHolderNorm r g + B * eHolderNorm r f) * edist x y ^ (r : ℝ) := by ring

end TauCeti

/-- A curve on a set `S` of times with `d(u s, u t)² ≤ c |s - t|` is `1/2`-Hölder continuous on `S`
with constant `c ^ (1 / 2)`. -/
theorem HolderOnWith.of_edist_sq_le {X : Type*} [PseudoEMetricSpace X] {u : ℝ → X} {S : Set ℝ}
    {c : ℝ} (hc0 : 0 ≤ c)
    (hsq : ∀ s ∈ S, ∀ t ∈ S, s ≤ t → edist (u s) (u t) ^ 2 ≤ ENNReal.ofReal (c * |s - t|)) :
    HolderOnWith (c.toNNReal ^ (2⁻¹ : ℝ)) (1 / 2) u S := by
  refine fun s hs t ht ↦
    ((ENNReal.le_rpow_inv_iff (y := ENNReal.ofReal (c * |s - t|)) two_pos).2 ?_).trans_eq ?_
  · rw [ENNReal.rpow_two]
    rcases le_total s t with hst | hst
    · exact hsq s hs t ht hst
    · rw [edist_comm, abs_sub_comm]
      exact hsq t ht s hs hst
  · -- the exponent `1 / 2 : ℝ≥0` is coerced to `ℝ` here and must become `2⁻¹`
    have hhalf : ((1 / 2 : ℝ≥0) : ℝ) = 2⁻¹ := by norm_num
    rw [ENNReal.coe_rpow_of_nonneg _ (by norm_num), ENNReal.ofNNReal_toNNReal, edist_dist,
      Real.dist_eq, hhalf, ENNReal.ofReal_mul hc0,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]

namespace TauCeti

/-- For `α ≤ 1`, the cusp `x ↦ ‖x‖ ^ α` is `α`-Hölder with constant `1`. -/
theorem holderWith_norm_rpow {E : Type*} [SeminormedAddCommGroup E] {α : ℝ≥0} (hα : α ≤ 1) :
    HolderWith 1 α (fun x : E ↦ ‖x‖ ^ (α : ℝ)) := by
  have hα' : (α : ℝ) ≤ 1 := hα
  -- Subadditivity of `t ↦ t ^ α` gives `b ^ α - a ^ α ≤ (b - a) ^ α` for `0 ≤ a ≤ b`.
  have key : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ^ (α : ℝ) - a ^ (α : ℝ) ≤ (b - a) ^ (α : ℝ) := by
    intro a b ha hab
    have h := Real.rpow_add_le_add_rpow ha (sub_nonneg.2 hab) α.coe_nonneg hα'
    rw [add_sub_cancel] at h
    linarith
  rw [← holderOnWith_univ]
  refine HolderOnWith.of_dist_le fun x _ y _ ↦ ?_
  rw [Real.dist_eq, NNReal.coe_one, one_mul]
  have hxy : |‖x‖ - ‖y‖| ≤ dist x y := by
    rw [dist_eq_norm]; exact abs_norm_sub_norm_le x y
  rcases le_total ‖y‖ ‖x‖ with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 (Real.rpow_le_rpow (norm_nonneg y) h α.coe_nonneg))]
    refine (key _ _ (norm_nonneg y) h).trans (Real.rpow_le_rpow (sub_nonneg.2 h) ?_ α.coe_nonneg)
    exact (le_abs_self _).trans hxy
  · rw [abs_of_nonpos (sub_nonpos.2 (Real.rpow_le_rpow (norm_nonneg x) h α.coe_nonneg)), neg_sub]
    refine (key _ _ (norm_nonneg x) h).trans (Real.rpow_le_rpow (sub_nonneg.2 h) ?_ α.coe_nonneg)
    rw [abs_sub_comm] at hxy
    exact (le_abs_self _).trans hxy

/-- **Common local Hölder bounds give equicontinuity.** If each point `x ∈ s` has a neighbourhood
on which all the maps `f i` are `r`-Hölder with one constant, for a fixed exponent `r > 0`, then the
family `f` is equicontinuous on `s`. -/
theorem equicontinuousOn_of_forall_holderOnWith {ι X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] {f : ι → X → Y} {s : Set X} {r : ℝ≥0} (hr : 0 < r)
    (h : ∀ x ∈ s, ∃ C : ℝ≥0, ∃ t ∈ 𝓝 x, ∀ i, HolderOnWith C r (f i) t) :
    EquicontinuousOn f s := by
  intro x hx
  obtain ⟨C, t, ht, hC⟩ := h x hx
  refine (Metric.equicontinuousAt_of_continuity_modulus (fun y ↦ C * dist x y ^ (r : ℝ)) ?_ f ?_
    ).equicontinuousWithinAt s
  · have hcont : Continuous fun y ↦ (C : ℝ) * dist x y ^ (r : ℝ) :=
      continuous_const.mul ((continuous_const.dist continuous_id).rpow_const
        fun _ ↦ Or.inr r.coe_nonneg)
    simpa [Real.zero_rpow (NNReal.coe_pos.2 hr).ne'] using hcont.tendsto x
  · filter_upwards [ht] with y hy i
    exact (hC i).dist_le (mem_of_mem_nhds ht) hy

end TauCeti
