/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.HolderNorm
public import Mathlib.Topology.MetricSpace.Thickening

import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Hölder functions: a `dist` criterion, extension from a dense set, sums, and the seminorm

A Hölder bound stated with `dist` is equivalent to `HolderOnWith`, which Mathlib phrases with
`edist`. A function with bounded oscillation which satisfies a Hölder bound between nearby points
is Hölder, which turns Hölder bounds on the pieces of a cover into one on the whole set, and is
Hölder with every smaller exponent, with a constant depending on the scale; in particular, so is a
function which is Lipschitz between nearby points. Local Hölder bounds around the points of a
compact set are uniform on a thickening of the set.

A function which is Hölder continuous, with positive exponent, on a dense subset `s` of a
pseudo-emetric space and takes values in a complete emetric space extends to a function which is
Hölder continuous on the whole space, with the same constant and exponent.

The extension is the uniformly continuous extension along the dense inclusion `s → X`, and the
Hölder inequality passes from `s × s` to its closure because both of its sides are continuous.

This is how an almost-everywhere Hölder estimate becomes a Hölder continuous representative: a set
of full measure for a measure that is positive on open sets is dense.

Sums, differences and finite sums of Hölder functions are Hölder, with the sum of the constants.

Finally, on a metric space the infimum defining Mathlib's extended Hölder seminorm `eHolderNorm r f`
is attained, so the seminorm is the best constant in the Hölder inequality. Equivalently, it is the
supremum of the difference quotients `edist (f x) (f y) / edist x y ^ r` over pairs of distinct
points, the form in which Hölder seminorms are written in analysis texts.

## Main declarations

* `HolderOnWith.of_dist_le`: a Hölder bound stated with `dist` gives `HolderOnWith`; the converse
  is Mathlib's `HolderOnWith.dist_le`.
* `HolderOnWith.sub`: differences preserve the exponent and add the Hölder constants.
* `holderOnWith_iff_dist_le`: `HolderOnWith` is equivalent to the Hölder bound stated with `dist`.
* `HolderOnWith.of_le_of_dist_le`: a function satisfying a `β`-Hölder bound between points at
  distance less than `δ > 0`, with values within distance `D` of each other, is `γ`-Hölder for
  `γ ≤ β`, with constant `K δ^(β - γ) + D δ^(-γ)`.
* `LipschitzOnWith.holderOnWith_of_norm_le`: a bounded `L`-Lipschitz function with norm bound
  `M` is Hölder of any exponent at most one with constant `L + 2 M`.
* `HolderOnWith.of_dist_lt_of_dist_le`: a function satisfying a Hölder bound with constant `K`
  between points at distance less than `δ`, with values within distance `D` of each other, is
  Hölder with constant `K + D δ^(-r)`.
* `HolderOnWith.dist_le_mul_rpow_of_mem_ball`: on a ball of radius `ρ`, a Hölder function with
  constant `C` and exponent `r` stays within `C ρ^r` of its value at the centre.
* `HolderOnWith.extend_of_dense`: a Hölder function on a dense set extends to a Hölder
  function on the whole space.
* `HolderWith.sum`: a finite sum of Hölder functions is Hölder.
* `HolderOnWith.add`: sums of Hölder functions on a set.
* `IsCompact.exists_holderOnWith_thickening_and_norm_le`: a function which is Hölder on a ball
  around each point of a compact set `K` is Hölder with one constant, and bounded, on a thickening
  of `K`.
* `le_mul_edist_rpow_iff`: between distinct points, a bound by a multiple of `edist x y ^ r` is a
  bound on the difference quotient.
* `eHolderNorm_le_iff`: `eHolderNorm r f ≤ C` if and only if the Hölder inequality holds with the
  extended constant `C`.
* `eHolderNorm_eq_iSup`, `eHolderNorm_eq_iSup_dist`: the Hölder seminorm is the supremum of the
  difference quotients.
-/

public section

open Set Filter Topology
open scoped NNReal ENNReal

variable {X Y : Type*} [PseudoEMetricSpace X] [EMetricSpace Y] [CompleteSpace Y]
  {C r : ℝ≥0} {f : X → Y} {s : Set X}

/-- **Hölder functions extend from dense sets.** If `f` is Hölder continuous with constant `C` and
positive exponent `r` on a dense set `s`, and the target is complete, then some function which is
Hölder continuous with constant `C` and exponent `r` on the whole space agrees with `f` on `s`.
Compare `LipschitzOnWith.extend_real`, which needs no density but only applies to real values. -/
theorem HolderOnWith.extend_of_dense (hf : HolderOnWith C r f s) (hr : 0 < r)
    (hs : Dense s) : ∃ g : X → Y, HolderWith C r g ∧ EqOn f g s := by
  have hu : UniformContinuous (s.domRestrict f) := hf.holderWith.uniformContinuous hr
  have hi := isUniformInducing_val s
  have hd : DenseRange ((↑) : s → X) := hs.denseRange_val
  set g := (hi.isDenseInducing hd).extend (s.domRestrict f)
  have hg : Continuous g := (uniformContinuous_uniformly_extend hi hd hu).continuous
  have heq : EqOn f g s := fun x hx => (uniformly_extend_of_ind hi hd hu ⟨x, hx⟩).symm
  refine ⟨g, fun x y => ?_, heq⟩
  -- The Hölder inequality for `g` holds on the dense set `s × s`, and defines a closed set.
  have hclosed : IsClosed {q : X × X | edist (g q.1) (g q.2) ≤ C * edist q.1 q.2 ^ (r : ℝ)} :=
    isClosed_le (hg.fst'.edist hg.snd')
      ((ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp
        (ENNReal.continuous_rpow_const.comp continuous_edist))
  have hsub : s ×ˢ s ⊆ {q : X × X | edist (g q.1) (g q.2) ≤ C * edist q.1 q.2 ^ (r : ℝ)} :=
    fun q hq => by
      simp only [mem_ofPred_eq, ← heq hq.1, ← heq hq.2]
      exact hf q.1 hq.1 q.2 hq.2
  exact hclosed.closure_subset_iff.2 hsub ((hs.prod hs).closure_eq.symm ▸ mem_univ (x, y))

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

/-- `HolderOnWith` is equivalent to the Hölder bound stated with `dist`. Compare
`lipschitzOnWith_iff_dist_le_mul`. -/
theorem holderOnWith_iff_dist_le {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {C r : ℝ≥0} {f : X → Y} {s : Set X} :
    HolderOnWith C r f s ↔ ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ C * dist x y ^ (r : ℝ) :=
  ⟨fun hf _ hx _ hy => hf.dist_le hx hy, HolderOnWith.of_dist_le⟩

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
    [PseudoMetricSpace X] [NormedAddCommGroup F]
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

/-- The sum of two functions that are Hölder on `s` with a common exponent is Hölder on `s`, with
the sum of the constants. Compare Mathlib's `HolderWith.add`. -/
theorem HolderOnWith.add {X Y : Type*} [PseudoMetricSpace X] [SeminormedAddCommGroup Y]
    {C C' r : ℝ≥0} {f g : X → Y} {s : Set X} (hf : HolderOnWith C r f s)
    (hg : HolderOnWith C' r g s) : HolderOnWith (C + C') r (fun x => f x + g x) s :=
  HolderOnWith.of_dist_le fun x hx y hy => by
    push_cast
    linarith [dist_add_add_le (f x) (g x) (f y) (g y), hf.dist_le hx hy, hg.dist_le hx hy]

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
            Real.coe_toNNReal _ (hr z (htK z hzt)).le, coe_nnnorm]
      _ ≤ M := by
          exact_mod_cast Finset.single_le_sum
            (f := fun z => ‖f z‖₊ + L z * (r z).toNNReal ^ (α : ℝ)) (fun _ _ => zero_le) hzt
  set δ : ℝ≥0 := ⟨δ₀ / 2, by positivity⟩
  have hδ : 0 < δ := by rw [← NNReal.coe_pos]; exact half_pos hδ₀
  refine ⟨δ₀ / 2, half_pos hδ₀, ∑ z ∈ t, L z + 2 * M * δ ^ (-(α : ℝ)), M, ?_, hM⟩
  refine HolderOnWith.of_dist_lt_of_dist_le hδ (fun y hy y' hy' hyy' => ?_) fun y hy y' hy' => ?_
  · obtain ⟨z, hzt, hyz, hy'z⟩ := hball y hy y' hyy'
    refine ((hL z (htK z hzt)).dist_le hyz hy'z).trans ?_
    gcongr
    exact_mod_cast Finset.single_le_sum (fun _ _ => zero_le) hzt
  · push_cast
    linarith [dist_le_norm_add_norm (f y) (f y'), hM y hy, hM y' hy']

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
