/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.HolderNorm

import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Hölder functions: a `dist` criterion, extension from a dense set, finite sums, and the seminorm

A Hölder bound stated with `dist` is equivalent to `HolderOnWith`, which Mathlib phrases with
`edist`. A function with bounded oscillation is Hölder with every smaller exponent, with a
constant depending on a free scale.

A function which is Hölder continuous, with positive exponent, on a dense subset `s` of a
pseudo-emetric space and takes values in a complete emetric space extends to a function which is
Hölder continuous on the whole space, with the same constant and exponent.

The extension is the uniformly continuous extension along the dense inclusion `s → X`, and the
Hölder inequality passes from `s × s` to its closure because both of its sides are continuous.

This is how an almost-everywhere Hölder estimate becomes a Hölder continuous representative: a set
of full measure for a measure that is positive on open sets is dense.

Finite sums of Hölder functions are Hölder, with the sum of the constants.

Finally, on a metric space the infimum defining Mathlib's extended Hölder seminorm `eHolderNorm r f`
is attained, so the seminorm is the best constant in the Hölder inequality. Equivalently, it is the
supremum of the difference quotients `edist (f x) (f y) / edist x y ^ r` over pairs of distinct
points, the form in which Hölder seminorms are written in analysis texts.

## Main declarations

* `HolderOnWith.of_dist_le`: a Hölder bound stated with `dist` gives `HolderOnWith`; the converse
  is Mathlib's `HolderOnWith.dist_le`.
* `holderOnWith_iff_dist_le`: `HolderOnWith` is equivalent to the Hölder bound stated with `dist`.
* `HolderOnWith.of_le_of_dist_le`: a `β`-Hölder function with values within distance `D` of each
  other is `γ`-Hölder for `γ ≤ β`, with constant `K δ^(β - γ) + D δ^(-γ)` for every scale `δ > 0`.
* `HolderOnWith.dist_le_mul_rpow_of_mem_ball`: on a ball of radius `ρ`, a Hölder function with
  constant `C` and exponent `r` stays within `C ρ^r` of its value at the centre.
* `HolderOnWith.extend_of_dense`: a Hölder function on a dense set extends to a Hölder
  function on the whole space.
* `HolderWith.sum`: a finite sum of Hölder functions is Hölder.
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

/-- `HolderOnWith` is equivalent to the Hölder bound stated with `dist`. Compare
`lipschitzOnWith_iff_dist_le_mul`. -/
theorem holderOnWith_iff_dist_le {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {C r : ℝ≥0} {f : X → Y} {s : Set X} :
    HolderOnWith C r f s ↔ ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ C * dist x y ^ (r : ℝ) :=
  ⟨fun hf _ hx _ hy => hf.dist_le hx hy, HolderOnWith.of_dist_le⟩

/-- A function that is `β`-Hölder with constant `K` on `s`, and whose values on `s` lie within
distance `D` of each other, is `γ`-Hölder on `s` for every `γ ≤ β`. For each scale `δ > 0` the
constant is `K δ^(β - γ) + D δ^(-γ)`: the `β`-Hölder bound is used at distances at most `δ` and
the bound `D` at larger distances. A small scale makes the coefficient of `K` small at the price
of a large coefficient of `D`. Compare Mathlib's `HolderOnWith.of_le`, which bounds the domain
instead of the values. -/
theorem HolderOnWith.of_le_of_dist_le {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {K D δ β γ : ℝ≥0} {f : X → Y} {s : Set X} (hf : HolderOnWith K β f s)
    (hD : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ D) (hγβ : γ ≤ β) (hδ : 0 < δ) :
    HolderOnWith (K * δ ^ ((β : ℝ) - γ) + D * δ ^ (-(γ : ℝ))) γ f s := by
  have hγβ' : (γ : ℝ) ≤ β := hγβ
  have hδ' : (0 : ℝ) < δ := hδ
  refine HolderOnWith.of_dist_le fun x hx y hy => ?_
  have hK : 0 ≤ (K : ℝ) * (δ : ℝ) ^ ((β : ℝ) - γ) * dist x y ^ (γ : ℝ) := by positivity
  have hD' : 0 ≤ (D : ℝ) * (δ : ℝ) ^ (-(γ : ℝ)) * dist x y ^ (γ : ℝ) := by positivity
  push_cast
  rcases le_or_gt (dist x y) δ with h | h
  · calc dist (f x) (f y) ≤ K * dist x y ^ (β : ℝ) := hf.dist_le hx hy
      _ = K * dist x y ^ ((β : ℝ) - γ) * dist x y ^ (γ : ℝ) := by
        rw [mul_assoc, ← Real.rpow_add_of_nonneg dist_nonneg (sub_nonneg.2 hγβ') γ.coe_nonneg,
          sub_add_cancel]
      _ ≤ K * (δ : ℝ) ^ ((β : ℝ) - γ) * dist x y ^ (γ : ℝ) := by gcongr
      _ ≤ _ := by rw [add_mul]; exact le_add_of_nonneg_right hD'
  · calc dist (f x) (f y) ≤ D := hD x hx y hy
      _ = D * (δ : ℝ) ^ (-(γ : ℝ)) * (δ : ℝ) ^ (γ : ℝ) := by
        rw [mul_assoc, ← Real.rpow_add hδ', neg_add_cancel, Real.rpow_zero, mul_one]
      _ ≤ D * (δ : ℝ) ^ (-(γ : ℝ)) * dist x y ^ (γ : ℝ) := by gcongr
      _ ≤ _ := by rw [add_mul]; exact le_add_of_nonneg_left hK

/-- A function that is Hölder continuous with constant `C` and exponent `r` on the ball
`ball x₀ ρ` stays within `C ρ^r` of its value at the centre. -/
theorem HolderOnWith.dist_le_mul_rpow_of_mem_ball {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] {C r : ℝ≥0} {f : X → Y} {x₀ x : X} {ρ : ℝ}
    (hf : HolderOnWith C r f (Metric.ball x₀ ρ)) (hx : x ∈ Metric.ball x₀ ρ) :
    dist (f x) (f x₀) ≤ C * ρ ^ (r : ℝ) := by
  have hx' := Metric.mem_ball.1 hx
  calc dist (f x) (f x₀) ≤ C * dist x x₀ ^ (r : ℝ) :=
        hf.dist_le hx (Metric.mem_ball_self (dist_nonneg.trans_lt hx'))
    _ ≤ C * ρ ^ (r : ℝ) := by gcongr

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
