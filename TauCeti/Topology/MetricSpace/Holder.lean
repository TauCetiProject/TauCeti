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
# Hölder functions: a `dist` criterion, dense extension, finite sums, and the Hölder seminorm

A Hölder bound stated with `dist` is equivalent to `HolderOnWith`, which Mathlib phrases with
`edist`.

A function which is Hölder continuous, with positive exponent, on a dense subset `s` of a
pseudo-emetric space and takes values in a complete emetric space extends to a function which is
Hölder continuous on the whole space, with the same constant and exponent.

The extension is the uniformly continuous extension along the dense inclusion `s → X`, and the
Hölder inequality passes from `s × s` to its closure because both of its sides are continuous.

This is how an almost-everywhere Hölder estimate becomes a Hölder continuous representative: a set
of full measure for a measure that is positive on open sets is dense.

Finite sums of Hölder functions are Hölder, with the sum of the constants.

Mathlib defines the Hölder seminorm `eHolderNorm r f` as the infimum of the admissible Hölder
constants. On an emetric space it is also the supremum of the difference quotients
`edist (f x) (f y) / edist x y ^ r` over distinct points, and on a metric space it bounds every
increment of `f`. These are the forms in which Hölder seminorms are estimated by hand, for instance
when a seminorm on a product is compared with seminorms of the slices.

## Main declarations

* `HolderOnWith.of_dist_le`: a Hölder bound stated with `dist` gives `HolderOnWith`; the converse
  is Mathlib's `HolderOnWith.dist_le`.
* `holderOnWith_iff_dist_le`: `HolderOnWith` is equivalent to the Hölder bound stated with `dist`.
* `HolderOnWith.dist_le_mul_rpow_of_mem_ball`: on a ball of radius `ρ`, a Hölder function with
  constant `C` and exponent `r` stays within `C ρ^r` of its value at the centre.
* `HolderOnWith.extend_of_dense`: a Hölder function on a dense set extends to a Hölder
  function on the whole space.
* `HolderWith.sum`: a finite sum of Hölder functions is Hölder.
* `eHolderNorm_eq_iSup_edist_div` and `MemHolder.coe_nnHolderNorm_eq_iSup_dist_div`: the Hölder
  seminorm is the supremum of the difference quotients over distinct points.
* `edist_le_eHolderNorm_mul_rpow`: the Hölder seminorm bounds every increment.
* `HolderWith.eHolderNorm_comp_le`: precomposition with a Hölder map of constant `C ≠ 0` scales
  the Hölder seminorm by at most `C ^ r`.
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

section HolderNorm

variable {X Y Z : Type*}

/-- Every difference quotient `edist (f x) (f y) / edist x y ^ r` is bounded by the Hölder
seminorm. -/
theorem edist_div_rpow_le_eHolderNorm [PseudoEMetricSpace X] [PseudoEMetricSpace Y] (r : ℝ≥0)
    (f : X → Y) (x y : X) :
    edist (f x) (f y) / edist x y ^ (r : ℝ) ≤ eHolderNorm r f :=
  le_iInf₂ fun _ hfC => ENNReal.div_le_of_le_mul (hfC x y)

/-- The Hölder seminorm is the supremum of the difference quotients
`edist (f x) (f y) / edist x y ^ r` over distinct points `x ≠ y`. -/
theorem eHolderNorm_eq_iSup_edist_div [PseudoEMetricSpace X] [PseudoEMetricSpace Y] (r : ℝ≥0)
    (f : X → Y) :
    eHolderNorm r f = ⨆ (x) (y) (_ : x ≠ y), edist (f x) (f y) / edist x y ^ (r : ℝ) := by
  refine le_antisymm (le_of_forall_gt_imp_ge_of_dense fun C hC => ?_)
    (iSup₂_le fun x y => iSup_le fun _ => edist_div_rpow_le_eHolderNorm r f x y)
  -- Every finite constant `C` above the supremum is an admissible Hölder constant.
  have hC0 : C ≠ 0 := (pos_of_gt hC).ne'
  rcases eq_or_ne C ∞ with rfl | hCtop
  · exact le_top
  lift C to ℝ≥0 using hCtop
  refine HolderWith.eHolderNorm_le fun x y => ?_
  rcases eq_or_ne x y with rfl | hxy
  · simp
  have hq : edist (f x) (f y) / edist x y ^ (r : ℝ) < C :=
    lt_of_le_of_lt (le_iSup_of_le x <| le_iSup_of_le y <|
      le_iSup (fun _ : x ≠ y => edist (f x) (f y) / edist x y ^ (r : ℝ)) hxy) hC
  by_cases hd0 : edist x y ^ (r : ℝ) = 0
  · -- At zero distance, a finite quotient forces a zero increment.
    have hfxy : edist (f x) (f y) = 0 := by
      by_contra h
      rw [hd0, ENNReal.div_zero h] at hq
      exact not_top_lt hq
    simp [hfxy]
  by_cases hdtop : edist x y ^ (r : ℝ) = ∞
  · rw [hdtop, ENNReal.mul_top hC0]
    exact le_top
  · rw [← ENNReal.div_le_iff hd0 hdtop]
    exact hq.le

/-- On a metric space, the Hölder seminorm bounds every increment:
`edist (f x) (f y) ≤ eHolderNorm r f * edist x y ^ r`. -/
theorem edist_le_eHolderNorm_mul_rpow [MetricSpace X] [PseudoEMetricSpace Y] (r : ℝ≥0)
    (f : X → Y) (x y : X) :
    edist (f x) (f y) ≤ eHolderNorm r f * edist x y ^ (r : ℝ) := by
  rcases eq_or_ne x y with rfl | hxy
  · simp
  have hd0 : edist x y ^ (r : ℝ) ≠ 0 := by
    simp [ENNReal.rpow_eq_zero_iff, (edist_pos.2 hxy).ne']
  have hdtop : edist x y ^ (r : ℝ) ≠ ∞ := by
    simp [edist_ne_top]
  rw [← ENNReal.div_le_iff hd0 hdtop]
  exact edist_div_rpow_le_eHolderNorm r f x y

/-- The Hölder seminorm of a Hölder function is the supremum of the difference quotients
`dist (f x) (f y) / dist x y ^ r` over distinct points `x ≠ y`. -/
theorem MemHolder.coe_nnHolderNorm_eq_iSup_dist_div [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {r : ℝ≥0} {f : X → Y} (hf : MemHolder r f) :
    (nnHolderNorm r f : ℝ) =
      ⨆ (x) (y) (_ : x ≠ y), dist (f x) (f y) / dist x y ^ (r : ℝ) := by
  -- Every difference quotient is finite, so `toReal` commutes with each partial supremum.
  have hq (x y : X) : edist (f x) (f y) / edist x y ^ (r : ℝ) ≠ ∞ :=
    ne_top_of_le_ne_top hf.eHolderNorm_lt_top.ne (edist_div_rpow_le_eHolderNorm r f x y)
  rw [nnHolderNorm, ENNReal.coe_toNNReal_eq_toReal, eHolderNorm_eq_iSup_edist_div,
    ENNReal.toReal_iSup fun x => ne_top_of_le_ne_top hf.eHolderNorm_lt_top.ne
      (iSup₂_le fun y _ => edist_div_rpow_le_eHolderNorm r f x y)]
  refine iSup_congr fun x => ?_
  rw [ENNReal.toReal_iSup fun y => ne_top_of_le_ne_top (hq x y) (iSup_le fun _ => le_rfl)]
  refine iSup_congr fun y => ?_
  rw [ENNReal.toReal_iSup fun _ => hq x y]
  refine iSup_congr fun _ => ?_
  rw [ENNReal.toReal_div, ← ENNReal.toReal_rpow, edist_dist, edist_dist,
    ENNReal.toReal_ofReal dist_nonneg, ENNReal.toReal_ofReal dist_nonneg]

/-- Precomposition with a map that is Hölder continuous with constant `C ≠ 0` and exponent `s`
turns an `r`-Hölder function into an `r * s`-Hölder function, scaling the seminorm by at most
`C ^ r`. For instance, restriction to a subspace (`C = 1`, `s = 1`) does not increase the Hölder
seminorm. The hypothesis `C ≠ 0` cannot be dropped on pseudometric spaces: the identity of a
two-point space at distance zero is `0`-Hölder, while a function separating the two points has
infinite seminorm. -/
theorem HolderWith.eHolderNorm_comp_le [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    [PseudoEMetricSpace Z] {C s : ℝ≥0} {g : X → Y} (hg : HolderWith C s g) (hC : C ≠ 0)
    (r : ℝ≥0) (f : Y → Z) :
    eHolderNorm (r * s) (f ∘ g) ≤ eHolderNorm r f * (C : ℝ≥0∞) ^ (r : ℝ) := by
  have h0 : (C : ℝ≥0∞) ^ (r : ℝ) ≠ 0 := by simp [hC]
  have htop : (C : ℝ≥0∞) ^ (r : ℝ) ≠ ∞ := by simp
  rw [eHolderNorm.eq_1 r f, ENNReal.iInf_mul_of_ne h0 htop]
  refine le_iInf fun C' => ?_
  rw [ENNReal.iInf_mul_of_ne h0 htop]
  exact le_iInf fun hfC => by
    simpa [ENNReal.coe_rpow_of_ne_zero hC] using (hfC.comp hg).eHolderNorm_le

end HolderNorm
