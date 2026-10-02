/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Holder

import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Hölder functions: a `dist` criterion and extension from a dense set

A Hölder bound stated with `dist` is equivalent to `HolderOnWith`, which Mathlib phrases with
`edist`.

A function which is Hölder continuous, with positive exponent, on a dense subset `s` of a
pseudo-emetric space and takes values in a complete emetric space extends to a function which is
Hölder continuous on the whole space, with the same constant and exponent.

The extension is the uniformly continuous extension along the dense inclusion `s → X`, and the
Hölder inequality passes from `s × s` to its closure because both of its sides are continuous.

This is how an almost-everywhere Hölder estimate becomes a Hölder continuous representative: a set
of full measure for a measure that is positive on open sets is dense.

## Main declarations

* `HolderOnWith.of_dist_le`: a Hölder bound stated with `dist` gives `HolderOnWith`; the converse
  is Mathlib's `HolderOnWith.dist_le`.
* `holderOnWith_iff_dist_le`: `HolderOnWith` is equivalent to the Hölder bound stated with `dist`.
* `HolderOnWith.extend_of_dense`: a Hölder function on a dense set extends to a Hölder
  function on the whole space.
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
