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
# Extending a Hölder function from a dense set

A function which is Hölder continuous, with positive exponent, on a dense subset `s` of a
pseudo-emetric space and takes values in a complete emetric space extends to a function which is
Hölder continuous on the whole space, with the same constant and exponent.

The extension is the uniformly continuous extension along the dense inclusion `s → X`, and the
Hölder inequality passes from `s × s` to its closure because both of its sides are continuous.

This is how an almost-everywhere Hölder estimate becomes a Hölder continuous representative: a set
of full measure for a measure that is positive on open sets is dense.

## Main declarations

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
