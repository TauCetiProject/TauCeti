/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Second-countability of the one-point compactification

For a weakly locally compact, second-countable `R₁` space `X`, the Alexandroff one-point
compactification `OnePoint X` is second-countable: the images of a countable topological basis of
`X` together with the complements of the closures of a compact exhaustion
`CompactExhaustion.choice X` form a countable basis of `OnePoint X` at both finite points and `∞`.

## Main results

* `OnePoint.instSecondCountableTopology`: `SecondCountableTopology (OnePoint X)` for a weakly
  locally compact, second-countable `R₁` space `X`.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156, Springer,
  1995, Theorem 5.3.
-/

public section

open Set TopologicalSpace
open scoped OnePoint

namespace OnePoint

/-- The one-point compactification of a weakly locally compact, second-countable `R₁` space is
second-countable. -/
instance instSecondCountableTopology {X : Type*} [TopologicalSpace X] [WeaklyLocallyCompactSpace X]
    [SecondCountableTopology X] [R1Space X] : SecondCountableTopology (OnePoint X) := by
  obtain ⟨B, hBc, -, hB⟩ := exists_countable_basis X
  let K : CompactExhaustion X := CompactExhaustion.choice X
  let B' : Set (Set (OnePoint X)) :=
    ((fun U : Set X => ((↑) '' U : Set (OnePoint X))) '' B) ∪
      range fun n : ℕ => (((↑) '' closure (K n) : Set (OnePoint X))ᶜ)
  have hB'c : B'.Countable := (hBc.image _).union (countable_range _)
  have hB' : IsTopologicalBasis B' := by
    refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro s (⟨U, hU, rfl⟩ | ⟨n, rfl⟩)
      · exact isOpen_image_coe.2 (hB.isOpen hU)
      · exact isOpen_compl_image_coe.2 ⟨isClosed_closure, (K.isCompact n).closure⟩
    · intro z s hzs hs
      induction z using OnePoint.rec with
      | infty =>
        obtain ⟨_, hKcomp⟩ := (isOpen_iff_of_mem hzs).1 hs
        obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact hKcomp
        refine ⟨(((↑) '' closure (K n) : Set (OnePoint X))ᶜ), Or.inr ⟨n, rfl⟩,
          mem_compl infty_notMem_image_coe, ?_⟩
        intro w hw
        induction w using OnePoint.rec with
        | infty => exact hzs
        | coe x =>
          by_contra hx
          exact hw ⟨x, subset_closure (hn hx), rfl⟩
      | coe x =>
        obtain ⟨U, hUB, hxU, hUs⟩ := hB.exists_subset_of_mem_open hzs (isOpen_def.1 hs).2
        exact ⟨(↑) '' U, Or.inl ⟨U, hUB, rfl⟩, ⟨x, hxU, rfl⟩, image_subset_iff.2 hUs⟩
  exact ⟨⟨B', hB'c, hB'.eq_generateFrom⟩⟩

end OnePoint
