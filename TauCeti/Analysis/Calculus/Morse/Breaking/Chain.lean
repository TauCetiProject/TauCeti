/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.CompactSublevel

/-!
# Finite chains of broken Morse trajectories

If the closure of the stable set of `q` meets the stable set of a different nondegenerate
critical point `x`, forward endpoint convergence and Morse--Smale transversality produce a finite
chain of nonconstant negative-gradient trajectories from `x` to `q`. Each component strictly
decreases the Morse index, so the number of components is at most `morseIndex f x - morseIndex f q`.

The chain is represented by a list of critical points, with an actual connecting orbit between
each consecutive pair. Its tail length counts the components. The endpoint convergence assumption
is discharged for globally Morse functions with compact sublevels. These results identify finite
broken chains forced by stable-set closure incidence; they do not assert that an entire sequence
of trajectories converges to the chain.

The bounded chain construction is
`TauCeti.IsNondegenerateCriticalPoint.exists_isChain_of_mem_closure_stableSet_inter_stableSet`.
The compact-sublevel convergence theorem is `TauCeti.exists_stableSet_of_isCompact_sublevel`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Section 3.2 (broken trajectories and compactness).
-/

public section

open Set
open scoped Gradient NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {f : E → ℝ} {K : ℝ≥0} {x q : E}

namespace IsNondegenerateCriticalPoint

/-- For a globally Morse function with compact sublevels, a stable-set closure incidence
produces a finite chain of nonconstant trajectories without an additional convergence hypothesis.
The number of components is bounded by the Morse-index drop. -/
theorem exists_isChain_of_mem_closure_stableSet_inter_stableSet_of_isCompact_sublevel
    (hx : IsNondegenerateCriticalPoint f x) (hfs : ContDiff ℝ 2 f)
    (hf : LipschitzWith K (∇ f)) (hM : HasNondegenerateCriticalPointsOn f univ)
    (hcompact : ∀ c : ℝ, IsCompact {z | f z ≤ c}) (hqx : q ≠ x)
    (hy : (closure (Flow.stableSet (negativeGradientFlow f hf) q) ∩
      Flow.stableSet (negativeGradientFlow f hf) x).Nonempty)
    (htr : ∀ {a b z}, IsNondegenerateCriticalPoint f a →
      IsNondegenerateCriticalPoint f b →
      z ∈ Flow.unstableSet (negativeGradientFlow f hf) a →
      z ∈ Flow.stableSet (negativeGradientFlow f hf) b →
      Submodule.span ℝ (tangentConeAt ℝ
          (Flow.unstableSet (negativeGradientFlow f hf) a) z) ⊔
        Submodule.span ℝ (tangentConeAt ℝ
          (Flow.stableSet (negativeGradientFlow f hf) b) z) = ⊤) :
    ∃ l : List E,
      (x :: l).IsChain (fun a b ↦ a ≠ b ∧
        (Flow.unstableSet (negativeGradientFlow f hf) a ∩
          Flow.stableSet (negativeGradientFlow f hf) b).Nonempty) ∧
      (x :: l).getLast (List.cons_ne_nil _ _) = q ∧
      (∀ a ∈ x :: l, IsNondegenerateCriticalPoint f a) ∧
      l.length + morseIndex f q ≤ morseIndex f x :=
  hx.exists_isChain_of_mem_closure_stableSet_inter_stableSet hfs hf hqx hy
    (fun {_} _ ↦ exists_stableSet_of_isCompact_sublevel hfs hf hM _ (hcompact _)) htr

end IsNondegenerateCriticalPoint

end TauCeti
