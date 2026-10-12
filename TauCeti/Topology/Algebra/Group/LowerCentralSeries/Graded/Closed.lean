/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Closed
public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.PadicModule

/-!
# The graded bracket of the closed lower central series

The successive quotients of the closed lower central series are the case `p = 0` of Tau Ceti's
graded pieces for the lower `p`-series. This file gives that specialization its consumer-facing
names; its commutator formula is `lcsBracket_lcsGradedMk`. The `ℤ_p`-module structure and
bilinearity results for a pro-`p` group are the case `q = 0` of the results in
`TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.PadicModule`.

## Main definitions

* `TauCeti.lcsGradedPiece`: the successive quotient `γ_n(G) / γ_{n+1}(G)`, written additively.
* `TauCeti.lcsGradedMk`: the class of an element of `γ_n(G)`.
* `TauCeti.lcsBracket`: the bracket induced by the group commutator.

## Main results

* `TauCeti.lcsGradedMk_conj`: conjugation is trivial on each graded piece.
* `TauCeti.lcsGradedMk_surjective`: every graded class has a closed-series representative.
* `TauCeti.lcsBracket_lcsGradedMk`: the bracket of two classes is the class of the commutator.

## References

* M. Lazard, *Sur les groupes nilpotents et les anneaux de Lie*, Ann. Sci. École Norm. Sup. 71
  (1954).
-/

public section

open Subgroup
open scoped commutatorElement

namespace TauCeti

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The `n`-th graded piece of the closed lower central series, written additively. -/
abbrev lcsGradedPiece (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (n : ℕ) : Type u :=
  gradedPiece 0 G n

/-- The class in `γ_n(G) / γ_{n+1}(G)` of an element of `γ_n(G)`. -/
abbrev lcsGradedMk (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (n : ℕ) (x : closedLowerCentralSeries G n) : lcsGradedPiece G n :=
  gradedMk 0 G n ⟨x, by rw [← closedLowerCentralSeries_def]; exact x.2⟩

/-- Every class in a closed lower-central-series graded piece has a representative in that
term of the closed lower central series. -/
theorem lcsGradedMk_surjective (n : ℕ) : Function.Surjective (lcsGradedMk G n) := fun x ↦ by
  obtain ⟨y, rfl⟩ := gradedMk_surjective n x
  have hy : (y : G) ∈ closedLowerCentralSeries G n := by
    rw [closedLowerCentralSeries_def]
    exact y.2
  exact ⟨⟨y, hy⟩, rfl⟩

/-- Conjugation acts trivially on every graded piece of the closed lower central series. -/
@[simp]
theorem lcsGradedMk_conj (n : ℕ) (g : G) (x : closedLowerCentralSeries G n) :
    lcsGradedMk G n
        ⟨g * x * g⁻¹, (closedLowerCentralSeries_normal (G := G) n).conj_mem x x.2 g⟩ =
      lcsGradedMk G n x := by
  rw [gradedMk_eq_gradedMk_iff]
  exact mk_conj_of_mem_pLowerCentralSeries
    (closedLowerCentralSeries_def G n ▸ x.2) g

/-- The bracket on the graded pieces of the closed lower central series. Its degree is
`j + k + 1` because the series is indexed from zero. -/
abbrev lcsBracket (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (j k : ℕ) :
    lcsGradedPiece G j →+ lcsGradedPiece G k →+ lcsGradedPiece G (j + k + 1) :=
  gradedBracket 0 G j k

/-- The closed-series bracket on classes is represented by the group commutator. -/
theorem lcsBracket_lcsGradedMk {j k : ℕ} (x : closedLowerCentralSeries G j)
    (y : closedLowerCentralSeries G k) :
    lcsBracket G j k (lcsGradedMk G j x) (lcsGradedMk G k y) =
      lcsGradedMk G (j + k + 1)
        ⟨⁅(x : G), (y : G)⁆,
          (commutator_closedLowerCentralSeries_le j k)
            (Subgroup.commutator_mem_commutator x.2 y.2)⟩ := by
  rw [lcsBracket, lcsGradedMk, lcsGradedMk, gradedBracket_gradedMk]

end TauCeti
