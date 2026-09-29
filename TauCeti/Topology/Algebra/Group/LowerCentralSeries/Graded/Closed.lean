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
names; its commutator formula is `lcsBracket_lcsGradedMk`.

For a pro-`p` group, taking a `p`-adic power in either argument of a commutator acts on its class
by the same `p`-adic exponent. Thus the canonical `ℤ_p`-module structures on the graded pieces
make the bracket `ℤ_p`-bilinear. These are the case `q = 0` of the corresponding results for the
lower `q`-series in `TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.PadicModule`.

## Main definitions

* `TauCeti.lcsGradedPiece`: the successive quotient `γ_n(G) / γ_{n+1}(G)`, written additively.
* `TauCeti.lcsGradedMk`: the class of an element of `γ_n(G)`.
* `TauCeti.lcsBracket`: the bracket induced by the group commutator.

## Main results

* `TauCeti.lcsGradedMk_conj`: conjugation is trivial on each graded piece.
* `TauCeti.lcsBracket_lcsGradedMk`: the bracket of two classes is the class of the commutator.
* `TauCeti.gradedMap_lcsBracket`: the bracket is natural in continuous homomorphisms.
* `TauCeti.IsProP.lcsGradedMk_padicPow`: a `p`-adic power becomes scalar multiplication on a
  graded piece.
* `TauCeti.lcsBracket_padicPow_left`, `TauCeti.lcsBracket_padicPow_right`: a `p`-adic power in
  either argument becomes the same power of the bracket class.
* `TauCeti.IsProP.lcsBracket_smul_left`, `TauCeti.IsProP.lcsBracket_smul_right`: the bracket is
  `ℤ_p`-linear in each variable.

## References

* M. Lazard, *Sur les groupes nilpotents et les anneaux de Lie*, Ann. Sci. École Norm. Sup. 71
  (1954).
-/

public section

open Subgroup
open scoped commutatorElement

namespace TauCeti

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The `n`-th graded piece of the closed lower central series, written additively. -/
abbrev lcsGradedPiece (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (n : ℕ) : Type u :=
  gradedPiece 0 G n

/-- The class in `γ_n(G) / γ_{n+1}(G)` of an element of `γ_n(G)`. -/
abbrev lcsGradedMk (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (n : ℕ) (x : closedLowerCentralSeries G n) : lcsGradedPiece G n :=
  gradedMk 0 G n ⟨x, by rw [← closedLowerCentralSeries_def]; exact x.2⟩

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

/-- **Naturality of the closed-series bracket**: the graded maps induced by a continuous
homomorphism commute with the bracket. -/
theorem gradedMap_lcsBracket {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (f : G →* H) (hf : Continuous f) {j k : ℕ} (x : lcsGradedPiece G j)
    (y : lcsGradedPiece G k) :
    gradedMap 0 f hf (j + k + 1) (lcsBracket G j k x y) =
      lcsBracket H j k (gradedMap 0 f hf j x) (gradedMap 0 f hf k y) :=
  gradedMap_gradedBracket f hf x y

section PadicPow

variable {p : ℕ} [Fact p.Prime] [CompactSpace G] [TotallyDisconnectedSpace G]

/-- The canonical `ℤ_p`-module structure on a graded piece of the closed lower central series
of a pro-`p` group. It is the module structure on the abelian pro-`p` quotient
`γ_n(G) / γ_{n+1}(G)`, the case `q = 0` of `TauCeti.IsProP.gradedPieceModule`. -/
@[instance_reducible]
noncomputable def IsProP.lcsGradedPieceModule (hG : IsProP p G) (n : ℕ) :
    Module ℤ_[p] (lcsGradedPiece G n) :=
  hG.gradedPieceModule 0 n

/-- In a pro-`p` group, the class of a `p`-adic power in a closed-series graded piece is the
corresponding `ℤ_p`-scalar multiple. -/
@[simp]
theorem IsProP.lcsGradedMk_padicPow (hG : IsProP p G) {n : ℕ}
    (x : closedLowerCentralSeries G n) (u : ℤ_[p]) :
    letI := hG.lcsGradedPieceModule n
    lcsGradedMk G n
        ⟨hG.padicPow (x : G) u,
          hG.padicPow_mem (isClosed_closedLowerCentralSeries n) x.2 u⟩ =
      u • lcsGradedMk G n x :=
  hG.gradedMk_padicPow ⟨x, closedLowerCentralSeries_def G n ▸ x.2⟩ u

/-- Taking a `p`-adic power in the first argument of the closed-series bracket takes the same
power of the bracket class. This is `ℤ_p`-linearity in the first variable on representatives. -/
theorem lcsBracket_padicPow_left (hG : IsProP p G) {j k : ℕ}
    (x : closedLowerCentralSeries G j) (y : closedLowerCentralSeries G k) (u : ℤ_[p]) :
    ∃ hx : hG.padicPow (x : G) u ∈ closedLowerCentralSeries G j,
    ∃ hxy : hG.padicPow ⁅(x : G), (y : G)⁆ u ∈ closedLowerCentralSeries G (j + k + 1),
      lcsBracket G j k (lcsGradedMk G j ⟨_, hx⟩) (lcsGradedMk G k y) =
        lcsGradedMk G (j + k + 1) ⟨_, hxy⟩ :=
  ⟨hG.padicPow_mem (isClosed_closedLowerCentralSeries j) x.2 u,
    hG.padicPow_mem (isClosed_closedLowerCentralSeries (j + k + 1))
      ((commutator_closedLowerCentralSeries_le j k)
        (Subgroup.commutator_mem_commutator x.2 y.2)) u,
    hG.gradedBracket_padicPow_left ⟨x, closedLowerCentralSeries_def G j ▸ x.2⟩
      ⟨y, closedLowerCentralSeries_def G k ▸ y.2⟩ u⟩

/-- Taking a `p`-adic power in the second argument of the closed-series bracket takes the same
power of the bracket class. This is `ℤ_p`-linearity in the second variable on representatives. -/
theorem lcsBracket_padicPow_right (hG : IsProP p G) {j k : ℕ}
    (x : closedLowerCentralSeries G j) (y : closedLowerCentralSeries G k) (u : ℤ_[p]) :
    ∃ hy : hG.padicPow (y : G) u ∈ closedLowerCentralSeries G k,
    ∃ hxy : hG.padicPow ⁅(x : G), (y : G)⁆ u ∈ closedLowerCentralSeries G (j + k + 1),
      lcsBracket G j k (lcsGradedMk G j x) (lcsGradedMk G k ⟨_, hy⟩) =
        lcsGradedMk G (j + k + 1) ⟨_, hxy⟩ :=
  ⟨hG.padicPow_mem (isClosed_closedLowerCentralSeries k) y.2 u,
    hG.padicPow_mem (isClosed_closedLowerCentralSeries (j + k + 1))
      ((commutator_closedLowerCentralSeries_le j k)
        (Subgroup.commutator_mem_commutator x.2 y.2)) u,
    hG.gradedBracket_padicPow_right ⟨x, closedLowerCentralSeries_def G j ▸ x.2⟩
      ⟨y, closedLowerCentralSeries_def G k ▸ y.2⟩ u⟩

/-- The closed-series bracket of a pro-`p` group is `ℤ_p`-linear in its first argument. -/
theorem IsProP.lcsBracket_smul_left (hG : IsProP p G) {j k : ℕ} (u : ℤ_[p])
    (x : lcsGradedPiece G j) (y : lcsGradedPiece G k) :
    letI := hG.lcsGradedPieceModule j
    letI := hG.lcsGradedPieceModule k
    letI := hG.lcsGradedPieceModule (j + k + 1)
    lcsBracket G j k (u • x) y = u • lcsBracket G j k x y :=
  hG.gradedBracket_smul_left u x y

/-- The closed-series bracket of a pro-`p` group is `ℤ_p`-linear in its second argument. -/
theorem IsProP.lcsBracket_smul_right (hG : IsProP p G) {j k : ℕ} (u : ℤ_[p])
    (x : lcsGradedPiece G j) (y : lcsGradedPiece G k) :
    letI := hG.lcsGradedPieceModule j
    letI := hG.lcsGradedPieceModule k
    letI := hG.lcsGradedPieceModule (j + k + 1)
    lcsBracket G j k x (u • y) = u • lcsBracket G j k x y :=
  hG.gradedBracket_smul_right u x y

end PadicPow

end TauCeti
