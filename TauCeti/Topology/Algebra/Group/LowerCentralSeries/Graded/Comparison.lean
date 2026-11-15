/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.Closed

/-!
# Comparing the closed and lower `p`-series graded pieces

The closed lower central series `γ_n(G)` is contained termwise in every lower `p`-series
`λ_n(G)`. These inclusions descend to additive maps

`γ_n(G) / γ_{n+1}(G) → λ_n(G) / λ_{n+1}(G)`.

This file defines the comparison as `TauCeti.lcsToPLowerCentral`. It sends the class of an
element of `γ_n(G)` to the class of the same element in `λ_n(G)`, is natural under continuous
homomorphisms, and respects the graded brackets. Thus it is the degreewise comparison between
the graded Lie rings of the two series.

## Main definitions

* `TauCeti.lcsToPLowerCentral`: the additive comparison map in each degree.

## Main results

* `TauCeti.lcsToPLowerCentral_gradedMk`: the comparison on classes.
* `TauCeti.lcsToPLowerCentral_zero`: comparison with the lower `0`-series is the identity.
* `TauCeti.lcsToPLowerCentral_gradedMap`: naturality under continuous homomorphisms.
* `TauCeti.lcsToPLowerCentral_lcsBracket`: compatibility with the graded brackets.

## References

* M. Lazard, *Sur les groupes nilpotents et les anneaux de Lie*, Ann. Sci. École Norm. Sup. 71
  (1954).
-/

public section

namespace TauCeti

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The comparison from the `n`-th graded piece of the closed lower central series to the
`n`-th graded piece of the lower `p`-series, induced by the termwise inclusions `γ_n(G) ≤ λ_n(G)`.
Its value on classes is `TauCeti.lcsToPLowerCentral_gradedMk`. -/
def lcsToPLowerCentral (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (n : ℕ) : lcsGradedPiece G n →+ gradedPiece p G n :=
  MonoidHom.toAdditive <|
    QuotientGroup.quotientMapSubgroupOfOfLe
      (by
        rw [← closedLowerCentralSeries_def]
        exact closedLowerCentralSeries_le_pLowerCentralSeries (G := G) p (n + 1))
      (by
        rw [← closedLowerCentralSeries_def]
        exact closedLowerCentralSeries_le_pLowerCentralSeries (G := G) p n)

/-- The closed-to-lower-series comparison sends the class of an element of `γ_n(G)`, represented
as an element of the lower `0`-series, to the class of the same element in `λ_n(G)`. -/
@[simp]
theorem lcsToPLowerCentral_gradedMk (p : ℕ) (n : ℕ) (x : pLowerCentralSeries 0 G n) :
    lcsToPLowerCentral p G n (gradedMk 0 G n x) =
      gradedMk p G n
        ⟨x, closedLowerCentralSeries_le_pLowerCentralSeries (G := G) p n (by
          simpa only [closedLowerCentralSeries_def] using x.2)⟩ := by
  rw [lcsToPLowerCentral, gradedMk_def, MonoidHom.toAdditive_apply_apply, toMul_ofMul,
    QuotientGroup.quotientMapSubgroupOfOfLe_mk, gradedMk_def]
  congr 1

/-- Comparing the closed lower central series with the lower `0`-series does not change a graded
class. -/
@[simp]
theorem lcsToPLowerCentral_zero (n : ℕ) :
    lcsToPLowerCentral 0 G n = AddMonoidHom.id (lcsGradedPiece G n) := by
  refine AddMonoidHom.ext fun z => ?_
  obtain ⟨x, rfl⟩ := gradedMk_surjective (p := 0) (G := G) n z
  rw [lcsToPLowerCentral_gradedMk, AddMonoidHom.id_apply]

/-- The closed-to-lower-series comparison is natural under continuous homomorphisms. -/
@[simp]
theorem lcsToPLowerCentral_gradedMap {H : Type v} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (p : ℕ) (f : G →* H) (hf : Continuous f) (n : ℕ)
    (x : lcsGradedPiece G n) :
    lcsToPLowerCentral p H n (gradedMap 0 f hf n x) =
      gradedMap p f hf n (lcsToPLowerCentral p G n x) := by
  obtain ⟨x, rfl⟩ := lcsGradedMk_surjective n x
  simp only [lcsGradedMk, gradedMap_gradedMk, lcsToPLowerCentral_gradedMk]

/-- The closed-to-lower-series comparison respects the graded brackets. -/
@[simp]
theorem lcsToPLowerCentral_lcsBracket (p : ℕ) {j k : ℕ} (x : lcsGradedPiece G j)
    (y : lcsGradedPiece G k) :
    lcsToPLowerCentral p G (j + k + 1) (lcsBracket G j k x y) =
      gradedBracket p G j k (lcsToPLowerCentral p G j x)
        (lcsToPLowerCentral p G k y) := by
  obtain ⟨x, rfl⟩ := lcsGradedMk_surjective j x
  obtain ⟨y, rfl⟩ := lcsGradedMk_surjective k y
  rw [lcsBracket_lcsGradedMk]
  simp only [lcsGradedMk, lcsToPLowerCentral_gradedMk, gradedBracket_gradedMk]

end TauCeti
