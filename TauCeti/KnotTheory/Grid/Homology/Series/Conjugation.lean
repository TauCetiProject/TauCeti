/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.FullyBlocked.Symmetry
public import TauCeti.KnotTheory.Grid.Homology.Series.FullyBlocked
public import TauCeti.KnotTheory.Grid.Homology.SimplyBlocked.Transpose

/-!
# The conjugation symmetry of simply blocked grid homology

For a knot grid `G`, simply blocked grid homology `G-hat` satisfies the conjugation symmetry

`G-hat_m(G', a) ≅ G-hat_(m - 2a)(G, -a)`,

where `G'` is the diagram obtained from `G` by exchanging its `O`- and `X`-markings. At the level
of `(O-Maslov, Alexander)` Poincaré series over `𝔽₂` this reads
`P(G-hat(G')) = conjugate (P(G-hat(G)))`, for the involution `(m, a) ↦ (m - 2a, -a)` of bidegrees
(`TauCeti.Bigraded.conjugate`); over a field, a finite-dimensional bigraded vector space is
determined up to bigraded isomorphism by its Poincaré series.

The proof follows Ozsváth--Stipsicz--Szabó, Proposition 7.1.1. Exchanging the markings does not
change the fully blocked complex, and moves a grid state of bidegree `(m, a)` to bidegree
`(m - 2a - (n - 1), -a - (n - 1))`; so the Poincaré series of `GH~(G')` is the conjugate of that
of `GH~(G)`, shifted by `(1 - n, 1 - n)`
(`TauCeti.OddComponentGridDiagram.bigradedFullyBlockedHomologyPoincareSeries_swapMarkings`).
Both series are those of `G-hat` times `W ^ (n - 1)`
(`TauCeti.GridDiagram.IsKnot.bigradedFullyBlockedHomologyPoincareSeries_eq_mul_W_pow`); the
conjugate of `W` is `W` shifted by `(1, 1)` (`TauCeti.Bigraded.conjugate_W`), which absorbs the
shift, and `W ^ (n - 1)` cancels.

In the conventions of Ozsváth--Stipsicz--Szabó, the marking swap and the diagonal reflection
`TauCeti.GridDiagram.transpose` each present the orientation reverse of the knot, so their
composite presents the knot itself; diagonal reflection preserves `G-hat`
(`TauCeti.GridDiagram.IsKnot.bigradedSimplyBlockedHomologyPoincareSeries_transpose`), so the
symmetry also holds between `G` and `G.transpose.swapMarkings`. Applying the Euler characteristic
turns it into the symmetry `χ(t) ↦ χ(t⁻¹)` of the graded Euler characteristic.

## Main results

* `TauCeti.GridDiagram.IsKnot.bigradedSimplyBlockedHomologyPoincareSeries_swapMarkings`: the
  Poincaré series of `G-hat` of the marking-swapped diagram is the conjugate series.
* `TauCeti.GridDiagram.IsKnot.bigradedSimplyBlockedHomologyPoincareSeries_transpose_swapMarkings`:
  the same for the reflected and marking-swapped diagram.
* `TauCeti.GridDiagram.IsKnot.gradedSimplyBlockedHomologyEulerChar_swapMarkings`,
  `TauCeti.GridDiagram.IsKnot.gradedSimplyBlockedHomologyEulerChar_transpose_swapMarkings`: the
  Euler characteristics are related by `T ↦ T⁻¹`.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Section 7.1 (Proposition 7.1.1).
-/

public section

namespace TauCeti.GridDiagram.IsKnot

open LaurentPolynomial

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot)

local notation "F" => ZMod 2
local notation "hGₛ" => G.isKnot_swapMarkings.mpr hG
local notation "hGₜₛ" => G.transpose.isKnot_swapMarkings.mpr (G.isKnot_transpose.mpr hG)

/-- **Conjugation symmetry of `G-hat`.** For a knot grid `G` and any blocked column `i`, the
`(O-Maslov, Alexander)` Poincaré series of simply blocked grid homology of the marking-swapped
diagram is the conjugate of that of `G`: `G-hat_m(G.swapMarkings, a) ≅ G-hat_(m - 2a)(G, -a)`. -/
theorem bigradedSimplyBlockedHomologyPoincareSeries_swapMarkings (i : Fin n) :
    (hGₛ).bigradedSimplyBlockedHomologyPoincareSeries F i =
      Bigraded.conjugate (hG.bigradedSimplyBlockedHomologyPoincareSeries F i) := by
  have hn : (((n - 1 : ℕ) : ℤ)) = (n : ℤ) - 1 := by
    have := i.pos
    omega
  have hshift : (AddMonoidAlgebra.single (1 - (n : ℤ), 1 - (n : ℤ)) 1 : Bigraded.Series) *
      AddMonoidAlgebra.single (((n - 1 : ℕ) : ℤ), ((n - 1 : ℕ) : ℤ)) 1 = 1 := by
    rw [AddMonoidAlgebra.single_mul_single, mul_one, hn, AddMonoidAlgebra.one_def]
    congr 1
    ext <;> simp
  refine mul_left_injective₀ (pow_ne_zero (n - 1) Bigraded.W_ne_zero) ?_
  simp only
  rw [← (hGₛ).bigradedFullyBlockedHomologyPoincareSeries_eq_mul_W_pow i,
    ← hG.swapMarkings_toOddComponentGridDiagram,
    OddComponentGridDiagram.bigradedFullyBlockedHomologyPoincareSeries_swapMarkings,
    hG.bigradedFullyBlockedHomologyPoincareSeries_eq_mul_W_pow i, map_mul,
    Bigraded.conjugate_W_pow, mul_left_comm,
    ← mul_assoc (AddMonoidAlgebra.single (1 - (n : ℤ), 1 - (n : ℤ)) 1), hshift, one_mul]

/-- **Conjugation symmetry of `G-hat`, within one knot.** For a knot grid `G` and any blocked
column `i`, the Poincaré series of `G-hat` of the reflected and marking-swapped diagram, blocked
at the column `G.O i` that reflection moves `i` to, is the conjugate of that of `G`. -/
theorem bigradedSimplyBlockedHomologyPoincareSeries_transpose_swapMarkings (i : Fin n) :
    (hGₜₛ).bigradedSimplyBlockedHomologyPoincareSeries F (G.O i) =
      Bigraded.conjugate (hG.bigradedSimplyBlockedHomologyPoincareSeries F i) := by
  rw [(G.isKnot_transpose.mpr hG).bigradedSimplyBlockedHomologyPoincareSeries_swapMarkings,
    hG.bigradedSimplyBlockedHomologyPoincareSeries_transpose]

/-- The Alexander-graded Euler characteristic of `G-hat` of the marking-swapped diagram is that of
`G` with `T` replaced by `T⁻¹`. -/
theorem gradedSimplyBlockedHomologyEulerChar_swapMarkings (i : Fin n) :
    (hGₛ).gradedSimplyBlockedHomologyEulerChar F i =
      invert (hG.gradedSimplyBlockedHomologyEulerChar F i) := by
  rw [gradedSimplyBlockedHomologyEulerChar_eq_euler, gradedSimplyBlockedHomologyEulerChar_eq_euler,
    hG.bigradedSimplyBlockedHomologyPoincareSeries_swapMarkings, Bigraded.euler_conjugate]

/-- The Alexander-graded Euler characteristic of `G-hat` of the reflected and marking-swapped
diagram is that of `G` with `T` replaced by `T⁻¹`. -/
theorem gradedSimplyBlockedHomologyEulerChar_transpose_swapMarkings (i : Fin n) :
    (hGₜₛ).gradedSimplyBlockedHomologyEulerChar F (G.O i) =
      invert (hG.gradedSimplyBlockedHomologyEulerChar F i) := by
  rw [gradedSimplyBlockedHomologyEulerChar_eq_euler, gradedSimplyBlockedHomologyEulerChar_eq_euler,
    hG.bigradedSimplyBlockedHomologyPoincareSeries_transpose_swapMarkings, Bigraded.euler_conjugate]

end TauCeti.GridDiagram.IsKnot
