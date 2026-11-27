/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.Grid.Grading
public import TauCeti.LowDimTopology.Heegaard.Knot.Multigrading

/-!
# The component gradings of a grid are the Alexander multigrading of its Heegaard diagram

Let `G` be an `n × n` grid diagram of a link, viewed as a multi-pointed genus-one Heegaard diagram
(`TauCeti.GridDiagram.heegaardRegionSystem`) with the `O`-markings as `w`-basepoints and the
`X`-markings as `z`-basepoints. A link component `q` of `G` carries the basepoints of the markings
in its columns: the `w`'s `TauCeti.GridDiagram.componentOBasepoints q` and the `z`'s
`TauCeti.GridDiagram.componentXBasepoints q`. `TauCeti.LowDimTopology.Heegaard.Grid.Grading` shows
that for every domain `D` from (the generator of) a grid state `x` to (that of) `y`,

`∑_{c ∈ q} n_{X_c}(D) - ∑_{c ∈ q} n_{O_c}(D) = A_q(x) - A_q(y)`

(`TauCeti.GridDiagram.componentAlexanderMultiplicity_apply_of_isDomainBetween`), where `A_q` is
the Alexander grading of the component `q` in grid homology
(`TauCeti.GridDiagram.componentAlexander`), and that a domain from a generator to itself has
vanishing multiplicity at every component
(`TauCeti.GridDiagram.componentAlexanderMultiplicity_eq_zero_of_isDomainBetween_self`). This file
identifies, with these basepoints, the relative Alexander multigrading of the Heegaard diagram
(`TauCeti.HeegaardRegionSystem.relativeComponentAlexanderGrading`) with the component gradings.

Consequently:

* the periodic values of the multigrading vanish
  (`TauCeti.GridDiagram.periodicComponentAlexanderValues_eq_bot`), so for grid diagrams the
  general results on link diagrams hold without their hypothesis on periodic domains;
* the relative multigrading of two grid states is `A_q(x) - A_q(y)`
  (`TauCeti.GridDiagram.intCast_relativeComponentAlexanderGrading_gridStateEquivGenerator`); in
  particular the component gradings of any two grid states differ by integers
  (`TauCeti.GridDiagram.exists_intCast_eq_componentAlexander_sub_componentAlexander`), although
  they are only rational;
* a term `∏_b X_b ^ m b · y` of the full multi-pointed differential of `x` has
  `A_q(x) - A_q(y) = ∑_{c ∈ q} (m (X_c) - m (O_c))`
  (`GridDiagram.componentAlexander_sub_componentAlexander_eq_of_coeff_fullCoefficient_ne_zero`),
  and the hat differential, which counts the domains avoiding every marking, preserves every
  component grading
  (`TauCeti.GridDiagram.componentAlexander_eq_of_hatCoefficient_ne_zero`).

## Main results

* `TauCeti.GridDiagram.periodicComponentAlexanderValues_eq_bot`: the multigrading has no periodic
  values.
* `TauCeti.GridDiagram.intCast_relativeComponentAlexanderGrading_gridStateEquivGenerator`: the
  relative multigrading is the difference of the component gradings.

## References

* C. Manolescu, P. Ozsváth, Z. Szabó and D. Thurston, *On combinatorial link Floer homology*,
  Geom. Topol. **11** (2007), [arXiv:math/0610559](https://arxiv.org/abs/math/0610559), §2, where
  the Alexander multigrading of a grid state is defined and compared with that of the Heegaard
  diagram.
* P. Ozsváth and Z. Szabó, *Holomorphic disks, link invariants and the multi-variable Alexander
  polynomial*, Algebr. Geom. Topol. **8** (2008),
  [arXiv:math/0512286](https://arxiv.org/abs/math/0512286), §3, for the Alexander multigrading
  of a multi-pointed link diagram.
-/

public section

namespace TauCeti

open Finset HeegaardRegionSystem

variable {n : ℕ}

namespace GridDiagram

variable (G : GridDiagram n)

section Domains

variable [NeZero n]

/-- **The Alexander multigrading of a grid has no periodic values.** Every domain of the Heegaard
diagram of a grid diagram whose boundary is a combination of whole curves has vanishing Alexander
multiplicity at every link component. -/
theorem periodicComponentAlexanderValues_eq_bot :
    G.heegaardRegionSystem.periodicComponentAlexanderValues G.componentOBasepoints
      G.componentXBasepoints = ⊥ :=
  periodicComponentAlexanderValues_eq_bot_iff.mpr fun _ hα hβ =>
    G.componentAlexanderMultiplicity_eq_zero_of_isDomainBetween_self
      (g := G.gridStateEquivGenerator ⟨1⟩)
      (isDomainBetween_self_iff_arcBoundary_eq_zero.mpr ⟨hα, hβ⟩)

/-- **The relative Alexander multigrading of a grid.** The relative Alexander multigrading of the
generators of two grid states is the difference of their component gradings. -/
theorem intCast_relativeComponentAlexanderGrading_gridStateEquivGenerator (x y : GridState n)
    (q : G.Components) :
    (G.heegaardRegionSystem.relativeComponentAlexanderGrading G.componentOBasepoints
        G.componentXBasepoints (G.gridStateEquivGenerator x) (G.gridStateEquivGenerator y) q :
        ℚ) =
      G.componentAlexander q x - G.componentAlexander q y := by
  obtain ⟨D, hD⟩ := G.exists_isDomainBetween (G.gridStateEquivGenerator x)
    (G.gridStateEquivGenerator y)
  rw [hD.relativeComponentAlexanderGrading_eq G.periodicComponentAlexanderValues_eq_bot,
    G.componentAlexanderMultiplicity_apply_of_isDomainBetween hD]

end Domains

section Differentials

variable [NeZero n] {χ : Fin n × Fin n → ℤ} {x y : GridState n}

/-- **The full differential and the component gradings.** If the full multi-pointed coefficient
from `x` to `y` contains the monomial `∏_b X_b ^ m b`, then `A_q(x) - A_q(y)` is the total exponent
of the `X`-markings of the component `q` minus that of its `O`-markings. -/
theorem componentAlexander_sub_componentAlexander_eq_of_coeff_fullCoefficient_ne_zero
    {m : Fin n ⊕ Fin n →₀ ℕ}
    (h : (G.heegaardRegionSystem.fullCoefficient χ (G.gridStateEquivGenerator x)
      (G.gridStateEquivGenerator y)).coeff m ≠ 0) (q : G.Components) :
    G.componentAlexander q x - G.componentAlexander q y =
      ∑ c ∈ G.componentColumns q, ((m (Sum.inr c) : ℚ) - m (Sum.inl c)) := by
  rw [← G.intCast_relativeComponentAlexanderGrading_gridStateEquivGenerator,
    relativeComponentAlexanderGrading_eq_of_coeff_fullCoefficient_ne_zero
      G.periodicComponentAlexanderValues_eq_bot h q,
    sum_componentXBasepoints, sum_componentOBasepoints, sum_sub_distrib]
  norm_cast

/-- **The hat differential preserves the component gradings.** A nonzero coefficient of the hat
differential of the Heegaard diagram of a grid diagram, which counts the domains avoiding every
marking, joins grid states with the same component gradings. -/
theorem componentAlexander_eq_of_hatCoefficient_ne_zero
    (h : G.heegaardRegionSystem.hatCoefficient χ (G.gridStateEquivGenerator x)
      (G.gridStateEquivGenerator y) ≠ 0) (q : G.Components) :
    G.componentAlexander q x = G.componentAlexander q y := by
  rw [← sub_eq_zero, ← G.intCast_relativeComponentAlexanderGrading_gridStateEquivGenerator,
    relativeComponentAlexanderGrading_eq_zero_of_hatCoefficient_ne_zero
      G.periodicComponentAlexanderValues_eq_bot h, Pi.zero_apply, Int.cast_zero]

end Differentials

/-- **The component gradings differ by integers.** The Alexander gradings `A_q` of the components
of a grid diagram are rational, but those of any two grid states differ by an integer, the relative
Alexander multigrading of the Heegaard diagram. -/
theorem exists_intCast_eq_componentAlexander_sub_componentAlexander (q : G.Components)
    (x y : GridState n) :
    ∃ k : ℤ, (k : ℚ) = G.componentAlexander q x - G.componentAlexander q y := by
  rcases eq_zero_or_neZero n with rfl | _
  · obtain rfl : x = y := (GridState.equivPerm 0).injective (Subsingleton.elim _ _)
    exact ⟨0, by rw [sub_self, Int.cast_zero]⟩
  · exact ⟨_, G.intCast_relativeComponentAlexanderGrading_gridStateEquivGenerator x y q⟩

end GridDiagram

end TauCeti
