/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.Grid.Grading
public import TauCeti.LowDimTopology.Heegaard.Knot.Multigrading

/-!
# The grid multigrading is the Alexander multigrading of the grid Heegaard diagram

Let `G` be an `n × n` grid diagram of a link `L = L₁ ∪ ⋯ ∪ L_ℓ`, viewed as a multi-pointed
genus-one Heegaard diagram (`TauCeti.GridDiagram.heegaardRegionSystem`) with the markings in the
columns of the link component `q` as the basepoints of `q`
(`TauCeti.GridDiagram.componentOBasepoints`, `TauCeti.GridDiagram.componentXBasepoints`).
`TauCeti.LowDimTopology.Heegaard.Grid.Grading` shows that for every domain `D` from (the
generator of) a grid state `x` to (the generator of) a grid state `y` and every component `q`,

`∑_{c ∈ q} n_{X_c}(D) - ∑_{c ∈ q} n_{O_c}(D) = A_q(x) - A_q(y)`

(`TauCeti.GridDiagram.componentAlexanderMultiplicity_apply_eq_sub_of_isDomainBetween`), and that
a domain from a generator to itself has vanishing multiplicity vector
(`TauCeti.GridDiagram.componentAlexanderMultiplicity_eq_zero_of_isDomainBetween_self`). This file
identifies the Heegaard Floer Alexander multigrading
`TauCeti.HeegaardRegionSystem.relativeComponentAlexanderGrading` of
`TauCeti.LowDimTopology.Heegaard.AlexanderGrading` with the combinatorial Alexander multigrading
`TauCeti.GridDiagram.componentAlexander` of grid homology.

The periodic values of the multigrading vanish
(`TauCeti.GridDiagram.periodicComponentAlexanderValues_eq_bot`), so the relative multigrading
is a vector of integers determined by any domain. It is the difference of the grid multigradings
(`TauCeti.GridDiagram.heegaardRegionSystem_relativeComponentAlexanderGrading_apply`). The hat
differential of the grid Heegaard diagram preserves every `A_q`. A term `∏_b X_b ^ m b · y` of its
full multi-pointed differential of `x` has
`A_q(x) - A_q(y) = ∑_{c ∈ q} m(X_c) - ∑_{c ∈ q} m(O_c)`, so the variable of an `X`-marking of `q`
has degree `1` in the `q`-th grading and that of an `O`-marking of `q` degree `-1`.

## Main results

* `TauCeti.GridDiagram.periodicComponentAlexanderValues_eq_bot`: the periodic values of the grid
  multigrading vanish.
* `TauCeti.GridDiagram.heegaardRegionSystem_relativeComponentAlexanderGrading_apply`: the
  relative Alexander multigrading of the grid Heegaard diagram is the difference of the grid
  multigradings.
* In the namespace `TauCeti.GridDiagram`, `componentAlexander_eq_of_hatCoefficient_ne_zero` and
  `componentAlexander_sub_componentAlexander_eq_of_coeff_fullCoefficient_ne_zero`: the gradings of
  the terms of the hat and full differentials.

## References

* C. Manolescu, P. Ozsváth, Z. Szabó and D. Thurston, *On combinatorial link Floer homology*,
  Geom. Topol. **11** (2007), [arXiv:math/0610559](https://arxiv.org/abs/math/0610559), §2: the
  Alexander multigrading of a grid state and its agreement with the multigrading of the
  multi-pointed Heegaard diagram of the grid.
-/

public section

namespace TauCeti

open Finset HeegaardRegionSystem

variable {n : ℕ}

namespace GridDiagram

variable [NeZero n] (G : GridDiagram n)

/-- **The periodic values of the grid multigrading vanish.** In the Heegaard diagram of a grid
diagram, with the markings of each link component as its basepoints, every domain whose boundary
is a combination of whole curves has vanishing Alexander multiplicity vector. -/
theorem periodicComponentAlexanderValues_eq_bot :
    G.heegaardRegionSystem.periodicComponentAlexanderValues G.componentOBasepoints
      G.componentXBasepoints = ⊥ := by
  refine (AddSubgroup.eq_bot_iff_forall _).mpr fun v hv => ?_
  obtain ⟨E, hE, rfl⟩ := (mem_periodicComponentAlexanderValues_iff_exists_isDomainBetween
    (G.gridStateEquivGenerator G.O)).mp hv
  exact componentAlexanderMultiplicity_eq_zero_of_isDomainBetween_self hE

/-- **The relative Alexander multigrading of a grid is the grid multigrading.** In the Heegaard
diagram of a grid diagram, with the markings of each link component as its basepoints, the
relative Alexander multigrading of the generators of two grid states `x` and `y` at a component
`q` is `A_q(x) - A_q(y)`. -/
theorem heegaardRegionSystem_relativeComponentAlexanderGrading_apply (x y : GridState n)
    (q : G.Components) :
    (G.heegaardRegionSystem.relativeComponentAlexanderGrading G.componentOBasepoints
        G.componentXBasepoints (G.gridStateEquivGenerator x) (G.gridStateEquivGenerator y) q :
          ℚ) =
      G.componentAlexander q x - G.componentAlexander q y := by
  obtain ⟨D, hD⟩ := G.exists_isDomainBetween (G.gridStateEquivGenerator x)
    (G.gridStateEquivGenerator y)
  rw [hD.relativeComponentAlexanderGrading_eq (periodicComponentAlexanderValues_eq_bot G),
    componentAlexanderMultiplicity_apply_eq_sub_of_isDomainBetween hD]

variable {G}

/-- **The hat differential of a grid preserves the multigrading.** A nonzero coefficient of the hat
differential of the Heegaard diagram of a grid diagram joins grid states with the same Alexander
grading `A_q` for every link component `q`. -/
theorem componentAlexander_eq_of_hatCoefficient_ne_zero {χ : Fin n × Fin n → ℤ}
    {x y : GridState n}
    (h : G.heegaardRegionSystem.hatCoefficient χ (G.gridStateEquivGenerator x)
      (G.gridStateEquivGenerator y) ≠ 0) (q : G.Components) :
    G.componentAlexander q x = G.componentAlexander q y := by
  have h₀ := relativeComponentAlexanderGrading_eq_zero_of_hatCoefficient_ne_zero
    (periodicComponentAlexanderValues_eq_bot G) h
  have := G.heegaardRegionSystem_relativeComponentAlexanderGrading_apply x y q
  rw [h₀, Pi.zero_apply, Int.cast_zero] at this
  linarith

/-- **The gradings of the terms of the full differential of a grid.** A term `∏_b X_b ^ m b · y` of
the full multi-pointed differential of the generator of `x` in the Heegaard diagram of a grid
diagram has `A_q(x) - A_q(y) = ∑_{c ∈ q} m(X_c) - ∑_{c ∈ q} m(O_c)` for every link component `q`.
So, giving the variable of an `X`-marking of `q` degree `1` and that of an `O`-marking of `q` degree
`-1` in the `q`-th grading, the full differential preserves every Alexander grading. -/
theorem componentAlexander_sub_componentAlexander_eq_of_coeff_fullCoefficient_ne_zero
    {χ : Fin n × Fin n → ℤ} {x y : GridState n} {m : Fin n ⊕ Fin n →₀ ℕ}
    (h : (G.heegaardRegionSystem.fullCoefficient χ (G.gridStateEquivGenerator x)
      (G.gridStateEquivGenerator y)).coeff m ≠ 0) (q : G.Components) :
    G.componentAlexander q x - G.componentAlexander q y =
      ∑ c ∈ G.componentColumns q, (m (Sum.inr c) : ℚ) -
        ∑ c ∈ G.componentColumns q, (m (Sum.inl c) : ℚ) := by
  rw [← G.heegaardRegionSystem_relativeComponentAlexanderGrading_apply x y q,
    relativeComponentAlexanderGrading_eq_of_coeff_fullCoefficient_ne_zero
      (periodicComponentAlexanderValues_eq_bot G) h q]
  simp

end GridDiagram

end TauCeti
