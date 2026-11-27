/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Grading.Component
public import TauCeti.LowDimTopology.Heegaard.Grid.Grading
public import TauCeti.LowDimTopology.Heegaard.Knot.Multigrading

/-!
# The component gradings of a grid are the Alexander multigrading of its Heegaard diagram

Let `G` be an `n × n` grid diagram of a link, viewed as a multi-pointed genus-one Heegaard diagram
(`TauCeti.GridDiagram.heegaardRegionSystem`) with the `O`-markings as `w`-basepoints and the
`X`-markings as `z`-basepoints. A link component `q` of `G` carries the basepoints of the markings
in its columns: the `w`'s `TauCeti.GridDiagram.componentOBasepoints q` and the `z`'s
`TauCeti.GridDiagram.componentXBasepoints q`. This file shows that, with these basepoints, the
relative Alexander multigrading of the Heegaard diagram
(`TauCeti.HeegaardRegionSystem.relativeComponentAlexanderGrading`) is the difference of the
Alexander gradings `A_q` of the components in grid homology
(`TauCeti.GridDiagram.componentAlexander`): for every domain `D` from (the generator of) a grid
state `x` to (that of) `y`,

`∑_{c ∈ q} n_{X_c}(D) - ∑_{c ∈ q} n_{O_c}(D) = A_q(x) - A_q(y)`

(`TauCeti.GridDiagram.componentAlexanderMultiplicity_apply_of_isDomainBetween`). This is the
link version of `TauCeti.GridDiagram.sum_basepoint_inr_sub_sum_basepoint_inl_of_isDomainBetween`,
to which it sums over the components.

The proof follows the knot case. Across a rectangle both sides count the markings of `q` that the
rectangle covers (`TauCeti.GridDiagram.componentAlexander_sub_componentAlexander_eq_card_sub_card`).
A domain from a generator to itself is a sum `E(c, r) = a(r) + b(c)` of horizontal and vertical
annuli (`TauCeti.GridDiagram.exists_eq_add_of_isDomainBetween_self`). Its multiplicity at the
markings of `q` is `∑_{c ∈ q} a(X c) - ∑_{c ∈ q} a(O c)`, which vanishes because the `X`- and the
`O`-markings of a component occupy the same rows
(`TauCeti.GridDiagram.sum_componentColumns_O_eq_sum_componentColumns_X`). Rectangle moves join any
two grid states, so the rectangle case extends to all domains.

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

## Main definitions

* `TauCeti.GridDiagram.componentOBasepoints`, `TauCeti.GridDiagram.componentXBasepoints`: the
  `w`- and `z`-basepoints of a link component.

## Main results

* `TauCeti.GridDiagram.componentAlexanderMultiplicity_apply_of_isDomainBetween`: the component
  gradings are the Alexander multigrading of every domain.
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

section Basepoints

/-- The `w`-basepoints of the link component `q` in the Heegaard diagram of a grid diagram: the
basepoints `Sum.inl c` of the `O`-markings in the columns `c` of `q`. -/
def componentOBasepoints (q : G.Components) : Finset (Fin n ⊕ Fin n) :=
  (G.componentColumns q).map .inl

/-- The `w`-basepoints of a component as the image of its columns under `Sum.inl`. -/
theorem componentOBasepoints_def (q : G.Components) :
    G.componentOBasepoints q = (G.componentColumns q).map .inl :=
  (rfl)

/-- The `z`-basepoints of the link component `q` in the Heegaard diagram of a grid diagram: the
basepoints `Sum.inr c` of the `X`-markings in the columns `c` of `q`. -/
def componentXBasepoints (q : G.Components) : Finset (Fin n ⊕ Fin n) :=
  (G.componentColumns q).map .inr

/-- The `z`-basepoints of a component as the image of its columns under `Sum.inr`. -/
theorem componentXBasepoints_def (q : G.Components) :
    G.componentXBasepoints q = (G.componentColumns q).map .inr :=
  (rfl)

variable {G}

/-- The `O`-marking of a column is a `w`-basepoint of the component of that column. -/
@[simp]
theorem inl_mem_componentOBasepoints {q : G.Components} {c : Fin n} :
    Sum.inl c ∈ G.componentOBasepoints q ↔ G.componentOfColumn c = q := by
  simp [componentOBasepoints]

/-- No `X`-marking is a `w`-basepoint. -/
@[simp]
theorem inr_notMem_componentOBasepoints (q : G.Components) (c : Fin n) :
    Sum.inr c ∉ G.componentOBasepoints q := by
  simp [componentOBasepoints]

/-- The `X`-marking of a column is a `z`-basepoint of the component of that column. -/
@[simp]
theorem inr_mem_componentXBasepoints {q : G.Components} {c : Fin n} :
    Sum.inr c ∈ G.componentXBasepoints q ↔ G.componentOfColumn c = q := by
  simp [componentXBasepoints]

/-- No `O`-marking is a `z`-basepoint. -/
@[simp]
theorem inl_notMem_componentXBasepoints (q : G.Components) (c : Fin n) :
    Sum.inl c ∉ G.componentXBasepoints q := by
  simp [componentXBasepoints]

variable (G)

/-- A sum over the `w`-basepoints of a component is a sum over its columns. -/
theorem sum_componentOBasepoints {M : Type*} [AddCommMonoid M] (q : G.Components)
    (f : Fin n ⊕ Fin n → M) :
    ∑ b ∈ G.componentOBasepoints q, f b = ∑ c ∈ G.componentColumns q, f (Sum.inl c) :=
  sum_map _ _ _

/-- A sum over the `z`-basepoints of a component is a sum over its columns. -/
theorem sum_componentXBasepoints {M : Type*} [AddCommMonoid M] (q : G.Components)
    (f : Fin n ⊕ Fin n → M) :
    ∑ b ∈ G.componentXBasepoints q, f b = ∑ c ∈ G.componentColumns q, f (Sum.inr c) :=
  sum_map _ _ _

end Basepoints

section Domains

variable [NeZero n]

/-- **The multiplicity of a rectangle at the markings of a component.** The Alexander multiplicity
of the domain of a rectangle from `x` to `y` at the component `q` is the difference
`A_q(x) - A_q(y)` of the component gradings. -/
theorem componentAlexanderMultiplicity_domain {x y : GridState n} (R : GridRectangleBetween x y)
    (q : G.Components) :
    (G.heegaardRegionSystem.componentAlexanderMultiplicity G.componentOBasepoints
        G.componentXBasepoints R.toGridRectangle.domain q : ℚ) =
      G.componentAlexander q x - G.componentAlexander q y := by
  rw [G.componentAlexander_sub_componentAlexander_eq_card_sub_card q R,
    componentAlexanderMultiplicity_apply, sum_componentXBasepoints, sum_componentOBasepoints]
  simp only [heegaardRegionSystem_basepoint_inl, heegaardRegionSystem_basepoint_inr]
  rw [← G.sum_componentXSet q R.toGridRectangle.domain,
    ← G.sum_componentOSet q R.toGridRectangle.domain]
  simp only [GridRectangle.domain_apply, sum_boole, filter_mem_eq_inter]
  norm_cast

/-- **Domains from a generator to itself have vanishing Alexander multiplicities.** A domain from
a generator of the Heegaard diagram of a grid diagram to itself has the same multiplicity at the
`X`-markings of each component as at its `O`-markings. -/
theorem componentAlexanderMultiplicity_eq_zero_of_isDomainBetween_self
    {g : G.heegaardRegionSystem.Generator} {E : Fin n × Fin n → ℤ}
    (hE : G.heegaardRegionSystem.IsDomainBetween g g E) :
    G.heegaardRegionSystem.componentAlexanderMultiplicity G.componentOBasepoints
      G.componentXBasepoints E = 0 := by
  obtain ⟨a, b, h⟩ := G.exists_eq_add_of_isDomainBetween_self hE
  ext q
  simp only [componentAlexanderMultiplicity_apply, sum_componentXBasepoints,
    sum_componentOBasepoints, heegaardRegionSystem_basepoint_inl,
    heegaardRegionSystem_basepoint_inr, h, sum_add_distrib,
    G.sum_componentColumns_O_eq_sum_componentColumns_X q a, sub_self, Pi.zero_apply]

/-- **The component gradings of every domain.** For every domain `D` from the generator of a grid
state `x` to the generator of a grid state `y` and every link component `q`, the Alexander
multiplicity `∑_{c ∈ q} n_{X_c}(D) - ∑_{c ∈ q} n_{O_c}(D)` is the difference `A_q(x) - A_q(y)` of
the component gradings of grid homology. -/
theorem componentAlexanderMultiplicity_apply_of_isDomainBetween {x y : GridState n}
    {D : Fin n × Fin n → ℤ}
    (hD : G.heegaardRegionSystem.IsDomainBetween (G.gridStateEquivGenerator x)
      (G.gridStateEquivGenerator y) D) (q : G.Components) :
    (G.heegaardRegionSystem.componentAlexanderMultiplicity G.componentOBasepoints
        G.componentXBasepoints D q : ℚ) =
      G.componentAlexander q x - G.componentAlexander q y :=
  eq_sub_of_isDomainBetween (fun _ _ D => (G.heegaardRegionSystem.componentAlexanderMultiplicity
      G.componentOBasepoints G.componentXBasepoints D q : ℚ)) (G.componentAlexander q)
    (fun _ _ => by rw [map_add, Pi.add_apply, Int.cast_add])
    (fun hE => by
      rw [G.componentAlexanderMultiplicity_eq_zero_of_isDomainBetween_self hE, Pi.zero_apply,
        Int.cast_zero])
    (fun R => G.componentAlexanderMultiplicity_domain R q) hD

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
