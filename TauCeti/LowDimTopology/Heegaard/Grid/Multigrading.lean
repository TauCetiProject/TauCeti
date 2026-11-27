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
# The grid multigrading is the Alexander multigrading of the grid Heegaard diagram

Let `G` be an `n × n` grid diagram of a link `L = L₁ ∪ ⋯ ∪ L_ℓ`, viewed as a multi-pointed
genus-one Heegaard diagram (`TauCeti.GridDiagram.heegaardRegionSystem`) with the `O`-markings as
`w`-basepoints and the `X`-markings as `z`-basepoints. The markings in the columns of the link
component `q` are the basepoints of `q`: the `w`'s `TauCeti.GridDiagram.componentOBasepoints q` and
the `z`'s `TauCeti.GridDiagram.componentXBasepoints q`. With these, the Heegaard Floer Alexander
multigrading `TauCeti.HeegaardRegionSystem.relativeComponentAlexanderGrading` of
`TauCeti.LowDimTopology.Heegaard.AlexanderGrading` is the combinatorial Alexander multigrading
`TauCeti.GridDiagram.componentAlexander` of grid homology: for every domain `D` from (the
generator of) a grid state `x` to (the generator of) a grid state `y` and every component `q`,

`∑_{c ∈ q} n_{X_c}(D) - ∑_{c ∈ q} n_{O_c}(D) = A_q(x) - A_q(y)`

(`TauCeti.GridDiagram.componentAlexanderMultiplicity_apply_eq_sub_of_isDomainBetween`). This is
the link version of the knot statement
`TauCeti.GridDiagram.sum_basepoint_inr_sub_sum_basepoint_inl_of_isDomainBetween`, and the proof is
the same. Across a rectangle both sides count the markings of `q` it covers
(`TauCeti.GridDiagram.componentAlexander_sub_componentAlexander_eq_card_sub_card`). A domain from a
generator to itself is a sum of horizontal and vertical annuli
(`TauCeti.GridDiagram.exists_eq_add_of_isDomainBetween_self`). A vertical annulus contains either
no marking of `q` or one `X` and one `O` of `q`. The `X`- and `O`-markings of `q` occupy the same
rows (`TauCeti.GridDiagram.sum_componentColumns_X_eq_sum_O`), so a horizontal annulus meets as
many `X`'s as `O`'s of `q`. Hence such a domain has vanishing multiplicity vector.

Consequently the periodic values of the multigrading vanish
(`TauCeti.GridDiagram.periodicComponentAlexanderValues_eq_bot`), so the relative multigrading
is a vector of integers determined by any domain. It is the difference of the grid multigradings
(`TauCeti.GridDiagram.heegaardRegionSystem_relativeComponentAlexanderGrading_apply`). The hat
differential of the grid Heegaard diagram preserves every `A_q`. A term `∏_b X_b ^ m b · y` of its
full multi-pointed differential of `x` has
`A_q(x) - A_q(y) = ∑_{c ∈ q} m(X_c) - ∑_{c ∈ q} m(O_c)`, so the variable of an `X`-marking of `q`
has degree `1` in the `q`-th grading and that of an `O`-marking of `q` degree `-1`.

## Main definitions

* `TauCeti.GridDiagram.componentOBasepoints`, `TauCeti.GridDiagram.componentXBasepoints`: the
  `O`- and `X`-basepoints of a link component in the Heegaard diagram of a grid.

## Main results

* `TauCeti.GridDiagram.componentAlexanderMultiplicity_apply_eq_sub_of_isDomainBetween`: the
  multiplicity vector of every domain is the difference of the grid multigradings.
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
* C. Manolescu, P. Ozsváth and S. Sarkar, *A combinatorial description of knot Floer homology*,
  Ann. of Math. **169** (2009), [arXiv:math/0607691](https://arxiv.org/abs/math/0607691), §2: the
  reduction to rectangles and to the periodic domains of a grid.
-/

public section

namespace TauCeti

open Finset HeegaardRegionSystem

variable {n : ℕ}

namespace GridDiagram

variable (G : GridDiagram n)

section Basepoints

/-- The `O`-basepoints `Sum.inl c` of the link component `q`, for the columns `c` of `q`, in the
Heegaard diagram of a grid diagram: the `w`'s of `q`. -/
def componentOBasepoints (q : G.Components) : Finset (Fin n ⊕ Fin n) :=
  (G.componentColumns q).map Function.Embedding.inl

/-- The `X`-basepoints `Sum.inr c` of the link component `q`, for the columns `c` of `q`, in the
Heegaard diagram of a grid diagram: the `z`'s of `q`. -/
def componentXBasepoints (q : G.Components) : Finset (Fin n ⊕ Fin n) :=
  (G.componentColumns q).map Function.Embedding.inr

variable {G} {q : G.Components} {c : Fin n}

/-- `Sum.inl c` is an `O`-basepoint of `q` when the column `c` lies on `q`. -/
@[simp]
theorem inl_mem_componentOBasepoints :
    Sum.inl c ∈ G.componentOBasepoints q ↔ G.componentOfColumn c = q := by
  simp [componentOBasepoints, mem_componentColumns]

/-- No `X`-marking is an `O`-basepoint of a component. -/
@[simp]
theorem inr_notMem_componentOBasepoints : Sum.inr c ∉ G.componentOBasepoints q := by
  simp [componentOBasepoints]

/-- `Sum.inr c` is an `X`-basepoint of `q` when the column `c` lies on `q`. -/
@[simp]
theorem inr_mem_componentXBasepoints :
    Sum.inr c ∈ G.componentXBasepoints q ↔ G.componentOfColumn c = q := by
  simp [componentXBasepoints, mem_componentColumns]

/-- No `O`-marking is an `X`-basepoint of a component. -/
@[simp]
theorem inl_notMem_componentXBasepoints : Sum.inl c ∉ G.componentXBasepoints q := by
  simp [componentXBasepoints]

/-- A sum over the `O`-basepoints of a component is a sum over its columns. -/
@[simp]
theorem sum_componentOBasepoints {M : Type*} [AddCommMonoid M] (f : Fin n ⊕ Fin n → M) :
    ∑ b ∈ G.componentOBasepoints q, f b = ∑ c ∈ G.componentColumns q, f (Sum.inl c) :=
  sum_map _ _ _

/-- A sum over the `X`-basepoints of a component is a sum over its columns. -/
@[simp]
theorem sum_componentXBasepoints {M : Type*} [AddCommMonoid M] (f : Fin n ⊕ Fin n → M) :
    ∑ b ∈ G.componentXBasepoints q, f b = ∑ c ∈ G.componentColumns q, f (Sum.inr c) :=
  sum_map _ _ _

end Basepoints

variable [NeZero n]

/-- The multiplicity vector of a domain in the Heegaard diagram of a grid diagram: its component
at `q` is the multiplicity at the `X`-markings of `q` minus that at the `O`-markings of `q`. -/
theorem heegaardRegionSystem_componentAlexanderMultiplicity_apply (D : Fin n × Fin n → ℤ)
    (q : G.Components) :
    G.heegaardRegionSystem.componentAlexanderMultiplicity G.componentOBasepoints
        G.componentXBasepoints D q =
      ∑ c ∈ G.componentColumns q, D (c, G.X c) - ∑ c ∈ G.componentColumns q, D (c, G.O c) := by
  simp [heegaardRegionSystem_basepoint_inl, heegaardRegionSystem_basepoint_inr]

/-- The multiplicity vector of the domain of a rectangle counts, at each component `q`, the
`X`-markings of `q` that the rectangle covers minus the `O`-markings of `q` that it covers. -/
theorem componentAlexanderMultiplicity_domain (R : GridRectangle n) (q : G.Components) :
    G.heegaardRegionSystem.componentAlexanderMultiplicity G.componentOBasepoints
        G.componentXBasepoints R.domain q =
      #(G.componentXSet q ∩ R.coveredSquares) - #(G.componentOSet q ∩ R.coveredSquares) := by
  rw [heegaardRegionSystem_componentAlexanderMultiplicity_apply, ← sum_componentXSet,
    ← sum_componentOSet]
  simp only [GridRectangle.domain_apply, sum_boole, filter_mem_eq_inter]

variable {G}

/-- **Domains from a generator to itself have vanishing multiplicity vector.** A domain from a
generator of the Heegaard diagram of a grid diagram to itself has, for every link component `q`,
the same total multiplicity at the `X`-markings of `q` as at the `O`-markings of `q`. -/
theorem componentAlexanderMultiplicity_eq_zero_of_isDomainBetween_self
    {g : G.heegaardRegionSystem.Generator} {E : Fin n × Fin n → ℤ}
    (hE : G.heegaardRegionSystem.IsDomainBetween g g E) :
    G.heegaardRegionSystem.componentAlexanderMultiplicity G.componentOBasepoints
      G.componentXBasepoints E = 0 := by
  -- `E` is a sum of horizontal and vertical annuli. A vertical annulus meets no marking of `q`
  -- or one `X` and one `O` of `q`; the `X`- and `O`-markings of `q` occupy the same rows.
  obtain ⟨a, b, h⟩ := G.exists_eq_add_of_isDomainBetween_self hE
  ext q
  simp only [heegaardRegionSystem_componentAlexanderMultiplicity_apply, h, sum_add_distrib,
    Pi.zero_apply, G.sum_componentColumns_X_eq_sum_O q a, sub_self]

variable (G) in
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

/-- **The grid multigrading of every domain.** For every domain `D` from the generator of a grid
state `x` to the generator of a grid state `y` and every link component `q`, the Heegaard Floer
Alexander multiplicity `∑_{c ∈ q} n_{X_c}(D) - ∑_{c ∈ q} n_{O_c}(D)` is the difference
`A_q(x) - A_q(y)` of the Alexander multigradings of grid homology. -/
theorem componentAlexanderMultiplicity_apply_eq_sub_of_isDomainBetween {x y : GridState n}
    {D : Fin n × Fin n → ℤ}
    (hD : G.heegaardRegionSystem.IsDomainBetween (G.gridStateEquivGenerator x)
      (G.gridStateEquivGenerator y) D) (q : G.Components) :
    (G.heegaardRegionSystem.componentAlexanderMultiplicity G.componentOBasepoints
        G.componentXBasepoints D q : ℚ) =
      G.componentAlexander q x - G.componentAlexander q y := by
  refine eq_sub_of_isDomainBetween (fun _ _ D =>
      (G.heegaardRegionSystem.componentAlexanderMultiplicity G.componentOBasepoints
        G.componentXBasepoints D q : ℚ)) (G.componentAlexander q)
    (fun _ _ => by simp only [map_add, Pi.add_apply, Int.cast_add]) (fun hE => ?_)
    (fun R => ?_) hD
  · rw [componentAlexanderMultiplicity_eq_zero_of_isDomainBetween_self hE, Pi.zero_apply,
      Int.cast_zero]
  · rw [componentAlexanderMultiplicity_domain,
      G.componentAlexander_sub_componentAlexander_eq_card_sub_card q R]
    norm_cast

variable (G) in
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
