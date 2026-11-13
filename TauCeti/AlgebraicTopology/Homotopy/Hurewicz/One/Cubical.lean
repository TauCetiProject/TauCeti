/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.CubePair

/-!
# The cubical and singular Hurewicz maps in degree one

A loop `p : Ω^ (Fin 1) X x` has two homology classes:

* its **cubical Hurewicz class** `GenLoop.cubicalHurewicz k p`, the class of the `1`-cube `p`
  itself, which is a cycle of the normalized cubical chains of `X`;
* its **Hurewicz class** `GenLoop.hurewicz R p` in simplicial singular homology, the image of the
  generator of `H₁(I¹, ∂I¹; R) ≅ R` under `p : (I¹, ∂I¹) ⟶ (X, {x})`.

The cubical–simplicial comparison `TauCeti.singularCubicalHomologyIso` identifies them exactly,
over every ring `k` and with no sign (`GenLoop.singularCubicalHomologyIso_inv_cubicalHurewicz`). In
higher degrees the two Hurewicz maps are only known to agree up to a universal sign over `ℤ`
(`HomotopyGroup.exists_hurewicz_eq_units_smul_cubicalHurewicz`); in degree one the sign is pinned
down by the computation of the fundamental cycle of the cube pair `(I¹, ∂I¹)`
(`TauCeti.singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle_zero`).

## Main results

* `GenLoop.singularCubicalHomologyIso_inv_cubicalHurewicz`: the comparison carries the cubical
  Hurewicz class of a loop to its Hurewicz class.
* `HomotopyGroup.singularCubicalHomologyIso_inv_cubicalHurewicz`,
  `HomotopyGroup.singularCubicalHomologyIso_inv_cubicalHurewiczHom`: the same for the Hurewicz maps
  and homomorphisms on `π₁(X, x)`.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapters II and VII.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology TauCeti
open scoped Topology.Homotopy

universe u

namespace GenLoop

variable (k : Type u) [Ring k] {X : Type u} [TopologicalSpace X] {x : X}

/-- **The degree-one cubical and singular Hurewicz classes agree**: over every ring `k`, the
cubical–simplicial comparison carries the cubical Hurewicz class of a loop `p : Ω^ (Fin 1) X x`,
the class of the `1`-cube `p`, to its Hurewicz class in simplicial singular homology. -/
theorem singularCubicalHomologyIso_inv_cubicalHurewicz (p : Ω^ (Fin 1) X x) :
    (singularCubicalHomologyIso k (TopCat.of X) 1).inv (cubicalHurewicz k p) =
      (hurewicz (ModuleCat.of k k) p).hom 1 := by
  -- The quotient map `H₁(X; k) ⟶ H₁(X, {x}; k)` is injective, and both classes are read there as
  -- the image under `p` of the generator of `H₁(I¹, ∂I¹; k)`, which in degree one is the class of
  -- the fundamental cycle of the cube pair.
  apply (ConcreteCategory.bijective_of_isIso
    (singularHomologyIsoOfSubsetSingleton (ModuleCat.of k k) 0 x).hom).1
  rw [← ModuleCat.comp_apply, hurewicz_comp_singularHomologyIsoOfSubsetSingleton_hom,
    ModuleCat.comp_apply, ← singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle_zero,
    singularHomologyIsoOfSubsetSingleton_hom]
  -- The general lemma is stated in degree `0 + 1`, so it closes the goal, stated in degree `1`, by
  -- `exact`.
  exact (singularHomologyMap_toCubeBoundaryPairHom_cubeBoundaryPairCycle k p).symm

end GenLoop

namespace HomotopyGroup

variable (k : Type u) [Ring k] {X : Type u} [TopologicalSpace X] {x : X}

/-- **The degree-one cubical and singular Hurewicz maps agree**: over every ring `k`, the
cubical–simplicial comparison carries the cubical Hurewicz class of `a ∈ π₁(X, x)` to its Hurewicz
class in simplicial singular homology. -/
theorem singularCubicalHomologyIso_inv_cubicalHurewicz (a : HomotopyGroup (Fin 1) X x) :
    (singularCubicalHomologyIso k (TopCat.of X) 1).inv (cubicalHurewicz k 0 a) =
      (hurewicz (ModuleCat.of k k) 0 a).hom 1 :=
  Quotient.inductionOn a fun p ↦ by
    rw [cubicalHurewicz_mk, hurewicz_mk]
    exact GenLoop.singularCubicalHomologyIso_inv_cubicalHurewicz k p

/-- **The degree-one cubical and singular Hurewicz homomorphisms agree**: over every ring `k`, the
cubical–simplicial comparison carries the cubical Hurewicz class of `a ∈ π₁(X, x)` to its Hurewicz
class in simplicial singular homology. -/
theorem singularCubicalHomologyIso_inv_cubicalHurewiczHom
    (a : Additive (HomotopyGroup (Fin 1) X x)) :
    (singularCubicalHomologyIso k (TopCat.of X) 1).inv (cubicalHurewiczHom k 0 a) =
      (hurewiczHom (ModuleCat.of k k) 0 a).hom 1 := by
  rw [cubicalHurewiczHom_apply, hurewiczHom_apply]
  exact singularCubicalHomologyIso_inv_cubicalHurewicz k a.toMul

end HomotopyGroup
