/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Cubical.Relative
public import TauCeti.AlgebraicTopology.Singular.Circle
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

For the circle `S¹`, oriented by the standard loop `t ↦ (cos 2πt, sin 2πt)`, the comparison sends
the cubical class of the standard loop to minus the fundamental class
`TauCeti.circleFundamentalClass`
(`TauCeti.singularCubicalHomologyIso_inv_cubicalHurewicz_circleGenLoop`). The sign comes from the
two boundary conventions: the cubical boundary of a `1`-cube `c` is `c(0) - c(1)`, while the
simplicial boundary of a `1`-simplex `σ` is `σ(1) - σ(0)`, and the fundamental class of the circle
is the class of the standard loop read as a singular simplex.

## Main results

* `GenLoop.singularCubicalHomologyIso_inv_cubicalHurewicz`: the comparison carries the cubical
  Hurewicz class of a loop to its Hurewicz class.
* `HomotopyGroup.singularCubicalHomologyIso_inv_cubicalHurewiczHom`: the same for the
  Hurewicz homomorphisms on `π₁(X, x)`.
* `TauCeti.singularCubicalHomologyIso_inv_cubicalHurewicz_circleGenLoop`: the cubical class of the
  standard loop of the circle is minus its fundamental class.

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
  let P := TopPair.ofSubset ({x} : Set (TopCat.of X))
  -- Read in the relative homology of `(X, {x})`, the comparison of absolute classes is the relative
  -- comparison of their images.
  have hπ : (singularCubicalHomologyIso k (TopCat.of X) 1).inv ≫
      (singularHomologyIsoOfSubsetSingleton (ModuleCat.of k k) 0 x).hom =
        HomologicalComplex.homologyMap
            (cokernel.π ((normalizedCubicalChainComplex k).map P.map)) 1 ≫
          (TopPair.singularCubicalHomologyIso k P 1).inv := by
    rw [singularHomologyIsoOfSubsetSingleton_hom]
    exact (TopPair.homologyMap_π_comp_singularCubicalHomologyIso_inv k P 1).symm
  -- In relative homology, the cubical class of `p` is the image of the fundamental cycle of the
  -- cube pair, whose comparison is the generator of `H₁(I¹, ∂I¹; k)`.
  have hrel : (TopPair.singularCubicalHomologyIso k P 1).inv
      (HomologicalComplex.homologyMap
        (cokernel.π ((normalizedCubicalChainComplex k).map P.map)) 1 (cubicalHurewicz k p)) =
        TopPair.singularHomologyMap (toCubeBoundaryPairHom p) (ModuleCat.of k k) 1
          ((singularHomologyCubeBoundaryPairIso (ModuleCat.of k k) 1).inv 1) := by
    let c : C(Fin 1 → unitInterval, P.fst) := p.1
    have hb := homologyMap_cubeBoundaryPairHom_cubeBoundaryPairCycle k (P := P) (m := 0) c
      (mapsTo_boundary_range_ofSubset p)
    have hc := ConcreteCategory.congr_hom (TopPair.singularCubicalHomologyIso_inv_naturality k
      (cubeBoundaryPairHom c (mapsTo_boundary_range_ofSubset p)) 1)
        (((cubeBoundaryPair.{u} 1).cubicalChainComplex k).homologyπ 1 (cubeBoundaryPairCycle k 0))
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hb,
      singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle_zero] at hc
    rw [homologyMap_π_cubicalHurewicz, toCubeBoundaryPairHom_eq_cubeBoundaryPairHom]
    exact hc
  -- The quotient map `H₁(X; k) ⟶ H₁(X, {x}; k)` is injective.
  apply (ConcreteCategory.bijective_of_isIso
    (singularHomologyIsoOfSubsetSingleton (ModuleCat.of k k) 0 x).hom).1
  exact (ConcreteCategory.congr_hom hπ (cubicalHurewicz k p)).trans (hrel.trans
    (ConcreteCategory.congr_hom
      (hurewicz_comp_singularHomologyIsoOfSubsetSingleton_hom (ModuleCat.of k k) p) 1).symm)

end GenLoop

namespace HomotopyGroup

variable (k : Type u) [Ring k] {X : Type u} [TopologicalSpace X] {x : X}

/-- **The degree-one cubical and singular Hurewicz homomorphisms agree**: over every ring `k`, the
cubical–simplicial comparison carries the cubical Hurewicz class of `a ∈ π₁(X, x)` to its Hurewicz
class in simplicial singular homology. -/
theorem singularCubicalHomologyIso_inv_cubicalHurewiczHom
    (a : Additive (HomotopyGroup (Fin 1) X x)) :
    (singularCubicalHomologyIso k (TopCat.of X) 1).inv (cubicalHurewiczHom k 0 a) =
      (hurewiczHom (ModuleCat.of k k) 0 a).hom 1 := by
  obtain ⟨p, hp⟩ : ∃ p : Ω^ (Fin 1) X x, (⟦p⟧ : HomotopyGroup (Fin 1) X x) = a.toMul :=
    Quotient.exists_rep _
  rw [cubicalHurewiczHom_apply, hurewiczHom_apply, ← hp, cubicalHurewicz_mk, hurewicz_mk]
  exact GenLoop.singularCubicalHomologyIso_inv_cubicalHurewicz k p

end HomotopyGroup

namespace TauCeti

variable (k : Type) [Ring k]

/-- **The cubical class of the standard loop of the circle is minus its fundamental class**: over
every ring `k`, the cubical–simplicial comparison carries the class of the `1`-cube
`t ↦ (cos 2πt, sin 2πt)` in normalized cubical homology to `-[S¹]`, the negative of
`TauCeti.circleFundamentalClass`. -/
theorem singularCubicalHomologyIso_inv_cubicalHurewicz_circleGenLoop :
    (singularCubicalHomologyIso k (TopCat.of Sphere1) 1).inv
        (GenLoop.cubicalHurewicz k circleGenLoop) =
      -(circleFundamentalClass (ModuleCat.of k k)).hom 1 := by
  rw [GenLoop.singularCubicalHomologyIso_inv_cubicalHurewicz, hurewicz_circleGenLoop,
    ModuleCat.hom_neg, LinearMap.neg_apply]

end TauCeti
