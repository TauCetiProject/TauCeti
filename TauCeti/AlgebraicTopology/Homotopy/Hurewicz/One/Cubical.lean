/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.One.Comparison
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.One.Naturality
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Cube.Pair

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

A third class is the one of Tau Ceti's degree-one Hurewicz isomorphism
`TauCeti.HurewiczOne.hurewiczHomologyAddEquiv : π₁(X, x)ᵃᵇ ≃+ H₁(X; ℤ)`, the class of the singular
`1`-simplex traced by the loop, which is minus the Hurewicz class
(`GenLoop.hurewicz_eq_neg_ιHomology₁`). Composing that isomorphism with the comparison gives its
cubical form `TauCeti.HurewiczOne.hurewiczCubicalHomologyAddEquiv : π₁(X, x)ᵃᵇ ≃+ H^□₁(X; ℤ)` for a
path-connected space, with no further sign or map. It sends the class of a loop to **minus** the
class of the same loop read as a `1`-cube: the cubical boundary of a `1`-cube `c` is
`c(0) - c(1)`, while the simplicial boundary of a `1`-simplex `σ` is `σ(1) - σ(0)`. It is natural in
based maps and independent of the base point, as the singular isomorphism is.

## Main results

* `GenLoop.singularCubicalHomologyIso_inv_cubicalHurewicz`: the comparison carries the cubical
  Hurewicz class of a loop to its Hurewicz class.
* `HomotopyGroup.singularCubicalHomologyIso_inv_cubicalHurewicz`,
  `HomotopyGroup.singularCubicalHomologyIso_inv_cubicalHurewiczHom`: the same for the Hurewicz maps
  and homomorphisms on `π₁(X, x)`.
* `TauCeti.HurewiczOne.hurewiczCubicalHomologyAddEquiv`: the degree-one Hurewicz isomorphism in
  cubical homology, and `TauCeti.HurewiczOne.hurewiczCubicalHomologyAddEquiv_ofMul_of_mk`, its value
  on a loop.
* `TauCeti.HurewiczOne.homologyMap_hurewiczCubicalHomologyAddEquiv_mapOfEq`,
  `TauCeti.HurewiczOne.hurewiczCubicalHomologyAddEquiv_fundamentalGroupMulEquivOfPath`: its
  naturality in based maps and its independence of the base point.
* `HomotopyGroup.cubicalHurewiczHom_zero_eq_neg_hurewiczCubicalHomologyAddEquiv`: the cubical
  Hurewicz homomorphism on `π₁(X, x)` is minus the cubical Hurewicz isomorphism.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapters II and VII.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 2A.1.
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

/-! ### The cubical form of the degree-one Hurewicz isomorphism -/

namespace TauCeti.HurewiczOne

variable {X : TopCat.{0}}

/-- **The degree-one Hurewicz isomorphism in cubical homology**: for a path-connected space `X`
with a base point `x`, the Hurewicz isomorphism `π₁(X, x)ᵃᵇ ≃+ H₁(X; ℤ)` followed by the
cubical–simplicial comparison `H₁(X; ℤ) ≅ H^□₁(X; ℤ)`. It sends the class of a loop to minus the
class of the same loop read as a `1`-cube (`hurewiczCubicalHomologyAddEquiv_ofMul_of_mk`). -/
def hurewiczCubicalHomologyAddEquiv [PathConnectedSpace X] (x : X) :
    Additive (Group.Abelianization (FundamentalGroup X x)) ≃+
      ((normalizedCubicalChainComplex ℤ).obj X).homology 1 :=
  (hurewiczHomologyAddEquiv x).trans (singularCubicalHomologyIso ℤ X 1).toLinearEquiv.toAddEquiv

/-- The cubical Hurewicz isomorphism is the singular one followed by the cubical–simplicial
comparison. -/
theorem hurewiczCubicalHomologyAddEquiv_apply [PathConnectedSpace X] {x : X}
    (a : Additive (Group.Abelianization (FundamentalGroup X x))) :
    hurewiczCubicalHomologyAddEquiv x a =
      (singularCubicalHomologyIso ℤ X 1).hom (hurewiczHomologyAddEquiv x a) := by
  rw [hurewiczCubicalHomologyAddEquiv, AddEquiv.trans_apply]
  rfl

/-- **The cubical Hurewicz isomorphism on a loop**: the class of a loop `γ` goes to minus the
cubical class of `γ` read as a `1`-cube. The sign comes from the two boundary conventions: the
cubical boundary of a `1`-cube `c` is `c(0) - c(1)`, while the simplicial boundary of a
`1`-simplex `σ` is `σ(1) - σ(0)`. -/
@[simp]
theorem hurewiczCubicalHomologyAddEquiv_ofMul_of_mk [PathConnectedSpace X] {x : X}
    (γ : Path x x) :
    hurewiczCubicalHomologyAddEquiv x (Additive.ofMul ((Group.Abelianization.of :
      FundamentalGroup X x →* _) (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)))) =
      -GenLoop.cubicalHurewicz ℤ ((genLoopEquivOfUnique (Fin 1)).symm γ) := by
  set p := (genLoopEquivOfUnique (Fin 1)).symm γ
  -- The comparison carries the cubical class of `p` to minus the singular class of `γ`.
  have h : (singularCubicalHomologyIso ℤ X 1).inv (GenLoop.cubicalHurewicz ℤ p) =
      -H₁AddEquivHomology X (loopClass γ) := by
    have := (GenLoop.singularCubicalHomologyIso_inv_cubicalHurewicz ℤ p).trans
      (GenLoop.hurewicz_hom_one_eq_neg_loopClass p)
    rwa [Equiv.apply_symm_apply] at this
  rw [hurewiczCubicalHomologyAddEquiv_apply, hurewiczHomologyAddEquiv_ofMul_of_mk,
    ← neg_neg (H₁AddEquivHomology X (loopClass γ)), ← h, map_neg, Iso.inv_hom_id_apply]

/-- The inverse of the cubical Hurewicz isomorphism sends the cubical class of a loop read as a
`1`-cube to minus the class of the loop. -/
theorem hurewiczCubicalHomologyAddEquiv_symm_cubicalHurewicz [PathConnectedSpace X] {x : X}
    (p : Ω^ (Fin 1) X x) :
    (hurewiczCubicalHomologyAddEquiv x).symm (GenLoop.cubicalHurewicz ℤ p) =
      -Additive.ofMul ((Group.Abelianization.of : FundamentalGroup X x →* _)
        (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (genLoopEquivOfUnique (Fin 1) p)))) := by
  rw [AddEquiv.symm_apply_eq, map_neg, hurewiczCubicalHomologyAddEquiv_ofMul_of_mk,
    Equiv.symm_apply_apply, neg_neg]

variable {Y : TopCat.{0}} (f : X ⟶ Y)

/-- **Naturality of the cubical Hurewicz isomorphism** in based maps: for a continuous map
carrying the base point `x` to a prescribed base point `y` of the target. -/
theorem homologyMap_hurewiczCubicalHomologyAddEquiv_mapOfEq [PathConnectedSpace X]
    [PathConnectedSpace Y] {x : X} {y : Y} (h : f x = y)
    (a : Additive (Group.Abelianization (FundamentalGroup X x))) :
    (HomologicalComplex.homologyMap ((normalizedCubicalChainComplex ℤ).map f) 1).hom
        (hurewiczCubicalHomologyAddEquiv x a) =
      hurewiczCubicalHomologyAddEquiv y (Additive.ofMul (Group.Abelianization.map
        (FundamentalGroup.mapOfEq f.hom h) a.toMul)) := by
  rw [hurewiczCubicalHomologyAddEquiv_apply, hurewiczCubicalHomologyAddEquiv_apply,
    ← homologyMap_hurewiczHomologyAddEquiv_mapOfEq f h, ← ModuleCat.comp_apply,
    ← ModuleCat.comp_apply, singularCubicalHomologyIso_hom_naturality]

/-- **Naturality of the cubical Hurewicz isomorphism** of path-connected spaces. -/
theorem homologyMap_hurewiczCubicalHomologyAddEquiv [PathConnectedSpace X]
    [PathConnectedSpace Y] {x : X} (a : Additive (Group.Abelianization (FundamentalGroup X x))) :
    (HomologicalComplex.homologyMap ((normalizedCubicalChainComplex ℤ).map f) 1).hom
        (hurewiczCubicalHomologyAddEquiv x a) =
      hurewiczCubicalHomologyAddEquiv (f x) (Additive.ofMul (Group.Abelianization.map
        (FundamentalGroup.map f.hom x) a.toMul)) := by
  rw [hurewiczCubicalHomologyAddEquiv_apply, hurewiczCubicalHomologyAddEquiv_apply,
    ← homologyMap_hurewiczHomologyAddEquiv f, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
    singularCubicalHomologyIso_hom_naturality]

/-- **Independence of the base point**: changing the base point along a path does not change the
cubical homology class supplied by the cubical Hurewicz isomorphism. -/
theorem hurewiczCubicalHomologyAddEquiv_fundamentalGroupMulEquivOfPath [PathConnectedSpace X]
    {x x' : X} (p : Path x x') (a : FundamentalGroup X x) :
    hurewiczCubicalHomologyAddEquiv x' (Additive.ofMul (Group.Abelianization.of
      (FundamentalGroup.fundamentalGroupMulEquivOfPath p a))) =
      hurewiczCubicalHomologyAddEquiv x (Additive.ofMul (Group.Abelianization.of a)) := by
  rw [hurewiczCubicalHomologyAddEquiv_apply, hurewiczCubicalHomologyAddEquiv_apply,
    hurewiczHomologyAddEquiv_fundamentalGroupMulEquivOfPath]

end TauCeti.HurewiczOne

namespace HomotopyGroup

open TauCeti.HurewiczOne

variable {X : Type} [TopologicalSpace X] [PathConnectedSpace X] {x : X}

/-- **The cubical Hurewicz map in degree one is minus the cubical Hurewicz isomorphism**: on
`π₁(X, x)`, the cubical Hurewicz homomorphism `HomotopyGroup.cubicalHurewiczHom` with integer
coefficients, sending a loop to the class of the `1`-cube it is, is minus
`TauCeti.HurewiczOne.hurewiczCubicalHomologyAddEquiv` on the abelianization. -/
theorem cubicalHurewiczHom_zero_eq_neg_hurewiczCubicalHomologyAddEquiv
    (a : Additive (HomotopyGroup (Fin 1) X x)) :
    cubicalHurewiczHom ℤ 0 a =
      -hurewiczCubicalHomologyAddEquiv (X := TopCat.of X) x (Additive.ofMul (Group.Abelianization.of
        (homotopyGroupOfUniqueMulEquivFundamentalGroup (Fin 1) a.toMul))) := by
  rw [hurewiczCubicalHomologyAddEquiv_apply, ← map_neg,
    ← hurewiczHom_hom_one_eq_neg_hurewiczHomologyAddEquiv,
    ← singularCubicalHomologyIso_inv_cubicalHurewiczHom, Iso.inv_hom_id_apply]

end HomotopyGroup
