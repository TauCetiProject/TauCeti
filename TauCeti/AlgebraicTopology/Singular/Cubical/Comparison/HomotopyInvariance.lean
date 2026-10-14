/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Basic

/-!
# Homotopy invariance of cubical singular chains

Homotopic maps induce chain homotopic maps of normalized cubical chains
(`TopCat.Homotopy.normalizedCubicalChainComplexMap`), so a homotopy equivalence of spaces induces a
chain homotopy equivalence of normalized cubical chain complexes
(`ContinuousMap.HomotopyEquiv.normalizedCubicalChainComplexHomotopyEquiv`), in particular a
quasi-isomorphism.

As the design of the comparison prescribes, this is not proved again on cubes: it is transported
from the homotopy invariance of simplicial singular chains through the natural chain homotopy
equivalence `TauCeti.cubicalSingularHomotopyEquiv`.  If `f` and `g` are homotopic, then, writing
`φ` and `ψ` for the comparison maps,
`N(f) ≃ φ ψ N(f) = φ S(f) ψ ≃ φ S(g) ψ = φ ψ N(g) ≃ N(g)`.

## Main definitions

* `TopCat.Homotopy.normalizedCubicalChainComplexMap`: the chain homotopy between the maps of
  normalized cubical chains induced by homotopic maps.
* `ContinuousMap.HomotopyEquiv.normalizedCubicalChainComplexHomotopyEquiv`: the chain homotopy
  equivalence induced by a homotopy equivalence.

## Main results

* `TopCat.Homotopy.congr_homologyMap_normalizedCubicalChainComplex`: homotopic maps induce the same
  map on cubical homology.
* `ContinuousMap.HomotopyEquiv.quasiIso_normalizedCubicalChainComplex_map`: a homotopy
  equivalence induces a quasi-isomorphism of normalized cubical chains.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology TauCeti

universe u

variable {k : Type u} [Ring k]

namespace TopCat.Homotopy

variable {X Y : TopCat.{u}} {f g : X ⟶ Y}

/-- The comparison maps intertwine the maps of normalized cubical chains with those of simplicial
singular chains. -/
private theorem comp_normalizedCubicalChainComplex_map (f : X ⟶ Y) :
    ((cubicalToSingular k).app X ≫ (singularToCubical k).app X) ≫
        (normalizedCubicalChainComplex k).map f =
      (cubicalToSingular k).app X ≫ (singularChains k).map f ≫ (singularToCubical k).app Y := by
  rw [Category.assoc, ← (singularToCubical k).naturality]

/-- **Homotopic maps induce chain homotopic maps of normalized cubical chains.** -/
def normalizedCubicalChainComplexMap (H : TopCat.Homotopy f g) (k : Type u) [Ring k] :
    _root_.Homotopy ((normalizedCubicalChainComplex k).map f)
      ((normalizedCubicalChainComplex k).map g) :=
  (((cubicalToSingularCompHomotopy k X).compRightId _).symm.trans
    (_root_.Homotopy.ofEq (comp_normalizedCubicalChainComplex_map f))).trans
    ((((TopCat.Homotopy.singularChainComplexFunctorObjMap H (ModuleCat.of k k)).compRight
      ((singularToCubical k).app Y)).compLeft ((cubicalToSingular k).app X)).trans
      ((_root_.Homotopy.ofEq (comp_normalizedCubicalChainComplex_map g)).symm.trans
        ((cubicalToSingularCompHomotopy k X).compRightId _)))

/-- Homotopic maps induce the same map on cubical homology. -/
theorem congr_homologyMap_normalizedCubicalChainComplex (H : TopCat.Homotopy f g) (n : ℕ) :
    HomologicalComplex.homologyMap ((normalizedCubicalChainComplex k).map f) n =
      HomologicalComplex.homologyMap ((normalizedCubicalChainComplex k).map g) n :=
  (normalizedCubicalChainComplexMap H k).homologyMap_eq n

end TopCat.Homotopy

namespace ContinuousMap.HomotopyEquiv

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

variable (k) in
/-- **A homotopy equivalence induces a chain homotopy equivalence of normalized cubical
chains.** -/
def normalizedCubicalChainComplexHomotopyEquiv (e : X ≃ₕ Y) :
    _root_.HomotopyEquiv ((normalizedCubicalChainComplex k).obj (TopCat.of X))
      ((normalizedCubicalChainComplex k).obj (TopCat.of Y)) where
  hom := (normalizedCubicalChainComplex k).map (TopCat.ofHom e.toFun)
  inv := (normalizedCubicalChainComplex k).map (TopCat.ofHom e.invFun)
  homotopyHomInvId :=
    (_root_.Homotopy.ofEq ((normalizedCubicalChainComplex k).map_comp _ _).symm).trans
      ((TopCat.Homotopy.normalizedCubicalChainComplexMap (f := TopCat.ofHom e.toFun ≫
        TopCat.ofHom e.invFun) (g := 𝟙 _) e.left_inv.some k).trans
        (_root_.Homotopy.ofEq ((normalizedCubicalChainComplex k).map_id _)))
  homotopyInvHomId :=
    (_root_.Homotopy.ofEq ((normalizedCubicalChainComplex k).map_comp _ _).symm).trans
      ((TopCat.Homotopy.normalizedCubicalChainComplexMap (f := TopCat.ofHom e.invFun ≫
        TopCat.ofHom e.toFun) (g := 𝟙 _) e.right_inv.some k).trans
        (_root_.Homotopy.ofEq ((normalizedCubicalChainComplex k).map_id _)))

@[simp]
theorem normalizedCubicalChainComplexHomotopyEquiv_hom (e : X ≃ₕ Y) :
    (normalizedCubicalChainComplexHomotopyEquiv k e).hom =
      (normalizedCubicalChainComplex k).map (TopCat.ofHom e.toFun) :=
  (rfl)

@[simp]
theorem normalizedCubicalChainComplexHomotopyEquiv_inv (e : X ≃ₕ Y) :
    (normalizedCubicalChainComplexHomotopyEquiv k e).inv =
      (normalizedCubicalChainComplex k).map (TopCat.ofHom e.invFun) :=
  (rfl)

/-- **A homotopy equivalence induces a quasi-isomorphism of normalized cubical chains.** -/
theorem quasiIso_normalizedCubicalChainComplex_map (e : X ≃ₕ Y) :
    QuasiIso ((normalizedCubicalChainComplex k).map (TopCat.ofHom e.toFun)) :=
  inferInstanceAs (QuasiIso (normalizedCubicalChainComplexHomotopyEquiv k e).hom)

end ContinuousMap.HomotopyEquiv
