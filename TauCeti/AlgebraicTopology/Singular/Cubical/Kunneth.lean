/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Homology.Kunneth.Sequence
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.CrossProduct
public import TauCeti.AlgebraicTopology.Singular.Kunneth.Basic

/-!
# The cubical Eilenberg–Zilber theorem and the Künneth theorem for cubical homology

The cubical cross product `TauCeti.cubicalCrossProduct`, `N(X; k) ⊗ N(Y; k) ⟶ N(X × Y; k)`, is a
quasi-isomorphism (`TauCeti.quasiIso_cubicalCrossProduct`).  After the comparison with simplicial
chains it is naturally chain homotopic to the tensor product of the two comparison maps followed
by the simplicial cross product (`TauCeti.cubicalSingularCrossProductHomotopy`), which is a
quasi-isomorphism since the shuffle map is a homotopy equivalence (Eilenberg–Zilber) and the
comparison maps are homotopy equivalences.

The Künneth map of the cubical chain complexes, `⨁_{p + q = n} Hₚ(X; k) ⊗ H_q(Y; k) ⟶ Hₙ(X × Y; k)`
with the cubical homology modules, is the algebraic Künneth map followed by the map induced by the
cross product (`TauCeti.cubicalHomologyKunneth`).  The Künneth theorem for it is the algebraic
Künneth theorem for the chain complexes `N(X; k)` and `N(Y; k)`, transported along the cross
product: when the cycles split off and the homology splits off the cycles, for instance over a
semisimple ring, it is an isomorphism, and over a principal ideal domain the Künneth sequence is
exact.  The normalized cubical chains are projective, being a retract of the free module on the
cubes (an instance in `Cubical/Normalization.lean`).

## Main definitions and results

* `TauCeti.quasiIso_cubicalCrossProduct`: the cubical cross product is a quasi-isomorphism.
* `TauCeti.cubicalHomologyKunneth`: the Künneth map of cubical homology.
* `TauCeti.isIso_cubicalHomologyKunneth`: the Künneth theorem for cubical homology.
* `TauCeti.cubicalHomologyKunnethShortComplex_shortExact`: the Künneth sequence over a principal
  ideal domain.
* `TauCeti.tensorHom_comp_singularHomologyKunneth`: the cubical Künneth map corresponds to the
  singular Künneth map (`TopCat.singularHomologyKunneth`) under the comparison isomorphism.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory HomologicalComplex Limits

universe u

namespace TauCeti

variable (k : Type u) [CommRing k]

/-- The tensor product of the two comparison maps is a quasi-isomorphism: they are homotopy
equivalences, and the tensor product preserves homotopy equivalences. -/
instance quasiIso_tensorHom_cubicalToSingular (X Y : TopCat.{u}) :
    QuasiIso ((cubicalToSingular k).app X ⊗ₘ (cubicalToSingular k).app Y) := by
  have hX : (cubicalSingularHomotopyEquiv k X).symm.hom = (cubicalToSingular k).app X :=
    cubicalSingularHomotopyEquiv_inv k X
  have hY : (cubicalSingularHomotopyEquiv k Y).symm.hom = (cubicalToSingular k).app Y :=
    cubicalSingularHomotopyEquiv_inv k Y
  have e := HomotopyEquiv.mapBifunctor_hom (F := curriedTensor (ModuleCat.{u} k))
    (c := ComplexShape.down ℕ) (cubicalSingularHomotopyEquiv k X).symm
    (cubicalSingularHomotopyEquiv k Y).symm
  rw [hX, hY] at e
  have : QuasiIso (HomotopyEquiv.mapBifunctor (curriedTensor (ModuleCat.{u} k))
      (ComplexShape.down ℕ) (cubicalSingularHomotopyEquiv k X).symm
      (cubicalSingularHomotopyEquiv k Y).symm).hom := inferInstance
  rw [e] at this
  rw [HomologicalComplex.tensorHom_eq_mapBifunctorMap]
  exact this

/-- The cubical cross product followed by the comparison map is a quasi-isomorphism: it is
homotopic to the tensor product of the two comparison maps followed by the simplicial cross
product. -/
instance quasiIso_cubicalCrossProductToSingularApp (X Y : TopCat.{u}) :
    QuasiIso (cubicalCrossProductToSingularApp k X Y) := by
  have : QuasiIso (singularCrossProductOfCubicalApp k X Y) := by
    rw [singularCrossProductOfCubicalApp_def]
    infer_instance
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap,
    (cubicalSingularCrossProductHomotopy k X Y).homologyMap_eq n,
    ← quasiIsoAt_iff_isIso_homologyMap]
  infer_instance

/-- **The cubical Eilenberg–Zilber theorem**: the cross product of normalized cubical chains
`N(X; k) ⊗ N(Y; k) ⟶ N(X × Y; k)` is a quasi-isomorphism. -/
instance quasiIso_cubicalCrossProduct (X Y : TopCat.{u}) :
    QuasiIso (cubicalCrossProduct k X Y) :=
  have : QuasiIso (cubicalCrossProduct k X Y ≫ (cubicalToSingular k).app (X ⊗ Y)) := by
    rw [← cubicalCrossProductToSingularApp_def]
    infer_instance
  quasiIso_of_comp_right (cubicalCrossProduct k X Y) ((cubicalToSingular k).app (X ⊗ Y))

variable (X Y : TopCat.{u})

/-- **The Künneth map of cubical homology**,
`⨁_{p + q = n} Hₚ(X; k) ⊗ H_q(Y; k) ⟶ Hₙ(X × Y; k)`, with the homology of the normalized cubical
chains: the algebraic Künneth map of the chain complexes `N(X; k)` and `N(Y; k)` followed by the
map induced by the cubical cross product. -/
def cubicalHomologyKunneth (n : ℕ) :
    GradedObject.Monoidal.tensorObj
        (fun p ↦ ((normalizedCubicalChainComplex k).obj X).homology p)
        (fun q ↦ ((normalizedCubicalChainComplex k).obj Y).homology q) n ⟶
      ((normalizedCubicalChainComplex k).obj (X ⊗ Y)).homology n :=
  homologyKunneth ((normalizedCubicalChainComplex k).obj X)
      ((normalizedCubicalChainComplex k).obj Y) n ≫
    homologyMap (cubicalCrossProduct k X Y) n

/-- The cubical Künneth map is the algebraic Künneth map of the chain complexes followed by the
map induced by the cubical cross product. -/
theorem cubicalHomologyKunneth_def (n : ℕ) :
    cubicalHomologyKunneth k X Y n =
      homologyKunneth ((normalizedCubicalChainComplex k).obj X)
          ((normalizedCubicalChainComplex k).obj Y) n ≫
        homologyMap (cubicalCrossProduct k X Y) n :=
  (rfl)

/-- The cubical Künneth map restricts to the homology cross product followed by the map induced by
the cubical cross product on each summand. -/
@[reassoc (attr := simp)]
theorem ι_cubicalHomologyKunneth (p q n : ℕ) (h : p + q = n) :
    GradedObject.Monoidal.ιTensorObj
        (fun p ↦ ((normalizedCubicalChainComplex k).obj X).homology p)
        (fun q ↦ ((normalizedCubicalChainComplex k).obj Y).homology q) p q n h ≫
      cubicalHomologyKunneth k X Y n =
      homologyCross ((normalizedCubicalChainComplex k).obj X)
          ((normalizedCubicalChainComplex k).obj Y) p q n h ≫
        homologyMap (cubicalCrossProduct k X Y) n := by
  rw [cubicalHomologyKunneth_def, ← Category.assoc, ι_homologyKunneth]

/-- **Naturality of the cubical Künneth map** in both spaces. -/
@[reassoc]
theorem cubicalHomologyKunneth_naturality {X X' Y Y' : TopCat.{u}} (f : X ⟶ X') (g : Y ⟶ Y')
    (n : ℕ) :
    GradedObject.Monoidal.tensorHom
        (fun p ↦ homologyMap ((normalizedCubicalChainComplex k).map f) p)
        (fun q ↦ homologyMap ((normalizedCubicalChainComplex k).map g) q) n ≫
      cubicalHomologyKunneth k X' Y' n =
      cubicalHomologyKunneth k X Y n ≫
        homologyMap ((normalizedCubicalChainComplex k).map (f ⊗ₘ g)) n := by
  rw [cubicalHomologyKunneth_def, cubicalHomologyKunneth_def, ← Category.assoc,
    homologyKunneth_naturality, Category.assoc, ← homologyMap_comp, Category.assoc,
    ← homologyMap_comp, ← cubicalCrossProduct_naturality,
    HomologicalComplex.tensorHom_eq_mapBifunctorMap]

/-- The cubical cross product induces an isomorphism on homology. -/
instance isIso_homologyMap_cubicalCrossProduct (n : ℕ) :
    IsIso (homologyMap (cubicalCrossProduct k X Y) n) :=
  (quasiIsoAt_iff_isIso_homologyMap _ _).1 inferInstance

/-- **The Künneth theorem for cubical homology**: if the cycles of the normalized cubical chain
complexes split off their terms and their homology splits off the cycles, the Künneth map
`⨁_{p + q = n} Hₚ(X; k) ⊗ H_q(Y; k) ⟶ Hₙ(X × Y; k)` is an isomorphism.  This is the Künneth
theorem for the chain complexes `N(X; k)` and `N(Y; k)`, transported along the cubical
Eilenberg–Zilber quasi-isomorphism. -/
theorem isIso_cubicalHomologyKunneth
    [∀ p, IsSplitMono (((normalizedCubicalChainComplex k).obj X).iCycles p)]
    [∀ p, IsSplitEpi (((normalizedCubicalChainComplex k).obj X).homologyπ p)]
    [∀ q, IsSplitMono (((normalizedCubicalChainComplex k).obj Y).iCycles q)]
    [∀ q, IsSplitEpi (((normalizedCubicalChainComplex k).obj Y).homologyπ q)] (n : ℕ) :
    IsIso (cubicalHomologyKunneth k X Y n) := by
  have := isIso_homologyKunneth_of_isSplitMono_of_isSplitEpi
    ((normalizedCubicalChainComplex k).obj X) ((normalizedCubicalChainComplex k).obj Y) n
  rw [cubicalHomologyKunneth_def]
  infer_instance

/-- **The Künneth theorem for cubical homology over a semisimple ring**, for instance a field:
`⨁_{p + q = n} Hₚ(X; k) ⊗ H_q(Y; k) ≅ Hₙ(X × Y; k)` for the homology of the normalized cubical
chains. -/
instance isIso_cubicalHomologyKunneth_of_isSemisimpleRing [IsSemisimpleRing k] (n : ℕ) :
    IsIso (cubicalHomologyKunneth k X Y n) :=
  isIso_cubicalHomologyKunneth k X Y n

/-- **The Künneth theorem for cubical homology with projective homology**: over a principal ideal
domain `k`, if the cubical homology modules of `X` and `Y` are projective, for instance free, the
Künneth map is an isomorphism.  The cycles split off the normalized cubical chains, since these
are projective. -/
theorem isIso_cubicalHomologyKunneth_of_projective [NoZeroDivisors k] [IsPrincipalIdealRing k]
    [∀ p, CategoryTheory.Projective (((normalizedCubicalChainComplex k).obj X).homology p)]
    [∀ q, CategoryTheory.Projective (((normalizedCubicalChainComplex k).obj Y).homology q)]
    (n : ℕ) : IsIso (cubicalHomologyKunneth k X Y n) :=
  isIso_cubicalHomologyKunneth k X Y n

/-- **The cubical Künneth map is the simplicial one under the comparison**: the tensor product of
the comparison isomorphisms on homology, followed by the algebraic Künneth map of the singular
chain complexes and the map induced by the simplicial cross product, is the cubical Künneth map
followed by the comparison isomorphism of the product.  Equivalently, the cubical cross product
corresponds to the homology cross product of singular homology. -/
theorem tensorHom_comp_homologyKunneth_comp_homologyMap_singularCrossProduct (n : ℕ) :
    GradedObject.Monoidal.tensorHom (fun p ↦ homologyMap ((cubicalToSingular k).app X) p)
        (fun q ↦ homologyMap ((cubicalToSingular k).app Y) q) n ≫
      homologyKunneth ((singularChains k).obj X) ((singularChains k).obj Y) n ≫
        homologyMap (singularCrossProduct k X Y) n =
      cubicalHomologyKunneth k X Y n ≫ homologyMap ((cubicalToSingular k).app (X ⊗ Y)) n := by
  rw [← Category.assoc, homologyKunneth_naturality, Category.assoc, ← homologyMap_comp,
    cubicalHomologyKunneth_def, Category.assoc, ← homologyMap_comp,
    ← cubicalCrossProductToSingularApp_def,
    homologyMap_cubicalCrossProductToSingularApp_eq_singularCrossProductOfCubicalApp,
    singularCrossProductOfCubicalApp_def, HomologicalComplex.tensorHom_eq_mapBifunctorMap]

/-- The same statement for the Künneth map of singular homology with coefficients in the ring
(`TopCat.singularHomologyKunneth`, followed by the unitor `k ⊗ k ≅ k`). -/
theorem tensorHom_comp_singularHomologyKunneth (n : ℕ) :
    GradedObject.Monoidal.tensorHom (fun p ↦ homologyMap ((cubicalToSingular k).app X) p)
        (fun q ↦ homologyMap ((cubicalToSingular k).app Y) q) n ≫
      (TopCat.singularHomologyKunneth X Y (𝟙_ (ModuleCat.{u} k)) (𝟙_ (ModuleCat.{u} k)) n ≫
        ((AlgebraicTopology.singularHomologyFunctor _ n).map
          (λ_ (𝟙_ (ModuleCat.{u} k))).hom).app (X ⊗ Y)) =
      cubicalHomologyKunneth k X Y n ≫ homologyMap ((cubicalToSingular k).app (X ⊗ Y)) n := by
  have h := tensorHom_comp_homologyKunneth_comp_homologyMap_singularCrossProduct k X Y n
  have e := homologyMap_comp (TopCat.shuffle X Y (𝟙_ (ModuleCat.{u} k)) (𝟙_ (ModuleCat.{u} k)))
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).map
      (λ_ (𝟙_ (ModuleCat.{u} k))).hom).app (X ⊗ Y)) n
  have h2 : homologyMap (singularCrossProduct k X Y) n =
      homologyMap (TopCat.shuffle X Y (𝟙_ (ModuleCat.{u} k)) (𝟙_ (ModuleCat.{u} k))) n ≫
        homologyMap (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).map
          (λ_ (𝟙_ (ModuleCat.{u} k))).hom).app (X ⊗ Y)) n := by
    rw [singularCrossProduct_def]
    exact e
  rw [h2] at h
  rw [TopCat.singularHomologyKunneth_def]
  exact (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans h

variable [NoZeroDivisors k] [IsPrincipalIdealRing k]

/-- The map `Hₘ₊₁(X × Y; k) ⟶ ⨁_{p + q = m} Tor₁(Hₚ(X; k), H_q(Y; k))` of the cubical Künneth
sequence: the inverse of the isomorphism induced by the cross product followed by the map to `Tor₁`
of the algebraic Künneth sequence. -/
def cubicalHomologyToTor (m : ℕ) :
    ((normalizedCubicalChainComplex k).obj (X ⊗ Y)).homology (m + 1) ⟶
      homologyTor ((normalizedCubicalChainComplex k).obj X)
        ((normalizedCubicalChainComplex k).obj Y) m :=
  inv (homologyMap (cubicalCrossProduct k X Y) (m + 1)) ≫
    homologyToTor ((normalizedCubicalChainComplex k).obj X)
      ((normalizedCubicalChainComplex k).obj Y) m

/-- The map `cubicalHomologyToTor` is the inverse of the isomorphism induced by the cross product
followed by the map to `Tor₁` of the algebraic Künneth sequence. -/
theorem cubicalHomologyToTor_def (m : ℕ) :
    cubicalHomologyToTor k X Y m =
      inv (homologyMap (cubicalCrossProduct k X Y) (m + 1)) ≫
        homologyToTor ((normalizedCubicalChainComplex k).obj X)
          ((normalizedCubicalChainComplex k).obj Y) m :=
  (rfl)

/-- The map induced by the cross product followed by the cubical map to `Tor₁` is the map to
`Tor₁` of the algebraic Künneth sequence. -/
@[reassoc (attr := simp)]
theorem homologyMap_cubicalCrossProduct_comp_cubicalHomologyToTor (m : ℕ) :
    homologyMap (cubicalCrossProduct k X Y) (m + 1) ≫ cubicalHomologyToTor k X Y m =
      homologyToTor ((normalizedCubicalChainComplex k).obj X)
        ((normalizedCubicalChainComplex k).obj Y) m := by
  rw [cubicalHomologyToTor_def, IsIso.hom_inv_id_assoc]

/-- The cubical Künneth map followed by the map to `Tor₁` vanishes. -/
@[reassoc (attr := simp)]
theorem cubicalHomologyKunneth_comp_cubicalHomologyToTor (m : ℕ) :
    cubicalHomologyKunneth k X Y (m + 1) ≫ cubicalHomologyToTor k X Y m = 0 := by
  rw [cubicalHomologyToTor_def, cubicalHomologyKunneth_def, Category.assoc,
    IsIso.hom_inv_id_assoc]
  exact homologyKunneth_comp_homologyToTor _ _ m

/-- The Künneth short complex of cubical homology,
`⨁_{p + q = m + 1} Hₚ(X; k) ⊗ H_q(Y; k) ⟶ Hₘ₊₁(X × Y; k) ⟶ ⨁_{p + q = m} Tor₁(Hₚ(X; k), H_q(Y; k))`,
formed by the cubical Künneth map and the map to `Tor₁` of the algebraic Künneth sequence, through
the isomorphism induced on homology by the cross product. -/
abbrev cubicalHomologyKunnethShortComplex (m : ℕ) : ShortComplex (ModuleCat.{u} k) :=
  ShortComplex.mk (cubicalHomologyKunneth k X Y (m + 1)) (cubicalHomologyToTor k X Y m)
    (cubicalHomologyKunneth_comp_cubicalHomologyToTor k X Y m)

/-- **The Künneth short exact sequence for cubical homology over a principal ideal domain**:

`0 ⟶ ⨁_{p + q = m + 1} Hₚ(X; k) ⊗ H_q(Y; k) ⟶ Hₘ₊₁(X × Y; k)`
`  ⟶ ⨁_{p + q = m} Tor₁(Hₚ(X; k), H_q(Y; k)) ⟶ 0`

is exact, for the homology of the normalized cubical chains. -/
theorem cubicalHomologyKunnethShortComplex_shortExact (m : ℕ) :
    (cubicalHomologyKunnethShortComplex k X Y m).ShortExact :=
  by
  refine ShortComplex.shortExact_of_iso ?_
    (homologyKunnethShortComplex_shortExact ((normalizedCubicalChainComplex k).obj X)
      ((normalizedCubicalChainComplex k).obj Y) m)
  exact ShortComplex.isoMk (Iso.refl _)
    (asIso (homologyMap (cubicalCrossProduct k X Y) (m + 1))) (Iso.refl _)
    (Category.id_comp _).symm (IsIso.hom_inv_id_assoc _ _)

end TauCeti

end

end
