/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import TauCeti.AlgebraicTopology.Singular.Cubical.LocalCoefficients.ChainComplex
public import TauCeti.Algebra.Homology.HomologicalComplex.Basic

/-!
# Zeroth cubical homology with local coefficients

The zeroth homology of the normalized cubical chains with coefficients in a local system `L` is
the colimit of `L` over the fundamental groupoid.  Its generators are the classes of the fibres at
points, and its relations identify a coefficient with its parallel transport along a path: a path
is a cubical `1`-chain whose boundary is the difference of the two end points, one of them with
the transported coefficient.  The identification is induced by the augmentation of `0`-chains into
the colimit.  The argument follows the one for singular chains with local coefficients in
`TauCeti.AlgebraicTopology.Singular.Twisted.Zero` (`twistedHomology₀IsoColimit`), with the
cubical `1`-chain of a path in place of the singular `1`-simplex, and the cubical augmentation in
place of the simplicial one.

## Main definitions

* `TauCeti.LocalCoefficientSystem.ιNormalizedTwistedCubicalHomology₀ L x`: the class in zeroth
  homology of a coefficient in the fibre at `x`.
* `TauCeti.LocalCoefficientSystem.normalizedTwistedCubicalHomology₀Cocone L`: the cocone of
  these classes, and
  `TauCeti.LocalCoefficientSystem.isColimitNormalizedTwistedCubicalHomology₀Cocone` the proof
  that it is a colimit.
* `TauCeti.LocalCoefficientSystem.normalizedTwistedCubicalHomology₀IsoColimit L`: the
  identification of zeroth homology with `colimit L`.

## Main statements

* `TauCeti.LocalCoefficientSystem.map_ιNormalizedTwistedCubicalHomology₀`: parallel transport
  does not change the class of a coefficient.
* `TauCeti.LocalCoefficientSystem.pOpcycles_comp_normalizedTwistedCubicalHomology₀IsoColimit_hom`:
  the identification is induced by the augmentation of `0`-chains into the colimit.
* `TauCeti.LocalCoefficientSystem.normalizedTwistedCubicalHomology₀IsoColimit_hom_naturality`:
  naturality in the local system.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
* A. Hatcher, *Algebraic Topology*, Section 3.H.
* `TauCeti/AlgebraicTopology/Singular/Twisted/Zero.lean`: the colimit description of zeroth
  singular homology with local coefficients, whose proof this file adapts.
-/

public section

noncomputable section

open CategoryTheory Limits unitInterval

universe u v w

namespace TauCeti.LocalCoefficientSystem

open NormalizedTwistedCubicalChain

variable {R : Type u} [Ring R] {X : TopCat.{v}}
  (L : LocalCoefficientSystem.{u, v, max v w} R X)

/-- The `0`-chain of a `0`-cube with a coefficient, as a morphism into the degree-zero term. -/
private def ofCubeHom (c : SingularCube X 0) :
    L.obj (FundamentalGroupoid.mk (c 0)) ⟶ L.normalizedTwistedCubicalChainComplex.X 0 :=
  ModuleCat.ofHom (ofCube L c)

/-- The class in zeroth homology of a coefficient at a `0`-cube. -/
private def ιCube (c : SingularCube X 0) :
    L.obj (FundamentalGroupoid.mk (c 0)) ⟶ L.normalizedTwistedCubicalChainComplex.homology 0 :=
  ofCubeHom L c ≫ L.normalizedTwistedCubicalChainComplex.pOpcycles 0 ≫
    L.normalizedTwistedCubicalChainComplex.isoHomologyι₀.inv

/-- The class in zeroth homology of a coefficient in the fibre at `x`. -/
def ιNormalizedTwistedCubicalHomology₀ (x : X) :
    L.obj (FundamentalGroupoid.mk x) ⟶ L.normalizedTwistedCubicalChainComplex.homology 0 :=
  -- The fibre at the constant `0`-cube is the fibre at `x` by definition.
  ιCube L (ContinuousMap.const _ x)

/-- A `0`-cube is the constant cube at its point, so its class is the class at that point. -/
private lemma ιCube_eq (c : SingularCube X 0) :
    ιCube L c = ιNormalizedTwistedCubicalHomology₀ L (c 0) := by
  have : c = ContinuousMap.const _ (c 0) := ContinuousMap.ext fun t ↦ by
    rw [Subsingleton.elim t 0]
    rfl
  -- After generalising the point, the two sides agree by definition.
  obtain ⟨x, rfl⟩ : ∃ x, c = ContinuousMap.const _ x := ⟨_, this⟩
  rfl

/-- The class in zeroth homology of a `0`-chain given by a point with a coefficient is the fibre
class of that coefficient. -/
theorem pOpcycles_comp_isoHomologyι₀_inv_ofCube (c : SingularCube X 0)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    (L.normalizedTwistedCubicalChainComplex.pOpcycles 0 ≫
        L.normalizedTwistedCubicalChainComplex.isoHomologyι₀.inv) (ofCube L c a) =
      ιNormalizedTwistedCubicalHomology₀ L (c 0) a :=
  ConcreteCategory.congr_hom (ιCube_eq L c) a

/-- The class in zeroth homology of a coefficient at a `0`-cube is the image of the corresponding
`0`-chain. -/
private lemma ιCube_apply (c : SingularCube X 0) (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    ιCube L c a = (L.normalizedTwistedCubicalChainComplex.pOpcycles 0 ≫
      L.normalizedTwistedCubicalChainComplex.isoHomologyι₀.inv) (ofCube L c a) :=
  -- Both sides unfold to the same composite of linear maps.
  rfl

/-- A boundary vanishes in zeroth homology. -/
private lemma d_comp_pOpcycles_isoHomologyι₀_inv :
    L.normalizedTwistedCubicalChainComplex.d 1 0 ≫
      L.normalizedTwistedCubicalChainComplex.pOpcycles 0 ≫
        L.normalizedTwistedCubicalChainComplex.isoHomologyι₀.inv = 0 := by
  rw [← Category.assoc, HomologicalComplex.d_pOpcycles, zero_comp]

/-- A boundary of a normalized `1`-chain vanishes in zeroth homology. -/
private lemma boundary_class_eq_zero (z : L.NormalizedTwistedCubicalChain 1) :
    (L.normalizedTwistedCubicalChainComplex.pOpcycles 0 ≫
      L.normalizedTwistedCubicalChainComplex.isoHomologyι₀.inv) (boundary L 0 z) = 0 := by
  have h := ConcreteCategory.congr_hom (d_comp_pOpcycles_isoHomologyι₀_inv L) z
  rw [← normalizedTwistedCubicalChainComplex_d_apply]
  exact h

/-- To compare the classes of the end points of a `1`-cube it suffices to do so at any two
coordinates `u` and `v` that equal `0` and `1`; this removes the dependence of the fibres on the
description of the end points as faces of the cube. -/
private lemma ι_cube_one_aux (c : SingularCube X 1) (u v : Fin 1 → I) (hu : u = 0) (hv : v = 1)
    (a : L.obj (FundamentalGroupoid.mk (c 0)))
    (h : ιNormalizedTwistedCubicalHomology₀ L (c u) (L.map (c.pathClass 0 u) a) =
      ιNormalizedTwistedCubicalHomology₀ L (c v) (L.map (c.pathClass 0 v) a)) :
    ιNormalizedTwistedCubicalHomology₀ L (c 0) a =
      ιNormalizedTwistedCubicalHomology₀ L (c 1) (L.map (c.pathClass 0 1) a) := by
  subst hu hv
  simpa using h

/-- The two end points of a cubical `1`-chain with a coefficient have the same class in zeroth
homology, after transport of the coefficient along the path inside the cube. -/
private lemma ι_cube_one (c : SingularCube X 1) (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    ιNormalizedTwistedCubicalHomology₀ L (c 0) a =
      ιNormalizedTwistedCubicalHomology₀ L (c 1) (L.map (c.pathClass 0 1) a) := by
  have h := boundary_class_eq_zero L (ofCube L c a)
  rw [boundary_ofCube] at h
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero, Fin.val_zero,
    pow_zero, one_smul] at h
  have h' := sub_eq_zero.1 ((map_sub _ _ _).symm.trans h)
  refine ι_cube_one_aux L c _ _ ?_ ?_ a
    ((ConcreteCategory.congr_hom (ιCube_eq L _) _).symm.trans
      (h'.trans (ConcreteCategory.congr_hom (ιCube_eq L _) _)))
  · ext j
    fin_cases j
    simp
  · ext j
    fin_cases j
    simp

/-- The classes of the end points of a `1`-cube agree after transport of the coefficient along
the cast path class of the cube, whose end points are identified with given points. -/
private lemma ι_cube_one_cast (c : SingularCube X 1) (x y : X) (hx : c 0 = x) (hy : c 1 = y)
    (a : L.obj (FundamentalGroupoid.mk x)) :
    ιNormalizedTwistedCubicalHomology₀ L x a =
      ιNormalizedTwistedCubicalHomology₀ L y
        (L.map (Path.Homotopic.Quotient.cast (c.pathClass 0 1) hx.symm hy.symm) a) := by
  subst hx hy
  simpa using ι_cube_one L c a

/-- Parallel transport along a path does not change the class of a coefficient in zeroth
homology: the path, as a cubical `1`-chain, has the two classes as its boundary. -/
@[reassoc (attr := simp)]
lemma map_ιNormalizedTwistedCubicalHomology₀ {x y : FundamentalGroupoid X} (p : x ⟶ y) :
    L.map p ≫ ιNormalizedTwistedCubicalHomology₀ L y.as =
      ιNormalizedTwistedCubicalHomology₀ L x.as := by
  induction p using Path.Homotopic.Quotient.ind with
  | mk γ =>
    -- The cube sweeping out the path, and the straight path from `0` to `1` inside the cube.
    let c : SingularCube X 1 := γ.toContinuousMap.comp ⟨fun t ↦ t 0, by fun_prop⟩
    let q : Path (0 : Fin 1 → I) 1 :=
      { toFun := fun t _ ↦ t
        continuous_toFun := by fun_prop
        source' := rfl
        target' := rfl }
    have hx : c 0 = x.as := γ.source
    have hy : c 1 = y.as := γ.target
    have key : Path.Homotopic.Quotient.cast (c.pathClass 0 1) hx.symm hy.symm =
        Path.Homotopic.Quotient.mk γ := by
      rw [ContinuousMap.pathClass_eq_mk c q, ← Path.Homotopic.Quotient.mk_cast]
      exact congrArg Path.Homotopic.Quotient.mk (Path.ext (funext fun t ↦ rfl))
    refine ModuleCat.hom_ext (LinearMap.ext fun a ↦ ?_)
    exact ((ι_cube_one_cast L c x.as y.as hx hy a).trans
      (congrArg (fun p ↦ ιNormalizedTwistedCubicalHomology₀ L y.as (L.map p a)) key)).symm

/-- Fibre classes generate zeroth homology. -/
@[ext]
lemma normalizedTwistedCubicalHomology₀_hom_ext {M : ModuleCat.{max v w} R}
    {f g : L.normalizedTwistedCubicalChainComplex.homology 0 ⟶ M}
    (h : ∀ x, ιNormalizedTwistedCubicalHomology₀ L x ≫ f =
      ιNormalizedTwistedCubicalHomology₀ L x ≫ g) : f = g := by
  apply (cancel_epi (L.normalizedTwistedCubicalChainComplex.isoHomologyι₀.inv)).1
  apply (cancel_epi (L.normalizedTwistedCubicalChainComplex.pOpcycles 0)).1
  refine ModuleCat.hom_ext (NormalizedTwistedCubicalChain.hom_ext fun c ↦
    LinearMap.ext fun a ↦ ?_)
  have h' := ConcreteCategory.congr_hom (h (c 0)) a
  rw [← ιCube_eq] at h'
  -- The composite with `ιCube` unfolds to the composite on the left, applied to `ofCube L c a`.
  exact h'

-- The cocone point must compute to the homology in the colimit comparison signatures.
/-- The canonical cocone from the local system to its zeroth cubical homology. -/
@[expose, simps pt ι_app]
def normalizedTwistedCubicalHomology₀Cocone : Cocone L where
  pt := L.normalizedTwistedCubicalChainComplex.homology 0
  ι :=
    { app x := ιNormalizedTwistedCubicalHomology₀ L x.as
      naturality x y p := by
        rw [Functor.const_obj_map]
        exact (map_ιNormalizedTwistedCubicalHomology₀ L p).trans (Category.comp_id _).symm }

/-- The augmentation of `0`-chains into a cocone, as a morphism out of the degree-zero term. -/
private def chainsDesc (s : Cocone L) : L.normalizedTwistedCubicalChainComplex.X 0 ⟶ s.pt :=
  ModuleCat.ofHom (augment s)

/-- The augmentation vanishes on boundaries. -/
private lemma d_comp_chainsDesc (s : Cocone L) :
    L.normalizedTwistedCubicalChainComplex.d 1 0 ≫ chainsDesc L s = 0 := by
  refine ModuleCat.hom_ext (LinearMap.ext fun z ↦ ?_)
  exact LinearMap.congr_fun (augment_boundary s) z

-- The construction uses Mathlib's opcycles and its isomorphism with degree-zero homology.
/-- The map out of zeroth homology induced by the augmentation into a cocone. -/
private def homologyDesc (s : Cocone L) :
    L.normalizedTwistedCubicalChainComplex.homology 0 ⟶ s.pt :=
  L.normalizedTwistedCubicalChainComplex.isoHomologyι₀.hom ≫
    L.normalizedTwistedCubicalChainComplex.descOpcycles (chainsDesc L s) 1 (by simp)
      (d_comp_chainsDesc L s)

/-- The induced map restricts to the augmentation on `0`-chains. -/
private lemma π_comp_homologyDesc (s : Cocone L) :
    L.normalizedTwistedCubicalChainComplex.pOpcycles 0 ≫
        L.normalizedTwistedCubicalChainComplex.isoHomologyι₀.inv ≫ homologyDesc L s =
      chainsDesc L s := by
  rw [homologyDesc, Iso.inv_hom_id_assoc, HomologicalComplex.p_descOpcycles]

/-- The induced map restricts to the leg of the cocone on each fibre class. -/
private lemma ι_comp_homologyDesc (s : Cocone L) (x : X) :
    ιNormalizedTwistedCubicalHomology₀ L x ≫ homologyDesc L s =
      s.ι.app (FundamentalGroupoid.mk x) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun a ↦ ?_)
  -- The fibre at the constant `0`-cube is the fibre at `x` by definition.
  exact (ConcreteCategory.congr_hom (π_comp_homologyDesc L s)
    (ofCubeHom L (ContinuousMap.const _ x) a)).trans
    (augment_ofCube s (ContinuousMap.const _ x) a)

/-- **Zeroth cubical homology with local coefficients is the colimit of the local system.**
The structure maps are the classes of the point fibres. -/
def isColimitNormalizedTwistedCubicalHomology₀Cocone :
    IsColimit (normalizedTwistedCubicalHomology₀Cocone L) where
  desc s := homologyDesc L s
  fac s x := ι_comp_homologyDesc L s x.as
  uniq s f hf := by
    apply normalizedTwistedCubicalHomology₀_hom_ext
    intro x
    exact (hf (FundamentalGroupoid.mk x)).trans (ι_comp_homologyDesc L s x).symm

/-- The canonical identification of zeroth cubical homology with the colimit of the local system
over the fundamental groupoid. -/
def normalizedTwistedCubicalHomology₀IsoColimit :
    L.normalizedTwistedCubicalChainComplex.homology 0 ≅ colimit L :=
  (isColimitNormalizedTwistedCubicalHomology₀Cocone L).coconePointUniqueUpToIso
    (colimit.isColimit L)

/-- The colimit comparison sends each fibre class to its colimit inclusion. -/
@[reassoc (attr := simp)]
lemma ιNormalizedTwistedCubicalHomology₀_isoColimit_hom (x : FundamentalGroupoid X) :
    ιNormalizedTwistedCubicalHomology₀ L x.as ≫
        (normalizedTwistedCubicalHomology₀IsoColimit L).hom =
      colimit.ι L x :=
  (isColimitNormalizedTwistedCubicalHomology₀Cocone L).comp_coconePointUniqueUpToIso_hom _ x

/-- The inverse colimit comparison recovers the fibre class from the colimit inclusion. -/
@[reassoc (attr := simp)]
lemma colimit_ι_normalizedTwistedCubicalHomology₀IsoColimit_inv (x : FundamentalGroupoid X) :
    colimit.ι L x ≫ (normalizedTwistedCubicalHomology₀IsoColimit L).inv =
      ιNormalizedTwistedCubicalHomology₀ L x.as :=
  (isColimitNormalizedTwistedCubicalHomology₀Cocone L).comp_coconePointUniqueUpToIso_inv _ x

/-- The colimit identification is induced by the augmentation of `0`-chains into the colimit: a
`0`-chain goes to the same element of the colimit as its class in homology. -/
lemma pOpcycles_comp_normalizedTwistedCubicalHomology₀IsoColimit_hom :
    L.normalizedTwistedCubicalChainComplex.pOpcycles 0 ≫
        L.normalizedTwistedCubicalChainComplex.isoHomologyι₀.inv ≫
          (normalizedTwistedCubicalHomology₀IsoColimit L).hom =
      ModuleCat.ofHom (augment (colimit.cocone L)) := by
  refine ModuleCat.hom_ext (NormalizedTwistedCubicalChain.hom_ext fun c ↦
    LinearMap.ext fun a ↦ ?_)
  have h := ConcreteCategory.congr_hom
    (ιNormalizedTwistedCubicalHomology₀_isoColimit_hom L (FundamentalGroupoid.mk (c 0))) a
  rw [← ιCube_eq] at h
  exact h.trans (augment_ofCube (colimit.cocone L) c a).symm

/-- A morphism of local systems acts on `0`-chains of a `0`-cube by its component at the
point. -/
private lemma ofCubeHom_comp_coefficientMap_f {K : LocalCoefficientSystem.{u, v, max v w} R X}
    (η : L ⟶ K) (c : SingularCube X 0) :
    ofCubeHom L c ≫ (normalizedTwistedCubicalChainComplexCoefficientMap η).f 0 =
      η.app (FundamentalGroupoid.mk (c 0)) ≫ ofCubeHom K c := by
  rw [normalizedTwistedCubicalChainComplexCoefficientMap_f]
  exact ModuleCat.hom_ext (LinearMap.ext fun a ↦ coefficientMap_ofCube η c a)

/-- A morphism of local systems acts on fibre classes by its component at that point. -/
@[reassoc (attr := simp)]
lemma ιNormalizedTwistedCubicalHomology₀_coefficientMap
    {K : LocalCoefficientSystem.{u, v, max v w} R X} (η : L ⟶ K) (x : X) :
    ιNormalizedTwistedCubicalHomology₀ L x ≫
        HomologicalComplex.homologyMap
          (normalizedTwistedCubicalChainComplexCoefficientMap η) 0 =
      η.app (FundamentalGroupoid.mk x) ≫ ιNormalizedTwistedCubicalHomology₀ K x := by
  refine ModuleCat.hom_ext (LinearMap.ext fun a ↦ ?_)
  -- The fibre at the constant `0`-cube is the fibre at `x` by definition.
  exact (ConcreteCategory.congr_hom
    (ChainComplex.pOpcycles_comp_isoHomologyι₀_inv_comp_homologyMap
      (normalizedTwistedCubicalChainComplexCoefficientMap η))
      (ofCubeHom L (ContinuousMap.const _ x) a)).trans
    (congrArg (ConcreteCategory.hom (K.normalizedTwistedCubicalChainComplex.pOpcycles 0 ≫
      K.normalizedTwistedCubicalChainComplex.isoHomologyι₀.inv))
      (ConcreteCategory.congr_hom
        (ofCubeHom_comp_coefficientMap_f L η (ContinuousMap.const _ x)) a))

/-- The colimit identification is natural in the coefficient system. -/
@[reassoc]
lemma normalizedTwistedCubicalHomology₀IsoColimit_hom_naturality
    {K : LocalCoefficientSystem.{u, v, max v w} R X} (η : L ⟶ K) :
    HomologicalComplex.homologyMap (normalizedTwistedCubicalChainComplexCoefficientMap η) 0 ≫
        (normalizedTwistedCubicalHomology₀IsoColimit K).hom =
      (normalizedTwistedCubicalHomology₀IsoColimit L).hom ≫ colim.map η := by
  apply normalizedTwistedCubicalHomology₀_hom_ext
  intro x
  rw [ιNormalizedTwistedCubicalHomology₀_coefficientMap_assoc]
  rw [ιNormalizedTwistedCubicalHomology₀_isoColimit_hom K (FundamentalGroupoid.mk x),
    ιNormalizedTwistedCubicalHomology₀_isoColimit_hom_assoc L (FundamentalGroupoid.mk x)]
  simp

end TauCeti.LocalCoefficientSystem
