/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.DenseAtYoneda
public import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy
public import TauCeti.AlgebraicTopology.SimplicialSet.Discrete
public import TauCeti.AlgebraicTopology.SimplicialSet.TopAdj
public import TauCeti.AlgebraicTopology.SimplicialSet.WeakEquivalence

/-!
# Connected components of geometric realizations

The connected components of a simplicial set `X` are the path components of its geometric
realization `|X|` (`SSet.π₀EquivZerothHomotopy`): the unit `X ⟶ Sing |X|` of the
realization–singular adjunction induces a bijection on connected components
(`SSet.bijective_mapπ₀_unit`), and Mathlib identifies the connected components of `Sing |X|` with
the path components of `|X|` (`TopCat.zerothHomotopyEquiv`). Injectivity comes from the
continuous map from `|X|` to the discrete space `π₀ X` adjoint to `X ⟶ π₀ X`; surjectivity from
writing `|X|` as the colimit of the realizations of the simplices of `X`, each of which is path
connected.

Consequently a weak equivalence of simplicial sets, a map whose realization is a weak homotopy
equivalence, induces a bijection on connected components
(`SSet.bijective_mapπ₀_of_weakEquivalence`). This is what makes a functor of simplicially
enriched categories that is a weak equivalence on mapping simplicial sets fully faithful on
homotopy categories.

## References

* P. G. Goerss and J. F. Jardine, *Simplicial Homotopy Theory*, Progress in Mathematics 174,
  Birkhäuser, 1999, Section I.11.
-/

public section

open CategoryTheory Limits Simplicial HomotopicalAlgebra

universe u

namespace TauCeti.TopCat

/-- The connected component of a singular vertex corresponds to the path component of its point.
-/
lemma π₀_mk_eq_zerothHomotopyEquiv_mk {T : TopCat.{u}} (q : (TopCat.toSSet.obj T) _⦋0⦌) :
    SSet.π₀.mk q = TopCat.zerothHomotopyEquiv (.mk (TopCat.toSSetObj₀Equiv q)) := by
  rw [TopCat.zerothHomotopyEquiv_mk, Equiv.symm_apply_apply]

end TauCeti.TopCat

namespace SSet

/-- The point of the geometric realization `|X|` given by a vertex `x` of `X`: the singular vertex
`(sSetTopAdj.unit.app X).app _ x` of `|X|`. -/
noncomputable def toTopPoint {X : SSet.{u}} (x : X _⦋0⦌) : |X| :=
  TopCat.toSSetObj₀Equiv ((sSetTopAdj.unit.app X).app _ x)

/-- The realization of a map sends the point of a vertex to the point of its image. -/
@[simp]
lemma toTop_map_toTopPoint {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    toTop.map f (toTopPoint x) = toTopPoint (f.app _ x) := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app (sSetTopAdj.unit.naturality f) _) x
  dsimp at h
  rw [toTopPoint, toTopPoint, h, TauCeti.TopCat.toSSetObj₀Equiv_toSSet_map_app]

/-- The singular simplicial set of a weak homotopy equivalence is bijective on connected
components, these being the path components of the spaces. -/
lemma bijective_mapπ₀_toSSet_map {T T' : TopCat.{u}} (g : T ⟶ T')
    (hg : g.hom.IsWeakHomotopyEquivalence) :
    Function.Bijective (mapπ₀ (TopCat.toSSet.map g)) := by
  -- Connected components of singular simplicial sets are path components via
  -- `TopCat.zerothHomotopyEquiv`.
  have hmk (p : (TopCat.toSSet.obj T) _⦋0⦌) : mapπ₀ (TopCat.toSSet.map g) (π₀.mk p) =
      TopCat.zerothHomotopyEquiv (.mk (g (TopCat.toSSetObj₀Equiv p))) := by
    rw [mapπ₀_mk, TauCeti.TopCat.π₀_mk_eq_zerothHomotopyEquiv_mk,
      TauCeti.TopCat.toSSetObj₀Equiv_toSSet_map_app]
  refine ⟨fun a b h ↦ ?_, fun b ↦ ?_⟩
  · induction a using π₀.rec with | mk p => ?_
    induction b using π₀.rec with | mk q => ?_
    rw [hmk, hmk] at h
    rw [TauCeti.TopCat.π₀_mk_eq_zerothHomotopyEquiv_mk p,
      TauCeti.TopCat.π₀_mk_eq_zerothHomotopyEquiv_mk q]
    exact congrArg _ (ZerothHomotopy.sound
      (hg.joined_iff.1 (Quotient.exact (TopCat.zerothHomotopyEquiv.injective h))).somePath)
  · induction b using π₀.rec with | mk q => ?_
    obtain ⟨s, hs⟩ := hg.exists_joined (TopCat.toSSetObj₀Equiv q)
    refine ⟨π₀.mk (TopCat.toSSetObj₀Equiv.symm s), ?_⟩
    rw [hmk, Equiv.apply_symm_apply, ZerothHomotopy.sound hs.somePath,
      TauCeti.TopCat.π₀_mk_eq_zerothHomotopyEquiv_mk]

variable (X : SSet.{u})

/-- The continuous map from `|X|` to the discrete space `π₀ X` adjoint to the map from `X` to the
discrete simplicial set on `π₀ X`. -/
private noncomputable def toTopToπ₀ : |X| ⟶ TopCat.discrete.obj (π₀ X) :=
  (sSetTopAdj.homEquiv X _).symm (X.toπ₀ ≫
    (constHomEquiv (π₀ X)).symm fun c ↦ TopCat.toSSetObj₀Equiv.symm c)

private lemma toTopToπ₀_toTopPoint (x : X _⦋0⦌) : toTopToπ₀ X (toTopPoint x) = π₀.mk x := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (sSetTopAdj.homEquiv_unit X _ (toTopToπ₀ X)) (Opposite.op ⦋0⦌)) x
  rw [toTopToπ₀, Equiv.apply_symm_apply] at h
  dsimp at h
  rw [toπ₀_app_zero, constHomEquiv_symm_app_zero] at h
  rw [toTopPoint, ← TauCeti.TopCat.toSSetObj₀Equiv_toSSet_map_app]
  exact (TopCat.toSSetObj₀Equiv.symm_apply_eq.1 h).symm

/-- The unit `X ⟶ Sing |X|` is injective on connected components: a path in `|X|` between the
points of two vertices stays in one connected component of `X`. -/
lemma injective_mapπ₀_unit : Function.Injective (mapπ₀ (sSetTopAdj.unit.app X)) := by
  -- A left inverse sends a component of `Sing |X|` to the value of `toTopToπ₀ X` on it, which
  -- is constant along paths since its target is discrete.
  let r : π₀ (TopCat.toSSet.obj |X|) → π₀ X := fun z ↦
    ZerothHomotopy.lift (toTopToπ₀ X) (fun a b p ↦ by
      have h := PreconnectedSpace.constant inferInstance
        ((ConcreteCategory.hom (toTopToπ₀ X)).continuous.comp p.continuous) (x := 0) (y := 1)
      simp only [Function.comp_apply, Path.source, Path.target] at h
      exact h)
      (TopCat.zerothHomotopyEquiv.symm z)
  refine Function.LeftInverse.injective (g := r) fun c ↦ ?_
  induction c using π₀.rec with | mk x => ?_
  simp only [r, mapπ₀_mk, TopCat.zerothHomotopyEquiv_symm_mk]
  exact toTopToπ₀_toTopPoint X x

/-- The unit `X ⟶ Sing |X|` is surjective on connected components: every point of `|X|` lies in
the realization of a simplex of `X`, which is path connected. -/
lemma surjective_mapπ₀_unit : Function.Surjective (mapπ₀ (sSetTopAdj.unit.app X)) := by
  intro z
  induction z using π₀.rec with | mk p => ?_
  -- The point of `p` comes from the realization of some simplex `j.hom : Δ[n] ⟶ X`.
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (toTop ⋙ forget TopCat) (denseAtUliftYoneda X))
    (TopCat.toSSetObj₀Equiv p)
  dsimp at y hy
  rw [Category.id_comp] at hy
  have : PathConnectedSpace |uliftYoneda.{u}.obj j.left| :=
    inferInstanceAs (PathConnectedSpace |stdSimplex.{u}.obj j.left|)
  let v : (uliftYoneda.{u}.obj j.left) _⦋0⦌ := ULift.up (SimplexCategory.const _ _ 0)
  refine ⟨π₀.mk (j.hom.app _ v), ?_⟩
  rw [mapπ₀_mk, TauCeti.TopCat.π₀_mk_eq_zerothHomotopyEquiv_mk,
    TauCeti.TopCat.π₀_mk_eq_zerothHomotopyEquiv_mk, ← hy]
  -- The singular vertex of the unit at a vertex is, by definition, the point of that vertex.
  change TopCat.zerothHomotopyEquiv (.mk (toTopPoint (j.hom.app _ v))) = _
  rw [← toTop_map_toTopPoint]
  exact congrArg _ (ZerothHomotopy.sound (((PathConnectedSpace.joined (toTopPoint v) y).map
    (toTop.map j.hom).hom.continuous).somePath))

/-- The unit `X ⟶ Sing |X|` of the realization–singular adjunction is bijective on connected
components. -/
lemma bijective_mapπ₀_unit : Function.Bijective (mapπ₀ (sSetTopAdj.unit.app X)) :=
  ⟨X.injective_mapπ₀_unit, X.surjective_mapπ₀_unit⟩

/-- The connected components of a simplicial set are the path components of its geometric
realization. -/
noncomputable def π₀EquivZerothHomotopy : π₀ X ≃ ZerothHomotopy |X| :=
  (Equiv.ofBijective _ X.bijective_mapπ₀_unit).trans TopCat.zerothHomotopyEquiv.symm

/-- The component of a vertex corresponds to the path component of its point. -/
@[simp]
lemma π₀EquivZerothHomotopy_mk (x : X _⦋0⦌) :
    X.π₀EquivZerothHomotopy (π₀.mk x) = .mk (toTopPoint x) :=
  (rfl)

open modelCategoryQuillen in
/-- A weak equivalence of simplicial sets induces a bijection on connected components. -/
theorem bijective_mapπ₀_of_weakEquivalence {X Y : SSet.{u}} (f : X ⟶ Y) [WeakEquivalence f] :
    Function.Bijective (mapπ₀ f) := by
  -- Compare with the singular simplicial sets of the realizations through the units.
  have h : mapπ₀ (sSetTopAdj.unit.app Y) ∘ mapπ₀ f =
      mapπ₀ (TopCat.toSSet.map (toTop.map f)) ∘ mapπ₀ (sSetTopAdj.unit.app X) := by
    funext c
    simp only [Function.comp_apply, ← mapπ₀_comp_apply]
    exact congrFun (congrArg mapπ₀ (sSetTopAdj.unit.naturality f)) c
  rw [← (bijective_mapπ₀_unit Y).of_comp_iff', h]
  exact (bijective_mapπ₀_toSSet_map _ ((modelCategoryQuillen.weakEquivalence_iff f).1 ‹_›)).comp
    (bijective_mapπ₀_unit X)

end SSet
