/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.NodeLocalRing
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# Holomorphic functions on normalization quotients

Given an equivalence relation on a complex manifold, define a sheaf on its topological quotient:
a section is a holomorphic function on the inverse image of an open set whose values agree at
related points. In particular, for the normalization of a nodal curve these are precisely the
holomorphic functions satisfying the matching condition at every pair of node flags. No
hypersurface charts or stability assumptions enter this construction.

`quotientSheaf` is a subsheaf of the direct image of the native holomorphic structure sheaf.
`quotientStalkBranch` restricts its germs to a point of the normalization. At two identified
points, `quotientStalkToNode` combines these restrictions into the existing branch-pair node
ring. This file constructs that comparison homomorphism, not an isomorphism of node stalks.

The construction works for arbitrary equivalence relations: the sheaf and the comparison maps
do not need finiteness of the flags, compactness, or connectedness of the curve. It makes no
claim that an arbitrary such quotient is a complex analytic space.

The sheaf proof uses Mathlib's direct-image sheaf and unique-gluing API. The local ring and
matching condition follow the normalization description of nodal curves in Joel W. Robbin and
Dietmar A. Salamon, *A construction of the Deligne–Mumford orbifold*, JEMS 8 (2006).
-/

public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open scoped Manifold

namespace TauCeti.holomorphicStructureSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  {X : Type} [TopologicalSpace X] [ChartedSpace H X] (s : Setoid X)

/-- The continuous projection from the normalization to its topological quotient. -/
-- Expose the projection so inverse-image section domains compute to quotient fibres.
@[expose]
def quotientMap : TopCat.of X ⟶ TopCat.of (Quotient s) :=
  TopCat.ofHom ⟨Quotient.mk s, continuous_quotient_mk'⟩

/-- The quotient projection sends a point to its equivalence class. -/
@[simp]
-- Avoid indexing on the two definitionally equal presentations of the continuous-map type.
theorem quotientMap_apply (x : X) :
    DFunLike.coe (F := no_index _) (ConcreteCategory.hom (quotientMap s)) x =
      Quotient.mk s x := rfl

/-- Holomorphic functions on the normalization over `U` which agree at identified points. -/
def quotientSectionSubring (U : Opens (Quotient s)) :
    Subring ((holomorphicStructureSheaf I X).obj.obj
      (op ((Opens.map (quotientMap s)).obj U))) where
  carrier := {f | ∀ (x y : X) (hx : Quotient.mk s x ∈ U)
    (hy : Quotient.mk s y ∈ U), s x y → f ⟨x, hx⟩ = f ⟨y, hy⟩}
  zero_mem' := fun _ _ _ _ _ ↦ by simp
  one_mem' := fun _ _ _ _ _ ↦ by simp
  add_mem' := by
    intro f g hf hg x y hx hy hxy
    simp only [add_apply, hf x y hx hy hxy, hg x y hx hy hxy]
  mul_mem' := by
    intro f g hf hg x y hx hy hxy
    simp only [mul_apply, hf x y hx hy hxy, hg x y hx hy hxy]
  neg_mem' := by
    intro f hf x y hx hy hxy
    simp only [neg_apply, hf x y hx hy hxy]

/-- The characteristic matching condition for sections on the quotient. -/
@[simp]
theorem mem_quotientSectionSubring (U : Opens (Quotient s))
    (f : (holomorphicStructureSheaf I X).obj.obj
      (op ((Opens.map (quotientMap s)).obj U))) :
    f ∈ quotientSectionSubring I s U ↔
      ∀ (x y : X) (hx : Quotient.mk s x ∈ U) (hy : Quotient.mk s y ∈ U),
        s x y → f ⟨x, hx⟩ = f ⟨y, hy⟩ := Iff.rfl

/-- On an open set over which no points are identified, every holomorphic function descends.
This applies in particular to opens in the smooth locus of a nodal normalization quotient. -/
theorem quotientSectionSubring_eq_top_of_injOn (U : Opens (Quotient s))
    (hU : Set.InjOn (Quotient.mk s) (Quotient.mk s ⁻¹' (U : Set (Quotient s)))) :
    quotientSectionSubring I s U = ⊤ := by
  apply top_unique
  intro f _ x y hx hy hxy
  have h : x = y := hU hx hy (Quotient.sound hxy)
  subst y
  rfl

private def quotientRestrict {U V : Opens (Quotient s)} (h : V ⟶ U) :
    quotientSectionSubring I s U →+* quotientSectionSubring I s V :=
  ((holomorphicStructureSheaf I X).obj.map ((Opens.map (quotientMap s)).map h).op).hom
    |>.restrict _ _ (by
      intro f hf x y hx hy hxy
      simpa only [map_apply] using hf x y (h.le hx) (h.le hy) hxy)

private def quotientPresheaf : TopCat.Presheaf CommRingCat (TopCat.of (Quotient s)) where
  obj U := CommRingCat.of (quotientSectionSubring I s U.unop)
  map h := CommRingCat.ofHom (quotientRestrict I s h.unop)
  map_id _ := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro f
    apply Subtype.ext
    exact (holomorphicStructureSheaf I X).obj.map_id_apply _ f.1
  map_comp h k := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro f
    apply Subtype.ext
    apply holomorphicStructureSheaf.ext
    intro x
    -- Remove the categorical and subring wrappers to compare the underlying restrictions.
    change ((holomorphicStructureSheaf I X).obj.map
        ((Opens.map (quotientMap s)).map (h ≫ k).unop).op f.1) x =
      ((holomorphicStructureSheaf I X).obj.map ((Opens.map (quotientMap s)).map k.unop).op
        ((holomorphicStructureSheaf I X).obj.map ((Opens.map (quotientMap s)).map h.unop).op f.1)) x
    simp only [map_apply]

private def quotientInclusion : quotientPresheaf I s ⟶
    (TopCat.Presheaf.pushforward CommRingCat (quotientMap s)).obj
      (holomorphicStructureSheaf I X).obj where
  app U := CommRingCat.ofHom (quotientSectionSubring I s U.unop).subtype

private theorem quotientPresheaf_isSheaf : (quotientPresheaf I s).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U f hf
  let F := (TopCat.Presheaf.pushforward CommRingCat (quotientMap s)).obj
    (holomorphicStructureSheaf I X).obj
  have hc : F.IsCompatible U (fun i ↦ (f i).1) := by
    intro i j
    exact congrArg Subtype.val (hf i j)
  obtain ⟨g, hg, hu⟩ := TopCat.Presheaf.IsSheaf.isSheafUniqueGluing
    (TopCat.Sheaf.pushforward_sheaf_of_sheaf (quotientMap s)
      (holomorphicStructureSheaf I X).property) U (fun i ↦ (f i).1) hc
  have hmem : g ∈ quotientSectionSubring I s (iSup U) := by
    intro x y hx hy hxy
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    have hj : Quotient.mk s y ∈ U i := Quotient.sound hxy ▸ hi
    have hgi : (holomorphicStructureSheaf I X).obj.map
        ((Opens.map (quotientMap s)).map (Opens.leSupr U i)).op g = (f i).1 := hg i
    have hxi := congrArg (fun t ↦ t ⟨x, hi⟩) hgi
    have hyi := congrArg (fun t ↦ t ⟨y, hj⟩) hgi
    simp only [map_apply] at hxi hyi
    exact hxi.trans (((f i).2 x y hi hj hxy).trans hyi.symm)
  refine ⟨⟨g, hmem⟩, fun i ↦ Subtype.ext (hg i), ?_⟩
  intro t ht
  exact Subtype.ext (hu t.1 fun i ↦ congrArg Subtype.val (ht i))

/-- The sheaf of holomorphic functions on the normalization which have matching values on each
fibre of the quotient map. For paired node flags this is the normalization construction of the
structure sheaf of a nodal curve. -/
def quotientSheaf : TopCat.Sheaf CommRingCat (TopCat.of (Quotient s)) :=
  ⟨quotientPresheaf I s, quotientPresheaf_isSheaf I s⟩

/-- Read a quotient section as its matching holomorphic function upstairs. -/
def quotientSheafSectionsEquiv (U : Opens (Quotient s)) :
    (quotientSheaf I s).obj.obj (op U) ≃+* quotientSectionSubring I s U :=
  RingEquiv.refl _

/-- The normalization pullback includes the quotient sheaf into the direct image of the
holomorphic structure sheaf. -/
def quotientSheafι : quotientSheaf I s ⟶
    (TopCat.Sheaf.pushforward CommRingCat (quotientMap s)).obj
      (holomorphicStructureSheaf I X) :=
  ⟨quotientInclusion I s⟩

/-- Normalization pullback reads the underlying holomorphic function. -/
@[simp]
theorem quotientSheafι_app_apply (U : Opens (Quotient s))
    (f : (quotientSheaf I s).obj.obj (op U)) :
    (@CommRingCat.Hom.hom _
      ((holomorphicStructureSheaf I X).obj.obj (op ((Opens.map (quotientMap s)).obj U)))
      ((quotientSheafι I s).hom.app (op U))) f =
      (quotientSheafSectionsEquiv I s U f).1 := (rfl)

/-- The quotient sheaf is a subobject of the direct image of the normalization sheaf. -/
instance quotientSheafι_mono : Mono (quotientSheafι I s) := by
  have (U : (Opens (Quotient s))ᵒᵖ) : Mono ((quotientSheafι I s).hom.app U) := by
    induction U using Opposite.rec
    apply ConcreteCategory.mono_of_injective
    intro f g h
    apply (quotientSheafSectionsEquiv I s _).injective
    apply Subtype.ext
    -- The simp-normal codomain is sections upstairs; h retains the direct-image presentation.
    erw [quotientSheafι_app_apply, quotientSheafι_app_apply] at h
    exact h
  exact (sheafToPresheaf (Opens.grothendieckTopology (Quotient s)) CommRingCat).mono_of_mono_map
    (NatTrans.mono_of_mono_app (quotientSheafι I s).hom)

/-- Restriction in the quotient sheaf is restriction of the holomorphic section upstairs. -/
@[simp]
theorem quotientSheaf_map_val {U V : Opens (Quotient s)} (h : V ⟶ U)
    (f : (quotientSheaf I s).obj.obj (op U)) :
    (quotientSheafSectionsEquiv I s V ((quotientSheaf I s).obj.map h.op f)).1 =
      (holomorphicStructureSheaf I X).obj.map
        ((Opens.map (quotientMap s)).map h).op (quotientSheafSectionsEquiv I s U f).1 := (rfl)

/-- A quotient germ restricts to a holomorphic germ at any point over its base point. -/
def quotientStalkBranch (z : Quotient s) (x : X) (hx : Quotient.mk s x = z) :
    (quotientSheaf I s).presheaf.stalk z →+*
      (holomorphicStructureSheaf I X).presheaf.stalk x :=
  (eqToHom (congrArg (fun w ↦ (quotientSheaf I s).presheaf.stalk w) hx.symm) ≫
    (TopCat.Presheaf.stalkFunctor CommRingCat (Quotient.mk s x)).map (quotientSheafι I s).hom ≫
    (holomorphicStructureSheaf I X).presheaf.stalkPushforward CommRingCat (quotientMap s) x).hom

/-- Restricting a quotient section's germ to a branch gives its ordinary holomorphic germ. -/
@[simp]
theorem quotientStalkBranch_germ (z : Quotient s) (x : X) (hx : Quotient.mk s x = z)
    (U : Opens (Quotient s)) (hz : z ∈ U) (f : (quotientSheaf I s).obj.obj (op U)) :
    quotientStalkBranch I s z x hx
      (ConcreteCategory.hom ((quotientSheaf I s).presheaf.germ U z hz) f) =
      (holomorphicStructureSheaf I X).presheaf.germ
        ((Opens.map (quotientMap s)).obj U) x
        (by rw [Opens.mem_map, quotientMap_apply, hx]; exact hz)
        (quotientSheafSectionsEquiv I s U f).1 := by
  subst z
  -- Remove the ring-hom and categorical-composition wrappers before using the stalk API.
  change (holomorphicStructureSheaf I X).presheaf.stalkPushforward CommRingCat (quotientMap s) x
      ((TopCat.Presheaf.stalkFunctor CommRingCat (Quotient.mk s x)).map
        (quotientSheafι I s).hom ((quotientSheaf I s).presheaf.germ U _ hz f)) = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  -- The sheaf pushforward and its presheaf pushforward have definitionally equal carriers.
  erw [TopCat.Presheaf.stalkPushforward_germ_apply]
  -- The inclusion lemma uses the upstairs codomain required by simpNF.
  erw [quotientSheafι_app_apply]

/-- The branch restrictions of a quotient germ have equal values at any two identified points. -/
theorem eval_quotientStalkBranch_eq (z : Quotient s) (x y : X)
    (hx : Quotient.mk s x = z) (hy : Quotient.mk s y = z)
    (f : (quotientSheaf I s).presheaf.stalk z) :
    eval I X x (quotientStalkBranch I s z x hx f) =
      eval I X y (quotientStalkBranch I s z y hy f) := by
  obtain ⟨U, hz, g, rfl⟩ := (quotientSheaf I s).presheaf.exists_germ_eq f
  rw [quotientStalkBranch_germ, quotientStalkBranch_germ]
  rw [eval_germ, eval_germ]
  exact (quotientSheafSectionsEquiv I s U g).2 x y (hx.symm ▸ hz) (hy.symm ▸ hz)
    (Quotient.exact (hx.trans hy.symm))

/-- At two identified normalization points, restriction gives a homomorphism from the quotient
stalk to the branch-pair node ring. -/
def quotientStalkToNode (x y : X) (hxy : s x y) :
    (quotientSheaf I s).presheaf.stalk (Quotient.mk s x) →+* nodeLocalRing I I x y :=
  nodeLocalRing.lift (quotientStalkBranch I s _ x rfl)
    (quotientStalkBranch I s _ y (Quotient.sound hxy).symm)
    (eval_quotientStalkBranch_eq I s _ x y rfl (Quotient.sound hxy).symm)

/-- The first branch of the node comparison is normalization restriction at the first flag. -/
@[simp]
theorem fst_quotientStalkToNode (x y : X) (hxy : s x y)
    (f : (quotientSheaf I s).presheaf.stalk (Quotient.mk s x)) :
    nodeLocalRing.fst I I x y (quotientStalkToNode I s x y hxy f) =
      quotientStalkBranch I s _ x rfl f := nodeLocalRing.fst_lift _ _ _ _

/-- The second branch of the node comparison is normalization restriction at the second flag. -/
@[simp]
theorem snd_quotientStalkToNode (x y : X) (hxy : s x y)
    (f : (quotientSheaf I s).presheaf.stalk (Quotient.mk s x)) :
    nodeLocalRing.snd I I x y (quotientStalkToNode I s x y hxy f) =
      quotientStalkBranch I s _ y (Quotient.sound hxy).symm f :=
  nodeLocalRing.snd_lift _ _ _ _

end TauCeti.holomorphicStructureSheaf
