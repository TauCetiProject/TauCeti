/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.NodeLocalRing
public import TauCeti.Topology.Category.TopCat.Quotient
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Topology.Sheaves.CommRingCat

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
ring.

When the identifications are isolated, these maps are isomorphisms. At a point near which no two
points are identified, `quotientStalkBranch_bijective` shows that the stalk of the quotient sheaf
is the holomorphic stalk of the normalization. At two distinct points `x` and `y` identified only
with each other, near which nothing else is identified, `quotientStalkToNode_bijective` shows
that the stalk is the branch-pair node ring: a germ on the quotient is the same as a pair of
holomorphic germs at `x` and `y` with equal values. The node case needs the normalization to be
Hausdorff, so that the two branch germs can be glued on disjoint neighbourhoods.

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

/-- Holomorphic functions on the normalization over `U` which agree at identified points. -/
def quotientSectionSubring (U : Opens (Quotient s)) :
    Subring ((holomorphicStructureSheaf I X).obj.obj
      (op ((Opens.map (TopCat.quotientMk s)).obj U))) where
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
      (op ((Opens.map (TopCat.quotientMk s)).obj U))) :
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
  ((holomorphicStructureSheaf I X).obj.map ((Opens.map (TopCat.quotientMk s)).map h).op).hom
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
    exact (holomorphicStructureSheaf I X).obj.map_comp_apply _ _ f.1

private def quotientInclusion : quotientPresheaf I s ⟶
    (TopCat.Presheaf.pushforward CommRingCat (TopCat.quotientMk s)).obj
      (holomorphicStructureSheaf I X).obj where
  app U := CommRingCat.ofHom (quotientSectionSubring I s U.unop).subtype

private theorem quotientPresheaf_isSheaf : (quotientPresheaf I s).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U f hf
  let F := (TopCat.Presheaf.pushforward CommRingCat (TopCat.quotientMk s)).obj
    (holomorphicStructureSheaf I X).obj
  have hc : F.IsCompatible U (fun i ↦ (f i).1) := by
    intro i j
    exact congrArg Subtype.val (hf i j)
  obtain ⟨g, hg, hu⟩ := TopCat.Presheaf.IsSheaf.isSheafUniqueGluing
    (TopCat.Sheaf.pushforward_sheaf_of_sheaf (TopCat.quotientMk s)
      (holomorphicStructureSheaf I X).property) U (fun i ↦ (f i).1) hc
  have hmem : g ∈ quotientSectionSubring I s (iSup U) := by
    intro x y hx hy hxy
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    have hj : Quotient.mk s y ∈ U i := Quotient.sound hxy ▸ hi
    have hgi : (holomorphicStructureSheaf I X).obj.map
        ((Opens.map (TopCat.quotientMk s)).map (Opens.leSupr U i)).op g = (f i).1 := hg i
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

/-- Quotient sections are equal if their holomorphic functions upstairs agree pointwise. -/
@[ext]
theorem quotientSheaf_ext {U : Opens (Quotient s)}
    {f g : (quotientSheaf I s).obj.obj (op U)}
    (h : ∀ x, (quotientSheafSectionsEquiv I s U f).1 x =
      (quotientSheafSectionsEquiv I s U g).1 x) : f = g := by
  apply (quotientSheafSectionsEquiv I s U).injective
  exact Subtype.ext (holomorphicStructureSheaf.ext h)

/-- The normalization pullback includes the quotient sheaf into the direct image of the
holomorphic structure sheaf. -/
def quotientSheafι : quotientSheaf I s ⟶
    (TopCat.Sheaf.pushforward CommRingCat (TopCat.quotientMk s)).obj
      (holomorphicStructureSheaf I X) :=
  ⟨quotientInclusion I s⟩

/-- Normalization pullback reads the underlying holomorphic function. -/
@[simp]
theorem quotientSheafι_app_apply (U : Opens (Quotient s))
    (f : (quotientSheaf I s).obj.obj (op U)) :
    (@CommRingCat.Hom.hom _
      ((holomorphicStructureSheaf I X).obj.obj (op ((Opens.map (TopCat.quotientMk s)).obj U)))
      ((quotientSheafι I s).hom.app (op U))) f =
      (quotientSheafSectionsEquiv I s U f).1 := (rfl)

/-- The quotient sheaf is a subobject of the direct image of the normalization sheaf. -/
instance quotientSheafι_mono : Mono (quotientSheafι I s) := by
  have (U : (Opens (Quotient s))ᵒᵖ) : Mono ((quotientSheafι I s).hom.app U) := by
    induction U using Opposite.rec
    apply ConcreteCategory.mono_of_injective
    exact Subtype.val_injective
  exact (sheafToPresheaf (Opens.grothendieckTopology (Quotient s)) CommRingCat).mono_of_mono_map
    (NatTrans.mono_of_mono_app (quotientSheafι I s).hom)

/-- Restriction in the quotient sheaf is restriction of the holomorphic section upstairs. -/
@[simp]
theorem quotientSheaf_map_val {U V : Opens (Quotient s)} (h : V ⟶ U)
    (f : (quotientSheaf I s).obj.obj (op U)) :
    (quotientSheafSectionsEquiv I s V ((quotientSheaf I s).obj.map h.op f)).1 =
      (holomorphicStructureSheaf I X).obj.map
        ((Opens.map (TopCat.quotientMk s)).map h).op (quotientSheafSectionsEquiv I s U f).1 := (rfl)

/-- A quotient germ restricts to a holomorphic germ at any point over its base point. -/
def quotientStalkBranch (z : Quotient s) (x : X) (hx : Quotient.mk s x = z) :
    (quotientSheaf I s).presheaf.stalk z →+*
      (holomorphicStructureSheaf I X).presheaf.stalk x :=
  (eqToHom (congrArg (fun w ↦ (quotientSheaf I s).presheaf.stalk w) hx.symm) ≫
    (TopCat.Presheaf.stalkFunctor CommRingCat (Quotient.mk s x)).map (quotientSheafι I s).hom ≫
    (holomorphicStructureSheaf I X).presheaf.stalkPushforward CommRingCat
      (TopCat.quotientMk s) x).hom

/-- Restricting a quotient section's germ to a branch gives its ordinary holomorphic germ. -/
@[simp]
theorem quotientStalkBranch_germ (z : Quotient s) (x : X) (hx : Quotient.mk s x = z)
    (U : Opens (Quotient s)) (hz : z ∈ U) (f : (quotientSheaf I s).obj.obj (op U)) :
    quotientStalkBranch I s z x hx
      (ConcreteCategory.hom ((quotientSheaf I s).presheaf.germ U z hz) f) =
      (holomorphicStructureSheaf I X).presheaf.germ
        ((Opens.map (TopCat.quotientMk s)).obj U) x
        (by rw [Opens.mem_map, TopCat.quotientMk_apply, hx]; exact hz)
        (quotientSheafSectionsEquiv I s U f).1 := by
  subst z
  exact (congrArg
    ((holomorphicStructureSheaf I X).presheaf.stalkPushforward CommRingCat (TopCat.quotientMk s) x)
    (TopCat.Presheaf.stalkFunctor_map_germ_apply U (Quotient.mk s x) hz
      (quotientSheafι I s).hom f)).trans
    (TopCat.Presheaf.stalkPushforward_germ_apply CommRingCat (TopCat.quotientMk s)
      (holomorphicStructureSheaf I X).presheaf U x hz
      (quotientSheafSectionsEquiv I s U f).1)

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

/-! ### Stalks at smooth points and at nodes

Away from the identified points, and at a pair of points identified only with each other, the
stalks of the quotient sheaf are the expected local rings. The hypotheses are local: near the
relevant points no other identifications occur. -/

section Stalk

open Topology

variable {I s}

/-- On `N`, a point is identified only with itself, or else both points lie in `{x, y}`. -/
private def IsPairNhd (s : Setoid X) (x y : X) (N : Set X) : Prop :=
  ∀ w ∈ N, ∀ v, s w v → v = w ∨ ((w = x ∨ w = y) ∧ (v = x ∨ v = y))

/-- The local hypotheses at an identified pair give an open neighbourhood of both points on
which nothing else is identified. -/
private theorem exists_isPairNhd {x y : X} (hclass : ∀ w, s x w → w = x ∨ w = y)
    (hx : ∀ᶠ w in 𝓝 x, ∀ v, s w v → v = w ∨ s x w)
    (hy : ∀ᶠ w in 𝓝 y, ∀ v, s w v → v = w ∨ s x w) :
    ∃ N : Opens X, x ∈ N ∧ y ∈ N ∧ IsPairNhd s x y N := by
  obtain ⟨A, hA, hAo, hxA⟩ := eventually_nhds_iff.mp hx
  obtain ⟨B, hB, hBo, hyB⟩ := eventually_nhds_iff.mp hy
  refine ⟨⟨A ∪ B, hAo.union hBo⟩, Or.inl hxA, Or.inr hyB, fun w hw v hwv ↦ ?_⟩
  have key : v = w ∨ s x w := hw.elim (fun h ↦ hA w h v hwv) (fun h ↦ hB w h v hwv)
  exact key.imp_right fun hxw ↦ ⟨hclass w hxw, hclass v (s.trans' hxw hwv)⟩

/-- An open subset of a pair neighbourhood containing both points of the pair is saturated. -/
private theorem saturated_of_isPairNhd {x y : X} {N : Set X} (hN : IsPairNhd s x y N)
    {V : Opens X} (hVN : (V : Set X) ⊆ N) (hxV : x ∈ V) (hyV : y ∈ V) :
    ∀ ⦃w v⦄, w ∈ V → s w v → v ∈ V := by
  intro w v hw hwv
  rcases hN w (hVN hw) v hwv with rfl | ⟨-, rfl | rfl⟩
  exacts [hw, hxV, hyV]

/-- A holomorphic function on an open set of a pair neighbourhood descends to the quotient as
soon as it takes equal values at the two points of the pair. -/
private def descendSection {x y : X} {N : Set X} (hN : IsPairNhd s x y N) (V : Opens X)
    (hVN : (V : Set X) ⊆ N) (hxV : x ∈ V) (hyV : y ∈ V)
    (τ : (holomorphicStructureSheaf I X).obj.obj (op V)) (hτ : τ ⟨x, hxV⟩ = τ ⟨y, hyV⟩) :
    (quotientSheaf I s).obj.obj
      (op (V.imageQuotientMk (saturated_of_isPairNhd hN hVN hxV hyV))) :=
  (quotientSheafSectionsEquiv I s _).symm
    ⟨(holomorphicStructureSheaf I X).obj.map
      (homOfLE fun _ hw ↦ (Opens.mem_map_imageQuotientMk V _).mp hw).op τ, by
      intro w v hw hv hwv
      simp only [map_apply]
      rcases hN w (hVN ((Opens.mem_map_imageQuotientMk V
        (saturated_of_isPairNhd hN hVN hxV hyV)).mp hw)) v hwv with rfl | ⟨hw' | hw', hv' | hv'⟩ <;>
        (try subst w) <;> (try subst v) <;> first | rfl | exact hτ | exact hτ.symm⟩

/-- The branch germs of a descended section are the germs of the original function. -/
private theorem quotientStalkBranch_germ_descendSection {x y : X} {N : Set X}
    (hN : IsPairNhd s x y N) (V : Opens X) (hVN : (V : Set X) ⊆ N) (hxV : x ∈ V) (hyV : y ∈ V)
    (τ : (holomorphicStructureSheaf I X).obj.obj (op V)) (hτ : τ ⟨x, hxV⟩ = τ ⟨y, hyV⟩)
    (z : Quotient s) (w : X) (hw : Quotient.mk s w = z) (hwV : w ∈ V) :
    quotientStalkBranch I s z w hw
      (ConcreteCategory.hom ((quotientSheaf I s).presheaf.germ _ z
        (hw ▸ (Opens.mem_map_imageQuotientMk V
          (saturated_of_isPairNhd hN hVN hxV hyV)).mpr hwV))
        (descendSection hN V hVN hxV hyV τ hτ)) =
      (holomorphicStructureSheaf I X).presheaf.germ V w hwV τ := by
  rw [quotientStalkBranch_germ, descendSection, RingEquiv.apply_symm_apply]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

/-- A germ on the quotient vanishes if its two branch germs at an identified pair vanish. -/
private theorem eq_zero_of_quotientStalkBranch {x y : X} (hxy : s x y) {N : Opens X}
    (hN : IsPairNhd s x y N) (hxN : x ∈ N) (hyN : y ∈ N)
    (f : (quotientSheaf I s).presheaf.stalk (Quotient.mk s x))
    (hfx : quotientStalkBranch I s _ x rfl f = 0)
    (hfy : quotientStalkBranch I s _ y (Quotient.sound hxy).symm f = 0) : f = 0 := by
  obtain ⟨U, hzU, σ, rfl⟩ := (quotientSheaf I s).presheaf.exists_germ_eq f
  rw [quotientStalkBranch_germ] at hfx hfy
  have hxU : x ∈ (Opens.map (TopCat.quotientMk s)).obj U := by
    rw [Opens.mem_map, TopCat.quotientMk_apply]
    exact hzU
  have hyU : y ∈ (Opens.map (TopCat.quotientMk s)).obj U := by
    rw [Opens.mem_map, TopCat.quotientMk_apply, ← Quotient.sound hxy]
    exact hzU
  obtain ⟨A, hxA, iA, _, hA⟩ := (holomorphicStructureSheaf I X).presheaf.germ_eq x hxU hxU _ 0
    (hfx.trans (map_zero _).symm)
  obtain ⟨B, hyB, iB, _, hB⟩ := (holomorphicStructureSheaf I X).presheaf.germ_eq y hyU hyU _ 0
    (hfy.trans (map_zero _).symm)
  rw [map_zero] at hA hB
  let V : Opens X := (A ⊓ N) ⊔ (B ⊓ N)
  have hVN : (V : Set X) ⊆ N := sup_le inf_le_right inf_le_right
  have hxV : x ∈ V := Or.inl ⟨hxA, hxN⟩
  have hyV : y ∈ V := Or.inr ⟨hyB, hyN⟩
  have hV := saturated_of_isPairNhd hN hVN hxV hyV
  have hWU : V.imageQuotientMk hV ≤ U := by
    intro z hz
    obtain ⟨w, hw | hw, rfl⟩ := (Opens.mem_imageQuotientMk V hV).mp hz
    exacts [iA.le hw.1, iB.le hw.1]
  have hxW : Quotient.mk s x ∈ V.imageQuotientMk hV :=
    (Opens.mem_map_imageQuotientMk V hV).mpr hxV
  have h0 : (quotientSheaf I s).presheaf.map (homOfLE hWU).op σ = 0 := by
    ext w
    rw [quotientSheaf_map_val, map_zero]
    obtain hw | hw := (Opens.mem_map_imageQuotientMk V hV).mp w.2
    · simpa using congrArg (fun t ↦ t ⟨w, hw.1⟩) hA
    · simpa using congrArg (fun t ↦ t ⟨w, hw.1⟩) hB
  rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE hWU) _ hxW, h0, map_zero]

/-- A holomorphic function near an identified pair, with equal values at the two points, is the
common branch restriction of a germ on the quotient. -/
private theorem exists_quotientStalkBranch_eq {x y : X} (hxy : s x y) {N : Opens X}
    (hN : IsPairNhd s x y N) (V : Opens X) (hVN : V ≤ N) (hxV : x ∈ V) (hyV : y ∈ V)
    (τ : (holomorphicStructureSheaf I X).obj.obj (op V)) (hτ : τ ⟨x, hxV⟩ = τ ⟨y, hyV⟩) :
    ∃ f : (quotientSheaf I s).presheaf.stalk (Quotient.mk s x),
      quotientStalkBranch I s _ x rfl f =
        (holomorphicStructureSheaf I X).presheaf.germ V x hxV τ ∧
      quotientStalkBranch I s _ y (Quotient.sound hxy).symm f =
        (holomorphicStructureSheaf I X).presheaf.germ V y hyV τ :=
  ⟨_, quotientStalkBranch_germ_descendSection hN V hVN hxV hyV τ hτ _ x rfl hxV,
    quotientStalkBranch_germ_descendSection hN V hVN hxV hyV τ hτ _ y _ hyV⟩

/-- **Stalks at smooth points.** At a point of the normalization near which no two points are
identified, restriction to the branch is an isomorphism from the stalk of the quotient sheaf to
the holomorphic stalk of the normalization. -/
theorem quotientStalkBranch_bijective (x : X) (hx : ∀ᶠ w in 𝓝 x, ∀ v, s w v → v = w) :
    Function.Bijective (quotientStalkBranch I s (Quotient.mk s x) x rfl) := by
  have hx' : ∀ᶠ w in 𝓝 x, ∀ v, s w v → v = w ∨ s x w :=
    hx.mono fun w hw v hwv ↦ Or.inl (hw v hwv)
  obtain ⟨N, hxN, -, hN⟩ := exists_isPairNhd (fun w hxw ↦ Or.inl (hx.self_of_nhds w hxw)) hx' hx'
  refine ⟨(injective_iff_map_eq_zero _).mpr fun f hf ↦
    eq_zero_of_quotientStalkBranch (s.refl' x) hN hxN hxN f hf hf, fun g ↦ ?_⟩
  obtain ⟨V, hxV, σ, rfl⟩ := (holomorphicStructureSheaf I X).presheaf.exists_germ_eq g
  obtain ⟨f, hf, -⟩ := exists_quotientStalkBranch_eq (s.refl' x) hN (V ⊓ N) inf_le_right
    ⟨hxV, hxN⟩ ⟨hxV, hxN⟩ ((holomorphicStructureSheaf I X).obj.map
      (homOfLE inf_le_left).op σ) rfl
  exact ⟨f, hf.trans (TopCat.Presheaf.germ_res_apply _ _ _ _ _)⟩

/-- At two points identified with each other and with no other point, near which nothing else
is identified, a germ on the quotient is determined by its two branch germs. -/
theorem quotientStalkToNode_injective {x y : X} (hxy : s x y)
    (hclass : ∀ w, s x w → w = x ∨ w = y)
    (hx : ∀ᶠ w in 𝓝 x, ∀ v, s w v → v = w ∨ s x w)
    (hy : ∀ᶠ w in 𝓝 y, ∀ v, s w v → v = w ∨ s x w) :
    Function.Injective (quotientStalkToNode I s x y hxy) := by
  obtain ⟨N, hxN, hyN, hN⟩ := exists_isPairNhd hclass hx hy
  refine (injective_iff_map_eq_zero _).mpr fun f hf ↦
    eq_zero_of_quotientStalkBranch hxy hN hxN hyN f ?_ ?_
  · simpa using congrArg (nodeLocalRing.fst I I x y) hf
  · simpa using congrArg (nodeLocalRing.snd I I x y) hf

/-- Sections of a sheaf of rings on two disjoint opens glue to a section on their union. -/
private theorem exists_section_sup_of_disjoint (F : TopCat.Sheaf CommRingCat (TopCat.of X))
    {A B : Opens X} (hAB : Disjoint A B) (σ : F.obj.obj (op A)) (ρ : F.obj.obj (op B)) :
    ∃ τ : F.obj.obj (op (A ⊔ B)),
      F.obj.map (homOfLE le_sup_left).op τ = σ ∧ F.obj.map (homOfLE le_sup_right).op τ = ρ :=
  ⟨_, TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst F A B ⟨(σ, ρ),
      (CommRingCat.subsingleton_of_isTerminal (F.isTerminalOfEqEmpty hAB.eq_bot)).elim _ _⟩,
    TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd F A B _⟩

/-- At two distinct points of a Hausdorff normalization, identified with each other and with no
other point, near which nothing else is identified, every pair of holomorphic branch germs with
equal values comes from a germ on the quotient. -/
theorem quotientStalkToNode_surjective [T2Space X] {x y : X} (hxy : s x y) (hne : x ≠ y)
    (hclass : ∀ w, s x w → w = x ∨ w = y)
    (hx : ∀ᶠ w in 𝓝 x, ∀ v, s w v → v = w ∨ s x w)
    (hy : ∀ᶠ w in 𝓝 y, ∀ v, s w v → v = w ∨ s x w) :
    Function.Surjective (quotientStalkToNode I s x y hxy) := by
  obtain ⟨N, hxN, hyN, hN⟩ := exists_isPairNhd hclass hx hy
  intro p
  obtain ⟨V₁, hx₁, σ, hσ⟩ :=
    (holomorphicStructureSheaf I X).presheaf.exists_germ_eq (nodeLocalRing.fst I I x y p)
  obtain ⟨V₂, hy₂, ρ, hρ⟩ :=
    (holomorphicStructureSheaf I X).presheaf.exists_germ_eq (nodeLocalRing.snd I I x y p)
  obtain ⟨u, v, hu, hv, hxu, hyv, huv⟩ := t2_separation hne
  -- Glue the two branch representatives on disjoint neighbourhoods of `x` and `y`.
  obtain ⟨A, hxA, hA₁, hAu, hAN⟩ : ∃ A : Opens X, x ∈ A ∧ A ≤ V₁ ∧ (A : Set X) ⊆ u ∧ A ≤ N :=
    ⟨V₁ ⊓ ⟨u, hu⟩ ⊓ N, ⟨⟨hx₁, hxu⟩, hxN⟩, inf_le_left.trans inf_le_left, fun _ h ↦ h.1.2,
      inf_le_right⟩
  obtain ⟨B, hyB, hB₂, hBv, hBN⟩ : ∃ B : Opens X, y ∈ B ∧ B ≤ V₂ ∧ (B : Set X) ⊆ v ∧ B ≤ N :=
    ⟨V₂ ⊓ ⟨v, hv⟩ ⊓ N, ⟨⟨hy₂, hyv⟩, hyN⟩, inf_le_left.trans inf_le_left, fun _ h ↦ h.1.2,
      inf_le_right⟩
  have hxV : x ∈ A ⊔ B := Opens.mem_sup.mpr (Or.inl hxA)
  have hyV : y ∈ A ⊔ B := Opens.mem_sup.mpr (Or.inr hyB)
  obtain ⟨τ, hτA, hτB⟩ := exists_section_sup_of_disjoint (holomorphicStructureSheaf I X)
    (Opens.coe_disjoint.mp (huv.mono hAu hBv))
    ((holomorphicStructureSheaf I X).obj.map (homOfLE hA₁).op σ)
    ((holomorphicStructureSheaf I X).obj.map (homOfLE hB₂).op ρ)
  have hσρ : σ ⟨x, hx₁⟩ = ρ ⟨y, hy₂⟩ := by
    rw [← eval_germ, ← eval_germ, hσ, hρ, nodeLocalRing.eval_fst, nodeLocalRing.eval_snd]
  have h₁ := congrArg (fun t ↦ t ⟨x, hxA⟩) hτA
  have h₂ := congrArg (fun t ↦ t ⟨y, hyB⟩) hτB
  simp only [map_apply] at h₁ h₂
  obtain ⟨f, hfx, hfy⟩ := exists_quotientStalkBranch_eq hxy hN (A ⊔ B)
    (sup_le hAN hBN) hxV hyV τ (h₁.trans (hσρ.trans h₂.symm))
  refine ⟨f, nodeLocalRing.ext ?_ ?_⟩
  · rw [fst_quotientStalkToNode, hfx, ← hσ]
    exact TopCat.Presheaf.germ_ext _ A hxA _ _ hτA
  · rw [snd_quotientStalkToNode, hfy, ← hρ]
    exact TopCat.Presheaf.germ_ext _ B hyB _ _ hτB

/-- **Stalks at nodes.** Let `x ≠ y` be identified with each other and with no other point, and
suppose no further identifications occur near `x` and `y`. Then the branch restrictions identify
the stalk of the quotient sheaf at their common image with the branch-pair node ring. -/
theorem quotientStalkToNode_bijective [T2Space X] {x y : X} (hxy : s x y) (hne : x ≠ y)
    (hclass : ∀ w, s x w → w = x ∨ w = y)
    (hx : ∀ᶠ w in 𝓝 x, ∀ v, s w v → v = w ∨ s x w)
    (hy : ∀ᶠ w in 𝓝 y, ∀ v, s w v → v = w ∨ s x w) :
    Function.Bijective (quotientStalkToNode I s x y hxy) :=
  ⟨quotientStalkToNode_injective hxy hclass hx hy,
    quotientStalkToNode_surjective hxy hne hclass hx hy⟩

end Stalk

end TauCeti.holomorphicStructureSheaf
