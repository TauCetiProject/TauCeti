/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Groupoid.Discrete
public import Mathlib.CategoryTheory.Products.Basic
public import TauCeti.Topology.CategoryTheory.Groupoid.Constructions
public import TauCeti.Topology.CategoryTheory.Groupoid.Effective.Basic
public import TauCeti.Topology.CategoryTheory.Groupoid.Examples
public import TauCeti.Topology.CategoryTheory.Prod

/-!
# The trivial gerbe `K × N ⇒ N`

Let `K` be a group and `N` a topological space. The trivial gerbe `TauCeti.TrivialGerbe K N` is
the product groupoid `SingleObj K × Discrete N` of the point groupoid `[*/K]` and the unit
groupoid of `N`. Its objects are homeomorphic to `N` (`TauCeti.TrivialGerbe.objectHomeomorph`) and
its total arrows to `K × N`, by their label and their source
(`TauCeti.TrivialGerbe.arrowHomeomorph`). Source and target both send `(g, x)` to `x`, the unit
at `x` is `(1, x)`, inversion inverts the label, and composing `(h, x)` followed by `(g, x)` gives
`(g * h, x)`. For a discrete group `K` the source and target are local homeomorphisms, and for a
compact `K` and a Hausdorff `N` the source-target map is proper. Thus for a finite discrete group
`K` and a Hausdorff manifold `N` this is a Hausdorff proper étale groupoid, the standard example of
an orbifold presentation whose isotropy is entirely ineffective.

Every arrow has equal source and target, so every arrow is ineffective
(`TauCeti.TrivialGerbe.ineffectiveArrows_eq_univ`). Consequently:

* the isotropy at every object is all of `K` (`TauCeti.TrivialGerbe.autMulEquiv`), and it equals
  the ineffective kernel (`TauCeti.TrivialGerbe.ineffectiveKernel_eq_top`), whose order `|K|` is
  constant;
* the effective quotient is equivalent to the unit groupoid `Discrete N`
  (`TauCeti.TrivialGerbe.effectiveQuotientEquivalence`), and the coarse space is `N`
  (`TauCeti.TrivialGerbe.isomorphismClassesHomeomorph`);
* when `K` is nontrivial and `N` is nonempty, the trivial gerbe is not equivalent to any thin
  category (`TauCeti.TrivialGerbe.isEmpty_equivalence_of_isThin`), in particular neither to
  `Discrete N` nor to its own effective quotient.

So effective reduction keeps the coarse space but loses the isotropy `K`, and it is not an
equivalence of groupoids. Since a Morita equivalence of topological groupoids is a zigzag of
functors which are in particular equivalences of the underlying groupoids, it is not a Morita
equivalence either.

## References

* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Cambridge Tracts in
  Mathematics 171, Cambridge University Press, 2007, Chapter 1, for ineffective orbifolds and the
  trivial gerbe.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
-/

public section

open CategoryTheory Set Topology

namespace TauCeti

/-- The trivial gerbe `K × N ⇒ N`: the product of the point groupoid `[*/K]` and the unit groupoid
of `N`. Its arrows are pairs `(g, x)` from `x` to `x`, and every label `g` is retained even though
it acts trivially on objects. -/
abbrev TrivialGerbe (K N : Type*) : Type _ := SingleObj K × Discrete N

namespace TrivialGerbe

section Groupoid

variable {K N : Type*} [Group K]

/-- In the trivial gerbe, every arrow is an arrow from an object to itself. -/
theorem left_eq_right (a : Quiver.Total (TrivialGerbe K N)) : a.left = a.right :=
  Prod.ext (Subsingleton.elim _ _) (Discrete.ext (Discrete.eq_of_hom a.hom.2))

/-- The isotropy group of the trivial gerbe at any object is `K`. An automorphism is sent to its
label, and the multiplication of `Aut` is the multiplication of `K`. -/
def autMulEquiv (x : TrivialGerbe K N) : Aut x ≃* K where
  toFun e := e.asIso.hom.1
  invFun g := Aut.of
    { hom := (g, 𝟙 x.2)
      inv := (g⁻¹, 𝟙 x.2)
      hom_inv_id := Prod.ext (by
          rw [prod_comp, SingleObj.comp_as_mul, prod_id, SingleObj.id_as_one, inv_mul_cancel])
        (Subsingleton.elim _ _)
      inv_hom_id := Prod.ext (by
          rw [prod_comp, SingleObj.comp_as_mul, prod_id, SingleObj.id_as_one, mul_inv_cancel])
        (Subsingleton.elim _ _) }
  left_inv e := Aut.ext (Iso.ext (Prod.ext rfl (Subsingleton.elim _ _)))
  right_inv _ := rfl
  map_mul' e e' := by
    simp [SingleObj.comp_as_mul]

@[simp]
theorem autMulEquiv_apply (x : TrivialGerbe K N) (e : Aut x) :
    autMulEquiv x e = e.asIso.hom.1 := (rfl)

@[simp]
theorem autMulEquiv_symm_apply_asIso_hom (x : TrivialGerbe K N) (g : K) :
    ((autMulEquiv x).symm g).asIso.hom = (g, 𝟙 x.2) := (rfl)

/-- When `K` is nontrivial and `N` is nonempty, the trivial gerbe is not equivalent to a thin
category. In particular it is not equivalent to the unit groupoid `Discrete N`, which has the same
objects and the same coarse space but trivial isotropy. -/
theorem isEmpty_equivalence_of_isThin [Nontrivial K] [Nonempty N] {D : Type*} [Category D]
    [Quiver.IsThin D] : IsEmpty (TrivialGerbe K N ≌ D) := by
  refine ⟨fun e ↦ ?_⟩
  let x : TrivialGerbe K N := (SingleObj.star K, ⟨Classical.arbitrary N⟩)
  have : Subsingleton (Aut x) :=
    ⟨fun g h ↦ Aut.ext (Iso.ext (e.functor.map_injective (Subsingleton.elim _ _)))⟩
  exact not_subsingleton K (autMulEquiv x).symm.toEquiv.subsingleton

end Groupoid

section Topology

variable (K N : Type*) [TopologicalSpace N]

/-- The objects of the trivial gerbe are homeomorphic to `N`. -/
def objectHomeomorph : TrivialGerbe K N ≃ₜ N where
  toFun x := x.2.as
  invFun x := (SingleObj.star K, ⟨x⟩)
  left_inv _ := Prod.ext (Subsingleton.elim _ _) rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_dom.comp continuous_snd
  continuous_invFun := continuous_const.prodMk (continuous_induced_rng.mpr continuous_id)

@[simp]
theorem objectHomeomorph_apply (x : TrivialGerbe K N) : objectHomeomorph K N x = x.2.as := (rfl)

@[simp]
theorem objectHomeomorph_symm_apply (x : N) :
    (objectHomeomorph K N).symm x = (SingleObj.star K, ⟨x⟩) := (rfl)

variable [Group K]

/-- The coarse space of the trivial gerbe is `N`. -/
def isomorphismClassesHomeomorph : Quotient (isIsomorphicSetoid (TrivialGerbe K N)) ≃ₜ N where
  toFun := Quotient.lift (objectHomeomorph K N) fun _ _ ⟨e⟩ ↦ Discrete.eq_of_hom e.hom.2
  invFun x := Quotient.mk _ ((objectHomeomorph K N).symm x)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h x => exact congrArg (Quotient.mk _) ((objectHomeomorph K N).symm_apply_apply x)
  right_inv _ := rfl
  continuous_toFun := (objectHomeomorph K N).continuous.quotient_lift _
  continuous_invFun := continuous_quotient_mk'.comp (objectHomeomorph K N).symm.continuous

@[simp]
theorem isomorphismClassesHomeomorph_mk (x : TrivialGerbe K N) :
    isomorphismClassesHomeomorph K N (Quotient.mk _ x) = x.2.as := (rfl)

@[simp]
theorem isomorphismClassesHomeomorph_symm_apply (x : N) :
    (isomorphismClassesHomeomorph K N).symm x =
      Quotient.mk (isIsomorphicSetoid (TrivialGerbe K N)) ((objectHomeomorph K N).symm x) :=
  (rfl)

variable [TopologicalSpace K]

/-- The total arrows of the trivial gerbe are homeomorphic to `K × N`, by their label and their
source. -/
def arrowHomeomorph : Quiver.Total (TrivialGerbe K N) ≃ₜ K × N :=
  (totalProdHomeomorph (SingleObj K) (Discrete N)).trans
    ((OneObjectGroupoid.arrowHomeomorph K).prodCongr (UnitGroupoid.arrowHomeomorph N))

@[simp]
theorem arrowHomeomorph_apply (a : Quiver.Total (TrivialGerbe K N)) :
    arrowHomeomorph K N a = (a.hom.1, a.left.2.as) := by
  simp [arrowHomeomorph, totalProdHomeomorph_apply]

@[simp]
theorem arrowHomeomorph_symm_apply (p : K × N) :
    (arrowHomeomorph K N).symm p =
      ⟨(SingleObj.star K, ⟨p.2⟩), (SingleObj.star K, ⟨p.2⟩), (p.1, 𝟙 _)⟩ :=
  (arrowHomeomorph K N).symm_apply_eq.mpr (by rw [arrowHomeomorph_apply]; rfl)

variable {K N}

/-- The source of an arrow `(g, x)` is `x`. -/
theorem objectHomeomorph_left (a : Quiver.Total (TrivialGerbe K N)) :
    objectHomeomorph K N a.left = (arrowHomeomorph K N a).2 := by
  simp

/-- The target of an arrow `(g, x)` is `x`. -/
theorem objectHomeomorph_right (a : Quiver.Total (TrivialGerbe K N)) :
    objectHomeomorph K N a.right = (arrowHomeomorph K N a).2 := by
  rw [← left_eq_right, objectHomeomorph_left]

/-- The unit at `x` is the arrow `(1, x)`. -/
theorem arrowHomeomorph_id (x : TrivialGerbe K N) :
    arrowHomeomorph K N ⟨x, x, 𝟙 x⟩ = (1, objectHomeomorph K N x) := by
  rw [arrowHomeomorph_apply, prod_id, SingleObj.id_as_one, objectHomeomorph_apply]

/-- Composing `(h, x)` followed by `(g, x)` gives `(g * h, x)`: categorical composition reverses
the order of the labels. -/
theorem arrowHomeomorph_comp (a b : Quiver.Total (TrivialGerbe K N)) (h : a.right = b.left) :
    arrowHomeomorph K N (a.comp b h) =
      ((arrowHomeomorph K N b).1 * (arrowHomeomorph K N a).1, (arrowHomeomorph K N a).2) := by
  obtain ⟨⟨⟨⟩, x⟩, ⟨⟨⟩, y⟩, f⟩ := a
  obtain ⟨⟨⟨⟩, y'⟩, ⟨⟨⟩, z⟩, g⟩ := b
  cases h
  rw [Quiver.Total.mk_comp_mk, arrowHomeomorph_apply, arrowHomeomorph_apply,
    arrowHomeomorph_apply, prod_comp, SingleObj.comp_as_mul]

/-- Inverting the arrow `(g, x)` gives `(g⁻¹, x)`. -/
theorem arrowHomeomorph_inverse (a : Quiver.Total (TrivialGerbe K N)) :
    arrowHomeomorph K N ⟨a.right, a.left, inv a.hom⟩ =
      ((arrowHomeomorph K N a).1⁻¹, (arrowHomeomorph K N a).2) := by
  obtain ⟨⟨⟨⟩, x⟩, ⟨⟨⟩, y⟩, f⟩ := a
  obtain rfl : x = y := Discrete.ext (Discrete.eq_of_hom f.2)
  have h := congrArg Prod.fst (IsIso.hom_inv_id f)
  rw [prod_comp, prod_id, SingleObj.comp_as_mul, SingleObj.id_as_one] at h
  rw [arrowHomeomorph_apply, arrowHomeomorph_apply, eq_inv_of_mul_eq_one_left h]

/-- Every arrow of the trivial gerbe is ineffective, whatever the topologies of `K` and `N`. -/
@[simp]
theorem ineffectiveArrows_eq_univ : ineffectiveArrows (TrivialGerbe K N) = univ :=
  eq_univ_of_forall fun _ ↦ mem_ineffectiveArrows_iff.mpr (.of_forall left_eq_right)

/-- Any two parallel arrows of the trivial gerbe are related by the germ relation: distinct labels
induce the same germ on objects. -/
theorem germRel_of_parallel {x y : TrivialGerbe K N} (f f' : x ⟶ y) :
    germRel (TrivialGerbe K N) f f' := by
  simp

/-- The effective quotient of the trivial gerbe is thin: all parallel arrows are identified. -/
instance : Quiver.IsThin (EffectiveQuotient (TrivialGerbe K N)) := fun x y ↦ by
  refine ⟨fun f f' ↦ ?_⟩
  obtain ⟨f, rfl⟩ := (toEffectiveQuotient (TrivialGerbe K N)).map_surjective f
  obtain ⟨f', rfl⟩ := (toEffectiveQuotient (TrivialGerbe K N)).map_surjective f'
  exact CategoryTheory.Quotient.sound _ (germRel_of_parallel f f')

variable (K N) in
/-- The functor from the effective quotient of the trivial gerbe to the unit groupoid of `N`
induced by forgetting the label. -/
def effectiveQuotientToDiscrete : EffectiveQuotient (TrivialGerbe K N) ⥤ Discrete N :=
  CategoryTheory.Quotient.lift _ (CategoryTheory.Prod.snd (SingleObj K) (Discrete N))
    fun _ _ _ _ _ ↦ Subsingleton.elim _ _

/-- Forgetting the label after passing to the effective quotient is the second projection. -/
@[simp]
theorem toEffectiveQuotient_comp_effectiveQuotientToDiscrete :
    toEffectiveQuotient (TrivialGerbe K N) ⋙ effectiveQuotientToDiscrete K N =
      CategoryTheory.Prod.snd (SingleObj K) (Discrete N) :=
  CategoryTheory.Quotient.lift_spec _ _ _

@[simp]
theorem effectiveQuotientToDiscrete_obj_toEffectiveQuotient_obj (x : TrivialGerbe K N) :
    (effectiveQuotientToDiscrete K N).obj ((toEffectiveQuotient (TrivialGerbe K N)).obj x) =
      x.2 := (rfl)

/-- Forgetting the label is faithful on the effective quotient, which is thin. -/
instance : (effectiveQuotientToDiscrete K N).Faithful where
  map_injective _ := Subsingleton.elim _ _

/-- Forgetting the label is full: an arrow of `Discrete N` is an equality of objects. -/
instance : (effectiveQuotientToDiscrete K N).Full where
  map_surjective {x y} f := by
    obtain ⟨x, rfl⟩ := (EffectiveQuotient.objEquiv _).surjective x
    obtain ⟨y, rfl⟩ := (EffectiveQuotient.objEquiv _).surjective y
    have h := Discrete.eq_of_hom f
    simp only [EffectiveQuotient.objEquiv_apply,
      effectiveQuotientToDiscrete_obj_toEffectiveQuotient_obj] at h
    exact ⟨eqToHom (congrArg _ (Prod.ext (Subsingleton.elim _ _) (Discrete.ext h))),
      Subsingleton.elim _ _⟩

/-- Every point of `N` is the image of an object of the effective quotient. -/
instance : (effectiveQuotientToDiscrete K N).EssSurj where
  mem_essImage y :=
    ⟨(toEffectiveQuotient (TrivialGerbe K N)).obj (SingleObj.star K, y), ⟨eqToIso (by simp)⟩⟩

/-- Forgetting the label is an equivalence from the effective quotient to `Discrete N`. -/
instance : (effectiveQuotientToDiscrete K N).IsEquivalence where

variable (K N) in
/-- The effective quotient of the trivial gerbe is equivalent to the unit groupoid of `N`: effective
reduction discards the whole isotropy `K`. -/
noncomputable def effectiveQuotientEquivalence :
    EffectiveQuotient (TrivialGerbe K N) ≌ Discrete N :=
  (effectiveQuotientToDiscrete K N).asEquivalence

@[simp]
theorem effectiveQuotientEquivalence_functor :
    (effectiveQuotientEquivalence K N).functor = effectiveQuotientToDiscrete K N := (rfl)

/-- For a compact group `K`, for instance a finite discrete one, and a Hausdorff space `N`, the
source-target map of the trivial gerbe is proper. -/
theorem isProperMap_source_target [CompactSpace K] [T2Space N] :
    IsProperMap fun a : Quiver.Total (TrivialGerbe K N) ↦ (a.left, a.right) := by
  -- The source-target map is the projection `K × N → N`, proper as `K` is compact, followed by
  -- the diagonal of `N`, a closed embedding as `N` is Hausdorff.
  have hdiag : IsProperMap fun x : N ↦ (x, x) :=
    IsClosedEmbedding.isProperMap
      ⟨isEmbedding_graph continuous_id, Set.range_diag (α := N) ▸ isClosed_diagonal⟩
  convert ((objectHomeomorph K N).symm.prodCongr (objectHomeomorph K N).symm).isProperMap.comp
    (hdiag.comp (isProperMap_snd_of_compactSpace.comp (arrowHomeomorph K N).isProperMap)) using 1
  funext a
  have h := (objectHomeomorph K N).eq_symm_apply.mpr (objectHomeomorph_left a)
  exact Prod.ext h ((left_eq_right a).symm.trans h)

section Etale

variable [DiscreteTopology K]

/-- For a discrete group `K`, the source of the trivial gerbe is a local homeomorphism. -/
theorem isLocalHomeomorph_source :
    IsLocalHomeomorph
      (Quiver.Total.left : Quiver.Total (TrivialGerbe K N) → TrivialGerbe K N) := by
  -- The source is the projection `K × N → N` read through the two homeomorphisms.
  convert (objectHomeomorph K N).symm.isLocalHomeomorph.comp
    (isLocalHomeomorph_snd.comp (arrowHomeomorph K N).isLocalHomeomorph) using 1
  exact funext fun a ↦ (objectHomeomorph K N).eq_symm_apply.mpr (objectHomeomorph_left a)

/-- For a discrete group `K`, the target of the trivial gerbe is a local homeomorphism. -/
theorem isLocalHomeomorph_target :
    IsLocalHomeomorph
      (Quiver.Total.right : Quiver.Total (TrivialGerbe K N) → TrivialGerbe K N) := by
  convert isLocalHomeomorph_source (K := K) (N := N) using 1
  exact funext fun a ↦ (left_eq_right a).symm

end Etale

section IneffectiveKernel

variable [IsTopologicalGroup K]
  (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total (TrivialGerbe K N) → TrivialGerbe K N))

/-- The ineffective kernel of the trivial gerbe is the whole isotropy group at every object. -/
@[simp]
theorem ineffectiveKernel_eq_top (x : TrivialGerbe K N) : ineffectiveKernel hs x = ⊤ := by
  ext
  simp

/-- The ineffective kernel of the trivial gerbe has order `|K|` at every object. -/
theorem card_ineffectiveKernel (x : TrivialGerbe K N) :
    Nat.card (ineffectiveKernel hs x) = Nat.card K := by
  rw [ineffectiveKernel_eq_top, Subgroup.card_top]
  exact Nat.card_congr (autMulEquiv x).toEquiv

/-- On the coarse space of the trivial gerbe, the order of the ineffective kernel is the constant
function `|K|`. -/
@[simp]
theorem coarseCardIneffectiveKernel_eq :
    coarseCardIneffectiveKernel hs = fun _ ↦ Nat.card K := by
  ext q
  induction q using Quotient.inductionOn with
  | h x => exact (coarseCardIneffectiveKernel_mk hs x).trans (card_ineffectiveKernel hs x)

end IneffectiveKernel

end Topology

end TrivialGerbe

end TauCeti
