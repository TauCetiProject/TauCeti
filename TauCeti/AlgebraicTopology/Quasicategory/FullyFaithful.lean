/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.FullSubcategory
public import TauCeti.AlgebraicTopology.Quasicategory.Isom
public import TauCeti.AlgebraicTopology.Quasicategory.PointwiseEquivalence
public import TauCeti.AlgebraicTopology.Quasicategory.RightMappingSpace
public import TauCeti.AlgebraicTopology.SimplicialSet.Realization.PiZero
public import TauCeti.AlgebraicTopology.SimplicialSet.PrismRealization
public import TauCeti.AlgebraicTopology.SimplicialSet.WeakHomotopyEquivalence.TrivialFibration

/-!
# Fully faithful maps of simplicial sets

A map of simplicial sets `f : X ⟶ Y` is *fully faithful* (`SSet.IsFullyFaithful f`) when, for all
vertices `x` and `y` of `X`, the induced map of right mapping spaces
`Hom^R_X(x, y) ⟶ Hom^R_Y(f x, f y)` is a weak equivalence for the Kan–Quillen model structure.
For quasicategories this is the notion of a fully faithful functor of `∞`-categories: the right
mapping spaces model the spaces of maps, and a weak equivalence is an isomorphism in the homotopy
category of spaces. It is the mapping-space condition in the characterization of the categorical
equivalences of quasicategories as the fully faithful and essentially surjective maps; that
categorical equivalences are fully faithful is
`SSet.QCat.IsCategoricalEquivalence.isFullyFaithful`.

Fully faithful maps are closed under composition and have the right cancellation property, and
every isomorphism is fully faithful. So is every trivial fibration: it induces trivial fibrations
of right mapping spaces (`SSet.rightMappingSpace.rlp_map`), since a lifting problem against the
map of right mapping spaces is, through `SSet.rightMappingSpace.sliceFiberIso`, one against a
relative slice map along the empty diagram. The inclusion of a full enhanced subcategory is fully
faithful: a simplex of a right mapping space has only its two endpoints as vertices, so the right
mapping spaces of the full enhanced subcategory are those of the ambient simplicial set. The right
mapping spaces of the nerve of a category are discrete on its morphisms, and the nerve of a fully
faithful functor is fully faithful.

Weak equivalences are bijective on connected components, and the connected components of the
right mapping spaces of a quasicategory are the morphisms of its homotopy category
(`SSet.rightMappingSpace.π₀Equiv`). Hence a fully faithful map of quasicategories is fully faithful
on homotopy categories, and, if it is also essentially surjective on homotopy categories, it induces
an equivalence of homotopy categories. Since the equivalences of a quasicategory are the edges
whose classes are invertible in the homotopy category, a fully faithful map of quasicategories
reflects equivalences.

Full faithfulness is invariant under natural equivalence. A natural transformation `α : F ⟶ G` of
maps `X ⟶ Y` into a quasicategory which is an equivalence of `Fun(X, Y)` has invertible components
(`SSet.Edge.isEquivalence_iff_forall_isEquivalence_map_evalAt`), so it is a map from `X` to the
quasicategory of equivalences `SSet.isom Y` whose evaluations at the two vertices of `Δ[1]` are
`F` and `G`. These evaluations are trivial fibrations (`SSet.isom.rlp_evalAt`), hence induce weak
homotopy equivalences of right mapping spaces, and two out of three shows that `F` and `G` induce
weak homotopy equivalences, or weak equivalences, of right mapping spaces together.

## Main definitions

* `SSet.IsFullyFaithful f`: the maps induced by `f` on right mapping spaces are weak equivalences.

## Main results

* `SSet.IsFullyFaithful.comp`, `SSet.IsFullyFaithful.of_comp`: composition and right
  cancellation.
* `SSet.IsFullyFaithful.fullEnhancedSubcategory_ι`: the inclusion of a full enhanced subcategory is
  fully faithful.
* `SSet.IsFullyFaithful.nerveMap`: the nerve of a fully faithful functor is fully faithful.
* `SSet.IsFullyFaithful.faithful_mapHomotopyCategory`,
  `SSet.IsFullyFaithful.full_mapHomotopyCategory`: a fully faithful map of quasicategories is fully
  faithful on homotopy categories, and `SSet.IsFullyFaithful.isEquivalence_mapHomotopyCategory`:
  it induces an equivalence of homotopy categories when it is also essentially surjective on them.
* `SSet.Edge.isEquivalence_map_iff_of_isFullyFaithful`: a fully faithful map of quasicategories
  reflects equivalences.
* `SSet.rightMappingSpace.rlp_map`, `SSet.IsFullyFaithful.of_rlp_monomorphisms`: a trivial
  fibration induces trivial fibrations of right mapping spaces, and is fully faithful.
* `SSet.rightMappingSpace.isWeakHomotopyEquivalence_map_iff_of_isEquivalence`,
  `SSet.rightMappingSpace.weakEquivalence_map_iff_of_isEquivalence`,
  `SSet.isFullyFaithful_iff_of_isEquivalence`: naturally equivalent maps into a quasicategory
  induce weak homotopy equivalences, or weak equivalences, of right mapping spaces together, and
  are fully faithful together.

## References

* J. Lurie, *Higher Topos Theory*, Definition 1.2.10.1 and §1.2.2.
-/

public section

open CategoryTheory HomotopicalAlgebra Opposite Simplicial

open scoped SSet.modelCategoryQuillen

universe u v w

namespace SSet

variable {X Y Z : SSet.{u}}

namespace rightMappingSpace

open Limits MorphismProperty

/-- For a trivial fibration `p : X ⟶ Y`, the relative slice map
`X_{/σ} ⟶ X_{/∅} ×_{Y_{/∅}} Y_{/σ ≫ p}` along the empty diagram is a trivial fibration: by the
universal property of slices, it lifts against `∂Δ[n] ⟶ Δ[n]` because `p` lifts against the
pushout-join `(∂Δ[n] ⋆ Δ[0]) ∪ Δ[n] ⟶ Δ[n] ⋆ Δ[0]`, a monomorphism. -/
private lemma rlp_restrictionMap_bot {p : X ⟶ Y} (hp : (monomorphisms SSet.{u}).rlp p)
    (σ : Δ[0] ⟶ X) :
    (monomorphisms SSet.{u}).rlp
      (slice.restrictionMap (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι p σ) := by
  rw [rlp_monomorphisms]
  rintro _ _ _ ⟨n⟩
  have := hp _ (monomorphisms.infer_property
    (Subcomplex.unionJoin ∂Δ[n] (⊥ : (Δ[0] : SSet.{u}).Subcomplex)).ι)
  exact (slice.forall_hasLiftingProperty_restrictionMap_iff_of_isPushout ∂Δ[n].ι _ p
    (Subcomplex.unionJoin.isPushout _ _) (Subcomplex.unionJoin.ι₁_ι _ _)
    (Subcomplex.unionJoin.ι₂_ι _ _)).2 this σ

/-- **A trivial fibration induces trivial fibrations of right mapping spaces**: if
`p : X ⟶ Y` has the right lifting property with respect to every monomorphism, then so does
`Hom^R_X(x, y) ⟶ Hom^R_Y(p x, p y)`. Through `SSet.rightMappingSpace.sliceFiberIso`, a lifting
problem against it is one against the relative slice map
`X_{/y} ⟶ X ×_Y Y_{/p y}` along the empty diagram, which lifts against monomorphisms since the
pushout-joins of monomorphisms with `∅ ⟶ Δ[0]` are monomorphisms. -/
theorem rlp_map {p : X ⟶ Y} (hp : (monomorphisms SSet.{u}).rlp p) (x y : X _⦋0⦌) :
    (monomorphisms SSet.{u}).rlp (map x y p) := by
  let σ : Δ[0] ⟶ X := yonedaEquiv.symm y
  let i := (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι
  have hL : ¬ (((⊥ : (Δ[0] : SSet.{u}).Subcomplex) : SSet.{u})).Nonempty := by
    rintro ⟨⟨_, ⟨⟩⟩⟩
  have hr := rlp_restrictionMap_bot hp σ
  -- A lifting problem against `map x y p` is one against the relative slice map, whose first
  -- component is constant at `x`: the right mapping spaces are the fibres over `x` and `p x`.
  intro A B j hj
  have := hr j hj
  refine ⟨fun {t b} sq ↦ ?_⟩
  -- The slices over the empty diagram are `X` and `Y`; `fE` and `fB` include the right mapping
  -- spaces as the fibres of the slices over `x` and `p x`, and `φ` identifies two slices of `Y`.
  have : IsIso (slice.π (i ≫ σ)) := slice.isIso_π _ hL
  have : IsIso (slice.π (i ≫ σ ≫ p)) := slice.isIso_π _ hL
  let fE := (sliceFiberIso x y).inv ≫ (fiber (slice.π σ) x).ι
  let fB := (sliceFiberIso (p.app _ x) (p.app _ y)).inv ≫
    (fiber (slice.π (yonedaEquiv.symm (p.app _ y))) (p.app _ x)).ι
  have hσp : 𝟙 Δ[0] ≫ yonedaEquiv.symm (p.app _ y) ≫ 𝟙 Y = σ ≫ p := by simp [σ]
  let φ : slice (yonedaEquiv.symm (p.app _ y)) ⟶ slice (σ ≫ p) := slice.map (𝟙 _) (𝟙 _) hσp
  let u : B ⟶ slice (i ≫ σ) := const x ≫ inv (slice.π (i ≫ σ))
  have hfB : fB ≫ slice.π _ = const (p.app _ x) := by
    simp only [fB, Category.assoc, fiber.ι_comp, comp_const]
  have hfE : fE ≫ slice.π σ = const x := by
    simp only [fE, Category.assoc, fiber.ι_comp, comp_const]
  let mE : slice (i ≫ σ) ⟶ slice (i ≫ σ ≫ p) := slice.map (𝟙 _) p (by simp)
  let mB : slice (σ ≫ p) ⟶ slice (i ≫ σ ≫ p) := slice.map i (𝟙 _) (by simp)
  have w : u ≫ mE = (b ≫ fB ≫ φ) ≫ mB := by
    rw [← cancel_mono (slice.π (i ≫ σ ≫ p))]
    simp only [u, φ, mE, mB, Category.assoc, slice.map_π, IsIso.inv_hom_id_assoc, Category.comp_id]
    rw [hfB, const_comp, comp_const]
  -- The lifting problem against the relative slice map.
  have hnat := sliceFiberIso_inv_comp_map x y p
  have hm : (slice.map (𝟙 _) p (by simp) : slice σ ⟶ slice (σ ≫ p)) =
      slice.map (𝟙 Δ[0]) p (by rw [Category.id_comp, yonedaEquiv_symm_comp]) ≫ φ := by
    rw [slice.map_comp]
    congr 1
  have sq' : CommSq (t ≫ fE) j (slice.restrictionMap i p σ) (pullback.lift u (b ≫ fB ≫ φ) w) := by
    refine ⟨pullback.hom_ext ?_ ?_⟩
    · rw [← cancel_mono (slice.π (i ≫ σ))]
      simp only [Category.assoc, slice.restrictionMap_fst, pullback.lift_fst, slice.map_π,
        Category.comp_id, u, IsIso.inv_hom_id, hfE, comp_const]
    · simp only [Category.assoc, slice.restrictionMap_snd, pullback.lift_snd]
      rw [hm, ← Category.assoc fE, show fE ≫ _ = _ ≫ fB from hnat, Category.assoc,
        reassoc_of% sq.w]
  have hl : sq'.lift ≫ slice.π σ = const x := by
    have h₁ : slice.restrictionMap i p σ ≫ pullback.fst _ _ ≫ slice.π (i ≫ σ) = slice.π σ := by
      rw [slice.restrictionMap_fst_assoc, slice.map_π, Category.comp_id]
    rw [← h₁, reassoc_of% sq'.fac_right, pullback.lift_fst_assoc, Category.assoc,
      IsIso.inv_hom_id, Category.comp_id]
  -- Its solution lies in the fibre over `x`, hence in the right mapping space.
  have : Mono fB := by dsimp [fB]; infer_instance
  have : IsIso φ := by dsimp [φ]; infer_instance
  refine ⟨⟨{ l := fiber.lift sq'.lift (slice.π σ) x hl ≫ (sliceFiberIso x y).hom
             fac_left := ?_
             fac_right := ?_ }⟩⟩
  · rw [← cancel_mono (sliceFiberIso x y).inv, Category.assoc, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, ← cancel_mono (fiber (slice.π σ) x).ι, Category.assoc, fiber.lift_ι,
      sq'.fac_left, Category.assoc]
  · have hnat' : map x y p ≫ fB = fE ≫ slice.map (𝟙 Δ[0]) p
        (by rw [Category.id_comp, yonedaEquiv_symm_comp]) := hnat.symm
    rw [← cancel_mono fB, ← cancel_mono φ]
    simp only [Category.assoc]
    rw [reassoc_of% hnat']
    simp only [fE, Category.assoc, Iso.hom_inv_id_assoc, fiber.lift_ι_assoc]
    rw [← hm, ← slice.restrictionMap_snd i p σ, reassoc_of% sq'.fac_right, pullback.lift_snd]

end rightMappingSpace

/-- A map of simplicial sets `f : X ⟶ Y` is fully faithful when, for all vertices `x` and `y` of
`X`, the induced map of right mapping spaces `Hom^R_X(x, y) ⟶ Hom^R_Y(f x, f y)` is a weak
equivalence. -/
class IsFullyFaithful (f : X ⟶ Y) : Prop where
  weakEquivalence_map (x y : X _⦋0⦌) : WeakEquivalence (rightMappingSpace.map x y f)

attribute [instance] IsFullyFaithful.weakEquivalence_map

namespace IsFullyFaithful

variable (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A map inducing isomorphisms on all right mapping spaces is fully faithful. -/
lemma of_isIso_map (h : ∀ x y : X _⦋0⦌, IsIso (rightMappingSpace.map x y f)) :
    IsFullyFaithful f :=
  ⟨fun x y ↦ have := h x y; inferInstance⟩

instance of_isIso [IsIso f] : IsFullyFaithful f :=
  of_isIso_map f fun _ _ ↦ inferInstance

variable {f} in
/-- A trivial fibration, a map with the right lifting property with respect to every monomorphism,
is fully faithful: it induces trivial fibrations of right mapping spaces. -/
lemma of_rlp_monomorphisms (hf : (MorphismProperty.monomorphisms SSet.{u}).rlp f) :
    IsFullyFaithful f :=
  ⟨fun x y ↦ modelCategoryQuillen.weakEquivalence_of_rlp_monomorphisms
    (rightMappingSpace.rlp_map hf x y)⟩

instance comp [IsFullyFaithful f] [IsFullyFaithful g] : IsFullyFaithful (f ≫ g) :=
  ⟨fun x y ↦ by
    rw [rightMappingSpace.map_comp]
    infer_instance⟩

/-- If `g` and `f ≫ g` are fully faithful, so is `f`. -/
lemma of_comp [IsFullyFaithful g] [IsFullyFaithful (f ≫ g)] : IsFullyFaithful f :=
  ⟨fun x y ↦ by
    have := weakEquivalence_map (f := f ≫ g) x y
    rw [rightMappingSpace.map_comp] at this
    exact weakEquivalence_of_postcomp _ (rightMappingSpace.map (f.app _ x) (f.app _ y) g)⟩

/-- The inclusion of a full enhanced subcategory is fully faithful: a simplex of a right mapping
space between vertices satisfying `P` has only these two vertices, so it lies in the full enhanced
subcategory. -/
instance fullEnhancedSubcategory_ι (P : X _⦋0⦌ → Prop) :
    IsFullyFaithful (X.fullEnhancedSubcategory P).ι :=
  of_isIso_map _ fun x y ↦ rightMappingSpace.isIso_map_ι x y fun n s ↦
    (mem_fullEnhancedSubcategory_obj_iff_forall_fin P (s.val : X _⦋n + 1⦌)).2 fun i ↦ by
      cases i using Fin.lastCases with
      | last =>
        rw [rightMappingSpace.map_const_last s]
        exact (mem_fullEnhancedSubcategory_obj_zero_iff P y.val).1 y.property
      | cast j =>
        rw [rightMappingSpace.map_const_castSucc s j]
        exact (mem_fullEnhancedSubcategory_obj_zero_iff P x.val).1 x.property

/-- The nerve of a fully faithful functor is fully faithful. -/
instance nerveMap {C D : Type v} [Category.{w} C] [Category.{w} D] (F : C ⥤ D) [F.Full]
    [F.Faithful] : IsFullyFaithful (nerveMap F) := by
  refine of_isIso_map _ fun x y ↦ (rightMappingSpace.isIso_map_iff_bijective _).2 ?_
  -- Edges of nerves are morphisms, on which the nerve of `F` acts by `F.map`.
  obtain ⟨a, rfl⟩ := nerveEquiv.symm.surjective x
  obtain ⟨b, rfl⟩ := nerveEquiv.symm.surjective y
  have hE : Function.Bijective (nerve.edgeMk : (a ⟶ b) → _) :=
    ⟨Function.LeftInverse.injective (g := nerve.homEquiv) fun _ ↦ nerve.homEquiv_edgeMk _,
      nerve.edgeMk_surjective⟩
  have hcomp : nerve.homEquiv ∘ (fun e ↦ e.map (CategoryTheory.nerveMap F)) ∘ nerve.edgeMk =
      fun f : a ⟶ b ↦ F.map f :=
    funext fun f ↦ nerve.homEquiv_edgeMk_map_nerveMap f F
  exact (Function.Bijective.of_comp_iff _ hE).1
    ((Function.Bijective.of_comp_iff' nerve.homEquiv.bijective _).1
      (hcomp ▸ ⟨F.map_injective, F.map_surjective⟩))

/-! ### Homotopy categories -/

section HomotopyCategory

variable [X.Quasicategory] [Y.Quasicategory] [IsFullyFaithful f]

/-- Under `rightMappingSpace.π₀Equiv`, the action of `mapHomotopyCategory f` on morphisms from `x`
to `y` is the bijection induced on connected components by the weak equivalence
`Hom^R_X(x, y) ⟶ Hom^R_Y(f x, f y)`. -/
private theorem bijective_map_mapHomotopyCategory (x y : X _⦋0⦌) :
    Function.Bijective ((mapHomotopyCategory f).map :
      (HomotopyCategory.mk x ⟶ HomotopyCategory.mk y) → _) := by
  have h : ((mapHomotopyCategory f).map :
      (HomotopyCategory.mk x ⟶ HomotopyCategory.mk y) → _) =
      rightMappingSpace.π₀Equiv _ _ ∘ mapπ₀ (rightMappingSpace.map x y f) ∘
        (rightMappingSpace.π₀Equiv x y).symm := by
    funext φ
    rw [Function.comp_apply, Function.comp_apply, rightMappingSpace.π₀Equiv_mapπ₀_map,
      Equiv.apply_symm_apply]
  rw [h]
  exact (Equiv.bijective _).comp
    ((bijective_mapπ₀_of_weakEquivalence _).comp (Equiv.bijective _))

/-- A fully faithful map of quasicategories is faithful on homotopy categories. -/
instance faithful_mapHomotopyCategory : (mapHomotopyCategory f).Faithful where
  map_injective {a b} := by
    induction a with | mk x => ?_
    induction b with | mk y => ?_
    exact (bijective_map_mapHomotopyCategory f x y).1

/-- A fully faithful map of quasicategories is full on homotopy categories. -/
instance full_mapHomotopyCategory : (mapHomotopyCategory f).Full where
  map_surjective {a b} := by
    induction a with | mk x => ?_
    induction b with | mk y => ?_
    exact (bijective_map_mapHomotopyCategory f x y).2

/-- A fully faithful and essentially surjective map of quasicategories induces an equivalence of
homotopy categories. -/
instance isEquivalence_mapHomotopyCategory [(mapHomotopyCategory f).EssSurj] :
    (mapHomotopyCategory f).IsEquivalence where

end HomotopyCategory

end IsFullyFaithful

/-! ### Naturally equivalent maps -/

section isom

open MonoidalCategory CartesianMonoidalCategory MonoidalClosed

variable {F G : ((ihom X).obj Y) _⦋0⦌}

/-- A natural transformation `α : F ⟶ G` of maps `X ⟶ Y`, an edge of `Fun(X, Y)`, as a map
`X ⟶ Fun(Δ[1], Y)` sending a vertex `x` of `X` to the component of `α` at `x`. -/
private noncomputable def componentMap (α : Edge F G) : X ⟶ (ihom Δ[1]).obj Y :=
  curry ((β_ Δ[1] X).hom ≫ uncurry (yonedaEquiv.symm α.edge))

/-- Evaluating `componentMap α` at a vertex `v` of `Δ[1]` is the map `X ⟶ Y` given by `α` at `v`. -/
private lemma componentMap_evalAt (α : Edge F G) (v : Δ[1] _⦋0⦌) :
    componentMap α ≫ evalAt v Y = ihomObj₀Equiv X Y ((yonedaEquiv.symm α.edge).app _ v) := by
  rw [componentMap, curry_evalAt, lift_braiding_hom_assoc, ihomObj₀Equiv_app]

/-- The edge of `Y` given by `componentMap α` at a vertex `x` of `X` is the component of `α`. -/
private lemma ihomObj₀Equiv_componentMap_app (α : Edge F G) (x : X _⦋0⦌) :
    ihomObj₀Equiv Δ[1] Y ((componentMap α).app _ x) = yonedaEquiv.symm α.edge ≫ evalAt x Y := by
  rw [ihomObj₀Equiv_app, componentMap, uncurry_curry, ← Category.assoc, lift_braiding_hom,
    evalAt_eq, ← Category.assoc, comp_lift, comp_const, Category.comp_id, uncurry_eq,
    ← Category.assoc, lift_whiskerLeft, Category.id_comp]

/-- A natural transformation whose components are equivalences factors through the quasicategory
of equivalences `SSet.isom Y`. -/
private lemma range_componentMap_le [Y.Quasicategory] (α : Edge F G) (hα : α.IsEquivalence) :
    Subcomplex.range (componentMap α) ≤ isom Y := by
  refine (range_le_isom_iff _).2 fun x ↦ ?_
  have h : stdSimplex.edge 1 0 1 (Fin.zero_le _) = yonedaEquiv (𝟙 Δ[1]) := by
    ext i
    fin_cases i <;> rfl
  refine (Edge.isEquivalence_iff_of_edge_eq (e' := α.map (evalAt x Y)) ?_).2
    ((Edge.isEquivalence_iff_forall_isEquivalence_map_evalAt α).1 hα x)
  rw [Edge.mk'_edge, ihomObj₀Equiv_componentMap_app, h, ← yonedaEquiv_comp, Category.id_comp,
    yonedaEquiv_comp, Equiv.apply_symm_apply, Edge.map_edge]

/-- The vertices of `Δ[1]` correspond to the endpoints of a natural transformation. -/
private lemma yonedaEquiv_symm_app_obj₀Equiv_symm (α : Edge F G) :
    (yonedaEquiv.symm α.edge).app _ (stdSimplex.obj₀Equiv.symm 0) = F ∧
      (yonedaEquiv.symm α.edge).app _ (stdSimplex.obj₀Equiv.symm 1) = G := by
  rw [← Equiv.apply_symm_apply yonedaEquiv (stdSimplex.obj₀Equiv.symm 0),
    ← Equiv.apply_symm_apply yonedaEquiv (stdSimplex.obj₀Equiv.symm 1), ← yonedaEquiv_comp,
    ← yonedaEquiv_comp, yonedaEquiv_symm_zero, yonedaEquiv_symm_zero, ← stdSimplex.δ_one_eq_const,
    ← stdSimplex.δ_zero_eq_const, stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp,
    Equiv.apply_symm_apply]
  exact ⟨α.src_eq, α.tgt_eq⟩

/-- For a natural transformation `α : F ⟶ G` of maps `X ⟶ Y` into a quasicategory whose
components are equivalences, and vertices `x` and `y` of `X`, the maps of right mapping spaces
`Hom^R_X(x, y) ⟶ Hom^R_Y(F x, F y)` and `Hom^R_X(x, y) ⟶ Hom^R_Y(G x, G y)` induced by `F` and
`G` factor through one map to a right mapping space of the quasicategory of equivalences
`SSet.isom Y`, followed by evaluations at the vertices of `Δ[1]`, which are trivial fibrations
(`SSet.isom.rlp_evalAt`). -/
private lemma exists_map_eq [Y.Quasicategory] (α : Edge F G) (hα : α.IsEquivalence) :
    ∃ (H : X ⟶ (isom Y : SSet.{u})),
      ihomObj₀Equiv X Y F = H ≫ (isom Y).ι ≫ evalAt (stdSimplex.obj₀Equiv.symm 0) Y ∧
      ihomObj₀Equiv X Y G = H ≫ (isom Y).ι ≫ evalAt (stdSimplex.obj₀Equiv.symm 1) Y := by
  refine ⟨Subcomplex.lift _ (range_componentMap_le α hα), ?_, ?_⟩
  · rw [← Category.assoc, Subcomplex.lift_ι, componentMap_evalAt,
      (yonedaEquiv_symm_app_obj₀Equiv_symm α).1]
  · rw [← Category.assoc, Subcomplex.lift_ι, componentMap_evalAt,
      (yonedaEquiv_symm_app_obj₀Equiv_symm α).2]

/-- For a natural transformation `α : F ⟶ G` of maps `X ⟶ Y` into a quasicategory which is an
equivalence of `Fun(X, Y)`, **`F` and `G` induce weak homotopy equivalences
`Hom^R_X(x, y) ⟶ Hom^R_Y(F x, F y)` and `Hom^R_X(x, y) ⟶ Hom^R_Y(G x, G y)` together.** -/
theorem rightMappingSpace.isWeakHomotopyEquivalence_map_iff_of_isEquivalence [Y.Quasicategory]
    {α : Edge F G}
    (hα : α.IsEquivalence) (x y : X _⦋0⦌) :
    IsWeakHomotopyEquivalence (rightMappingSpace.map x y (ihomObj₀Equiv X Y F)) ↔
      IsWeakHomotopyEquivalence (rightMappingSpace.map x y (ihomObj₀Equiv X Y G)) := by
  obtain ⟨H, hF, hG⟩ := exists_map_eq α hα
  have (i : Fin 2) (a b : (isom Y : SSet.{u}) _⦋0⦌) : IsWeakHomotopyEquivalence
      (rightMappingSpace.map a b ((isom Y).ι ≫ evalAt (stdSimplex.obj₀Equiv.symm i) Y)) :=
    isWeakHomotopyEquivalence_of_rlp_monomorphisms
      (rightMappingSpace.rlp_map (isom.rlp_evalAt i) a b)
  rw [hF, hG, rightMappingSpace.map_comp x y H, rightMappingSpace.map_comp x y H]
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · have := IsWeakHomotopyEquivalence.of_postcomp (rightMappingSpace.map x y H)
      (rightMappingSpace.map (H.app _ x) (H.app _ y)
        ((isom Y).ι ≫ evalAt (stdSimplex.obj₀Equiv.symm 0) Y))
    infer_instance
  · have := IsWeakHomotopyEquivalence.of_postcomp (rightMappingSpace.map x y H)
      (rightMappingSpace.map (H.app _ x) (H.app _ y)
        ((isom Y).ι ≫ evalAt (stdSimplex.obj₀Equiv.symm 1) Y))
    infer_instance

/-- For a natural transformation `α : F ⟶ G` of maps `X ⟶ Y` into a quasicategory which is an
equivalence of `Fun(X, Y)`, `F` and `G` induce weak equivalences of right mapping spaces
together. -/
theorem rightMappingSpace.weakEquivalence_map_iff_of_isEquivalence [Y.Quasicategory]
    {α : Edge F G}
    (hα : α.IsEquivalence) (x y : X _⦋0⦌) :
    WeakEquivalence (rightMappingSpace.map x y (ihomObj₀Equiv X Y F)) ↔
      WeakEquivalence (rightMappingSpace.map x y (ihomObj₀Equiv X Y G)) := by
  obtain ⟨H, hF, hG⟩ := exists_map_eq α hα
  have (i : Fin 2) (a b : (isom Y : SSet.{u}) _⦋0⦌) : WeakEquivalence
      (rightMappingSpace.map a b ((isom Y).ι ≫ evalAt (stdSimplex.obj₀Equiv.symm i) Y)) :=
    modelCategoryQuillen.weakEquivalence_of_rlp_monomorphisms
      (rightMappingSpace.rlp_map (isom.rlp_evalAt i) a b)
  rw [hF, hG, rightMappingSpace.map_comp x y H, rightMappingSpace.map_comp x y H,
    weakEquivalence_postcomp_iff, weakEquivalence_postcomp_iff]

/-- **Full faithfulness is invariant under natural equivalence**: for an equivalence `α : F ⟶ G`
of `Fun(X, Y)`, with `Y` a quasicategory, the map `X ⟶ Y` given by `F` is fully faithful exactly
when the one given by `G` is. -/
theorem isFullyFaithful_iff_of_isEquivalence [Y.Quasicategory] {α : Edge F G}
    (hα : α.IsEquivalence) :
    IsFullyFaithful (ihomObj₀Equiv X Y F) ↔ IsFullyFaithful (ihomObj₀Equiv X Y G) :=
  ⟨fun h ↦ ⟨fun x y ↦ (rightMappingSpace.weakEquivalence_map_iff_of_isEquivalence hα x y).1
    (h.weakEquivalence_map x y)⟩,
   fun h ↦ ⟨fun x y ↦ (rightMappingSpace.weakEquivalence_map_iff_of_isEquivalence hα x y).2
    (h.weakEquivalence_map x y)⟩⟩

end isom

/-- **Fully faithful maps reflect equivalences**: for a fully faithful map `f` of quasicategories,
an edge of the source is an equivalence exactly when its image under `f` is. -/
theorem Edge.isEquivalence_map_iff_of_isFullyFaithful [X.Quasicategory] [Y.Quasicategory]
    (f : X ⟶ Y) [IsFullyFaithful f] {x₀ x₁ : X _⦋0⦌} (e : Edge x₀ x₁) :
    (e.map f).IsEquivalence ↔ e.IsEquivalence := by
  rw [Edge.isEquivalence_iff_isIso_homotopyCategoryHomMk,
    Edge.isEquivalence_iff_isIso_homotopyCategoryHomMk, ← mapHomotopyCategory_map_homMk]
  exact isIso_iff_of_reflects_iso _ _

end SSet
