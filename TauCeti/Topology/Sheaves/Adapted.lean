/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.GuitartExact.KanExtension
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import TauCeti.CategoryTheory.Sites.DenseSubsite
public import TauCeti.CategoryTheory.Sites.TopologicalBasis
public import TauCeti.CategoryTheory.Thin
public import TauCeti.Topology.Category.TopCat.Opens

/-!
# Presheaves adapted to a basis

A presheaf `F` on a topological space `X` is *adapted* to a set `B` of opens if, for every open
`V`, the restriction maps `F(V) ⟶ F(U)` to the members `U ∈ B` with `U ≤ V` exhibit `F(V)` as the
limit of the `F(U)`. In the language of Kan extensions, `F` is the pointwise right Kan extension
of its restriction to `B` along the inclusion of `B` into the opens of `X`. This is the sense in
which the structure presheaf of an adic spectrum, defined on rational opens and extended to all
opens by limits, is determined by its values on the rational opens.

When `B` is a basis of the topology, an adapted presheaf is a sheaf exactly when its restriction
to `B` is a sheaf for the topology restricted to `B`; this is what makes sheaf conditions checkable
on a basis for presheaves defined by such limits. Only the direction from `B` to `X` uses
adaptedness; the other direction holds for every sheaf. Conversely, when the target category has
limits, every sheaf is adapted to every basis: a sheaf is determined on an open `V` by its values
on the basic opens contained in `V`. So, for a basis, being a sheaf is the same as being adapted
and a sheaf on the basis.

## Main definitions

* `TopCat.Presheaf.IsAdapted`: `F` is adapted to `B`.

## Main results

* `TopCat.Presheaf.isSheaf_of_isAdapted_of_isSheaf_restrictedTopology`: an adapted presheaf whose
  restriction to `B` is a sheaf for the restricted topology is a sheaf.
* `TopCat.Presheaf.IsSheaf.isSheaf_restrictedTopology`: the restriction of a sheaf to a basis is a
  sheaf for the restricted topology.
* `TopCat.Presheaf.isSheaf_iff_of_isAdapted`: for a presheaf adapted to a basis, the two sheaf
  conditions are equivalent.
* `TopCat.Presheaf.IsSheaf.isAdapted`: a sheaf with values in a category with limits is adapted
  to every basis.
* `TopCat.Presheaf.isSheaf_iff_isAdapted_and_isSheaf_restrictedTopology`: for a basis, a presheaf
  is a sheaf exactly when it is adapted to the basis and a sheaf on the basis.
* `TopCat.Presheaf.IsAdapted.mono`: a presheaf adapted to `B` is adapted to every `B' ⊇ B`. This
  is how adaptedness to the rational opens of an adic spectrum yields adaptedness to its open
  affinoid subspaces.
* `TopCat.Presheaf.IsAdapted.of_iso`, `TopCat.Presheaf.IsAdapted.pushforward_of_iso`:
  adaptedness is invariant under isomorphism of presheaves and under homeomorphism, for the family
  of opens whose preimages lie in `B`.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Remark and Definition 8.9.
* M. Artin, A. Grothendieck, J.-L. Verdier, *Théorie des topos et cohomologie étale des schémas*
  (SGA 4), Tome 1, Exposé III, 2.2, for the passage from a sheaf on the basis to a sheaf on the
  space, which is Mathlib's `CategoryTheory.RanIsSheafOfIsCocontinuous.isLimitMultifork`.
-/

public section

universe w v u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace TopCat.Presheaf

variable {C : Type u} [Category.{v} C] {X : TopCat.{w}} (F : X.Presheaf C) (B : Set (Opens X))

/-- A presheaf `F` on `X` is adapted to a set `B` of opens if, at every open `V`, the restriction
maps to the members of `B` contained in `V` make `F.obj (op V)` the limit of `F` over them: `F`
is the pointwise right Kan extension of its restriction to `B`. -/
@[expose] def IsAdapted : Prop :=
  Nonempty (Functor.RightExtension.mk F
    (𝟙 ((inducedFunctor (Subtype.val : B → Opens X)).op ⋙ F))).IsPointwiseRightKanExtension

/-! ### Enlarging the family -/

section Mono

variable {F} {B} {B' : Set (Opens X)}

/-- For `B ⊆ B'`, the functor from the members of `B` to the members of `B'`, reading a member of
`B` as a member of `B'`. -/
private def inducedOfSubset (hBB' : B ⊆ B') :
    InducedCategory (Opens X) (Subtype.val : B → Opens X) ⥤
      InducedCategory (Opens X) (Subtype.val : B' → Opens X) where
  obj b := ⟨b.1, hBB' b.2⟩
  map φ := InducedCategory.homMk φ.hom

/-- For `B ⊆ B'`, the functor from the members of `B` below an open `Y` to the members of `B'`
below `Y`, reading a member of `B` as a member of `B'`. -/
private def structuredArrowOfSubset (hBB' : B ⊆ B') (Y : (Opens X)ᵒᵖ) :
    StructuredArrow Y (inducedFunctor (Subtype.val : B → Opens X)).op ⥤
      StructuredArrow Y (inducedFunctor (Subtype.val : B' → Opens X)).op :=
  StructuredArrow.map₂ (F := (inducedOfSubset hBB').op) (G := 𝟭 _) (𝟙 Y) (𝟙 _)

/-- Reading a member of `B` below `Y` as a member of `B'` does not change the leg of the
Kan-extension cone of `F` at it: both are the restriction map of `F` from `Y`. -/
private theorem coneAt_π_app_structuredArrowOfSubset_obj (hBB' : B ⊆ B') {Y : (Opens X)ᵒᵖ}
    (g : StructuredArrow Y (inducedFunctor (Subtype.val : B → Opens X)).op) :
    ((Functor.RightExtension.mk F
      (𝟙 ((inducedFunctor (Subtype.val : B' → Opens X)).op ⋙ F))).coneAt Y).π.app
        ((structuredArrowOfSubset hBB' Y).obj g) =
      ((Functor.RightExtension.mk F
        (𝟙 ((inducedFunctor (Subtype.val : B → Opens X)).op ⋙ F))).coneAt Y).π.app g := by
  -- both legs are `F.map` of a morphism out of `Y` in the thin category `(Opens X)ᵒᵖ`
  simp only [Functor.RightExtension.coneAt_π_app, Functor.RightExtension.mk_left,
    Functor.RightExtension.mk_hom, NatTrans.id_app, Functor.comp_obj, Category.comp_id]
  exact congrArg F.map (Subsingleton.elim _ _)

/-- **Adaptedness passes to a larger family.** If `F` is adapted to `B` and `B ⊆ B'`, then `F`
is adapted to `B'`: a compatible family on the members of `B'` below `V` is determined by its
restriction to the members of `B`, and a compatible family on the members of `B` below `V`
extends to the members `U' ∈ B'` below `V` through the limit description of `F(U')`. -/
theorem IsAdapted.mono (hBB' : B ⊆ B') (hF : F.IsAdapted B) : F.IsAdapted B' := by
  obtain ⟨h⟩ := hF
  refine ⟨fun Y ↦ IsLimit.mk (fun s ↦ (h Y).lift (s.whisker (structuredArrowOfSubset hBB' Y)))
    (fun s g ↦ ?_) (fun s m hm ↦ ?_)⟩
  · -- the leg at `U' ∈ B'` is determined by its restrictions to the members `U ∈ B` below `U'`
    refine (h ((inducedFunctor (Subtype.val : B' → Opens X)).op.obj g.right)).hom_ext'
      fun U φ ↦ ?_
    -- both sides are the leg of `s` at `U`, read as a member of `B'` below `Y`
    have h₁ := (h Y).fac (s.whisker (structuredArrowOfSubset hBB' Y))
      (StructuredArrow.mk (g.hom ≫ φ))
    -- the restriction along `φ`, read as a morphism of members of `B'` below `Y`; the type
    -- ascription records that its image under the diagram is `F.map φ`, which holds by definition
    have h₂ : s.π.app g ≫ F.map φ =
        s.π.app ((structuredArrowOfSubset hBB' Y).obj (StructuredArrow.mk (g.hom ≫ φ))) :=
      s.w (StructuredArrow.homMk
        (InducedCategory.homMk (X := (inducedOfSubset hBB').obj U.unop) (Y := g.right.unop)
          φ.unop).op (Subsingleton.elim _ _) :
        g ⟶ (structuredArrowOfSubset hBB' Y).obj (StructuredArrow.mk (g.hom ≫ φ)))
    simp only [Functor.RightExtension.coneAt_π_app, Functor.RightExtension.mk_left,
      Functor.RightExtension.mk_hom, NatTrans.id_app, Functor.comp_obj, Category.comp_id,
      StructuredArrow.mk_right, StructuredArrow.mk_hom_eq_self, Functor.map_comp,
      Cone.whisker_π, Functor.whiskerLeft_app] at h₁ ⊢
    exact (Category.assoc _ _ _).trans (h₁.trans h₂.symm)
  · -- a morphism into `F(Y)` is determined by its restrictions to the members of `B` below `Y`
    refine (h Y).uniq (s.whisker (structuredArrowOfSubset hBB' Y)) m fun g ↦ ?_
    rw [Cone.whisker_π, Functor.whiskerLeft_app, ← coneAt_π_app_structuredArrowOfSubset_obj hBB' g]
    exact hm _

end Mono

/-! ### Transport along isomorphisms -/

section OfIso

variable {F} {B}

/-- **Adaptedness is invariant under isomorphism of presheaves.** -/
theorem IsAdapted.of_iso {G : X.Presheaf C} (e : F ≅ G) (hF : F.IsAdapted B) : G.IsAdapted B := by
  obtain ⟨h⟩ := hF
  refine ⟨fun Y ↦ IsLimit.equivOfNatIsoOfIso
    (Functor.isoWhiskerLeft (StructuredArrow.proj Y (inducedFunctor (Subtype.val : B → Opens X)).op)
      (Functor.isoWhiskerLeft (inducedFunctor (Subtype.val : B → Opens X)).op e))
    ((Functor.RightExtension.mk F (𝟙 _)).coneAt Y) ((Functor.RightExtension.mk G (𝟙 _)).coneAt Y)
    (Cone.ext (e.app Y) fun g ↦ ?_) (h Y)⟩
  simp

end OfIso

section Pushforward

variable {F} {Y : TopCat.{w}} (f : X ≅ Y)

/-- For a homeomorphism `f : X ≅ Y`, the functor from the members of the preimage of `B` to the
members of `B`, taking preimages. -/
private def inducedMapIso :
    InducedCategory (Opens Y) (Subtype.val : (Opens.map f.hom).obj ⁻¹' B → Opens Y) ⥤
      InducedCategory (Opens X) (Subtype.val : B → Opens X) where
  obj b := ⟨(Opens.map f.hom).obj b.1, b.2⟩
  map φ := InducedCategory.homMk ((Opens.map f.hom).map φ.hom)

private instance : (inducedMapIso B f).Full where
  map_surjective {b₁ b₂} ψ :=
    ⟨InducedCategory.homMk (X := b₁) (Y := b₂)
      -- `Opens.map f.hom` is the functor of the equivalence `Opens.mapMapIso f`, hence full
      (leOfHom ((Opens.mapMapIso f).functor.preimage ψ.hom)).hom, Subsingleton.elim _ _⟩

private instance : (inducedMapIso B f).EssSurj where
  mem_essImage b := by
    -- the member `f(U)` of the preimage of `B`, for `U = b` a member of `B`
    have hmem : (Opens.map f.inv).obj b.1 ∈ (Opens.map f.hom).obj ⁻¹' B := by
      rw [Set.mem_preimage, Opens.map_hom_obj_map_inv_obj]
      exact b.2
    exact ⟨⟨(Opens.map f.inv).obj b.1, hmem⟩,
      ⟨eqToIso (Subtype.ext (Opens.map_hom_obj_map_inv_obj f b.1))⟩⟩

private instance : (inducedMapIso B f).IsEquivalence where

/-- The commutative square of the inclusions of the members of the preimage of `B` and of `B` into
the opens, and of the preimage functors; its two-square is the identity. -/
private def pushforwardSquare :
    TwoSquare (inducedFunctor (Subtype.val : (Opens.map f.hom).obj ⁻¹' B → Opens Y)).op
      (inducedMapIso B f).op (Opens.map f.hom).op (inducedFunctor (Subtype.val : B → Opens X)).op :=
  TwoSquare.mk _ _ _ _ (𝟙 _)

private instance : IsIso (pushforwardSquare B f).natTrans := inferInstanceAs (IsIso (𝟙 _))

/-- The components of the identity two-square `pushforwardSquare` are identities, read along the
definitional equality of the two spellings of `f⁻¹(U)` for a member `U` of the preimage of `B`:
as the preimage of `U`, and as the member of `B` that `U` is read as. `F` maps them to
identities. -/
private theorem map_pushforwardSquare_natTrans_app
    (b : (InducedCategory (Opens Y) (Subtype.val : (Opens.map f.hom).obj ⁻¹' B → Opens Y))ᵒᵖ) :
    F.map ((pushforwardSquare B f).natTrans.app b) =
      𝟙 (F.obj ((Opens.map f.hom).op.obj ((inducedFunctor _).op.obj b))) :=
  F.map_id _

variable {B} in
/-- **Adaptedness is invariant under homeomorphism.** If `F` is adapted to `B` and `f : X ≅ Y` is
an isomorphism of topological spaces, the pushforward `f_* F` is adapted to the opens of `Y` whose
preimages lie in `B`. -/
theorem IsAdapted.pushforward_of_iso (hF : F.IsAdapted B) :
    (f.hom _* F).IsAdapted ((Opens.map f.hom).obj ⁻¹' B) := by
  obtain ⟨h⟩ := hF
  refine ⟨fun V ↦ ?_⟩
  -- the square `pushforwardSquare` is Guitart exact, its vertical functors being equivalences
  -- (`Opens.map f.hom` is the functor of the equivalence `Opens.mapMapIso f`), so the cone at `V`
  -- of the right extension `f_* F = (Opens.map f.hom).op ⋙ F` is a limit cone exactly when the
  -- cone at `f⁻¹(V)` of the right extension `F` is
  have : (Opens.map f.hom).IsEquivalence := (Opens.mapMapIso f).isEquivalence_functor
  have := ((Functor.RightExtension.mk F (𝟙 _)).isPointwiseRightKanExtensionAtCompTwoSquareEquiv
    (pushforwardSquare B f) V).symm (h _)
  -- the legs agree: both are the restriction map of `f_* F` from `V`, composed with identities
  refine IsLimit.ofIsoLimit this (Cone.ext (Iso.refl _) fun g ↦ ?_)
  simp only [Functor.RightExtension.coneAt_π_app, Functor.RightExtension.coneAt_pt,
    Functor.RightExtension.mk_left, Functor.RightExtension.mk_hom, Functor.comp_map,
    Functor.comp_obj, NatTrans.comp_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, NatTrans.id_app, Category.comp_id,
    map_pushforwardSquare_natTrans_app (F := F) B f, Iso.refl_hom, pushforward_obj_map,
    Functor.op_map]
  -- the identities are those of `F(f⁻¹(U))` for `U = g.right`, composed along the definitional
  -- equality of the two spellings of `f⁻¹(U)`, which `simp` does not see through
  exact (congrArg (F.map _ ≫ ·) ((Category.id_comp _).trans (Category.id_comp _))).trans
    ((Category.comp_id _).trans (Category.id_comp _).symm)

end Pushforward

/-! ### The sheaf condition on a basis -/

/-- **The sheaf condition on a basis `B` suffices for an adapted presheaf.** If `F` is adapted to
the basis `B` and its restriction to `B` is a sheaf for the topology restricted to `B`, then `F` is
a sheaf. A sieve on a member of `B` covers for the restricted topology exactly when its image
covers in `X` (`Functor.mem_restrictedTopology_iff`), so the hypothesis involves only covers of
members of `B` by members of `B`. The inclusion of a basis is cocontinuous for the restricted
topology, and a pointwise right Kan extension of a sheaf along a cocontinuous functor is a sheaf
(SGA 4 III 2.2). -/
theorem isSheaf_of_isAdapted_of_isSheaf_restrictedTopology (hB : Opens.IsBasis B)
    (hF : F.IsAdapted B)
    (h : CategoryTheory.Presheaf.IsSheaf
      ((inducedFunctor (Subtype.val : B → Opens X)).restrictedTopology
        (Opens.grothendieckTopology X))
      ((inducedFunctor (Subtype.val : B → Opens X)).op ⋙ F)) :
    F.IsSheaf :=
  -- a basis is cover-dense, so its inclusion is cocontinuous for the restricted topology
  have := TauCeti.TopologicalSpace.Opens.coverDense_inducedFunctor_subtypeVal hB
  (Presheaf.isSheaf_iff_multifork _ _).mpr fun _ S ↦
    ⟨RanIsSheafOfIsCocontinuous.isLimitMultifork h hF.some S⟩

/-- The restriction of a sheaf to a basis `B` is a sheaf for the restricted topology on `B`. -/
theorem IsSheaf.isSheaf_restrictedTopology {B : Set (Opens X)} (hB : Opens.IsBasis B)
    {F : X.Presheaf C} (hF : F.IsSheaf) :
    CategoryTheory.Presheaf.IsSheaf
      ((inducedFunctor (Subtype.val : B → Opens X)).restrictedTopology
        (Opens.grothendieckTopology X))
      ((inducedFunctor (Subtype.val : B → Opens X)).op ⋙ F) :=
  -- a basis is cover-dense, hence a dense subsite for the restricted topology, hence continuous
  have := TauCeti.TopologicalSpace.Opens.coverDense_inducedFunctor_subtypeVal hB
  Functor.op_comp_isSheaf_of_isSheaf _ _ _ F hF

/-- **A presheaf adapted to a basis is a sheaf exactly when it is a sheaf on the basis**, for the
topology restricted to the basis. -/
theorem isSheaf_iff_of_isAdapted (hB : Opens.IsBasis B) (hF : F.IsAdapted B) :
    F.IsSheaf ↔ CategoryTheory.Presheaf.IsSheaf
      ((inducedFunctor (Subtype.val : B → Opens X)).restrictedTopology
        (Opens.grothendieckTopology X))
      ((inducedFunctor (Subtype.val : B → Opens X)).op ⋙ F) :=
  ⟨fun h ↦ h.isSheaf_restrictedTopology hB,
    isSheaf_of_isAdapted_of_isSheaf_restrictedTopology F B hB hF⟩

/-! ### Sheaves are adapted to every basis -/

section HasLimits

variable [HasLimitsOfSize.{w, w} C]

/-- **A sheaf is adapted to every basis.** If `F` takes values in a category with limits and is a
sheaf, then for every basis `B` and every open `V`, the restriction maps exhibit `F(V)` as the
limit of the `F(U)` over the members `U ∈ B` below `V`: a basis is a dense subsite of the opens,
and a sheaf is the pointwise right Kan extension of its restriction to a dense subsite. -/
theorem IsSheaf.isAdapted {B : Set (Opens X)} (hB : Opens.IsBasis B) {F : X.Presheaf C}
    (hF : F.IsSheaf) : F.IsAdapted B :=
  have := TauCeti.TopologicalSpace.Opens.coverDense_inducedFunctor_subtypeVal hB
  ⟨Functor.IsDenseSubsite.isPointwiseRightKanExtension (inducedFunctor (Subtype.val : B → Opens X))
    ((inducedFunctor (Subtype.val : B → Opens X)).restrictedTopology
      (Opens.grothendieckTopology X))
    (Opens.grothendieckTopology X) ⟨F, hF⟩⟩

/-- **For a basis `B`, a presheaf is a sheaf exactly when it is adapted to `B` and a sheaf on
`B`**, for the topology restricted to `B`. -/
theorem isSheaf_iff_isAdapted_and_isSheaf_restrictedTopology (hB : Opens.IsBasis B) :
    F.IsSheaf ↔ F.IsAdapted B ∧ CategoryTheory.Presheaf.IsSheaf
      ((inducedFunctor (Subtype.val : B → Opens X)).restrictedTopology
        (Opens.grothendieckTopology X))
      ((inducedFunctor (Subtype.val : B → Opens X)).op ⋙ F) :=
  ⟨fun h ↦ ⟨h.isAdapted hB, h.isSheaf_restrictedTopology hB⟩,
    fun h ↦ isSheaf_of_isAdapted_of_isSheaf_restrictedTopology F B hB h.1 h.2⟩

end HasLimits

end TopCat.Presheaf

end
