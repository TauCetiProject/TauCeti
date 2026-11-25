/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import TauCeti.CategoryTheory.Limits.Lattice

/-!
# Open subsets of schemes

This file records general-purpose facts about open subsets of schemes.

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.instNonemptyTop` states that the whole space is a nonempty open
  subset of any nonempty scheme.
* `AlgebraicGeometry.IsAffineOpen.presheaf_map_fromSpec_appIso_hom` identifies restriction of
  structure-sheaf sections along the affine chart `Spec Γ(X, U)`.
* `AlgebraicGeometry.Scheme.Hom.preimage_finset_inf` and
  `AlgebraicGeometry.Scheme.Hom.preimage_finite_product`: inverse images commute with finite
  intersections, written as `Finset.inf` or as finite products of opens.
* `AlgebraicGeometry.Scheme.Hom.isAffineOpen_finset_inf_preimage`: along an affine morphism, the
  inverse images of a family of opens with affine nonempty finite intersections, such as the covers
  used to compute cohomology by Čech complexes, again have affine nonempty finite intersections.
* `AlgebraicGeometry.Scheme.Hom.iSup_affineOpens_le_preimage_eq_top`: the affine opens of `X`
  which a morphism `X ⟶ Y` maps into an affine open of `Y` cover `X`.
* `AlgebraicGeometry.Scheme.toSpecΓ_morphismRestrict_comp_basicOpenIsoSpecAway_hom`:
  restricting `toSpecΓ` to the basic open of a global section, as the map induced by a ring map out
  of the localization extending the restriction.
* `AlgebraicGeometry.Scheme.Hom.appLE_eq_id_of_eq_id` identifies the restriction maps of a scheme
  endomorphism equal to the identity.
* `AlgebraicGeometry.Scheme.Hom.preimage_eq_preimage_inf_of_comp_eq`: in a commutative square, the
  preimage under `f'` of an open of the base lying over `W` lies in the preimage under `g'` of
  `f⁻¹ W`.
* `AlgebraicGeometry.Scheme.forall_affineOpens_map_of_le`: a condition on the restrictions of a
  section over `V` to all affine opens inside `V` is inherited by its restriction to any smaller
  open.
* `AlgebraicGeometry.Scheme.existsUnique_gluing_affineOpens`: sections over the affine opens,
  compatible with restriction, glue to a unique global section.
* `AlgebraicGeometry.Scheme.eq_of_forall_affineOpens_map_eq`: global sections are determined by
  their restrictions to the affine opens, and
  `AlgebraicGeometry.Scheme.presheaf_map_homOfLE_comp` composes restriction homomorphisms.
* `AlgebraicGeometry.Scheme.exists_finite_affineOpens_cover`: a quasi-compact open is covered by
  finitely many affine opens contained in it, in the form used by sheaf gluing.
* `AlgebraicGeometry.IsAffineOpen.fromSpec_appLE_self` and
  `AlgebraicGeometry.Scheme.Hom.appLE_ΓSpecIso_hom_naturality` compute the global sections of
  affine charts `Spec R ⟶ X` and their precomposites with `Spec.map φ`.
* `AlgebraicGeometry.IsAffineOpen.span_restrict_basicOpen_le_eq_top`: for affine opens `V ≤ U`,
  the restrictions of the functions on `U` whose basic open lies in `V` generate the unit ideal of
  `Γ(X, V)`.
* `AlgebraicGeometry.IsAffineOpen.exists_finset_sup_basicOpen_eq`: a quasi-compact open inside an
  affine open `U` is a finite union of basic opens of `U` contained in it.
* `AlgebraicGeometry.Scheme.inf_mem_range_basicOpen` and
  `AlgebraicGeometry.IsAffineOpen.exists_mem_range_basicOpen_le_sup`: the basic opens of `U` are
  closed under intersections, and for `U` affine, a basic open covered by a basic open `A` and
  finitely many basic opens `V i` is covered by `A` and one basic open inside the union of the
  `V i`.
* `AlgebraicGeometry.IsAffineOpen.isAffineHom_ι`: an affine open in a scheme with affine
  diagonal has affine inclusion.
* `AlgebraicGeometry.IsAffineOpen.finset_inf`: on a scheme with affine diagonal, nonempty finite
  intersections of affine opens are affine.
* `AlgebraicGeometry.Scheme.OpenCover.dense_of_forall_dense_subset`: a subset of a scheme is dense
  if its preimage in every chart of an open cover contains a dense subset.
* `AlgebraicGeometry.Scheme.Hom.top_le_preimage` and
  `AlgebraicGeometry.Scheme.Hom.basicOpen_appLE_eq_bot`: if a morphism `f` maps every point to `x`,
  every open neighbourhood of `x` pulls back to the whole source, and a section whose basic open
  misses `x` pulls back to a global section with empty basic open.
* `AlgebraicGeometry.Scheme.notMem_closure_basicOpen_of_isNilpotent_germ`: a section with
  nilpotent germ at `y` vanishes on a neighbourhood of `y`.
-/

open TopologicalSpace AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

public section

open CategoryTheory Opposite

noncomputable section

variable {X : Scheme.{u}} {U : X.Opens}

/-- The preimages of two opens covering the target cover the source. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.preimage_sup_eq_top {Y : Scheme.{u}}
    (f : X ⟶ Y) {U V : Y.Opens} (hUV : U ⊔ V = ⊤) :
    f ⁻¹ᵁ U ⊔ f ⁻¹ᵁ V = ⊤ := by
  rw [← f.preimage_sup, hUV, f.preimage_top]

/-- Taking inverse images under a morphism of schemes commutes with finite intersections. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Hom.preimage_finset_inf {Y : Scheme.{u}} (f : X ⟶ Y)
    {ι : Type*} (s : Finset ι) (U : ι → Y.Opens) :
    f ⁻¹ᵁ s.inf U = s.inf fun i ↦ f ⁻¹ᵁ U i :=
  Finset.apply_inf_eq_inf_comp (f ⁻¹ᵁ ·) (fun _ _ ↦ rfl) rfl

open Limits in
/-- Taking inverse images under a morphism of schemes commutes with finite products of opens,
which are their intersections. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.preimage_finite_product {Y : Scheme.{u}} (f : X ⟶ Y)
    {J : Type*} [Finite J] (U : J → Y.Opens) :
    f ⁻¹ᵁ ∏ᶜ U = ∏ᶜ fun j ↦ f ⁻¹ᵁ U j := by
  classical
  have := Fintype.ofFinite J
  exact (congrArg (f ⁻¹ᵁ ·) (CompleteLattice.finite_product_eq_finset_image_inf U id)).trans <|
    (f.preimage_finset_inf _ U).trans
      (CompleteLattice.finite_product_eq_finset_image_inf (fun j ↦ f ⁻¹ᵁ U j) id).symm

/-- Along an affine morphism, the inverse images of a family of opens whose nonempty finite
intersections are affine again have affine nonempty finite intersections. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.isAffineOpen_finset_inf_preimage {Y : Scheme.{u}}
    (f : X ⟶ Y) [IsAffineHom f] {ι : Type*} {U : ι → Y.Opens}
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (s.inf U)) (s : Finset ι) (hs : s.Nonempty) :
    IsAffineOpen (s.inf fun i ↦ f ⁻¹ᵁ U i) :=
  f.preimage_finset_inf s U ▸ (hU s hs).preimage f

/-- For a morphism `f : X ⟶ Y`, the affine opens of `X` which `f` maps into an affine open of `Y`
cover `X`. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.iSup_affineOpens_le_preimage_eq_top {Y : Scheme.{u}}
    (f : X ⟶ Y) :
    ⨆ V : {V : X.affineOpens // ∃ U : Y.affineOpens, V.val ≤ f ⁻¹ᵁ U.val}, V.val.val = ⊤ := by
  refine eq_top_iff.2 fun x _ ↦ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).is_open'
  exact Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, ⟨U, hU⟩, hVU⟩, hxV⟩

/-- An affine open in a scheme with affine diagonal has affine inclusion. -/
lemma _root_.AlgebraicGeometry.IsAffineOpen.isAffineHom_ι (hU : IsAffineOpen U)
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))] : IsAffineHom U.ι :=
  ⟨fun V hV ↦ U.ι.isAffineOpen_iff_of_isOpenImmersion.mp (by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact hU.inf hV)⟩

/-- On a scheme with affine diagonal, for instance a separated one, a nonempty finite intersection
of affine opens is affine. -/
lemma _root_.AlgebraicGeometry.IsAffineOpen.finset_inf
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))] {ι : Type*} (s : Finset ι)
    (hs : s.Nonempty) {U : ι → X.Opens} (hU : ∀ i ∈ s, IsAffineOpen (U i)) :
    IsAffineOpen (s.inf U) := by
  rw [Finset.inf_eq_iInf]
  exact IsAffineOpen.biInf _ s.finite_toSet hs hU

/-- If an endomorphism `f` of `X` equals the identity, then so does each of its restriction maps
`Γ(X, U) ⟶ Γ(X, U)`. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.appLE_eq_id_of_eq_id {f : X ⟶ X}
    (hf : f = 𝟙 X) (U : X.Opens) (e : U ≤ f ⁻¹ᵁ U) : f.appLE U U e = 𝟙 _ := by
  subst hf
  rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
  exact (Category.id_comp _).trans (X.presheaf.map_id _)

/-- In a commutative square `g' ≫ f = f' ≫ g`, for an open `W' ⊆ g⁻¹ W` of the base `S'`, the
preimage `f'⁻¹ W'` lies inside `g'⁻¹ (f⁻¹ W)`, so it equals its intersection with it. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.preimage_eq_preimage_inf_of_comp_eq
    {X' S S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'} {g : S' ⟶ S} {g' : X' ⟶ X}
    (hw : g' ≫ f = f' ≫ g) {W : S.Opens} {W' : S'.Opens} (h : W' ≤ g ⁻¹ᵁ W) :
    f' ⁻¹ᵁ W' = g' ⁻¹ᵁ (f ⁻¹ᵁ W) ⊓ f' ⁻¹ᵁ W' := by
  refine (inf_eq_right.mpr ?_).symm
  rw [← Scheme.Hom.comp_preimage, hw, Scheme.Hom.comp_preimage]
  exact f'.preimage_mono h

/-- A condition imposed on the restrictions of a section `b` over `V` to all affine opens inside `V`
is inherited by the restriction of `b` to any smaller open `V'`. -/
theorem _root_.AlgebraicGeometry.Scheme.forall_affineOpens_map_of_le {V V' : X.Opens}
    (hV'V : V' ≤ V) {b : Γ(X, V)} {P : ∀ W : X.affineOpens, Γ(X, W) → Prop}
    (h : ∀ (W : X.affineOpens) (hWV : W.val ≤ V), P W (X.presheaf.map (homOfLE hWV).op b))
    (W : X.affineOpens) (hWV' : W.val ≤ V') :
    P W (X.presheaf.map (homOfLE hWV').op (X.presheaf.map (homOfLE hV'V).op b)) := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]
  exact h W (hWV'.trans hV'V)

/-- **Sections glue along the affine opens.** A family of sections `s U ∈ Γ(X, U)`, one over each
affine open `U` of `X`, compatible with restriction from an affine open to a smaller one, consists
of the restrictions of a unique global section. -/
theorem _root_.AlgebraicGeometry.Scheme.existsUnique_gluing_affineOpens (X : Scheme.{u})
    (s : ∀ U : X.affineOpens, Γ(X, U.val))
    (hs : ∀ (U V : X.affineOpens) (h : V.val ≤ U.val), X.presheaf.map (homOfLE h).op (s U) = s V) :
    ∃! t : Γ(X, ⊤), ∀ U : X.affineOpens, X.presheaf.map (homOfLE le_top).op t = s U := by
  -- every open `V` is covered by the affine opens it contains
  have hcov (V : X.Opens) : V ≤ ⨆ W : {W : X.affineOpens // W.val ≤ V}, W.val.val := fun x hx ↦ by
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
    exact Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWV⟩, hxW⟩
  refine X.sheaf.existsUnique_gluing' (fun U : X.affineOpens ↦ U.val) ⊤ (fun _ ↦ homOfLE le_top)
    (iSup_affineOpens_eq_top X).ge s fun U U' ↦ ?_
  -- on `U ⊓ U'`, the two restrictions agree on every affine open `W ⊆ U ⊓ U'`
  refine X.sheaf.eq_of_locally_eq' (fun W : {W : X.affineOpens // W.val ≤ U.val ⊓ U'.val} ↦
      W.val.val) _
    (fun W ↦ homOfLE W.property) (hcov _) _ _ fun W ↦ ?_
  -- stated through `X.presheaf`, the underlying presheaf of `X.sheaf`
  have h₁ : X.presheaf.map (homOfLE W.property).op (X.presheaf.map (Opens.infLELeft U.val U'.val).op
      (s U)) =
      s W.val := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact hs U W.val (W.property.trans inf_le_left)
  have h₂ :
      X.presheaf.map (homOfLE W.property).op (X.presheaf.map (Opens.infLERight U.val U'.val).op
          (s U')) =
        s W.val := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact hs U' W.val (W.property.trans inf_le_right)
  exact h₁.trans h₂.symm

/-- Restriction of sections from `W` to `U` followed by restriction to `V ≤ U` is restriction from
`W` to `V`, as a composite of ring homomorphisms. -/
theorem _root_.AlgebraicGeometry.Scheme.presheaf_map_homOfLE_comp {V U W : X.Opens} (hVU : V ≤ U)
    (hUW : U ≤ W) :
    (X.presheaf.map (homOfLE hVU).op).hom.comp (X.presheaf.map (homOfLE hUW).op).hom =
      (X.presheaf.map (homOfLE (hVU.trans hUW)).op).hom := by
  rw [← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

/-- **Global sections are determined by their restrictions to the affine opens.** -/
theorem _root_.AlgebraicGeometry.Scheme.eq_of_forall_affineOpens_map_eq (X : Scheme.{u})
    {x y : Γ(X, ⊤)}
    (h : ∀ U : X.affineOpens, X.presheaf.map (homOfLE (le_top : U.val ≤ ⊤)).op x =
      X.presheaf.map (homOfLE (le_top : U.val ≤ ⊤)).op y) :
    x = y :=
  (X.existsUnique_gluing_affineOpens (fun U ↦ X.presheaf.map (homOfLE (le_top : U.val ≤ ⊤)).op y)
    fun _ _ hVU ↦ congrArg (· y)
      (congrArg DFunLike.coe (Scheme.presheaf_map_homOfLE_comp (X := X) hVU le_top))).unique h
    fun _ ↦ rfl

/-- A quasi-compact open `U` is covered by finitely many affine opens contained in it. This is
`AlgebraicGeometry.isCompact_iff_finite_and_eq_biUnion_affineOpens` stated as a family of opens
below `U` whose supremum contains `U`, the form taken by the sheaf gluing lemmas
`TopCat.Sheaf.eq_of_locally_eq'` and `TopCat.Sheaf.existsUnique_gluing'`. -/
theorem _root_.AlgebraicGeometry.Scheme.exists_finite_affineOpens_cover
    (hU : IsCompact (U : Set X)) :
    ∃ (s : Set X.affineOpens) (_ : Finite s), (∀ i : s, (i.val : X.Opens) ≤ U) ∧
      U ≤ ⨆ i : s, (i.val : X.Opens) := by
  obtain ⟨s, hs, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hU
  exact ⟨s, hs.to_subtype, fun i ↦ e ▸ le_biSup (fun j : X.affineOpens ↦ (j : X.Opens)) i.property,
    by rw [e, iSup_subtype']⟩

/-- A compact open admits a finite affine refinement whose members map into affine
opens of the target of a given scheme morphism. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.exists_finite_affine_refinement
    {Y S : Scheme.{u}} (p : Y ⟶ S) (V : Y.Opens) (hV : IsCompact (V : Set Y)) :
    ∃ (U : V → Y.Opens), (∀ x, IsAffineOpen (U x)) ∧
      (∀ x, U x ≤ V) ∧ ∃ (W : V → S.Opens), (∀ x, IsAffineOpen (W x)) ∧
        (∀ x, U x ≤ p ⁻¹ᵁ W x) ∧ ∃ t : Finset V,
          (V : Set Y) ⊆ ⋃ x ∈ t, (U x : Set Y) := by
  classical
  have hnbhd (x : V) : ∃ (U : Y.Opens), IsAffineOpen U ∧ x.val ∈ U ∧
      U ≤ V ∧ ∃ W : S.Opens, IsAffineOpen W ∧ U ≤ p ⁻¹ᵁ W := by
    obtain ⟨W, hW, hxW, _⟩ := exists_isAffineOpen_mem_and_subset
      (X := S) (x := p x.val) (U := ⊤) (by trivial)
    obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
      (U := V ⊓ p ⁻¹ᵁ W) ⟨x.property, hxW⟩
    exact ⟨U, hU, hxU, le_trans hUV inf_le_left, W, hW, le_trans hUV inf_le_right⟩
  choose U hU hxU hUV W hW hUW using hnbhd
  obtain ⟨t, ht⟩ := hV.elim_finite_subcover (fun x ↦ (U x : Set Y))
    (fun x ↦ (U x).isOpen) (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
  exact ⟨U, hU, hUV, W, hW, hUW, t, ht⟩

/-- Along the open immersion `hU.fromSpec : Spec Γ(X, U) ⟶ X` onto an affine open `U`,
restricting a section of `𝒪_X` from `U` to the image of an open `V` and transporting it to `V`
gives the restriction to `V` of the corresponding global section of `Spec Γ(X, U)`. -/
@[reassoc]
theorem _root_.AlgebraicGeometry.IsAffineOpen.presheaf_map_fromSpec_appIso_hom
    (hU : IsAffineOpen U) (V : (Spec Γ(X, U)).Opens) :
    X.presheaf.map (homOfLE (by
        simpa [hU.opensRange_fromSpec] using hU.fromSpec.image_le_opensRange V)).op ≫
      (hU.fromSpec.appIso V).hom =
      (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec Γ(X, U)).presheaf.map V.leTop.op := by
  rw [← hU.fromSpec.appLE_appIso_inv (by simp [hU.fromSpec_preimage_self]), Category.assoc,
    Iso.inv_hom_id, Category.comp_id, Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc,
    ← Functor.map_comp]
  rfl

/-- Pulling a section over an affine open `U` back to all of `Spec Γ(X, U)` along `hU.fromSpec`
is the inverse of the global-sections isomorphism of `Spec`. -/
theorem _root_.AlgebraicGeometry.IsAffineOpen.fromSpec_appLE_self (hU : IsAffineOpen U)
    (e : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ e = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  exact (congrArg _ ((congrArg _ (Subsingleton.elim _ _)).trans
    ((Spec Γ(X, U)).presheaf.map_id _))).trans (Category.comp_id _)

/-- For affine opens `V ≤ U`, the restrictions to `V` of the functions on `U` whose basic open lies
in `V` generate the unit ideal of `Γ(X, V)`. -/
theorem _root_.AlgebraicGeometry.IsAffineOpen.span_restrict_basicOpen_le_eq_top {V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ U) :
    Ideal.span {g : Γ(X, V) | ∃ f : Γ(X, U), X.basicOpen f ≤ V ∧
      X.presheaf.map (homOfLE hVU).op f = g} = ⊤ := by
  refine (hV.self_le_iSup_basicOpen_iff).mp fun x hx ↦ ?_
  obtain ⟨f, hfV, hxf⟩ := hU.exists_basicOpen_le ⟨x, hx⟩ (hVU hx)
  refine Opens.mem_iSup.mpr ⟨⟨_, f, hfV, rfl⟩, ?_⟩
  rw [Scheme.basicOpen_res]
  exact ⟨hx, hxf⟩

/-- A quasi-compact open `W` contained in an affine open `U` is the union of finitely many basic
opens of `U` contained in `W`. -/
theorem _root_.AlgebraicGeometry.IsAffineOpen.exists_finset_sup_basicOpen_eq (hU : IsAffineOpen U)
    {W : X.Opens} (hW : IsCompact (W : Set X)) (hWU : W ≤ U) :
    ∃ s : Finset {f : Γ(X, U) // X.basicOpen f ≤ W}, s.sup (fun i ↦ X.basicOpen i.val) = W := by
  obtain ⟨s, hs⟩ := hW.elim_finite_subcover
    (fun i : {f : Γ(X, U) // X.basicOpen f ≤ W} ↦ (X.basicOpen i.val : Set X))
    (fun i ↦ (X.basicOpen i.val).isOpen) fun x hx ↦ by
      obtain ⟨f, hf, hxf⟩ := hU.exists_basicOpen_le ⟨x, hx⟩ (hWU hx)
      exact Set.mem_iUnion.mpr ⟨⟨f, hf⟩, hxf⟩
  refine ⟨s, le_antisymm (Finset.sup_le fun i _ ↦ i.property) fun x hx ↦ ?_⟩
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hs hx)
  exact (Finset.le_sup (f := fun i : {f : Γ(X, U) // X.basicOpen f ≤ W} ↦ X.basicOpen i.val) hi) hxi

/-- The basic opens `X.basicOpen f` of sections `f` over an open `U` are closed under binary
intersections. -/
theorem _root_.AlgebraicGeometry.Scheme.inf_mem_range_basicOpen :
    ∀ V ∈ Set.range fun f : Γ(X, U) ↦ X.basicOpen f,
      ∀ W ∈ Set.range fun f : Γ(X, U) ↦ X.basicOpen f,
        V ⊓ W ∈ Set.range fun f : Γ(X, U) ↦ X.basicOpen f := by
  rintro _ ⟨f, rfl⟩ _ ⟨g, rfl⟩
  exact ⟨f * g, Scheme.basicOpen_mul _ _ _⟩

/-- Let `U` be an affine open. If a basic open `Y` of `U` lies in the union of a basic open `A`
and of finitely many basic opens `V i`, `i ∈ s`, of `U`, then it lies in the union of `A` and of a
single basic open of `U` contained in the union of the `V i`. -/
theorem _root_.AlgebraicGeometry.IsAffineOpen.exists_mem_range_basicOpen_le_sup
    (hU : IsAffineOpen U) {Y A : X.Opens} (hY : Y ∈ Set.range fun f : Γ(X, U) ↦ X.basicOpen f)
    (hA : A ∈ Set.range fun f : Γ(X, U) ↦ X.basicOpen f) {ι : Type*} (V : ι → X.Opens)
    (hV : ∀ i, V i ∈ Set.range fun f : Γ(X, U) ↦ X.basicOpen f) (s : Finset ι)
    (h : Y ≤ A ⊔ s.sup V) : ∃ W ∈ Set.range fun f : Γ(X, U) ↦ X.basicOpen f,
      Y ≤ A ⊔ W ∧ W ≤ s.sup V := by
  classical
  obtain ⟨g, rfl⟩ := hY
  obtain ⟨f, rfl⟩ := hA
  choose f' hf' using hV
  beta_reduce at h hf'
  let r : Γ(X, U) → Γ(X, X.basicOpen g) := fun a ↦ X.presheaf.map (homOfLE (X.basicOpen_le g)).op a
  have hr (a : Γ(X, U)) : X.basicOpen (r a) = X.basicOpen g ⊓ X.basicOpen a :=
    Scheme.basicOpen_res _ _ _
  let T : Set Γ(X, X.basicOpen g) := (fun i ↦ r (f' i)) '' ↑s
  -- the restrictions of `f` and of the `f' i` to `D(g)` generate the unit ideal there
  have hspan : Ideal.span (insert (r f) T) = ⊤ := by
    refine ((hU.basicOpen g).self_le_iSup_basicOpen_iff (s := insert (r f) T)).1 ?_
    intro x hx
    rcases Opens.mem_sup.1 (h hx) with hxf | hxs
    · exact Opens.mem_iSup.2 ⟨⟨r f, Set.mem_insert _ _⟩, by rw [hr]; exact ⟨hx, hxf⟩⟩
    · rw [Finset.sup_eq_iSup] at hxs
      obtain ⟨i, hxi⟩ := Opens.mem_iSup.1 hxs
      obtain ⟨hi, hxi⟩ := Opens.mem_iSup.1 hxi
      exact Opens.mem_iSup.2 ⟨⟨r (f' i), Set.mem_insert_of_mem _ ⟨i, hi, rfl⟩⟩,
        by rw [hr, hf']; exact ⟨hx, hxi⟩⟩
  obtain ⟨a, z, hz, haz⟩ := Ideal.mem_span_insert.1
    (hspan ▸ Submodule.mem_top : (1 : Γ(X, X.basicOpen g)) ∈ Ideal.span (insert (r f) T))
  obtain ⟨h', hh'⟩ := hU.basicOpen_basicOpen_is_basicOpen g z
  refine ⟨X.basicOpen h', ⟨h', rfl⟩, ?_, ?_⟩
  · rw [hh']
    calc X.basicOpen g = X.basicOpen (a * r f + z) := by rw [← haz, Scheme.basicOpen_one]
      _ ≤ X.basicOpen (a * r f) ⊔ X.basicOpen z := X.basicOpen_add_le _ _
      _ ≤ X.basicOpen f ⊔ X.basicOpen z := by
        refine sup_le_sup_right ?_ _
        rw [Scheme.basicOpen_mul, hr]
        exact inf_le_right.trans inf_le_right
  · -- a point of `D(z)` outside every `V i` would lie in the zero locus of the span of `T`
    rw [hh']
    intro x hx
    by_contra hxs
    have hxT : x ∈ X.zeroLocus T := by
      rw [Scheme.mem_zeroLocus_iff]
      rintro _ ⟨i, hi, rfl⟩ hxi
      rw [hr, hf'] at hxi
      exact hxs (Finset.le_sup (f := V) hi hxi.2)
    rw [← Scheme.zeroLocus_span, Scheme.mem_zeroLocus_iff] at hxT
    exact hxT z hz hx

/-- Global sections of an affine chart `f : Spec R ⟶ Y` are natural in `R`: precomposing `f` with
`Spec.map φ` turns the induced map `Γ(Y, V) ⟶ R` into its composite with `φ`. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.appLE_ΓSpecIso_hom_naturality {R S : CommRingCat.{u}}
    {Y : Scheme.{u}} (f : Spec R ⟶ Y) {q : Spec S ⟶ Y} (φ : R ⟶ S) (h : q = Spec.map φ ≫ f)
    {V : Y.Opens} (e : ⊤ ≤ f ⁻¹ᵁ V) (e' : ⊤ ≤ q ⁻¹ᵁ V) :
    q.appLE V ⊤ e' ≫ (Scheme.ΓSpecIso S).hom =
      (f.appLE V ⊤ e ≫ (Scheme.ΓSpecIso R).hom) ≫ φ := by
  subst h
  -- `Scheme.Hom.appLE_eq_app` at `⊤` applies because `Spec.map φ ⁻¹ᵁ ⊤` is `⊤` by definition.
  have h : (Spec.map φ ≫ f).appLE V ⊤ e' = f.appLE V ⊤ e ≫ (Spec.map φ).appTop :=
    (Scheme.Hom.appLE_comp_appLE (Spec.map φ) f V ⊤ ⊤ e le_top).symm.trans
      (congrArg (f.appLE V ⊤ e ≫ ·) (Scheme.Hom.appLE_eq_app (Spec.map φ) (U := ⊤)))
  rw [h, Category.assoc, Category.assoc, Scheme.ΓSpecIso_naturality]

/-- Restricting the canonical map to the spectrum of global sections to the basic open of a
global section `s` and identifying the spectrum of a localization with the basic open is the map
induced by any ring map out of the localization that extends the restriction of global
sections. -/
lemma _root_.AlgebraicGeometry.Scheme.toSpecΓ_morphismRestrict_comp_basicOpenIsoSpecAway_hom
    (s : Γ(X, ⊤)) (l : Localization.Away s →+* Γ(X, X.basicOpen s))
    (hl : l.comp (algebraMap Γ(X, ⊤) (Localization.Away s)) =
      (X.presheaf.map (homOfLE (le_top : X.basicOpen s ≤ ⊤)).op).hom) :
    (X.isoOfEq (X.toSpecΓ_preimage_basicOpen s)).inv ≫
        X.toSpecΓ ∣_ PrimeSpectrum.basicOpen s ≫
        (basicOpenIsoSpecAway s).hom =
      (X.basicOpen s).toSpecΓ ≫ Spec.map (CommRingCat.ofHom l) := by
  rw [← cancel_mono (Spec.map (CommRingCat.ofHom
    (algebraMap Γ(X, ⊤) (Localization.Away s))))]
  simp only [Category.assoc, basicOpenIsoSpecAway_hom_SpecMap]
  have hrest := congrArg
    (fun e ↦ (X.isoOfEq (X.toSpecΓ_preimage_basicOpen s)).inv ≫ e)
    (morphismRestrict_ι X.toSpecΓ
      (PrimeSpectrum.basicOpen s : (Spec Γ(X, ⊤)).Opens))
  simp only [Scheme.isoOfEq_inv_ι_assoc] at hrest
  refine hrest.trans ?_
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [hl]
  exact (Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top (X.basicOpen s)).symm

/-- If `f` maps every point to `x`, the preimage of any open neighbourhood of `x` is everything. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.top_le_preimage {Y : Scheme.{u}} (f : Y ⟶ X) {x : X}
    (hf : ∀ y, f y = x) (hxU : x ∈ U) : ⊤ ≤ f ⁻¹ᵁ U :=
  fun y _ ↦ f.mem_preimage.mpr (hf y ▸ hxU)

/-- If `f` maps every point to `x` and the basic open of `s` misses `x`, the pullback of `s` to
the global sections of `Y` has empty basic open. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.basicOpen_appLE_eq_bot {Y : Scheme.{u}} (f : Y ⟶ X)
    {x : X} (hf : ∀ y, f y = x) (e : ⊤ ≤ f ⁻¹ᵁ U) {s : Γ(X, U)} (hs : x ∉ X.basicOpen s) :
    Y.basicOpen (f.appLE U ⊤ e s) = ⊥ := by
  rw [Scheme.basicOpen_appLE, eq_bot_iff]
  rintro y ⟨-, hy⟩
  exact hs (hf y ▸ hy)

/-- If the germ at `y` of a section `t` is nilpotent, then `t` vanishes on a neighbourhood of `y`,
so `y` is not in the closure of the basic open of `t`. -/
theorem _root_.AlgebraicGeometry.Scheme.notMem_closure_basicOpen_of_isNilpotent_germ {y : X}
    (hy : y ∈ U) {t : Γ(X, U)} (h : IsNilpotent (X.presheaf.germ U y hy t)) :
    y ∉ closure (X.basicOpen t : Set X) := by
  obtain ⟨n, hn⟩ := h
  -- Some power `t ^ (n + 1)` restricts to zero on an open neighbourhood `V ⊆ U` of `y`.
  obtain ⟨V, hyV, iVU, _, hV⟩ := X.presheaf.germ_eq y hy hy (t ^ (n + 1)) 0
    (by rw [map_pow, pow_succ, hn, zero_mul, map_zero])
  rw [mem_closure_iff]
  push Not
  -- On `V`, the basic open of `t` agrees with that of the zero section, which is empty.
  refine ⟨V, V.isOpen, hyV, Set.eq_empty_iff_forall_notMem.mpr fun z ⟨hzV, hz⟩ ↦ ?_⟩
  have : z ∈ X.basicOpen (X.presheaf.map iVU.op (t ^ (n + 1))) := by
    rw [Scheme.basicOpen_res, Scheme.basicOpen_pow _ _ n.succ_pos]
    exact ⟨hzV, hz⟩
  rw [hV, map_zero, Scheme.basicOpen_zero] at this
  simp at this

end

end

namespace Scheme

/-- The whole space is a nonempty open subset of a nonempty scheme. -/
public instance instNonemptyTop {X : Scheme.{u}} [Nonempty X] :
    Nonempty ((⊤ : X.Opens) : Type u) :=
  let ⟨x⟩ := ‹Nonempty X›
  ⟨⟨x, trivial⟩⟩

/-- Let `𝒰` be an open cover of `X`. A subset `U` of `X` is dense if its preimage in every chart
of `𝒰` contains a dense subset. -/
public theorem _root_.AlgebraicGeometry.Scheme.OpenCover.dense_of_forall_dense_subset
    {X : Scheme.{u}} {U : Set X} (𝒰 : X.OpenCover) {s : ∀ i, Set (𝒰.X i)}
    (hs : ∀ i, Dense (s i)) (hsU : ∀ i, s i ⊆ 𝒰.f i ⁻¹' U) : Dense U := by
  refine dense_iff_inter_open.mpr fun V hV ⟨x, hxV⟩ ↦ ?_
  obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
  obtain ⟨z, hzV, hzs⟩ := (hs i).inter_open_nonempty _ (hV.preimage (𝒰.f i).continuous) ⟨y, hxV⟩
  exact ⟨_, hzV, hsU i hzs⟩

end Scheme

end AlgebraicGeometry

end TauCeti
