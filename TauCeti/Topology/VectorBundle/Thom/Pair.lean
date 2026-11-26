/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.TopPair
public import TauCeti.Topology.VectorBundle.Subbundle
public import TauCeti.Topology.VectorBundle.ZeroSection

/-!
# The Thom pair of a bundle

Let `E → B` be a bundle whose fibres have a zero element, and let `E₀ ⊆ E` be the complement of
the zero section (`TauCeti.zeroSectionCompl`). The *Thom pair* of the bundle is the topological pair
`(E, E₀)` (`TauCeti.thomPair`).

This file collects the structural definitions and functorial maps on Thom pairs that depend only on
the bundle total space and not on singular cohomology or Thom/Euler classes:

* `TauCeti.thomPair`: the Thom pair `(E, E₀)`.
* `TauCeti.thomPairOver`: the Thom pair `(E|_W, E₀|_W)` of the restriction to a subset `W` of the
  base; over the whole base it is `(E, E₀)` (`TauCeti.thomPairOverUnivIso`).
* `TauCeti.thomPairOverMap`: the restriction map `(E|_W, E₀|_W) ⟶ (E|_{W'}, E₀|_{W'})` for
  `W ⊆ W'`.
* `TauCeti.thomPairModelIso`, `TauCeti.subbundleThomPairModelIso`: changing the phantom model-fibre
  parameter of a Thom pair (or of a subbundle Thom pair) without changing the total-space topology.
* `TauCeti.thomPairMapOfNeZero`: a continuous map `f : X → E` taking nonzero values off a set `S`,
  as a map of pairs `(X, X ∖ S) ⟶ (E, E₀)`.
-/

public section

noncomputable section

open Bundle CategoryTheory Set

universe w

namespace TauCeti

section Pair

variable {B : Type w} (F : Type*) (E : B → Type w) [∀ b, Zero (E b)]

variable [TopologicalSpace (TotalSpace F E)]

/-- The Thom pair `(E, E₀)` of a bundle: its total space relative to the complement of the zero
section. -/
abbrev thomPair : TopPair.{w} :=
  TopPair.ofSubset (X := TopCat.of (TotalSpace F E)) (zeroSectionCompl F E)

/-- The Thom pair `(E|_W, E₀|_W)` of the restriction of a bundle to a subset `W` of its base: the
vectors over `W`, relative to the nonzero ones, as subspaces of the total space. -/
abbrev thomPairOver (W : Set B) : TopPair.{w} :=
  TopPair.ofInclusion (X := TopCat.of (TotalSpace F E))
    (inter_subset_left : π F E ⁻¹' W ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' W)

/-- Over the whole base, the Thom pair `(E|_B, E₀|_B)` of the restriction is the Thom pair
`(E, E₀)`. -/
def thomPairOverUnivIso : thomPairOver F E univ ≅ thomPair F E :=
  have := TopCat.isIso_restrictPreimagePairMap (X := TopCat.of (TotalSpace F E)) (π F E)
    (zeroSectionCompl F E) (S := univ) fun _ ↦ trivial
  asIso (TopCat.restrictPreimagePairMap _ _ univ)

/-- The isomorphism `thomPairOverUnivIso` is the inclusion `TopCat.restrictPreimagePairMap` of the
pair over the whole base into `(E, E₀)`. -/
theorem thomPairOverUnivIso_hom :
    (thomPairOverUnivIso F E).hom = TopCat.restrictPreimagePairMap (X := TopCat.of (TotalSpace F E))
      (π F E) (zeroSectionCompl F E) univ :=
  (rfl)

@[simp]
theorem thomPairOverUnivIso_hom_fst_apply (v : π F E ⁻¹' univ) :
    TopPair.Hom.fst (thomPairOverUnivIso F E).hom v = v.val :=
  TopCat.restrictPreimagePairMap_fst_apply (X := TopCat.of (TotalSpace F E)) (π F E)
    (zeroSectionCompl F E) univ v

/-- On total spaces, the isomorphism `thomPairOverUnivIso` is the inclusion of the subtype. -/
theorem thomPairOverUnivIso_hom_fst_eq :
    (TopPair.Hom.fst (thomPairOverUnivIso F E).hom).hom =
      ContinuousMap.subtypeVal (π F E ⁻¹' univ) :=
  ContinuousMap.ext fun v ↦ thomPairOverUnivIso_hom_fst_apply F E v

@[simp]
theorem thomPairOverUnivIso_hom_snd_apply (v : ↥(π F E ⁻¹' univ ∩ zeroSectionCompl F E)) :
    TopPair.Hom.snd (thomPairOverUnivIso F E).hom v = ⟨v.val, v.property.2⟩ :=
  TopCat.restrictPreimagePairMap_snd_apply (X := TopCat.of (TotalSpace F E)) (π F E)
    (zeroSectionCompl F E) univ v

@[simp]
theorem thomPairOverUnivIso_inv_fst_apply (v : TotalSpace F E) :
    TopPair.Hom.fst (thomPairOverUnivIso F E).inv v = ⟨v, trivial⟩ :=
  Subtype.ext ((thomPairOverUnivIso_hom_fst_apply F E _).symm.trans
    ((TopPair.proj₁.mapIso (thomPairOverUnivIso F E)).inv_hom_id_apply v))

@[simp]
theorem thomPairOverUnivIso_inv_snd_apply (v : zeroSectionCompl F E) :
    TopPair.Hom.snd (thomPairOverUnivIso F E).inv v = ⟨v.val, trivial, v.property⟩ :=
  Subtype.ext (congrArg Subtype.val ((TopPair.Hom.w_apply (thomPairOverUnivIso F E).inv v).trans
    (thomPairOverUnivIso_inv_fst_apply F E v.val)) :)

/-- For `W ⊆ W'`, the map of Thom pairs `(E|_W, E₀|_W) ⟶ (E|_{W'}, E₀|_{W'})` induced by the
inclusion. -/
def thomPairOverMap {W W' : Set B} (h : W ⊆ W') : thomPairOver F E W ⟶ thomPairOver F E W' :=
  TopPair.ofHom (TopCat.ofHom (ContinuousMap.inclusion (preimage_mono h)))
    (TopCat.ofHom (ContinuousMap.inclusion (inter_subset_inter_left _ (preimage_mono h))))
    (by ext; rfl)

@[simp]
theorem thomPairOverMap_fst_apply {W W' : Set B} (h : W ⊆ W') (v : π F E ⁻¹' W) :
    TopPair.Hom.fst (thomPairOverMap F E h) v = ⟨v.val, h v.property⟩ :=
  (rfl)

/-- The map of ambient spaces of `thomPairOverMap F E h` is the inclusion `E|_W ⊆ E|_{W'}`. -/
theorem thomPairOverMap_fst {W W' : Set B} (h : W ⊆ W') :
    TopPair.Hom.fst (thomPairOverMap F E h) =
      TopCat.ofHom (ContinuousMap.inclusion (preimage_mono h)) :=
  (rfl)

@[simp]
theorem thomPairOverMap_snd_apply {W W' : Set B} (h : W ⊆ W')
    (v : (thomPairOver F E W).snd) :
    TopPair.Hom.snd (thomPairOverMap F E h) v = ⟨v.val, h v.property.1, v.property.2⟩ :=
  (rfl)

@[simp]
theorem thomPairOverMap_self {W : Set B} : thomPairOverMap F E (subset_refl W) = 𝟙 _ :=
  TopPair.hom_ext_of_fst _ (TopCat.ext fun _ ↦ rfl)

@[reassoc (attr := simp)]
theorem thomPairOverMap_comp_thomPairOverMap {W W' W'' : Set B} (h : W ⊆ W') (h' : W' ⊆ W'') :
    thomPairOverMap F E h ≫ thomPairOverMap F E h' = thomPairOverMap F E (h.trans h') :=
  TopPair.hom_ext_of_fst _ (TopCat.ext fun _ ↦ rfl)

/-- For `W ⊆ W'`, the inclusion of Thom pairs `(E|_W, E₀|_W) ⟶ (E|_{W'}, E₀|_{W'})` followed by the
inclusion of `(E|_{W'}, E₀|_{W'})` into `(E, E₀)` is the inclusion of `(E|_W, E₀|_W)`. -/
@[reassoc (attr := simp)]
theorem thomPairOverMap_comp_restrictPreimagePairMap {W W' : Set B} (h : W ⊆ W') :
    thomPairOverMap F E h ≫ TopCat.restrictPreimagePairMap (X := TopCat.of (TotalSpace F E))
      (π F E) (zeroSectionCompl F E) W' = TopCat.restrictPreimagePairMap _ _ W :=
  TopPair.hom_ext_of_fst _ (TopCat.ext fun v ↦
    (TopCat.restrictPreimagePairMap_fst_apply _ _ _ _).trans
      (TopCat.restrictPreimagePairMap_fst_apply _ _ _ v).symm)

/-- **Changing the phantom model-fibre parameter of a Thom pair.** If two total-space topologies
for the same family `E` over `B` (with possibly different model-fibre types `F` and `F'`) make the
identity map `(b, v) ↦ (b, v)` continuous in both directions, their Thom pairs are isomorphic. -/
def thomPairModelIso {B : Type w} {F F' : Type*} {E : B → Type w}
    [TopologicalSpace (TotalSpace F E)] [TopologicalSpace (TotalSpace F' E)] [∀ b, Zero (E b)]
    (h₁ : Continuous fun v : TotalSpace F E ↦ TotalSpace.mk' F' v.proj v.snd)
    (h₂ : Continuous fun v : TotalSpace F' E ↦ TotalSpace.mk' F v.proj v.snd) :
    thomPair F E ≅ thomPair F' E :=
  TopPair.ofSubsetIso
    { toFun := fun v ↦ TotalSpace.mk' F' v.proj v.snd
      invFun := fun v ↦ TotalSpace.mk' F v.proj v.snd
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := h₁
      continuous_invFun := h₂ }
    fun _ ↦
      ⟨fun hv ↦ mem_zeroSectionCompl.2 (by exact (mem_zeroSectionCompl (F := F) (E := E)).1 hv),
       fun hv ↦ mem_zeroSectionCompl.2 (by exact (mem_zeroSectionCompl (F := F') (E := E)).1 hv)⟩

@[simp]
theorem thomPairModelIso_hom_fst_apply {B : Type w} {F F' : Type*} {E : B → Type w}
    [TopologicalSpace (TotalSpace F E)] [TopologicalSpace (TotalSpace F' E)] [∀ b, Zero (E b)]
    (h₁ : Continuous fun v : TotalSpace F E ↦ TotalSpace.mk' F' v.proj v.snd)
    (h₂ : Continuous fun v : TotalSpace F' E ↦ TotalSpace.mk' F v.proj v.snd)
    (v : TotalSpace F E) :
    TopPair.Hom.fst (thomPairModelIso h₁ h₂).hom v = TotalSpace.mk' F' v.proj v.snd := by
  rw [thomPairModelIso, TopPair.ofSubsetIso_hom]
  exact TopPair.ofSubsetMap_fst_apply (X := TopCat.of (TotalSpace F E)) _ _ v

@[simp]
theorem thomPairModelIso_hom_snd_apply {B : Type w} {F F' : Type*} {E : B → Type w}
    [TopologicalSpace (TotalSpace F E)] [TopologicalSpace (TotalSpace F' E)] [∀ b, Zero (E b)]
    (h₁ : Continuous fun v : TotalSpace F E ↦ TotalSpace.mk' F' v.proj v.snd)
    (h₂ : Continuous fun v : TotalSpace F' E ↦ TotalSpace.mk' F v.proj v.snd)
    (v : zeroSectionCompl F E) :
    (TopPair.Hom.snd (thomPairModelIso h₁ h₂).hom v).val =
      TotalSpace.mk' F' v.val.proj v.val.snd := by
  rw [thomPairModelIso, TopPair.ofSubsetIso_hom]
  exact TopPair.ofSubsetMap_snd_apply (X := TopCat.of (TotalSpace F E)) _ _ v

@[simp]
theorem thomPairModelIso_inv_fst_apply {B : Type w} {F F' : Type*} {E : B → Type w}
    [TopologicalSpace (TotalSpace F E)] [TopologicalSpace (TotalSpace F' E)] [∀ b, Zero (E b)]
    (h₁ : Continuous fun v : TotalSpace F E ↦ TotalSpace.mk' F' v.proj v.snd)
    (h₂ : Continuous fun v : TotalSpace F' E ↦ TotalSpace.mk' F v.proj v.snd)
    (v : TotalSpace F' E) :
    TopPair.Hom.fst (thomPairModelIso h₁ h₂).inv v = TotalSpace.mk' F v.proj v.snd := by
  rw [thomPairModelIso, TopPair.ofSubsetIso_inv]
  exact TopPair.ofSubsetMap_fst_apply (X := TopCat.of (TotalSpace F' E)) _ _ v

@[simp]
theorem thomPairModelIso_inv_snd_apply {B : Type w} {F F' : Type*} {E : B → Type w}
    [TopologicalSpace (TotalSpace F E)] [TopologicalSpace (TotalSpace F' E)] [∀ b, Zero (E b)]
    (h₁ : Continuous fun v : TotalSpace F E ↦ TotalSpace.mk' F' v.proj v.snd)
    (h₂ : Continuous fun v : TotalSpace F' E ↦ TotalSpace.mk' F v.proj v.snd)
    (v : zeroSectionCompl F' E) :
    (TopPair.Hom.snd (thomPairModelIso h₁ h₂).inv v).val =
      TotalSpace.mk' F v.val.proj v.val.snd := by
  rw [thomPairModelIso, TopPair.ofSubsetIso_inv]
  exact TopPair.ofSubsetMap_snd_apply (X := TopCat.of (TotalSpace F' E)) _ _ v

/-- **Changing the phantom model-fibre parameter of a subbundle Thom pair.** For a family `V` of
submodules of `E`, equipping its total space with `subbundleTopology P V` gives the same subspace
topology from the ambient bundle for any model-fibre parameter `F₁` or `F₂`, so the resulting
Thom pairs are isomorphic. -/
def subbundleThomPairModelIso {𝕜 : Type*} (P : Type*) {B : Type w} {E : B → Type w}
    [Semiring 𝕜] [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
    [TopologicalSpace (TotalSpace P E)] (F₁ F₂ : Type*) (V : ∀ b, Submodule 𝕜 (E b)) :
    letI := subbundleTopology P (F' := F₁) V
    letI := subbundleTopology P (F' := F₂) V
    thomPair F₁ (fun b ↦ V b) ≅ thomPair F₂ (fun b ↦ V b) :=
  letI := subbundleTopology P (F' := F₁) V
  letI := subbundleTopology P (F' := F₂) V
  thomPairModelIso
    ((isEmbedding_totalSpace_subbundle P F₂ V).continuous_iff.2
      (isEmbedding_totalSpace_subbundle P F₁ V).continuous)
    ((isEmbedding_totalSpace_subbundle P F₁ V).continuous_iff.2
      (isEmbedding_totalSpace_subbundle P F₂ V).continuous)

@[simp]
theorem subbundleThomPairModelIso_hom_fst_apply {𝕜 : Type*} (P : Type*) {B : Type w}
    {E : B → Type w} [Semiring 𝕜] [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
    [TopologicalSpace (TotalSpace P E)] (F₁ F₂ : Type*) (V : ∀ b, Submodule 𝕜 (E b))
    (v : TotalSpace F₁ fun b ↦ V b) :
    letI := subbundleTopology P (F' := F₁) V
    letI := subbundleTopology P (F' := F₂) V
    TopPair.Hom.fst (subbundleThomPairModelIso P F₁ F₂ V).hom v =
      TotalSpace.mk' F₂ v.proj v.snd :=
  letI := subbundleTopology P (F' := F₁) V
  letI := subbundleTopology P (F' := F₂) V
  thomPairModelIso_hom_fst_apply _ _ v

@[simp]
theorem subbundleThomPairModelIso_hom_snd_apply {𝕜 : Type*} (P : Type*) {B : Type w}
    {E : B → Type w} [Semiring 𝕜] [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
    [TopologicalSpace (TotalSpace P E)] (F₁ F₂ : Type*) (V : ∀ b, Submodule 𝕜 (E b))
    (v : zeroSectionCompl F₁ fun b ↦ V b) :
    letI := subbundleTopology P (F' := F₁) V
    letI := subbundleTopology P (F' := F₂) V
    (TopPair.Hom.snd (subbundleThomPairModelIso P F₁ F₂ V).hom v).val =
      TotalSpace.mk' F₂ v.val.proj v.val.snd :=
  letI := subbundleTopology P (F' := F₁) V
  letI := subbundleTopology P (F' := F₂) V
  thomPairModelIso_hom_snd_apply _ _ v

@[simp]
theorem subbundleThomPairModelIso_inv_fst_apply {𝕜 : Type*} (P : Type*) {B : Type w}
    {E : B → Type w} [Semiring 𝕜] [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
    [TopologicalSpace (TotalSpace P E)] (F₁ F₂ : Type*) (V : ∀ b, Submodule 𝕜 (E b))
    (v : TotalSpace F₂ fun b ↦ V b) :
    letI := subbundleTopology P (F' := F₁) V
    letI := subbundleTopology P (F' := F₂) V
    TopPair.Hom.fst (subbundleThomPairModelIso P F₁ F₂ V).inv v =
      TotalSpace.mk' F₁ v.proj v.snd :=
  letI := subbundleTopology P (F' := F₁) V
  letI := subbundleTopology P (F' := F₂) V
  thomPairModelIso_inv_fst_apply _ _ v

@[simp]
theorem subbundleThomPairModelIso_inv_snd_apply {𝕜 : Type*} (P : Type*) {B : Type w}
    {E : B → Type w} [Semiring 𝕜] [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
    [TopologicalSpace (TotalSpace P E)] (F₁ F₂ : Type*) (V : ∀ b, Submodule 𝕜 (E b))
    (v : zeroSectionCompl F₂ fun b ↦ V b) :
    letI := subbundleTopology P (F' := F₁) V
    letI := subbundleTopology P (F' := F₂) V
    (TopPair.Hom.snd (subbundleThomPairModelIso P F₁ F₂ V).inv v).val =
      TotalSpace.mk' F₁ v.val.proj v.val.snd :=
  letI := subbundleTopology P (F' := F₁) V
  letI := subbundleTopology P (F' := F₂) V
  thomPairModelIso_inv_snd_apply _ _ v

variable {F E} {X : Type w} [TopologicalSpace X]

/-- The map of pairs `(X, X ∖ S) ⟶ (E, E₀)` into the Thom pair of a bundle given by a continuous
map `f : X → E` which takes nonzero values off `S`. For a section `s` and `S` its zero set, this is
`s` as a map of pairs. -/
def thomPairMapOfNeZero (f : C(X, TotalSpace F E)) {S : Set X} (h : ∀ x ∉ S, (f x).snd ≠ 0) :
    TopPair.ofSubset (Sᶜ : Set (TopCat.of X)) ⟶ thomPair F E :=
  TopPair.ofSubsetMap (TopCat.ofHom f) fun x hx ↦ mem_zeroSectionCompl.2 (h x hx)

@[simp]
theorem thomPairMapOfNeZero_fst_apply (f : C(X, TotalSpace F E)) {S : Set X}
    (h : ∀ x ∉ S, (f x).snd ≠ 0) (x : X) : TopPair.Hom.fst (thomPairMapOfNeZero f h) x = f x :=
  TopPair.ofSubsetMap_fst_apply (X := TopCat.of X) _ _ x

theorem thomPairMapOfNeZero_fst (f : C(X, TotalSpace F E)) {S : Set X}
    (h : ∀ x ∉ S, (f x).snd ≠ 0) : TopPair.Hom.fst (thomPairMapOfNeZero f h) = TopCat.ofHom f :=
  TopPair.ofSubsetMap_fst _ _

/-- Precomposing `thomPairMapOfNeZero f` with the map of pairs induced by a continuous map `g`
gives `thomPairMapOfNeZero` of any map equal to `f ∘ g`. -/
theorem ofSubsetMap_comp_thomPairMapOfNeZero_of_comp_eq {Y : Type w} [TopologicalSpace Y]
    (f : C(X, TotalSpace F E)) {S : Set X} (h : ∀ x ∉ S, (f x).snd ≠ 0) (g : C(Y, X)) {T : Set Y}
    (hg : MapsTo (TopCat.ofHom g) (Tᶜ : Set (TopCat.of Y)) (Sᶜ : Set (TopCat.of X)))
    {f' : C(Y, TotalSpace F E)} (hf : f.comp g = f') (h' : ∀ y ∉ T, (f' y).snd ≠ 0) :
    TopPair.ofSubsetMap (TopCat.ofHom g) hg ≫ thomPairMapOfNeZero f h =
      thomPairMapOfNeZero f' h' := by
  subst hf
  exact TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ rfl

end Pair

end TauCeti
