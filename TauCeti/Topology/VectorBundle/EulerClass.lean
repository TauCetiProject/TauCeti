/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.VectorBundle.Constructions
public import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance
public import TauCeti.Topology.Category.TopPair
public import TauCeti.Topology.Category.TopPair.ContinuousLinearEquiv
public import TauCeti.Topology.VectorBundle.ModelFiber
public import TauCeti.Topology.VectorBundle.ZeroSection
import TauCeti.Topology.VectorBundle.Smul

/-!
# Thom classes and Euler classes of vector bundles

Let `E → B` be a real vector bundle with finite-dimensional model fibre `F` of rank `r`, and let
`E₀ ⊆ E` be the complement of the zero section (`TauCeti.zeroSectionCompl`), an open set
(`TauCeti.isOpen_zeroSectionCompl`). The *Thom pair* of
the bundle is the topological pair `(E, E₀)` (`TauCeti.thomPair`). A *Thom class* is a relative
class `u ∈ Hʳ(E, E₀)` whose restriction to every fibre pair `(E_b, E_b ∖ {0})` generates the
cohomology of that pair (`TauCeti.IsThomClass`). With ordinary integral coefficients (specified
below) this is a cohomological orientation of the bundle; by the Thom isomorphism theorem, which
is not formalized here, every orientation determines a unique Thom class, and `-u` belongs to the
opposite orientation.

The *Euler class* of a relative class `u ∈ Hⁿ(E, E₀)` is its image in `Hⁿ(B)` under the
restriction `Hⁿ(E, E₀) ⟶ Hⁿ(E)` followed by pullback along the zero section
(`TauCeti.eulerClass`). With ordinary integral coefficients, for a Thom class this is the Euler
class of the oriented bundle, the characteristic class whose evaluation on surfaces appears in
the Euler class inequalities for foliations.

The Euler class is natural under maps of Thom pairs covering a map of bases
(`TauCeti.eulerClass_naturality`), in particular under pullback of bundles
(`TauCeti.eulerClass_pullback`). A map of Thom pairs restricting to isomorphisms of fibre pairs
carries Thom classes to Thom classes (`TauCeti.IsThomClass.singularCohomologyMap`); in particular,
pullback of bundles does (`TauCeti.IsThomClass.pullback`). The zero section is homotopic, through
`t • s`, to any continuous section `s` (`TauCeti.zeroSectionHomotopy`). So if `s` is nonzero off a
set `S`, the Euler class of `u` is the image of the pull-back `s^* u ∈ Hⁿ(B, B ∖ S)`
(`TauCeti.eulerClass_eq_singularCohomologyMap_thomPairMapOfNeZero`). In particular, a bundle with a
nowhere-vanishing continuous section has zero Euler class
(`TauCeti.eulerClass_eq_zero_of_forall_ne_zero`): every relative class restricts to zero on `E₀`.
So a trivial bundle of positive rank has zero Euler class (`TauCeti.eulerClass_trivial_eq_zero`).

The projection `π : E → B` is a homotopy equivalence with homotopy inverse the zero section
(`TauCeti.VectorBundle.totalSpaceHomotopyEquiv`), so pullback along the zero section is an
isomorphism `Hⁿ(E) ≅ Hⁿ(B)` with inverse `π^*`
(`TauCeti.singularCohomologyMap_zeroSectionHom_comp_singularCohomologyMap_thomPairProj`,
`TauCeti.isIso_singularCohomologyMap_zeroSectionHom`,
`TauCeti.isIso_singularCohomologyMap_thomPairProj`); so pulling the Euler class of `u` back along
`π` gives the image of `u` in `Hⁿ(E)` (`TauCeti.singularCohomologyMap_thomPairProj_eulerClass`).
Replacing `Hⁿ(E)` by `Hⁿ(B)` in the long exact sequence of the Thom pair gives the exact sequence

`⋯ ⟶ Hᵐ(E, E₀) ⟶ Hᵐ(B) ⟶ Hᵐ(E₀) ⟶ Hᵐ⁺¹(E, E₀) ⟶ Hᵐ⁺¹(B) ⟶ ⋯`

of the Euler class maps, the pullback along the restriction `π₀ : E₀ → B` of the projection
(`TauCeti.zeroSectionComplProjHom`) and the connecting morphisms of the pair
(`TauCeti.exact_eulerClass_singularCohomologyMap_zeroSectionComplProjHom`,
`TauCeti.exact_singularCohomologyMap_zeroSectionComplProjHom_singularCohomologyδ`,
`TauCeti.exact_singularCohomologyδ_eulerClass`), the start of the Gysin sequence.

Cohomology is the singular cohomology of `TauCeti/AlgebraicTopology/Cohomology/`, with the same
general coefficients: `Hom(C(X; R), M)` in a `k`-linear abelian category `C`. Integral cohomology
uses `C := ModuleCat ℤ`, `k := ℤ`, and `R = M = ModuleCat.of ℤ ℤ`.

## Main definitions

* `TauCeti.thomPair`: the Thom pair `(E, E₀)`.
* `TauCeti.thomPairOver`: the Thom pair `(E|_W, E₀|_W)` of the restriction to a subset `W` of the
  base; over the whole base it is the Thom pair `(E, E₀)` (`TauCeti.thomPairOverUnivIso`).
* `TauCeti.thomPairOverMap`: the restriction map `(E|_W, E₀|_W) ⟶ (E|_{W'}, E₀|_{W'})` for
  `W ⊆ W'`.
* `TauCeti.fiberThomPairMap`, `TauCeti.fiberThomPairOverMap`: the inclusions of the fibre pair
  `(E_b, E_b ∖ {0})` into the Thom pair and into the Thom pair over a set containing `b`; over a
  subsingleton base, `fiberThomPairMap` is an isomorphism
  (`TauCeti.isIso_fiberThomPairMap_of_subsingleton`).
* `TauCeti.thomPairMapOfNeZero`: a continuous map `f : X → E` taking nonzero values off a set `S`,
  as a map of pairs `(X, X ∖ S) ⟶ (E, E₀)`.
* `TauCeti.thomPairProj`, `TauCeti.thomPairOverProj`: the projection of the total space to the base,
  and its restriction over `W ⊆ B`, as morphisms out of the ambient spaces of the Thom pairs.
* `TauCeti.zeroSectionComplProj`: the restriction `π₀ : E₀ → B` of the projection to the
  complement of the zero section, and `TauCeti.zeroSectionComplProjHom`, the same map as a
  morphism out of the subspace of the Thom pair.
* `TauCeti.IsThomClass`: a relative class restricting to a generator on every fibre.
* `TauCeti.zeroSectionHomotopy`: the straight-line homotopy `t • s` from the zero section to a
  continuous section `s`.
* `TauCeti.eulerClass`: the Euler class `Hⁿ(E, E₀) ⟶ Hⁿ(B)`.
* `TauCeti.negTotalSpace`, `TauCeti.negThomPairMap`: fibrewise negation, as a self-map of the
  total space and of the Thom pair; it does not change Euler classes
  (`TauCeti.singularCohomologyMap_negThomPairMap_comp_eulerClass`). On a fibre it is conjugate to
  negation of `F` (`TauCeti.fiberThomPairMap_comp_negThomPairMap`).

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9 (the fundamental class `u ∈ Hⁿ(E, E₀; ℤ)` of an oriented bundle, the Euler
  class, its naturality and its vanishing for a bundle with a nowhere-zero section), §10 (the
  Thom isomorphism) and §12 (the exact sequence of the pair `(E, E₀)` in the proof of the Gysin
  sequence, Theorem 12.2).
* A. Hatcher, *Vector Bundles and K-Theory*, §4.D (Thom classes).
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Set Module

universe w v u

namespace TauCeti

section Pair

variable {B : Type w} (F : Type*) (E : B → Type w) [∀ b, Zero (E b)]

variable [TopologicalSpace (TotalSpace F E)]

/-- The Thom pair `(E, E₀)` of a bundle: its total space relative to the complement of the zero
section. -/
abbrev thomPair : TopPair.{w} :=
  TopPair.ofSubset (X := TopCat.of (TotalSpace F E)) (zeroSectionCompl F E)

variable {F E} in
/-- The Thom pair of a bundle does not depend on its model fibre: when the topology on the total
space with model fibre `F'` is induced along the identity of points from the total space with model
fibre `F`, the identity of points is an isomorphism of Thom pairs `(E, E₀)`
(`TauCeti.totalSpaceModelFiberHomeomorph`). -/
def thomPairModelFiberIso {F' : Type*} [TopologicalSpace (TotalSpace F' E)]
    (h_ind : Topology.IsInducing fun p : TotalSpace F' E ↦ TotalSpace.mk' F p.proj p.snd) :
    thomPair F' E ≅ thomPair F E :=
  TopPair.ofSubsetIso (totalSpaceModelFiberHomeomorph F E h_ind) fun _ ↦ by simp

variable {F E} in
@[simp]
theorem thomPairModelFiberIso_hom_fst_apply {F' : Type*} [TopologicalSpace (TotalSpace F' E)]
    (h_ind : Topology.IsInducing fun p : TotalSpace F' E ↦ TotalSpace.mk' F p.proj p.snd)
    (p : TotalSpace F' E) :
    TopPair.Hom.fst (thomPairModelFiberIso h_ind).hom p = TotalSpace.mk' F p.proj p.snd := by
  simp only [thomPairModelFiberIso, TopPair.ofSubsetIso_hom]
  exact (TopPair.ofSubsetMap_fst_apply (X := TopCat.of (TotalSpace F' E))
    (B := zeroSectionCompl F' E) _ _ p).trans (totalSpaceModelFiberHomeomorph_apply h_ind p)

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

section Open

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

variable (F) in
include F in
/-- The nonzero vectors of a fibre of a real vector bundle form an open set. -/
theorem isOpen_compl_zero_fiber (b : B) : IsOpen ({0}ᶜ : Set (E b)) := by
  let e := (trivializationAt F E b).continuousLinearEquivAt ℝ b
    (FiberBundle.mem_baseSet_trivializationAt' b)
  have : ({0}ᶜ : Set (E b)) = e ⁻¹' {0}ᶜ := by
    ext x
    simp only [mem_compl_singleton_iff, mem_preimage]
    exact (map_ne_zero_iff _ e.injective).symm
  rw [this]
  exact isOpen_compl_singleton.preimage e.continuous

end Open

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] {R : C}
  {k : Type*} [Ring k] [Linear k C] {M : C}

section ThomClass

variable {B : Type w} [TopologicalSpace B] (F : Type*) [TopologicalSpace F] (E : B → Type w)
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [∀ b, Zero (E b)]

/-- The inclusion `(E_b, E_b ∖ {0}) ⟶ (E, E₀)` of the fibre over `b` into the Thom pair. -/
def fiberThomPairMap (b : B) :
    TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b)) ⟶ thomPair F E :=
  TopPair.ofSubsetMap (TopCat.ofHom ⟨TotalSpace.mk b, FiberBundle.continuous_totalSpaceMk F E b⟩)
    fun _ hx ↦ mem_zeroSectionCompl.2 hx

@[simp]
theorem fiberThomPairMap_fst_apply (b : B) (x : E b) :
    TopPair.Hom.fst (fiberThomPairMap F E b) x = TotalSpace.mk b x := by
  unfold fiberThomPairMap
  exact TopPair.ofSubsetMap_fst_apply _ _ _

/-- The map of ambient spaces of the fibre inclusion over `b` is `x ↦ (b, x)`. -/
theorem fiberThomPairMap_fst (b : B) :
    TopPair.Hom.fst (fiberThomPairMap F E b) =
      TopCat.ofHom ⟨TotalSpace.mk b, FiberBundle.continuous_totalSpaceMk F E b⟩ :=
  TopCat.ext (fiberThomPairMap_fst_apply F E b)

/-- The fibre inclusion of a Thom pair is the map of pairs induced by `x ↦ (b, x)`. -/
theorem fiberThomPairMap_eq_ofSubsetMap (b : B) :
    fiberThomPairMap F E b = TopPair.ofSubsetMap
      (TopCat.ofHom ⟨TotalSpace.mk b, FiberBundle.continuous_totalSpaceMk F E b⟩)
      (fun _ hx ↦ mem_zeroSectionCompl.2 hx) :=
  (rfl)

/-- Over a subsingleton base `B`, the inclusion `(E_b, E_b ∖ {0}) ⟶ (E, E₀)` of the fibre over `b`
into the Thom pair is an isomorphism in `TopPair`. -/
instance isIso_fiberThomPairMap_of_subsingleton [Subsingleton B] (b : B) :
    IsIso (fiberThomPairMap F E b) := by
  let e : E b ≃ₜ TotalSpace F E :=
    (Equiv.ofBijective (TotalSpace.mk b) ⟨TotalSpace.mk_injective b,
      fun ⟨b', x⟩ ↦ by cases Subsingleton.elim b b'; exact ⟨x, rfl⟩⟩).toHomeomorphOfIsInducing
        (FiberBundle.totalSpaceMk_isInducing F E b)
  have : IsIso (TopPair.Hom.fst (fiberThomPairMap F E b)) := by
    rw [fiberThomPairMap_fst]
    exact (TopCat.isoOfHomeo (X := TopCat.of (E b)) (Y := TopCat.of (TotalSpace F E)) e).isIso_hom
  exact TopPair.isIso_of_isIso_fst_of_surjective_snd _ fun ⟨⟨b', x⟩, hx⟩ ↦ by
    cases Subsingleton.elim b b'
    refine ⟨⟨x, mem_zeroSectionCompl.1 hx⟩, ?_⟩
    rw [fiberThomPairMap_eq_ofSubsetMap]
    exact Subtype.ext (TopPair.ofSubsetMap_snd_apply _ _ _)

/-- The projection `π : E ⟶ B` of a fibre bundle, as a morphism of topological spaces out of the
ambient space of its Thom pair. -/
def thomPairProj : (thomPair F E).fst ⟶ TopCat.of B :=
  TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩

/-- The projection of a Thom pair is the bundle projection `π F E`, so the pairs over subsets `W`
of the base built from it (as in `TopCat.pullbackCupRestrict`) are the Thom pairs
`thomPairOver F E W`. -/
theorem thomPairProj_def :
    thomPairProj F E = TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩ :=
  (rfl)

@[simp]
theorem thomPairProj_apply (v : TotalSpace F E) : thomPairProj F E v = v.proj :=
  (rfl)

/-- The projection `π₀ : E₀ → B` of the complement of the zero section to the base, the
restriction of the bundle projection. -/
@[expose] def zeroSectionComplProj : C(zeroSectionCompl F E, B) :=
  ⟨fun v ↦ (v : TotalSpace F E).proj, (FiberBundle.continuous_proj F E).comp continuous_subtypeVal⟩

@[simp]
theorem zeroSectionComplProj_apply (v : zeroSectionCompl F E) :
    zeroSectionComplProj F E v = (v : TotalSpace F E).proj :=
  (rfl)

/-- The projection `π₀ : E₀ → B` (`TauCeti.zeroSectionComplProj`) as a morphism of topological
spaces out of the subspace of the Thom pair. -/
def zeroSectionComplProjHom : (thomPair F E).snd ⟶ TopCat.of B :=
  TopCat.ofHom (zeroSectionComplProj F E)

theorem zeroSectionComplProjHom_def :
    zeroSectionComplProjHom F E = (thomPair F E).map ≫ thomPairProj F E :=
  (rfl)

@[simp]
theorem zeroSectionComplProjHom_apply (v : zeroSectionCompl F E) :
    zeroSectionComplProjHom F E v = (v : TotalSpace F E).proj :=
  thomPairProj_apply F E (v : TotalSpace F E)

/-- The fibre inclusion over `b` followed by the projection is constant at `b`. -/
theorem fiberThomPairMap_fst_comp_thomPairProj (b : B) :
    TopPair.Hom.fst (fiberThomPairMap F E b) ≫ thomPairProj F E =
      TopCat.ofHom (ContinuousMap.const _ b) :=
  TopCat.ext fun x ↦ congrArg TotalSpace.proj (fiberThomPairMap_fst_apply F E b x)

/-- The projection `E|_W ⟶ W` of a fibre bundle restricted to a subset `W` of its base, as a
morphism of topological spaces out of the ambient space of `TauCeti.thomPairOver`. -/
def thomPairOverProj (W : Set B) : (thomPairOver F E W).fst ⟶ TopCat.of W :=
  TopCat.ofHom
    ((⟨π F E, FiberBundle.continuous_proj F E⟩ : C(TotalSpace F E, B)).restrictPreimage W)

/-- `TauCeti.thomPairOverProj` is the preimage restriction of the bundle projection `π F E`,
matching the projection used in `TopCat.pullbackCupRestrict`. -/
theorem thomPairOverProj_def (W : Set B) :
    thomPairOverProj F E W =
      TopCat.ofHom
        ((⟨π F E, FiberBundle.continuous_proj F E⟩ : C(TotalSpace F E, B)).restrictPreimage W) :=
  (rfl)

/-- Evaluating `TauCeti.thomPairOverProj` returns the base projection as a point of `W`. -/
@[simp]
theorem thomPairOverProj_apply {W : Set B} (v : (thomPairOver F E W).fst) :
    thomPairOverProj F E W v = ⟨v.val.proj, v.property⟩ :=
  (rfl)

/-- For `W ⊆ W'`, the restriction map of Thom pairs commutes with `TauCeti.thomPairOverProj` and the
inclusion `W ↪ W'`. -/
@[reassoc]
theorem thomPairOverMap_fst_comp_thomPairOverProj {W W' : Set B} (h : W ⊆ W') :
    TopPair.Hom.fst (thomPairOverMap F E h) ≫ thomPairOverProj F E W' =
      thomPairOverProj F E W ≫ TopCat.ofHom (ContinuousMap.inclusion h) :=
  TopCat.ext fun _ ↦ rfl

/-- The inclusion of `(E|_W, E₀|_W)` into `(E, E₀)` commutes with `TauCeti.thomPairOverProj`,
`TauCeti.thomPairProj`, and the subtype inclusion `W ↪ B`. -/
@[reassoc]
theorem restrictPreimagePairMap_fst_comp_thomPairProj (W : Set B) :
    TopPair.Hom.fst (TopCat.restrictPreimagePairMap (X := TopCat.of (TotalSpace F E)) (π F E)
      (zeroSectionCompl F E) W) ≫ thomPairProj F E =
      thomPairOverProj F E W ≫ TopCat.ofHom ⟨Subtype.val, continuous_subtypeVal⟩ :=
  TopCat.ext fun v ↦ (TopCat.comp_app _ _ v).trans
    (congrArg (thomPairProj F E) (TopCat.restrictPreimagePairMap_fst_apply _ _ W v))

/-- The inclusion `(E_b, E_b ∖ {0}) ⟶ (E|_W, E₀|_W)` of the fibre over a point `b ∈ W` into the
Thom pair of the restriction to `W`. -/
@[expose] def fiberThomPairOverMap {W : Set B} {b : B} (hb : b ∈ W) :
    TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b)) ⟶ thomPairOver F E W :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun x ↦ ⟨TotalSpace.mk b x, hb⟩,
      (FiberBundle.continuous_totalSpaceMk F E b).subtype_mk _⟩)
    (TopCat.ofHom ⟨fun x ↦ ⟨TotalSpace.mk b x.val, hb, mem_zeroSectionCompl.2 x.property⟩,
      ((FiberBundle.continuous_totalSpaceMk F E b).comp continuous_subtypeVal).subtype_mk _⟩)
    (by ext; rfl)

@[simp]
theorem fiberThomPairOverMap_fst_apply {W : Set B} {b : B} (hb : b ∈ W) (x : E b) :
    TopPair.Hom.fst (fiberThomPairOverMap F E hb) x = ⟨TotalSpace.mk b x, hb⟩ :=
  (rfl)

/-- The map of ambient spaces of the fibre inclusion over `b ∈ W` is `x ↦ (b, x)`. -/
theorem fiberThomPairOverMap_fst {W : Set B} {b : B} (hb : b ∈ W) :
    TopPair.Hom.fst (fiberThomPairOverMap F E hb) =
      TopCat.ofHom ⟨fun x ↦ ⟨TotalSpace.mk b x, hb⟩,
        (FiberBundle.continuous_totalSpaceMk F E b).subtype_mk _⟩ :=
  (rfl)

/-- The fibre inclusion over `b ∈ W` into `(E|_W, E₀|_W)` followed by `TauCeti.thomPairOverProj` is
constant at `⟨b, hb⟩`. -/
@[reassoc]
theorem fiberThomPairOverMap_fst_comp_thomPairOverProj {W : Set B} {b : B} (hb : b ∈ W) :
    TopPair.Hom.fst (fiberThomPairOverMap F E hb) ≫ thomPairOverProj F E W =
      TopCat.ofHom (ContinuousMap.const _ ⟨b, hb⟩) :=
  TopCat.ext fun _ ↦ rfl

/-- The fibre inclusion into `(E|_W, E₀|_W)` followed by the inclusion of `(E|_W, E₀|_W)` into
`(E, E₀)` is the fibre inclusion into the Thom pair `(E, E₀)`. -/
@[reassoc (attr := simp)]
theorem fiberThomPairOverMap_comp_restrictPreimagePairMap {W : Set B} {b : B} (hb : b ∈ W) :
    fiberThomPairOverMap F E hb ≫ TopCat.restrictPreimagePairMap
      (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) W = fiberThomPairMap F E b :=
  TopPair.hom_ext_of_fst _ (TopCat.ext fun x ↦
    (TopCat.restrictPreimagePairMap_fst_apply _ _ _ _).trans
      (fiberThomPairMap_fst_apply F E b x).symm)

/-- The fibre inclusions commute with the restriction maps of Thom pairs. -/
@[reassoc (attr := simp)]
theorem fiberThomPairOverMap_comp_thomPairOverMap {W W' : Set B} (h : W ⊆ W') {b : B}
    (hb : b ∈ W) :
    fiberThomPairOverMap F E hb ≫ thomPairOverMap F E h = fiberThomPairOverMap F E (h hb) :=
  TopPair.hom_ext_of_fst _ (TopCat.ext fun _ ↦ rfl)

/-- Over the whole base, the fibre inclusion into `(E|_B, E₀|_B)` is the fibre inclusion into the
Thom pair `(E, E₀)`. -/
@[reassoc (attr := simp)]
theorem fiberThomPairOverMap_comp_thomPairOverUnivIso_hom (b : B) :
    fiberThomPairOverMap F E (mem_univ b) ≫ (thomPairOverUnivIso F E).hom =
      fiberThomPairMap F E b :=
  TopPair.hom_ext_of_fst _ (TopCat.ext fun x ↦
    (thomPairOverUnivIso_hom_fst_apply F E _).trans (fiberThomPairMap_fst_apply F E b x).symm)

/-- The fibre inclusion over `b` into the Thom pair `(E, E₀)`, followed by the inclusion of the
pair over the whole base into the pair over a set `W'` covering the base, is the fibre inclusion
into the pair over any `W ⊆ W'` containing `b`, followed by the inclusion of the pair over `W`
into the pair over `W'`. -/
theorem fiberThomPairMap_comp_thomPairOverUnivIso_inv_comp_thomPairOverMap {W W' : Set B}
    (h : univ ⊆ W') (h' : W ⊆ W') {b : B} (hb : b ∈ W) :
    fiberThomPairMap F E b ≫ (thomPairOverUnivIso F E).inv ≫ thomPairOverMap F E h =
      fiberThomPairOverMap F E hb ≫ thomPairOverMap F E h' := by
  rw [← fiberThomPairOverMap_comp_thomPairOverUnivIso_hom, Category.assoc, Iso.hom_inv_id_assoc,
    fiberThomPairOverMap_comp_thomPairOverMap, fiberThomPairOverMap_comp_thomPairOverMap]

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A Thom class of a real vector bundle with finite-dimensional model fibre `F` of rank
`r = finrank ℝ F`: a relative class `u ∈ Hʳ(E, E₀)` whose restriction to the fibre pair
`(E_b, E_b ∖ {0})` over every point `b` generates the `k`-module `Hʳ(E_b, E_b ∖ {0})`. With ordinary
integral coefficients (`C := ModuleCat ℤ`, `k := ℤ`, `R = M = ModuleCat.of ℤ ℤ`) this is the notion
of a cohomological orientation of the bundle.

Finite-dimensionality of `F` is part of the predicate: otherwise `finrank ℝ F = 0` and the
degree-zero condition would hold vacuously, so a bundle with infinite-dimensional fibres has no
Thom class. -/
def IsThomClass (u : (thomPair F E).singularCohomology R k M (finrank ℝ F)) : Prop :=
  FiniteDimensional ℝ F ∧
    ∀ b, Submodule.span k {TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ u} = ⊤

variable {F E} in
theorem isThomClass_iff {u : (thomPair F E).singularCohomology R k M (finrank ℝ F)} :
    IsThomClass F E u ↔ FiniteDimensional ℝ F ∧
      ∀ b, Submodule.span k {TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ u} = ⊤ :=
  Iff.rfl

variable {F E} in
/-- Negation preserves the fibrewise generator condition, so the negative of a Thom class is a
Thom class. -/
theorem IsThomClass.neg {u : (thomPair F E).singularCohomology R k M (finrank ℝ F)}
    (hu : IsThomClass F E u) : IsThomClass F E (-u) := by
  refine ⟨hu.1, fun b ↦ ?_⟩
  rw [map_neg, ← Set.neg_singleton, Submodule.span_neg]
  exact hu.2 b

variable {F E} in
/-- **Thom classes pull back along fibrewise isomorphisms.** Let `φ : (E', E'₀) ⟶ (E, E₀)` be a map
of Thom pairs which, over a map of bases `g : B' → B`, restricts on the fibre over every `b'` to an
isomorphism `ψ b'` of fibre pairs `(E'_{b'}, E'_{b'} ∖ {0}) ≅ (E_{g b'}, E_{g b'} ∖ {0})`. Then `φ`
pulls Thom classes of `E` back to Thom classes of `E'`. -/
theorem IsThomClass.singularCohomologyMap {B' : Type w} [TopologicalSpace B'] {E' : B' → Type w}
    [TopologicalSpace (TotalSpace F E')] [∀ b, TopologicalSpace (E' b)] [FiberBundle F E']
    [∀ b, Zero (E' b)] {u : (thomPair F E).singularCohomology R k M (finrank ℝ F)}
    (hu : IsThomClass F E u) (φ : thomPair F E' ⟶ thomPair F E) (g : B' → B)
    (ψ : ∀ b', TopPair.ofSubset (X := TopCat.of (E' b')) ({0}ᶜ : Set (E' b')) ≅
      TopPair.ofSubset (X := TopCat.of (E (g b'))) ({0}ᶜ : Set (E (g b'))))
    (hψ : ∀ b', fiberThomPairMap F E' b' ≫ φ = (ψ b').hom ≫ fiberThomPairMap F E (g b')) :
    IsThomClass F E' (TopPair.singularCohomologyMap φ _ u) := by
  refine ⟨hu.1, fun b' ↦ ?_⟩
  rw [← ConcreteCategory.comp_apply, ← TopPair.singularCohomologyMap_comp, hψ,
    TopPair.singularCohomologyMap_comp, ConcreteCategory.comp_apply]
  -- The isomorphism `ψ b'` induces a linear isomorphism `e` in cohomology, carrying generators to
  -- generators; by definition of the cohomology functor, `e` applies
  -- `TopPair.singularCohomologyMap (ψ b').hom`.
  let e : (TopPair.ofSubset (X := TopCat.of (E (g b'))) ({0}ᶜ : Set (E (g b')))).singularCohomology
      R k M (finrank ℝ F) ≃ₗ[k]
      (TopPair.ofSubset (X := TopCat.of (E' b')) ({0}ᶜ : Set (E' b'))).singularCohomology
        R k M (finrank ℝ F) :=
    ((TopPair.singularCohomologyFunctor R k M (finrank ℝ F)).mapIso (ψ b').op).toLinearEquiv
  have h := (Submodule.map_eq_top_iff (e := e)).2 (hu.2 (g b'))
  rw [← Submodule.span_image_linearEquiv e, Set.image_singleton] at h
  exact h

end ThomClass

section Pullback

/-- The canonical map from the total space of a pullback bundle `f *ᵖ E` to the total space of `E`
keeps each vector, so the nonzero vectors of `f *ᵖ E` are exactly the points sent to nonzero vectors
of `E`. -/
theorem preimage_pullbackLift_zeroSectionCompl {B B' : Type w} {F : Type*} {E : B → Type w}
    [∀ b, AddCommMonoid (E b)] (f : B' → B) :
    Pullback.lift f ⁻¹' zeroSectionCompl F E = zeroSectionCompl F (f *ᵖ E) := by
  ext z
  simp only [mem_preimage, mem_zeroSectionCompl, Pullback.lift_snd]
  -- The zero of the fibre of `f *ᵖ E` over `x` is, by definition, the zero of `E (f x)`.
  rfl

variable {B : Type w} [TopologicalSpace B] (F : Type*) (E : B → Type w)
  [TopologicalSpace (TotalSpace F E)] [∀ b, Zero (E b)] {B' : Type w}
  [TopologicalSpace B'] (f : C(B', B))

/-- The zero of a fibre of the pullback `f*E` is the zero of the corresponding fibre of `E`. -/
local instance pullbackFiberZero (b' : B') : Zero (((⇑f) *ᵖ E) b') :=
  inferInstanceAs (Zero (E (f b')))

/-- The map `(f*E, (f*E)₀) ⟶ (E, E₀)` of Thom pairs covering a continuous map `f : B' → B`. -/
def pullbackThomPairMap : thomPair F ((⇑f) *ᵖ E) ⟶ thomPair F E :=
  TopPair.ofSubsetMap (TopCat.ofHom ⟨Pullback.lift f, Pullback.continuous_lift F E f⟩)
    fun _ hv ↦ mem_zeroSectionCompl.2 (mem_zeroSectionCompl.1 hv :)

@[simp]
theorem pullbackThomPairMap_fst_apply (v : TotalSpace F ((⇑f) *ᵖ E)) :
    TopPair.Hom.fst (pullbackThomPairMap F E f) v = Pullback.lift f v := by
  unfold pullbackThomPairMap
  exact TopPair.ofSubsetMap_fst_apply _ _ _

/-- On nonzero vectors, the map of Thom pairs `(f*E, (f*E)₀) ⟶ (E, E₀)` is the canonical map of the
pull-back. -/
@[simp]
theorem pullbackThomPairMap_snd_apply (v : (thomPair F ((⇑f) *ᵖ E)).snd) :
    (TopPair.Hom.snd (pullbackThomPairMap F E f) v).val = Pullback.lift f v.val := by
  unfold pullbackThomPairMap
  exact TopPair.ofSubsetMap_snd_apply _ _ _

variable [TopologicalSpace F] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

/-- The fibre of the Thom pair of `f*E` over `b'` is included in the Thom pair of `E` as the fibre
over `f b'`. -/
theorem fiberThomPairMap_comp_pullbackThomPairMap (b' : B') :
    fiberThomPairMap F ((⇑f) *ᵖ E) b' ≫ pullbackThomPairMap F E f = fiberThomPairMap F E (f b') :=
  TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ (TopCat.ext fun _ ↦ rfl)

/-- The canonical map from the total space of a pull-back bundle covers the map of bases. -/
theorem pullbackThomPairMap_fst_comp_thomPairProj :
    TopPair.Hom.fst (pullbackThomPairMap F E f) ≫ thomPairProj F E =
      thomPairProj F ((⇑f) *ᵖ E) ≫ TopCat.ofHom f :=
  TopCat.ext fun v ↦ congrArg TotalSpace.proj (pullbackThomPairMap_fst_apply F E f v)

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {F E} in
/-- The pullback of a Thom class of `E` along a continuous map `f` is a Thom class of `f*E`. -/
theorem IsThomClass.pullback {u : (thomPair F E).singularCohomology R k M (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    IsThomClass F ((⇑f) *ᵖ E) (TopPair.singularCohomologyMap (pullbackThomPairMap F E f) _ u) :=
  hu.singularCohomologyMap _ f (fun _ ↦ Iso.refl _) fun b' ↦
    (fiberThomPairMap_comp_pullbackThomPairMap F E f b').trans (Category.id_comp _).symm

end Pullback

section EulerClass

variable {B : Type w} [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- The zero section `B ⟶ E` of a real vector bundle, as a morphism of topological spaces into
the ambient space of the Thom pair. -/
def zeroSectionHom : TopCat.of B ⟶ (thomPair F E).fst :=
  TopCat.ofHom ⟨zeroSection F E, Trivialization.continuous_zeroSection ℝ⟩

@[simp]
theorem zeroSectionHom_apply (b : B) : zeroSectionHom F E b = zeroSection F E b :=
  (rfl)

/-- The zero section followed by the projection is the identity of the base. -/
@[reassoc (attr := simp)]
theorem zeroSectionHom_comp_thomPairProj : zeroSectionHom F E ≫ thomPairProj F E = 𝟙 _ :=
  TopCat.ext fun b ↦ by
    rw [ConcreteCategory.comp_apply, zeroSectionHom_apply, thomPairProj_apply]
    rfl

variable (R k M) in
/-- Pulling a class of the base back to the total space and then along the zero section gives the
class back. -/
@[reassoc (attr := simp)]
theorem singularCohomologyMap_thomPairProj_comp_singularCohomologyMap_zeroSectionHom (n : ℕ) :
    TopCat.singularCohomologyMap (R := R) (k := k) (M := M) (thomPairProj F E) n ≫
      TopCat.singularCohomologyMap (zeroSectionHom F E) n = 𝟙 _ := by
  rw [← TopCat.singularCohomologyMap_comp, zeroSectionHom_comp_thomPairProj,
    TopCat.singularCohomologyMap_id]

variable (R k M) in
/-- **The zero section induces an isomorphism on cohomology**, with inverse the pullback along the
projection (`TauCeti.VectorBundle.totalSpaceHomotopyEquiv`): pulling a class of the total space
back along the zero section and then to the total space gives the class back. -/
@[reassoc (attr := simp)]
theorem singularCohomologyMap_zeroSectionHom_comp_singularCohomologyMap_thomPairProj (n : ℕ) :
    TopCat.singularCohomologyMap (R := R) (k := k) (M := M) (zeroSectionHom F E) n ≫
      TopCat.singularCohomologyMap (thomPairProj F E) n = 𝟙 _ := by
  let e := VectorBundle.totalSpaceHomotopyEquiv F E
  have hπ : TopCat.ofHom e.toFun = thomPairProj F E :=
    TopCat.ext fun v ↦ (congrFun (VectorBundle.coe_totalSpaceHomotopyEquiv F E) v).trans
      (thomPairProj_apply F E v).symm
  have hs : TopCat.ofHom e.invFun = zeroSectionHom F E :=
    TopCat.ext fun b ↦ (congrFun (VectorBundle.coe_totalSpaceHomotopyEquiv_symm F E) b).trans
      (zeroSectionHom_apply F E b).symm
  have h := (e.singularCohomologyIso R k M n).inv_hom_id
  rwa [ContinuousMap.HomotopyEquiv.singularCohomologyIso_hom,
    ContinuousMap.HomotopyEquiv.singularCohomologyIso_inv, hπ, hs] at h

variable {F E} in
@[simp]
theorem singularCohomologyMap_zeroSectionHom_singularCohomologyMap_thomPairProj_apply {n : ℕ}
    (x : (TopCat.of B).singularCohomology R k M n) :
    TopCat.singularCohomologyMap (zeroSectionHom F E) n
      (TopCat.singularCohomologyMap (thomPairProj F E) n x) = x := by
  rw [← ConcreteCategory.comp_apply,
    singularCohomologyMap_thomPairProj_comp_singularCohomologyMap_zeroSectionHom,
    ConcreteCategory.id_apply]

variable {F E} in
@[simp]
theorem singularCohomologyMap_thomPairProj_singularCohomologyMap_zeroSectionHom_apply {n : ℕ}
    (x : (thomPair F E).fst.singularCohomology R k M n) :
    TopCat.singularCohomologyMap (thomPairProj F E) n
      (TopCat.singularCohomologyMap (zeroSectionHom F E) n x) = x := by
  rw [← ConcreteCategory.comp_apply,
    singularCohomologyMap_zeroSectionHom_comp_singularCohomologyMap_thomPairProj,
    ConcreteCategory.id_apply]

/-- Pulling back along the projection is an isomorphism `Hⁿ(B) ≅ Hⁿ(E)`, with inverse the pull-back
along the zero section. -/
instance isIso_singularCohomologyMap_thomPairProj (n : ℕ) :
    IsIso (TopCat.singularCohomologyMap (R := R) (k := k) (M := M) (thomPairProj F E) n) :=
  ⟨_, singularCohomologyMap_thomPairProj_comp_singularCohomologyMap_zeroSectionHom R k M F E n,
    singularCohomologyMap_zeroSectionHom_comp_singularCohomologyMap_thomPairProj R k M F E n⟩

/-- Pulling back along the zero section is an isomorphism `Hⁿ(E) ≅ Hⁿ(B)`, with inverse the
pull-back along the projection. -/
instance isIso_singularCohomologyMap_zeroSectionHom (n : ℕ) :
    IsIso (TopCat.singularCohomologyMap (R := R) (k := k) (M := M) (zeroSectionHom F E) n) :=
  ⟨_, singularCohomologyMap_zeroSectionHom_comp_singularCohomologyMap_thomPairProj R k M F E n,
    singularCohomologyMap_thomPairProj_comp_singularCohomologyMap_zeroSectionHom R k M F E n⟩

@[simp]
theorem inv_singularCohomologyMap_thomPairProj (n : ℕ) :
    inv (TopCat.singularCohomologyMap (R := R) (k := k) (M := M) (thomPairProj F E) n) =
      TopCat.singularCohomologyMap (zeroSectionHom F E) n :=
  IsIso.inv_eq_of_hom_inv_id
    (singularCohomologyMap_thomPairProj_comp_singularCohomologyMap_zeroSectionHom R k M F E n)

@[simp]
theorem inv_singularCohomologyMap_zeroSectionHom (n : ℕ) :
    inv (TopCat.singularCohomologyMap (R := R) (k := k) (M := M) (zeroSectionHom F E) n) =
      TopCat.singularCohomologyMap (thomPairProj F E) n :=
  IsIso.inv_eq_of_hom_inv_id
    (singularCohomologyMap_zeroSectionHom_comp_singularCohomologyMap_thomPairProj R k M F E n)

/-- Pulling back along the projection is injective on cohomology: the zero section pulls it back. -/
theorem singularCohomologyMap_thomPairProj_injective (n : ℕ) :
    Function.Injective
      (TopCat.singularCohomologyMap (R := R) (k := k) (M := M) (thomPairProj F E) n) :=
  Function.LeftInverse.injective
    singularCohomologyMap_zeroSectionHom_singularCohomologyMap_thomPairProj_apply

/-- Fibrewise negation `v ↦ -v` of a real vector bundle, written `v ↦ (-1) • v`, as a self-map of
its total space. -/
def negTotalSpace : C(TotalSpace F E, TotalSpace F E) where
  toFun v := TotalSpace.mk' F v.proj ((-1 : ℝ) • v.snd)
  continuous_toFun := continuous_const.smul_totalSpace continuous_id

@[simp]
theorem negTotalSpace_apply (v : TotalSpace F E) :
    negTotalSpace F E v = TotalSpace.mk' F v.proj ((-1 : ℝ) • v.snd) :=
  (rfl)

/-- Fibrewise negation `v ↦ -v`, as a self-map of the Thom pair `(E, E₀)`. -/
def negThomPairMap : thomPair F E ⟶ thomPair F E :=
  TopPair.ofSubsetMap (TopCat.ofHom (negTotalSpace F E)) fun _ hv ↦
    mem_zeroSectionCompl.2 (smul_ne_zero (neg_ne_zero.2 one_ne_zero) (mem_zeroSectionCompl.1 hv))

@[simp]
theorem negThomPairMap_fst_apply (v : TotalSpace F E) :
    TopPair.Hom.fst (negThomPairMap F E) v = TotalSpace.mk' F v.proj ((-1 : ℝ) • v.snd) :=
  TopPair.ofSubsetMap_fst_apply (X := TopCat.of (TotalSpace F E)) _ _ v

/-- Fibrewise negation fixes the zero section. -/
theorem zeroSectionHom_comp_negThomPairMap_fst :
    zeroSectionHom F E ≫ TopPair.Hom.fst (negThomPairMap F E) = zeroSectionHom F E :=
  TopCat.ext fun b ↦ (negThomPairMap_fst_apply F E _).trans
    (congrArg (TotalSpace.mk' F b) (smul_zero (-1 : ℝ)))

variable {F E} in
/-- The straight-line homotopy `t • s` from the zero section to a continuous section `s`. -/
def zeroSectionHomotopy {s : ∀ b, E b} (hs : Continuous fun b ↦ TotalSpace.mk' F b (s b)) :
    TopCat.Homotopy (zeroSectionHom F E) (TopCat.ofHom ⟨_, hs⟩) where
  toFun p := TotalSpace.mk' F p.2 ((p.1 : ℝ) • s p.2)
  continuous_toFun :=
    (continuous_subtypeVal.comp continuous_fst).smul_totalSpace (hs.comp continuous_snd)
  map_zero_left b := (congrArg (TotalSpace.mk' F b) (zero_smul ℝ (s b))).trans
    (zeroSectionHom_apply F E b).symm
  map_one_left b := congrArg (TotalSpace.mk' F b) (one_smul ℝ (s b))

variable (R k M) in
/-- The Euler class `e(u) ∈ Hⁿ(B)` of a relative class `u ∈ Hⁿ(E, E₀)` of a real vector bundle, as
a morphism `Hⁿ(E, E₀) ⟶ Hⁿ(B)`: restriction from the Thom pair to the total space, followed by
pullback along the zero section. With ordinary integral coefficients (`C := ModuleCat ℤ`,
`k := ℤ`, `R = M = ModuleCat.of ℤ ℤ`), the Euler class of an oriented bundle is the image of its
Thom class (`TauCeti.IsThomClass`). -/
def eulerClass (n : ℕ) :
    (thomPair F E).singularCohomology R k M n ⟶ (TopCat.of B).singularCohomology R k M n :=
  (thomPair F E).singularCohomologyπ R k M n ≫ TopCat.singularCohomologyMap (zeroSectionHom F E) n

theorem eulerClass_def (n : ℕ) :
    eulerClass R k M F E n = (thomPair F E).singularCohomologyπ R k M n ≫
      TopCat.singularCohomologyMap (zeroSectionHom F E) n :=
  (rfl)

/-- **Naturality of the Euler class.** A map of Thom pairs `φ : (E', E'₀) ⟶ (E, E₀)` which carries
the zero section over a map of bases `f : B' ⟶ B` to the zero section intertwines the Euler
classes. -/
theorem eulerClass_naturality {B' : Type w} [TopologicalSpace B'] {F' : Type*}
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] {E' : B' → Type w}
    [TopologicalSpace (TotalSpace F' E')] [∀ b, AddCommMonoid (E' b)] [∀ b, Module ℝ (E' b)]
    [∀ b, TopologicalSpace (E' b)] [FiberBundle F' E'] [VectorBundle ℝ F' E']
    (φ : thomPair F' E' ⟶ thomPair F E) (f : TopCat.of B' ⟶ TopCat.of B)
    (h : zeroSectionHom F' E' ≫ TopPair.Hom.fst φ = f ≫ zeroSectionHom F E) (n : ℕ) :
    TopPair.singularCohomologyMap φ n ≫ eulerClass R k M F' E' n =
      eulerClass R k M F E n ≫ TopCat.singularCohomologyMap f n := by
  rw [eulerClass_def, eulerClass_def, Category.assoc, ← TopCat.singularCohomologyMap_comp, ← h,
    TopCat.singularCohomologyMap_comp, TopPair.singularCohomologyπ_naturality_assoc]

/-- **The Euler class through a section.** If a real vector bundle has a continuous section `s`
which is nonzero off a set `S ⊆ B`, then the Euler class of a relative class `u ∈ Hⁿ(E, E₀)` is the
image in `Hⁿ(B)` of its pull-back `s^* u ∈ Hⁿ(B, B ∖ S)` along `s : (B, B ∖ S) ⟶ (E, E₀)`: the zero
section is homotopic to `s` through `t • s`. -/
theorem eulerClass_eq_singularCohomologyMap_thomPairMapOfNeZero {s : ∀ b, E b}
    (hs : Continuous fun b ↦ TotalSpace.mk' F b (s b)) {S : Set B} (hS : ∀ b ∉ S, s b ≠ 0)
    (n : ℕ) :
    eulerClass R k M F E n =
      TopPair.singularCohomologyMap (thomPairMapOfNeZero ⟨_, hs⟩ hS) n ≫
        (TopPair.ofSubset (Sᶜ : Set (TopCat.of B))).singularCohomologyπ R k M n := by
  have h := TopPair.singularCohomologyπ_naturality (R := R) (k := k) (M := M)
    (thomPairMapOfNeZero ⟨_, hs⟩ hS) n
  rw [thomPairMapOfNeZero_fst] at h
  rw [eulerClass_def]
  exact (congrArg ((thomPair F E).singularCohomologyπ R k M n ≫ ·)
    ((zeroSectionHomotopy hs).congr_singularCohomologyMap R k M n)).trans h

/-- **A nowhere-vanishing section kills the Euler class.** If a real vector bundle has a continuous
section `s` with `s b ≠ 0` for every `b`, then its Euler class vanishes in every degree: the zero
section is homotopic through `t • s` to `s`, which takes values in `E₀`, and every relative class
restricts to zero on `E₀`. -/
theorem eulerClass_eq_zero_of_forall_ne_zero {s : ∀ b, E b}
    (hs : Continuous fun b ↦ TotalSpace.mk' F b (s b)) (hs₀ : ∀ b, s b ≠ 0) (n : ℕ) :
    eulerClass R k M F E n = 0 := by
  -- The map `Hⁿ(B, B ∖ ∅) ⟶ Hⁿ(B)` vanishes, as `B ∖ ∅` is the whole of `B`.
  have h : ∀ T : Set (TopCat.of B), T = univ →
      (TopPair.ofSubset T).singularCohomologyπ R k M n = 0 := by
    rintro _ rfl
    exact TopPair.singularCohomologyπ_ofSubset_univ _ n
  rw [eulerClass_eq_singularCohomologyMap_thomPairMapOfNeZero F E hs (S := ∅) (fun b _ ↦ hs₀ b),
    h _ compl_empty]
  exact comp_zero

/-- **The Euler class is invariant under fibrewise negation**: pulling a relative class back along
`v ↦ -v` does not change its Euler class, since negation fixes the zero section. -/
theorem singularCohomologyMap_negThomPairMap_comp_eulerClass (n : ℕ) :
    TopPair.singularCohomologyMap (negThomPairMap F E) n ≫ eulerClass R k M F E n =
      eulerClass R k M F E n := by
  rw [eulerClass_naturality F E (negThomPairMap F E) (𝟙 _)
    ((zeroSectionHom_comp_negThomPairMap_fst F E).trans (Category.id_comp _).symm),
    TopCat.singularCohomologyMap_id, Category.comp_id]

variable {B' : Type w} [TopologicalSpace B'] (f : C(B', B)) in
/-- The Euler class of a pullback bundle `f*E` is the pullback along `f` of the Euler class of
`E`. -/
theorem eulerClass_pullback (n : ℕ) :
    TopPair.singularCohomologyMap (pullbackThomPairMap F E f) n ≫
        eulerClass R k M F ((⇑f) *ᵖ E) n =
      eulerClass R k M F E n ≫ TopCat.singularCohomologyMap (TopCat.ofHom f) n :=
  eulerClass_naturality F E _ _
    (TopCat.ext fun _ ↦ (pullbackThomPairMap_fst_apply F E f _).trans rfl) n

variable (R k M)

/-- **Exactness at the cohomology of the base**: `Hᵐ(E, E₀) ⟶ Hᵐ(B) ⟶ Hᵐ(E₀)`, the Euler class map
followed by the pullback along `π₀ : E₀ → B`, is exact. -/
theorem exact_eulerClass_singularCohomologyMap_zeroSectionComplProjHom (m : ℕ) :
    Function.Exact (eulerClass R k M F E m)
      (TopCat.singularCohomologyMap (zeroSectionComplProjHom F E) m) := by
  have hex : Function.Exact ((thomPair F E).singularCohomologyπ R k M m)
      (TopCat.singularCohomologyMap (thomPair F E).map m) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      ((thomPair F E).singularCohomology_exact_space R k M m)
  -- Transport exactness of `Hᵐ(E, E₀) ⟶ Hᵐ(E) ⟶ Hᵐ(E₀)` along `π^* : Hᵐ(B) ≅ Hᵐ(E)`.
  intro y
  rw [zeroSectionComplProjHom_def, TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply,
    hex]
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨x, ?_⟩, fun ⟨x, hx⟩ ↦ ⟨x, ?_⟩⟩
  · rw [eulerClass_def, ConcreteCategory.comp_apply, hx,
      singularCohomologyMap_zeroSectionHom_singularCohomologyMap_thomPairProj_apply]
  · rw [← hx, eulerClass_def, ConcreteCategory.comp_apply,
      singularCohomologyMap_thomPairProj_singularCohomologyMap_zeroSectionHom_apply]

/-- **Exactness at the cohomology of `E₀`**: `Hˡ(B) ⟶ Hˡ(E₀) ⟶ Hᵐ(E, E₀)`, the pullback along
`π₀ : E₀ → B` followed by the connecting morphism of the pair `(E, E₀)`, is exact, for
`l + 1 = m`. -/
theorem exact_singularCohomologyMap_zeroSectionComplProjHom_singularCohomologyδ (l m : ℕ)
    (hl : l + 1 = m) :
    Function.Exact (TopCat.singularCohomologyMap (zeroSectionComplProjHom F E) l)
      ((thomPair F E).singularCohomologyδ R k M l m hl) := by
  have hex : Function.Exact (TopCat.singularCohomologyMap (thomPair F E).map l)
      ((thomPair F E).singularCohomologyδ R k M l m hl) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      ((thomPair F E).singularCohomology_exact_subspace R k M l m hl)
  -- Transport exactness of `Hˡ(E) ⟶ Hˡ(E₀) ⟶ Hᵐ(E, E₀)` along `π^* : Hˡ(B) ≅ Hˡ(E)`.
  intro y
  rw [hex, zeroSectionComplProjHom_def, TopCat.singularCohomologyMap_comp]
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨TopCat.singularCohomologyMap (zeroSectionHom F E) l x, ?_⟩,
    fun ⟨x, hx⟩ ↦ ⟨TopCat.singularCohomologyMap (thomPairProj F E) l x, hx⟩⟩
  rwa [ConcreteCategory.comp_apply,
    singularCohomologyMap_thomPairProj_singularCohomologyMap_zeroSectionHom_apply]

/-- **Exactness at relative cohomology**: `Hˡ(E₀) ⟶ Hᵐ(E, E₀) ⟶ Hᵐ(B)`, the connecting morphism of
the pair `(E, E₀)` followed by the Euler class map, is exact, for `l + 1 = m`. -/
theorem exact_singularCohomologyδ_eulerClass (l m : ℕ) (hl : l + 1 = m) :
    Function.Exact ((thomPair F E).singularCohomologyδ R k M l m hl) (eulerClass R k M F E m) := by
  have hex : Function.Exact ((thomPair F E).singularCohomologyδ R k M l m hl)
      ((thomPair F E).singularCohomologyπ R k M m) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      ((thomPair F E).singularCohomology_exact_relative R k M l m hl)
  -- The Euler class map is `Hᵐ(E, E₀) ⟶ Hᵐ(E)` followed by the isomorphism `s^*`.
  intro y
  rw [← hex y, eulerClass_def, ConcreteCategory.comp_apply]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, map_zero]⟩
  rw [← singularCohomologyMap_thomPairProj_singularCohomologyMap_zeroSectionHom_apply
    ((thomPair F E).singularCohomologyπ R k M m y), h, map_zero]

/-- The Euler class map followed by the pullback along `π₀ : E₀ → B` is zero. -/
@[reassoc (attr := simp)]
theorem eulerClass_comp_singularCohomologyMap_zeroSectionComplProjHom (m : ℕ) :
    eulerClass R k M F E m ≫ TopCat.singularCohomologyMap (zeroSectionComplProjHom F E) m = 0 := by
  ext y
  exact
    (exact_eulerClass_singularCohomologyMap_zeroSectionComplProjHom R k M F E
      m).apply_apply_eq_zero y

/-- The pullback along `π₀ : E₀ → B` followed by the connecting morphism of the pair `(E, E₀)` is
zero. -/
@[reassoc (attr := simp)]
theorem singularCohomologyMap_zeroSectionComplProjHom_comp_singularCohomologyδ (l m : ℕ)
    (hl : l + 1 = m) :
    TopCat.singularCohomologyMap (zeroSectionComplProjHom F E) l ≫
      (thomPair F E).singularCohomologyδ R k M l m hl = 0 := by
  ext y
  exact (exact_singularCohomologyMap_zeroSectionComplProjHom_singularCohomologyδ R k M F E l m
    hl).apply_apply_eq_zero y

/-- The connecting morphism of the pair `(E, E₀)` followed by the Euler class map is zero. -/
@[reassoc (attr := simp)]
theorem singularCohomologyδ_comp_eulerClass (l m : ℕ) (hl : l + 1 = m) :
    (thomPair F E).singularCohomologyδ R k M l m hl ≫ eulerClass R k M F E m = 0 := by
  ext y
  exact (exact_singularCohomologyδ_eulerClass R k M F E l m hl).apply_apply_eq_zero y

/-- Pulling the Euler class of a relative class `u ∈ Hⁿ(E, E₀)` back along the projection gives
the image of `u` in `Hⁿ(E)`. -/
@[simp]
theorem singularCohomologyMap_thomPairProj_eulerClass (n : ℕ)
    (u : (thomPair F E).singularCohomology R k M n) :
    TopCat.singularCohomologyMap (thomPairProj F E) n (eulerClass R k M F E n u) =
      (thomPair F E).singularCohomologyπ R k M n u := by
  rw [eulerClass_def, ConcreteCategory.comp_apply,
    singularCohomologyMap_thomPairProj_singularCohomologyMap_zeroSectionHom_apply]

end EulerClass

section FiberNeg

variable {B : Type w} [TopologicalSpace B] (F : Type w) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- **Fibrewise negation is conjugate to negation of `F`.** On the fibre over `b`, read through a
continuous linear equivalence `t : E b ≃L[ℝ] F`, the map `negThomPairMap` is
`t⁻¹ ∘ (x ↦ -x) ∘ t`. -/
theorem fiberThomPairMap_comp_negThomPairMap (b : B) (t : E b ≃L[ℝ] F) :
    fiberThomPairMap F E b ≫ negThomPairMap F E =
      t.complZeroPairIso.hom ≫ (ContinuousLinearEquiv.neg ℝ : F ≃L[ℝ] F).complZeroPairIso.hom ≫
        t.complZeroPairIso.inv ≫ fiberThomPairMap F E b := by
  refine TopPair.hom_ext_of_fst _ (TopCat.ext fun (x : E b) ↦ ?_)
  have h₁ : TopPair.Hom.fst t.complZeroPairIso.inv
      (TopPair.Hom.fst (ContinuousLinearEquiv.neg ℝ : F ≃L[ℝ] F).complZeroPairIso.hom
        (TopPair.Hom.fst t.complZeroPairIso.hom x)) = (-1 : ℝ) • x := by
    have h : t.symm (-t x) = (-1 : ℝ) • x := by
      simpa using t.symm_apply_apply ((-1 : ℝ) • x)
    simp only [ContinuousLinearEquiv.complZeroPairIso_hom_fst_apply,
      ContinuousLinearEquiv.complZeroPairIso_inv_fst_apply, ContinuousLinearEquiv.neg_apply]
    exact h
  -- The ambient map of a composite of maps of pairs is the composite of the ambient maps. After
  -- `TopPair.Hom.fst_comp`, `ConcreteCategory.comp_apply` and `ContinuousMap.comp_apply` do not
  -- fire: the intermediate objects are `TopPair.ofSubset` carriers that agree with the types of
  -- the composed maps only after unfolding. So `change` states the iterated applications.
  change TopPair.Hom.fst (negThomPairMap F E) (TopPair.Hom.fst (fiberThomPairMap F E b) x) =
    TopPair.Hom.fst (fiberThomPairMap F E b) (TopPair.Hom.fst t.complZeroPairIso.inv
      (TopPair.Hom.fst (ContinuousLinearEquiv.neg ℝ : F ≃L[ℝ] F).complZeroPairIso.hom
        (TopPair.Hom.fst t.complZeroPairIso.hom x)))
  rw [h₁]
  exact (congrArg _ (fiberThomPairMap_fst_apply F E b x)).trans
    ((negThomPairMap_fst_apply F E _).trans (fiberThomPairMap_fst_apply F E b _).symm)

end FiberNeg

/-- A trivial real vector bundle `B × V` of positive rank has zero Euler class in every degree. -/
theorem eulerClass_trivial_eq_zero (B : Type w) [TopologicalSpace B] (V : Type w)
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Nontrivial V] (n : ℕ) :
    eulerClass R k M V (Trivial B V) n = 0 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  exact eulerClass_eq_zero_of_forall_ne_zero (s := fun _ ↦ x) V (Trivial B V)
    ((Trivial.homeomorphProd B V).symm.continuous.comp (continuous_id.prodMk continuous_const))
    (fun _ ↦ hx) n

end TauCeti
