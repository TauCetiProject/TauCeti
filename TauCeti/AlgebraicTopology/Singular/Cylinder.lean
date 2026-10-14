/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Empty
public import TauCeti.AlgebraicTopology.Singular.Excision
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.AlgebraicTopology.Singular.Triple

/-!
# The relative homology of a cylinder modulo its ends

For a topological space `X`, the cylinder pair `(X × I, X × ∂I)`, where `∂I = {0, 1}`, has
relative singular homology `Hₙ₊₁(X × I, X × ∂I) ≅ Hₙ(X)`, naturally in `X`, and
`H₀(X × I, X × ∂I) = 0`.  Coefficients are an object of an abelian category with coproducts.

The isomorphism comes from the triple `(X × I, X × ∂I, X × {0})`.  The bottom end `X × {0}` is a
strong deformation retract of the cylinder, so the relative homology of `(X × I, X × {0})`
vanishes and the connecting morphism `Hₙ₊₁(X × I, X × ∂I) ⟶ Hₙ(X × ∂I, X × {0})` of the triple is
an isomorphism.  Excising the bottom end, the top end `x ↦ (x, 1)` induces an isomorphism
`Hₙ(X) ⟶ Hₙ(X × ∂I, X × {0})`.

The isomorphism is characterized by the connecting morphism of the pair: under
`Hₙ₊₁(X × I, X × ∂I) ≅ Hₙ(X)`, the connecting morphism `Hₙ₊₁(X × I, X × ∂I) ⟶ Hₙ(X × ∂I)` is the
difference `ι₁ - ι₀` of the maps induced by the two ends
(`TauCeti.singularHomologyδ_cylinderBoundaryPair`).  This is the form in which the computation
enters the homology of spaces obtained by gluing the two ends of a cylinder, such as mapping tori:
after the gluing, `ι₁ - ι₀` becomes `f_* - id` for the gluing map `f`.

## Main declarations

* `TauCeti.cylinderBoundaryPair X`: the pair `(X × I, X × ∂I)`, with the inclusions
  `TauCeti.cylinderBoundaryι₀` and `TauCeti.cylinderBoundaryι₁` of the two ends and the maps of
  pairs `TauCeti.cylinderBoundaryPairMap` induced by maps of spaces.
* `TauCeti.singularHomologyCylinderBoundaryPairIso`: `Hₙ₊₁(X × I, X × ∂I) ≅ Hₙ(X)`, natural in `X`
  (`TauCeti.singularHomologyCylinderBoundaryPairIso_hom_naturality`).
* `TauCeti.singularHomologyδ_cylinderBoundaryPair`: the connecting morphism of the pair is the
  difference of the maps induced by the two ends.
* `TauCeti.isZero_singularHomology_cylinderBoundaryPair_zero`: `H₀(X × I, X × ∂I) = 0`.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1: the long exact sequence of a triple and
  excision (Theorem 2.20).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Topology unitInterval

universe w v u

namespace TauCeti

variable (X : TopCat.{w})

/-- The ends `X × ∂I = X × {0, 1}` of the cylinder `X × I`. -/
def cylinderBoundary : Set (X × I) := Prod.snd ⁻¹' {0, 1}

@[simp]
lemma mem_cylinderBoundary {p : X × I} : p ∈ cylinderBoundary X ↔ p.2 = 0 ∨ p.2 = 1 := Iff.rfl

/-- The cylinder pair `(X × I, X × ∂I)`. -/
abbrev cylinderBoundaryPair : TopPair.{w} :=
  TopPair.ofSubset (X := TopCat.of (X × I)) (cylinderBoundary X)

/-- The inclusion `x ↦ (x, 0)` of `X` as the bottom end of the cylinder. -/
def cylinderBoundaryι₀ : X ⟶ (cylinderBoundaryPair X).snd :=
  TopCat.ofHom ⟨fun x ↦ ⟨(x, 0), (mem_cylinderBoundary X).2 (Or.inl rfl)⟩, by fun_prop⟩

/-- The inclusion `x ↦ (x, 1)` of `X` as the top end of the cylinder. -/
def cylinderBoundaryι₁ : X ⟶ (cylinderBoundaryPair X).snd :=
  TopCat.ofHom ⟨fun x ↦ ⟨(x, 1), (mem_cylinderBoundary X).2 (Or.inr rfl)⟩, by fun_prop⟩

@[simp]
lemma cylinderBoundaryι₀_apply (x : X) : (cylinderBoundaryι₀ X x).1 = (x, 0) := (rfl)

@[simp]
lemma cylinderBoundaryι₁_apply (x : X) : (cylinderBoundaryι₁ X x).1 = (x, 1) := (rfl)

lemma isEmbedding_cylinderBoundaryι₀ : IsEmbedding (cylinderBoundaryι₀ X) :=
  (isEmbedding_prodMkLeft (0 : I)).codRestrict (cylinderBoundary X) fun _ ↦
    (mem_cylinderBoundary X).2 (Or.inl rfl)

lemma isEmbedding_cylinderBoundaryι₁ : IsEmbedding (cylinderBoundaryι₁ X) :=
  (isEmbedding_prodMkLeft (1 : I)).codRestrict (cylinderBoundary X) fun _ ↦
    (mem_cylinderBoundary X).2 (Or.inr rfl)

variable {X} in
/-- The map of cylinder pairs `(X × I, X × ∂I) ⟶ (Y × I, Y × ∂I)` induced by `g : X ⟶ Y`. -/
def cylinderBoundaryPairMap {Y : TopCat.{w}} (g : X ⟶ Y) :
    cylinderBoundaryPair X ⟶ cylinderBoundaryPair Y :=
  TopPair.ofSubsetMap (TopCat.ofHom (g.hom.prodMap (ContinuousMap.id I))) fun _ hp ↦
    (mem_cylinderBoundary Y).2 ((mem_cylinderBoundary X).1 hp)

variable {X} in
@[simp]
lemma cylinderBoundaryPairMap_fst_apply {Y : TopCat.{w}} (g : X ⟶ Y) (p : X × I) :
    TopPair.Hom.fst (cylinderBoundaryPairMap g) p = (g p.1, p.2) :=
  TopPair.ofSubsetMap_fst_apply (X := TopCat.of (X × I)) _ _ p

variable {X} in
@[simp]
lemma cylinderBoundaryPairMap_snd_apply {Y : TopCat.{w}} (g : X ⟶ Y)
    (p : (cylinderBoundaryPair X).snd) :
    (TopPair.Hom.snd (cylinderBoundaryPairMap g) p).1 = (g p.1.1, p.1.2) :=
  TopPair.ofSubsetMap_snd_apply _ _ _

@[simp]
lemma cylinderBoundaryPairMap_id : cylinderBoundaryPairMap (𝟙 X) = 𝟙 (cylinderBoundaryPair X) :=
  TopPair.ofSubsetMap_id _

variable {X} in
@[reassoc]
lemma cylinderBoundaryPairMap_comp {Y Z : TopCat.{w}} (g : X ⟶ Y) (g' : Y ⟶ Z) :
    cylinderBoundaryPairMap (g ≫ g') = cylinderBoundaryPairMap g ≫ cylinderBoundaryPairMap g' :=
  TopPair.ofSubsetMap_comp (TopCat.ofHom (g.hom.prodMap (ContinuousMap.id I)))
    (TopCat.ofHom (g'.hom.prodMap (ContinuousMap.id I))) _ _ _

variable {X} in
@[reassoc (attr := simp)]
lemma cylinderBoundaryι₀_comp_cylinderBoundaryPairMap {Y : TopCat.{w}} (g : X ⟶ Y) :
    cylinderBoundaryι₀ X ≫ TopPair.Hom.snd (cylinderBoundaryPairMap g) =
      g ≫ cylinderBoundaryι₀ Y := by
  ext x
  exact Subtype.ext (TopPair.ofSubsetMap_snd_apply _ _ _)

variable {X} in
@[reassoc (attr := simp)]
lemma cylinderBoundaryι₁_comp_cylinderBoundaryPairMap {Y : TopCat.{w}} (g : X ⟶ Y) :
    cylinderBoundaryι₁ X ≫ TopPair.Hom.snd (cylinderBoundaryPairMap g) =
      g ≫ cylinderBoundaryι₁ Y := by
  ext x
  exact Subtype.ext (TopPair.ofSubsetMap_snd_apply _ _ _)

/-- The projection `X × I ⟶ X`. -/
private def cylinderProj : (cylinderBoundaryPair X).fst ⟶ X :=
  TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

/-- The projection `X × ∂I ⟶ X`. -/
private abbrev cylinderBoundaryProj : (cylinderBoundaryPair X).snd ⟶ X :=
  (cylinderBoundaryPair X).map ≫ cylinderProj X

private lemma cylinderBoundaryι₀_proj : cylinderBoundaryι₀ X ≫ cylinderBoundaryProj X = 𝟙 X :=
  rfl

private lemma cylinderBoundaryι₁_proj : cylinderBoundaryι₁ X ≫ cylinderBoundaryProj X = 𝟙 X :=
  rfl

/-- The triple `(X × I, X × ∂I, X)`, with `X` included as the bottom end. -/
private abbrev cylinderTriple : TopTriple.{w} :=
  TopTriple.of (cylinderBoundaryι₀ X) (cylinderBoundaryPair X).map
    (isEmbedding_cylinderBoundaryι₀ X) (cylinderBoundaryPair X).isEmbedding_map

/-- The bottom end `X × {0}` of the cylinder. -/
private def cylinderBottom : Set (X × I) := Prod.snd ⁻¹' {0}

private lemma mem_cylinderBottom {p : X × I} : p ∈ cylinderBottom X ↔ p.2 = 0 := Iff.rfl

section Homology

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- The relative homology of the cylinder modulo its bottom end vanishes: the identity of the
cylinder is homotopic, through maps preserving the bottom end, to the collapse onto it. -/
private lemma isZero_singularHomology_cylinderBottom (n : ℕ) :
    IsZero ((TopPair.ofSubset (X := TopCat.of (X × I)) (cylinderBottom X)).singularHomology
      R n) := by
  let c : TopCat.of (X × I) ⟶ TopCat.of (X × I) := TopCat.ofHom ⟨fun p ↦ (p.1, 0), by fun_prop⟩
  let F : TopCat.Homotopy (𝟙 (TopCat.of (X × I))) c :=
    { toFun := fun q ↦ (q.2.1, σ q.1 * q.2.2)
      continuous_toFun := by fun_prop
      map_zero_left := fun p ↦ by simp
      map_one_left := fun p ↦ by simp [c] }
  have hF : ∀ (τ : I) (p : TopCat.of (X × I)), p ∈ cylinderBottom X →
      F (τ, p) ∈ cylinderBottom X := by
    intro τ p hp
    rw [mem_cylinderBottom] at hp ⊢
    exact (congrArg (σ τ * ·) hp).trans (mul_zero _)
  let g : TopCat.of (X × I) ⟶
      (TopPair.ofSubset (X := TopCat.of (X × I)) (cylinderBottom X)).snd :=
    TopCat.ofHom ⟨fun p ↦ ⟨(p.1, 0), (mem_cylinderBottom X).2 rfl⟩, by fun_prop⟩
  have hc : Set.MapsTo c (cylinderBottom X) (cylinderBottom X) := fun p _ ↦
    (mem_cylinderBottom X).2 rfl
  have H : TopPair.Homotopy (𝟙 _) (TopPair.ofSubsetMap c hc) := by
    rw [← TopPair.ofSubsetMap_id (X := TopCat.of (X × I)) (B := cylinderBottom X) fun _ hx ↦ hx]
    exact TopPair.ofSubsetHomotopy F hF
  -- By construction, `g` followed by the inclusion of the bottom end is the collapse `c`.
  exact TopPair.isZero_singularHomology_of_homotopy H g
    ((rfl : g ≫ _ = c).trans (TopPair.ofSubsetMap_fst _ _).symm) R n

/-- The pair `(X × I, X × {0})` as a subset pair maps isomorphically onto the total pair of
`cylinderTriple X`. -/
private def cylinderBottomToTotal :
    TopPair.ofSubset (X := TopCat.of (X × I)) (cylinderBottom X) ⟶
      TopTriple.totalPair.obj (cylinderTriple X) :=
  TopPair.ofHom (𝟙 _) (TopCat.ofHom ⟨fun p ↦ p.1.1, by fun_prop⟩) (by
    ext p
    exact Prod.ext rfl ((mem_cylinderBottom X).1 p.2).symm)

private instance : IsIso (cylinderBottomToTotal X) :=
  have : IsIso (TopPair.Hom.fst (cylinderBottomToTotal X)) :=
    inferInstanceAs (IsIso (𝟙 (TopCat.of (X × I))))
  TopPair.isIso_of_isIso_fst_of_surjective_snd _ fun x ↦
    ⟨⟨(x, 0), (mem_cylinderBottom X).2 rfl⟩, rfl⟩

/-- The relative homology of `(X × I, X)`, the total pair of `cylinderTriple X`, vanishes. -/
private lemma isZero_singularHomology_cylinderTriple_totalPair (n : ℕ) :
    IsZero ((TopTriple.totalPair.obj (cylinderTriple X)).singularHomology R n) :=
  (isZero_singularHomology_cylinderBottom X R n).of_iso
    (asIso (TopPair.singularHomologyMap (cylinderBottomToTotal X) R n)).symm

/-- The connecting morphism `Hₙ₊₁(X × I, X × ∂I) ⟶ Hₙ(X × ∂I, X)` of `cylinderTriple X` is an
isomorphism, since the total pair has vanishing homology. -/
private instance isIso_singularHomologyδ_cylinderTriple (n : ℕ) :
    IsIso ((cylinderTriple X).singularHomologyδ R (n + 1) n) :=
  (cylinderTriple X).isIso_singularHomologyδ_of_isZero R (n + 1) n
    (isZero_singularHomology_cylinderTriple_totalPair X R (n + 1))
    (isZero_singularHomology_cylinderTriple_totalPair X R n)

/-- The top end `x ↦ (x, 1)` as a map of pairs `(X, ∅) ⟶ (X × ∂I, X)`. -/
private def cylinderTopToInner :
    TopPair.incl.obj X ⟶ TopTriple.innerPair.obj (cylinderTriple X) :=
  TopPair.ofHom (cylinderBoundaryι₁ X) (TopCat.isInitialPEmpty.to _) (by ext x; induction x)

/-- Excision of the bottom end: the top end induces isomorphisms
`Hₙ(X) ≅ Hₙ(X, ∅) ⟶ Hₙ(X × ∂I, X)`. -/
private instance isIso_singularHomologyMap_cylinderTopToInner (n : ℕ) :
    IsIso (TopPair.singularHomologyMap (cylinderTopToInner X) R n) := by
  refine TopPair.isIso_singularHomologyMap_of_open_cover R (cylinderTopToInner X)
    (isEmbedding_cylinderBoundaryι₁ X) ?_
    (fun b : Bool ↦ (fun p : (cylinderBoundaryPair X).snd ↦ p.1.2) ⁻¹' {bif b then 0 else 1}ᶜ)
    (fun b ↦ isClosed_singleton.isOpen_compl.preimage (by fun_prop)) ?_ ?_ n
  · rintro x ⟨y, hy⟩
    exact absurd (congrArg (fun p : (cylinderBoundaryPair X).snd ↦ p.1.2) hy) zero_ne_one
  · refine Set.eq_univ_of_forall fun p ↦ Set.mem_iUnion.2 ?_
    by_cases hp : p.1.2 = 0
    · exact ⟨false, by simp [hp]⟩
    · exact ⟨true, by simpa using hp⟩
  · intro b
    cases b
    · refine Or.inl fun p hp ↦ ⟨p.1.1, Subtype.ext (Prod.ext rfl ?_)⟩
      exact (((mem_cylinderBoundary X).1 p.2).resolve_right (by simpa using hp)).symm
    · refine Or.inr fun p hp ↦ ⟨p.1.1, Subtype.ext (Prod.ext rfl ?_)⟩
      exact (((mem_cylinderBoundary X).1 p.2).resolve_left (by simpa using hp)).symm

/-- The comparison `Hₙ(X) ⟶ Hₙ(X × ∂I, X)` induced by the top end. -/
private abbrev cylinderTopComparison (n : ℕ) :
    ((singularHomologyFunctor A n).obj R).obj X ⟶
      (TopTriple.innerPair.obj (cylinderTriple X)).singularHomology R n :=
  ((singularHomologyFunctor A n).obj R).map (cylinderBoundaryι₁ X) ≫
    (TopTriple.innerPair.obj (cylinderTriple X)).singularHomologyπ R n

private instance (n : ℕ) : IsIso (cylinderTopComparison X R n) := by
  have h : cylinderTopComparison X R n = (TopPair.incl.obj X).singularHomologyπ R n ≫
      TopPair.singularHomologyMap (cylinderTopToInner X) R n :=
    SSetPair.homologyπ_naturality (TopPair.toSSetPair.map (cylinderTopToInner X)) R n
  have hπ : IsIso ((TopPair.incl.obj X).singularHomologyπ R n) := inferInstance
  rw [h]
  exact IsIso.comp_isIso' hπ (isIso_singularHomologyMap_cylinderTopToInner X R n)

/-- The relative homology `H₀(X × I, X × ∂I)` vanishes: every point of the cylinder is joined to
its ends by a path. -/
theorem isZero_singularHomology_cylinderBoundaryPair_zero :
    IsZero ((cylinderBoundaryPair X).singularHomology R 0) :=
  (isZero_singularHomology_cylinderTriple_totalPair X R 0).of_epi
    (TopPair.singularHomologyMap (TopTriple.totalToOuter.app (cylinderTriple X)) R 0)

/-- **The homology of a cylinder modulo its ends**: `Hₙ₊₁(X × I, X × ∂I) ≅ Hₙ(X)`.  It is the
connecting morphism of the triple `(X × I, X × ∂I, X × {0})` followed by the inverse of the map
`Hₙ(X) ⟶ Hₙ(X × ∂I, X × {0})` induced by the top end. -/
def singularHomologyCylinderBoundaryPairIso (n : ℕ) :
    (cylinderBoundaryPair X).singularHomology R (n + 1) ≅
      ((singularHomologyFunctor A n).obj R).obj X :=
  asIso ((cylinderTriple X).singularHomologyδ R (n + 1) n rfl) ≪≫
    (asIso (cylinderTopComparison X R n)).symm

private lemma singularHomologyCylinderBoundaryPairIso_hom_comp (n : ℕ) :
    (singularHomologyCylinderBoundaryPairIso X R n).hom ≫ cylinderTopComparison X R n =
      (cylinderBoundaryPair X).singularHomologyδ R (n + 1) n ≫
        (TopTriple.innerPair.obj (cylinderTriple X)).singularHomologyπ R n := by
  refine Eq.trans ?_ ((cylinderTriple X).singularHomologyδ_eq_comp_singularHomologyπ R (n + 1) n)
  simp [singularHomologyCylinderBoundaryPairIso]

/-- **The connecting morphism of the cylinder pair.**  Under
`Hₙ₊₁(X × I, X × ∂I) ≅ Hₙ(X)`, the connecting morphism to `Hₙ(X × ∂I)` is the difference of the
maps induced by the top and bottom ends. -/
theorem singularHomologyδ_cylinderBoundaryPair (n : ℕ) :
    (cylinderBoundaryPair X).singularHomologyδ R (n + 1) n =
      (singularHomologyCylinderBoundaryPairIso X R n).hom ≫
        (((singularHomologyFunctor A n).obj R).map (cylinderBoundaryι₁ X) -
          ((singularHomologyFunctor A n).obj R).map (cylinderBoundaryι₀ X)) := by
  let H := (singularHomologyFunctor A n).obj R
  let δ : (cylinderBoundaryPair X).singularHomology R (n + 1) ⟶
      H.obj (cylinderBoundaryPair X).snd :=
    (cylinderBoundaryPair X).singularHomologyδ R (n + 1) n
  let Φ := (singularHomologyCylinderBoundaryPairIso X R n).hom
  let π : H.obj (cylinderBoundaryPair X).snd ⟶
      (TopTriple.innerPair.obj (cylinderTriple X)).singularHomology R n :=
    (TopTriple.innerPair.obj (cylinderTriple X)).singularHomologyπ R n
  have hδπ : δ ≫ π = Φ ≫ H.map (cylinderBoundaryι₁ X) ≫ π :=
    (singularHomologyCylinderBoundaryPairIso_hom_comp X R n).symm
  -- The connecting morphism vanishes after the projection `X × ∂I ⟶ X × I ⟶ X`.
  have hδp : δ ≫ H.map (cylinderBoundaryProj X) = 0 := by
    have h0 : δ ≫ H.map (cylinderBoundaryPair X).map = 0 :=
      (cylinderBoundaryPair X).singularHomologyδ_comp R (n + 1) n
    rw [H.map_comp, ← Category.assoc, h0, zero_comp]
  have : Mono (H.map (cylinderBoundaryι₀ X)) :=
    mono_of_mono_fac (by
      rw [← H.map_comp, cylinderBoundaryι₀_proj, CategoryTheory.Functor.map_id] :
      H.map (cylinderBoundaryι₀ X) ≫ H.map (cylinderBoundaryProj X) = 𝟙 _)
  -- By exactness of `Hₙ(X) ⟶ Hₙ(X × ∂I) ⟶ Hₙ(X × ∂I, X)`, the difference between `δ` and the
  -- contribution of the top end comes from the bottom end.
  have hS : (ShortComplex.mk (H.map (cylinderBoundaryι₀ X)) π
      ((TopTriple.innerPair.obj (cylinderTriple X)).homologyMap_comp_singularHomologyπ
        R n)).Exact :=
    (TopTriple.innerPair.obj (cylinderTriple X)).singularHomology_exact_space R n
  obtain ⟨b, hb⟩ := hS.lift' (δ - Φ ≫ H.map (cylinderBoundaryι₁ X))
    (by rw [Preadditive.sub_comp, Category.assoc, hδπ, sub_self])
  have hb' : b = -Φ := by
    have h := congrArg (· ≫ H.map (cylinderBoundaryProj X)) hb
    simp only [Category.assoc, ← H.map_comp, cylinderBoundaryι₀_proj, cylinderBoundaryι₁_proj,
      CategoryTheory.Functor.map_id, Category.comp_id, Preadditive.sub_comp, hδp] at h
    rw [h, zero_sub, Category.comp_id]
  have key : δ = Φ ≫ (H.map (cylinderBoundaryι₁ X) - H.map (cylinderBoundaryι₀ X)) := by
    rw [Preadditive.comp_sub, ← sub_add_cancel δ (Φ ≫ H.map (cylinderBoundaryι₁ X)), ← hb, hb',
      Preadditive.neg_comp]
    abel
  exact key

/-- The difference of the maps induced by the two ends is a monomorphism: followed by the
quotient map to `Hₙ(X × ∂I, X × {0})` it is the comparison induced by the top end. -/
private lemma mono_singularHomologyMap_cylinderBoundaryι₁_sub (n : ℕ) :
    Mono (((singularHomologyFunctor A n).obj R).map (cylinderBoundaryι₁ X) -
      ((singularHomologyFunctor A n).obj R).map (cylinderBoundaryι₀ X)) := by
  let H := (singularHomologyFunctor A n).obj R
  let π : H.obj (cylinderBoundaryPair X).snd ⟶
      (TopTriple.innerPair.obj (cylinderTriple X)).singularHomology R n :=
    (TopTriple.innerPair.obj (cylinderTriple X)).singularHomologyπ R n
  have h₀ : H.map (cylinderBoundaryι₀ X) ≫ π = 0 :=
    (TopTriple.innerPair.obj (cylinderTriple X)).homologyMap_comp_singularHomologyπ R n
  have h : (H.map (cylinderBoundaryι₁ X) - H.map (cylinderBoundaryι₀ X)) ≫ π =
      cylinderTopComparison X R n := by
    rw [Preadditive.sub_comp, h₀, sub_zero]
  exact mono_of_mono_fac h

/-- **Naturality of `Hₙ₊₁(X × I, X × ∂I) ≅ Hₙ(X)`** in maps `g : X ⟶ Y`. -/
@[reassoc]
theorem singularHomologyCylinderBoundaryPairIso_hom_naturality {Y : TopCat.{w}} (g : X ⟶ Y)
    (n : ℕ) :
    TopPair.singularHomologyMap (cylinderBoundaryPairMap g) R (n + 1) ≫
        (singularHomologyCylinderBoundaryPairIso Y R n).hom =
      (singularHomologyCylinderBoundaryPairIso X R n).hom ≫
        ((singularHomologyFunctor A n).obj R).map g := by
  let H := (singularHomologyFunctor A n).obj R
  let δX : (cylinderBoundaryPair X).singularHomology R (n + 1) ⟶
      H.obj (cylinderBoundaryPair X).snd :=
    (cylinderBoundaryPair X).singularHomologyδ R (n + 1) n
  let δY : (cylinderBoundaryPair Y).singularHomology R (n + 1) ⟶
      H.obj (cylinderBoundaryPair Y).snd :=
    (cylinderBoundaryPair Y).singularHomologyδ R (n + 1) n
  have hδ : δX ≫ H.map (TopPair.Hom.snd (cylinderBoundaryPairMap g)) =
      TopPair.singularHomologyMap (cylinderBoundaryPairMap g) R (n + 1) ≫ δY :=
    TopPair.singularHomologyδ_naturality R (cylinderBoundaryPairMap g) (n + 1) n
  have hX : δX = (singularHomologyCylinderBoundaryPairIso X R n).hom ≫
      (H.map (cylinderBoundaryι₁ X) - H.map (cylinderBoundaryι₀ X)) :=
    singularHomologyδ_cylinderBoundaryPair X R n
  have hY : δY = (singularHomologyCylinderBoundaryPairIso Y R n).hom ≫
      (H.map (cylinderBoundaryι₁ Y) - H.map (cylinderBoundaryι₀ Y)) :=
    singularHomologyδ_cylinderBoundaryPair Y R n
  have := mono_singularHomologyMap_cylinderBoundaryι₁_sub Y R n
  rw [← cancel_mono (H.map (cylinderBoundaryι₁ Y) - H.map (cylinderBoundaryι₀ Y)), Category.assoc,
    ← hY, ← hδ, hX]
  simp only [H, Category.assoc, Preadditive.sub_comp, Preadditive.comp_sub, ← Functor.map_comp,
    cylinderBoundaryι₀_comp_cylinderBoundaryPairMap,
    cylinderBoundaryι₁_comp_cylinderBoundaryPairMap]

end Homology

end TauCeti
