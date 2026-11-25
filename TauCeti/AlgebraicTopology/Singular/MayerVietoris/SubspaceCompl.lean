/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Relative
public import TauCeti.Data.Set.Function
public import TauCeti.LinearAlgebra.Submodule.LineExtension

/-!
# Relative homology modulo the preimage of the complement of a subspace

Let `q : X → F` be a continuous map to a real normed space of finite dimension `r`, and let `A`
be an open subset of `X`. For a subspace `W` of `F`, `TauCeti.subspaceComplPair q A W` is the pair
`(X, A ∪ q⁻¹(F ∖ W))`. Assume that `X` is acyclic modulo `A` and the preimage of the complement of
every closed half-subspace: for every subspace `W'` of `F` and every functional `φ` on `F` with
`φ v = 1` for some `v ∈ W'`, the pair `(X, A ∪ q⁻¹(F ∖ {y ∈ W' | φ y ≤ 0}))` has vanishing
homology. Then

* `Hₙ(X, A ∪ q⁻¹(F ∖ W)) = 0` for `n` below the codimension of `W`
  (`TauCeti.isZero_singularHomology_subspaceComplPair`);
* `Hₘ(X, A ∪ q⁻¹(F ∖ W)) ≅ Hₙ(X, A)` for `W` of codimension `c` and `m = n + c`
  (`TauCeti.subspaceComplPairSingularHomologyIso`), naturally in maps over `F`
  (`TauCeti.subspaceComplPairSingularHomologyIso_hom_naturality`), where a map `f` over `F`
  carrying `A` into `A'` induces the maps of pairs `TauCeti.subspaceComplPairMap`.

The computation removes one dimension at a time, along the extensions `W ⊆ W'` of
`Submodule.LineExtension`. For an extension `ψ` to `F` of the functional of the step, the set
`A ∪ q⁻¹(F ∖ W)` is the union of the open sets `A ∪ q⁻¹(F ∖ {y ∈ W' | ±ψ y ≤ 0})`, which
intersect in `A ∪ q⁻¹(F ∖ W')`. Both are acyclic by assumption, so the relative Mayer–Vietoris
sequence (`TopCat.relativeMayerVietorisδ`) gives
`Hₙ₊₁(X, A ∪ q⁻¹(F ∖ W)) ≅ Hₙ(X, A ∪ q⁻¹(F ∖ W'))` and shows that `H₀(X, A ∪ q⁻¹(F ∖ W))`
vanishes.

With `A = ∅` this is the common core of the homology of the Thom pair of a product bundle
(`TauCeti.prodThomPairSingularHomologyIso`, with `q` the projection `B × F → F`) and of a Serre
fibration over a disk relative to its boundary sphere
(`TauCeti.TopCat.singularHomologyPreimageNeZeroIso`). For a product bundle `K × Y → K` over a
neighbourhood `K` of `0`, a point `y` of a `T₁` space `Y` and `A = K × (Y ∖ {y})`, under the
acyclicity hypothesis it computes the local homology `Hₘ(K × Y, (K × Y) ∖ {(0, y)})` of the total
space at a point of the fibre over `0`.
-/

public section

noncomputable section

open CategoryTheory Limits Module

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F] {X : TopCat.{w}} (q : C(X, F))
  (A : Set X)

/-- The pair `(X, A ∪ q⁻¹(F ∖ W))` for a continuous map `q : X → F`, a subset `A` of `X` and a
subspace `W` of `F`. -/
abbrev subspaceComplPair (W : Submodule ℝ F) : TopPair.{w} :=
  TopPair.ofSubset (A ∪ q ⁻¹' (W : Set F)ᶜ)

instance : IsEmpty (subspaceComplPair q ∅ (⊤ : Submodule ℝ F)).snd :=
  ⟨fun x ↦ x.property.elim id fun h ↦ h Submodule.mem_top⟩

variable {q A} {X' X'' : TopCat.{w}} {q' : C(X', F)} {q'' : C(X'', F)} {A' : Set X'}
  {A'' : Set X''}

omit [NormedSpace ℝ F] in
/-- A map `f : X ⟶ X'` over `F` carrying `A` into `A'` carries `A ∪ q⁻¹(S)` into `A' ∪ q'⁻¹(S)`. -/
private lemma mapsTo_union_preimage (f : X ⟶ X') (hf : ∀ x, q' (f x) = q x)
    (hA : Set.MapsTo f A A') (S : Set F) :
    Set.MapsTo f (A ∪ q ⁻¹' S) (A' ∪ q' ⁻¹' S) :=
  hA.union_union (Set.mapsTo_preimage_of_apply_eq f hf S)

/-- The map of pairs `(X, A ∪ q⁻¹(F ∖ W)) ⟶ (X', A' ∪ q'⁻¹(F ∖ W))` induced by a map `f : X ⟶ X'`
over `F` carrying `A` into `A'`. -/
def subspaceComplPairMap (f : X ⟶ X') (hf : ∀ x, q' (f x) = q x) (hA : Set.MapsTo f A A')
    (W : Submodule ℝ F) : subspaceComplPair q A W ⟶ subspaceComplPair q' A' W :=
  TopPair.ofSubsetMap f (mapsTo_union_preimage f hf hA _)

/-- `subspaceComplPairMap f hf hA W` is the map of pairs `TopPair.ofSubsetMap` induced by `f`. -/
lemma subspaceComplPairMap_eq_ofSubsetMap (f : X ⟶ X') (hf : ∀ x, q' (f x) = q x)
    (hA : Set.MapsTo f A A') (W : Submodule ℝ F)
    (h : Set.MapsTo f (A ∪ q ⁻¹' (W : Set F)ᶜ) (A' ∪ q' ⁻¹' (W : Set F)ᶜ)) :
    subspaceComplPairMap f hf hA W = TopPair.ofSubsetMap f h :=
  (rfl)

@[simp]
lemma subspaceComplPairMap_fst_apply (f : X ⟶ X') (hf : ∀ x, q' (f x) = q x)
    (hA : Set.MapsTo f A A') (W : Submodule ℝ F) (x : (subspaceComplPair q A W).fst) :
    TopPair.Hom.fst (subspaceComplPairMap f hf hA W) x = f x :=
  TopPair.ofSubsetMap_fst_apply _ _ x

/-- The map of ambient spaces underlying `subspaceComplPairMap f hf hA W` is `f`. -/
lemma subspaceComplPairMap_fst (f : X ⟶ X') (hf : ∀ x, q' (f x) = q x) (hA : Set.MapsTo f A A')
    (W : Submodule ℝ F) : TopPair.Hom.fst (subspaceComplPairMap f hf hA W) = f :=
  TopPair.ofSubsetMap_fst _ _

@[simp]
lemma subspaceComplPairMap_snd_apply (f : X ⟶ X') (hf : ∀ x, q' (f x) = q x)
    (hA : Set.MapsTo f A A') (W : Submodule ℝ F) (x : (subspaceComplPair q A W).snd) :
    (TopPair.Hom.snd (subspaceComplPairMap f hf hA W) x).val = f x.val :=
  TopPair.ofSubsetMap_snd_apply _ _ x

/-- The map of pairs induced by the identity is the identity. -/
@[simp]
lemma subspaceComplPairMap_id (hf : ∀ x, q (𝟙 X x) = q x) (hA : Set.MapsTo (𝟙 X) A A)
    (W : Submodule ℝ F) :
    subspaceComplPairMap (𝟙 X) hf hA W = 𝟙 (subspaceComplPair q A W) :=
  TopPair.ofSubsetMap_id _

/-- The map of pairs induced by a composite of maps over `F` is the composite of the induced
maps. -/
@[reassoc]
lemma subspaceComplPairMap_comp (f : X ⟶ X') (hf : ∀ x, q' (f x) = q x) (hA : Set.MapsTo f A A')
    (g : X' ⟶ X'') (hg : ∀ x, q'' (g x) = q' x) (hA' : Set.MapsTo g A' A'')
    (hfg : ∀ x, q'' ((f ≫ g) x) = q x) (hAA : Set.MapsTo (f ≫ g) A A'') (W : Submodule ℝ F) :
    subspaceComplPairMap (f ≫ g) hfg hAA W =
      subspaceComplPairMap f hf hA W ≫ subspaceComplPairMap g hg hA' W :=
  TopPair.ofSubsetMap_comp _ _ _ _ _

variable (q A) in
/-- The identification of `(X, A ∪ q⁻¹(F ∖ W))` with `(X, A ∪ q⁻¹(F ∖ F))`, which is `(X, A)`, for
`W` equal to `F`. -/
def subspaceComplPairTopIso {W : Submodule ℝ F} (hW : W = ⊤) :
    subspaceComplPair q A W ≅ subspaceComplPair q A ⊤ :=
  TopPair.ofSubsetIso (Homeomorph.refl _) fun x ↦ by
    rw [hW]
    rfl

/-- The identification `subspaceComplPairTopIso` commutes with the maps of pairs induced by a map
over `F` carrying `A` into `A'`. -/
@[reassoc]
lemma subspaceComplPairTopIso_hom_naturality (f : X ⟶ X') (hf : ∀ x, q' (f x) = q x)
    (hA : Set.MapsTo f A A') {W : Submodule ℝ F} (hW : W = ⊤) :
    (subspaceComplPairTopIso q A hW).hom ≫ subspaceComplPairMap f hf hA ⊤ =
      subspaceComplPairMap f hf hA W ≫ (subspaceComplPairTopIso q' A' hW).hom := by
  simp only [subspaceComplPairTopIso, subspaceComplPairMap_eq_ofSubsetMap f hf hA _
    (mapsTo_union_preimage f hf hA _), TopPair.ofSubsetIso_hom]
  exact TopPair.ofSubsetMap_comp_ofSubsetMap_eq _ _ _ _ rfl

namespace SubspaceComplPair

variable (q A)

/-- The preimage of the complement of the closed half-subspace `{y ∈ W | φ y ≤ 0}`. -/
abbrev halfCompl (W : Submodule ℝ F) (φ : F →ₗ[ℝ] ℝ) : Set X :=
  q ⁻¹' {y | y ∈ W ∧ φ y ≤ 0}ᶜ

/-- The complement of a closed half-subspace has open preimage. -/
lemma isOpen_halfCompl [FiniteDimensional ℝ F] (W : Submodule ℝ F) (φ : F →ₗ[ℝ] ℝ) :
    IsOpen (halfCompl q W φ) :=
  ((W.isClosed_of_finiteDimensional.inter (isClosed_le φ.continuous_of_finiteDimensional
    continuous_const)).isOpen_compl).preimage q.continuous

/-- The union of `A` with the preimage of the complement of the closed half-subspace
`{y ∈ W | φ y ≤ 0}`. -/
private abbrev half (W : Submodule ℝ F) (φ : F →ₗ[ℝ] ℝ) : Set X :=
  A ∪ halfCompl q W φ

private lemma isOpen_half [FiniteDimensional ℝ F] (hA : IsOpen A) (W : Submodule ℝ F)
    (φ : F →ₗ[ℝ] ℝ) : IsOpen (half q A W φ) :=
  hA.union (isOpen_halfCompl q W φ)

variable {W : Submodule ℝ F}

/-- The identification of `(X, A ∪ q⁻¹(F ∖ W))` with the pair modulo the union of the two
half-subspace complements of a step. -/
private def unionIso (s : W.LineExtension) :
    subspaceComplPair q A W ≅
      TopPair.ofSubset (half q A s.W' s.extension ∪ half q A s.W' (-s.extension)) :=
  TopPair.ofSubsetIso (Homeomorph.refl _) fun x ↦ by
    rw [← Set.union_union_distrib_left, ← Set.preimage_union,
      s.compl_union_compl s.extension_comp]
    rfl

/-- The identification of the pair modulo the intersection of the two half-subspace complements of
a step with `(X, A ∪ q⁻¹(F ∖ W'))`. -/
private def interIso (s : W.LineExtension) :
    TopPair.ofSubset (half q A s.W' s.extension ∩ half q A s.W' (-s.extension)) ≅
      subspaceComplPair q A s.W' :=
  TopPair.ofSubsetIso (Homeomorph.refl _) fun x ↦ by
    rw [← Set.union_inter_distrib_left, ← Set.preimage_inter, s.compl_inter_compl]
    rfl

variable (hA : IsOpen A) (hq : ∀ (W : Submodule ℝ F) (φ : F →ₗ[ℝ] ℝ) (v : F), v ∈ W → φ v = 1 →
  ∀ n, IsZero ((TopPair.ofSubset (A ∪ q ⁻¹' {y | y ∈ W ∧ φ y ≤ 0}ᶜ)).singularHomology R n))

include hq

private lemma isZero_biprod (s : W.LineExtension) (n : ℕ) :
    IsZero ((TopPair.ofSubset (half q A s.W' s.extension)).singularHomology R n ⊞
      (TopPair.ofSubset (half q A s.W' (-s.extension))).singularHomology R n) :=
  biprod_isZero_iff _ _ |>.2 ⟨hq _ _ _ s.v.property s.extension_apply_v n,
    hq _ _ _ (neg_mem s.v.property) (by simp) n⟩

variable [FiniteDimensional ℝ F]

include hA in
private lemma isIso_relativeMayerVietorisδ (s : W.LineExtension) (n : ℕ) :
    IsIso (TopCat.relativeMayerVietorisδ R (isOpen_half q A hA s.W' s.extension)
      (isOpen_half q A hA s.W' (-s.extension)) (n + 1) n rfl) := by
  have := (TopCat.relativeMayerVietoris_exact₃ R (isOpen_half q A hA s.W' s.extension)
    (isOpen_half q A hA s.W' (-s.extension)) (n + 1) n rfl).mono_g
      ((isZero_biprod R q A hq s _).eq_of_src _ _)
  have := (TopCat.relativeMayerVietoris_exact₁ R (isOpen_half q A hA s.W' s.extension)
    (isOpen_half q A hA s.W' (-s.extension)) (n + 1) n rfl).epi_f
      ((isZero_biprod R q A hq s _).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- One step of the computation: `Hₙ₊₁(X, A ∪ q⁻¹(F ∖ W)) ≅ Hₙ(X, A ∪ q⁻¹(F ∖ W'))`. -/
private def stepIso (s : W.LineExtension) (n : ℕ) :
    (subspaceComplPair q A W).singularHomology R (n + 1) ≅
      (subspaceComplPair q A s.W').singularHomology R n :=
  haveI := isIso_relativeMayerVietorisδ R q A hA hq s n
  asIso (TopPair.singularHomologyMap (unionIso q A s).hom R (n + 1)) ≪≫
    asIso (TopCat.relativeMayerVietorisδ R (isOpen_half q A hA s.W' s.extension)
      (isOpen_half q A hA s.W' (-s.extension)) (n + 1) n rfl) ≪≫
    asIso (TopPair.singularHomologyMap (interIso q A s).hom R n)

omit [FiniteDimensional ℝ F] in
private lemma isZero_singularHomology_zero (s : W.LineExtension) :
    IsZero ((subspaceComplPair q A W).singularHomology R 0) := by
  have := TopCat.epi_relativeMayerVietorisFromBiprod_zero R (U := half q A s.W' s.extension)
    (V := half q A s.W' (-s.extension))
  exact ((isZero_biprod R q A hq s 0).of_epi
    (TopCat.relativeMayerVietorisFromBiprod R _ _ 0)).of_iso
      (asIso (TopPair.singularHomologyMap (unionIso q A s).hom R 0))

/-! ### Naturality in maps over `F` -/

variable (hA' : IsOpen A') (hq' : ∀ (W : Submodule ℝ F) (φ : F →ₗ[ℝ] ℝ) (v : F), v ∈ W →
  φ v = 1 → ∀ n,
    IsZero ((TopPair.ofSubset (A' ∪ q' ⁻¹' {y | y ∈ W ∧ φ y ≤ 0}ᶜ)).singularHomology R n))
  (f : X ⟶ X') (hf : ∀ x, q' (f x) = q x) (hfA : Set.MapsTo f A A')

private lemma stepIso_hom_naturality (s : W.LineExtension) (n : ℕ) :
    (stepIso R q A hA hq s n).hom ≫
        TopPair.singularHomologyMap (subspaceComplPairMap f hf hfA s.W') R n =
      TopPair.singularHomologyMap (subspaceComplPairMap f hf hfA W) R (n + 1) ≫
        (stepIso R q' A' hA' hq' s n).hom := by
  have hU := mapsTo_union_preimage f hf hfA {y | y ∈ s.W' ∧ s.extension y ≤ 0}ᶜ
  have hV := mapsTo_union_preimage f hf hfA {y | y ∈ s.W' ∧ (-s.extension) y ≤ 0}ᶜ
  have hinter : (interIso q A s).hom ≫ subspaceComplPairMap f hf hfA s.W' =
      TopPair.ofSubsetMap f (hU.inter_inter hV) ≫ (interIso q' A' s).hom := by
    simp only [interIso, subspaceComplPairMap_eq_ofSubsetMap f hf hfA _
      (mapsTo_union_preimage f hf hfA _), TopPair.ofSubsetIso_hom]
    exact TopPair.ofSubsetMap_comp_ofSubsetMap_eq _ _ _ _ rfl
  have hunion : (unionIso q A s).hom ≫ TopPair.ofSubsetMap f (hU.union_union hV) =
      subspaceComplPairMap f hf hfA W ≫ (unionIso q' A' s).hom := by
    simp only [unionIso, subspaceComplPairMap_eq_ofSubsetMap f hf hfA _
      (mapsTo_union_preimage f hf hfA _), TopPair.ofSubsetIso_hom]
    exact TopPair.ofSubsetMap_comp_ofSubsetMap_eq _ _ _ _ rfl
  simp only [stepIso, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [← TopPair.singularHomologyMap_comp, hinter, TopPair.singularHomologyMap_comp,
    TopCat.relativeMayerVietorisδ_naturality_assoc R _ _ (isOpen_half q' A' hA' s.W' s.extension)
      (isOpen_half q' A' hA' s.W' (-s.extension)) f hU hV (n + 1) n rfl,
    ← TopPair.singularHomologyMap_comp_assoc, hunion,
    TopPair.singularHomologyMap_comp_assoc]

end SubspaceComplPair

open SubspaceComplPair

variable (q A) [FiniteDimensional ℝ F] (hA : IsOpen A)
  (hq : ∀ (W : Submodule ℝ F) (φ : F →ₗ[ℝ] ℝ) (v : F), v ∈ W → φ v = 1 → ∀ n,
    IsZero ((TopPair.ofSubset (A ∪ q ⁻¹' {y | y ∈ W ∧ φ y ≤ 0}ᶜ)).singularHomology R n))

include hA hq

/-- **Vanishing below the codimension.** If `X` is acyclic modulo `A` and the preimage under `q`
of the complement of every closed half-subspace of `F`, then `Hₙ(X, A ∪ q⁻¹(F ∖ W)) = 0` whenever
`n` is less than the codimension of `W`. -/
theorem isZero_singularHomology_subspaceComplPair :
    ∀ (n : ℕ) (W : Submodule ℝ F), n + finrank ℝ W < finrank ℝ F →
      IsZero ((subspaceComplPair q A W).singularHomology R n)
  | 0, W, h => isZero_singularHomology_zero R q A hq
      (W.lineExtension (Submodule.lt_top_of_finrank_lt_finrank (by omega)).ne)
  | n + 1, W, h =>
    let s := W.lineExtension (Submodule.lt_top_of_finrank_lt_finrank (by omega)).ne
    (isZero_singularHomology_subspaceComplPair n s.W' (by rw [s.finrank_eq]; omega)).of_iso
      (stepIso R q A hA hq s n)

/-- **The homology modulo the preimage of the complement of a subspace.** If `X` is acyclic modulo
`A` and the preimage under `q` of the complement of every closed half-subspace of `F`, then
`Hₘ(X, A ∪ q⁻¹(F ∖ W)) ≅ Hₙ(X, A ∪ q⁻¹(F ∖ F))`, which is `Hₙ(X, A)`, for `W` of codimension
`c` and `m = n + c`.

The isomorphism is the composite of `c` relative Mayer–Vietoris connecting morphisms, for a fixed
choice of a flag of subspaces of `F` (`Submodule.lineExtension`) that does not depend on `X`. -/
def subspaceComplPairSingularHomologyIso :
    ∀ (c : ℕ) (W : Submodule ℝ F), finrank ℝ W + c = finrank ℝ F → ∀ (n m : ℕ), n + c = m →
      ((subspaceComplPair q A W).singularHomology R m ≅
        (subspaceComplPair q A (⊤ : Submodule ℝ F)).singularHomology R n)
  | 0, _, hW, n, _, rfl =>
    asIso (TopPair.singularHomologyMap
      (subspaceComplPairTopIso q A (Submodule.eq_top_of_finrank_eq hW)).hom R n)
  | c + 1, W, hW, n, _, rfl =>
    let s := W.lineExtension (Submodule.lt_top_of_finrank_lt_finrank (by omega)).ne
    stepIso R q A hA hq s (n + c) ≪≫
      subspaceComplPairSingularHomologyIso c s.W' (by rw [s.finrank_eq]; omega) n (n + c) rfl

variable {q A} (hA' : IsOpen A') (hq' : ∀ (W : Submodule ℝ F) (φ : F →ₗ[ℝ] ℝ) (v : F), v ∈ W →
    φ v = 1 → ∀ n,
      IsZero ((TopPair.ofSubset (A' ∪ q' ⁻¹' {y | y ∈ W ∧ φ y ≤ 0}ᶜ)).singularHomology R n))
  (f : X ⟶ X') (hf : ∀ x, q' (f x) = q x) (hfA : Set.MapsTo f A A')

/-- The isomorphism `Hₘ(X, A ∪ q⁻¹(F ∖ W)) ≅ Hₙ(X, A ∪ q⁻¹(F ∖ F))`, for `m = n + c` with `c` the
codimension of `W`, is natural in maps over `F` carrying `A` into `A'`. -/
@[reassoc]
theorem subspaceComplPairSingularHomologyIso_hom_naturality :
    ∀ (c : ℕ) (W : Submodule ℝ F) (hW : finrank ℝ W + c = finrank ℝ F) (n m : ℕ)
      (h : n + c = m),
      (subspaceComplPairSingularHomologyIso R q A hA hq c W hW n m h).hom ≫
          TopPair.singularHomologyMap (subspaceComplPairMap f hf hfA ⊤) R n =
        TopPair.singularHomologyMap (subspaceComplPairMap f hf hfA W) R m ≫
          (subspaceComplPairSingularHomologyIso R q' A' hA' hq' c W hW n m h).hom
  | 0, W, hW, n, _, rfl => by
    rw [subspaceComplPairSingularHomologyIso, subspaceComplPairSingularHomologyIso, asIso_hom,
      asIso_hom, ← TopPair.singularHomologyMap_comp, subspaceComplPairTopIso_hom_naturality,
      TopPair.singularHomologyMap_comp]
    rfl
  | c + 1, W, hW, n, _, rfl => by
    rw [subspaceComplPairSingularHomologyIso, subspaceComplPairSingularHomologyIso, Iso.trans_hom,
      Iso.trans_hom, Category.assoc, subspaceComplPairSingularHomologyIso_hom_naturality c,
      ← Category.assoc, stepIso_hom_naturality, Category.assoc]
    rfl

end TauCeti
