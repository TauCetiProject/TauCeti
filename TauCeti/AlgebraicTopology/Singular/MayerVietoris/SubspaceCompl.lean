/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Relative
public import TauCeti.LinearAlgebra.Submodule.LineExtension

/-!
# Relative homology modulo the preimage of the complement of a subspace

Let `q : X → F` be a continuous map to a real normed space of finite dimension `r`. For a
subspace `W` of `F`, `TauCeti.subspaceComplPair q W` is the pair `(X, q⁻¹(F ∖ W))`. Assume that
`X` is acyclic modulo the preimage of the complement of every closed half-subspace: for every
subspace `W'` of `F` and every functional `φ` on `F` with `φ v = 1` for some `v ∈ W'`, the pair
`(X, q⁻¹(F ∖ {y ∈ W' | φ y ≤ 0}))` has vanishing homology. Then

* `Hₙ(X, q⁻¹(F ∖ W)) = 0` for `n` below the codimension of `W`
  (`TauCeti.isZero_singularHomology_subspaceComplPair`);
* `Hₘ(X, q⁻¹(F ∖ W)) ≅ Hₙ(X, ∅)` for `W` of codimension `c` and `m = n + c`
  (`TauCeti.subspaceComplPairSingularHomologyIso`), naturally in maps over `F`
  (`TauCeti.subspaceComplPairSingularHomologyIso_hom_naturality`).

The computation removes one dimension at a time, along the extensions `W ⊆ W'` of
`Submodule.LineExtension`. For an extension `ψ` to `F` of the functional of the step, the set
`q⁻¹(F ∖ W)` is the union of the open sets `q⁻¹(F ∖ {y ∈ W' | ±ψ y ≤ 0})`, which intersect in
`q⁻¹(F ∖ W')`. Both are acyclic by assumption, so the relative Mayer–Vietoris sequence
(`TopCat.relativeMayerVietorisδ`) gives `Hₙ₊₁(X, q⁻¹(F ∖ W)) ≅ Hₙ(X, q⁻¹(F ∖ W'))` and shows
that `H₀(X, q⁻¹(F ∖ W))` vanishes.

This is the common core of the homology of the Thom pair of a product bundle
(`TauCeti.prodThomPairSingularHomologyIso`, with `q` the projection `B × F → F`) and of a Serre
fibration over a disk relative to its boundary sphere
(`TauCeti.TopCat.singularHomologyPreimageNeZeroIso`).
-/

public section

noncomputable section

open CategoryTheory Limits Module

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F] {X : TopCat.{w}} (q : C(X, F))

/-- The pair `(X, q⁻¹(F ∖ W))` for a continuous map `q : X → F` and a subspace `W` of `F`. -/
abbrev subspaceComplPair (W : Submodule ℝ F) : TopPair.{w} :=
  TopPair.ofSubset (q ⁻¹' (W : Set F)ᶜ)

instance : IsEmpty (subspaceComplPair q (⊤ : Submodule ℝ F)).snd :=
  ⟨fun x ↦ x.2 Submodule.mem_top⟩

variable {q} {X' : TopCat.{w}} {q' : C(X', F)}

omit [NormedSpace ℝ F] in
/-- A map `f : X ⟶ X'` over `F` carries preimages under `q` into preimages under `q'`. -/
private lemma mapsTo_preimage (f : X ⟶ X') (hf : ∀ x, q' (f x) = q x) (S : Set F) :
    Set.MapsTo f (q ⁻¹' S) (q' ⁻¹' S) :=
  fun x hx ↦ by rw [Set.mem_preimage, hf]; exact hx

/-- The map of pairs `(X, q⁻¹(F ∖ W)) ⟶ (X', q'⁻¹(F ∖ W))` induced by a map `f : X ⟶ X'` over
`F`. -/
@[expose] def subspaceComplPairMap (f : X ⟶ X') (hf : ∀ x, q' (f x) = q x) (W : Submodule ℝ F) :
    subspaceComplPair q W ⟶ subspaceComplPair q' W :=
  TopPair.ofSubsetMap f fun x hx ↦ by rw [Set.mem_preimage, hf]; exact hx

namespace SubspaceComplPair

variable (q)

/-- The preimage of the complement of the closed half-subspace `{y ∈ W | φ y ≤ 0}`. -/
private abbrev half (W : Submodule ℝ F) (φ : F →ₗ[ℝ] ℝ) : Set X :=
  q ⁻¹' {y | y ∈ W ∧ φ y ≤ 0}ᶜ

private lemma isOpen_half [FiniteDimensional ℝ F] (W : Submodule ℝ F) (φ : F →ₗ[ℝ] ℝ) :
    IsOpen (half q W φ) :=
  ((W.closed_of_finiteDimensional.inter (isClosed_le φ.continuous_of_finiteDimensional
    continuous_const)).isOpen_compl).preimage q.continuous

variable {W : Submodule ℝ F}

/-- A chosen extension to `F` of the functional of an extension by a line. -/
private def extension (s : W.LineExtension) : F →ₗ[ℝ] ℝ :=
  (LinearMap.exists_extend s.φ).choose

private lemma extension_comp (s : W.LineExtension) : extension s ∘ₗ s.W'.subtype = s.φ :=
  (LinearMap.exists_extend s.φ).choose_spec

private lemma extension_apply_v (s : W.LineExtension) : extension s s.v = 1 :=
  (LinearMap.congr_fun (extension_comp s) s.v).trans s.apply_v

/-- The identification of `(X, q⁻¹(F ∖ W))` with the pair modulo the union of the two
half-subspace complements of a step. -/
private def unionIso (s : W.LineExtension) :
    subspaceComplPair q W ≅
      TopPair.ofSubset (half q s.W' (extension s) ∪ half q s.W' (-extension s)) :=
  TopPair.ofSubsetIso (Homeomorph.refl _) fun x ↦ by
    rw [← Set.preimage_union, s.compl_union_compl (extension_comp s)]
    rfl

/-- The identification of the pair modulo the intersection of the two half-subspace complements of
a step with `(X, q⁻¹(F ∖ W'))`. -/
private def interIso (s : W.LineExtension) :
    TopPair.ofSubset (half q s.W' (extension s) ∩ half q s.W' (-extension s)) ≅
      subspaceComplPair q s.W' :=
  TopPair.ofSubsetIso (Homeomorph.refl _) fun x ↦ by
    rw [← Set.preimage_inter, s.compl_inter_compl]
    rfl

/-- The identification of `(X, q⁻¹(F ∖ W))` with `(X, ∅)` for `W` equal to `F`. -/
private def topIso (hW : W = ⊤) : subspaceComplPair q W ≅ subspaceComplPair q ⊤ :=
  TopPair.ofSubsetIso (Homeomorph.refl _) fun x ↦ by
    rw [hW]
    rfl

variable (hq : ∀ (W : Submodule ℝ F) (φ : F →ₗ[ℝ] ℝ) (v : F), v ∈ W → φ v = 1 → ∀ n,
  IsZero ((TopPair.ofSubset (q ⁻¹' {y | y ∈ W ∧ φ y ≤ 0}ᶜ)).singularHomology R n))

include hq

private lemma isZero_biprod (s : W.LineExtension) (n : ℕ) :
    IsZero ((TopPair.ofSubset (half q s.W' (extension s))).singularHomology R n ⊞
      (TopPair.ofSubset (half q s.W' (-extension s))).singularHomology R n) :=
  biprod_isZero_iff _ _ |>.2 ⟨hq _ _ _ s.v.2 (extension_apply_v s) n,
    hq _ _ _ (neg_mem s.v.2) (by simp [extension_apply_v]) n⟩

variable [FiniteDimensional ℝ F]

private lemma isIso_relativeMayerVietorisδ (s : W.LineExtension) (n : ℕ) :
    IsIso (TopCat.relativeMayerVietorisδ R (isOpen_half q s.W' (extension s))
      (isOpen_half q s.W' (-extension s)) (n + 1) n rfl) := by
  have := (TopCat.relativeMayerVietoris_exact₃ R (isOpen_half q s.W' (extension s))
    (isOpen_half q s.W' (-extension s)) (n + 1) n rfl).mono_g
      ((isZero_biprod R q hq s _).eq_of_src _ _)
  have := (TopCat.relativeMayerVietoris_exact₁ R (isOpen_half q s.W' (extension s))
    (isOpen_half q s.W' (-extension s)) (n + 1) n rfl).epi_f
      ((isZero_biprod R q hq s _).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- One step of the computation: `Hₙ₊₁(X, q⁻¹(F ∖ W)) ≅ Hₙ(X, q⁻¹(F ∖ W'))`. -/
private def stepIso (s : W.LineExtension) (n : ℕ) :
    (subspaceComplPair q W).singularHomology R (n + 1) ≅
      (subspaceComplPair q s.W').singularHomology R n :=
  haveI := isIso_relativeMayerVietorisδ R q hq s n
  asIso (TopPair.singularHomologyMap (unionIso q s).hom R (n + 1)) ≪≫
    asIso (TopCat.relativeMayerVietorisδ R (isOpen_half q s.W' (extension s))
      (isOpen_half q s.W' (-extension s)) (n + 1) n rfl) ≪≫
    asIso (TopPair.singularHomologyMap (interIso q s).hom R n)

private lemma isZero_singularHomology_zero (s : W.LineExtension) :
    IsZero ((subspaceComplPair q W).singularHomology R 0) := by
  have := TopCat.epi_relativeMayerVietorisFromBiprod_zero R (isOpen_half q s.W' (extension s))
    (isOpen_half q s.W' (-extension s))
  exact ((isZero_biprod R q hq s 0).of_epi
    (TopCat.relativeMayerVietorisFromBiprod R _ _ 0)).of_iso
      (asIso (TopPair.singularHomologyMap (unionIso q s).hom R 0))

/-! ### Naturality in maps over `F` -/

variable (hq' : ∀ (W : Submodule ℝ F) (φ : F →ₗ[ℝ] ℝ) (v : F), v ∈ W → φ v = 1 → ∀ n,
  IsZero ((TopPair.ofSubset (q' ⁻¹' {y | y ∈ W ∧ φ y ≤ 0}ᶜ)).singularHomology R n))
  (f : X ⟶ X') (hf : ∀ x, q' (f x) = q x)

private lemma stepIso_hom_naturality (s : W.LineExtension) (n : ℕ) :
    (stepIso R q hq s n).hom ≫
        TopPair.singularHomologyMap (subspaceComplPairMap f hf s.W') R n =
      TopPair.singularHomologyMap (subspaceComplPairMap f hf W) R (n + 1) ≫
        (stepIso R q' hq' s n).hom := by
  have hU := mapsTo_preimage f hf {y | y ∈ s.W' ∧ extension s y ≤ 0}ᶜ
  have hV := mapsTo_preimage f hf {y | y ∈ s.W' ∧ (-extension s) y ≤ 0}ᶜ
  have hinter : (interIso q s).hom ≫ subspaceComplPairMap f hf s.W' =
      TopPair.ofSubsetMap f (hU.inter_inter hV) ≫ (interIso q' s).hom := by
    simp only [interIso, subspaceComplPairMap, TopPair.ofSubsetIso_hom]
    exact TopPair.ofSubsetMap_comp_ofSubsetMap_eq _ _ _ _ rfl
  have hunion : (unionIso q s).hom ≫ TopPair.ofSubsetMap f (hU.union_union hV) =
      subspaceComplPairMap f hf W ≫ (unionIso q' s).hom := by
    simp only [unionIso, subspaceComplPairMap, TopPair.ofSubsetIso_hom]
    exact TopPair.ofSubsetMap_comp_ofSubsetMap_eq _ _ _ _ rfl
  simp only [stepIso, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [← TopPair.singularHomologyMap_comp, hinter, TopPair.singularHomologyMap_comp,
    TopCat.relativeMayerVietorisδ_naturality_assoc R _ _ (isOpen_half q' s.W' (extension s))
      (isOpen_half q' s.W' (-extension s)) f hU hV (n + 1) n rfl,
    ← TopPair.singularHomologyMap_comp_assoc, hunion,
    TopPair.singularHomologyMap_comp_assoc]

end SubspaceComplPair

open SubspaceComplPair

variable (q) [FiniteDimensional ℝ F]
  (hq : ∀ (W : Submodule ℝ F) (φ : F →ₗ[ℝ] ℝ) (v : F), v ∈ W → φ v = 1 → ∀ n,
    IsZero ((TopPair.ofSubset (q ⁻¹' {y | y ∈ W ∧ φ y ≤ 0}ᶜ)).singularHomology R n))

include hq

/-- **Vanishing below the codimension.** If `X` is acyclic modulo the preimage under `q` of the
complement of every closed half-subspace of `F`, then `Hₙ(X, q⁻¹(F ∖ W)) = 0` whenever `n` is
less than the codimension of `W`. -/
theorem isZero_singularHomology_subspaceComplPair :
    ∀ (n : ℕ) (W : Submodule ℝ F), n + finrank ℝ W < finrank ℝ F →
      IsZero ((subspaceComplPair q W).singularHomology R n)
  | 0, W, h => isZero_singularHomology_zero R q hq
      (W.lineExtension (Submodule.lt_top_of_finrank_lt_finrank (by omega)).ne)
  | n + 1, W, h =>
    let s := W.lineExtension (Submodule.lt_top_of_finrank_lt_finrank (by omega)).ne
    (isZero_singularHomology_subspaceComplPair n s.W' (by rw [s.finrank_eq]; omega)).of_iso
      (stepIso R q hq s n)

/-- **The homology modulo the preimage of the complement of a subspace.** If `X` is acyclic
modulo the preimage under `q` of the complement of every closed half-subspace of `F`, then
`Hₘ(X, q⁻¹(F ∖ W)) ≅ Hₙ(X, ∅)` for `W` of codimension `c` and `m = n + c`.

The isomorphism is the composite of `c` relative Mayer–Vietoris connecting morphisms, for a fixed
choice of a flag of subspaces of `F` (`Submodule.lineExtension`) that does not depend on `X`. -/
def subspaceComplPairSingularHomologyIso :
    ∀ (c : ℕ) (W : Submodule ℝ F), finrank ℝ W + c = finrank ℝ F → ∀ (n m : ℕ), n + c = m →
      ((subspaceComplPair q W).singularHomology R m ≅
        (subspaceComplPair q (⊤ : Submodule ℝ F)).singularHomology R n)
  | 0, _, hW, n, _, rfl =>
    asIso (TopPair.singularHomologyMap (topIso q (Submodule.eq_top_of_finrank_eq hW)).hom R n)
  | c + 1, W, hW, n, _, rfl =>
    let s := W.lineExtension (Submodule.lt_top_of_finrank_lt_finrank (by omega)).ne
    stepIso R q hq s (n + c) ≪≫
      subspaceComplPairSingularHomologyIso c s.W' (by rw [s.finrank_eq]; omega) n (n + c) rfl

variable {q} (hq' : ∀ (W : Submodule ℝ F) (φ : F →ₗ[ℝ] ℝ) (v : F), v ∈ W → φ v = 1 → ∀ n,
    IsZero ((TopPair.ofSubset (q' ⁻¹' {y | y ∈ W ∧ φ y ≤ 0}ᶜ)).singularHomology R n))
  (f : X ⟶ X') (hf : ∀ x, q' (f x) = q x)

/-- The isomorphism `Hₘ(X, q⁻¹(F ∖ W)) ≅ Hₙ(X, ∅)`, for `m = n + c` with `c` the codimension of
`W`, is natural in maps over `F`. -/
@[reassoc]
theorem subspaceComplPairSingularHomologyIso_hom_naturality :
    ∀ (c : ℕ) (W : Submodule ℝ F) (hW : finrank ℝ W + c = finrank ℝ F) (n m : ℕ)
      (h : n + c = m),
      (subspaceComplPairSingularHomologyIso R q hq c W hW n m h).hom ≫
          TopPair.singularHomologyMap (subspaceComplPairMap f hf ⊤) R n =
        TopPair.singularHomologyMap (subspaceComplPairMap f hf W) R m ≫
          (subspaceComplPairSingularHomologyIso R q' hq' c W hW n m h).hom
  | 0, W, hW, n, _, rfl => by
    have h : (topIso q (Submodule.eq_top_of_finrank_eq hW)).hom ≫ subspaceComplPairMap f hf ⊤ =
        subspaceComplPairMap f hf W ≫ (topIso q' (Submodule.eq_top_of_finrank_eq hW)).hom := by
      simp only [topIso, subspaceComplPairMap, TopPair.ofSubsetIso_hom]
      exact TopPair.ofSubsetMap_comp_ofSubsetMap_eq _ _ _ _ rfl
    rw [subspaceComplPairSingularHomologyIso, subspaceComplPairSingularHomologyIso, asIso_hom,
      asIso_hom, ← TopPair.singularHomologyMap_comp, h, TopPair.singularHomologyMap_comp]
    rfl
  | c + 1, W, hW, n, _, rfl => by
    rw [subspaceComplPairSingularHomologyIso, subspaceComplPairSingularHomologyIso, Iso.trans_hom,
      Iso.trans_hom, Category.assoc, subspaceComplPairSingularHomologyIso_hom_naturality c,
      ← Category.assoc, stepIso_hom_naturality, Category.assoc]
    rfl

end TauCeti
