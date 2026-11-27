/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.FreeProduct.Full.Basic
import TauCeti.Analysis.CStarAlgebra.Quotient

/-!
# Functoriality, relabeling, and grouping for the full unital C⋆-free product

This file develops the empty-index isomorphism and structural combinators for `FullFreeProduct A`
from its universal property and the algebraic star free-product combinators in
`TauCeti.LinearAlgebra.FreeProduct.Star`:

* `TauCeti.FullFreeProduct.isEmptyEquiv`: `FullFreeProduct A ≃⋆ₐ[ℂ] ℂ` when `[IsEmpty I]`.
* `TauCeti.FullFreeProduct.map`, `TauCeti.FullFreeProduct.map_surjective`, and
  `TauCeti.FullFreeProduct.mapEquiv`: functoriality in the factor C⋆-algebras, preservation of
  surjectivity, and lifting of factorwise `⋆`-isomorphisms.
* `TauCeti.FullFreeProduct.reindexHom` and `TauCeti.FullFreeProduct.reindexEquiv`: index pullback
  and relabeling.
* `TauCeti.FullFreeProduct.sigmaEquiv` and `TauCeti.FullFreeProduct.fiberEquiv`: sigma associativity
  and fiber grouping.
-/

public section

noncomputable section

open LinearAlgebra.FreeProduct

namespace TauCeti.FullFreeProduct

variable {I : Type*} [DecidableEq I] (A : I → Type*) [∀ i, CStarAlgebra (A i)]

/-- The full unital C⋆-free product over an empty index type is canonically (and hence
isometrically) `⋆`-isomorphic to `ℂ`. -/
def isEmptyEquiv [IsEmpty I] : FullFreeProduct A ≃⋆ₐ[ℂ] ℂ :=
  StarAlgEquiv.ofStarAlgHom
    (lift fun i => isEmptyElim i)
    (StarAlgHom.ofId ℂ (FullFreeProduct A))
    (starAlgHom_ext fun i => isEmptyElim i)
    (StarAlgHom.ext fun c => AlgHomClass.commutes (lift (A := A) fun i => isEmptyElim i) c)

@[simp]
theorem isEmptyEquiv_ofAlgebraic [IsEmpty I] (x : LinearAlgebra.FreeProduct ℂ A) :
    isEmptyEquiv A (ofAlgebraic A x) = isEmptyStarAlgEquiv ℂ A x :=
  DFunLike.congr_fun
    (LinearAlgebra.FreeProduct.starAlgHom_ext
      (f := (isEmptyEquiv A).toStarAlgHom.comp (ofAlgebraic A))
      (g := (isEmptyStarAlgEquiv ℂ A).toStarAlgHom) fun i => isEmptyElim i) x

@[simp]
theorem isEmptyEquiv_symm_apply [IsEmpty I] (c : ℂ) :
    (isEmptyEquiv A).symm c = algebraMap ℂ (FullFreeProduct A) c :=
  (rfl)

section Functoriality

variable {A}

/-- Functoriality of `FullFreeProduct`: a family of unital `⋆`-homomorphisms `f i : A i →⋆ₐ[ℂ] A' i`
induces a unital `⋆`-homomorphism `FullFreeProduct A →⋆ₐ[ℂ] FullFreeProduct A'`. -/
def map {A' : I → Type*} [∀ i, CStarAlgebra (A' i)]
    (f : (i : I) → A i →⋆ₐ[ℂ] A' i) : FullFreeProduct A →⋆ₐ[ℂ] FullFreeProduct A' :=
  lift fun i => (factor (A := A') i).comp (f i)

@[simp]
theorem map_factor {A' : I → Type*} [∀ i, CStarAlgebra (A' i)]
    (f : (i : I) → A i →⋆ₐ[ℂ] A' i) (i : I) (a : A i) :
    map f (factor i a) = factor i (f i a) := by
  rw [map, lift_factor, StarAlgHom.comp_apply]

@[simp]
theorem map_comp_factor {A' : I → Type*} [∀ i, CStarAlgebra (A' i)]
    (f : (i : I) → A i →⋆ₐ[ℂ] A' i) (i : I) :
    (map f).comp (factor i) = (factor i).comp (f i) := by
  rw [map, lift_comp_factor]

@[simp]
theorem map_ofAlgebraic {A' : I → Type*} [∀ i, CStarAlgebra (A' i)]
    (f : (i : I) → A i →⋆ₐ[ℂ] A' i) (x : LinearAlgebra.FreeProduct ℂ A) :
    map f (ofAlgebraic A x) = ofAlgebraic A' (mapStar f x) := by
  have h : (map f).comp (ofAlgebraic A) = (ofAlgebraic A').comp (mapStar f) := by
    ext i a
    simp [← factor_apply]
  exact DFunLike.congr_fun h x

@[simp]
theorem map_id :
    map (fun i => StarAlgHom.id ℂ (A i)) = StarAlgHom.id ℂ (FullFreeProduct A) := by
  ext i a
  simp

theorem map_comp {A' A'' : I → Type*} [∀ i, CStarAlgebra (A' i)] [∀ i, CStarAlgebra (A'' i)]
    (g : (i : I) → A' i →⋆ₐ[ℂ] A'' i) (f : (i : I) → A i →⋆ₐ[ℂ] A' i) :
    map (fun i => (g i).comp (f i)) = (map g).comp (map f) := by
  ext i a
  simp

/-- If every factor `⋆`-homomorphism `f i` is surjective, then `FullFreeProduct.map f` is
surjective. -/
theorem map_surjective {A' : I → Type*} [∀ i, CStarAlgebra (A' i)]
    {f : (i : I) → A i →⋆ₐ[ℂ] A' i} (hf : ∀ i, Function.Surjective (f i)) :
    Function.Surjective (map f) := by
  refine StarAlgHom.surjective_of_denseRange ?_
  refine (denseRange_ofAlgebraic (A := A')).mono ?_
  rintro _ ⟨y, rfl⟩
  obtain ⟨x, rfl⟩ := mapStar_surjective hf y
  exact ⟨ofAlgebraic A x, map_ofAlgebraic f x⟩

/-- Factorwise `⋆`-isomorphisms induce an isometric `⋆`-isomorphism of full C⋆-free products. -/
def mapEquiv {A' : I → Type*} [∀ i, CStarAlgebra (A' i)]
    (e : (i : I) → A i ≃⋆ₐ[ℂ] A' i) : FullFreeProduct A ≃⋆ₐ[ℂ] FullFreeProduct A' :=
  congrAlgebraic (mapStarEquiv e)

@[simp]
theorem mapEquiv_ofAlgebraic {A' : I → Type*} [∀ i, CStarAlgebra (A' i)]
    (e : (i : I) → A i ≃⋆ₐ[ℂ] A' i) (x : LinearAlgebra.FreeProduct ℂ A) :
    mapEquiv e (ofAlgebraic A x) = ofAlgebraic A' (mapStarEquiv e x) :=
  congrAlgebraic_ofAlgebraic (mapStarEquiv e) x

@[simp]
theorem mapEquiv_toStarAlgHom {A' : I → Type*} [∀ i, CStarAlgebra (A' i)]
    (e : (i : I) → A i ≃⋆ₐ[ℂ] A' i) :
    (mapEquiv e).toStarAlgHom = map fun i => (e i).toStarAlgHom := by
  ext i a
  simp [mapEquiv, factor_apply]

@[simp]
theorem mapEquiv_factor {A' : I → Type*} [∀ i, CStarAlgebra (A' i)]
    (e : (i : I) → A i ≃⋆ₐ[ℂ] A' i) (i : I) (a : A i) :
    mapEquiv e (factor i a) = factor i (e i a) := by
  simp [factor_apply]

@[simp]
theorem mapEquiv_symm {A' : I → Type*} [∀ i, CStarAlgebra (A' i)]
    (e : (i : I) → A i ≃⋆ₐ[ℂ] A' i) :
    (mapEquiv e).symm = mapEquiv fun i => (e i).symm := by
  rw [mapEquiv, congrAlgebraic_symm, mapStarEquiv_symm, ← mapEquiv]

end Functoriality

/-- Pull back the index set of a full C⋆-free product along any map `f : J → I`. -/
def reindexHom {J : Type*} [DecidableEq J] (f : J → I) :
    FullFreeProduct (fun j => A (f j)) →⋆ₐ[ℂ] FullFreeProduct A :=
  lift fun j => factor (A := A) (f j)

@[simp]
theorem reindexHom_factor {J : Type*} [DecidableEq J] (f : J → I) (j : J) (a : A (f j)) :
    reindexHom A f (factor (A := fun k => A (f k)) j a) = factor (A := A) (f j) a := by
  rw [reindexHom, lift_factor]

@[simp]
theorem reindexHom_ofAlgebraic {J : Type*} [DecidableEq J] (f : J → I)
    (x : LinearAlgebra.FreeProduct ℂ fun j => A (f j)) :
    reindexHom A f (ofAlgebraic (fun j => A (f j)) x) =
      ofAlgebraic A (reindexStarHom ℂ A f x) := by
  have h : (reindexHom A f).comp (ofAlgebraic (fun j => A (f j))) =
      (ofAlgebraic A).comp (reindexStarHom ℂ A f) := by
    ext j a
    simp [← factor_apply]
  exact DFunLike.congr_fun h x

/-- Relabeling the index type along an equivalence `σ : J ≃ I` induces an isometric `⋆`-isomorphism
of full C⋆-free products. -/
def reindexEquiv {J : Type*} [DecidableEq J] (σ : J ≃ I) :
    FullFreeProduct (fun j => A (σ j)) ≃⋆ₐ[ℂ] FullFreeProduct A :=
  congrAlgebraic (reindexStarAlgEquiv ℂ A σ)

@[simp]
theorem reindexEquiv_ofAlgebraic {J : Type*} [DecidableEq J] (σ : J ≃ I)
    (x : LinearAlgebra.FreeProduct ℂ fun j => A (σ j)) :
    reindexEquiv A σ (ofAlgebraic (fun j => A (σ j)) x) =
      ofAlgebraic A (reindexStarAlgEquiv ℂ A σ x) :=
  congrAlgebraic_ofAlgebraic (reindexStarAlgEquiv ℂ A σ) x

@[simp]
theorem reindexEquiv_toStarAlgHom {J : Type*} [DecidableEq J] (σ : J ≃ I) :
    (reindexEquiv A σ).toStarAlgHom = reindexHom A σ := by
  ext j a
  simp [reindexEquiv, factor_apply]

@[simp]
theorem reindexEquiv_factor {J : Type*} [DecidableEq J] (σ : J ≃ I) (j : J) (a : A (σ j)) :
    reindexEquiv A σ (factor (A := fun k => A (σ k)) j a) = factor (A := A) (σ j) a := by
  simp [factor_apply]

@[simp]
theorem reindexEquiv_symm_factor {J : Type*} [DecidableEq J] (σ : J ≃ I) (j : J) (a : A (σ j)) :
    (reindexEquiv A σ).symm (factor (A := A) (σ j) a) =
      factor (A := fun k => A (σ k)) j a :=
  (reindexEquiv A σ).symm_apply_eq.mpr (reindexEquiv_factor A σ j a).symm

/-- Grouping the factors of `FullFreeProduct A` along any indexing map `p : I → J` relies on sigma
associativity, proved first for arbitrary dependent families `B : (j : J) → κ j → Type*`. -/
def sigmaEquiv {J : Type*} [DecidableEq J] {κ : J → Type*} [∀ j, DecidableEq (κ j)]
    (B : (j : J) → κ j → Type*) [∀ j k, CStarAlgebra (B j k)] :
    FullFreeProduct (fun p : Σ j, κ j => B p.fst p.snd) ≃⋆ₐ[ℂ]
      FullFreeProduct (fun j => FullFreeProduct (B j)) :=
  StarAlgEquiv.ofStarAlgHom
    (lift fun p => (factor (A := fun j => FullFreeProduct (B j)) p.fst).comp
      (factor (A := B p.fst) p.snd))
    (lift fun j => lift fun k => factor (A := fun p : Σ j, κ j => B p.fst p.snd) ⟨j, k⟩)
    (starAlgHom_ext fun p b => by
      rcases p with ⟨j, k⟩
      simp)
    (starAlgHom_ext fun j x => by
      have hj :
          ((lift fun p : Σ j, κ j =>
              (factor (A := fun j => FullFreeProduct (B j)) p.fst).comp
                (factor (A := B p.fst) p.snd)).comp
            (lift fun k => factor (A := fun p : Σ j, κ j => B p.fst p.snd) ⟨j, k⟩)) =
            factor (A := fun j => FullFreeProduct (B j)) j :=
        starAlgHom_ext fun k b => by simp
      simpa using DFunLike.congr_fun hj x)

@[simp]
theorem sigmaEquiv_factor {J : Type*} [DecidableEq J] {κ : J → Type*} [∀ j, DecidableEq (κ j)]
    (B : (j : J) → κ j → Type*) [∀ j k, CStarAlgebra (B j k)] (j : J) (k : κ j) (b : B j k) :
    sigmaEquiv B (factor (A := fun p : Σ j, κ j => B p.fst p.snd) ⟨j, k⟩ b) =
      factor (A := fun j => FullFreeProduct (B j)) j (factor (A := B j) k b) := by
  simp [sigmaEquiv]

@[simp]
theorem sigmaEquiv_symm_factor {J : Type*} [DecidableEq J] {κ : J → Type*}
    [∀ j, DecidableEq (κ j)] (B : (j : J) → κ j → Type*) [∀ j k, CStarAlgebra (B j k)]
    (j : J) (k : κ j) (b : B j k) :
    (sigmaEquiv B).symm
      (factor (A := fun j => FullFreeProduct (B j)) j (factor (A := B j) k b)) =
      factor (A := fun p : Σ j, κ j => B p.fst p.snd) ⟨j, k⟩ b :=
  (sigmaEquiv B).symm_apply_eq.mpr (sigmaEquiv_factor B j k b).symm

/-- Grouping the factors of `FullFreeProduct A` along any indexing map `p : I → J` identifies
`FullFreeProduct A` with the full C⋆-free product over `j : J` of the fiber full C⋆-free products
over `{i : I // p i = j}`. -/
def fiberEquiv {J : Type*} [DecidableEq J] (p : I → J) :
    FullFreeProduct A ≃⋆ₐ[ℂ]
      FullFreeProduct (fun j : J => FullFreeProduct (fun i : {i : I // p i = j} => A i.val)) :=
  (reindexEquiv A (Equiv.sigmaFiberEquiv p)).symm.trans
    (sigmaEquiv fun j (i : {i : I // p i = j}) => A i.val)

@[simp]
theorem fiberEquiv_factor {J : Type*} [DecidableEq J] (p : I → J) (i : I) (a : A i) :
    fiberEquiv A p (factor (A := A) i a) =
      factor (A := fun j : J => FullFreeProduct (fun k : {k : I // p k = j} => A k.val)) (p i)
        (factor (A := fun k : {k : I // p k = p i} => A k.val) ⟨i, rfl⟩ a) := by
  have h1 : (reindexEquiv A (Equiv.sigmaFiberEquiv p)).symm (factor (A := A) i a) =
      factor (A := fun q : Σ j : J, {k : I // p k = j} => A (Equiv.sigmaFiberEquiv p q))
        ⟨p i, ⟨i, rfl⟩⟩ a :=
    reindexEquiv_symm_factor A (Equiv.sigmaFiberEquiv p) ⟨p i, ⟨i, rfl⟩⟩ a
  exact (congrArg (sigmaEquiv fun j (k : {k : I // p k = j}) => A k.val) h1).trans
    (sigmaEquiv_factor (fun j (k : {k : I // p k = j}) => A k.val) (p i) ⟨i, rfl⟩ a)

@[simp]
theorem fiberEquiv_symm_factor {J : Type*} [DecidableEq J] (p : I → J)
    (j : J) (i : {i : I // p i = j}) (a : A i.val) :
    (fiberEquiv A p).symm
      (factor (A := fun j' : J => FullFreeProduct (fun k : {k : I // p k = j'} => A k.val)) j
        (factor (A := fun k : {k : I // p k = j} => A k.val) i a)) = factor (A := A) i.val a := by
  obtain ⟨i, rfl⟩ := i
  exact (fiberEquiv A p).symm_apply_eq.mpr (fiberEquiv_factor A p i a).symm

end TauCeti.FullFreeProduct
