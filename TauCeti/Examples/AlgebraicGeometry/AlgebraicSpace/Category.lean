/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.FieldTheory.Galois.Basic
import TauCeti.AlgebraicGeometry.AlgebraicSpace.Category

/-!
# Examples for the category of algebraic spaces

The embedded empty scheme is initial and the embedded spectrum of the integers is terminal, so
`Hom(h_∅, F)` and `Hom(F, h_{Spec ℤ})` are points for every algebraic space `F`, whereas there is
no morphism from the spectrum of a field to the empty scheme. Since the embedding of schemes is
fully faithful, the endomorphisms of `h_{Spec K}` over `h_{Spec ℚ}` for a quadratic extension `K/ℚ`,
which is necessarily Galois, are exactly the images of the two Galois automorphisms of `K`.
-/

open CategoryTheory Limits Opposite AlgebraicGeometry TauCeti.AlgebraicGeometry Spaces AlgSpace

universe u

-- `Hom(h_∅, F)` is a point: the embedded empty scheme is initial.
noncomputable example (F : AlgSpace.{u}) : Unique (ofScheme.obj (∅ : Scheme.{u}) ⟶ F) :=
  ⟨⟨emptyIsInitial.to F⟩, fun _ ↦ emptyIsInitial.hom_ext _ _⟩

-- `Hom(F, h_{Spec ℤ})` is a point: the embedded spectrum of the integers is terminal.
noncomputable example (F : AlgSpace.{u}) :
    Unique (F ⟶ ofScheme.obj (Spec (.of (ULift.{u} ℤ)))) :=
  ⟨⟨specZIsTerminal.from F⟩, fun _ ↦ specZIsTerminal.hom_ext _ _⟩

-- `Hom(h_{Spec k}, h_∅)` is empty: a morphism of schemes `Spec k ⟶ ∅` would send the point of
-- `Spec k` into the empty scheme.
example (k : Type u) [Field k] :
    IsEmpty (ofScheme.obj (Spec (.of k)) ⟶ ofScheme.obj (∅ : Scheme.{u})) :=
  ⟨fun f ↦ IsEmpty.elim inferInstance ((ofScheme.preimage f).base (Nonempty.some inferInstance))⟩

-- For a quadratic extension `K/ℚ` (necessarily Galois), the endomorphisms of `h_{Spec K}` over
-- `h_{Spec ℚ}` are exactly the images of the Galois automorphisms of `K`, and there are two.
example (K : Type) [Field K] [Algebra ℚ K] (hK : Module.finrank ℚ K = 2) :
    Set.BijOn (fun σ : K ≃ₐ[ℚ] K ↦ ofScheme.map (Spec.map (CommRingCat.ofHom (σ : K →+* K))))
      Set.univ {φ | φ ≫ ofScheme.map (Spec.algebraMap ℚ K) = ofScheme.map (Spec.algebraMap ℚ K)} ∧
    Nat.card {φ : ofScheme.obj (Spec (.of K)) ⟶ ofScheme.obj (Spec (.of K)) //
      φ ≫ ofScheme.map (Spec.algebraMap ℚ K) = ofScheme.map (Spec.algebraMap ℚ K)} = 2 := by
  -- A degree-two extension of `ℚ` is finite and, being separable, Galois.
  have : FiniteDimensional ℚ K := Module.finite_of_finrank_pos (by omega)
  have : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  -- Full faithfulness of `ofScheme`, then Mathlib's `Spec.homEquivAlgHom`, then the fact that
  -- `ℚ`-algebra endomorphisms of a finite extension are automorphisms.
  let e : {φ : ofScheme.obj (Spec (.of K)) ⟶ ofScheme.obj (Spec (.of K)) //
      φ ≫ ofScheme.map (Spec.algebraMap ℚ K) = ofScheme.map (Spec.algebraMap ℚ K)} ≃
      (K ≃ₐ[ℚ] K) :=
    ((Functor.FullyFaithful.ofFullyFaithful ofScheme).homEquiv.subtypeEquiv fun _ ↦ by
        simp only [Functor.FullyFaithful.homEquiv_apply, ← Functor.map_comp,
          ofScheme.map_injective.eq_iff]).symm.trans
      (Spec.homEquivAlgHom.trans (algEquivEquivAlgHom ℚ K).toEquiv.symm)
  -- The inverse of `e` is the map in the statement, by unfolding the equivalences.
  have he (σ : K ≃ₐ[ℚ] K) : (e.symm σ).val =
      ofScheme.map (Spec.map (CommRingCat.ofHom (σ : K →+* K))) := rfl
  refine ⟨⟨fun σ _ ↦ by simpa only [he, Set.mem_ofPred_eq] using (e.symm σ).property,
    fun σ _ τ _ h ↦ e.symm.injective (Subtype.ext (by simpa only [he] using h)),
    fun φ hφ ↦ ⟨e ⟨φ, hφ⟩, trivial, by
      simpa only [he] using congrArg Subtype.val (e.symm_apply_apply ⟨φ, hφ⟩)⟩⟩, ?_⟩
  rw [Nat.card_congr e, IsGalois.card_aut_eq_finrank, hK]
