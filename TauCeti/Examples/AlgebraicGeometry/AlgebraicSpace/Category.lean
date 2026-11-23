/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.FieldTheory.Galois.Basic
import TauCeti.AlgebraicGeometry.AlgebraicSpace.Category

/-!
# Examples for the category of algebraic spaces

The embedded empty scheme is initial and the embedded spectrum of the integers is terminal, so
`Hom(h_∅, F)` and `Hom(F, h_{Spec ℤ})` are points for every algebraic space `F`, whereas there is
no morphism from the spectrum of a field to the empty scheme. Since the embedding of schemes is
fully faithful, the endomorphisms of `h_{Spec K}` over `h_{Spec ℚ}` for a quadratic Galois extension
`K/ℚ` are the two Galois automorphisms of `K`.
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

-- For a quadratic Galois extension `K/ℚ`, the endomorphisms of `h_{Spec K}` over `h_{Spec ℚ}` are
-- the two Galois automorphisms.
example (K : Type) [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hK : Module.finrank ℚ K = 2) :
    Nat.card {φ : ofScheme.obj (Spec (.of K)) ⟶ ofScheme.obj (Spec (.of K)) //
      φ ≫ ofScheme.map (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) =
        ofScheme.map (Spec.map (CommRingCat.ofHom (algebraMap ℚ K)))} = 2 := by
  let π := Spec.map (CommRingCat.ofHom (algebraMap ℚ K))
  -- Every endomorphism of `Spec K` lies over `Spec ℚ`, since ring maps out of `ℚ` are unique.
  have hπ (g : Spec (.of K) ⟶ Spec (.of K)) : g ≫ π = π := by
    rw [← Spec.map_preimage g, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext_rat _ _))
  -- Endomorphisms of `Spec K` are ring endomorphisms of `K`.
  let s : (Spec (.of K) ⟶ Spec (.of K)) ≃ (K →+* K) :=
    { toFun g := (Spec.preimage g).hom
      invFun r := Spec.map (CommRingCat.ofHom r)
      left_inv g := by simp
      right_inv r := by simp }
  let e : {φ : ofScheme.obj (Spec (.of K)) ⟶ ofScheme.obj (Spec (.of K)) //
      φ ≫ ofScheme.map π = ofScheme.map π} ≃ (K ≃ₐ[ℚ] K) :=
    (((Functor.FullyFaithful.ofFullyFaithful ofScheme).homEquiv.subtypeEquiv fun g ↦ by
        simp [← Functor.map_comp, hπ g]).symm.trans
      (Equiv.subtypeUnivEquiv hπ)).trans
      (s.trans ((RingHom.equivRatAlgHom K K).trans (algEquivEquivAlgHom ℚ K).symm))
  rw [Nat.card_congr e, IsGalois.card_aut_eq_finrank, hK]
