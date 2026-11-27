/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.RingTheory.Flat.Rank
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.LocalProperties.Invertible
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-!
# Finite locally free ring maps of constant rank

A ring map is finite locally free of rank `d` when it is finite, flat and has rank `d` at every
prime. Finite presentation follows from constant rank. This property is invariant under
isomorphism of its target.
-/

public section

namespace RingHom

variable {A B B' : Type*} [CommRing A] [CommRing B] [CommRing B']

/-- A finite locally free ring map of constant rank `d`. -/
def IsFiniteLocallyFreeOfRank (d : ℕ) (f : A →+* B) : Prop :=
  f.Finite ∧ f.Flat ∧ ∀ p, f.finrank p = d

/-- The characteristic conditions of finite local freeness of a fixed rank. -/
theorem isFiniteLocallyFreeOfRank_iff {d : ℕ} {f : A →+* B} :
    IsFiniteLocallyFreeOfRank d f ↔ f.Finite ∧ f.Flat ∧ ∀ p, f.finrank p = d :=
  (Iff.rfl)

/-- A finite locally free ring map is finite. -/
theorem IsFiniteLocallyFreeOfRank.finite {d : ℕ} {f : A →+* B}
    (h : IsFiniteLocallyFreeOfRank d f) : f.Finite :=
  (isFiniteLocallyFreeOfRank_iff.mp h).1

/-- A finite locally free ring map is flat. -/
theorem IsFiniteLocallyFreeOfRank.flat {d : ℕ} {f : A →+* B}
    (h : IsFiniteLocallyFreeOfRank d f) : f.Flat :=
  (isFiniteLocallyFreeOfRank_iff.mp h).2.1

/-- A finite locally free ring map has its prescribed rank at every prime. -/
theorem IsFiniteLocallyFreeOfRank.finrank {d : ℕ} {f : A →+* B}
    (h : IsFiniteLocallyFreeOfRank d f) (p : PrimeSpectrum A) : f.finrank p = d :=
  (isFiniteLocallyFreeOfRank_iff.mp h).2.2 p

/-- Composing with a target isomorphism preserves finite local freeness and its rank. -/
theorem IsFiniteLocallyFreeOfRank.ringEquiv_comp {d : ℕ} {f : A →+* B}
    (h : IsFiniteLocallyFreeOfRank d f) (e : B ≃+* B') :
    IsFiniteLocallyFreeOfRank d (e.toRingHom.comp f) := by
  obtain ⟨hfin, hflat, hrank⟩ := isFiniteLocallyFreeOfRank_iff.mp h
  apply isFiniteLocallyFreeOfRank_iff.mpr
  refine ⟨(RingHom.Finite.of_surjective _ e.surjective).comp hfin,
    hflat.comp (RingHom.Flat.of_bijective e.bijective), fun p ↦ ?_⟩
  rw [RingHom.finrank_comp_left_of_bijective _ _ e.bijective hfin hflat, hrank]

/-- Finite local freeness of a fixed rank is invariant under target isomorphisms. -/
@[simp]
theorem isFiniteLocallyFreeOfRank_ringEquiv_comp_iff {d : ℕ} (f : A →+* B) (e : B ≃+* B') :
    IsFiniteLocallyFreeOfRank d ((e : B →+* B').comp f) ↔ IsFiniteLocallyFreeOfRank d f := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.ringEquiv_comp e⟩
  convert h.ringEquiv_comp e.symm
  ext
  simp

/-- An algebra is finite locally free of rank `d` exactly when its underlying module is finite
and flat and its stalk rank is constantly `d`. -/
theorem isFiniteLocallyFreeOfRank_algebraMap_iff {d : ℕ} [Algebra A B] :
    IsFiniteLocallyFreeOfRank d (algebraMap A B) ↔ Module.Finite A B ∧ Module.Flat A B ∧
      ∀ p, Module.rankAtStalk (R := A) B p = d := by
  rw [isFiniteLocallyFreeOfRank_iff, RingHom.finite_algebraMap, RingHom.flat_algebraMap_iff,
    RingHom.finrank_algebraMap]

/-- Finite flat ring maps of constant rank are finitely presented. -/
theorem IsFiniteLocallyFreeOfRank.finitePresentation {d : ℕ} {f : A →+* B}
    (h : IsFiniteLocallyFreeOfRank d f) : f.FinitePresentation := by
  let := f.toAlgebra
  rw [← RingHom.algebraMap_toAlgebra f] at h ⊢
  obtain ⟨hfin, hflat, hrank⟩ := isFiniteLocallyFreeOfRank_algebraMap_iff.mp h
  have : Module.FinitePresentation A B :=
    Module.FinitePresentation.of_finite_of_flat_of_rankAtStalk_constant d fun m _ ↦ hrank _
  exact RingHom.finitePresentation_algebraMap.mpr (.of_finitePresentation A B)

end RingHom
