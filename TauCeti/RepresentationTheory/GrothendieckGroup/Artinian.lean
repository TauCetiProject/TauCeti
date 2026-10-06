/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.SimpleBasis
public import TauCeti.RingTheory.CompositionSeries.Regular
public import Mathlib.CategoryTheory.IsomorphismClasses

/-!
# The Grothendieck group of an Artinian ring is finite and free

A composition series of the left regular module contains every simple module up to
isomorphism. Removing repeated isomorphism classes gives a finite exhaustive family of
pairwise nonisomorphic simples. Their classes form a basis of `G₀(mod R)` over `ℤ`.

This supplies the finite simple-class basis without requiring the caller to choose or
classify the simple modules first. In particular it applies to finite group algebras in
arbitrary characteristic, including the nonsemisimple case.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II,
  Section 6.
-/

public section

namespace TauCeti

open CategoryTheory

universe u

variable (R : Type u) [Ring R] [IsArtinianRing R]

/-- An Artinian ring has a finite exhaustive family of pairwise nonisomorphic simple
left modules. The indexing set may be empty when the ring is trivial. -/
theorem exists_isExhaustiveSimpleFamily :
    ∃ (n : ℕ) (S : Fin n → FGModuleCat.{u} R),
      (∀ i, IsSimpleModule R (S i)) ∧
      (Pairwise fun i j ↦ IsEmpty ((S i : Type u) ≃ₗ[R] S j)) ∧
      IsExhaustiveSimpleFamily S := by
  classical
  obtain ⟨s, hbot, htop⟩ := exists_compositionSeries_of_isNoetherian_isArtinian R R
  let F : Fin s.length → FGModuleCat.{u} R := fun i ↦
    FGModuleCat.of R (↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc))
  have hF (i : Fin s.length) : IsSimpleModule R (F i) :=
    isSimpleModule_subquotient s i
  let t := Setoid.comap F (isIsomorphicSetoid (FGModuleCat.{u} R))
  let I := Quotient t
  let S : I → FGModuleCat.{u} R := fun i ↦ F i.out
  have hS (i : I) : IsSimpleModule R (S i) := hF i.out
  have hnoniso : Pairwise fun i j ↦ IsEmpty ((S i : Type u) ≃ₗ[R] S j) := by
    intro i j hij
    refine ⟨fun e ↦ hij ?_⟩
    have heq : Quotient.mk t i.out = Quotient.mk t j.out :=
      Quotient.sound ⟨e.toFGModuleCatIso⟩
    simpa only [Quotient.out_eq] using heq
  have hexhaustive : IsExhaustiveSimpleFamily S := by
    rw [isExhaustiveSimpleFamily_iff]
    intro M hM
    let instSimpleM : IsSimpleModule R M := hM
    obtain ⟨i, hi⟩ := exists_isCompositionFactorAt_regular R M s hbot htop
    obtain ⟨e⟩ := (isCompositionFactorAt_iff).mp hi
    let q : I := Quotient.mk t i
    have hq : t q.out i := Quotient.exact q.out_eq
    obtain ⟨f⟩ := hq
    exact ⟨q, ⟨e.symm.trans (FGModuleCat.isoToLinearEquiv f).symm⟩⟩
  let e := Fintype.equivFin I
  refine ⟨Fintype.card I, S ∘ e.symm, fun i ↦ hS (e.symm i), ?_, ?_⟩
  · intro i j hij
    exact hnoniso (fun heq ↦ hij (e.symm.injective heq))
  · rw [isExhaustiveSimpleFamily_iff] at hexhaustive ⊢
    intro M hM
    obtain ⟨i, hi⟩ := hexhaustive M hM
    refine ⟨e i, ?_⟩
    exact (congrArg (fun j ↦ Nonempty ((M : Type u) ≃ₗ[R] S j))
      (e.symm_apply_apply i)).mpr hi

private theorem free_and_finite_exactK0 :
    Module.Free ℤ (ExactK0 (finiteModulesExactStructure R)) ∧
      Module.Finite ℤ (ExactK0 (finiteModulesExactStructure R)) := by
  obtain ⟨n, S, hS, hnoniso, hexhaustive⟩ := exists_isExhaustiveSimpleFamily R
  let instSimpleFamily : ∀ i, IsSimpleModule R (S i) := hS
  exact ⟨free_exactK0_of_isExhaustiveSimpleFamily S hnoniso hexhaustive,
    finite_exactK0_of_isExhaustiveSimpleFamily S hnoniso hexhaustive⟩

/-- The exact Grothendieck group of finitely generated modules over an Artinian ring is
free over `ℤ`, with a basis of simple-module classes. -/
noncomputable instance instFreeExactK0OfIsArtinianRing :
    Module.Free ℤ (ExactK0 (finiteModulesExactStructure R)) :=
  (free_and_finite_exactK0 R).1

/-- The exact Grothendieck group of finitely generated modules over an Artinian ring is
finitely generated over `ℤ`. -/
instance instFiniteExactK0OfIsArtinianRing :
    Module.Finite ℤ (ExactK0 (finiteModulesExactStructure R)) :=
  (free_and_finite_exactK0 R).2

end TauCeti
