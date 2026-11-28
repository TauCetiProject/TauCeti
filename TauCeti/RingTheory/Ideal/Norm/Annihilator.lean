/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.Coset.Card
import Mathlib.LinearAlgebra.Isomorphisms
import TauCeti.RingTheory.Ideal.Annihilator

/-!
# The absolute norm of the annihilator of a finite module

Over an infinite Dedekind domain, the norm of the annihilator of a finite module divides
its cardinality. For a quotient of two nested lattices this bounds the norm of the ideal
that carries the larger lattice into the smaller one by the lattice index.
-/

public section

open LinearMap Submodule

/-- The absolute norm of the annihilator of a module over an infinite Dedekind domain divides
its cardinality. For infinite modules the cardinality is zero by the convention for `Nat.card`. -/
theorem Module.absNorm_annihilator_dvd_natCard (R : Type*) (M : Type*)
    [CommRing R] [IsDedekindDomain R] [Infinite R] [AddCommGroup M] [Module R M] :
    (Module.annihilator R M).absNorm ∣ Nat.card M := by
  classical
  rcases finite_or_infinite M with hM | hM
  · suffices ∀ (n : ℕ) (X : Type _) [AddCommGroup X] [Module R X] [Finite X],
        Nat.card X = n → (Module.annihilator R X).absNorm ∣ n from this _ M rfl
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro X _ _ _ hn
      subst n
      rcases subsingleton_or_nontrivial X with hX | hX
      · rw [Module.annihilator_eq_top_iff.mpr hX, Ideal.absNorm_top]
        exact one_dvd _
      -- Pass to the smaller quotient by a nonzero cyclic submodule.
      obtain ⟨x, hx⟩ := exists_ne (0 : X)
      let S := span R {x}
      have : Finite (X ⧸ S) := _root_.Finite.of_surjective S.mkQ S.mkQ_surjective
      have hcard : Nat.card X = Nat.card (X ⧸ S) * Nat.card S :=
        AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup S.toAddSubgroup
      have hS : 1 < Nat.card S := by
        apply (AddSubgroup.one_lt_card_iff_ne_bot (H := S.toAddSubgroup)).2
        rw [← bot_toAddSubgroup (R := R) (M := X), ne_eq, toAddSubgroup_inj]
        exact span_singleton_eq_bot.not.mpr hx
      have hlt : Nat.card (X ⧸ S) < Nat.card X := by
        rw [hcard]
        exact lt_mul_of_one_lt_right Nat.card_pos hS
      -- The cyclic submodule is the quotient of the ring by its annihilator.
      have hcyclic : S.annihilator.absNorm = Nat.card S := by
        rw [Ideal.absNorm_eq_natCard, annihilator_span_singleton]
        exact Nat.card_congr ((toSpanSingleton R X x).quotKerEquivRange.trans
          (LinearEquiv.ofEq _ _ (range_toSpanSingleton _))).toEquiv
      calc
        (Module.annihilator R X).absNorm ∣
            (S.annihilator * Module.annihilator R (X ⧸ S)).absNorm :=
          Ideal.absNorm_dvd_absNorm_of_le S.annihilator_mul_annihilator_quotient_le
        _ ∣ Nat.card X := by
          rw [map_mul, hcyclic, hcard, mul_comm (Nat.card (X ⧸ S))]
          exact Nat.mul_dvd_mul_left _ (ih _ hlt (X ⧸ S) rfl)
  · rw [Nat.card_eq_zero_of_infinite]
    exact dvd_zero _
