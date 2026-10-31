/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Henselian
public import TauCeti.RingTheory.Huber.Padic.Field

/-!
# Checks for henselian subrings of complete Tate rings

The power-bounded subring of `ℚ_p` lifts the simple root zero of `X^p - X - p`.
The ring-of-definition formulation and the zero ring are also covered. The negative check
records why the theorem uses a pseudouniformizer in the ambient ring rather than merely an
ideal of definition of an arbitrary complete Huber ring.
-/

public section

open Polynomial

namespace TauCeti.Huber.HenselianChecks

variable (p : ℕ) [Fact p.Prime]

/-- *henselian_test_Zp*: lift the simple root zero of `X^p - X - p` into the principal
ideal of the power-bounded subring of `ℚ_p`. -/
example : ∃ x : powerBoundedSubring ℚ_[p], (x : ℚ_[p]) ^ p - x = p ∧
    ∃ y : powerBoundedSubring ℚ_[p], (p : ℚ_[p]) * y = x := by
  let π : powerBoundedSubring ℚ_[p] :=
    ⟨p, mem_powerBoundedSubring.mpr (IsPowerBounded.of_isTopologicallyNilpotent
      (Padic.isPseudoUniformizer_p (p := p)).isTopologicallyNilpotent)⟩
  have hπ : (π : ℚ_[p]) = p := (rfl)
  have := henselianRing_powerBoundedSubring π (hπ ▸ Padic.isPseudoUniformizer_p)
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  let f : (powerBoundedSubring ℚ_[p])[X] := X ^ p - X - C π
  have hf : f.Monic := by
    have hdeg : (X + C π : (powerBoundedSubring ℚ_[p])[X]).degree < p := by
      apply lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
      · simpa using (WithBot.coe_lt_coe.mpr hp)
      · exact lt_of_le_of_lt degree_C_le (by exact_mod_cast (Nat.zero_lt_of_lt hp))
    simpa only [sub_add_eq_sub_sub] using monic_X_pow_sub hdeg
  obtain ⟨x, hx, hxπ⟩ := HenselianRing.is_henselian (I := Ideal.span {π}) f hf 0
    (by simp [f, ne_zero_of_lt hp])
    (by simp [f, derivative_X_pow, Nat.sub_ne_zero_of_lt hp])
  have hroot : x ^ p - x = π := by simpa [f, Polynomial.IsRoot, sub_eq_zero] using hx
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp (by simpa using hxπ)
  refine ⟨x, ?_, y, ?_⟩
  · exact_mod_cast hroot
  · exact_mod_cast hy.symm

/-- The ring-of-definition result applies to any contained pseudouniformizer, regardless
of the originally chosen ideal of definition. -/
example {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
    [IsTopologicalRing A] [CompleteSpace A] [T0Space A]
    (P : PairOfDefinition A) (π : P.ringOfDefinition)
    (hπ : IsPseudoUniformizer (π : A)) :
    HenselianRing P.ringOfDefinition (Ideal.span {π}) :=
  P.henselianRing π hπ

/-- *henselian_zero_ring*: the zero ring is permitted, with zero as pseudouniformizer. -/
example {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
    [IsTopologicalRing A] [IsHuberRing A] [CompleteSpace A] [T0Space A] [Subsingleton A] :
    HenselianRing (powerBoundedSubring A) (Ideal.span {(0 : powerBoundedSubring A)}) := by
  apply henselianRing_powerBoundedSubring
  rw [isPseudoUniformizer_iff]
  exact ⟨by
    rw [Subsingleton.elim (↑(0 : powerBoundedSubring A) : A) 1]
    exact isUnit_one, IsTopologicallyNilpotent.zero⟩

/-- *henselian_test_not_tate*: no element of `ℤ_p` satisfies the ambient
pseudouniformizer hypothesis, despite its adic completeness. -/
example (x : ℤ_[p]) : ¬ IsPseudoUniformizer x := by
  intro hx
  obtain ⟨P⟩ := IsHuberRing.nonempty_pairOfDefinition (A := ℤ_[p])
  exact PadicInt.not_isTateRing (p := p)
    (IsTateRing.of_isOpen_isBounded P.ringOfDefinition P.isOpen_ringOfDefinition
      P.isBounded_ringOfDefinition hx)

end TauCeti.Huber.HenselianChecks
