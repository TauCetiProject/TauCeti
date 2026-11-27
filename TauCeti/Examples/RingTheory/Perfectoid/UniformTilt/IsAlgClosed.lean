/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.Padic
public import TauCeti.RingTheory.Perfectoid.Untilt
public import TauCeti.RingTheory.Perfectoid.UniformTilt.IsAlgClosed

/-!
# Checks for algebraically closed tilts

The tilt of `ℂ_p` is algebraically closed; this is found by instance search from the perfectoid
structure of `ℂ_p`. In particular the Artin–Schreier equations `x ^ p - x = t` are solvable in it.
For a complete algebraically closed nonarchimedean field `C` in which `p` is topologically
nilpotent, the tilt `O_C♭ = PreTilt O_C p` of its valuation ring is absolutely integrally closed,
so the fraction field `C♭` of `O_C♭` is algebraically closed.
-/

public section

open scoped NormedField Valued
open Polynomial TauCeti TauCeti.Perfectoid

namespace TauCeti.Examples.TiltIsAlgClosed

variable (p : ℕ) [Fact p.Prime]

example : IsAlgClosed (tiltField p ℂ_[p]) := inferInstance

-- Artin–Schreier equations `x ^ p - x = t` are solvable in the tilt of `ℂ_p`.
example (t : tiltField p ℂ_[p]) : ∃ x : tiltField p ℂ_[p], x ^ p - x = t := by
  have hdeg : (X ^ p - (X + C t) : (tiltField p ℂ_[p])[X]).natDegree = p := by
    rw [natDegree_sub_eq_left_of_natDegree_lt, natDegree_X_pow]
    rw [natDegree_X_pow, natDegree_X_add_C]
    exact (Fact.out : p.Prime).one_lt
  obtain ⟨x, hx⟩ := IsAbsolutelyIntegrallyClosed.exists_root (X ^ p - (X + C t) : _[X])
    ((monic_X_pow p).sub_of_left (by
      rw [degree_X_pow, degree_X_add_C]
      exact_mod_cast (Fact.out : p.Prime).one_lt))
    (hdeg ▸ (Fact.out : p.Prime).pos)
  exact ⟨x, by simpa [sub_sub, sub_eq_iff_eq_add'] using hx⟩

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C]
  [IsAlgClosed C] [Fact (IsTopologicallyNilpotent (p : C))]

example : IsAbsolutelyIntegrallyClosed (PreTilt 𝒪[C] p) := inferInstance

-- The fraction field `C♭` of the tilt `O_C♭` is algebraically closed.
example : IsAlgClosed (FractionRing (PreTilt 𝒪[C] p)) :=
  IsAbsolutelyIntegrallyClosed.isAlgClosed (A := PreTilt 𝒪[C] p) _

end TauCeti.Examples.TiltIsAlgClosed
