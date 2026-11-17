/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.GradedAlgebra.CoeffSubalgebra.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Algebra.Polynomial.Monic

/-!
# Flatness of coefficient subalgebras over the parameter ring

A coefficient subalgebra of `B[t]` containing the parameter is flat over `k[t]` when `k` is
a field. No domain hypothesis on `B` is needed: a nonzero scalar polynomial has invertible
leading coefficient after mapping to `B`, so multiplication by it is injective. The
Dedekind-domain torsion-free criterion then gives flatness. This applies to Rees algebras
of increasing multiplicative filtrations, including induced filtrations on subalgebras.

## References

* D. Eisenbud, *Commutative Algebra with a View Toward Algebraic Geometry*, §15.8.
-/

public section

open Polynomial

namespace TauCeti.coeffSubalgebra

variable {k B : Type*} [Field k] [Ring B] [Algebra k B]
  (M : ℕ → Submodule k B) [SetLike.GradedMonoid M] (h1 : (1 : B) ∈ M 1)

/-- A coefficient subalgebra containing the parameter has no torsion over `k[t]`, even when
its coefficient algebra has zero divisors. -/
theorem isTorsionFree :
    letI := algebra M h1
    Module.IsTorsionFree k[X] (coeffSubalgebra M) := by
  let := algebra M h1
  rcases subsingleton_or_nontrivial B with hB | hB
  · infer_instance
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro p f hf
  rcases eq_or_ne p 0 with rfl | hp
  · exact Or.inl rfl
  right
  apply Subtype.ext
  have he : p.map (algebraMap k B) * (f : B[X]) = 0 := by
    simpa [Algebra.smul_def, coe_algebraMap] using congrArg Subtype.val hf
  have hu : IsUnit p.leadingCoeff := isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hp)
  have hul : IsUnit (p.map (algebraMap k B)).leadingCoeff := by
    rw [leadingCoeff_map_eq_of_isUnit_leadingCoeff (algebraMap k B) hu]
    exact hu.map (algebraMap k B)
  exact (isUnit_leadingCoeff_mul_right_eq_zero_iff hul).mp he

/-- A coefficient subalgebra containing the parameter is flat over the polynomial ring over
a field. Neither finite generation nor exhaustiveness of the graded family is required. -/
theorem flat :
    letI := algebra M h1
    Module.Flat k[X] (coeffSubalgebra M) := by
  let := algebra M h1
  let := isTorsionFree M h1
  infer_instance

end TauCeti.coeffSubalgebra
