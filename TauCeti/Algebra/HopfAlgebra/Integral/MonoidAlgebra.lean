/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.HopfAlgebra.Integral.Basic
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra

/-!
# Integrals in a group algebra

The left and right integrals in a group algebra are exactly the elements with constant
coefficients. For a finite group the sum of its elements is therefore a two-sided integral;
it is nonzero over any nontrivial coefficient semiring, even when its counit, the group order,
vanishes. In particular no invertibility of the group order is needed here.

## References

* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, Chapter 2.
-/

public section

namespace MonoidAlgebra

open TauCeti Coalgebra

variable {R G : Type*} [CommSemiring R] [Group G]

/-- Left integrals in a group algebra have constant coefficients, and conversely. -/
theorem mem_leftIntegral_iff_coeff (t : MonoidAlgebra R G) :
    t ∈ leftIntegral R (MonoidAlgebra R G) ↔ ∀ g, t.coeff g = t.coeff 1 := by
  rw [mem_leftIntegral_iff]
  constructor
  · intro ht g
    simpa using congrArg (fun a : MonoidAlgebra R G => a.coeff 1) (ht (single g⁻¹ 1))
  · intro ht h
    induction h using MonoidAlgebra.induction_on with
    | of g =>
      ext x
      simp [of_apply, ht]
    | add a b ha hb => simp [add_mul, ha, hb, add_smul]
    | smul r a ha => simp [ha, smul_smul]

/-- Right integrals in a group algebra have constant coefficients, and conversely. -/
theorem mem_rightIntegral_iff_coeff (t : MonoidAlgebra R G) :
    t ∈ rightIntegral R (MonoidAlgebra R G) ↔ ∀ g, t.coeff g = t.coeff 1 := by
  rw [mem_rightIntegral_iff]
  constructor
  · intro ht g
    simpa using congrArg (fun a : MonoidAlgebra R G => a.coeff 1) (ht (single g⁻¹ 1))
  · intro ht h
    induction h using MonoidAlgebra.induction_on with
    | of g =>
      ext x
      simp [of_apply, ht]
    | add a b ha hb => simp [mul_add, ha, hb, add_smul]
    | smul r a ha => simp [ha, smul_smul]

/-- The two integral submodules of a group algebra agree, even for a noncommutative group. -/
theorem leftIntegral_eq_rightIntegral :
    leftIntegral R (MonoidAlgebra R G) = rightIntegral R (MonoidAlgebra R G) := by
  ext t
  rw [mem_leftIntegral_iff_coeff, mem_rightIntegral_iff_coeff]

section FiniteSum

variable (R G) [Fintype G]

/-- The unnormalized sum of the group elements is a left integral. -/
theorem sum_single_one_mem_leftIntegral :
    (∑ g : G, single g (1 : R)) ∈ leftIntegral R (MonoidAlgebra R G) := by
  classical
  rw [mem_leftIntegral_iff_coeff]
  simp [coeff_sum, Finsupp.single_apply]

/-- The unnormalized sum of the group elements is a right integral. -/
theorem sum_single_one_mem_rightIntegral :
    (∑ g : G, single g (1 : R)) ∈ rightIntegral R (MonoidAlgebra R G) := by
  rw [← leftIntegral_eq_rightIntegral]
  exact sum_single_one_mem_leftIntegral R G

end FiniteSum

variable (R G) [Finite G]

/-- A finite group algebra over nontrivial coefficients has nonzero integrals,
even when the group order vanishes in the coefficient semiring. -/
theorem leftIntegral_ne_bot [Nontrivial R] :
    leftIntegral R (MonoidAlgebra R G) ≠ ⊥ := by
  classical
  let := Fintype.ofFinite G
  rw [Submodule.ne_bot_iff]
  refine ⟨∑ g : G, single g (1 : R), sum_single_one_mem_leftIntegral R G, ?_⟩
  intro h
  have := congrArg (fun a : MonoidAlgebra R G => a.coeff 1) h
  simp [coeff_sum, Finsupp.single_apply] at this

end MonoidAlgebra
