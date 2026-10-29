/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.RiemannRoch.SectionRing.Basic
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Pencil
public import TauCeti.RingTheory.GradedAlgebra.Generation

/-!
# Finite generation of pole-divisor section rings

For a function field `F / k` with exact constants and a nonzero function `z`, the section
ring of its pole divisor is a finitely generated `k`-algebra. This supplies the finiteness
hypothesis for projective embeddings of its `Proj`.

The pencil `1, z` generates successive Riemann–Roch spaces in sufficiently high degree.
On the section ring this gives an eventual recurrence between homogeneous pieces. Each
piece is finite-dimensional, so the general direct-sum generation criterion applies.
Constant functions are included: their pole divisor is zero, and multiplication by the
section `X` already generates every piece from the preceding one.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter IV, Section 3.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition,
  Theorem 1.5.17.
-/

public section

namespace TauCeti.Divisor

open AlgebraicGeometry _root_.Polynomial

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- The pencil recurrence for Riemann–Roch spaces lifts to multiplication of homogeneous
pieces in the section ring of the pole divisor. -/
theorem sectionRingGrade_succ_poles_le_mul (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (z : Fˣ) (n : ℕ)
    (hn : 2 * (genus k F : ℤ) - 1 ≤ ((n : ℤ) - 1) * degree (poles hF z)) :
    sectionRingGrade (poles hF z) (n + 1) ≤
      sectionRingGrade (poles hF z) 1 * sectionRingGrade (poles hF z) n := by
  intro f hf
  obtain ⟨c, hc, hcf⟩ := coeffSubalgebra.mem_grade_iff.mp hf
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    (mem_riemannRochSpace_succ_nsmul_poles_iff hF hex z n hn c).mp hc
  let A := coeffSubalgebra.monomial (fun i ↦ riemannRochSpace (i • poles hF z)) n a ha
  let B := coeffSubalgebra.monomial (fun i ↦ riemannRochSpace (i • poles hF z)) n b hb
  have h1 : (1 : F) ∈ riemannRochSpace (poles hF z) :=
    one_mem_riemannRochSpace_iff.mpr (isEffective_poles hF z).zero_le
  have hz := mem_riemannRochSpace_poles hF z
  have heq : f = monomialDegreeOne h1 * A + monomialDegreeOne hz * B := by
    apply Subtype.ext
    simpa only [Subalgebra.coe_add, A, B, monomialDegreeOne_mul_monomial, one_mul,
      ← map_add] using hcf.symm
  rw [heq]
  exact add_mem (monomialDegreeOne_mul_monomial_mem h1 ha)
    (monomialDegreeOne_mul_monomial_mem hz hb)

/-- The section ring of the pole divisor of any nonzero function is a finitely generated
algebra over the exact constant field. No separability or perfectness is required. -/
theorem finiteType_sectionRing_poles (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (z : Fˣ) :
    Algebra.FiniteType k (sectionRing (poles hF z)) := by
  have hD : 0 ≤ poles hF z := (isEffective_poles hF z).zero_le
  have hdeg : 0 ≤ degree (poles hF z) := degree_nonneg hD
  have hstep : ∃ N : ℕ, ∀ n, N ≤ n → sectionRingGrade (poles hF z) (n + 1) ≤
      sectionRingGrade (poles hF z) 1 * sectionRingGrade (poles hF z) n := by
    by_cases hzero : poles hF z = 0
    · refine ⟨0, fun n _ f hf ↦ ?_⟩
      obtain ⟨a, ha, haf⟩ := coeffSubalgebra.mem_grade_iff.mp hf
      have ha' : a ∈ riemannRochSpace (n • poles hF z) := by simpa [hzero] using ha
      have h1 : (1 : F) ∈ riemannRochSpace (poles hF z) :=
        one_mem_riemannRochSpace_iff.mpr hD
      let A := coeffSubalgebra.monomial (fun i ↦ riemannRochSpace (i • poles hF z)) n a ha'
      have heq : f = monomialDegreeOne h1 * A := by
        apply Subtype.ext
        simpa only [A, monomialDegreeOne_mul_monomial, one_mul] using haf.symm
      rw [heq]
      exact monomialDegreeOne_mul_monomial_mem h1 ha'
    · have hpos : 1 ≤ degree (poles hF z) := by
        have := degree_pos hF hD hzero
        omega
      refine ⟨2 * genus k F + 1, fun n hn ↦ sectionRingGrade_succ_poles_le_mul hF hex z n ?_⟩
      have hn' : (2 * genus k F + 1 : ℤ) ≤ n := by exact_mod_cast hn
      nlinarith
  obtain ⟨N, hN⟩ := hstep
  have hfg (n : ℕ) : (sectionRingGrade (poles hF z) n).FG :=
    (Submodule.fg_iff_finiteDimensional _).mpr
      (finiteDimensional_sectionRingGrade hF (poles hF z) n)
  exact GradedAlgebra.finiteType_of_le_mul (sectionRingGrade (poles hF z)) N
    (sectionRingGrade (poles hF z) 1)
    ((hfg 1).sup (Submodule.fg_iSup _ fun i ↦ hfg i)) hN

end TauCeti.Divisor
