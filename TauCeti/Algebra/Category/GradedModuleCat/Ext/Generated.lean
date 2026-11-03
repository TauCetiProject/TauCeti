/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Abelian
public import TauCeti.Algebra.Category.GradedModuleCat.Shift
public import TauCeti.Algebra.Module.GradedModule.Generated
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Basic

/-!
# Projective Euler values from a single generating degree

A graded projective generated in degree `d` has maps into a shift of a degree-zero module
only for shift `d`. Its q-Euler value is therefore a single Laurent monomial of exponent
`-d`. This computes projective multiplicities from maps to degree-zero simples, without
requiring a cohomological bound on resolutions of those simples.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Section 1.2, for generating degrees and maps to shifted simples.
* Z. Dancso and A. Licata, *Koszul algebras and flow lattices*, Section 2.2, for the
  q-antilinear convention in the first variable.
-/

public section

namespace TauCeti.GradedModuleCat

open CategoryTheory LaurentPolynomial

universe w v uk uA

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [HasExt.{w} (GradedModuleCat.{v} 𝒜)]

/-- A projective generated in degree `d` pairs with a degree-zero target by the monomial
`dim Hom(P,N{d}) q⁻ᵈ`. The admissibility witness concerns only this projective pair. -/
theorem gradedExtEuler_eq_C_mul_T_of_isGeneratedInDegree
    (P N : GradedModuleCat.{v} 𝒜) [Projective P] {d : ℤ}
    (hP : P.grading.IsGeneratedInDegree A d)
    (hN : ∀ p, p ≠ 0 → N.grading.piece p = ⊥)
    (h : IsGradedEulerAdmissible.{w} k (shift 𝒜) P N) :
    gradedExtEuler k (shift 𝒜) h =
      C (Module.finrank k (P ⟶ N.shiftObj d) : ℤ) * T (-d) := by
  classical
  rw [gradedExtEuler_projective]
  apply LaurentPolynomial.ext
  intro p
  rw [coeff_targetShiftGradedDimension,
    (homShiftPowEquiv 𝒜 P N (-p)).finrank_eq, ← single_eq_C_mul_T,
    AddMonoidAlgebra.coeff_single]
  by_cases hp : p = -d
  · subst p
    rw [neg_neg]
    simp
  · have hpiece : (N.shiftObj (-p)).grading.piece d = ⊥ := by
      simpa [sub_eq_add_neg] using hN (d + p) (by omega)
    have hzero (f : P ⟶ N.shiftObj (-p)) : f = 0 := by
      apply hom_ext
      rw [hom_zero]
      exact P.grading.linearMap_eq_zero_of_isGeneratedInDegree hP f.isHomogeneous
        (by simpa only [add_zero] using hpiece)
    let _ : Subsingleton (P ⟶ N.shiftObj (-p)) := subsingleton_of_forall_eq 0 hzero
    simp [Ne.symm hp, Module.finrank_zero_of_subsingleton]

end TauCeti.GradedModuleCat
