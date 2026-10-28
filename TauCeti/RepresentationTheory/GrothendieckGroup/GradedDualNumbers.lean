/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Idempotent.Matrix
public import TauCeti.Algebra.Category.GradedModuleCat.Free
public import TauCeti.Algebra.DualNumber.Basic
public import TauCeti.Algebra.DualNumber.Grading
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.ModuleResolution
public import TauCeti.Algebra.Polynomial.Laurent.Basic
public import TauCeti.Algebra.Polynomial.Laurent.Coeff

/-!
# The graded Cartan matrix of the dual numbers

Let `k` be a field and grade the dual numbers `A = k[ε]` with `ε` in degree two
(`TauCeti.dualNumberIntegerGrade`). The degree-zero piece of `A` is `k`, spanned by the idempotent
`1`, so up to internal shift `A` has one indecomposable finite graded projective, `A` itself, and
one graded simple, the residue field `S = A/(ε)` concentrated in degree zero
(`TauCeti.dualNumberGradedResidue`). The regular module has the graded composition factors `S` and
`S{2}`, so the graded Cartan matrix of `A` is the one-by-one matrix `1 + q²`. These dual numbers
are the factor of the zigzag algebra at an isolated vertex, where
`TauCeti.gradedCartanMatrix_zigzagAlgebra` has the same diagonal entry `1 + q²`.

Its determinant `1 + q²` is not a unit of `ℤ[q,q⁻¹]`: at `q = 1` it becomes `2`, the ungraded
Cartan matrix of `k[ε]` (`TauCeti.cartanMatrix_dualNumber`). Graded Cartan unimodularity
(`TauCeti.isUnit_det_gradedCartanMatrix_gradedIdempotentProjectiveBasis`) therefore fails for the
only pair of graded simples: `(S, S)` is not graded Euler-admissible, so the q-Euler characteristic
`χ_q(S, S)` is not defined and no totalised fallback value is exposed for it. This is the graded
counterpart of the dual-numbers rejection `TauCeti.not_isEulerAdmissible_dualNumberResidue`. It
also shows that `S` has no finite resolution by finite graded projectives, the graded counterpart
of `TauCeti.not_admitsFiniteResolution_dualNumberResidue`.

## Main definitions

* `TauCeti.dualNumberGradedResidue`: the graded residue field `S = A/(ε)`, the graded head of `A`.
* `TauCeti.dualNumberGradedProjectiveBasis` and `TauCeti.dualNumberGradedResidueBasis`: the bases
  `[A]` of `K₀^gr(proj A)` and `[S]` of `G₀^gr(mod A)` over `ℤ[q,q⁻¹]`.

## Main results

* `TauCeti.gradedCartanMatrix_dualNumber`: the graded Cartan matrix of `k[ε]` is `1 + q²`.
* `TauCeti.not_isUnit_det_gradedCartanMatrix_dualNumber`: its determinant is not a unit.
* `TauCeti.not_isGradedEulerAdmissible_dualNumberGradedResidue`: the pair `(S, S)` is not graded
  Euler-admissible.
* `TauCeti.not_admitsFiniteResolution_dualNumberGradedResidue`: `S` has no finite resolution by
  finite graded projectives.

## Implementation notes

The integer grading is installed with `attribute [local instance] dualNumberIntegerGradedAlgebra`,
since `TauCeti.dualNumberIntegerGradedAlgebra` is a definition rather than a global instance.
Importing modules activate it in the same way to restate these results.

## References

* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* 185 (2022), Section 2.2, for the graded Cartan matrix and the
  q-Euler form over `ℤ[q,q⁻¹]`.
* Ibrahim Assem, Daniel Simson and Andrzej Skowroński, *Elements of the Representation Theory of
  Associative Algebras I*, Chapter III, Section 3, for the ungraded Cartan matrix and the role of
  finite global dimension in unimodularity.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory LaurentPolynomial

universe u

variable (k : Type u) [Field k]

attribute [local instance] dualNumberIntegerGradedAlgebra

/-! ### The idempotent data of the graded dual numbers -/

/-- The single idempotent `1` is a complete family of orthogonal idempotents. -/
private theorem completeOrthogonalIdempotents_one :
    CompleteOrthogonalIdempotents fun _ : Unit => (1 : DualNumber k) :=
  CompleteOrthogonalIdempotents.unique_iff.2 rfl

/-- The degree-zero piece of the dual numbers is spanned by the idempotent `1`. -/
private theorem dualNumberIntegerGrade_zero_le_span :
    dualNumberIntegerGrade k 0 ≤
      Submodule.span k (Set.range fun _ : Unit => (1 : DualNumber k)) := by
  rw [Set.range_const, dualNumberIntegerGrade_zero_eq_span_one]

/-! ### The graded residue field and the canonical bases -/

/-- The **graded residue field** `S = k[ε]/(ε)`, concentrated in degree zero: the graded head
`A / A₊` of the regular module `A`. -/
abbrev dualNumberGradedResidue : GradedModuleCat.{u} (dualNumberIntegerGrade k) :=
  gradedPositiveMulQuotient (dualNumberIntegerGrade k) (one_mem_dualNumberIntegerGrade_zero k)

/-- The basis `[A]` of `K₀^gr(proj A)` over `ℤ[q,q⁻¹]`, for the dual numbers `A = k[ε]` with
`ε` in degree two. -/
def dualNumberGradedProjectiveBasis :
    Module.Basis Unit (LaurentPolynomial ℤ)
      (LaurentK0.{u} (gradedFiniteProjectiveModulesExactStructure (dualNumberIntegerGrade k))) :=
  gradedIdempotentProjectiveBasis (completeOrthogonalIdempotents_one k)
    (fun _ => one_mem_dualNumberIntegerGrade_zero k)
    (fun _ => Ideal.isHomogeneous_span_singleton _
      ⟨0, one_mem_dualNumberIntegerGrade_zero k⟩)
    (fun _ => dualNumberIntegerGrade_eq_bot_of_neg k) (dualNumberIntegerGrade_zero_le_span k)
    (fun _ => one_ne_zero)

/-- The basis `[S]` of `G₀^gr(mod A)` over `ℤ[q,q⁻¹]` given by the graded residue field, for the
dual numbers `A = k[ε]` with `ε` in degree two. -/
def dualNumberGradedResidueBasis :
    Module.Basis Unit (LaurentPolynomial ℤ)
      (LaurentK0.{u} (gradedFiniteModulesExactStructure (dualNumberIntegerGrade k))) :=
  gradedIdempotentHeadBasis (fun _ => dualNumberIntegerGrade_eq_bot_of_neg k)
    (completeOrthogonalIdempotents_one k) (fun _ => one_mem_dualNumberIntegerGrade_zero k)
    (dualNumberIntegerGrade_zero_le_span k) (fun _ => one_ne_zero)

/-- The vector of `TauCeti.dualNumberGradedProjectiveBasis` is the class `[A]` of the regular
module, as the graded ideal generated by `1`. -/
@[simp]
theorem dualNumberGradedProjectiveBasis_apply (i : Unit) :
    dualNumberGradedProjectiveBasis k i =
      LaurentK0.of.{u} (gradedFiniteProjectiveModulesExactStructure (dualNumberIntegerGrade k))
        ⟨GradedModuleCat.ofIdeal (dualNumberIntegerGrade k) (Ideal.span {1})
            (Ideal.isHomogeneous_span_singleton _
              ⟨0, one_mem_dualNumberIntegerGrade_zero k⟩),
          gradedFiniteProjectiveModules_ofIdeal_span_singleton IsIdempotentElem.one
            (Ideal.isHomogeneous_span_singleton _
              ⟨0, one_mem_dualNumberIntegerGrade_zero k⟩)⟩ := by
  rw [dualNumberGradedProjectiveBasis, gradedIdempotentProjectiveBasis_apply]

/-- The vector of `TauCeti.dualNumberGradedResidueBasis` is the class `[S]` of the graded residue
field. -/
@[simp]
theorem dualNumberGradedResidueBasis_apply (i : Unit) :
    dualNumberGradedResidueBasis k i =
      LaurentK0.of.{u} (gradedFiniteModulesExactStructure (dualNumberIntegerGrade k))
        ⟨dualNumberGradedResidue k, gradedFiniteModules_gradedPositiveMulQuotient _ _⟩ := by
  rw [dualNumberGradedResidueBasis, gradedIdempotentHeadBasis_apply]

/-! ### The graded Cartan matrix -/

/-- The degree-`p` piece of the dual numbers is one-dimensional in degrees `0` and `2`, and zero
otherwise. -/
private theorem finrank_dualNumberIntegerGrade (p : ℤ) :
    (Module.finrank k (dualNumberIntegerGrade k p) : ℤ) =
      (1 + T 2 : LaurentPolynomial ℤ).coeff p := by
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ← mul_one (T 2 : LaurentPolynomial ℤ),
    coeff_T_mul, coeff_one, coeff_one]
  rcases lt_or_ge p 0 with hp | hp
  · rw [dualNumberIntegerGrade_eq_bot_of_neg k hp, finrank_bot]
    simp [hp.ne, show p - 2 ≠ 0 by omega]
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp
  rw [dualNumberIntegerGrade_ofNat]
  rcases eq_or_ne n 0 with rfl | h0
  · simp [(dualNumberGradeZeroEquiv k).finrank_eq]
  rcases eq_or_ne n 2 with rfl | h2
  · simp [(dualNumberGradeTwoEquiv k).finrank_eq]
  rw [dualNumberGrade_eq_bot k h0 h2, finrank_bot]
  simp [h0, show (n : ℤ) - 2 ≠ 0 by omega]

/-- **The graded Cartan matrix of the dual numbers is `1 + q²`**, with `ε` in degree two, in the
bases `[A]` and `[S]`: the regular module has the graded composition factors `S` and `S{2}`. At
`q = 1` this is the ungraded Cartan matrix `2` of `TauCeti.cartanMatrix_dualNumber`. -/
@[simp]
theorem gradedCartanMatrix_dualNumber :
    gradedCartanMatrix (dualNumberIntegerGrade k) (dualNumberGradedProjectiveBasis k)
        (dualNumberGradedResidueBasis k) =
      Matrix.of fun _ _ : Unit => (1 + T 2 : LaurentPolynomial ℤ) := by
  ext i j p
  rw [dualNumberGradedProjectiveBasis, dualNumberGradedResidueBasis,
    coeff_gradedCartanMatrix_gradedIdempotentProjectiveBasis, Matrix.of_apply]
  have htop : cornerSubmodule k (1 : DualNumber k) 1 = ⊤ :=
    eq_top_iff.2 fun x _ => by simpa using mul_mul_mem_cornerSubmodule k 1 1 x
  rw [htop, top_inf_eq, finrank_dualNumberIntegerGrade]

/-- The graded Cartan matrix of the dual numbers has determinant `1 + q²`. -/
theorem det_gradedCartanMatrix_dualNumber :
    (gradedCartanMatrix (dualNumberIntegerGrade k) (dualNumberGradedProjectiveBasis k)
        (dualNumberGradedResidueBasis k)).det = 1 + T 2 := by
  rw [gradedCartanMatrix_dualNumber, Matrix.det_unique, Matrix.of_apply]

/-- **The graded Cartan matrix of the dual numbers is not unimodular**: its determinant `1 + q²`
is not a unit of `ℤ[q,q⁻¹]`, because it evaluates to `2` at `q = 1`. -/
theorem not_isUnit_det_gradedCartanMatrix_dualNumber :
    ¬ IsUnit (gradedCartanMatrix (dualNumberIntegerGrade k) (dualNumberGradedProjectiveBasis k)
        (dualNumberGradedResidueBasis k)).det := by
  rw [det_gradedCartanMatrix_dualNumber]
  intro h
  have h2 := h.map (laurentEval (R := ℤ) (1 : ℤˣ))
  rw [map_add, map_one, laurentEval_T, one_zpow, Units.val_one, Int.isUnit_iff] at h2
  omega

/-! ### The graded dual-numbers rejection -/

/-- **The graded dual-numbers rejection.** The graded residue field `S` of `k[ε]`, with `ε` in
degree two, is not graded Euler-admissible against itself. Because `TauCeti.gradedExtEuler`
consumes a proof of `TauCeti.IsGradedEulerAdmissible`, it cannot be instantiated for this pair. -/
theorem not_isGradedEulerAdmissible_dualNumberGradedResidue
    [HasExt.{u} (GradedModuleCat.{u} (dualNumberIntegerGrade k))] :
    ¬ IsGradedEulerAdmissible.{u} k (GradedModuleCat.shift (dualNumberIntegerGrade k))
      (dualNumberGradedResidue k) (dualNumberGradedResidue k) := fun h =>
  -- `S` is the only graded head, so admissibility of `(S, S)` would make the graded Cartan
  -- matrix unimodular, contradicting `TauCeti.not_isUnit_det_gradedCartanMatrix_dualNumber`.
  not_isUnit_det_gradedCartanMatrix_dualNumber k
    (isUnit_det_gradedCartanMatrix_gradedIdempotentProjectiveBasis _ _ _ _ _ _ fun _ _ => h)

/-- **The graded residue field of `k[ε]` has no finite graded projective resolution**: such a
resolution would make `(S, S)` graded Euler-admissible. -/
theorem not_admitsFiniteResolution_dualNumberGradedResidue :
    ¬ (gradedModuleCanonicalExactStructure (dualNumberIntegerGrade k)).admitsFiniteResolution
      (gradedFiniteProjectiveModules (dualNumberIntegerGrade k)) (dualNumberGradedResidue k) :=
  fun h => by
    have := hasExt_of_enoughProjectives.{u} (GradedModuleCat.{u} (dualNumberIntegerGrade k))
    exact not_isGradedEulerAdmissible_dualNumberGradedResidue k
      (isGradedEulerAdmissible_of_admitsFiniteProjectiveResolution h)

end TauCeti
