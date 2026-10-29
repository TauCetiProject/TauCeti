/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.SimpleBasis

/-!
# Graded Cartan coefficients over nonsplitting fields

Let `Sᵢ` be an exhaustive family of graded simples concentrated in degree zero, and let `eᵢ`
be degree-zero idempotents with diagonal, nonzero action on this family. Put
`dᵢ = dim_k(eᵢ • (Sᵢ)₀)`. For every finite graded module `M`, its simple-basis coefficient
`mᵢₚ` satisfies

`dᵢ mᵢₚ = dim_k(eᵢ • Mₚ)`.

In particular `mᵢₚ` is nonnegative and the dimension on the right is divisible by `dᵢ`.
Applied to a projective `A fⱼ`, this computes the coefficient of `qᵖ` in the graded Cartan
matrix as the exact quotient `dim_k(eᵢ A fⱼ ∩ 𝒜 p) / dᵢ`. The divisor is not assumed to be
one. When `Sᵢ` is the simple head of `A eᵢ`, it is the division-endomorphism dimension; the
statements here require only the diagonal idempotent data and do not construct an action of
that division algebra on arbitrary Hom spaces.

These are coefficient computations in the existing simple-class basis, rather than a new
definition of a graded Jordan–Hölder multiplicity.

## References

* Peter Webb, *A Course in Finite Group Representation Theory*, Sections 7.3--7.4, for the
  division-endomorphism correction to projective/simple multiplicity formulas.
* Zsuzsanna Dancso and Anthony Licata, *Koszul algebras and flow lattices*, Section 2.2, for
  graded Cartan matrices and the convention `[M{p}] = qᵖ[M]`.
-/

public section

namespace TauCeti

open CategoryTheory LaurentPolynomial
open scoped Pointwise

universe uk uA uI uJ

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  [Module.Finite k A] {𝒜 : ℤ → Submodule k A} {I : Type uI}
  (S : I → (gradedFiniteModules 𝒜).FullSubcategory) {e : I → A}
  (he : ∀ i, IsIdempotentElem (e i)) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hne : Pairwise fun i j => (S j).obj.smulGradedDimension (e i) = 0)
  (hself : ∀ i, (S i).obj.smulGradedDimension (e i) ≠ 0)
  (hS : IsExhaustiveGradedSimpleFamily S)

/-- The simple-basis coefficient of a finite graded module, multiplied by the diagonal
idempotent dimension, is the dimension of the corresponding homogeneous idempotent summand. -/
theorem finrank_smul_simple_piece_zero_mul_coeff_repr
    (M : (gradedFiniteModules 𝒜).FullSubcategory) (i : I)
    (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) (p : ℤ) :
    (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ) *
        ((gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS).repr
          (LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) M) i).coeff p =
      Module.finrank k ↥(e i • M.obj.grading.piece p) := by
  have h := congrArg (fun f : LaurentPolynomial ℤ => f.coeff p)
    (gradedIdempotentCoordinate_eq_mul_gradedSimpleClassBasisOfNeZero_repr
      S he he₀ hne hself hS (LaurentK0.of _ M) i)
  rw [gradedIdempotentCoordinate_of,
    GradedModuleCat.smulGradedDimension_eq_C_of_concentrated _ _ hconc,
    ← smul_eq_C_mul] at h
  simpa only [GradedModuleCat.coeff_smulGradedDimension, AddMonoidAlgebra.coeff_smul,
    Finsupp.smul_apply, smul_eq_mul] using h.symm

/-- All coefficients of an actual finite graded module in the simple-class basis are
nonnegative. The field need not split the simple modules. -/
theorem coeff_gradedSimpleClassBasisOfNeZero_repr_nonneg
    (M : (gradedFiniteModules 𝒜).FullSubcategory) (i : I)
    (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) (p : ℤ) :
    0 ≤ ((gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS).repr
      (LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) M) i).coeff p := by
  have hdim := finrank_smul_simple_piece_zero_mul_coeff_repr S he he₀ hne hself hS M i hconc p
  have hpos : (0 : ℤ) < Module.finrank k ↥(e i • (S i).obj.grading.piece 0) :=
    Int.natCast_pos.mpr ((S i).obj.finrank_smul_piece_zero_pos_of_concentrated
      (e i) hconc (hself i))
  exact nonneg_of_mul_nonneg_right (hdim ▸ Int.natCast_nonneg _) hpos

include he he₀ hne hself hS in
/-- The diagonal simple dimension divides each homogeneous idempotent-summand dimension
of a finite graded module. -/
theorem finrank_smul_simple_piece_zero_dvd_finrank_smul_piece
    (M : (gradedFiniteModules 𝒜).FullSubcategory) (i : I)
    (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) (p : ℤ) :
    Module.finrank k ↥(e i • (S i).obj.grading.piece 0) ∣
      Module.finrank k ↥(e i • M.obj.grading.piece p) := by
  apply Int.natCast_dvd_natCast.mp
  exact ⟨_, (finrank_smul_simple_piece_zero_mul_coeff_repr
    S he he₀ hne hself hS M i hconc p).symm⟩

section Cartan

variable [GradedAlgebra 𝒜] {J : Type uJ} [Fintype J] [Finite I]
  (bP : Module.Basis J (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  {f : A} (hf : IsIdempotentElem f)
  (hF : (Ideal.span {f} : Ideal A).IsHomogeneous 𝒜) (j : J)
  (hj : bP j = LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
    ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {f}) hF,
      gradedFiniteProjectiveModules_ofIdeal_span_singleton hf hF⟩)

include hj in
/-- **The weighted graded Cartan coefficient formula.** A coefficient in a column `[A f]`,
multiplied by `dim_k(eᵢ • (Sᵢ)₀)`, is the corresponding graded corner dimension. -/
theorem finrank_smul_simple_piece_zero_mul_coeff_gradedCartanMatrix (i : I)
    (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) (p : ℤ) :
    (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ) *
        (gradedCartanMatrix 𝒜 bP
          (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS) i j).coeff p =
      Module.finrank k ↥(cornerSubmodule k (e i) f ⊓ 𝒜 p) := by
  rw [gradedCartanMatrix_apply, hj, gradedCartanMap_of]
  exact (finrank_smul_simple_piece_zero_mul_coeff_repr S he he₀ hne hself hS _ i hconc p).trans
    (by rw [← GradedModuleCat.coeff_smulGradedDimension]
        exact GradedModuleCat.coeff_smulGradedDimension_ofIdeal_span_singleton
          (he i) (he₀ i) hf hF p)

include hj in
/-- **An exact integer quotient computes graded Cartan coefficients over a nonsplitting
field.** The divisor is positive and the division has no remainder. -/
theorem coeff_gradedCartanMatrix_eq_div (i : I)
    (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) (p : ℤ) :
    (gradedCartanMatrix 𝒜 bP
        (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS) i j).coeff p =
      (Module.finrank k ↥(cornerSubmodule k (e i) f ⊓ 𝒜 p) : ℤ) /
        Module.finrank k ↥(e i • (S i).obj.grading.piece 0) := by
  rw [← finrank_smul_simple_piece_zero_mul_coeff_gradedCartanMatrix
    S he he₀ hne hself hS bP hf hF j hj i hconc]
  exact (Int.mul_ediv_cancel_left _ (ne_of_gt (Int.natCast_pos.mpr
    ((S i).obj.finrank_smul_piece_zero_pos_of_concentrated
      (e i) hconc (hself i))))).symm

end Cartan

end TauCeti
