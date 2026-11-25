/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.HomCoordinate
public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.Basic

/-!
# Projective coordinates of linear resolution terms

For a projective basis `[A eᵢ]` and a finite-dimensional degree-zero target `N` with vanishing
off-diagonal idempotent dimensions `gdim(eⱼ • N) = 0` for `j ≠ i`, a finite term `Pₙ` of a linear
resolution satisfies

`dᵢ · coordinate_i(Pₙ) = dim_k Extⁿ(M, N{n}) qⁿ`, where `dᵢ = dim_k(eᵢ • N)`.

The unweighted coordinate formula requires `dᵢ = 1`. When `N` is the simple head of `A eᵢ` and the
canonical map `A eᵢ → N` is a projective cover, `dᵢ = dim_k End_A(N)`; this interpretation is not
assumed for the arbitrary finite-dimensional target accepted here. The calculation includes
homological degree zero and requires neither finite-dimensionality of the algebra, a nonnegative
algebra grading, nor termination or Euler-admissibility of the resolved module. Together with
degreewise Euler cancellation it supplies the resolution-term multiplicities in Cartan--Poincaré
identities for infinite linear resolutions.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Sections 1.2 and 2.11, for linear resolutions and the Hilbert-matrix identity.
* P. Webb, *A Course in Finite Group Representation Theory*, Proposition 7.4.1, for the
  division-endomorphism dimension factor in projective/simple pairings.

The coordinate calculation uses `TauCeti.smulGradedDimension_mul_repr_of_isGeneratedInDegree`
and the linear-resolution Ext equivalence
`TauCeti.GradedProjectiveResolution.IsLinear.extLinearEquivShiftObj`.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian LaurentPolynomial

universe uk uA uI

section Terms

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}

namespace GradedProjectiveResolution

variable {M : GradedModuleCat.{uA} 𝒜}

/-- A finitely generated term of a concrete graded projective resolution, as an object of the
finite graded projective category. -/
def finiteProjectiveTerm
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading) (n : ℕ)
    [Module.Finite A (r.X n)] : (gradedFiniteProjectiveModules 𝒜).FullSubcategory :=
  ⟨r.termObj n, gradedFiniteProjectiveModules_iff.mpr ⟨inferInstance, r.projective n⟩⟩

/-- The underlying graded object of the finite projective term is the original resolution term. -/
@[simp]
theorem finiteProjectiveTerm_obj
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading) (n : ℕ)
    [Module.Finite A (r.X n)] : (r.finiteProjectiveTerm n).obj = r.termObj n := (rfl)

end GradedProjectiveResolution

end Terms

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
  [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]
  {I : Type uI} {e : I → A}
  (he : ∀ i, IsIdempotentElem (e i)) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  (hbP : ∀ i, bP i = LaurentK0.of.{uA} _
    (gradedIdempotentProjective (he i) (he₀ i)))

namespace GradedProjectiveResolution

variable {M : GradedModuleCat.{uA} 𝒜}
  {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}

include hbP in
/-- **Ext dimensions compute the projective coordinates of every linear resolution term.**
For a finite-dimensional degree-zero target `N` with `gdim(eⱼ • N) = 0` for every `j ≠ i`, the
weighted coordinate `gdim(eᵢ • N) · [Pₙ]ᵢ` equals `dim_k Extⁿ(M, N{n}) · qⁿ`. The diagonal
idempotent dimension retains the nonsplitting-field correction. Neither finite-dimensionality of
`A` nor cohomological boundedness is assumed, and `n = 0` is included. -/
theorem IsLinear.smulGradedDimension_mul_repr_finiteProjectiveTerm (hr : r.IsLinear)
    (N : GradedModuleCat.{uA} 𝒜) [Module.Finite k N]
    (hconc : ∀ p, p ≠ 0 → N.grading.piece p = ⊥) (n : ℕ)
    [Module.Finite A (r.X n)] (i : I)
    (hne : ∀ j, j ≠ i → N.smulGradedDimension (e j) = 0) :
    N.smulGradedDimension (e i) *
        bP.repr (LaurentK0.of.{uA} _ (r.finiteProjectiveTerm n)) i =
      C (Module.finrank k (Ext.{uA} M (N.shiftObj n) n) : ℤ) * T n := by
  have hgen : (r.finiteProjectiveTerm n).obj.grading.IsGeneratedInDegree A (n : ℤ) := by
    rw [finiteProjectiveTerm_obj]
    exact (isLinear_iff.mp hr) n
  rw [smulGradedDimension_mul_repr_of_isGeneratedInDegree he he₀ bP hbP
    (r.finiteProjectiveTerm n) hgen N hconc i hne, finiteProjectiveTerm_obj]
  suffices Module.finrank k (r.termObj n ⟶ N.shiftObj n) =
      Module.finrank k (Ext.{uA} M (N.shiftObj n) n) by rw [this]
  cases n with
  | zero =>
      let aug := r.augmentationLinearEquiv fun f ↦ hr.hom_eq_zero 1
        (GradedModuleCat.shiftObj_piece_eq_bot_of_concentrated hconc 0 1 (by omega))
        (r.differential 0 ≫ f)
      exact (aug.symm.trans (Ext.linearEquiv₀ (R := k)).symm).finrank_eq
  | succ n =>
      exact (hr.extLinearEquivShiftObj hconc n).finrank_eq

include hbP in
/-- For a normalized degree-zero target `N` (`gdim(eᵢ • N) = 1` and `gdim(eⱼ • N) = 0` for
`j ≠ i`), the `i`th coordinate of `Pₙ` is `dim_k Extⁿ(M, N{n}) qⁿ`. -/
theorem IsLinear.repr_finiteProjectiveTerm (hr : r.IsLinear)
    (N : GradedModuleCat.{uA} 𝒜) [Module.Finite k N]
    (hconc : ∀ p, p ≠ 0 → N.grading.piece p = ⊥) (i : I)
    (hne : ∀ j, j ≠ i → N.smulGradedDimension (e j) = 0)
    (hself : N.smulGradedDimension (e i) = 1)
    (n : ℕ) [Module.Finite A (r.X n)] :
    bP.repr (LaurentK0.of.{uA} _ (r.finiteProjectiveTerm n)) i =
      C (Module.finrank k (Ext.{uA} M (N.shiftObj n) n) : ℤ) * T n := by
  simpa only [hself, one_mul] using
    hr.smulGradedDimension_mul_repr_finiteProjectiveTerm he he₀ bP hbP N hconc n i hne

include hbP in
/-- The class of a finite term of a linear resolution is the sum of its projective basis
classes with coefficients given by diagonal Ext dimensions and the internal shift `qⁿ`. -/
theorem IsLinear.of_finiteProjectiveTerm_eq_sum [Fintype I] (hr : r.IsLinear)
    (S : I → GradedModuleCat.{uA} 𝒜) [∀ i, Module.Finite k (S i)]
    (hne : Pairwise fun i j => (S j).smulGradedDimension (e i) = 0)
    (hconc : ∀ i p, p ≠ 0 → (S i).grading.piece p = ⊥)
    (hself : ∀ i, (S i).smulGradedDimension (e i) = 1)
    (n : ℕ) [Module.Finite A (r.X n)] :
    LaurentK0.of.{uA} _ (r.finiteProjectiveTerm n) =
      ∑ i, (C (Module.finrank k (Ext.{uA} M ((S i).shiftObj n) n) : ℤ) * T n) • bP i := by
  classical
  conv_lhs => rw [← bP.sum_repr (LaurentK0.of.{uA} _ (r.finiteProjectiveTerm n))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hr.repr_finiteProjectiveTerm he he₀ bP hbP (S i) (hconc i) i (fun j hji => hne hji)
    (hself i)]

end GradedProjectiveResolution

end TauCeti
