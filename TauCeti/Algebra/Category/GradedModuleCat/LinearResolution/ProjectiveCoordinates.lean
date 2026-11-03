/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Duality
public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.MinimalResolution
public import TauCeti.Algebra.Category.GradedModuleCat.Concentrated

/-!
# Projective coordinates of linear resolution terms

In a projective basis `[Aeᵢ]` dual to degree-zero simples `Sᵢ`, a finite term `Pₙ` of a
linear resolution has coordinate

`dim_k Extⁿ(M,Sᵢ{n}) qⁿ`.

Over a nonsplitting field the coordinate is multiplied by `dim_k End(Sᵢ)`; we retain this
factor as the idempotent dimension of the simple. The normalized formula is derived only when
these dimensions are one. The calculation includes homological degree zero and does not require
termination or Euler-admissibility of the resolved module. Together with degreewise Euler
cancellation it supplies the resolution-term multiplicities in Cartan--Poincaré identities for
infinite linear resolutions.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Sections 1.2 and 2.11, for linear resolutions and the Hilbert-matrix identity.
* P. Webb, *A Course in Finite Group Representation Theory*, Proposition 7.4.1, for the
  division-endomorphism dimension factor in projective/simple pairings.

The coordinate calculation uses `TauCeti.gradedProjectiveExtEuler_simple_eq_mul_invert_repr`
and the minimal-resolution Ext equivalence
`TauCeti.GradedProjectiveResolution.IsMinimal.extLinearEquiv`.
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
  [Module.Finite k A] [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]
  {I : Type uI} [Finite I]
  (S : I → (gradedFiniteModules 𝒜).FullSubcategory) {e : I → A}
  (he : ∀ i, IsIdempotentElem (e i)) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hI : ∀ i, (Ideal.span {e i} : Ideal A).IsHomogeneous 𝒜)
  (hne : Pairwise fun i j => (S j).obj.smulGradedDimension (e i) = 0)
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  (hbP : ∀ i, bP i = LaurentK0.of.{uA} _
    ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
      gradedFiniteProjectiveModules_ofIdeal_span_singleton (he i) (hI i)⟩)

namespace GradedProjectiveResolution

variable {M : GradedModuleCat.{uA} 𝒜}
  {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}

include he₀ hne hbP in
/-- **Ext dimensions compute the projective coordinates of every linear resolution term.**
The diagonal idempotent dimension retains the nonsplitting-field correction. There is no
cohomological boundedness assumption, and `n = 0` is included. -/
theorem IsLinear.smulGradedDimension_mul_repr_finiteProjectiveTerm (hr : r.IsLinear)
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) (n : ℕ)
    [Module.Finite A (r.X n)] (i : I) :
    (S i).obj.smulGradedDimension (e i) *
        bP.repr (LaurentK0.of.{uA} _ (r.finiteProjectiveTerm n)) i =
      C (Module.finrank k (Ext.{uA} M ((S i).obj.shiftObj n) n) : ℤ) * T n := by
  have hgen : (r.finiteProjectiveTerm n).obj.grading.IsGeneratedInDegree A (n : ℤ) :=
    (isLinear_iff.mp hr) n
  rw [smulGradedDimension_mul_repr_of_isGeneratedInDegree S he he₀ hI hne bP hbP
    (r.finiteProjectiveTerm n) hgen hconc i]
  have htarget : (⨆ (p : ℤ) (_ : 0 < p), 𝒜 p) •
      (⊤ : Submodule k ((S i).obj.shiftObj n)) = ⊥ :=
    ((S i).obj.shiftObj n).positive_smul_top_eq_bot_of_concentrated n fun p hp ↦ by
      simpa [sub_eq_add_neg] using hconc i (p - n) (sub_ne_zero.mpr hp)
  rw [finiteProjectiveTerm_obj, ((hr.isMinimal hneg).extLinearEquiv htarget n).finrank_eq]

include he₀ hne hbP in
/-- Over normalized projective/simple bases, the `i`th coordinate of `Pₙ` is
`dim_k Extⁿ(M,Sᵢ{n}) qⁿ`. -/
theorem IsLinear.repr_finiteProjectiveTerm (hr : r.IsLinear)
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hself : ∀ i, (S i).obj.smulGradedDimension (e i) = 1)
    (n : ℕ) [Module.Finite A (r.X n)] (i : I) :
    bP.repr (LaurentK0.of.{uA} _ (r.finiteProjectiveTerm n)) i =
      C (Module.finrank k (Ext.{uA} M ((S i).obj.shiftObj n) n) : ℤ) * T n := by
  simpa only [hself, one_mul] using
    hr.smulGradedDimension_mul_repr_finiteProjectiveTerm
      S he he₀ hI hne bP hbP hneg hconc n i

omit [Finite I] in
include he₀ hne hbP in
/-- The class of a finite term of a linear resolution is the sum of its projective basis
classes with coefficients given by diagonal Ext dimensions and the internal shift `qⁿ`. -/
theorem IsLinear.of_finiteProjectiveTerm_eq_sum [Fintype I] (hr : r.IsLinear)
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (hself : ∀ i, (S i).obj.smulGradedDimension (e i) = 1)
    (n : ℕ) [Module.Finite A (r.X n)] :
    LaurentK0.of.{uA} _ (r.finiteProjectiveTerm n) =
      ∑ i, (C (Module.finrank k (Ext.{uA} M ((S i).obj.shiftObj n) n) : ℤ) * T n) • bP i := by
  classical
  conv_lhs => rw [← bP.sum_repr (LaurentK0.of.{uA} _ (r.finiteProjectiveTerm n))]
  simp only [hr.repr_finiteProjectiveTerm S he he₀ hI hne bP hbP hneg hconc hself]

end GradedProjectiveResolution

end TauCeti
