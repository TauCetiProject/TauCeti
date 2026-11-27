/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormDet

/-!
# Determinant ratios for factored Gram operators

A Gram operator `f† ∘ f` can factor as a scalar times an ordered product of endomorphisms,
even when `f` does not factor through those endomorphisms. Its squared norm determinant is
then a scalar power times the product of the absolute determinants of the factors. When
comparing two such maps, a scale common to the corresponding individual determinants cancels.
The ordered product matters at the operator level; the determinants themselves commute.

The comparison is the determinant step of
`New.Data.exists_chainDeterminant_pos_and_div_chainDeterminant_one_eq` in
`New/Determinant/Chain/NormOfChain.lean` of lsernau/grh-lean (`72fead1`).
-/

public section

namespace LinearMap

variable {𝕜 U V W : Type*} [RCLike 𝕜]
  [NormedAddCommGroup U] [InnerProductSpace 𝕜 U] [FiniteDimensional 𝕜 U]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]

/-- If the Gram operator is a scalar times an ordered product, the squared norm determinant
is the corresponding scalar power times the product of the absolute determinants. -/
theorem normDet_sq_eq_norm_pow_mul_prod_of_inner_map_map_eq
    (f : U →ₗ[𝕜] V) {c : 𝕜} {A : List (Module.End 𝕜 U)}
    (h : ∀ x y, inner 𝕜 (f x) (f y) = c * inner 𝕜 x (A.prod y)) :
    f.normDet ^ 2 = ‖c‖ ^ Module.finrank 𝕜 U * (A.map fun a ↦ ‖a.det‖).prod := by
  -- The range is finite dimensional even when the ambient codomain is not.
  have hgram : f.rangeRestrict.adjoint ∘ₗ f.rangeRestrict = c • A.prod := by
    ext y
    refine ext_inner_left 𝕜 fun x ↦ ?_
    simpa [f.rangeRestrict.adjoint_inner_right, inner_smul_right] using h x y
  have hdet := f.rangeRestrict.normDet_sq
  rw [hgram, LinearMap.det_smul, map_list_prod] at hdet
  simpa only [rangeRestrict, normDet_codRestrict, RCLike.norm_ofReal,
    abs_of_nonneg (sq_nonneg f.normDet), norm_mul, norm_pow, List.norm_prod_map]
    using congrArg norm hdet

/-- Compare the Gram determinants of two maps whose Gram operators factor along the same
list of indices. The numbers `Z j` and `Z' j` are the absolute factor determinants rescaled
by the same nonzero scale `a j`. These individual scales cancel from the quotient, leaving
the product of the individual determinant ratios times the ratio of the overall scalar
powers. In a lift chain, `Z j` and `Z' j` are the single-lift Gram determinants, which can be
computed on spaces other than the chain's source.
No injectivity is needed for this identity with totalized division. -/
theorem normDet_sq_div_eq_pow_mul_prod
    (f : U →ₗ[𝕜] V) (g : U →ₗ[𝕜] W) {ι : Type*} (steps : List ι)
    {A B : ι → Module.End 𝕜 U} {c c' : 𝕜} {a Z Z' : ι → ℝ}
    (hf : ∀ x y, inner 𝕜 (f x) (f y) = c * inner 𝕜 x ((steps.map A).prod y))
    (hg : ∀ x y, inner 𝕜 (g x) (g y) = c' * inner 𝕜 x ((steps.map B).prod y))
    (ha : ∀ j ∈ steps, a j ≠ 0)
    (hZ : ∀ j ∈ steps, Z j = a j * ‖(A j).det‖)
    (hZ' : ∀ j ∈ steps, Z' j = a j * ‖(B j).det‖) :
    f.normDet ^ 2 / g.normDet ^ 2 =
      ‖c / c'‖ ^ Module.finrank 𝕜 U * (steps.map fun j ↦ Z j / Z' j).prod := by
  have hdiv : (steps.map fun j ↦ ‖(A j).det‖ / ‖(B j).det‖).prod =
      (steps.map fun j ↦ ‖(A j).det‖).prod / (steps.map fun j ↦ ‖(B j).det‖).prod := by
    simpa using Multiset.prod_map_div (m := (steps : Multiset ι))
      (f := fun j ↦ ‖(A j).det‖) (g := fun j ↦ ‖(B j).det‖)
  have hprod : (steps.map fun j ↦ ‖(A j).det‖ / ‖(B j).det‖).prod =
      (steps.map fun j ↦ Z j / Z' j).prod := by
    congr 1
    apply List.map_congr_left
    intro j hj
    rw [hZ j hj, hZ' j hj, mul_div_mul_left _ _ (ha j hj)]
  rw [f.normDet_sq_eq_norm_pow_mul_prod_of_inner_map_map_eq hf,
    g.normDet_sq_eq_norm_pow_mul_prod_of_inner_map_map_eq hg, ← div_mul_div_comm,
    ← div_pow, ← norm_div]
  simp only [List.map_map, Function.comp_def, ← hdiv, hprod]

end LinearMap
