/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Variety
public import TauCeti.Algebra.DualNumber.Log
public import TauCeti.Algebra.Coalgebra.Comodule.GroupLike
import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Character

/-!
# The reduced unipotent variety of the multiplicative group

The unipotent variety of `𝔾ₘ` is the identity scheme: its ideal is `(T - 1)` and its
points over every coefficient algebra consist only of the identity. This is stronger
than a field-valued assertion.

The universal matrices of the faithful representations `t ↦ t` and
`t ↦ diag(t, t⁻¹)` have characteristic-polynomial ideals `(T - 1)` and
`((T - 1)²)`, respectively. Their radicals agree, but their points over the dual
numbers do not: `t = 1 + ε` satisfies the latter equations and not the former.
Thus taking the radical before evaluating on a nonreduced algebra is essential.

We use the intrinsic ideal `HopfAlgebra.unipotentVarietyIdeal`, not a new reduction
after extension of the coefficient algebra.

## References

* A. Bertoloni Meli, N. Imai and A. Youcis, *The Jacobson–Morozov morphism for
  Langlands parameters in the relative setting*, §2.1, Proposition 2.3.
-/

public section

noncomputable section

open LaurentPolynomial WithConv

namespace TauCeti.MultiplicativeGroup

universe u v

variable {k : Type u} [Field k]

/-- The reduced unipotent variety of the multiplicative group is the identity scheme. -/
theorem unipotentVarietyIdeal_eq_span :
    HopfAlgebra.unipotentVarietyIdeal k k[T;T⁻¹] = Ideal.span {(T 1 - 1 : k[T;T⁻¹])} := by
  apply le_antisymm
  · simpa only [ker_counitAlgHom] using
      (HopfAlgebra.unipotentVarietyIdeal_le_ker_counitAlgHom (k := k) (H := k[T;T⁻¹]))
  · rw [Ideal.span_singleton_le_iff_mem, HopfAlgebra.mem_unipotentVarietyIdeal_iff]
    intro g hg
    have h := hg.apply_groupLike_eq_one (groupLikeT k)
    simpa [sub_eq_zero] using h

/-- Over any commutative value algebra, the fixed reduced unipotent variety of `𝔾ₘ`
contains only the identity point. -/
@[simp]
theorem unipotentVarietyIdeal_le_ker_iff {A : Type v} [CommRing A] [Algebra k A]
    (g : WithConv (k[T;T⁻¹] →ₐ[k] A)) :
    HopfAlgebra.unipotentVarietyIdeal k k[T;T⁻¹] ≤ RingHom.ker g.ofConv ↔ g = 1 := by
  rw [unipotentVarietyIdeal_eq_span, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker,
    map_sub, map_one, sub_eq_zero]
  constructor
  · intro h
    apply (pointsMulEquiv (R := k) (A := A)).injective
    apply Units.ext
    simpa using h
  · rintro rfl
    simp

section Equations

variable {R : Type*} [CommRing R]

/-- The characteristic-polynomial equations of the one-dimensional faithful character
of `𝔾ₘ` generate `(T - 1)`. -/
theorem contentIdeal_charpoly_standard :
    ((Matrix.diagonal (fun _ : Fin 1 ↦ (T 1 : R[T;T⁻¹]))).charpoly -
      (Polynomial.X - 1) ^ 1).contentIdeal = Ideal.span {(T 1 - 1 : R[T;T⁻¹])} := by
  have hpoly : (Matrix.diagonal (fun _ : Fin 1 ↦ (T 1 : R[T;T⁻¹]))).charpoly -
      (Polynomial.X - 1) ^ 1 = Polynomial.C (-(T 1 - 1)) := by
    simp [Matrix.charpoly_diagonal]
  rw [hpoly, Polynomial.contentIdeal_C, Ideal.span_singleton_neg]

/-- The characteristic-polynomial equations of `t ↦ diag(t, t⁻¹)` generate
`((T - 1)²)`, with their nonreduced scheme structure retained. -/
theorem contentIdeal_charpoly_paired :
    ((Matrix.diagonal ![(T 1 : R[T;T⁻¹]), T (-1)]).charpoly -
      (Polynomial.X - 1) ^ 2).contentIdeal = Ideal.span {((T 1 - 1 : R[T;T⁻¹]) ^ 2)} := by
  have hunit : (T 1 : R[T;T⁻¹]) * T (-1) = 1 := by rw [← T_add]; simp
  have hpoly : (Matrix.diagonal ![(T 1 : R[T;T⁻¹]), T (-1)]).charpoly -
      (Polynomial.X - 1) ^ 2 =
      Polynomial.monomial 1 (-(T (-1) * (T 1 - 1) ^ 2)) := by
    simp only [Matrix.charpoly_diagonal, Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, ← Polynomial.C_mul_X_eq_monomial,
      map_neg, map_mul, map_pow, map_sub, map_one]
    have hc : Polynomial.C (T 1 : R[T;T⁻¹]) * Polynomial.C (T (-1)) = 1 := by
      rw [← map_mul, hunit, map_one]
    linear_combination
      (Polynomial.X * Polynomial.C (T 1 : R[T;T⁻¹]) - 2 * Polynomial.X + 1) * hc
  rw [hpoly, Polynomial.contentIdeal_monomial, Ideal.span_singleton_neg]
  exact Ideal.span_singleton_mul_left_unit (isUnit_T (-1)) _

/-- Both faithful-character equation ideals have the same radical. -/
theorem radical_contentIdeal_charpoly_paired :
    (((Matrix.diagonal ![(T 1 : R[T;T⁻¹]), T (-1)]).charpoly -
      (Polynomial.X - 1) ^ 2).contentIdeal).radical =
      (Ideal.span {(T 1 - 1 : R[T;T⁻¹])}).radical := by
  rw [contentIdeal_charpoly_paired, ← Ideal.span_singleton_pow, Ideal.radical_pow _ (by decide)]

end Equations

/-- The radical of the paired-character equations is precisely the intrinsic unipotent
variety ideal, not just an ideal with the same field-valued points. -/
theorem radical_contentIdeal_charpoly_paired_eq_unipotentVarietyIdeal :
    (((Matrix.diagonal ![(T 1 : k[T;T⁻¹]), T (-1)]).charpoly -
      (Polynomial.X - 1) ^ 2).contentIdeal).radical =
      HopfAlgebra.unipotentVarietyIdeal k k[T;T⁻¹] := by
  rw [radical_contentIdeal_charpoly_paired, ← unipotentVarietyIdeal_eq_span,
    HopfAlgebra.radical_unipotentVarietyIdeal]

section Comodules

variable (R : Type*) [CommRing R]

/-- The rank-one comodule of the standard character of the multiplicative group. -/
abbrev standardComodule : Comodule R R[T;T⁻¹] (Fin 1 → R) :=
  Comodule.ofGroupLike (Pi.basisFun R (Fin 1)) (fun _ ↦ (T 1 : R[T;T⁻¹]))
    (fun _ ↦ by simpa using (groupLikeT R).isGroupLikeElem_val)

/-- The rank-two comodule of the characters `T` and `T⁻¹` of the multiplicative group. -/
abbrev pairedComodule : Comodule R R[T;T⁻¹] (Fin 2 → R) :=
  Comodule.ofGroupLike (Pi.basisFun R (Fin 2)) ![(T 1 : R[T;T⁻¹]), T (-1)]
    (fun i ↦ ⟨by fin_cases i <;> simp, by fin_cases i <;> simp [LaurentPolynomial.comul_T]⟩)

variable {R} [Nontrivial R]

/-- For the native rank-one comodule with character `T`, the unipotence ideal is `(T - 1)`. -/
theorem unipotenceIdeal_standard :
    letI := standardComodule R
    Comodule.unipotenceIdeal R R[T;T⁻¹] (Fin 1 → R) = Ideal.span {(T 1 - 1 : R[T;T⁻¹])} := by
  let := standardComodule R
  rw [Comodule.unipotenceIdeal_eq_contentIdeal_coefficientMatrix_charpoly (Pi.basisFun R (Fin 1)),
    Comodule.coefficientMatrix_ofGroupLike, Module.finrank_fin_fun]
  exact contentIdeal_charpoly_standard

/-- For the native comodule with characters `T` and `T⁻¹`, the unipotence ideal is
`((T - 1)²)`. In particular the unreduced ideal really depends on the representation. -/
theorem unipotenceIdeal_paired :
    letI := pairedComodule R
    Comodule.unipotenceIdeal R R[T;T⁻¹] (Fin 2 → R) =
      Ideal.span {((T 1 - 1 : R[T;T⁻¹]) ^ 2)} := by
  let := pairedComodule R
  rw [Comodule.unipotenceIdeal_eq_contentIdeal_coefficientMatrix_charpoly (Pi.basisFun R (Fin 2)),
    Comodule.coefficientMatrix_ofGroupLike, Module.finrank_fin_fun]
  exact contentIdeal_charpoly_paired

end Comodules

/-- The infinitesimal point satisfies the unsaturated equations of the paired representation. -/
theorem contentIdeal_charpoly_paired_le_ker_laurentEval_dualNumberUnit
    {R : Type*} [CommRing R] :
    ((Matrix.diagonal ![(T 1 : R[T;T⁻¹]), T (-1)]).charpoly -
      (Polynomial.X - 1) ^ 2).contentIdeal ≤ RingHom.ker (laurentEval (dualNumberUnit R)) := by
  rw [contentIdeal_charpoly_paired, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
  simp [pow_two]

/-- The infinitesimal point is excluded from the fixed reduced unipotent variety. -/
theorem not_unipotentVarietyIdeal_le_ker_dualNumberUnit :
    ¬ HopfAlgebra.unipotentVarietyIdeal k k[T;T⁻¹] ≤
      RingHom.ker (laurentEval (dualNumberUnit k)) := by
  rw [unipotentVarietyIdeal_eq_span, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
  simp only [map_sub, map_one, laurentEval_T, zpow_one, coe_dualNumberUnit,
    add_sub_cancel_left]
  exact DualNumber.eps_ne_zero

end TauCeti.MultiplicativeGroup
