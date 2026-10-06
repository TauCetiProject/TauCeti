/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import TauCeti.FieldTheory.RatFunc.Automorphism
-- Non-public: `Matrix.GeneralLinearGroup.mem_center_iff_entries` identifies the kernel of the
-- action below with the centre of `GL₂(k)`, in the proofs only.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.CenterFinTwo

/-!
# Linear fractional transformations of the rational function field

Four elements `a, b, c, d` of an integral domain `k` with `a d - b c ≠ 0` give the linear fractional
transformation `(a X + b) / (c X + d)` of `k(X)`. The inverse linear fractional formula recovers
`X` from it. When `k` is a field, it is a transcendental generator of `k(X)` over `k` and
therefore the image of `X` under an automorphism of `k(X)` over `k`.

Over a field `k`, the coefficients form an invertible `2 × 2` matrix, and conversely every
invertible `2 × 2` matrix over `k` has nonzero determinant, so the construction applies to `GL₂(k)`.

## Main definitions

* `RatFunc.mobiusOf`: the linear fractional transformation of four coefficients, with its defining
  equation `mobiusOf_def`.
* `RatFunc.mobiusAutOf`: the automorphism of `k(X)` sending `X` to it.
* `Matrix.GeneralLinearGroup.mobius` (with `Matrix.GeneralLinearGroup.mobius_def`) and
  `Matrix.GeneralLinearGroup.mobiusAut`: the same for an invertible matrix.
* `RatFunc.mobiusAutHom`: the group homomorphism `GL₂(k) →* Aut(k(X)/k)`.
* `RatFunc.pglEquivAlgEquiv`: the isomorphism `PGL₂(k) ≃* Aut(k(X)/k)`, evaluated on a class of
  matrices by `Matrix.GeneralLinearGroup.pglEquivAlgEquiv_mk`.
* `RatFunc.translationAut`: the translation `X ↦ X + c`.

## Main results

* `RatFunc.transcendental_mobiusOf` and `RatFunc.adjoin_mobiusOf_eq_top`: a linear fractional
  transformation is a transcendental generator of `k(X)`.
* `RatFunc.X_eq_div_mobiusOf`: the inverse coefficient matrix recovers `X`.
* `Matrix.GeneralLinearGroup.mobiusAut_mobius` and `RatFunc.mobiusAutHom`: substitution composes
  the coefficient matrices in the opposite order, so inversion gives a group homomorphism
  `GL₂(k) →* Aut(k(X)/k)`.
* `RatFunc.infinite_algEquiv`: over an infinite field the translations already make
  `Aut(k(X)/k)` infinite.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Exercise 1.2.
-/

public section

open scoped MatrixGroups

namespace RatFunc

variable {K : Type*}

section Domain

variable [CommRing K] [IsDomain K]

/-- A nonzero linear polynomial in `X`, read in `k(X)`, is nonzero. -/
theorem mul_X_add_C_ne_zero {c d : K} (hcd : c ≠ 0 ∨ d ≠ 0) : C c * X + C d ≠ 0 := by
  have hmap : C c * X + C d =
      algebraMap (Polynomial K) (RatFunc K) (Polynomial.C c * Polynomial.X + Polynomial.C d) := by
    rw [map_add, map_mul, algebraMap_C, algebraMap_C, algebraMap_X]
  rw [hmap, Ne, map_eq_zero_iff _ (algebraMap_injective K)]
  intro h0
  have h1 : c = 0 := by simpa using congrArg (fun p : Polynomial K ↦ p.coeff 1) h0
  have h0' : d = 0 := by simpa using congrArg (fun p : Polynomial K ↦ p.coeff 0) h0
  rcases hcd with h | h
  · exact h h1
  · exact h h0'

section MobiusOf

variable (a b c d : K)

/-- The **linear fractional transformation** `(a X + b) / (c X + d)` of `k(X)`. -/
noncomputable def mobiusOf : RatFunc K := (C a * X + C b) / (C c * X + C d)

/-- The defining equation of `mobiusOf`. -/
theorem mobiusOf_def : mobiusOf a b c d = (C a * X + C b) / (C c * X + C d) := (rfl)

variable {a b c d} (hdet : a * d - b * c ≠ 0)
include hdet

/-- The denominator of a linear fractional transformation with invertible coefficients is
nonzero. -/
theorem mobiusOf_den_ne_zero : C c * X + C d ≠ 0 := by
  refine mul_X_add_C_ne_zero ?_
  by_contra h
  simp only [not_or, not_not] at h
  exact hdet (by rw [h.1, h.2]; ring)

/-- Clearing the denominator of a linear fractional transformation. -/
theorem mobiusOf_mul_den : mobiusOf a b c d * (C c * X + C d) = C a * X + C b :=
  div_mul_cancel₀ _ (mobiusOf_den_ne_zero hdet)

/-- The coefficient `a - c · m` scaled by the denominator is the determinant. -/
theorem sub_mul_mobiusOf_mul_den :
    (C a - C c * mobiusOf a b c d) * (C c * X + C d) = C (a * d - b * c) := by
  have h := mobiusOf_mul_den hdet
  rw [map_sub, map_mul, map_mul]
  linear_combination (-(C c)) * h

/-- **The coefficient `a - c · m` is nonzero**, being the determinant over the denominator. -/
theorem sub_mul_mobiusOf_ne_zero : C a - C c * mobiusOf a b c d ≠ 0 := by
  intro h0
  refine ((map_eq_zero_iff C C_injective).not.mpr hdet) ?_
  rw [← sub_mul_mobiusOf_mul_den hdet, h0, zero_mul]

/-- **The inverse coefficient matrix recovers `X`**: `X · (a - c · m) = d · m - b`, both sides
being the determinant times `X` over the denominator. -/
theorem X_mul_sub_mul_mobiusOf :
    (X : RatFunc K) * (C a - C c * mobiusOf a b c d) = C d * mobiusOf a b c d - C b := by
  refine mul_right_cancel₀ (mobiusOf_den_ne_zero hdet) ?_
  have h := mobiusOf_mul_den hdet
  linear_combination (-(C c * X + C d)) * h

/-- **`X` is a linear fractional transformation of `m`**, by the inverse coefficient matrix. -/
theorem X_eq_div_mobiusOf :
    (X : RatFunc K) =
      (C d * mobiusOf a b c d - C b) / (C a - C c * mobiusOf a b c d) :=
  (eq_div_iff (sub_mul_mobiusOf_ne_zero hdet)).mpr (X_mul_sub_mul_mobiusOf hdet)

/-- **A linear fractional transformation is transcendental**: its inverse formula expresses
`X` in terms of it and the constants. -/
theorem transcendental_mobiusOf : Transcendental K (mobiusOf a b c d) := by
  intro halg
  apply transcendental_X (K := K)
  rw [X_eq_div_mobiusOf hdet, div_eq_mul_inv]
  have hC (x : K) : IsAlgebraic K (C x : RatFunc K) := by
    simpa only [algebraMap_eq_C] using isAlgebraic_algebraMap (A := RatFunc K) x
  exact ((hC d).mul halg |>.sub (hC b)).mul (((hC a).sub ((hC c).mul halg)).inv)

/-- A nonzero linear expression in a Möbius transformation is nonzero. -/
theorem mul_mobiusOf_add_ne_zero (c' d' : K) (hcd' : c' ≠ 0 ∨ d' ≠ 0) :
    C c' * mobiusOf a b c d + C d' ≠ 0 := by
  intro h0
  apply mul_X_add_C_ne_zero hcd'
  have hpoly : (Polynomial.C c' * Polynomial.X + Polynomial.C d' : Polynomial K) = 0 :=
    (transcendental_iff.mp (transcendental_mobiusOf hdet)) _
      (by simpa [← algebraMap_eq_C] using h0)
  simpa using congrArg (algebraMap (Polynomial K) (RatFunc K)) hpoly

/-- **A linear fractional transformation is the identity exactly for a scalar coefficient
matrix**: `(a X + b) / (c X + d) = X` if and only if `b = 0`, `c = 0` and `a = d`. -/
theorem mobiusOf_eq_X_iff : mobiusOf a b c d = X ↔ b = 0 ∧ c = 0 ∧ a = d := by
  constructor
  · intro h
    rw [mobiusOf_def, div_eq_iff (mobiusOf_den_ne_zero hdet)] at h
    have hpoly : (Polynomial.C a * Polynomial.X + Polynomial.C b : Polynomial K) =
        Polynomial.C c * Polynomial.X ^ 2 + Polynomial.C d * Polynomial.X := by
      refine algebraMap_injective K ?_
      simp only [map_add, map_mul, map_pow, algebraMap_C, algebraMap_X]
      linear_combination h
    refine ⟨?_, ?_, ?_⟩
    · simpa using congrArg (fun p : Polynomial K ↦ p.coeff 0) hpoly
    · simpa using (congrArg (fun p : Polynomial K ↦ p.coeff 2) hpoly).symm
    · simpa using congrArg (fun p : Polynomial K ↦ p.coeff 1) hpoly
  · rintro ⟨rfl, rfl, rfl⟩
    have ha : a ≠ 0 := by
      intro h
      rw [h] at hdet
      simp at hdet
    simp [mobiusOf_def, (map_eq_zero_iff C C_injective).not.mpr ha]

/-- Multiplying a linear expression in a Möbius transformation by its denominator multiplies
its coefficient row by the coefficient matrix. -/
theorem mul_mobiusOf_add_mul_den (c' d' : K) :
    (C c' * mobiusOf a b c d + C d') * (C c * X + C d) =
      C (c' * a + d' * c) * X + C (c' * b + d' * d) := by
  have hm := mobiusOf_mul_den hdet
  simp only [map_add, map_mul]
  linear_combination (C c') * hm

end MobiusOf

/-- A translation `X + c` is a linear fractional transformation. -/
@[simp]
theorem mobiusOf_one_right (c : K) : mobiusOf 1 c 0 1 = X + C c := by
  simp [mobiusOf_def]

end Domain

end RatFunc

namespace Matrix.GeneralLinearGroup

open RatFunc

variable {K : Type*} [CommRing K] [IsDomain K]

variable (A : GL (Fin 2) K)

/-- The **linear fractional transformation of an invertible matrix** `A = !![a, b; c, d]`. -/
noncomputable def mobius : RatFunc K :=
  mobiusOf ((A : Matrix (Fin 2) (Fin 2) K) 0 0) ((A : Matrix (Fin 2) (Fin 2) K) 0 1)
    ((A : Matrix (Fin 2) (Fin 2) K) 1 0) ((A : Matrix (Fin 2) (Fin 2) K) 1 1)

/-- The defining equation of `mobius`. -/
theorem mobius_def : mobius A =
    mobiusOf ((A : Matrix (Fin 2) (Fin 2) K) 0 0) ((A : Matrix (Fin 2) (Fin 2) K) 0 1)
      ((A : Matrix (Fin 2) (Fin 2) K) 1 0) ((A : Matrix (Fin 2) (Fin 2) K) 1 1) := (rfl)

/-- The identity matrix gives the identity transformation. -/
@[simp]
theorem mobius_one : mobius (1 : GL (Fin 2) K) = X := by
  rw [mobius, mobiusOf]
  simp

end Matrix.GeneralLinearGroup

namespace RatFunc

variable {K : Type*}

section Field

variable [Field K]

section MobiusOf

variable {a b c d : K} (hdet : a * d - b * c ≠ 0)
include hdet

/-- **A linear fractional transformation generates `k(X)`**, since `X` is a linear fractional
transformation of it. -/
theorem adjoin_mobiusOf_eq_top : IntermediateField.adjoin K {mobiusOf a b c d} = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← adjoin_X]
  refine IntermediateField.adjoin_simple_le_iff.mpr ?_
  rw [X_eq_div_mobiusOf hdet]
  simp only [← algebraMap_eq_C]
  exact div_mem
    (sub_mem (mul_mem (IntermediateField.algebraMap_mem _ _)
      (IntermediateField.mem_adjoin_simple_self _ _)) (IntermediateField.algebraMap_mem _ _))
    (sub_mem (IntermediateField.algebraMap_mem _ _)
      (mul_mem (IntermediateField.algebraMap_mem _ _)
        (IntermediateField.mem_adjoin_simple_self _ _)))

/-- **The automorphism of `k(X)` given by a linear fractional transformation**: the automorphism
sending `X` to `(a X + b) / (c X + d)`. -/
noncomputable def mobiusAutOf : RatFunc K ≃ₐ[K] RatFunc K :=
  algEquivOfAdjoinEqTop (adjoin_mobiusOf_eq_top hdet)

@[simp]
theorem mobiusAutOf_X : mobiusAutOf hdet X = mobiusOf a b c d :=
  algEquivOfAdjoinEqTop_X _

/-- **A linear fractional transformation gives the identity automorphism exactly for a scalar
coefficient matrix.** -/
theorem mobiusAutOf_eq_one_iff : mobiusAutOf hdet = 1 ↔ b = 0 ∧ c = 0 ∧ a = d := by
  rw [← mobiusOf_eq_X_iff hdet]
  refine ⟨fun h ↦ ?_, fun h ↦ algEquiv_ext (by rw [mobiusAutOf_X, h, AlgEquiv.one_apply])⟩
  rw [← mobiusAutOf_X hdet, h, AlgEquiv.one_apply]

section Comp

variable (a' b' c' d' : K)

/-- **Substitution composes linear fractional transformations by multiplying their coefficient
matrices in the opposite order.** Only the inner transformation needs an invertible coefficient
matrix; the outer coefficients may be arbitrary. -/
theorem mobiusAutOf_mobiusOf :
    mobiusAutOf hdet (mobiusOf a' b' c' d') =
      mobiusOf (a' * a + b' * c) (a' * b + b' * d) (c' * a + d' * c) (c' * b + d' * d) := by
  rw [mobiusOf_def, map_div₀]
  simp only [map_add, map_mul, ← algebraMap_eq_C, AlgEquiv.commutes, mobiusAutOf_X]
  simp only [algebraMap_eq_C]
  rw [← mul_div_mul_right _ _ (mobiusOf_den_ne_zero hdet),
    mul_mobiusOf_add_mul_den hdet, mul_mobiusOf_add_mul_den hdet, mobiusOf_def]

end Comp

end MobiusOf

end Field

end RatFunc

namespace Matrix.GeneralLinearGroup

open RatFunc

variable {K : Type*} [Field K] (A : GL (Fin 2) K)

/-- The automorphism of `k(X)` given by an invertible matrix. -/
noncomputable def mobiusAut : RatFunc K ≃ₐ[K] RatFunc K :=
  mobiusAutOf (by simpa only [Matrix.det_fin_two] using A.det_ne_zero)

@[simp]
theorem mobiusAut_X : mobiusAut A X = mobius A :=
  mobiusAutOf_X _

/-- **Substituting one linear fractional transformation into another multiplies the matrices in
the opposite order.** -/
theorem mobiusAut_mobius (B : GL (Fin 2) K) : mobiusAut A (mobius B) = mobius (B * A) := by
  rw [mobiusAut, mobius_def, mobius_def, mobiusAutOf_mobiusOf]
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

/-- **The identity automorphism comes exactly from the central matrices.** -/
theorem mobiusAut_eq_one_iff : mobiusAut A = 1 ↔ A ∈ Subgroup.center (GL (Fin 2) K) := by
  rw [mobiusAut, mobiusAutOf_eq_one_iff, Matrix.GeneralLinearGroup.mem_center_iff_entries]

end Matrix.GeneralLinearGroup

namespace RatFunc

open Matrix.GeneralLinearGroup

variable {K : Type*} [Field K]

/-- **The linear fractional transformations as a group of automorphisms**: the homomorphism
`GL₂(k) →* Aut(k(X)/k)` sending `A` to the automorphism `X ↦ (a X + b) / (c X + d)` of the inverse
matrix. Inversion is what makes it a homomorphism rather than an antihomomorphism, since
substitution composes the matrices in the opposite order. -/
noncomputable def mobiusAutHom : GL (Fin 2) K →* (RatFunc K ≃ₐ[K] RatFunc K) where
  toFun A := mobiusAut A⁻¹
  map_one' := algEquiv_ext (by simp)
  map_mul' A B := algEquiv_ext (by
    rw [AlgEquiv.mul_apply, mobiusAut_X, mobiusAut_X, mobiusAut_mobius, mul_inv_rev])

end RatFunc

namespace Matrix.GeneralLinearGroup

open RatFunc

variable {K : Type*} [Field K] (A : GL (Fin 2) K)

@[simp]
theorem mobiusAutHom_apply_X : mobiusAutHom A X = mobius A⁻¹ :=
  mobiusAut_X _

end Matrix.GeneralLinearGroup

namespace RatFunc

open Matrix.GeneralLinearGroup

variable {K : Type*} [Field K]

/-- **The kernel of the linear fractional action is the centre of `GL₂(k)`**: the scalar matrices.
So `PGL₂(k)` acts faithfully on `k(X)`. -/
theorem ker_mobiusAutHom :
    (mobiusAutHom : GL (Fin 2) K →* _).ker = Subgroup.center (GL (Fin 2) K) := by
  ext A
  rw [MonoidHom.mem_ker, mobiusAutHom, MonoidHom.coe_mk, OneHom.coe_mk, mobiusAut_eq_one_iff,
    Subgroup.inv_mem_iff]

/-- **Every generator of `k(X)` over `k` is a linear fractional transformation**: its numerator and
denominator have degree at most one, and the determinant of their coefficients is nonzero. -/
theorem exists_mobiusOf_eq_of_adjoin_eq_top {f : RatFunc K}
    (htop : IntermediateField.adjoin K {f} = ⊤) :
    ∃ a b c d : K, a * d - b * c ≠ 0 ∧ mobiusOf a b c d = f := by
  have hmax : max f.num.natDegree f.denom.natDegree = 1 := by
    rw [← finrank_eq_max_natDegree f]
    exact IntermediateField.finrank_eq_one_iff_eq_top.mpr htop
  have hnumle : f.num.natDegree ≤ 1 := le_of_max_le_left hmax.le
  have hdenle : f.denom.natDegree ≤ 1 := le_of_max_le_right hmax.le
  have hnum := Polynomial.eq_X_add_C_of_natDegree_le_one hnumle
  have hden := Polynomial.eq_X_add_C_of_natDegree_le_one hdenle
  set a := f.num.coeff 1 with ha
  set b := f.num.coeff 0 with hb
  set c := f.denom.coeff 1 with hc
  set d := f.denom.coeff 0 with hd
  have hdet : a * d - b * c ≠ 0 := by
    by_cases hc0 : c = 0
    · -- the denominator is the constant `d ≠ 0`, so the numerator has degree one and `a ≠ 0`
      have hdeg : f.denom.natDegree = 0 := by
        refine Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr ?_
        rw [hden, hc0, map_zero, zero_mul, zero_add]
        exact Polynomial.degree_C_le
      have hnum1 : f.num.natDegree = 1 := by
        rw [hdeg] at hmax
        simpa using hmax
      have hane : a ≠ 0 := by
        rw [ha, ← hnum1]
        exact Polynomial.leadingCoeff_ne_zero.mpr fun h0 ↦ by simp [h0] at hnum1
      have hdne : d ≠ 0 := by
        intro h0
        refine f.denom_ne_zero ?_
        rw [hden, hc0, h0, map_zero, zero_mul, zero_add]
      rw [hc0, mul_zero, sub_zero]
      exact mul_ne_zero hane hdne
    · -- otherwise the denominator would divide the numerator, against their coprimality
      intro hzero
      have hca : (Polynomial.C c * Polynomial.C (a * c⁻¹) : Polynomial K) = Polynomial.C a := by
        rw [← Polynomial.C_mul]
        congr 1
        field_simp
      have hcb : (Polynomial.C d * Polynomial.C (a * c⁻¹) : Polynomial K) = Polynomial.C b := by
        rw [← Polynomial.C_mul]
        congr 1
        field_simp
        linear_combination hzero
      have hdvd : f.denom ∣ f.num := ⟨Polynomial.C (a * c⁻¹), by
        rw [hnum, hden]
        linear_combination (-(Polynomial.X : Polynomial K)) * hca - hcb⟩
      have hunit := (isCoprime_num_denom f).isUnit_of_dvd' hdvd dvd_rfl
      have hdeg0 := Polynomial.natDegree_eq_zero_of_isUnit hunit
      have hle : 1 ≤ f.denom.natDegree := Polynomial.le_natDegree_of_ne_zero (hc ▸ hc0)
      omega
  refine ⟨a, b, c, d, hdet, ?_⟩
  rw [mobiusOf_def, ← num_div_denom f]
  conv_rhs => rw [hnum, hden]
  simp only [map_add, map_mul, algebraMap_C, algebraMap_X]

/-- **Every automorphism of `k(X)` over `k` is a linear fractional transformation.** -/
theorem mobiusAutHom_surjective :
    Function.Surjective (mobiusAutHom : GL (Fin 2) K →* (RatFunc K ≃ₐ[K] RatFunc K)) := by
  intro σ
  obtain ⟨a, b, c, d, hdet, hf⟩ :=
    exists_mobiusOf_eq_of_adjoin_eq_top (adjoin_apply_X_eq_top σ)
  have hunit : IsUnit (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) K) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two_of]
    exact isUnit_iff_ne_zero.mpr hdet
  refine ⟨hunit.unit⁻¹, ?_⟩
  refine algEquiv_ext ?_
  rw [mobiusAutHom_apply_X, inv_inv, mobius_def]
  simpa [IsUnit.unit_spec] using hf

/-- **`PGL₂(k)` is the automorphism group of the rational function field** (Stichtenoth,
Exercise 1.2): the linear fractional transformations exhaust the automorphisms of `k(X)` over `k`,
and two matrices give the same automorphism exactly when they differ by a scalar. -/
noncomputable def pglEquivAlgEquiv : PGL(2, K) ≃* (RatFunc K ≃ₐ[K] RatFunc K) :=
  (QuotientGroup.quotientMulEquivOfEq ker_mobiusAutHom.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ mobiusAutHom_surjective)

end RatFunc

namespace Matrix.GeneralLinearGroup

open RatFunc

variable {K : Type*} [Field K]

/-- The isomorphism `PGL₂(k) ≃* Aut(k(X)/k)` sends the class of a matrix to its linear fractional
transformation; with `Matrix.GeneralLinearGroup.mobiusAutHom_apply_X` this evaluates it at `X`. -/
@[simp]
theorem pglEquivAlgEquiv_mk (A : GL (Fin 2) K) :
    pglEquivAlgEquiv (Matrix.ProjGenLinGroup.mk A) = mobiusAutHom A := by rfl

end Matrix.GeneralLinearGroup

namespace RatFunc

variable {K : Type*} [Field K]

section Translation

variable (b : K)

/-- The **translation automorphism** `X ↦ X + c` of `k(X)`. -/
noncomputable def translationAut : RatFunc K ≃ₐ[K] RatFunc K :=
  mobiusAutOf (a := 1) (b := b) (c := 0) (d := 1) (by simp)

@[simp]
theorem translationAut_X : translationAut b X = X + C b := by
  rw [translationAut, mobiusAutOf_X, mobiusOf_one_right]

/-- Distinct scalars give distinct translations. -/
theorem translationAut_injective : Function.Injective (translationAut : K → _) := by
  intro b₁ b₂ h
  have hX := congrArg (fun σ : RatFunc K ≃ₐ[K] RatFunc K ↦ σ X) h
  simp only [translationAut_X, add_right_inj] at hX
  exact C_injective hX

/-- **The automorphism group of `k(X)` over an infinite field is infinite**, witnessed by the
translations. This is why the finiteness of the automorphism group of a function field needs genus
at least two. -/
theorem infinite_algEquiv [Infinite K] : Infinite (RatFunc K ≃ₐ[K] RatFunc K) :=
  Infinite.of_injective _ (translationAut_injective (K := K))

end Translation

end RatFunc
