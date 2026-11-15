/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The completion of a nonnegatively graded algebra along its grading

Let `A = ⨁ₙ Aₙ` be an `ℕ`-graded algebra over a commutative semiring `R`, given internally by
`𝒜 : ℕ → Submodule R A` with `GradedAlgebra 𝒜`.  Its **completion along the grading** is the
algebra of formal series `∑ₙ aₙ` with `aₙ ∈ Aₙ`, multiplied by the Cauchy product.  It is the
completion of `A` for the descending filtration `⨁_{m ≥ n} Aₘ`, for instance the length-adic
completion of a path algebra with respect to its path-length grading.

This file realizes that completion as the subalgebra `TauCeti.gradedCompletion 𝒜` of the formal
power series `PowerSeries A` whose coefficient of index `n` lies in `Aₙ`: the Cauchy product of
power series is exactly the multiplication of such formal sums, so no separate ring structure has
to be built.  The subalgebra itself only uses that the grading is multiplicative
(`SetLike.GradedMonoid 𝒜`), not the decomposition of `A`.  The comparison map from `A` sends an
element to the power series of its homogeneous components; it is injective, and its image consists
of the series with finitely many nonzero coefficients.

## Main definitions

* `TauCeti.gradedCompletion`: the completion of `A` along `𝒜`, as a subalgebra of `PowerSeries A`.
* `TauCeti.gradedComponentSeries`: the power series of homogeneous components of an element of
  `A`, an algebra homomorphism `A →ₐ[R] PowerSeries A`.
* `TauCeti.toGradedCompletion`: the comparison map `A →ₐ[R] gradedCompletion 𝒜`.

## Main results

* `TauCeti.mem_gradedCompletion_iff`: a power series lies in the completion exactly when its
  `n`-th coefficient is homogeneous of degree `n`.
* `TauCeti.coeff_gradedComponentSeries`: the `n`-th coefficient of the series of components is
  the degree-`n` component.
* `TauCeti.gradedComponentSeries_injective` and `TauCeti.toGradedCompletion_injective`: the
  comparison map is injective.
* `TauCeti.mem_range_gradedComponentSeries_iff` and `TauCeti.mem_range_toGradedCompletion_iff`:
  **the image of `A` in its completion consists of the series with finitely many nonzero
  coefficients.**

## References

* B. Keller, *Deformed Calabi--Yau completions*, Section 6, for the completion of a graded path
  algebra with respect to path length.
-/

public section

namespace TauCeti

open DirectSum PowerSeries

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (𝒜 : ℕ → Submodule R A)

/-! ### The completion -/

section GradedMonoid

variable [SetLike.GradedMonoid 𝒜]

/-- **The completion of a nonnegatively graded algebra along its grading**: the subalgebra of
formal power series over `A` whose coefficient of index `n` is homogeneous of degree `n`.  Its
elements are the formal sums `∑ₙ aₙ` with `aₙ ∈ 𝒜 n`, multiplied by the Cauchy product. -/
def gradedCompletion : Subalgebra R (PowerSeries A) where
  carrier := {f | ∀ n, coeff n f ∈ 𝒜 n}
  mul_mem' {f g} hf hg n := by
    rw [coeff_mul]
    refine Submodule.sum_mem _ fun ij hij => ?_
    rw [← Finset.mem_antidiagonal.mp hij]
    exact SetLike.mul_mem_graded (hf ij.1) (hg ij.2)
  add_mem' {f g} hf hg n := by
    rw [map_add]
    exact add_mem (hf n) (hg n)
  algebraMap_mem' r n := by
    rw [PowerSeries.algebraMap_apply, coeff_C]
    split_ifs with h
    · exact h ▸ SetLike.algebraMap_mem_graded 𝒜 r
    · exact zero_mem _

/-- A power series lies in the completion exactly when its `n`-th coefficient is homogeneous of
degree `n`. -/
@[simp]
theorem mem_gradedCompletion_iff {f : PowerSeries A} :
    f ∈ gradedCompletion 𝒜 ↔ ∀ n, coeff n f ∈ 𝒜 n :=
  Iff.rfl

end GradedMonoid

/-! ### The series of homogeneous components -/

variable [GradedAlgebra 𝒜]

/-- The power series of homogeneous components of a homogeneous element of degree `i` is the
monomial of that element in index `i`. -/
private theorem mk_decompose_of_mem {i : ℕ} {a : A} (ha : a ∈ 𝒜 i) :
    (PowerSeries.mk fun n => (decompose 𝒜 a n : A)) = monomial i a := by
  ext n
  rw [coeff_mk, coeff_monomial]
  split_ifs with h
  · exact h ▸ decompose_of_mem_same 𝒜 ha
  · exact decompose_of_mem_ne 𝒜 ha (Ne.symm h)

/-- The power series of homogeneous components of an element of a nonnegatively graded algebra:
the coefficient of index `n` is the degree-`n` component.  It is an algebra homomorphism, because
the degree-`n` component of a product is the Cauchy product of the components of the factors. -/
def gradedComponentSeries : A →ₐ[R] PowerSeries A where
  toFun a := PowerSeries.mk fun n => (decompose 𝒜 a n : A)
  map_one' := by
    rw [mk_decompose_of_mem 𝒜 (SetLike.one_mem_graded 𝒜), monomial_zero_eq_C_apply, map_one]
  map_mul' a b := by
    ext n
    rw [coeff_mk, coeff_mul, decompose_mul, DirectSum.coe_mul_apply_eq_sum_antidiagonal]
    simp only [coeff_mk]
  map_zero' := by
    ext n
    simp
  map_add' a b := by
    ext n
    simp
  commutes' r := by
    rw [mk_decompose_of_mem 𝒜 (SetLike.algebraMap_mem_graded 𝒜 r), monomial_zero_eq_C_apply,
      PowerSeries.algebraMap_apply]

/-- The `n`-th coefficient of the series of homogeneous components is the degree-`n`
component. -/
@[simp]
theorem coeff_gradedComponentSeries (a : A) (n : ℕ) :
    coeff n (gradedComponentSeries 𝒜 a) = (decompose 𝒜 a n : A) :=
  coeff_mk n fun n => (decompose 𝒜 a n : A)

/-- The series of components of a homogeneous element of degree `n` is the monomial of that
element in index `n`. -/
theorem gradedComponentSeries_of_mem {n : ℕ} {a : A} (ha : a ∈ 𝒜 n) :
    gradedComponentSeries 𝒜 a = monomial n a :=
  mk_decompose_of_mem 𝒜 ha

/-- An element is determined by the series of its homogeneous components. -/
theorem gradedComponentSeries_injective : Function.Injective (gradedComponentSeries 𝒜) := by
  intro a b hab
  refine (decompose 𝒜).injective (DirectSum.ext fun n => Subtype.ext ?_)
  simpa only [coeff_gradedComponentSeries] using congrArg (coeff n) hab

/-- **The series of homogeneous components of elements of `A` are exactly the series with
homogeneous coefficients and finitely many nonzero coefficients.** -/
theorem mem_range_gradedComponentSeries_iff {f : PowerSeries A} :
    f ∈ (gradedComponentSeries 𝒜).range ↔
      (∀ n, coeff n f ∈ 𝒜 n) ∧ (Function.support fun n => coeff n f).Finite := by
  classical
  rw [AlgHom.mem_range]
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨fun n => by simp, (decompose 𝒜 a).support.finite_toSet.subset fun n hn => ?_⟩
    simpa using hn
  · rintro ⟨hf, hfin⟩
    refine ⟨∑ n ∈ hfin.toFinset, coeff n f, ?_⟩
    rw [map_sum, Finset.sum_congr rfl fun n _ => gradedComponentSeries_of_mem 𝒜 (hf n)]
    ext m
    simp [coeff_monomial, eq_comm]

/-! ### The comparison map -/

/-- The series of homogeneous components lies in the completion. -/
theorem gradedComponentSeries_mem_gradedCompletion (a : A) :
    gradedComponentSeries 𝒜 a ∈ gradedCompletion 𝒜 :=
  (mem_gradedCompletion_iff 𝒜).2 fun n => by simp

/-- **The comparison map from a nonnegatively graded algebra to its completion**, sending an
element to the series of its homogeneous components. -/
noncomputable def toGradedCompletion : A →ₐ[R] gradedCompletion 𝒜 :=
  (gradedComponentSeries 𝒜).codRestrict (gradedCompletion 𝒜)
    (gradedComponentSeries_mem_gradedCompletion 𝒜)

/-- The comparison map, viewed as a power series, is the series of homogeneous components. -/
@[simp]
theorem coe_toGradedCompletion_apply (a : A) :
    (toGradedCompletion 𝒜 a : PowerSeries A) = gradedComponentSeries 𝒜 a :=
  (rfl)

/-- The comparison map is injective: a graded algebra embeds in its completion. -/
theorem toGradedCompletion_injective : Function.Injective (toGradedCompletion 𝒜) :=
  (AlgHom.injective_codRestrict _ _ _).2 (gradedComponentSeries_injective 𝒜)

/-- **The image of the comparison map consists of the series with finitely many nonzero
coefficients.** -/
theorem mem_range_toGradedCompletion_iff {f : gradedCompletion 𝒜} :
    f ∈ (toGradedCompletion 𝒜).range ↔
      (Function.support fun n => coeff n (f : PowerSeries A)).Finite := by
  refine Iff.trans ?_ <| (mem_range_gradedComponentSeries_iff 𝒜).trans <|
    and_iff_right ((mem_gradedCompletion_iff 𝒜).1 f.2)
  simp only [AlgHom.mem_range, Subtype.ext_iff, coe_toGradedCompletion_apply]

end TauCeti
