/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HahnSeries.Multiplication

/-!
# Powers of Hahn series and compatibility with coefficient scalars

Over a domain, taking a power multiplies the order and raises the leading coefficient to that
power. These formulas detect whether a leading pole term can be cancelled by a power.

The order formula allows semiring coefficients; Mathlib's `HahnSeries.addVal` requires ring
coefficients, so its `AddValuation.map_pow` does not cover this generality.

The formulas are `TauCeti.hahnSeries_leadingCoeff_pow n` and
`TauCeti.hahnSeries_orderTop_pow n`; both are also simplification lemmas. The exponent is
explicit, and the series is inferred from the equality being rewritten.

With the typeclasses below in scope, use the qualified names as follows:

```lean
example (f : HahnSeries Γ R) (n : ℕ) :
    (f ^ n).leadingCoeff = f.leadingCoeff ^ n :=
  TauCeti.hahnSeries_leadingCoeff_pow n (f := f)

example [Nontrivial R] (f : HahnSeries Γ R) (n : ℕ) :
    (f ^ n).orderTop = n • f.orderTop :=
  TauCeti.hahnSeries_orderTop_pow n (f := f)
```

This file also records that coefficientwise scalar multiplication associates and commutes with
multiplication of Hahn series (`TauCeti.hahnSeries_isScalarTower` and
`TauCeti.hahnSeries_smulCommClass`). Mathlib provides this for the action of Hahn
series on Hahn modules, and for Hahn series through their algebra structure; but the default
algebra structure on Laurent series `R⸨X⸩` comes from `R⟦X⟧` and is not definitionally the
coefficientwise one, so for instance the `R⸨X⸩`-module structure on `R`-derivations of `R⸨X⸩`
needs this instance.

Finally, `HahnModule.of_symm_smul'` reads the coefficientwise action of `R` on `HahnModule Γ R V`
through `HahnModule.of`, for the action instance underlying the `R`-module structure.
`HahnModule.ofLinearEquiv` bundles this coefficient-preserving comparison as an `R`-linear
equivalence. The lemmas `HahnModule.coeff_smul_single_zero` and
`HahnModule.single_smul_single_zero` describe the convolution action of a scalar series on a
constant module-valued series, coefficientwise and on monomials.
-/

public section

namespace TauCeti

/-- Coefficientwise scalar multiplication commutes with multiplication of Hahn series. -/
instance hahnSeries_smulCommClass {Γ R : Type*} [AddCommMonoid Γ] [PartialOrder Γ]
    [IsOrderedCancelAddMonoid Γ] [CommSemiring R] :
    SMulCommClass R (HahnSeries Γ R) (HahnSeries Γ R) where
  smul_comm r x y := by
    simp only [← HahnSeries.C_mul_eq_smul, smul_eq_mul, mul_left_comm]

/-- Coefficientwise scalar multiplication associates with multiplication of Hahn series. -/
instance hahnSeries_isScalarTower {Γ R : Type*} [AddCommMonoid Γ] [PartialOrder Γ]
    [IsOrderedCancelAddMonoid Γ] [Semiring R] :
    IsScalarTower R (HahnSeries Γ R) (HahnSeries Γ R) where
  smul_assoc r x y := by
    simp only [← HahnSeries.C_mul_eq_smul, smul_eq_mul, mul_assoc]

variable {Γ R : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [Semiring R] [NoZeroDivisors R]

/-- The leading coefficient of a power is the power of the leading coefficient. -/
@[simp]
theorem hahnSeries_leadingCoeff_pow (n : ℕ) {f : HahnSeries Γ R} :
    (f ^ n).leadingCoeff = f.leadingCoeff ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

/-- The order of a power is the corresponding multiple of the order, including at zero. -/
@[simp]
theorem hahnSeries_orderTop_pow [Nontrivial R] (n : ℕ) {f : HahnSeries Γ R} :
    (f ^ n).orderTop = n • f.orderTop := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih, add_nsmul]

end TauCeti

namespace HahnModule

/-- The coefficientwise scalar action underlying the `R`-module structure, read through `of`.
Mathlib's `HahnModule.of_symm_smul` is stated for a different, though propositionally equal,
scalar action instance, so it does not rewrite this one. -/
@[simp]
theorem of_symm_smul' {Γ R V : Type*} [PartialOrder Γ] [Monoid R] [AddMonoid V]
    [DistribMulAction R V] (r : R) (x : HahnModule Γ R V) :
    (of R).symm (r • x) = r • (of R).symm x :=
  rfl

/-- The coefficient-preserving comparison between Hahn series and Hahn modules, linear for the
coefficientwise action of `R`. -/
noncomputable def ofLinearEquiv (R : Type*) {Γ V : Type*} [PartialOrder Γ] [Semiring R]
    [AddCommMonoid V] [Module R V] : HahnSeries Γ V ≃ₗ[R] HahnModule Γ R V where
  __ := of R
  map_add' := of_add
  map_smul' r f := (of R).symm.injective <| by simp

@[simp]
theorem ofLinearEquiv_apply {Γ R V : Type*} [PartialOrder Γ] [Semiring R] [AddCommMonoid V]
    [Module R V] (f : HahnSeries Γ V) : ofLinearEquiv R f = of R f := (rfl)

@[simp]
theorem ofLinearEquiv_symm_apply {Γ R V : Type*} [PartialOrder Γ] [Semiring R] [AddCommMonoid V]
    [Module R V] (f : HahnModule Γ R V) : (ofLinearEquiv R).symm f = (of R).symm f := (rfl)

open HahnSeries

variable {Γ R V : Type*} [AddCommMonoid Γ] [PartialOrder Γ]
  [IsOrderedCancelAddMonoid Γ]

/-- Multiplying a constant module-valued series by a scalar series multiplies each coefficient
by the constant vector. -/
@[simp]
theorem coeff_smul_single_zero [Zero R] [AddCommMonoid V] [SMulWithZero R V]
    (f : HahnSeries Γ R) (v : V) (g : Γ) :
    ((of R).symm (f • of R (single 0 v))).coeff g = f.coeff g • v := by
  classical
  rw [coeff_smul_right (x := f) (y := of R (single (0 : Γ) v))
    (Set.isPWO_singleton 0) (by exact support_single_subset)]
  trans f.coeff g • ((of R).symm (of R (single (0 : Γ) v))).coeff 0
  · apply Finset.sum_eq_single (g, 0)
    · intro ij hij hne
      have hj : ij.2 = 0 := ((Finset.mem_vaddAntidiagonal _ _).mp hij).2.1
      have hi : ij.1 = g := by simpa [hj] using ((Finset.mem_vaddAntidiagonal _ _).mp hij).2.2
      exact (hne (Prod.ext hi hj)).elim
    · intro h
      by_cases hf : f.coeff g = 0
      · simp [hf]
      · exact (h ((Finset.mem_vaddAntidiagonal _ _).mpr ⟨hf, rfl, by simp⟩)).elim
  · simp

/-- A scalar monomial times a constant vector series is a vector-valued monomial. -/
@[simp]
theorem single_smul_single_zero [Zero R] [AddCommMonoid V] [SMulWithZero R V]
    (g : Γ) (r : R) (v : V) :
    single g r • of R (single 0 v) = of R (single g (r • v)) := by
  apply HahnModule.ext
  funext h
  by_cases hh : h = g <;> simp [hh]

end HahnModule
