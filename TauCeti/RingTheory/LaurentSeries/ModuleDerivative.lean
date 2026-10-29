/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.HahnSeries.Bilinear
public import TauCeti.RingTheory.LaurentSeries.Lattice

/-!
# The derivative and residue pairing of module-valued Laurent series

For a module `V` over a semiring `R`, the `V`-valued Laurent series `V((t))` are modelled as
`HahnModule ℤ R V`, on which the scalar Laurent series `R⸨X⸩` act by convolution. This file
transports Mathlib's coefficientwise derivative `LaurentSeries.derivative` on `LaurentSeries V`
through `HahnModule.of` to the derivative `D` of `V((t))`, so that `D (v tⁿ) = n v tⁿ⁻¹`.

Over a commutative ring, `D` is a derivation over the derivative of scalar Laurent series:
`D (f • x) = D f • x + f • D x`. The proof goes through the Euler operator `t D`, which multiplies
the coefficient of `tⁿ` by `n`. The derivative maps the lattice `U_a(V) = tᵃ V⟦t⟧` into
`U_{a - 1}(V)`, which is its continuity for the lattice topology, and it commutes with linear maps
of coefficients.

For a bilinear form `Φ` on `V`, extended coefficientwise by `HahnModule.convolution`, the residue
pairing is `(x, y) ↦ Res Φ(x, D y) dt`, the coefficient of `t⁻¹` in `Φ(x, D y)`. On monomials it
pairs `v tᵐ` and `w tⁿ` to `n Φ(v, w)` when `m + n = 0`, and to zero otherwise.

## Main definitions and results

* `HahnModule.derivative R`: the derivative `D` of `V`-valued Laurent series.
* `HahnModule.derivative_of`, `HahnModule.of_symm_derivative`: `D` is Mathlib's derivative of
  `LaurentSeries V`, read through `HahnModule.of`.
* `HahnModule.coeff_derivative`: the coefficient of `tⁿ` in `D x` is `(n + 1) x_{n + 1}`.
* `HahnModule.derivative_single`: `D (v tⁿ) = n v tⁿ⁻¹`.
* `HahnModule.coeff_single_one_smul_derivative`: the Euler operator `t D` multiplies the
  coefficient of `tⁿ` by `n`.
* `HahnModule.derivative_smul`: the Leibniz rule `D (f • x) = D f • x + f • D x`.
* `HahnModule.derivative_mem_lattice`: `D` maps `U_a(V)` into `U_{a - 1}(V)`.
* `HahnModule.derivative_map`: `D` commutes with linear maps of coefficients.
* `HahnModule.residuePairing R Φ`: the residue pairing `(x, y) ↦ Res Φ(x, D y) dt`.
* `HahnModule.residuePairing_single_single`: the residue pairing on monomials.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.2 and §1.3.
-/

public section

noncomputable section

open HahnSeries
open scoped LaurentSeries

namespace HahnModule

section Semiring

variable (R : Type*) {V W : Type*} [Semiring R] [AddCommGroup V] [Module R V] [AddCommGroup W]
  [Module R W]

/-- The derivative `D (v tⁿ) = n v tⁿ⁻¹` of `V`-valued Laurent series: Mathlib's coefficientwise
derivative `LaurentSeries.derivative` of `LaurentSeries V`, transported through `HahnModule.of`. -/
def derivative : HahnModule ℤ R V →ₗ[R] HahnModule ℤ R V :=
  (ofLinearEquiv R).toLinearMap ∘ₗ LaurentSeries.derivative R ∘ₗ
    (ofLinearEquiv R).symm.toLinearMap

variable {R}

/-- On `HahnModule.of f`, the derivative is Mathlib's derivative of `f`. -/
theorem derivative_of (f : LaurentSeries V) :
    derivative R (of R f) = of R (LaurentSeries.derivative R f) := by
  simp [derivative]

/-- Read through `HahnModule.of`, the derivative is Mathlib's derivative. -/
theorem of_symm_derivative (x : HahnModule ℤ R V) :
    (of R).symm (derivative R x) = LaurentSeries.derivative R ((of R).symm x) := by
  simp [derivative]

/-- The coefficient of `tⁿ` in `D x` is `(n + 1)` times the coefficient of `tⁿ⁺¹` in `x`. -/
@[simp]
theorem coeff_derivative (x : HahnModule ℤ R V) (n : ℤ) :
    ((of R).symm (derivative R x)).coeff n = (n + 1) • ((of R).symm x).coeff (n + 1) := by
  simp [derivative]

/-- The derivative of a monomial: `D (v tⁿ) = n v tⁿ⁻¹`. -/
@[simp]
theorem derivative_single (n : ℤ) (v : V) :
    derivative R (of R (single n v)) = of R (single (n - 1) (n • v)) := by
  rw [derivative_of, LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_single,
    Nat.cast_one, Ring.choose_one_right]

/-- The derivative maps the lattice `U_a(V) = tᵃ V⟦t⟧` into `U_{a - 1}(V)`: continuity of `D` for
the topology whose neighbourhoods of zero are these lattices. -/
theorem derivative_mem_lattice {a : ℤ} {x : HahnModule ℤ R V}
    (hx : x ∈ TauCeti.HahnModule.lattice R V a) :
    derivative R x ∈ TauCeti.HahnModule.lattice R V (a - 1) := by
  rw [TauCeti.HahnModule.mem_lattice_iff] at hx ⊢
  intro n hn
  rw [coeff_derivative, hx (n + 1) (by omega), smul_zero]

/-- The derivative commutes with a linear map `g : V → W` applied to coefficients. -/
theorem derivative_map (g : V →ₗ[R] W) (x : HahnModule ℤ R V) :
    derivative R (of R (((of R).symm x).map g)) =
      of R (((of R).symm (derivative R x)).map g) := by
  simp [derivative]

end Semiring

section CommRing

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The Euler operator `t D` multiplies the coefficient of `tⁿ` by `n`. -/
theorem coeff_single_one_smul_derivative (x : HahnModule ℤ R V) (n : ℤ) :
    ((of R).symm (single (1 : ℤ) (1 : R) • derivative R x)).coeff n =
      n • ((of R).symm x).coeff n := by
  have h := coeff_single_smul_vadd (r := (1 : R)) (x := derivative R x) (a := n - 1)
    (b := (1 : ℤ))
  rw [vadd_eq_add, add_sub_cancel] at h
  rw [h, one_smul, coeff_derivative, sub_add_cancel]

/-- The Euler operator `t D` of scalar Laurent series multiplies the coefficient of `tⁿ` by `n`. -/
private theorem coeff_single_one_mul_derivative (f : R⸨X⸩) (n : ℤ) :
    (single (1 : ℤ) (1 : R) * LaurentSeries.derivative R f).coeff n = n • f.coeff n := by
  have h := coeff_single_mul_add (r := (1 : R)) (x := LaurentSeries.derivative R f) (a := n - 1)
    (b := (1 : ℤ))
  rw [sub_add_cancel] at h
  rw [h, one_mul]
  simp only [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff,
    Nat.cast_one, sub_add_cancel, Ring.choose_one_right]

/-- The Leibniz rule for the Euler operator `t D`. -/
private theorem single_one_smul_derivative_smul (f : R⸨X⸩) (x : HahnModule ℤ R V) :
    single (1 : ℤ) (1 : R) • derivative R (f • x) =
      (single (1 : ℤ) (1 : R) * LaurentSeries.derivative R f) • x +
        f • (single (1 : ℤ) (1 : R) • derivative R x) := by
  ext n
  have hf : (single (1 : ℤ) (1 : R) * LaurentSeries.derivative R f).support ⊆ f.support :=
    fun i hi h ↦ hi (by rw [coeff_single_one_mul_derivative, h, smul_zero])
  have hx : ((of R).symm (single (1 : ℤ) (1 : R) • derivative R x)).support ⊆
      ((of R).symm x).support :=
    fun i hi h ↦ hi (by rw [coeff_single_one_smul_derivative, h, smul_zero])
  rw [of_symm_add, HahnSeries.coeff_add, coeff_single_one_smul_derivative, coeff_smul,
    coeff_smul_left f.isPWO_support hf, coeff_smul_right ((of R).symm x).isPWO_support hx,
    Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij hij ↦ ?_
  obtain ⟨-, -, hij⟩ := (Finset.mem_vaddAntidiagonal _ _).1 hij
  rw [coeff_single_one_mul_derivative, coeff_single_one_smul_derivative, ← hij, vadd_eq_add,
    add_zsmul, smul_assoc, smul_comm (f.coeff ij.1) ij.2]

/-- **The Leibniz rule** `D (f • x) = D f • x + f • D x` for a scalar Laurent series `f` and a
`V`-valued Laurent series `x`. -/
theorem derivative_smul (f : R⸨X⸩) (x : HahnModule ℤ R V) :
    derivative R (f • x) = LaurentSeries.derivative R f • x + f • derivative R x := by
  -- Multiply the Leibniz rule for `t D` by `t⁻¹`.
  have ht : single (-1 : ℤ) (1 : R) * single 1 1 = 1 := by
    rw [single_mul_single, neg_add_cancel, mul_one, single_zero_one]
  rw [← one_smul R⸨X⸩ (derivative R (f • x)), ← ht, mul_smul, single_one_smul_derivative_smul,
    smul_add, ← mul_smul, ← mul_assoc, ht, one_mul, smul_smul, mul_comm _ f, mul_smul,
    ← mul_smul _ _ (derivative R x), ht, one_smul]

variable (R) in
/-- The residue pairing `(x, y) ↦ Res Φ(x, D y) dt` of `V`-valued Laurent series attached to a
bilinear form `Φ` on `V`: the coefficient of `t⁻¹` in the coefficientwise extension of `Φ`
evaluated at `x` and `D y`. -/
def residuePairing (Φ : LinearMap.BilinForm R V) : LinearMap.BilinForm R (HahnModule ℤ R V) :=
  ((convolution ℤ Φ).compl₂ (derivative R)).compr₂ (coeff.linearMap (-1))

/-- The residue pairing evaluates as the coefficient of `t⁻¹` in `Φ(x, D y)`. -/
theorem residuePairing_apply (Φ : LinearMap.BilinForm R V) (x y : HahnModule ℤ R V) :
    residuePairing R Φ x y = (convolution ℤ Φ x (derivative R y)).coeff (-1) :=
  (rfl)

/-- The residue pairing on monomials: `Res Φ(v tᵐ, D (w tⁿ)) dt` is `n Φ(v, w)` when `m + n = 0`,
and zero otherwise. -/
@[simp]
theorem residuePairing_single_single (Φ : LinearMap.BilinForm R V) (m n : ℤ) (v w : V) :
    residuePairing R Φ (of R (single m v)) (of R (single n w)) =
      if m + n = 0 then n • Φ v w else 0 := by
  rw [residuePairing_apply, derivative_single, convolution_single_single, coeff_single,
    map_zsmul]
  split_ifs with h₁ h₂ h₂ <;> first | rfl | omega

end CommRing

end HahnModule
