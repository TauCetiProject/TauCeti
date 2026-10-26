/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DividedPowerAlgebra.Exp
public import TauCeti.RingTheory.DividedPowerAlgebra.Grading
public import TauCeti.RingTheory.PolynomialLaw.Homogeneous
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import TauCeti.RingTheory.TensorProduct.Basic

/-!
# The universal homogeneous polynomial law

For a module `M` over a commutative semiring `R` and `d : ℕ`, this file constructs the
universal homogeneous polynomial law `γ_d : M → Γ^d_R(M)` of degree `d`, with values in the
degree-`d` homogeneous piece of the divided power algebra. After scalar extension to a
commutative `R`-algebra `S` it is given by
`γ_d(∑ⱼ sⱼ ⊗ mⱼ) = ∑_{∑ⱼ nⱼ = d} (∏ⱼ sⱼ ^ nⱼ) ⊗ ∏ⱼ dp nⱼ mⱼ`,
so that its ground value is `γ_d(m) = dp R d m`, and over a polynomial ring the coefficient of
`∏ⱼ Tⱼ ^ nⱼ` in `γ_d(∑ⱼ Tⱼ ⊗ mⱼ)` is `∏ⱼ dp nⱼ mⱼ` when `∑ⱼ nⱼ = d`, and zero otherwise. No
factorial is inverted: over `ℤ` the coefficient of `U V` in `γ_2(U ⊗ x + V ⊗ y)` is
`dp 1 x * dp 1 y`, with no factor `2`.

Roby's representability theorem identifies the degree-`d` homogeneous laws `M → N` with the linear
maps `Γ^d_R(M) → N`, by composition with `γ_d`.

## Main declarations

* `DividedPowerAlgebra.gamma R M d`: the universal homogeneous polynomial law of degree `d`.
* `DividedPowerAlgebra.isHomogeneousOfDegree_gamma`: it is homogeneous of degree `d`.
* `DividedPowerAlgebra.gamma_toFun_tmul`: `γ_d(s ⊗ m) = s ^ d ⊗ dp R d m`.
* `DividedPowerAlgebra.gamma_toFun_sum_tmul`: the formula for `γ_d` on a finite sum of pure
  tensors, after scalar extension to an algebra in any universe.
* `DividedPowerAlgebra.ground_gamma_apply`: the ground value of `γ_d` at `m` is `dp R d m`.
* `DividedPowerAlgebra.gamma_comp_toPolynomialLaw`: naturality in the source module.
* `DividedPowerAlgebra.coe_lid_rTensor_lcoeff_gamma_toFun_sum_X_tmul`: the coefficient of the
  monomial `∏ⱼ Tⱼ ^ kⱼ` in `γ_d(∑ⱼ Tⱼ ⊗ mⱼ)` is `∏ⱼ dp kⱼ mⱼ` when `∑ⱼ kⱼ = d`, and `0`
  otherwise.

## Implementation notes

The values of all the laws `γ_d` are packaged into the divided-power exponential
`DividedPowerAlgebra.exp`, `exp(x) = ∑_d γ_d(x) X ^ d`, a power series with coefficients in
`S ⊗[R] Γ_R(M)`, which is defined on pure tensors by `exp(s ⊗ m) = ∑ₙ (s ^ n ⊗ dp R n m) X ^ n`.
The law `γ_d` is the `X ^ d`-coefficient of `exp`, projected to the degree-`d` piece through the
direct-sum grading of `Γ_R(M)`.

## References

* [N. Roby, *Lois polynômes et lois formelles en théorie des modules* (1963),
  Proposition IV.1 and Théorème IV.1][Roby-1963]
* The ambient `DividedPowerAlgebra` and the `PolynomialLaw`s are the Mathlib formalizations by
  Antoine Chambert-Loir and María Inés de Frutos-Fernández.
-/

public section

noncomputable section

universe u

open TensorProduct PowerSeries

namespace DividedPowerAlgebra

variable {R : Type u} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]

/-- The exponential of a finite sum of pure tensors. -/
private theorem exp_sum_tmul {S : Type*} [CommSemiring S] [Algebra R S] {ι : Type*}
    (t : Finset ι) (s : ι → S) (m : ι → M) :
    exp (∑ j ∈ t, s j ⊗ₜ[R] m j) = ∏ j ∈ t, exp (s j ⊗ₜ[R] m j) := by
  classical
  induction t using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, exp_zero]
  | insert j t hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, exp_add, ih]

/-- The value of the law `γ_d` on `x : S ⊗[R] M`: the `X ^ d`-coefficient of the exponential,
projected to the degree-`d` piece. -/
private def gammaFun (d : ℕ) {S : Type*} [CommSemiring S] [Algebra R S] (x : S ⊗[R] M) :
    S ⊗[R] homogeneousSubmodule (R := R) (M := M) d :=
  (homogeneousProj R M d).lTensor S (coeff d (exp x))

private theorem gammaFun_rTensor (d : ℕ) {S T : Type*} [CommSemiring S] [Algebra R S]
    [CommSemiring T] [Algebra R T] (φ : S →ₐ[R] T) (x : S ⊗[R] M) :
    φ.toLinearMap.rTensor _ (gammaFun d x) = gammaFun d (φ.toLinearMap.rTensor M x) := by
  rw [gammaFun, gammaFun, exp_rTensor, coeff_map]
  generalize coeff d (exp x) = c
  induction c using TensorProduct.inductionOn with
  | tmul s y => simp
  | add y z hy hz => simp only [map_add, hy, hz]

variable (R M) in
/-- The universal homogeneous polynomial law `γ_d : M → Γ^d_R(M)` of degree `d`. After scalar
extension to a commutative `R`-algebra `S` it sends `∑ⱼ sⱼ ⊗ mⱼ` to
`∑_{∑ⱼ nⱼ = d} (∏ⱼ sⱼ ^ nⱼ) ⊗ ∏ⱼ dp R nⱼ mⱼ` (see `gamma_toFun_sum_tmul`), and its ground value is
`m ↦ dp R d m` (see `ground_gamma_apply`). -/
def gamma (d : ℕ) : M →ₚₗ[R] homogeneousSubmodule (R := R) (M := M) d where
  toFun' _ _ _ := gammaFun d
  isCompat' φ := funext fun x ↦ gammaFun_rTensor d φ x

private theorem gamma_toFun (d : ℕ) (S : Type*) [CommSemiring S] [Algebra R S]
    (x : S ⊗[R] M) : (gamma R M d).toFun S x = gammaFun d x := by
  obtain ⟨n, ψ, p, rfl⟩ := PolynomialLaw.exists_lift x
  rw [← PolynomialLaw.isCompat_apply, ← PolynomialLaw.toFun'_eq_toFun]
  exact gammaFun_rTensor d ψ p

/-- The universal law `γ_d` is homogeneous of degree `d`. -/
theorem isHomogeneousOfDegree_gamma (d : ℕ) : (gamma R M d).IsHomogeneousOfDegree d :=
  PolynomialLaw.isHomogeneousOfDegree_iff.mpr fun S _ _ s x ↦ by
    rw [PolynomialLaw.toFun'_eq_toFun, gamma_toFun, gamma_toFun]
    rw [gammaFun, gammaFun, exp_smul, coeff_rescale (R := S ⊗[R] DividedPowerAlgebra R M),
      LinearMap.smul_lTensor]
    congr 1
    simpa using (Algebra.smul_def (s ^ d) (coeff d (exp x))).symm

/-- The value of `γ_d` on a finite sum of pure tensors:
`γ_d(∑ⱼ sⱼ ⊗ mⱼ) = ∑_{∑ⱼ nⱼ = d} (∏ⱼ sⱼ ^ nⱼ) ⊗ ∏ⱼ dp R nⱼ mⱼ`. Each product
`∏ⱼ dp R nⱼ mⱼ` lies in the degree-`d` piece, where it is its own degree-`d` component. -/
theorem gamma_toFun_sum_tmul (d : ℕ) {S : Type*} [CommSemiring S] [Algebra R S] {ι : Type*}
    [DecidableEq ι] (t : Finset ι) (s : ι → S) (m : ι → M) :
    (gamma R M d).toFun S (∑ j ∈ t, s j ⊗ₜ[R] m j) =
      ∑ l ∈ t.finsuppAntidiag d, (∏ j ∈ t, s j ^ l j) ⊗ₜ[R]
        DirectSum.decompose (homogeneousSubmodule (R := R) (M := M))
          (∏ j ∈ t, dp R (l j) (m j)) d := by
  rw [gamma_toFun, gammaFun, exp_sum_tmul, coeff_prod (R := S ⊗[R] DividedPowerAlgebra R M),
    map_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  simp_rw [coeff_exp_tmul]
  rw [Algebra.TensorProduct.prod_tmul, LinearMap.lTensor_tmul, homogeneousProj_apply]

/-- The value of `γ_d` on a pure tensor: `γ_d(s ⊗ m) = s ^ d ⊗ dp R d m`. -/
@[simp]
theorem gamma_toFun_tmul (d : ℕ) {S : Type*} [CommSemiring S] [Algebra R S] (s : S) (m : M) :
    (gamma R M d).toFun S (s ⊗ₜ[R] m) =
      (s ^ d) ⊗ₜ[R] ⟨dp R d m, dp_mem_homogeneousSubmodule d m⟩ := by
  rw [gamma_toFun, gammaFun, coeff_exp_tmul, LinearMap.lTensor_tmul,
    homogeneousProj_apply, decompose_dp, DirectSum.of_eq_same]

/-- The ground value of `γ_d` at `m` is `dp R d m`. -/
@[simp]
theorem ground_gamma_apply (d : ℕ) (m : M) :
    (gamma R M d).ground m = ⟨dp R d m, dp_mem_homogeneousSubmodule d m⟩ := by
  rw [PolynomialLaw.ground_apply, PolynomialLaw.toFun'_eq_toFun, gamma_toFun_tmul, one_pow,
    TensorProduct.lid_tmul, one_smul]

open MvPolynomial in
/-- The coefficient of the monomial `∏ⱼ Tⱼ ^ kⱼ` in `γ_d(∑ⱼ Tⱼ ⊗ mⱼ)`, computed over the
polynomial ring `R[Tⱼ]`, is `∏ⱼ dp R kⱼ mⱼ` when `∑ⱼ kⱼ = d`, and `0` otherwise. -/
theorem coe_lid_rTensor_lcoeff_gamma_toFun_sum_X_tmul (d : ℕ) {ι : Type*} [Fintype ι]
    (m : ι → M) (k : ι →₀ ℕ) :
    (TensorProduct.lid R (homogeneousSubmodule (R := R) (M := M) d) ((lcoeff R k).rTensor _
      ((gamma R M d).toFun (MvPolynomial ι R) (∑ j, MvPolynomial.X j ⊗ₜ[R] m j))) :
        DividedPowerAlgebra R M) =
      if ∑ j, k j = d then ∏ j, dp R (k j) (m j) else 0 := by
  classical
  have hX (l : ι →₀ ℕ) : ∏ j, (MvPolynomial.X j : MvPolynomial ι R) ^ l j = monomial l 1 := by
    rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ fun _ ↦ pow_zero _]
  have hdec (h : ∑ j, k j = d) : (DirectSum.decompose (homogeneousSubmodule (R := R) (M := M))
      (∏ j, dp R (k j) (m j)) d : DividedPowerAlgebra R M) = ∏ j, dp R (k j) (m j) :=
    DirectSum.decompose_of_mem_same _ <| prod_dp_mem_homogeneousSubmodule_of_sum_eq m k h
  rw [gamma_toFun_sum_tmul]
  simp +contextual [hX, MvPolynomial.coeff_monomial, ite_smul,
    apply_ite (Subtype.val : homogeneousSubmodule (R := R) (M := M) d → _), Finset.sum_ite_eq',
    Finset.mem_finsuppAntidiag, hdec]

/-- The universal homogeneous law is natural in its source module. -/
theorem gamma_comp_toPolynomialLaw {N : Type*} [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) (d : ℕ) :
    (gamma R N d).comp f.toPolynomialLaw =
      (mapHomogeneousSubmodule f d).toPolynomialLaw.comp (gamma R M d) := by
  ext S _ _ x
  simp only [PolynomialLaw.comp_toFun', Function.comp_apply, LinearMap.toPolynomialLaw_toFun']
  rw [PolynomialLaw.toFun'_eq_toFun, PolynomialLaw.toFun'_eq_toFun]
  -- The law is not additive, so expand a whole tensor as a finite sum before applying its formula.
  obtain ⟨n, s, m, rfl⟩ := TensorProduct.exists_sum_tmul_eq x
  simp only [map_sum, LinearMap.baseChange_tmul]
  rw [gamma_toFun_sum_tmul, gamma_toFun_sum_tmul, map_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [LinearMap.baseChange_tmul]
  congr 1
  apply Subtype.ext
  have hdeg : ∑ j, k j = d := (Finset.mem_finsuppAntidiag.mp hk).1
  have hM : ∏ j, dp R (k j) (m j) ∈ homogeneousSubmodule (R := R) (M := M) d :=
    prod_dp_mem_homogeneousSubmodule_of_sum_eq m k hdeg
  have hN : ∏ j, dp R (k j) (f (m j)) ∈ homogeneousSubmodule (R := R) (M := N) d :=
    prod_dp_mem_homogeneousSubmodule_of_sum_eq (fun j ↦ f (m j)) k hdeg
  simp only [coe_mapHomogeneousSubmodule_apply, DirectSum.decompose_of_mem_same _ hM,
    DirectSum.decompose_of_mem_same _ hN, map_prod, map_apply_dp]

end DividedPowerAlgebra
