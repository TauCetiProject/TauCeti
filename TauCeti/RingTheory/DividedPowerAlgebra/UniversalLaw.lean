/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DividedPowerAlgebra.Grading
public import TauCeti.RingTheory.PolynomialLaw.Homogeneous
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Data.Nat.Choose.Sum
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
* `DividedPowerAlgebra.coe_lid_rTensor_lcoeff_gamma_toFun_sum_X_tmul`: the coefficient of the
  monomial `∏ⱼ Tⱼ ^ kⱼ` in `γ_d(∑ⱼ Tⱼ ⊗ mⱼ)` is `∏ⱼ dp kⱼ mⱼ` when `∑ⱼ kⱼ = d`, and `0`
  otherwise.

## Implementation notes

The values of all the laws `γ_d` are packaged into the divided-power exponential
`exp(x) = ∑_d γ_d(x) X ^ d`, a power series with coefficients in `S ⊗[R] Γ_R(M)`, which is
defined on pure tensors by `exp(s ⊗ m) = ∑ₙ (s ^ n ⊗ dp R n m) X ^ n`. The Roby relations
`dp_add`, `dp_mul` and `dp_smul` say exactly that this formula is multiplicative in each of `s`
and `m`, and balanced, so that `exp` is a well-defined map from `S ⊗[R] M` to the multiplicative
monoid of power series. The law `γ_d` is the `X ^ d`-coefficient of `exp`, projected to the
degree-`d` piece through the direct-sum grading of `Γ_R(M)`.

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

section Exp

variable {S : Type*} [CommSemiring S] [Algebra R S]

variable (R) in
/-- The divided-power exponential `∑ₙ (s ^ n ⊗ dp R n m) X ^ n` of a pure tensor `s ⊗ m`. -/
private def expTmul (s : S) (m : M) : (S ⊗[R] DividedPowerAlgebra R M)⟦X⟧ :=
  PowerSeries.mk fun n ↦ (s ^ n) ⊗ₜ[R] dp R n m

private theorem coeff_expTmul (s : S) (m : M) (n : ℕ) :
    coeff n (expTmul R s m) = (s ^ n) ⊗ₜ[R] dp R n m :=
  coeff_mk _ _

private theorem expTmul_zero_right (s : S) : expTmul R s (0 : M) = 1 := by
  ext n
  rw [coeff_expTmul, coeff_one, dp_null]
  split_ifs with hn
  · rw [hn, pow_zero, Algebra.TensorProduct.one_def]
  · rw [tmul_zero]

private theorem expTmul_add_right (s : S) (m m' : M) :
    expTmul R s (m + m') = expTmul R s m * expTmul R s m' := by
  ext n
  rw [coeff_mul, coeff_expTmul, dp_add, tmul_sum]
  refine Finset.sum_congr rfl fun ⟨a, b⟩ hab ↦ ?_
  rw [coeff_expTmul, coeff_expTmul, Algebra.TensorProduct.tmul_mul_tmul, ← pow_add,
    Finset.mem_antidiagonal.mp hab]

private theorem expTmul_zero_left (m : M) : expTmul R (0 : S) m = 1 := by
  ext n
  rw [coeff_expTmul, coeff_one]
  rcases n with _ | n
  · simp [dp_zero, Algebra.TensorProduct.one_def]
  · simp

private theorem expTmul_add_left (s s' : S) (m : M) :
    expTmul R (s + s') m = expTmul R s m * expTmul R s' m := by
  ext n
  rw [coeff_mul, coeff_expTmul, (Commute.all s s').add_pow', sum_tmul]
  refine Finset.sum_congr rfl fun ⟨a, b⟩ hab ↦ ?_
  rw [coeff_expTmul, coeff_expTmul, Algebra.TensorProduct.tmul_mul_tmul, dp_mul,
    Finset.mem_antidiagonal.mp hab, smul_tmul]

private theorem expTmul_smul (r : R) (s : S) (m : M) :
    expTmul R (r • s) m = expTmul R s (r • m) := by
  ext n
  rw [coeff_expTmul, coeff_expTmul, smul_pow, dp_smul, smul_tmul]

/-- A shortcut instance: without it, synthesizing the additive structure on
`M →+ Additive (S ⊗[R] DividedPowerAlgebra R M)⟦X⟧` fails, because the search for a commutative
monoid structure on the power series ring tries instance paths that abort the search. -/
private local instance instAddCommMonoidAdditiveExpSeries :
    AddCommMonoid (Additive ((S ⊗[R] DividedPowerAlgebra R M)⟦X⟧)) :=
  Additive.addCommMonoid

variable (R M S) in
/-- The divided-power exponential of pure tensors, as a biadditive map to the multiplicative monoid
of power series. -/
private def expTmulHom : S →+ M →+ Additive ((S ⊗[R] DividedPowerAlgebra R M)⟦X⟧) where
  toFun s :=
    { toFun m := Additive.ofMul (expTmul R s m)
      map_zero' := by rw [expTmul_zero_right, ofMul_one]
      map_add' m m' := by rw [expTmul_add_right, ofMul_mul] }
  map_zero' := AddMonoidHom.ext fun m ↦ congrArg Additive.ofMul (expTmul_zero_left m)
  map_add' s s' := AddMonoidHom.ext fun m ↦ congrArg Additive.ofMul (expTmul_add_left s s' m)

private theorem expTmulHom_apply_apply (s : S) (m : M) :
    expTmulHom R M S s m = Additive.ofMul (expTmul R s m) :=
  rfl

variable (R M S) in
/-- The divided-power exponential, as an additive map to the multiplicative monoid of power
series. -/
private def expAddHom : S ⊗[R] M →+ Additive ((S ⊗[R] DividedPowerAlgebra R M)⟦X⟧) :=
  liftAddHom (expTmulHom R M S) fun r s m ↦ by
    rw [expTmulHom_apply_apply, expTmulHom_apply_apply, expTmul_smul]

/-- The divided-power exponential `exp(x) = ∑_d γ_d(x) X ^ d` of `x : S ⊗[R] M`. -/
private def exp (x : S ⊗[R] M) : (S ⊗[R] DividedPowerAlgebra R M)⟦X⟧ :=
  (expAddHom R M S x).toMul

private theorem exp_tmul (s : S) (m : M) : exp (s ⊗ₜ[R] m) = expTmul R s m := by
  rw [exp, expAddHom, liftAddHom_tmul, expTmulHom_apply_apply, toMul_ofMul]

private theorem exp_zero : exp (0 : S ⊗[R] M) = 1 := by
  rw [exp, map_zero, toMul_zero]

private theorem exp_add (x y : S ⊗[R] M) : exp (x + y) = exp x * exp y := by
  simp only [exp, map_add, toMul_add]

/-- The exponential is natural in the algebra `S`. -/
private theorem exp_rTensor {T : Type*} [CommSemiring T] [Algebra R T] (φ : S →ₐ[R] T)
    (x : S ⊗[R] M) :
    exp (φ.toLinearMap.rTensor M x) =
      PowerSeries.map (Algebra.TensorProduct.rTensor (DividedPowerAlgebra R M) φ).toRingHom
        (exp x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
      ext n
      rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, exp_tmul, exp_tmul, coeff_map,
        coeff_expTmul, coeff_expTmul]
      simp
  | add x y hx hy => rw [map_add, exp_add, exp_add, hx, hy, map_mul]

/-- Scalar multiplication by `s` rescales the exponential by `s ⊗ 1`. -/
private theorem exp_smul (s : S) (x : S ⊗[R] M) :
    exp (s • x) = rescale (s ⊗ₜ[R] (1 : DividedPowerAlgebra R M)) (exp x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s' m =>
      ext n
      rw [smul_tmul', exp_tmul, exp_tmul, coeff_rescale (R := S ⊗[R] DividedPowerAlgebra R M),
        coeff_expTmul, coeff_expTmul]
      simp [mul_pow]
  | add x y hx hy => rw [smul_add, exp_add, exp_add, hx, hy, map_mul]

/-- The exponential of a finite sum of pure tensors. -/
private theorem exp_sum_tmul {ι : Type*} (t : Finset ι) (s : ι → S) (m : ι → M) :
    exp (∑ j ∈ t, s j ⊗ₜ[R] m j) = ∏ j ∈ t, expTmul R (s j) (m j) := by
  classical
  induction t using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, exp_zero]
  | insert j t hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, exp_add, exp_tmul, ih]

end Exp

variable (R M) in
/-- The projection of `Γ_R(M)` onto its degree-`d` piece. -/
private def proj (d : ℕ) :
    DividedPowerAlgebra R M →ₗ[R] homogeneousSubmodule (R := R) (M := M) d :=
  DirectSum.component R ℕ _ d ∘ₗ
    (DirectSum.decomposeLinearEquiv (homogeneousSubmodule (R := R) (M := M))).toLinearMap

private theorem proj_apply (d : ℕ) (x : DividedPowerAlgebra R M) :
    proj R M d x = DirectSum.decompose (homogeneousSubmodule (R := R) (M := M)) x d :=
  rfl

/-- The value of the law `γ_d` on `x : S ⊗[R] M`: the `X ^ d`-coefficient of the exponential,
projected to the degree-`d` piece. -/
private def gammaFun (d : ℕ) {S : Type*} [CommSemiring S] [Algebra R S] (x : S ⊗[R] M) :
    S ⊗[R] homogeneousSubmodule (R := R) (M := M) d :=
  (proj R M d).lTensor S (coeff d (exp x))

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
  simp_rw [coeff_expTmul]
  rw [Algebra.TensorProduct.prod_tmul, LinearMap.lTensor_tmul, proj_apply]

/-- The value of `γ_d` on a pure tensor: `γ_d(s ⊗ m) = s ^ d ⊗ dp R d m`. -/
@[simp]
theorem gamma_toFun_tmul (d : ℕ) {S : Type*} [CommSemiring S] [Algebra R S] (s : S) (m : M) :
    (gamma R M d).toFun S (s ⊗ₜ[R] m) =
      (s ^ d) ⊗ₜ[R] ⟨dp R d m, dp_mem_homogeneousSubmodule d m⟩ := by
  rw [gamma_toFun, gammaFun, exp_tmul, coeff_expTmul, LinearMap.lTensor_tmul, proj_apply,
    decompose_dp, DirectSum.of_eq_same]

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
    DirectSum.decompose_of_mem_same _ <| h ▸
      SetLike.prod_mem_graded _ _ _ fun j _ ↦ dp_mem_homogeneousSubmodule (k j) (m j)
  rw [gamma_toFun_sum_tmul]
  simp +contextual [hX, MvPolynomial.coeff_monomial, ite_smul,
    apply_ite (Subtype.val : homogeneousSubmodule (R := R) (M := M) d → _), Finset.sum_ite_eq',
    Finset.mem_finsuppAntidiag, hdec]

end DividedPowerAlgebra
