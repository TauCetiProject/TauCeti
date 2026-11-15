/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Kronecker
public import TauCeti.RingTheory.MvPolynomial.RestrictSupport
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.RingTheory.Polynomial.DegreeLT
import TauCeti.Data.Finsupp.Weight

/-!
# The power substitution `F ↦ F(X, X ^ B)`

For `B : ℕ`, the *power substitution* `MvPolynomial.powerSubstitution B` sends a bivariate
polynomial `F(Z, W)` (variable `0` is `Z`, variable `1` is `W`) to the univariate polynomial
`F(X, X ^ B)`. It is the Kronecker substitution of `TauCeti.RingTheory.MvPolynomial.Kronecker`
for the weight `![1, B]`, which sends the exponent `μ` to `μ 0 + B * μ 1`. On exponents with
`μ 0 < B` this map is injective (uniqueness of quotient and remainder on division by `B`), so the
substitution is injective on polynomials of `Z`-degree below `B`.

## Main results

* `MvPolynomial.coeff_powerSubstitution`: for `F` of `Z`-degree below `B` and `μ 0 < B`, the
  coefficient of `X ^ (μ 0 + B * μ 1)` in `F(X, X ^ B)` is the coefficient of `Z ^ μ 0 W ^ μ 1`.
* `MvPolynomial.powerSubstitution_injOn`: the substitution is injective on polynomials of
  `Z`-degree below `B`, for every `B` (at `B = 0` this set is empty).
* `MvPolynomial.support_powerSubstitution_subset`,
  `MvPolynomial.natDegree_powerSubstitution_le`: the exponents of `F(X, X ^ B)` are among the
  weights `μ 0 + B * μ 1` of the exponents of `F`, so its degree is at most
  `degreeOf 0 F + B * degreeOf 1 F`.
* `MvPolynomial.powerSubstitution_map`: naturality under a ring map of the coefficients.
* `MvPolynomial.eval_powerSubstitution`: `F(X, X ^ B)` evaluated at `a` is `F(a, a ^ B)`.
* `MvPolynomial.powerSubstitution_mem_degreeLT_iff`: for `F` of `Z`-degree below `B`, the degree of
  `F(X, X ^ B)` is below `N` iff `F` is supported on the exponents of weight `μ 0 + B * μ 1 < N`.
* `MvPolynomial.powerSubstitutionEquiv`: for `0 < B`, the substitution is a linear equivalence from
  the polynomials of `Z`-degree below `B` (supported on the strip `{μ | μ 0 < B}`) onto `R[X]`.
* `MvPolynomial.powerSubstitutionDegreeLTEquiv`: for `0 < B`, it restricts to a linear equivalence
  from the polynomials supported on the weighted strip `{μ | μ 0 < B ∧ μ 0 + B * μ 1 < N}` onto
  `Polynomial.degreeLT R N`; in particular that space has rank `N`
  (`MvPolynomial.finrank_restrictSupport_weightedStrip`).

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53 (2004),
  Lemma 11.17, which uses the substitution `h(X, X ^ q)`.
* L. Pottmeyer, *Diophantine Approximation*, lecture notes (version of 17 January 2022), §3.3,
  proof of Theorem 3.3.7 and Exercise 3.5(a), the Kronecker substitution `xᵢ ↦ t ^ (d ^ (i - 1))`,
  injective on monomials of partial degrees below `d`.
-/

public section

noncomputable section

namespace MvPolynomial

open Finsupp

variable {R S : Type*}

section CommSemiring

variable [CommSemiring R] [CommSemiring S]

/-- The power substitution `Z ↦ X`, `W ↦ X ^ B` on bivariate polynomials, with variable `0 = Z`
and variable `1 = W`: the evaluation homomorphism `F ↦ F(X, X ^ B)`. -/
def powerSubstitution (B : ℕ) : MvPolynomial (Fin 2) R →ₐ[R] Polynomial R :=
  aeval ![Polynomial.X, Polynomial.X ^ B]

@[simp]
theorem powerSubstitution_X_zero (B : ℕ) :
    powerSubstitution (R := R) B (X 0) = Polynomial.X := by
  simp [powerSubstitution]

@[simp]
theorem powerSubstitution_X_one (B : ℕ) :
    powerSubstitution (R := R) B (X 1) = Polynomial.X ^ B := by
  simp [powerSubstitution]

/-- The power substitution is the Kronecker substitution `Xₛ ↦ X ^ eₛ` for the weight
`e = ![1, B]`. -/
theorem powerSubstitution_eq_aeval_X_pow (B : ℕ) :
    powerSubstitution (R := R) B = aeval fun s ↦ (Polynomial.X : Polynomial R) ^ ![1, B] s := by
  refine algHom_ext fun s ↦ ?_
  fin_cases s <;> simp [powerSubstitution]

/-- The power substitution sends the monomial `c Z ^ μ 0 W ^ μ 1` to `c X ^ (μ 0 + B * μ 1)`. -/
@[simp]
theorem powerSubstitution_monomial (B : ℕ) (μ : Fin 2 →₀ ℕ) (c : R) :
    powerSubstitution B (monomial μ c) = Polynomial.monomial (μ 0 + B * μ 1) c := by
  rw [powerSubstitution_eq_aeval_X_pow, aeval_X_pow_left_monomial, weight_vecCons_one]

/-- For `F` of `Z`-degree below `B` and an exponent `μ` with `μ 0 < B`, the coefficient of
`X ^ (μ 0 + B * μ 1)` in `F(X, X ^ B)` is the coefficient of `Z ^ μ 0 W ^ μ 1` in `F`. -/
theorem coeff_powerSubstitution {B : ℕ} {F : MvPolynomial (Fin 2) R} (hF : F.degreeOf 0 < B)
    {μ : Fin 2 →₀ ℕ} (hμ : μ 0 < B) :
    (powerSubstitution B F).coeff (μ 0 + B * μ 1) = F.coeff μ := by
  rw [powerSubstitution_eq_aeval_X_pow, ← weight_vecCons_one]
  exact coeff_aeval_X_pow_weight (injOn_weight_vecCons_one B)
    ((mem_restrictSupport_iff (R := R)).mp (mem_restrictSupport_of_degreeOf_lt hF)) hμ

/-- **The power substitution is injective below the `Z`-degree `B`.** Two bivariate polynomials
of `Z`-degree below `B` with the same image `F(X, X ^ B)` are equal. No positivity of `B` is
needed: for `B = 0` the set is empty. -/
theorem powerSubstitution_injOn (B : ℕ) :
    Set.InjOn (powerSubstitution (R := R) B) {F : MvPolynomial (Fin 2) R | F.degreeOf 0 < B} := by
  rw [powerSubstitution_eq_aeval_X_pow]
  exact (injOn_aeval_X_pow (injOn_weight_vecCons_one B)).mono fun _ ↦
    mem_restrictSupport_of_degreeOf_lt

/-- The power substitution preserves linear independence of a family of polynomials of
`Z`-degree below `B`. -/
theorem linearIndependent_powerSubstitution {ι : Type*} {B : ℕ} {φ : ι → MvPolynomial (Fin 2) R}
    (hφB : ∀ i, (φ i).degreeOf 0 < B) (hφ : LinearIndependent R φ) :
    LinearIndependent R fun i ↦ powerSubstitution B (φ i) := by
  rw [powerSubstitution_eq_aeval_X_pow]
  exact linearIndependent_aeval_X_pow (injOn_weight_vecCons_one B)
    (fun i ↦ (mem_restrictSupport_iff (R := R)).mp (mem_restrictSupport_of_degreeOf_lt (hφB i))) hφ

/-- The exponents of `F(X, X ^ B)` are among the weights `μ 0 + B * μ 1` of the exponents `μ`
of `F`. -/
theorem support_powerSubstitution_subset (B : ℕ) (F : MvPolynomial (Fin 2) R) :
    (powerSubstitution B F).support ⊆ F.support.image fun μ ↦ μ 0 + B * μ 1 := by
  classical
  intro N hN
  by_contra hNim
  apply Polynomial.mem_support_iff.mp hN
  conv_lhs => rw [F.as_sum]
  simp only [map_sum, powerSubstitution_monomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial_apply]
  exact Finset.sum_eq_zero fun μ hμ ↦ ite_eq_right fun h ↦ hNim (Finset.mem_image.mpr ⟨μ, hμ, h⟩)

/-- The degree of `F(X, X ^ B)` is at most `degreeOf 0 F + B * degreeOf 1 F`. -/
theorem natDegree_powerSubstitution_le (B : ℕ) (F : MvPolynomial (Fin 2) R) :
    (powerSubstitution B F).natDegree ≤ F.degreeOf 0 + B * F.degreeOf 1 := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN ↦ ?_
  refine Polynomial.notMem_support_iff.mp fun hmem ↦ ?_
  obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.mp (support_powerSubstitution_subset B F hmem)
  exact hN.not_ge (Nat.add_le_add (monomial_le_degreeOf 0 hμ)
    (Nat.mul_le_mul_left B (monomial_le_degreeOf 1 hμ)))

/-- The power substitution commutes with a ring map `f : R →+* S` applied to the coefficients. -/
@[simp]
theorem powerSubstitution_map (f : R →+* S) (B : ℕ) (F : MvPolynomial (Fin 2) R) :
    powerSubstitution B (map f F) = Polynomial.map f (powerSubstitution B F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial μ c => simp
  | add F G hF hG => simp [hF, hG, Polynomial.map_add]

/-- **Evaluation formula.** `F(X, X ^ B)` evaluated at `a` is `F(a, a ^ B)`. -/
@[simp]
theorem eval_powerSubstitution (B : ℕ) (a : R) (F : MvPolynomial (Fin 2) R) :
    (powerSubstitution B F).eval a = eval ![a, a ^ B] F := by
  induction F using MvPolynomial.induction_on' with
  | monomial μ c => simp [eval_monomial, Finsupp.prod_fintype, pow_add, pow_mul]
  | add F G hF hG => simp [hF, hG]

/-! ### Degree bounds and the weighted strip -/

/-- If every exponent `μ` of `F` has weight `μ 0 + B * μ 1` below `N`, then `F(X, X ^ B)` has
degree below `N`. -/
theorem powerSubstitution_mem_degreeLT {B N : ℕ} {F : MvPolynomial (Fin 2) R}
    (hF : F ∈ restrictSupport R {μ : Fin 2 →₀ ℕ | μ 0 + B * μ 1 < N}) :
    powerSubstitution B F ∈ Polynomial.degreeLT R N := by
  rw [Polynomial.mem_degreeLT, Polynomial.degree_lt_iff_coeff_zero]
  intro n hn
  refine Polynomial.notMem_support_iff.mp fun hmem ↦ ?_
  obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.mp (support_powerSubstitution_subset B F hmem)
  exact hn.not_gt (hF hμ)

/-- For `F` of `Z`-degree below `B`, `F(X, X ^ B)` has degree below `N` exactly when every exponent
`μ` of `F` has weight `μ 0 + B * μ 1` below `N`. -/
theorem powerSubstitution_mem_degreeLT_iff {B N : ℕ} {F : MvPolynomial (Fin 2) R}
    (hF : F.degreeOf 0 < B) :
    powerSubstitution B F ∈ Polynomial.degreeLT R N ↔
      F ∈ restrictSupport R {μ : Fin 2 →₀ ℕ | μ 0 + B * μ 1 < N} := by
  refine ⟨fun h ↦ (mem_restrictSupport_iff R).mpr fun μ hμ ↦ ?_, powerSubstitution_mem_degreeLT⟩
  have hμB : μ 0 < B := (degreeOf_lt_iff ((Nat.zero_le _).trans_lt hF)).mp hF μ hμ
  have hc : (powerSubstitution B F).coeff (μ 0 + B * μ 1) ≠ 0 := by
    rw [coeff_powerSubstitution hF hμB]
    exact mem_support_iff.mp hμ
  exact_mod_cast (Polynomial.le_degree_of_ne_zero hc).trans_lt (Polynomial.mem_degreeLT.mp h)

variable {B : ℕ}

/-- Division with remainder by `B` recovers an exponent `μ` with `μ 0 < B` from its weight
`μ 0 + B * μ 1`. -/
private theorem single_mod_add_single_div (hB : 0 < B) {μ : Fin 2 →₀ ℕ} (hμ : μ 0 < B) :
    single 0 ((μ 0 + B * μ 1) % B) + single 1 ((μ 0 + B * μ 1) / B) = μ := by
  refine Finsupp.ext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
  · simp [Nat.mod_eq_of_lt hμ]
  · simp [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hμ]

/-- **The power substitution as a linear equivalence.** For `0 < B`, `F ↦ F(X, X ^ B)` is an
`R`-linear equivalence from the polynomials supported on the strip `{μ | μ 0 < B}`, that is of
`Z`-degree below `B`, onto `R[X]`. On monomials it is the bijection `μ ↦ μ 0 + B * μ 1` of the strip
onto `ℕ`, whose inverse is division with remainder by `B`. See `powerSubstitutionEquiv_apply`. -/
def powerSubstitutionEquiv (hB : 0 < B) :
    restrictSupport R {μ : Fin 2 →₀ ℕ | μ 0 < B} ≃ₗ[R] Polynomial R :=
  (basisRestrictSupport R _).equiv (Polynomial.basisMonomials R)
    { toFun μ := (μ : Fin 2 →₀ ℕ) 0 + B * (μ : Fin 2 →₀ ℕ) 1
      invFun n := ⟨single 0 (n % B) + single 1 (n / B), by simpa using Nat.mod_lt n hB⟩
      left_inv μ := Subtype.ext (single_mod_add_single_div hB μ.2)
      right_inv n := by simpa using Nat.mod_add_div n B }

/-- `powerSubstitutionEquiv` is the power substitution. -/
@[simp]
theorem powerSubstitutionEquiv_apply (hB : 0 < B)
    (F : restrictSupport R {μ : Fin 2 →₀ ℕ | μ 0 < B}) :
    powerSubstitutionEquiv hB F = powerSubstitution B F := by
  suffices (powerSubstitutionEquiv hB).toLinearMap =
      (powerSubstitution B).toLinearMap ∘ₗ Submodule.subtype _ from LinearMap.congr_fun this F
  refine (basisRestrictSupport R _).ext fun μ ↦ ?_
  simp [powerSubstitutionEquiv, Polynomial.coe_basisMonomials]

/-- The coefficients of the bivariate preimage of `P` under `powerSubstitutionEquiv` are those of
`P`: the coefficient of `Z ^ μ 0 W ^ μ 1`, for `μ 0 < B`, is the coefficient of
`X ^ (μ 0 + B * μ 1)` in `P`. -/
theorem coeff_powerSubstitutionEquiv_symm (hB : 0 < B) (P : Polynomial R) {μ : Fin 2 →₀ ℕ}
    (hμ : μ 0 < B) :
    ((powerSubstitutionEquiv hB).symm P : MvPolynomial (Fin 2) R).coeff μ =
      P.coeff (μ 0 + B * μ 1) := by
  set F := (powerSubstitutionEquiv hB).symm P
  have hP : P = powerSubstitution B F := by
    rw [← powerSubstitutionEquiv_apply hB, LinearEquiv.apply_symm_apply]
  rw [hP, coeff_powerSubstitution (degreeOf_lt_of_mem_restrictSupport F.2 hB fun _ h ↦ h) hμ]

/-- **The weighted strip and `degreeLT`.** For `0 < B`, the power substitution `F ↦ F(X, X ^ B)` is
an `R`-linear equivalence from the polynomials supported on the weighted strip
`{μ | μ 0 < B ∧ μ 0 + B * μ 1 < N}` onto `Polynomial.degreeLT R N`. On monomials it is the
bijection `μ ↦ μ 0 + B * μ 1` of the strip onto `Fin N`. See
`coe_powerSubstitutionDegreeLTEquiv_apply`. -/
def powerSubstitutionDegreeLTEquiv (hB : 0 < B) (N : ℕ) :
    restrictSupport R {μ : Fin 2 →₀ ℕ | μ 0 < B ∧ μ 0 + B * μ 1 < N} ≃ₗ[R]
      Polynomial.degreeLT R N :=
  (basisRestrictSupport R _).equiv (Polynomial.degreeLT.basis R N)
    { toFun μ := ⟨(μ : Fin 2 →₀ ℕ) 0 + B * (μ : Fin 2 →₀ ℕ) 1, μ.2.2⟩
      invFun n := ⟨single 0 (n % B) + single 1 (n / B),
        by simpa [Nat.mod_add_div] using And.intro (Nat.mod_lt n hB) n.2⟩
      left_inv μ := Subtype.ext (single_mod_add_single_div hB μ.2.1)
      right_inv n := Fin.ext <| by simpa using Nat.mod_add_div n B }

/-- `powerSubstitutionDegreeLTEquiv` is the power substitution. -/
@[simp]
theorem coe_powerSubstitutionDegreeLTEquiv_apply (hB : 0 < B) (N : ℕ)
    (F : restrictSupport R {μ : Fin 2 →₀ ℕ | μ 0 < B ∧ μ 0 + B * μ 1 < N}) :
    (powerSubstitutionDegreeLTEquiv hB N F : Polynomial R) = powerSubstitution B F := by
  suffices (Polynomial.degreeLT R N).subtype ∘ₗ (powerSubstitutionDegreeLTEquiv hB N).toLinearMap =
      (powerSubstitution B).toLinearMap ∘ₗ Submodule.subtype _ from LinearMap.congr_fun this F
  refine (basisRestrictSupport R _).ext fun μ ↦ ?_
  simp [powerSubstitutionDegreeLTEquiv, Polynomial.X_pow_eq_monomial]

/-- The bivariate preimage of `P ∈ degreeLT R N` under `powerSubstitutionDegreeLTEquiv` is its
preimage under `powerSubstitutionEquiv`. -/
theorem coe_powerSubstitutionDegreeLTEquiv_symm_apply (hB : 0 < B) (N : ℕ)
    (P : Polynomial.degreeLT R N) :
    ((powerSubstitutionDegreeLTEquiv hB N).symm P : MvPolynomial (Fin 2) R) =
      ↑((powerSubstitutionEquiv (R := R) hB).symm ↑P) := by
  set F := (powerSubstitutionDegreeLTEquiv hB N).symm P
  set G := (powerSubstitutionEquiv hB).symm (P : Polynomial R)
  refine powerSubstitution_injOn B (degreeOf_lt_of_mem_restrictSupport F.2 hB fun _ h ↦ h.1)
    (degreeOf_lt_of_mem_restrictSupport G.2 hB fun _ h ↦ h) ?_
  rw [← coe_powerSubstitutionDegreeLTEquiv_apply hB N, ← powerSubstitutionEquiv_apply hB,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- For `0 < B`, the polynomials supported on the weighted strip
`{μ | μ 0 < B ∧ μ 0 + B * μ 1 < N}` form a module of rank `N`. -/
theorem finrank_restrictSupport_weightedStrip [StrongRankCondition R] (hB : 0 < B) (N : ℕ) :
    Module.finrank R (restrictSupport R {μ : Fin 2 →₀ ℕ | μ 0 < B ∧ μ 0 + B * μ 1 < N}) = N := by
  rw [(powerSubstitutionDegreeLTEquiv hB N).finrank_eq,
    Module.finrank_eq_card_basis (Polynomial.degreeLT.basis R N), Fintype.card_fin]

end CommSemiring

/-! The bound `B` on the `Z`-degree cannot be dropped: `Z ^ 2` and `W` both map to `X ^ 2`. -/

example : powerSubstitution (R := ℤ) 2 (X 0 ^ 2) = powerSubstitution 2 (X 1) := by
  simp

example : (X 0 ^ 2 : MvPolynomial (Fin 2) ℤ) ≠ X 1 := by
  intro h
  simpa [degreeOf_X] using congrArg (degreeOf 0) h

/-! For `B = 2`, the coefficient of `Z W` in the bivariate preimage of `X ^ 3 = X ^ (1 + 2 * 1)` is
`1`. -/

example : ((powerSubstitutionEquiv (R := ℤ) two_pos).symm (Polynomial.X ^ 3) :
    MvPolynomial (Fin 2) ℤ).coeff (single 0 1 + single 1 1) = 1 := by
  rw [coeff_powerSubstitutionEquiv_symm two_pos _ (by simp)]
  simp [Polynomial.coeff_X_pow]

end MvPolynomial
