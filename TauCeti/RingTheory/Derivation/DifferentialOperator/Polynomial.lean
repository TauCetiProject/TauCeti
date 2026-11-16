/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.PolynomialAlgebra
public import TauCeti.RingTheory.Derivation.DifferentialOperator.PrincipalParts

/-!
# Differential operators, Hasse derivatives, and principal parts of `R[X]`

This file specializes Grothendieck's differential operators and modules of principal parts to a
univariate polynomial algebra `R[X]` over an arbitrary commutative ring `R`, without any
characteristic zero hypothesis.

1. **Ordinary and Hasse derivatives**: `Polynomial.derivative` has differential order `1` (and not
   `0` when `Nontrivial R`), with `[d/dX, X] = 1`. More generally, for every `k : ℕ`, the `k`-th
   Hasse derivative `Polynomial.hasseDeriv k : R[X] →ₗ[R] R[X]` satisfies
   `[hasseDeriv (k + 1), X] = hasseDeriv k`, lies in
   `differentialOperators R R[X] R[X] R[X] k` over *any* commutative ring `R`, and does not lie in
   `differentialOperators R R[X] R[X] R[X] j` for `j < k` whenever `Nontrivial R`.
2. **Truncated Taylor realization of `PrincipalParts R R[X] R[X] m`**: composing
   `polyEquivTensor' R R[X]` with `Polynomial.taylorEquiv X` identifies the truncated diagonal
   quotient `(R[X] ⊗[R] R[X]) ⧸ (KaehlerDifferential.ideal R R[X]) ^ (m + 1)` as an `R[X]`-algebra
   with `R[X][X] ⧸ Ideal.span {X ^ (m + 1)}`. Consequently, `PrincipalParts R R[X] R[X] m` is
   `R[X]`-linearly isomorphic to `R[X][X] ⧸ Ideal.span {X ^ (m + 1)}`, carrying the universal
   `m`-jet `jet m f` to the truncated Hasse-Taylor expansion
   `∑ k ∈ range (m + 1), hasseDeriv k f • mk (X ^ k)`.

## Main definitions

* `TauCeti.polynomialTensorTaylorEquiv`: the `R[X]`-algebra equivalence
  `R[X] ⊗[R] R[X] ≃ₐ[R[X]] R[X][X]` sending `p ⊗ₜ f` to `p • taylor X (f.map C)` and
  `1 ⊗ₜ X - X ⊗ₜ 1` to `X`.
* `TauCeti.polynomialPrincipalPartsAlgEquiv`: the `R[X]`-algebra equivalence
  `((R[X] ⊗[R] R[X]) ⧸ (KaehlerDifferential.ideal R R[X]) ^ (m + 1)) ≃ₐ[R[X]]`
  `(R[X][X] ⧸ Ideal.span {X ^ (m + 1)})`.
* `TauCeti.PrincipalParts.polynomialSelfEquiv`: the `R[X]`-linear equivalence
  `PrincipalParts R R[X] R[X] m ≃ₗ[R[X]] R[X][X] ⧸ Ideal.span {X ^ (m + 1)}`.

## Main results

* `TauCeti.smulCommutator_X_derivative`, `TauCeti.derivative_mem_differentialOperators_one`, and
  `TauCeti.derivative_notMem_differentialOperators_zero`.
* `TauCeti.smulCommutator_X_hasseDeriv_succ`, `TauCeti.smulCommutator_X_pow_hasseDeriv`,
  `TauCeti.hasseDeriv_mem_differentialOperators`, and
  `TauCeti.hasseDeriv_notMem_differentialOperators_of_lt`.
* `TauCeti.PrincipalParts.polynomialSelfEquiv_jet`: the universal `m`-jet of `f : R[X]` maps to
  `∑ k ∈ Finset.range (m + 1), hasseDeriv k f • Ideal.Quotient.mk _ (X ^ k)`.

## References

* A. Grothendieck, *Éléments de géométrie algébrique IV*, Quatrième partie, §16.8 and §16.11.
-/

public section

noncomputable section

open Finset Polynomial
open scoped TensorProduct

namespace TauCeti

/-! ### Ordinary and Hasse derivatives on `R[X]` -/

section Derivatives

variable {R : Type*} [CommRing R]

/-- On `R[X]`, the commutator `[d/dX, X]` is the identity operator. -/
@[simp]
theorem smulCommutator_X_derivative :
    smulCommutator R (X : R[X]) (derivative : R[X] →ₗ[R] R[X]) = LinearMap.id := by
  apply LinearMap.ext
  intro f
  rw [smulCommutator_apply_apply, LinearMap.id_apply, smul_eq_mul, smul_eq_mul, derivative_mul,
    derivative_X, one_mul, add_sub_cancel_right]

/-- `Polynomial.derivative` has differential order at most `1` on `R[X]`. -/
theorem derivative_mem_differentialOperators_one :
    (derivative : R[X] →ₗ[R] R[X]) ∈ differentialOperators R R[X] R[X] R[X] 1 := by
  have h : ((derivative' : Derivation R R[X] R[X]) : R[X] →ₗ[R] R[X]) = derivative :=
    LinearMap.ext derivative'_apply
  exact h ▸ (derivative' (R := R)).mem_differentialOperators_one

/-- Over a nontrivial ring `R`, `Polynomial.derivative` does not have differential order `0`. -/
theorem derivative_notMem_differentialOperators_zero [Nontrivial R] :
    (derivative : R[X] →ₗ[R] R[X]) ∉ differentialOperators R R[X] R[X] R[X] 0 := by
  intro h0
  have hX := congr($(smulCommutator_eq_zero_of_mem_differentialOperators_zero h0 X) 1)
  rw [smulCommutator_X_derivative, LinearMap.id_apply, LinearMap.zero_apply] at hX
  exact one_ne_zero hX

/-- Commutator of the `(k + 1)`-th Hasse derivative with multiplication by `g : R[X]`:
`[hasseDeriv (k + 1), g] = ∑ ij ∈ (antidiagonal (k + 1)).erase (0, k + 1),`
`hasseDeriv ij.1 g • hasseDeriv ij.2`. -/
theorem smulCommutator_hasseDeriv_succ (k : ℕ) (g : R[X]) :
    smulCommutator R g (hasseDeriv (k + 1) : R[X] →ₗ[R] R[X]) =
      ∑ ij ∈ (antidiagonal (k + 1)).erase (0, k + 1),
        hasseDeriv ij.1 g • (hasseDeriv ij.2 : R[X] →ₗ[R] R[X]) := by
  apply LinearMap.ext
  intro f
  have hmem : (0, k + 1) ∈ antidiagonal (k + 1) := by simp
  rw [smulCommutator_apply_apply, smul_eq_mul, smul_eq_mul, hasseDeriv_mul,
    ← add_sum_erase _ _ hmem, hasseDeriv_zero, LinearMap.id_apply, add_sub_cancel_left,
    LinearMap.sum_apply]
  rfl

/-- Commutator of Hasse derivatives with `X`: `[hasseDeriv (k + 1), X] = hasseDeriv k`. -/
@[simp]
theorem smulCommutator_X_hasseDeriv_succ (k : ℕ) :
    smulCommutator R (X : R[X]) (hasseDeriv (k + 1) : R[X] →ₗ[R] R[X]) = hasseDeriv k := by
  rw [smulCommutator_hasseDeriv_succ, sum_eq_single (1, k)]
  · simp [derivative_X]
  · rintro ⟨i, j⟩ hij hne
    rw [mem_erase, mem_antidiagonal] at hij
    dsimp only at hij
    have hi0 : i ≠ 0 := fun h0 ↦ hij.1 (Prod.ext h0 (by omega))
    have hi1 : i ≠ 1 := fun h1 ↦ hne (Prod.ext h1 (by omega))
    simp [hasseDeriv_X i (by omega)]
  · intro hmem
    refine (hmem (mem_erase.2 ⟨?_, mem_antidiagonal.2 (Nat.add_comm 1 k)⟩)).elim
    simp

/-- Iterated commutators of Hasse derivatives with `X`:
`(smulCommutator R X ^ j) (hasseDeriv (k + j)) = hasseDeriv k`. -/
theorem smulCommutator_X_pow_hasseDeriv_add (k j : ℕ) :
    (smulCommutator R (X : R[X]) ^ j) (hasseDeriv (k + j) : R[X] →ₗ[R] R[X]) = hasseDeriv k := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, mul_apply_eq_comp, ← add_assoc, smulCommutator_X_hasseDeriv_succ, ih]

/-- The top `k`-fold commutator of `hasseDeriv k` with `X` is the identity operator. -/
@[simp]
theorem smulCommutator_X_pow_hasseDeriv (k : ℕ) :
    (smulCommutator R (X : R[X]) ^ k) (hasseDeriv k : R[X] →ₗ[R] R[X]) = LinearMap.id := by
  simpa using smulCommutator_X_pow_hasseDeriv_add (R := R) 0 k

/-- Over any commutative ring `R`, the `k`-th Hasse derivative on `R[X]` is a differential operator
of order at most `k`. -/
theorem hasseDeriv_mem_differentialOperators (k : ℕ) :
    (hasseDeriv k : R[X] →ₗ[R] R[X]) ∈ differentialOperators R R[X] R[X] R[X] k := by
  refine Nat.strongRecOn k fun n ih ↦ ?_
  rcases n with _ | n
  · rw [hasseDeriv_zero]
    exact LinearMap.restrictScalars_mem_differentialOperators_zero
      (LinearMap.id : R[X] →ₗ[R[X]] R[X])
  · rw [mem_differentialOperators_succ_iff]
    intro g
    rw [smulCommutator_hasseDeriv_succ]
    refine sum_mem fun ij hij ↦ smul_mem_differentialOperators _ ?_
    rw [mem_erase, mem_antidiagonal] at hij
    have hi0 : ij.1 ≠ 0 := fun h0 ↦ hij.1 (Prod.ext h0 (by omega))
    have hjk : ij.2 ≤ n := by omega
    exact differentialOperators_mono hjk (ih ij.2 (by omega))

/-- Over a nontrivial commutative ring `R`, `hasseDeriv k` does not have differential order `≤ j`
for any `j < k`. -/
theorem hasseDeriv_notMem_differentialOperators_of_lt [Nontrivial R] {j k : ℕ} (h : j < k) :
    (hasseDeriv k : R[X] →ₗ[R] R[X]) ∉ differentialOperators R R[X] R[X] R[X] j := by
  intro hj
  have hzero := smulCommutator_pow_eq_zero hj h (X : R[X])
  rw [smulCommutator_X_pow_hasseDeriv] at hzero
  have h1 := congr($hzero (1 : R[X]))
  simp at h1

end Derivatives

/-! ### Truncated Taylor realization of `PrincipalParts R R[X] R[X] m` -/

section TaylorPrincipalParts

variable (R : Type*) [CommRing R]

/-- The `R[X]`-algebra isomorphism `R[X] ⊗[R] R[X] ≃ₐ[R[X]] R[X][X]` obtained by composing
`(polyEquivTensor' R R[X]).symm` with `taylorEquiv X`: on pure tensors `p ⊗ₜ f` it produces
`p • taylor X (f.map C)` (i.e. `C p * f(X + T)` in the outer indeterminate `T`), sending the
diagonal generator `1 ⊗ₜ X - X ⊗ₜ 1` to the outer indeterminate `X`. -/
def polynomialTensorTaylorEquiv : R[X] ⊗[R] R[X] ≃ₐ[R[X]] R[X][X] :=
  (polyEquivTensor' R R[X]).symm.trans (taylorEquiv (X : R[X]))

@[simp]
theorem polynomialTensorTaylorEquiv_tmul (p f : R[X]) :
    polynomialTensorTaylorEquiv R (p ⊗ₜ[R] f) = p • taylor (X : R[X]) (f.map C) := by
  simp [polynomialTensorTaylorEquiv, polyEquivTensor_symm_apply_tmul_eq_smul,
    Polynomial.algebraMap_eq]
  rfl

@[simp]
theorem polynomialTensorTaylorEquiv_diag_X :
    polynomialTensorTaylorEquiv R ((1 : R[X]) ⊗ₜ[R] X - X ⊗ₜ[R] (1 : R[X])) = X := by
  rw [map_sub, polynomialTensorTaylorEquiv_tmul, polynomialTensorTaylorEquiv_tmul]
  simp [Algebra.smul_def]

/-- Evaluating the constant term (`T = 0`) of `polynomialTensorTaylorEquiv R z` recovers the
diagonal multiplication `Algebra.TensorProduct.lmul' R z`. -/
theorem coeff_zero_polynomialTensorTaylorEquiv (z : R[X] ⊗[R] R[X]) :
    (polynomialTensorTaylorEquiv R z).coeff 0 = Algebra.TensorProduct.lmul' R z := by
  induction z using TensorProduct.inductionOn with
  | tmul p f =>
    simp [polynomialTensorTaylorEquiv_tmul, smul_eq_mul, eval_map, eval₂_C_X]
  | add x y hx hy =>
    rw [map_add, coeff_add, map_add, hx, hy]

/-- `polynomialTensorTaylorEquiv` carries the Kähler diagonal ideal of `R[X] / R` onto the principal
ideal `(X)` of `R[X][X]`. -/
theorem map_kaehlerIdeal_polynomialTensorTaylorEquiv :
    (KaehlerDifferential.ideal R R[X]).map (polynomialTensorTaylorEquiv R :
      R[X] ⊗[R] R[X] →+* R[X][X]) = Ideal.span {(X : R[X][X])} := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro z hz
    rw [Ideal.mem_comap, Ideal.mem_span_singleton, X_dvd_iff, RingHom.coe_coe,
      coeff_zero_polynomialTensorTaylorEquiv]
    exact RingHom.mem_ker.1 hz
  · rw [Ideal.span_singleton_le_iff_mem, ← polynomialTensorTaylorEquiv_diag_X R]
    exact Ideal.mem_map_of_mem _ (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R X)

theorem map_kaehlerIdeal_pow_polynomialTensorTaylorEquiv (m : ℕ) :
    ((KaehlerDifferential.ideal R R[X]) ^ (m + 1)).map (polynomialTensorTaylorEquiv R :
      R[X] ⊗[R] R[X] →+* R[X][X]) = Ideal.span {(X : R[X][X]) ^ (m + 1)} := by
  rw [Ideal.map_pow, map_kaehlerIdeal_polynomialTensorTaylorEquiv, Ideal.span_singleton_pow]

/-- The `R[X]`-algebra isomorphism identifying the `(m + 1)`-st infinitesimal neighborhood of the
diagonal `(R[X] ⊗[R] R[X]) ⧸ (KaehlerDifferential.ideal R R[X]) ^ (m + 1)` with the truncated
polynomial ring `R[X][X] ⧸ Ideal.span {X ^ (m + 1)}`. -/
def polynomialPrincipalPartsAlgEquiv (m : ℕ) :
    ((R[X] ⊗[R] R[X]) ⧸ (KaehlerDifferential.ideal R R[X]) ^ (m + 1)) ≃ₐ[R[X]]
      (R[X][X] ⧸ Ideal.span {(X : R[X][X]) ^ (m + 1)}) :=
  Ideal.quotientEquivAlg ((KaehlerDifferential.ideal R R[X]) ^ (m + 1))
    (Ideal.span {(X : R[X][X]) ^ (m + 1)}) (polynomialTensorTaylorEquiv R)
    (map_kaehlerIdeal_pow_polynomialTensorTaylorEquiv R m).symm

@[simp]
theorem polynomialPrincipalPartsAlgEquiv_mk (m : ℕ) (z : R[X] ⊗[R] R[X]) :
    polynomialPrincipalPartsAlgEquiv R m (Ideal.Quotient.mk _ z) =
      Ideal.Quotient.mk _ (polynomialTensorTaylorEquiv R z) :=
  Ideal.quotientEquivAlg_mk _ _ _ z

namespace PrincipalParts

/-- Over any commutative ring `R`, `PrincipalParts R R[X] R[X] m` is `R[X]`-linearly isomorphic to
the truncated Taylor polynomial quotient `R[X][X] ⧸ Ideal.span {X ^ (m + 1)}`. -/
def polynomialSelfEquiv (m : ℕ) :
    PrincipalParts R R[X] R[X] m ≃ₗ[R[X]] R[X][X] ⧸ Ideal.span {(X : R[X][X]) ^ (m + 1)} :=
  selfEquiv R R[X] m ≪≫ₗ (polynomialPrincipalPartsAlgEquiv R m).toLinearEquiv

@[simp]
theorem polynomialSelfEquiv_mkQ (m : ℕ) (z : R[X] ⊗[R] R[X]) :
    polynomialSelfEquiv R m (mkQ R R[X] R[X] m z) =
      Ideal.Quotient.mk _ (polynomialTensorTaylorEquiv R z) := by
  simp [polynomialSelfEquiv]

@[simp]
theorem polynomialSelfEquiv_diag_X (m : ℕ) :
    polynomialSelfEquiv R m (jet R R[X] R[X] m X - (X : R[X]) • jet R R[X] R[X] m 1) =
      Ideal.Quotient.mk (Ideal.span {(X : R[X][X]) ^ (m + 1)}) (X : R[X][X]) := by
  rw [jet_apply, ← mkQ_tmul, ← map_sub, polynomialSelfEquiv_mkQ,
    polynomialTensorTaylorEquiv_diag_X]

/-- Under `polynomialSelfEquiv R m`, the universal `m`-jet of `f : R[X]` is the truncated
Hasse-Taylor expansion `∑ k ∈ range (m + 1), hasseDeriv k f • mk (X ^ k)`. -/
theorem polynomialSelfEquiv_jet (m : ℕ) (f : R[X]) :
    polynomialSelfEquiv R m (jet R R[X] R[X] m f) =
      ∑ k ∈ Finset.range (m + 1),
        hasseDeriv k f • Ideal.Quotient.mk (Ideal.span {(X : R[X][X]) ^ (m + 1)}) (X ^ k) := by
  rw [jet_apply, polynomialSelfEquiv_mkQ, polynomialTensorTaylorEquiv_tmul, one_smul]
  have hsum :
      (∑ k ∈ Finset.range (m + 1),
        hasseDeriv k f • Ideal.Quotient.mk (Ideal.span {(X : R[X][X]) ^ (m + 1)}) (X ^ k)) =
      Ideal.Quotient.mk _ (∑ k ∈ Finset.range (m + 1), C (hasseDeriv k f) * X ^ k) := by
    simp only [← Ideal.Quotient.mkₐ_eq_mk R[X], ← map_smul, ← map_sum, smul_eq_C_mul]
  rw [hsum, Ideal.Quotient.eq, Ideal.mem_span_singleton, X_pow_dvd_iff]
  intro d hd
  rw [coeff_sub, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero, sum_ite_eq, mem_range, hd,
    ↓reduceIte, taylor_coeff, hasseDeriv_map, eval_map, eval₂_C_X, sub_self]

end PrincipalParts

end TaylorPrincipalParts

end TauCeti
