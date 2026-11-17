/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.Matrix.Block
import TauCeti.RingTheory.MvPolynomial.LinearSubst
import TauCeti.RingTheory.MvPolynomial.RestrictSupport
import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Algebraic coefficient modules of weight `(n, s)`

Let `K` be a commutative ring, `ι` a finite set, `n : ι → ℕ` and `s : ι → ℤ`. The algebraic
coefficient module `L_n(K)` is the `K`-module of polynomials in variables `zᵢ` (`i ∈ ι`) of degree
at most `nᵢ` in each `zᵢ`. The group `∏ᵢ GL₂(K)` acts on it on the right by the weight-`(n, s)`
slash: for `γ = (γᵢ)` with `γᵢ = !![aᵢ, bᵢ; cᵢ, dᵢ]`,

`P ∣ γ = ∏ᵢ det(γᵢ)^{sᵢ} (cᵢ zᵢ + dᵢ)^{nᵢ} · P((aᵢ zᵢ + bᵢ) / (cᵢ zᵢ + dᵢ))`,

that is, on monomials, `z^m ↦ ∏ᵢ det(γᵢ)^{sᵢ} (aᵢ zᵢ + bᵢ)^{mᵢ} (cᵢ zᵢ + dᵢ)^{nᵢ - mᵢ}`. These are
the coefficient modules of Hilbert and quaternionic modular forms of weight `nᵢ + 2` at the
embedding `i`, the exponent `sᵢ` fixing the normalization of the determinant.

The slash is defined on all polynomials by its value on monomials, and is an action only on
`L_n(K)`. The composition law `P ∣ (γ δ) = (P ∣ γ) ∣ δ` is proved by homogenizing: writing
`zᵢ^{mᵢ}` as `Xᵢ^{mᵢ} Yᵢ^{nᵢ - mᵢ}` identifies `L_n(K)` with the polynomials in `Xᵢ, Yᵢ` that are
homogeneous of degree `nᵢ` in each pair `(Xᵢ, Yᵢ)`, and on these the slash is
`det(γᵢ)^{sᵢ} · P(aᵢ Xᵢ + bᵢ Yᵢ, cᵢ Xᵢ + dᵢ Yᵢ)`, a linear change of variables by the block-diagonal
matrix of the `γᵢ`, which composes on the right (`MvPolynomial.linearSubst_mul`).

## Main definitions

* `TauCeti.algWeightModule K n`: the polynomials of degree at most `nᵢ` in each variable `zᵢ`.
* `TauCeti.algWeightSlash n s γ`: the weight-`(n, s)` slash by `γ ∈ ∏ᵢ GL₂(K)`.
* `TauCeti.algWeightAction n s`: the right action of `∏ᵢ GL₂(K)` on `algWeightModule K n`, as a
  representation of the opposite group.

## Main results

* `TauCeti.algWeightSlash_mem`: the slash preserves `algWeightModule K n`.
* `TauCeti.algWeightSlash_one`, `TauCeti.algWeightSlash_mul`: the slash is a right action on
  `algWeightModule K n`.
* `TauCeti.algWeightSlash_scalar`: the scalar `uᵢ` in each factor acts by `∏ᵢ uᵢ^{nᵢ + 2 sᵢ}`.
* `TauCeti.map_algWeightSlash`: changing coefficients along a ring homomorphism carries the slash
  by `γ` to the slash by the image of `γ`.
-/

public section

open MvPolynomial Matrix

namespace TauCeti

section Module

variable (K : Type*) [CommSemiring K] {ι : Type*}

/-- The algebraic coefficient module `L_n(K)`: the polynomials in the variables `zᵢ` whose degree
in each `zᵢ` is at most `nᵢ`. -/
noncomputable def algWeightModule (n : ι → ℕ) : Submodule K (MvPolynomial ι K) :=
  restrictSupport K {m | ∀ i, m i ≤ n i}

variable {K}

/-- A polynomial lies in `L_n(K)` when each of its monomials has degree at most `nᵢ` in `zᵢ`. -/
theorem mem_algWeightModule {n : ι → ℕ} {P : MvPolynomial ι K} :
    P ∈ algWeightModule K n ↔ ∀ m ∈ P.support, ∀ i, m i ≤ n i := by
  simp only [algWeightModule, mem_restrictSupport_iff, Set.subset_def, Finset.mem_coe,
    Set.mem_ofPred_eq]

/-- A polynomial lies in `L_n(K)` exactly when its degree in each `zᵢ` is at most `nᵢ`. -/
theorem mem_algWeightModule_iff_degreeOf_le {n : ι → ℕ} {P : MvPolynomial ι K} :
    P ∈ algWeightModule K n ↔ ∀ i, P.degreeOf i ≤ n i :=
  mem_restrictSupport_iff_degreeOf_le

/-- A monomial `r z^m` lies in `L_n(K)` when `mᵢ ≤ nᵢ` for every `i`, or `r = 0`. -/
@[simp]
theorem monomial_mem_algWeightModule {n : ι → ℕ} {m : ι →₀ ℕ} {r : K} :
    monomial m r ∈ algWeightModule K n ↔ (∀ i, m i ≤ n i) ∨ r = 0 :=
  monomial_mem_restrictSupport K

end Module

section Slash

variable {K : Type*} [CommRing K] {ι : Type*} [Fintype ι]

/-- The weight-`(n, s)` slash by `γ = (γᵢ) ∈ ∏ᵢ GL₂(K)`, with `γᵢ = !![aᵢ, bᵢ; cᵢ, dᵢ]`: the
`K`-linear map sending the monomial `z^m` to
`∏ᵢ det(γᵢ)^{sᵢ} (aᵢ zᵢ + bᵢ)^{mᵢ} (cᵢ zᵢ + dᵢ)^{nᵢ - mᵢ}`. On `algWeightModule K n` it is
`P ↦ ∏ᵢ det(γᵢ)^{sᵢ} (cᵢ zᵢ + dᵢ)^{nᵢ} · P((aᵢ zᵢ + bᵢ) / (cᵢ zᵢ + dᵢ))`, and it is a right action
there (`TauCeti.algWeightSlash_mul`). -/
noncomputable def algWeightSlash (n : ι → ℕ) (s : ι → ℤ) (γ : ι → GL (Fin 2) K) :
    MvPolynomial ι K →ₗ[K] MvPolynomial ι K :=
  (basisMonomials ι K).constr K fun m ↦
    C ((∏ i, GeneralLinearGroup.det (γ i) ^ s i : Kˣ) : K) *
      ∏ i, (C (γ i 0 0) * X i + C (γ i 0 1)) ^ m i * (C (γ i 1 0) * X i + C (γ i 1 1)) ^ (n i - m i)

/-- The slash of a monomial: `(r z^m) ∣ γ = r ∏ᵢ det(γᵢ)^{sᵢ} (aᵢ zᵢ + bᵢ)^{mᵢ}
(cᵢ zᵢ + dᵢ)^{nᵢ - mᵢ}`. -/
theorem algWeightSlash_monomial (n : ι → ℕ) (s : ι → ℤ) (γ : ι → GL (Fin 2) K) (m : ι →₀ ℕ)
    (r : K) :
    algWeightSlash n s γ (monomial m r) =
      C (r * ((∏ i, GeneralLinearGroup.det (γ i) ^ s i : Kˣ) : K)) *
        ∏ i, (C (γ i 0 0) * X i + C (γ i 0 1)) ^ m i *
          (C (γ i 1 0) * X i + C (γ i 1 1)) ^ (n i - m i) := by
  have h : monomial m r = r • basisMonomials ι K m := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, algWeightSlash, Module.Basis.constr_basis, smul_eq_C_mul, map_mul, mul_assoc]

/-! ### The homogeneous model

The variables `X (0, i)` and `X (1, i)` of `MvPolynomial (Fin 2 × ι) K` play the roles of `Xᵢ`
and `Yᵢ`. -/

/-- The homogenization `z^m ↦ ∏ᵢ Xᵢ^{mᵢ} Yᵢ^{nᵢ - mᵢ}`. -/
private noncomputable def algWeightHom (n : ι → ℕ) :
    MvPolynomial ι K →ₗ[K] MvPolynomial (Fin 2 × ι) K :=
  (basisMonomials ι K).constr K fun m ↦ ∏ i, X (0, i) ^ m i * X (1, i) ^ (n i - m i)

omit [Fintype ι] in
/-- The dehomogenization `Xᵢ ↦ zᵢ`, `Yᵢ ↦ 1`. -/
private noncomputable def algWeightDehom : MvPolynomial (Fin 2 × ι) K →ₐ[K] MvPolynomial ι K :=
  aeval fun p ↦ ![X p.2, 1] p.1

/-- The change of variables `Xᵢ ↦ aᵢ Xᵢ + bᵢ Yᵢ`, `Yᵢ ↦ cᵢ Xᵢ + dᵢ Yᵢ`. -/
private noncomputable def algWeightSubst [DecidableEq ι] (γ : ι → GL (Fin 2) K) :
    MvPolynomial (Fin 2 × ι) K →ₐ[K] MvPolynomial (Fin 2 × ι) K :=
  linearSubst (blockDiagonal fun i ↦ (γ i : Matrix (Fin 2) (Fin 2) K))

omit [Fintype ι] in
/-- The multidegree: `Xᵢ` and `Yᵢ` have weight the `i`-th standard vector. -/
private def algWeightWeight [DecidableEq ι] (p : Fin 2 × ι) : ι → ℕ :=
  Pi.single p.2 1

omit [Fintype ι] in
private theorem weight_algWeightWeight_apply [Finite ι] [DecidableEq ι] (e : Fin 2 × ι →₀ ℕ)
    (i : ι) : Finsupp.weight algWeightWeight e i = e (0, i) + e (1, i) := by
  cases nonempty_fintype ι
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Finset.sum_apply, Fintype.sum_prod_type,
    algWeightWeight, Pi.single_apply, Fin.sum_univ_two]

omit [Fintype ι] in
@[simp]
private theorem algWeightDehom_X_zero (i : ι) :
    algWeightDehom (X (0, i) : MvPolynomial _ K) = X i := by
  simp [algWeightDehom]

omit [Fintype ι] in
@[simp]
private theorem algWeightDehom_X_one (i : ι) :
    algWeightDehom (X (1, i) : MvPolynomial _ K) = 1 := by
  simp [algWeightDehom]

private theorem algWeightHom_monomial (n : ι → ℕ) (m : ι →₀ ℕ) (r : K) :
    algWeightHom n (monomial m r) = C r * ∏ i, X (0, i) ^ m i * X (1, i) ^ (n i - m i) := by
  have h : monomial m r = r • basisMonomials ι K m := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, algWeightHom, Module.Basis.constr_basis, smul_eq_C_mul]

omit [Fintype ι] in
private theorem algWeightDehom_monomial [Finite ι] (d : Fin 2 × ι →₀ ℕ) (r : K) :
    algWeightDehom (monomial d r) =
      monomial (Finsupp.equivFunOnFinite.symm fun i ↦ d (0, i)) r := by
  cases nonempty_fintype ι
  simp [algWeightDehom, monomial_eq, Finsupp.prod_fintype, Fintype.prod_prod_type,
    Fin.prod_univ_two]

private theorem algWeightSubst_X [DecidableEq ι] (γ : ι → GL (Fin 2) K) (a : Fin 2) (i : ι) :
    algWeightSubst γ (X (a, i)) = C (γ i a 0) * X (0, i) + C (γ i a 1) * X (1, i) := by
  simp [algWeightSubst, linearSubst_X, Fintype.sum_prod_type, blockDiagonal_apply,
    Fin.sum_univ_two, apply_ite C, ite_mul]

/-- The homogenization of a polynomial of degree at most `nᵢ` in each `zᵢ` is homogeneous of
degree `nᵢ` in each pair `(Xᵢ, Yᵢ)`. -/
private theorem isWeightedHomogeneous_algWeightHom [DecidableEq ι] {n : ι → ℕ}
    {P : MvPolynomial ι K} (hP : P ∈ algWeightModule K n) :
    (algWeightHom n P).IsWeightedHomogeneous algWeightWeight n := by
  rw [P.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun m hm ↦ ?_
  rw [algWeightHom_monomial]
  have hn : ∑ i, (m i • algWeightWeight (0, i) + (n i - m i) • algWeightWeight (1, i)) = n := by
    ext j
    have := mem_algWeightModule.mp hP m hm j
    simp [Finset.sum_apply, algWeightWeight, Pi.single_apply, Finset.sum_add_distrib]
    omega
  have h := (IsWeightedHomogeneous.prod Finset.univ _ _ fun i _ ↦
    ((isWeightedHomogeneous_X K algWeightWeight (0, i)).pow (m i)).mul
      ((isWeightedHomogeneous_X K algWeightWeight (1, i)).pow (n i - m i))).C_mul (P.coeff m)
  rwa [hn] at h

/-- The change of variables preserves the multidegree. -/
private theorem isWeightedHomogeneous_algWeightSubst [DecidableEq ι]
    {Q : MvPolynomial (Fin 2 × ι) K} {n : ι → ℕ} (hQ : Q.IsWeightedHomogeneous algWeightWeight n)
    (γ : ι → GL (Fin 2) K) :
    (algWeightSubst γ Q).IsWeightedHomogeneous algWeightWeight n := by
  rw [aeval_unique (algWeightSubst γ)]
  refine hQ.aeval fun ⟨a, i⟩ ↦ ?_
  rw [Function.comp_apply, algWeightSubst_X]
  exact ((isWeightedHomogeneous_X K _ _).C_mul _).add ((isWeightedHomogeneous_X K _ _).C_mul _)

omit [Fintype ι] in
/-- Dehomogenizing a polynomial homogeneous of degree `nᵢ` in each pair `(Xᵢ, Yᵢ)` gives a
polynomial of degree at most `nᵢ` in each `zᵢ`. -/
private theorem algWeightDehom_mem [Finite ι] [DecidableEq ι] {Q : MvPolynomial (Fin 2 × ι) K}
    {n : ι → ℕ} (hQ : Q.IsWeightedHomogeneous algWeightWeight n) :
    algWeightDehom Q ∈ algWeightModule K n := by
  induction hQ using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q _ _ hp hq => simpa using add_mem hp hq
  | monomial d r hr =>
    rw [algWeightDehom_monomial, monomial_mem_algWeightModule]
    refine Or.inl fun i ↦ ?_
    have := congrFun hr i
    rw [weight_algWeightWeight_apply] at this
    rw [Finsupp.coe_equivFunOnFinite_symm]
    omega

/-- Homogenizing in degree `n` undoes dehomogenization on polynomials homogeneous of degree `nᵢ`
in each pair `(Xᵢ, Yᵢ)`. -/
private theorem algWeightHom_algWeightDehom [DecidableEq ι] {Q : MvPolynomial (Fin 2 × ι) K}
    {n : ι → ℕ} (hQ : Q.IsWeightedHomogeneous algWeightWeight n) :
    algWeightHom n (algWeightDehom Q) = Q := by
  induction hQ using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q _ _ hp hq => simp [hp, hq]
  | monomial d r hr =>
    have hd : ∀ i, n i - d (0, i) = d (1, i) := fun i ↦ by
      have := congrFun hr i
      rw [weight_algWeightWeight_apply] at this
      omega
    rw [algWeightDehom_monomial, algWeightHom_monomial]
    simp [hd, monomial_eq, Finsupp.prod_fintype,
      Fintype.prod_prod_type, Fin.prod_univ_two, Finset.prod_mul_distrib]

/-- The slash is the dehomogenization of a change of variables of the homogenization. -/
private theorem algWeightSlash_apply_eq [DecidableEq ι] (n : ι → ℕ) (s : ι → ℤ)
    (γ : ι → GL (Fin 2) K) (P : MvPolynomial ι K) :
    algWeightSlash n s γ P = ((∏ i, GeneralLinearGroup.det (γ i) ^ s i : Kˣ) : K) •
      algWeightDehom (algWeightSubst γ (algWeightHom n P)) := by
  induction P using MvPolynomial.induction_on' with
  | monomial m r =>
    simp only [algWeightSlash_monomial, algWeightHom_monomial, map_mul, map_prod, map_pow,
      algHom_C, algebraMap_eq, algWeightSubst_X, map_add, algWeightDehom_X_zero,
      algWeightDehom_X_one, mul_one, smul_eq_C_mul]
    ring
  | add p q hp hq => simp [hp, hq]

/-- The weight-`(n, s)` slash preserves the polynomials of degree at most `nᵢ` in each `zᵢ`. -/
theorem algWeightSlash_mem (n : ι → ℕ) (s : ι → ℤ) (γ : ι → GL (Fin 2) K)
    {P : MvPolynomial ι K} (hP : P ∈ algWeightModule K n) :
    algWeightSlash n s γ P ∈ algWeightModule K n := by
  classical
  rw [algWeightSlash_apply_eq]
  exact Submodule.smul_mem _ _ <| algWeightDehom_mem <|
    isWeightedHomogeneous_algWeightSubst (isWeightedHomogeneous_algWeightHom hP) γ

/-- The identity acts trivially. -/
@[simp]
theorem algWeightSlash_one (n : ι → ℕ) (s : ι → ℤ) :
    algWeightSlash n s (1 : ι → GL (Fin 2) K) = LinearMap.id := by
  refine (basisMonomials ι K).ext fun m ↦ ?_
  rw [coe_basisMonomials, algWeightSlash_monomial, LinearMap.id_apply]
  simp [monomial_eq, Finsupp.prod_fintype]

/-- The weight-`(n, s)` slash is a right action on the polynomials of degree at most `nᵢ` in each
`zᵢ`: `P ∣ (γ δ) = (P ∣ γ) ∣ δ`. -/
theorem algWeightSlash_mul (n : ι → ℕ) (s : ι → ℤ) (γ δ : ι → GL (Fin 2) K)
    {P : MvPolynomial ι K} (hP : P ∈ algWeightModule K n) :
    algWeightSlash n s (γ * δ) P = algWeightSlash n s δ (algWeightSlash n s γ P) := by
  classical
  have hmat : (fun i ↦ ((γ * δ) i : Matrix (Fin 2) (Fin 2) K)) =
      fun i ↦ (γ i : Matrix (Fin 2) (Fin 2) K) * (δ i : Matrix (Fin 2) (Fin 2) K) :=
    funext fun i ↦ by rw [Pi.mul_apply, Units.val_mul]
  have hsubst : algWeightSubst (γ * δ) = (algWeightSubst δ).comp (algWeightSubst γ) := by
    rw [algWeightSubst, algWeightSubst, algWeightSubst, hmat, blockDiagonal_mul, linearSubst_mul]
  simp only [algWeightSlash_apply_eq]
  rw [map_smul, map_smul, map_smul, algWeightHom_algWeightDehom
      (isWeightedHomogeneous_algWeightSubst (isWeightedHomogeneous_algWeightHom hP) γ), hsubst,
    AlgHom.comp_apply, smul_smul, Pi.mul_def]
  simp only [map_mul, mul_zpow, Finset.prod_mul_distrib, Units.val_mul, mul_comm]

/-- The scalar `uᵢ` in each factor acts on `L_n(K)` by `∏ᵢ uᵢ^{nᵢ + 2 sᵢ}`. -/
theorem algWeightSlash_scalar (n : ι → ℕ) (s : ι → ℤ) (u : ι → Kˣ) {P : MvPolynomial ι K}
    (hP : P ∈ algWeightModule K n) :
    algWeightSlash n s (fun i ↦ GeneralLinearGroup.scalar (Fin 2) (u i)) P =
      ((∏ i, u i ^ ((n i : ℤ) + 2 * s i) : Kˣ) : K) • P := by
  rw [P.as_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hmn := mem_algWeightModule.mp hP m hm
  have key : ∀ i, ((u i ^ 2) ^ s i * u i ^ m i * u i ^ (n i - m i) : Kˣ) =
      u i ^ ((n i : ℤ) + 2 * s i) := fun i ↦ by
    simp only [← zpow_natCast, ← zpow_mul, ← zpow_add]
    congr 1
    push_cast [Nat.cast_sub (hmn i)]
    ring
  rw [algWeightSlash_monomial]
  simp only [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq,
    diagonal_apply_ne _ zero_ne_one, diagonal_apply_ne _ one_ne_zero, map_zero, add_zero, zero_mul,
    zero_add, GeneralLinearGroup.det_scalar, Fintype.card_fin, Units.coe_prod, map_mul, map_prod]
  rw [mul_assoc, ← Finset.prod_mul_distrib, smul_eq_C_mul, map_prod, monomial_eq,
    Finsupp.prod_fintype _ _ fun _ ↦ pow_zero _, mul_left_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [← key i]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, mul_pow]
  ring

/-- Changing coefficients along a ring homomorphism `f` carries the slash by `γ` to the slash by
the image of `γ` under `f`. -/
theorem map_algWeightSlash {L : Type*} [CommRing L] (f : K →+* L) (n : ι → ℕ) (s : ι → ℤ)
    (γ : ι → GL (Fin 2) K) (P : MvPolynomial ι K) :
    map f (algWeightSlash n s γ P) =
      algWeightSlash n s (fun i ↦ GeneralLinearGroup.map f (γ i)) (map f P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial m r =>
    simp [algWeightSlash_monomial, GeneralLinearGroup.map_det, ← map_zpow]
  | add p q hp hq => simp [hp, hq]

end Slash

section Action

variable {K : Type*} [CommRing K] {ι : Type*} [Fintype ι]

/-- The algebraic coefficient module `L_n(K)` with the right action of `∏ᵢ GL₂(K)` by the
weight-`(n, s)` slash, as a representation of the opposite group: `op γ` acts by `P ↦ P ∣ γ`. -/
noncomputable def algWeightAction (n : ι → ℕ) (s : ι → ℤ) :
    Representation K (ι → GL (Fin 2) K)ᵐᵒᵖ (algWeightModule K n) where
  toFun γ := (algWeightSlash n s γ.unop).restrict fun _ hP ↦ algWeightSlash_mem n s γ.unop hP
  map_one' := LinearMap.ext fun P ↦ Subtype.ext <| by simp
  map_mul' γ δ := LinearMap.ext fun P ↦ Subtype.ext <| algWeightSlash_mul n s δ.unop γ.unop P.2

/-- `op γ` acts on `L_n(K)` by the slash `P ↦ P ∣ γ`. -/
@[simp]
theorem coe_algWeightAction_apply (n : ι → ℕ) (s : ι → ℤ) (γ : (ι → GL (Fin 2) K)ᵐᵒᵖ)
    (P : algWeightModule K n) :
    (algWeightAction n s γ P : MvPolynomial ι K) = algWeightSlash n s γ.unop P :=
  (rfl)

end Action

end TauCeti
