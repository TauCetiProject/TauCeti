/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.RepresentationTheory.Character.Twist
public import TauCeti.RingTheory.MvPolynomial.Block.Dehomogenize
public import TauCeti.RingTheory.MvPolynomial.LinearSubst
import TauCeti.RingTheory.MvPolynomial.Box

/-!
# The algebraic coefficient modules `L_{n,s}` and the weight-`(n, s)` slash

Let `K` be a commutative semiring, `ι` a finite set, `n : ι → ℕ` and `s : ι → ℤ`. The algebraic
coefficient module `L_n(K)` is the `K`-module of polynomials in variables `z_i`, `i : ι`, of
degree at most `n i` in `z_i`, that is `MvPolynomial.restrictSupport` on the box of exponents
bounded by `n` (`TauCeti.algWeightModule`). A tuple `γ = (γ_i)` of invertible `2 × 2` matrices
`γ_i = !![a_i, b_i; c_i, d_i]` acts on it by the weight-`(n, s)` slash

`P ∣ γ = ∏_i det(γ_i)^{s_i} (c_i z_i + d_i)^{n_i} · P((a_i z_i + b_i) / (c_i z_i + d_i))`,

that is, `z^m ↦ ∏_i det(γ_i)^{s_i} (a_i z_i + b_i)^{m_i} (c_i z_i + d_i)^{n_i - m_i}` on monomials
(`TauCeti.coe_algWeightSlash_monomial`). These modules, with the action of `GL₂` of a completion
of a number field through its embeddings, are the coefficients of the classical forms on a
definite quaternion algebra; the weights `k_i = n_i + 2` and the determinant twists `s_i` are their
algebraic weight.

The slash is a right action, `P ∣ (γ δ) = (P ∣ γ) ∣ δ` (`TauCeti.algWeightSlash_mul_apply`). The
proof passes through the homogeneous model: writing `z_i^{m_i}` as `X_i^{m_i} Y_i^{n_i - m_i}`
identifies `L_n(K)` with the polynomials in `Y_i = X (i, 0)` and `X_i = X (i, 1)` that are
homogeneous of degree `n_i` in each pair (`MvPolynomial.blockDehomogenizeEquiv`), and there the
untwisted slash is the linear substitution `X_i ↦ a_i X_i + b_i Y_i`, `Y_i ↦ c_i X_i + d_i Y_i`
of `MvPolynomial.linearSubst`, which is a right action of the matrix monoid. In one variable the
homogeneous model is the module of binary forms of `TauCeti.binaryFormRep`.

The untwisted slash `TauCeti.algWeightMatrixRep` is defined for every tuple of matrices, invertible
or not, and so is a right action of the multiplicative monoid `ι → Matrix (Fin 2) (Fin 2) K`; the
twist by `∏_i det(γ_i)^{s_i}`, for integers `s_i` of either sign, needs a commutative ring `K` and
invertible matrices, and gives the right action `TauCeti.algWeightAction` of `ι → GL (Fin 2) K`.

## Main definitions

* `TauCeti.algWeightModule K n`: the polynomials of degree at most `n i` in each `z_i`.
* `TauCeti.algWeightSubstMatrix γ`: the block-diagonal matrix of the substitution
  `X_i ↦ a_i X_i + b_i Y_i`, `Y_i ↦ c_i X_i + d_i Y_i` in the homogeneous coordinates.
* `TauCeti.algWeightHomogeneousRep K n`: the same substitution on the homogeneous model.
* `TauCeti.algWeightMatrixRep K n`: the untwisted slash, a representation of the opposite of the
  monoid `ι → Matrix (Fin 2) (Fin 2) K`.
* `TauCeti.algWeightDetChar K s`: the character `γ ↦ ∏_i det(γ_i)^{s_i}`.
* `TauCeti.algWeightAction K n s`: the weight-`(n, s)` slash, a representation of the opposite of
  `ι → GL (Fin 2) K`.
* `TauCeti.algWeightSlash n s γ`: the linear map `P ↦ P ∣ γ`.

## Main results

* `TauCeti.coe_algWeightMatrixRep_monomial`: the untwisted slash of a monomial.
* `TauCeti.algWeightMatrixRep_scalar`: the scalar tuple `(u_i I)` acts by `∏_i u_i^{n_i}` in the
  untwisted slash.
* `TauCeti.algWeightSlash_one`, `TauCeti.algWeightSlash_mul`, `TauCeti.algWeightSlash_mul_apply`:
  the slash is a right action.
* `TauCeti.coe_algWeightSlash_monomial`: the slash of a monomial.
* `TauCeti.algWeightSlash_scalar`: the scalar tuple `(u_i I)` acts by `∏_i u_i^{n_i + 2 s_i}`.
* `TauCeti.finrank_algWeightModule`: `L_n(K)` has rank `∏_i (n_i + 1)`.
* `TauCeti.mapRestrictSupport_algWeightSlash`: changing coefficients along a ring map carries the
  slash by `γ` to the slash by the image of `γ`.

## References

* K. Buzzard, *On `p`-adic families of automorphic forms*, in *Modular curves and abelian
  varieties*, Progr. Math. 224, Birkhäuser (2004), §§2 and 7.
* K. Buzzard, *Eigenvarieties*, in *L-functions and Galois representations*, LMS Lecture Note
  Ser. 320, Cambridge University Press (2007), §§9–10.
-/

public section

open MvPolynomial Matrix MulOpposite

namespace TauCeti

variable {ι K : Type*}

section Semiring

variable [CommSemiring K]

section Module

variable (K) in
/-- The algebraic coefficient module `L_n(K)`: the polynomials in the variables `z_i`, `i : ι`, of
degree at most `n i` in each `z_i`. Its monomial basis is
`MvPolynomial.basisRestrictSupport K {m | ∀ i, m i ≤ n i}`. -/
noncomputable abbrev algWeightModule (n : ι → ℕ) : Submodule K (MvPolynomial ι K) :=
  restrictSupport K {m : ι →₀ ℕ | ∀ i, m i ≤ n i}

/-- The algebraic coefficient module `L_n(K)` is free of rank `∏_i (n_i + 1)`, with the monomials
`z^m`, `m ≤ n`, as a basis. -/
theorem finrank_algWeightModule [Fintype ι] [StrongRankCondition K] (n : ι → ℕ) :
    Module.finrank K (algWeightModule K n) = ∏ i, (n i + 1) := by
  classical
  rw [finrank_restrictSupport, ← range_boxMonomial,
    ← Nat.card_congr (Equiv.ofInjective _ boxMonomial_injective), Nat.card_eq_fintype_card,
    Fintype.card_pi]
  simp

end Module

variable [DecidableEq ι]

section Matrix

/-- The matrix of the substitution `X_i ↦ a_i X_i + b_i Y_i`, `Y_i ↦ c_i X_i + d_i Y_i` in the
variables `Y_i = X (i, 0)` and `X_i = X (i, 1)`, for `γ_i = !![a_i, b_i; c_i, d_i]`. It is block
diagonal, and its block at `i` is `γ_i` with rows and columns reindexed by `Fin.rev`, because the
affine variable `X_i` is the second coordinate of the pair. -/
def algWeightSubstMatrix (γ : ι → Matrix (Fin 2) (Fin 2) K) :
    Matrix (ι × Fin 2) (ι × Fin 2) K :=
  (blockDiagonal fun i ↦ (γ i).submatrix Fin.rev Fin.rev).submatrix
    (Equiv.prodComm ι (Fin 2)) (Equiv.prodComm ι (Fin 2))

theorem algWeightSubstMatrix_apply (γ : ι → Matrix (Fin 2) (Fin 2) K) (x y : ι × Fin 2) :
    algWeightSubstMatrix γ x y = if x.1 = y.1 then γ x.1 x.2.rev y.2.rev else 0 := by
  obtain ⟨i, p⟩ := x
  obtain ⟨j, q⟩ := y
  by_cases h : i = j
  · subst h
    simp [algWeightSubstMatrix]
  · simp [algWeightSubstMatrix, blockDiagonal_apply', h]

/-- Changing coefficients commutes with forming `TauCeti.algWeightSubstMatrix`. -/
theorem map_algWeightSubstMatrix {L : Type*} [CommRing L] (f : K →+* L)
    (γ : ι → Matrix (Fin 2) (Fin 2) K) :
    (algWeightSubstMatrix γ).map f = algWeightSubstMatrix fun i ↦ (γ i).map f := by
  ext x y
  simp only [Matrix.map_apply, algWeightSubstMatrix_apply]
  split_ifs <;> simp

@[simp]
theorem algWeightSubstMatrix_one : algWeightSubstMatrix (1 : ι → Matrix (Fin 2) (Fin 2) K) = 1 := by
  have h : (fun i ↦ (1 : ι → Matrix (Fin 2) (Fin 2) K) i |>.submatrix Fin.rev Fin.rev) = 1 :=
    funext fun _ ↦ submatrix_one_equiv Fin.revPerm
  rw [algWeightSubstMatrix, h, blockDiagonal_one, submatrix_one_equiv]

variable [Fintype ι]

theorem algWeightSubstMatrix_mul (γ δ : ι → Matrix (Fin 2) (Fin 2) K) :
    algWeightSubstMatrix (γ * δ) = algWeightSubstMatrix γ * algWeightSubstMatrix δ := by
  rw [algWeightSubstMatrix, algWeightSubstMatrix, algWeightSubstMatrix, submatrix_mul_equiv,
    ← blockDiagonal_mul]
  congr 2
  funext i
  exact (submatrix_mul_equiv (γ i) (δ i) Fin.rev Fin.revPerm Fin.rev).symm

/-- The substitution of `TauCeti.algWeightSubstMatrix γ` sends the affine variable `X_i` to
`a_i X_i + b_i Y_i`. -/
theorem linearSubst_algWeightSubstMatrix_X_one (γ : ι → Matrix (Fin 2) (Fin 2) K) (i : ι) :
    linearSubst (algWeightSubstMatrix γ) (X (i, 1)) =
      C (γ i 0 0) * X (i, 1) + C (γ i 0 1) * X (i, 0) := by
  simp [linearSubst_X, algWeightSubstMatrix_apply, Fintype.sum_prod_type, apply_ite C, ite_mul,
    Fin.sum_univ_two, add_comm]

/-- The substitution of `TauCeti.algWeightSubstMatrix γ` sends the homogenizing variable `Y_i` to
`c_i X_i + d_i Y_i`. -/
theorem linearSubst_algWeightSubstMatrix_X_zero (γ : ι → Matrix (Fin 2) (Fin 2) K) (i : ι) :
    linearSubst (algWeightSubstMatrix γ) (X (i, 0)) =
      C (γ i 1 0) * X (i, 1) + C (γ i 1 1) * X (i, 0) := by
  simp [linearSubst_X, algWeightSubstMatrix_apply, Fintype.sum_prod_type, apply_ite C, ite_mul,
    Fin.sum_univ_two, add_comm]

/-- The block-diagonal substitution preserves multihomogeneity in the pairs `(Y_i, X_i)`. -/
theorem _root_.MvPolynomial.IsMultiHomogeneous.linearSubst_algWeightSubstMatrix {n : ι → ℕ}
    {P : MvPolynomial (ι × Fin 2) K} (hP : IsMultiHomogeneous n P)
    (γ : ι → Matrix (Fin 2) (Fin 2) K) :
    IsMultiHomogeneous n (linearSubst (algWeightSubstMatrix γ) P) := by
  rw [linearSubst_eq_aeval]
  refine hP.aeval fun i p ↦ IsMultiHomogeneous.sum _ _ fun y _ ↦ ?_
  rw [algWeightSubstMatrix_apply]
  split_ifs with h
  · obtain ⟨j, q⟩ := y
    obtain rfl : i = j := h
    exact (isMultiHomogeneous_X i q).C_mul _
  · simp

end Matrix

variable [Fintype ι]

section Rep

variable (K) in
/-- The untwisted slash in the homogeneous model: the right action of tuples of `2 × 2`
matrices on the polynomials that are homogeneous of degree `n i` in each pair `(Y_i, X_i)`, by
the substitution `X_i ↦ a_i X_i + b_i Y_i`, `Y_i ↦ c_i X_i + d_i Y_i`. -/
noncomputable def algWeightHomogeneousRep (n : ι → ℕ) :
    Representation K (ι → Matrix (Fin 2) (Fin 2) K)ᵐᵒᵖ (multiHomogeneousSubmodule K (Fin 2) n)
    where
  toFun γ := (linearSubst (algWeightSubstMatrix γ.unop)).toLinearMap.restrict fun _ hP ↦
    mem_multiHomogeneousSubmodule.2
      ((mem_multiHomogeneousSubmodule.1 hP).linearSubst_algWeightSubstMatrix _)
  map_one' := LinearMap.ext fun P ↦ Subtype.ext <| by simp [linearSubst_one]
  map_mul' γ δ := LinearMap.ext fun P ↦ Subtype.ext <| by
    simp [algWeightSubstMatrix_mul, linearSubst_mul_apply]

@[simp]
theorem coe_algWeightHomogeneousRep_apply {n : ι → ℕ} (γ : (ι → Matrix (Fin 2) (Fin 2) K)ᵐᵒᵖ)
    (P : multiHomogeneousSubmodule K (Fin 2) n) :
    (algWeightHomogeneousRep K n γ P : MvPolynomial (ι × Fin 2) K) =
      linearSubst (algWeightSubstMatrix γ.unop) P :=
  (rfl)

variable (K) in
/-- **The untwisted slash.** The right action of the monoid of tuples of `2 × 2` matrices
`γ_i = !![a_i, b_i; c_i, d_i]` on `L_n(K)`,
`P ↦ ∏_i (c_i z_i + d_i)^{n_i} · P((a_i z_i + b_i) / (c_i z_i + d_i))`: the homogeneous
substitution `TauCeti.algWeightHomogeneousRep`, transported along dehomogenization. -/
noncomputable def algWeightMatrixRep (n : ι → ℕ) :
    Representation K (ι → Matrix (Fin 2) (Fin 2) K)ᵐᵒᵖ (algWeightModule K n) :=
  (blockDehomogenizeEquiv K n).conjRingEquiv.toMonoidHom.comp (algWeightHomogeneousRep K n)

/-- The untwisted slash of `P` dehomogenizes the substitution into the block homogenization
of `P`. -/
theorem coe_algWeightMatrixRep_apply {n : ι → ℕ} (γ : (ι → Matrix (Fin 2) (Fin 2) K)ᵐᵒᵖ)
    (P : algWeightModule K n) :
    (algWeightMatrixRep K n γ P : MvPolynomial ι K) =
      blockDehomogenize (linearSubst (algWeightSubstMatrix γ.unop)
        (rename (Sum.elim (·, (0 : Fin 2)) (·, 1)) (blockHomogenize id n (P : MvPolynomial ι K))))
    := by
  simp [algWeightMatrixRep]

/-- **The untwisted slash of a monomial.** For `m ≤ n`, the slash of `z^m` by
`γ_i = !![a_i, b_i; c_i, d_i]` is `∏_i (a_i z_i + b_i)^{m_i} (c_i z_i + d_i)^{n_i - m_i}`. -/
theorem coe_algWeightMatrixRep_monomial {n : ι → ℕ} (γ : (ι → Matrix (Fin 2) (Fin 2) K)ᵐᵒᵖ)
    {m : ι →₀ ℕ} (hm : ∀ i, m i ≤ n i) :
    (algWeightMatrixRep K n γ ⟨monomial m 1, by simp [hm]⟩ : MvPolynomial ι K) =
      ∏ i, (C (γ.unop i 0 0) * X i + C (γ.unop i 0 1)) ^ m i *
        (C (γ.unop i 1 0) * X i + C (γ.unop i 1 1)) ^ (n i - m i) := by
  rw [coe_algWeightMatrixRep_apply, ← coe_blockDehomogenizeEquiv_symm_apply,
    blockDehomogenizeEquiv_symm_monomial hm]
  simp only [map_prod, map_mul, map_pow, linearSubst_algWeightSubstMatrix_X_one,
    linearSubst_algWeightSubstMatrix_X_zero, map_add, algHom_C, algebraMap_eq,
    blockDehomogenize_X_one, blockDehomogenize_X_zero, mul_one]

/-- The scalar matrix `u • 1` in every factor acts on `L_n(K)` by `∏_i u_i^{n_i}` in the untwisted
slash. -/
theorem algWeightMatrixRep_scalar {n : ι → ℕ} (u : ι → K) :
    algWeightMatrixRep K n (op fun i ↦ Matrix.scalar (Fin 2) (u i)) =
      (∏ i, u i ^ n i) • LinearMap.id := by
  refine (basisRestrictSupport K _).ext fun m ↦ Subtype.ext ?_
  have hm : ∀ i, (m : ι →₀ ℕ) i ≤ n i := m.property
  have hb : (basisRestrictSupport K {m : ι →₀ ℕ | ∀ i, m i ≤ n i} m : algWeightModule K n) =
      ⟨monomial m 1, by simp⟩ := Subtype.ext (by simp)
  rw [hb, coe_algWeightMatrixRep_monomial _ hm]
  simp only [unop_op, scalar_apply, diagonal_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
    SetLike.val_smul, smul_eq_C_mul, monomial_eq]
  simp only [↓reduceIte, Fin.isValue, zero_ne_one, C_0, add_zero, one_ne_zero, zero_mul,
    zero_add, map_prod, C_pow, C_1, Finsupp.prod_pow, one_mul, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (hm i)
  rw [hk, Nat.add_sub_cancel_left]
  ring

end Rep

end Semiring

section Twist

variable [CommRing K] [Fintype ι] [DecidableEq ι]

variable (K) in
/-- The character `γ ↦ ∏_i det(γ_i)^{s_i}` of the opposite of `ι → GL (Fin 2) K`, by which the
weight-`(n, s)` slash twists the untwisted one. -/
def algWeightDetChar (s : ι → ℤ) : (ι → GL (Fin 2) K)ᵐᵒᵖ →* Kˣ where
  toFun γ := ∏ i, GeneralLinearGroup.det (γ.unop i) ^ s i
  map_one' := by simp
  map_mul' γ δ := by
    simp [mul_zpow, Finset.prod_mul_distrib, mul_comm]

omit [DecidableEq ι] in
@[simp]
theorem algWeightDetChar_apply (s : ι → ℤ) (γ : (ι → GL (Fin 2) K)ᵐᵒᵖ) :
    algWeightDetChar K s γ = ∏ i, GeneralLinearGroup.det (γ.unop i) ^ s i :=
  (rfl)

variable (K) in
/-- **The weight-`(n, s)` slash** as a right action of `ι → GL (Fin 2) K` on `L_n(K)`: the
untwisted slash `TauCeti.algWeightMatrixRep` of the underlying matrices, twisted by the character
`γ ↦ ∏_i det(γ_i)^{s_i}`. -/
noncomputable def algWeightAction (n : ι → ℕ) (s : ι → ℤ) :
    Representation K (ι → GL (Fin 2) K)ᵐᵒᵖ (algWeightModule K n) :=
  Representation.charTwist (algWeightDetChar K s)
    ((algWeightMatrixRep K n).comp (MonoidHom.op (MonoidHom.compLeft (Units.coeHom _) ι)))

/-- The weight-`(n, s)` slash `P ↦ P ∣ γ` of `γ = (γ_i) : ι → GL (Fin 2) K` on `L_n(K)`,
`P ∣ γ = ∏_i det(γ_i)^{s_i} (c_i z_i + d_i)^{n_i} · P((a_i z_i + b_i) / (c_i z_i + d_i))`. -/
noncomputable def algWeightSlash (n : ι → ℕ) (s : ι → ℤ) (γ : ι → GL (Fin 2) K) :
    algWeightModule K n →ₗ[K] algWeightModule K n :=
  algWeightAction K n s (op γ)

@[simp]
theorem algWeightAction_op (n : ι → ℕ) (s : ι → ℤ) (γ : ι → GL (Fin 2) K) :
    algWeightAction K n s (op γ) = algWeightSlash n s γ :=
  (rfl)

/-- The weight-`(n, s)` slash is the untwisted slash of the underlying matrices, multiplied by
`∏_i det(γ_i)^{s_i}`. -/
theorem algWeightSlash_eq_smul (n : ι → ℕ) (s : ι → ℤ) (γ : ι → GL (Fin 2) K) :
    algWeightSlash n s γ =
      ((∏ i, GeneralLinearGroup.det (γ i) ^ s i : Kˣ) : K) •
        algWeightMatrixRep K n (op fun i ↦ (γ i : Matrix (Fin 2) (Fin 2) K)) := by
  simp only [algWeightSlash, algWeightAction, Representation.charTwist_apply,
    MonoidHom.comp_apply, MonoidHom.op_apply_apply, algWeightDetChar_apply, unop_op]
  -- `MonoidHom.compLeft (Units.coeHom _) ι γ` is by definition `fun i ↦ (γ i : Matrix _ _ K)`
  rfl

@[simp]
theorem algWeightSlash_one (n : ι → ℕ) (s : ι → ℤ) :
    algWeightSlash n s (1 : ι → GL (Fin 2) K) = LinearMap.id :=
  map_one (algWeightAction K n s)

/-- The weight-`(n, s)` slash is a right action: the slash by `γ δ` is the slash by `γ` followed
by the slash by `δ`. -/
theorem algWeightSlash_mul (n : ι → ℕ) (s : ι → ℤ) (γ δ : ι → GL (Fin 2) K) :
    algWeightSlash n s (γ * δ) = algWeightSlash n s δ ∘ₗ algWeightSlash n s γ :=
  map_mul (algWeightAction K n s) (op δ) (op γ)

/-- `P ∣ (γ δ) = (P ∣ γ) ∣ δ`. -/
theorem algWeightSlash_mul_apply (n : ι → ℕ) (s : ι → ℤ) (γ δ : ι → GL (Fin 2) K)
    (P : algWeightModule K n) :
    algWeightSlash n s (γ * δ) P = algWeightSlash n s δ (algWeightSlash n s γ P) := by
  rw [algWeightSlash_mul, LinearMap.comp_apply]

/-- **The weight-`(n, s)` slash of a monomial.** For `m ≤ n` and
`γ_i = !![a_i, b_i; c_i, d_i]`,
`z^m ∣ γ = ∏_i det(γ_i)^{s_i} · ∏_i (a_i z_i + b_i)^{m_i} (c_i z_i + d_i)^{n_i - m_i}`. -/
theorem coe_algWeightSlash_monomial (n : ι → ℕ) (s : ι → ℤ) (γ : ι → GL (Fin 2) K)
    {m : ι →₀ ℕ} (hm : ∀ i, m i ≤ n i) :
    (algWeightSlash n s γ ⟨monomial m 1, by simp [hm]⟩ : MvPolynomial ι K) =
      ((∏ i, GeneralLinearGroup.det (γ i) ^ s i : Kˣ) : K) •
        ∏ i, (C (γ i 0 0) * X i + C (γ i 0 1)) ^ m i *
          (C (γ i 1 0) * X i + C (γ i 1 1)) ^ (n i - m i) := by
  rw [algWeightSlash_eq_smul, LinearMap.smul_apply, Submodule.coe_smul,
    coe_algWeightMatrixRep_monomial _ hm, unop_op]

/-- **Scalars.** The scalar tuple `(u_i • 1)` acts on `L_n(K)` by `∏_i u_i^{n_i + 2 s_i}`. -/
theorem algWeightSlash_scalar (n : ι → ℕ) (s : ι → ℤ) (u : ι → Kˣ) :
    algWeightSlash n s (fun i ↦ GeneralLinearGroup.scalar (Fin 2) (u i)) =
      ((∏ i, u i ^ ((n i : ℤ) + 2 * s i) : Kˣ) : K) • LinearMap.id := by
  rw [algWeightSlash_eq_smul]
  simp only [GeneralLinearGroup.coe_scalar]
  rw [algWeightMatrixRep_scalar, smul_smul]
  congr 1
  have key (i : ι) : (u i ^ 2) ^ s i * u i ^ n i = u i ^ ((n i : ℤ) + 2 * s i) := by
    rw [zpow_add, zpow_mul, zpow_natCast, mul_comm]
    norm_cast
  simp only [GeneralLinearGroup.det_scalar, Fintype.card_fin, ← key, Finset.prod_mul_distrib,
    Units.val_mul, Units.coe_prod, Units.val_pow_eq_pow_val]

/-- **Change of coefficients.** For a ring map `f : K →+* L`, changing the coefficients of
`P ∣ γ` along `f` gives the slash, by the image of `γ`, of `P` with coefficients changed. -/
theorem mapRestrictSupport_algWeightSlash {L : Type*} [CommRing L] (f : K →+* L) (n : ι → ℕ)
    (s : ι → ℤ) (γ : ι → GL (Fin 2) K) (P : algWeightModule K n) :
    mapRestrictSupport _ f (algWeightSlash n s γ P) =
      algWeightSlash n s (fun i ↦ GeneralLinearGroup.map f (γ i)) (mapRestrictSupport _ f P) := by
  refine Subtype.ext ?_
  rw [coe_mapRestrictSupport_apply, algWeightSlash_eq_smul, algWeightSlash_eq_smul,
    LinearMap.smul_apply, LinearMap.smul_apply, Submodule.coe_smul, Submodule.coe_smul,
    coe_algWeightMatrixRep_apply, coe_algWeightMatrixRep_apply, coe_mapRestrictSupport_apply,
    smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C, map_blockDehomogenize, map_linearSubst,
    map_rename, ← blockHomogenize_map, map_algWeightSubstMatrix]
  congr 2
  rw [show ∏ i, GeneralLinearGroup.det (GeneralLinearGroup.map f (γ i)) ^ s i =
      Units.map (f : K →* L) (∏ i, GeneralLinearGroup.det (γ i) ^ s i) by
    simp [GeneralLinearGroup.map_det, map_prod, map_zpow], Units.coe_map, MonoidHom.coe_ofClass]

end Twist

/-! ### The right-action convention

In one variable with `n = 1`, take `γ = !![1, 1; 0, 1]` and `δ = !![1, 0; 1, 1]`. The slash of
`γ` fixes the constant `1` and the slash of `δ` sends it to `z + 1`, so the right action gives
`1 ∣ (γ δ) = (1 ∣ γ) ∣ δ = z + 1` with `γ δ = !![2, 1; 1, 1]`, while the other product
`δ γ = !![1, 1; 1, 2]` sends `1` to `z + 2`. -/

example : (algWeightMatrixRep ℤ (fun _ : Fin 1 ↦ 1) (op fun _ ↦ !![2, 1; 1, 1])
    ⟨monomial 0 1, by simp [mem_restrictSupport_iff]⟩ :
      MvPolynomial (Fin 1) ℤ) = X 0 + 1 := by
  rw [coe_algWeightMatrixRep_monomial _ (by simp)]
  simp

example : (algWeightMatrixRep ℤ (fun _ : Fin 1 ↦ 1) (op fun _ ↦ !![1, 1; 1, 2])
    ⟨monomial 0 1, by simp [mem_restrictSupport_iff]⟩ :
      MvPolynomial (Fin 1) ℤ) = X 0 + 2 := by
  rw [coe_algWeightMatrixRep_monomial _ (by simp)]
  simp

end TauCeti
