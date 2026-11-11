/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.Right.Defs
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Unit
import TauCeti.Algebra.Ring.NegOnePow
import TauCeti.LinearAlgebra.TensorProduct.Balanced.Grading.Basic

/-!
# The differential on a balanced tensor product of DG modules

For a right DG module `M` and a left DG module `N` over the same DG algebra `A`, the
ordinary balanced tensor product carries the differential
`d (m ⊗ n) = dM m ⊗ n + (-1)^|m| m ⊗ dN n`.
The two module Leibniz rules make this formula balanced even when the algebra differential
is nonzero. In the square of the differential the mixed terms cancel, leaving
`d (d (m ⊗ n)) = dM (dM m) ⊗ n + m ⊗ dN (dN n)`, which vanishes for DG modules.

Neither the balancing nor the square formula uses a square law for `dA`, `dM`, or `dN`, so the
differential `leibnizDifferential` is built from the two graded Leibniz rules alone. Curved DG
modules satisfy the same Leibniz rules, and their tensor differential is this one; its square
vanishes there because the curvature actions cancel across the tensor sign
(`TauCeti.BalancedTensorProduct.curvedDifferential_comp_self`).

This file constructs that endomorphism over an arbitrary commutative ground ring and proves
compatibility with tensoring module maps and homotopies, also from the Leibniz rules alone, and
with tensoring DG module morphisms and with the regular-module unit
identifications. It supplies the differential on the underlying balanced module; a grading
on the quotient and outer bimodule actions are separate constructions.

## Main definitions

* `TauCeti.BalancedTensorProduct.leibnizDifferential`: the signed tensor differential of two
  differentials obeying the right and left graded Leibniz rules for one algebra differential.
* `TauCeti.BalancedTensorProduct.differential`: its instance for a right and a left DG module.

## Main results

* `TauCeti.BalancedTensorProduct.leibnizDifferential_leibnizDifferential_tmul`: the square of
  the tensor differential is `dM² ⊗ 1 + 1 ⊗ dN²`.
* `TauCeti.BalancedTensorProduct.differential_comp_self`: for DG modules it squares to zero.
* `TauCeti.BalancedTensorProduct.leibnizDifferential_naturality`: tensoring maps commuting with
  the differentials commutes with the tensor differential.
* `TauCeti.BalancedTensorProduct.map_eq_leibnizDifferential_comp_map_add_map_comp_add`: a
  homotopy `k` in the first factor gives the homotopy `k ⊗ g` of tensored maps.
* `TauCeti.BalancedTensorProduct.tmul_sub_tmul_eq_add_koszulMapRight`: an odd graded linear
  homotopy `k` in the second factor gives the homotopy `m ⊗ x ↦ (-1) ^ |m| m ⊗ k x`
  (`TauCeti.BalancedTensorProduct.koszulMapRight`) for any tensor differentials given by the
  signed Leibniz formula on pure tensors.

## References

* B. Keller, *Deriving DG categories*, Section 6.1.
-/

public section

open MulOpposite DirectSum

namespace TauCeti.BalancedTensorProduct

variable {R A M N : Type*} [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {dA : A →ₗ[R] A}
  {hA : IsDGAlgebra 𝒜 dA} {ℳ : ℤ → Submodule R M} {ℳN : ℤ → Submodule R N}
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition ℳN]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  [SetLike.GradedSMul 𝒜 ℳN]
  {dM : M →ₗ[R] M} {dN : N →ₗ[R] N}

private noncomputable def differentialBilinear :
    M →ₗ[R] N →ₗ[R] BalancedTensorProduct R A M N :=
  (mk R A).comp dM +
    ((mk R A).comp ((InternalGrading.ofDecomposition ℳ).koszulTwist 1)).compl₂ dN

omit [Algebra R A] [IsScalarTower R Aᵐᵒᵖ M] [IsScalarTower R A N] in
private theorem differentialBilinear_apply (m : M) (n : N) :
    differentialBilinear (R := R) (A := A) (ℳ := ℳ) (dM := dM) (dN := dN) m n =
      tmul R A (dM m) n +
        tmul R A ((InternalGrading.ofDecomposition ℳ).koszulTwist 1 m) (dN n) := by
  simp [differentialBilinear]

omit [Algebra R A] [IsScalarTower R Aᵐᵒᵖ M] [IsScalarTower R A N] in
private theorem differentialBilinear_of_mem {q : ℤ} {m : M} (hm : m ∈ ℳ q) (n : N) :
    differentialBilinear (R := R) (A := A) (ℳ := ℳ) (dM := dM) (dN := dN) m n =
      tmul R A (dM m) n + (((q.negOnePow : ℤ) : R)) • tmul R A m (dN n) := by
  rw [differentialBilinear_apply,
    (InternalGrading.ofDecomposition ℳ).koszulTwist_apply_of_mem
      (by simpa only [InternalGrading.ofDecomposition_piece] using hm) 1, one_mul, smul_tmul]

omit [IsScalarTower R Aᵐᵒᵖ M] [IsScalarTower R A N] in
private theorem differentialBilinear_balanced_of_mem
    (hM : ∀ {q : ℤ} {x : M}, x ∈ ℳ q → ∀ a : A,
      dM (op a • x) = op a • dM x + q.negOnePow • (op (dA a) • x))
    (hN : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ x : N,
      dN (a • x) = dA a • x + p.negOnePow • (a • dN x))
    {p q : ℤ} {a : A} {m : M} (ha : a ∈ 𝒜 p) (hm : m ∈ ℳ q) (n : N) :
    differentialBilinear (R := R) (A := A) (ℳ := ℳ) (dM := dM) (dN := dN) (op a • m) n =
      differentialBilinear (R := R) (A := A) (ℳ := ℳ) (dM := dM) (dN := dN) m (a • n) := by
  have hop : op a ∈ (InternalGrading.ofDecomposition 𝒜).opposite.piece p :=
    ((InternalGrading.ofDecomposition 𝒜).op_mem_opposite_piece_iff p a).2
      (by simpa only [InternalGrading.ofDecomposition_piece] using ha)
  rw [differentialBilinear_of_mem (SetLike.GradedSMul.smul_mem hop hm),
    differentialBilinear_of_mem hm, hM hm a, hN ha n]
  simp only [negOnePow_smul_eq_negOnePowCast_smul (R := R), negOnePowCast_eq_intCast,
    add_tmul, smul_tmul, tmul_add, tmul_smul, balance, smul_add, smul_smul,
    vadd_eq_add, Int.negOnePow_add, Units.val_mul, Int.cast_mul]
  module

omit [IsScalarTower R Aᵐᵒᵖ M] [IsScalarTower R A N] in
private theorem differentialBilinear_balanced
    (hM : ∀ {q : ℤ} {x : M}, x ∈ ℳ q → ∀ a : A,
      dM (op a • x) = op a • dM x + q.negOnePow • (op (dA a) • x))
    (hN : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ x : N,
      dN (a • x) = dA a • x + p.negOnePow • (a • dN x))
    (a : A) (m : M) (n : N) :
    differentialBilinear (R := R) (A := A) (ℳ := ℳ) (dM := dM) (dN := dN) (op a • m) n =
      differentialBilinear (R := R) (A := A) (ℳ := ℳ) (dM := dM) (dN := dN) m (a • n) := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 a, ← DirectSum.sum_support_decompose ℳ m]
  conv_rhs => rw [← DirectSum.sum_support_decompose 𝒜 a, ← DirectSum.sum_support_decompose ℳ m]
  simp only [Finset.op_sum, Finset.sum_smul, Finset.smul_sum, map_sum, LinearMap.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  exact differentialBilinear_balanced_of_mem hM hN (SetLike.coe_mem _) (SetLike.coe_mem _) n

section Leibniz

omit [IsScalarTower R Aᵐᵒᵖ M] [IsScalarTower R A N]

variable
  (hM : ∀ {q : ℤ} {x : M}, x ∈ ℳ q → ∀ a : A,
    dM (op a • x) = op a • dM x + q.negOnePow • (op (dA a) • x))
  (hN : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ x : N,
    dN (a • x) = dA a • x + p.negOnePow • (a • dN x))

/-- The signed tensor differential `d (m ⊗ n) = dM m ⊗ n + (-1)^|m| m ⊗ dN n` on the ordinary
balanced tensor product, for differentials `dM` and `dN` obeying the right and the left graded
Leibniz rule for one algebra differential `dA`. These two rules are exactly what makes the
formula balanced; no square law is assumed, so the construction serves differential graded and
curved differential graded modules alike. -/
noncomputable def leibnizDifferential : Module.End R (BalancedTensorProduct R A M N) :=
  lift (differentialBilinear (R := R) (A := A) (ℳ := ℳ) (dM := dM) (dN := dN))
    (differentialBilinear_balanced hM hN)

/-- On arbitrary pure tensors, the sign is represented by the grading's Koszul twist. -/
@[simp]
theorem leibnizDifferential_tmul (m : M) (n : N) :
    leibnizDifferential hM hN (tmul R A m n) = tmul R A (dM m) n +
      tmul R A ((InternalGrading.ofDecomposition ℳ).koszulTwist 1 m) (dN n) := by
  rw [leibnizDifferential, lift_tmul, differentialBilinear_apply]

/-- The tensor differential has the usual sign on a homogeneous left factor. -/
theorem leibnizDifferential_tmul_of_mem {q : ℤ} {m : M} (hm : m ∈ ℳ q) (n : N) :
    leibnizDifferential hM hN (tmul R A m n) =
      tmul R A (dM m) n + (((q.negOnePow : ℤ) : R)) • tmul R A m (dN n) := by
  rw [leibnizDifferential, lift_tmul, differentialBilinear_of_mem hm]

/-- **The square of the tensor differential.** When `dM` raises degree by one, the mixed terms
of the square cancel by the Koszul sign, so the square of the tensor differential is
`dM² ⊗ 1 + 1 ⊗ dN²`. -/
theorem leibnizDifferential_leibnizDifferential_tmul (hMd : LinearMap.IsHomogeneous dM ℳ ℳ 1)
    (m : M) (n : N) :
    leibnizDifferential hM hN (leibnizDifferential hM hN (tmul R A m n)) =
      tmul R A (dM (dM m)) n + tmul R A m (dN (dN n)) := by
  have key :
      ((leibnizDifferential hM hN ∘ₗ leibnizDifferential hM hN) ∘ₗ (mk R A).flip n :
        M →ₗ[R] BalancedTensorProduct R A M N) =
      (mk R A).flip n ∘ₗ (dM ∘ₗ dM) + (mk R A).flip (dN (dN n)) := by
    apply (InternalGrading.ofDecomposition ℳ).linearMap_ext
    intro q x hx
    rw [InternalGrading.ofDecomposition_piece] at hx
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.flip_apply, mk_apply]
    rw [leibnizDifferential_tmul_of_mem hM hN hx, map_add, map_smul,
      leibnizDifferential_tmul_of_mem hM hN (hMd.map_mem hx),
      leibnizDifferential_tmul_of_mem hM hN hx, Int.negOnePow_succ]
    simp only [Units.val_neg, Int.cast_neg, neg_smul, smul_add, smul_smul, ← Int.cast_mul,
      ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one, one_smul]
    abel
  simpa only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.flip_apply, mk_apply]
    using LinearMap.congr_fun key m

section Map

variable {M' N' : Type*}
  [AddCommGroup M'] [Module R M'] [Module Aᵐᵒᵖ M']
  [AddCommGroup N'] [Module R N'] [Module A N']
  {ℳ' : ℤ → Submodule R M'} {ℳN' : ℤ → Submodule R N'}
  [DirectSum.Decomposition ℳ'] [DirectSum.Decomposition ℳN']
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ']
  [SetLike.GradedSMul 𝒜 ℳN'] {dM' : M' →ₗ[R] M'} {dN' : N' →ₗ[R] N'}
  (hM' : ∀ {q : ℤ} {x : M'}, x ∈ ℳ' q → ∀ a : A,
    dM' (op a • x) = op a • dM' x + q.negOnePow • (op (dA a) • x))
  (hN' : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ x : N',
    dN' (a • x) = dA a • x + p.negOnePow • (a • dN' x))
  {g : N →ₗ[R] N'} (hg : ∀ (a : A) n, g (a • n) = a • g n)

/-- Tensoring equivariant maps commuting with the differentials, the first of degree zero,
commutes with the tensor differential. -/
theorem leibnizDifferential_naturality (f : M →ₗ[R] M')
    (hf : ∀ (a : A) m, f (op a • m) = op a • f m) (hf₀ : LinearMap.IsHomogeneous f ℳ ℳ' 0)
    (hfd : dM' ∘ₗ f = f ∘ₗ dM) (hgd : dN' ∘ₗ g = g ∘ₗ dN) :
    leibnizDifferential hM' hN' ∘ₗ map f g hf hg = map f g hf hg ∘ₗ leibnizDifferential hM hN := by
  refine hom_ext_of_mem (ℳ := ℳ) fun {q x} hx n ↦ ?_
  have hfx : f x ∈ ℳ' q := by simpa only [add_zero] using hf₀.map_mem hx
  simp only [LinearMap.comp_apply, map_tmul]
  rw [leibnizDifferential_tmul_of_mem hM' hN' hfx, leibnizDifferential_tmul_of_mem hM hN hx,
    map_add, map_smul, map_tmul, map_tmul]
  simp only [← LinearMap.comp_apply, hfd, hgd]

/-- **Homotopies in the first factor.** If equivariant maps satisfy
`f₁ = dM' ∘ k + k ∘ dM + f₂` for an equivariant map `k` of degree `-1`, and `g` commutes with the
differentials, then tensoring with `g` gives `f₁ ⊗ g = d ∘ (k ⊗ g) + (k ⊗ g) ∘ d + f₂ ⊗ g`. No
Koszul sign enters `k ⊗ g`, because `k` acts on the first factor. -/
theorem map_eq_leibnizDifferential_comp_map_add_map_comp_add
    {f₁ f₂ k : M →ₗ[R] M'} (hf₁ : ∀ (a : A) m, f₁ (op a • m) = op a • f₁ m)
    (hf₂ : ∀ (a : A) m, f₂ (op a • m) = op a • f₂ m)
    (hk : ∀ (a : A) m, k (op a • m) = op a • k m) (hk₁ : LinearMap.IsHomogeneous k ℳ ℳ' (-1))
    (hfk : f₁ = dM' ∘ₗ k + k ∘ₗ dM + f₂) (hgd : dN' ∘ₗ g = g ∘ₗ dN) :
    map f₁ g hf₁ hg = leibnizDifferential hM' hN' ∘ₗ map k g hk hg +
      map k g hk hg ∘ₗ leibnizDifferential hM hN + map f₂ g hf₂ hg := by
  refine hom_ext_of_mem (ℳ := ℳ) fun hx n ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply, map_tmul]
  rw [leibnizDifferential_tmul_of_mem hM' hN' (hk₁.map_mem hx),
    leibnizDifferential_tmul_of_mem hM hN hx, map_add, map_smul, map_tmul, map_tmul, hfk]
  simp only [← LinearMap.comp_apply, hgd, LinearMap.add_apply, add_tmul,
    Int.negOnePow_add, Int.negOnePow_neg, Int.negOnePow_one, mul_neg, mul_one, Units.val_neg,
    Int.cast_neg, neg_smul]
  abel

end Map

section SecondFactor

variable {N' : Type*} [AddCommGroup N'] [Module R N'] [Module A N'] {ℳN' : ℤ → Submodule R N'}
  [DirectSum.Decomposition ℳN'] [SetLike.GradedSMul 𝒜 ℳN'] {dN' : N' →ₗ[R] N'}
  {k : N →ₗ[R] N'}

/-- Pairing the Koszul twist of the first factor with an odd graded linear map of the second is
balanced: the two signs picked up by an element of the algebra agree. -/
private theorem koszulTwist_tmul_balanced
    (hk : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ x : N, k (a • x) = p.negOnePow • (a • k x))
    (a : A) (m : M) (x : N) :
    tmul R A ((InternalGrading.ofDecomposition ℳ).koszulTwist 1 (op a • m)) (k x) =
      tmul R A ((InternalGrading.ofDecomposition ℳ).koszulTwist 1 m) (k (a • x)) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add a b ha hb => simp only [op_add, add_smul, map_add, add_tmul, tmul_add, ha, hb]
  | @homogeneous p a =>
    induction m using DirectSum.Decomposition.inductionOn ℳ with
    | zero => simp
    | add m m' hm hm' => simp only [smul_add, map_add, add_tmul, hm, hm']
    | @homogeneous q m =>
      have hop : op (a : A) ∈ (InternalGrading.ofDecomposition 𝒜).opposite.piece p :=
        ((InternalGrading.ofDecomposition 𝒜).op_mem_opposite_piece_iff p a).2
          (by simpa only [InternalGrading.ofDecomposition_piece] using a.2)
      have ham : op (a : A) • (m : M) ∈ (InternalGrading.ofDecomposition ℳ).piece (p + q) := by
        simpa only [InternalGrading.ofDecomposition_piece, vadd_eq_add] using
          SetLike.GradedSMul.smul_mem hop m.2
      have hm : (m : M) ∈ (InternalGrading.ofDecomposition ℳ).piece q := by
        simpa only [InternalGrading.ofDecomposition_piece] using m.2
      rw [InternalGrading.koszulTwist_one_apply_of_mem _ ham,
        InternalGrading.koszulTwist_one_apply_of_mem _ hm, hk a.2, Int.negOnePow_add]
      simp only [negOnePow_smul_eq_negOnePowCast_smul (R := R), negOnePowCast_eq_intCast,
        smul_tmul, tmul_smul, balance, Units.val_mul, Int.cast_mul, mul_smul]

variable (ℳ) in
/-- An odd graded linear map `k` in the second factor, tensored with the identity of the first:
`m ⊗ x ↦ (-1) ^ |m| m ⊗ k x`. The sign is the Koszul sign of `k` passing `m`, and it makes the map
well defined on the balanced tensor product. -/
noncomputable def koszulMapRight
    (hk : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ x : N, k (a • x) = p.negOnePow • (a • k x)) :
    BalancedTensorProduct R A M N →ₗ[R] BalancedTensorProduct R A M N' :=
  lift (((mk R A).comp ((InternalGrading.ofDecomposition ℳ).koszulTwist 1)).compl₂ k)
    (fun a m x ↦ by
      simpa only [LinearMap.compl₂_apply, LinearMap.comp_apply, mk_apply] using
        koszulTwist_tmul_balanced hk a m x)

/-- On pure tensors, the first factor acquires its Koszul twist. -/
@[simp]
theorem koszulMapRight_tmul
    (hk : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ x : N, k (a • x) = p.negOnePow • (a • k x))
    (m : M) (x : N) :
    koszulMapRight ℳ hk (tmul R A m x) =
      tmul R A ((InternalGrading.ofDecomposition ℳ).koszulTwist 1 m) (k x) := by
  simp [koszulMapRight]

/-- On a homogeneous first factor of degree `q`, the Koszul twist is the sign `(-1) ^ q`. -/
theorem koszulMapRight_tmul_of_mem
    (hk : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ x : N, k (a • x) = p.negOnePow • (a • k x))
    {q : ℤ} {m : M} (hm : m ∈ ℳ q) (x : N) :
    koszulMapRight ℳ hk (tmul R A m x) = ((q.negOnePow : ℤ) : R) • tmul R A m (k x) := by
  rw [koszulMapRight_tmul, (InternalGrading.ofDecomposition ℳ).koszulTwist_apply_of_mem
      (by simpa only [InternalGrading.ofDecomposition_piece] using hm) 1, one_mul, smul_tmul]

/-- **Homotopies in the second factor.** Let `D` and `D'` be endomorphisms of `M ⊗_A N` and
`M ⊗_A N'` given on homogeneous pure tensors by the signed tensor differential
`m ⊗ x ↦ dM m ⊗ x + (-1) ^ |m| m ⊗ d x`, such as `leibnizDifferential`. If equivariant maps
satisfy `g₁ - g₂ = dN' ∘ k + k ∘ dN` for an odd graded linear map `k`, then on pure tensors
`m ⊗ g₁ x - m ⊗ g₂ x = D' (h (m ⊗ x)) + h (D (m ⊗ x))` for the Koszul-signed tensor
`h = koszulMapRight ℳ hk` of `k`. -/
theorem tmul_sub_tmul_eq_add_koszulMapRight (hMd : LinearMap.IsHomogeneous dM ℳ ℳ 1)
    (hk : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ x : N, k (a • x) = p.negOnePow • (a • k x))
    {g₁ g₂ : N →ₗ[R] N'} (hgk : ∀ x, g₁ x - g₂ x = dN' (k x) + k (dN x))
    {D : BalancedTensorProduct R A M N →ₗ[R] BalancedTensorProduct R A M N}
    {D' : BalancedTensorProduct R A M N' →ₗ[R] BalancedTensorProduct R A M N'}
    (hD : ∀ {q : ℤ} {m : M}, m ∈ ℳ q → ∀ x : N,
      D (tmul R A m x) = tmul R A (dM m) x + q.negOnePow • tmul R A m (dN x))
    (hD' : ∀ {q : ℤ} {m : M}, m ∈ ℳ q → ∀ x : N',
      D' (tmul R A m x) = tmul R A (dM m) x + q.negOnePow • tmul R A m (dN' x))
    (m : M) (x : N) :
    tmul R A m (g₁ x) - tmul R A m (g₂ x) =
      D' (koszulMapRight ℳ hk (tmul R A m x)) + koszulMapRight ℳ hk (D (tmul R A m x)) := by
  induction m using DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp [zero_tmul]
  | add m m' hm hm' =>
    simp only [add_tmul, map_add]
    rw [add_sub_add_comm, hm, hm']
    abel
  | @homogeneous q m =>
    have hsub (u v : N') : tmul R A (m : M) (u - v) = tmul R A (m : M) u - tmul R A (m : M) v := by
      simpa only [mk_apply] using map_sub (mk R A (m : M)) u v
    rw [← hsub, hgk, tmul_add, koszulMapRight_tmul_of_mem hk m.2, map_smul, hD' m.2, hD m.2,
      map_add, map_zsmul_unit, koszulMapRight_tmul_of_mem hk (hMd.map_mem m.2),
      koszulMapRight_tmul_of_mem hk m.2, Int.negOnePow_succ]
    -- The two terms involving `dM m` cancel, and the remaining sign appears twice.
    simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul R, Units.val_neg, Int.cast_neg,
      neg_smul, smul_add, smul_smul, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self,
      Units.val_one, Int.cast_one, one_smul]
    abel

end SecondFactor

end Leibniz

/-- The signed tensor differential on the ordinary balanced tensor product of a right and a
left DG module. No flatness assumption is needed for this underived construction. -/
noncomputable def differential (hM : IsDGRightModule hA ℳ dM) (hN : IsDGLeftModule hA ℳN dN) :
    Module.End R (BalancedTensorProduct R A M N) :=
  leibnizDifferential hM.leibniz hN.leibniz

/-- The DG tensor differential is the tensor differential of the two Leibniz rules. -/
theorem differential_eq_leibnizDifferential (hM : IsDGRightModule hA ℳ dM)
    (hN : IsDGLeftModule hA ℳN dN) :
    differential hM hN = leibnizDifferential hM.leibniz hN.leibniz :=
  (rfl)

/-- On arbitrary pure tensors, the sign is represented by the grading's Koszul twist. -/
@[simp]
theorem differential_tmul (hM : IsDGRightModule hA ℳ dM) (hN : IsDGLeftModule hA ℳN dN)
    (m : M) (n : N) :
    differential hM hN (tmul R A m n) = tmul R A (dM m) n +
      tmul R A ((InternalGrading.ofDecomposition ℳ).koszulTwist 1 m) (dN n) :=
  leibnizDifferential_tmul hM.leibniz hN.leibniz m n

/-- The tensor differential has the usual sign on a homogeneous left factor. -/
theorem differential_tmul_of_mem (hM : IsDGRightModule hA ℳ dM)
    (hN : IsDGLeftModule hA ℳN dN) {q : ℤ} {m : M} (hm : m ∈ ℳ q) (n : N) :
    differential hM hN (tmul R A m n) =
      tmul R A (dM m) n + (((q.negOnePow : ℤ) : R)) • tmul R A m (dN n) :=
  leibnizDifferential_tmul_of_mem hM.leibniz hN.leibniz hm n

/-- The differential on the balanced tensor product squares to zero. -/
@[simp]
theorem differential_comp_self (hM : IsDGRightModule hA ℳ dM)
    (hN : IsDGLeftModule hA ℳN dN) :
    differential hM hN ∘ₗ differential hM hN = 0 := by
  apply hom_ext
  intro m n
  rw [LinearMap.comp_apply, differential,
    leibnizDifferential_leibnizDifferential_tmul _ _ hM.isHomogeneous, hM.sq_zero, hN.sq_zero]
  simp

/-- Applying the tensor differential twice gives zero. -/
@[simp]
theorem differential_sq_zero (hM : IsDGRightModule hA ℳ dM) (hN : IsDGLeftModule hA ℳN dN)
    (z : BalancedTensorProduct R A M N) : differential hM hN (differential hM hN z) = 0 :=
  LinearMap.congr_fun (differential_comp_self hM hN) z

section Naturality

variable {M' N' : Type*}
  [AddCommGroup M'] [Module R M'] [Module Aᵐᵒᵖ M'] [IsScalarTower R Aᵐᵒᵖ M']
  [AddCommGroup N'] [Module R N'] [Module A N'] [IsScalarTower R A N']
  {ℳ' : ℤ → Submodule R M'} {ℳN' : ℤ → Submodule R N'}
  [DirectSum.Decomposition ℳ'] [DirectSum.Decomposition ℳN']
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ']
  [SetLike.GradedSMul 𝒜 ℳN'] {dM' : M' →ₗ[R] M'} {dN' : N' →ₗ[R] N'}

/-- Tensoring equivariant chain maps, with the first map of degree zero, commutes with the balanced
tensor differential. Only the first map's degree is needed for this differential identity. -/
theorem differential_naturality (hM : IsDGRightModule hA ℳ dM) (hN : IsDGLeftModule hA ℳN dN)
    (hM' : IsDGRightModule hA ℳ' dM') (hN' : IsDGLeftModule hA ℳN' dN')
    (f : M →ₗ[R] M') (g : N →ₗ[R] N')
    (hf : ∀ (a : A) m, f (op a • m) = op a • f m)
    (hg : ∀ (a : A) n, g (a • n) = a • g n)
    (hf₀ : LinearMap.IsHomogeneous f ℳ ℳ' 0)
    (hfd : dM' ∘ₗ f = f ∘ₗ dM) (hgd : dN' ∘ₗ g = g ∘ₗ dN) :
    differential hM' hN' ∘ₗ map f g hf hg = map f g hf hg ∘ₗ differential hM hN :=
  leibnizDifferential_naturality hM.leibniz hN.leibniz hM'.leibniz hN'.leibniz hg f hf hf₀ hfd hgd

end Naturality

/-- The left regular-module unit identification commutes with the tensor differential. -/
@[simp]
theorem lid_comp_differential (hA : IsDGAlgebra 𝒜 dA) (hN : IsDGLeftModule hA ℳN dN) :
    (lid R A N).toLinearMap ∘ₗ differential hA.isDGRightModule hN =
      dN ∘ₗ (lid R A N).toLinearMap := by
  refine hom_ext_of_mem (ℳ := 𝒜) fun hx n ↦ ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [differential_tmul_of_mem hA.isDGRightModule hN hx, map_add, map_smul,
    lid_tmul, lid_tmul, lid_tmul, hN.leibniz hx n,
    negOnePow_smul_eq_negOnePowCast_smul (R := R), negOnePowCast_eq_intCast]

/-- The right regular-module unit identification commutes with the tensor differential. -/
@[simp]
theorem rid_comp_differential (hA : IsDGAlgebra 𝒜 dA) (hM : IsDGRightModule hA ℳ dM) :
    (rid R A M).toLinearMap ∘ₗ differential hM hA.isDGLeftModule =
      dM ∘ₗ (rid R A M).toLinearMap := by
  refine hom_ext_of_mem (ℳ := ℳ) fun hx a ↦ ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [differential_tmul_of_mem hM hA.isDGLeftModule hx, map_add, map_smul,
    rid_tmul, rid_tmul, rid_tmul, hM.leibniz hx a,
    negOnePow_smul_eq_negOnePowCast_smul (R := R), negOnePowCast_eq_intCast]

end TauCeti.BalancedTensorProduct
