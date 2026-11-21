/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import TauCeti.Algebra.Lie.CartanInvolution.Basic
import Mathlib.Algebra.Lie.Derivation.Killing
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.InnerProductSpace.Spectral.Relative
import TauCeti.LinearAlgebra.Eigenspace.DiagonalBasis

/-!
# Conjugacy of Cartan involutions

Any two Cartan involutions `θ` and `θ'` of a real semisimple Lie algebra `L` are conjugate by an
inner automorphism of the form `e^{ad Z}` with `Z ∈ θ.cartanP`.

The proof follows Knapp (Chapter VI, §2, Theorem 6.16): the composition `N = θ ∘ θ'` is
self-adjoint for the inner product `B_θ(x, y) = -B(x, θ y)`, so `P = N²` is symmetric and strictly
positive definite for `B_θ`. Diagonalizing `P` over `ℝ` produces a basis of `P`-eigenvectors with
strictly positive eigenvalues `λᵢ`. Defining `D = log P` and `φ = P^{-1/4}` on this basis:

1. `D` is a derivation of `L` (since `P` is a Lie automorphism and `log(λᵢ λⱼ) = log λᵢ + log λⱼ`),
   hence inner (`D = ad Z₀`) because `L` is Killing; anti-commutation of `D` with `θ` forces
   `Z₀ ∈ θ.cartanP`, and `Z = -(1 / 4) • Z₀ ∈ θ.cartanP`.
2. `φ = P^{-1/4}` is a Lie automorphism of `L` acting on every `ad Z`-eigenvector of eigenvalue `μ`
   as scalar multiplication by `Real.exp μ`.
3. The conjugate Cartan involution `θ₁ = φ ∘ θ ∘ φ⁻¹` commutes with `θ'`, so `θ₁ = θ'` by
   `LieEquiv.IsCartanInvolution.eq_of_commute`.

This gives the norm-free algebraic form (`LieEquiv.IsCartanInvolution.exists_mem_cartanP_conj_eq`),
which immediately specializes to `Ad (lieExp Z)` on the Lie algebra of a real Lie group via
`LieEquiv.IsCartanInvolution.iSup_eigenspace_ad_eq_top`.

## Main results

* `LieEquiv.IsCartanInvolution.exists_mem_cartanP_conj_eq`: any two Cartan involutions `θ, θ'` of
  a real Lie algebra satisfy `θ' (φ y) = φ (θ y)` for a Lie automorphism `φ` and `Z ∈ θ.cartanP`
  such that `φ` acts as `Real.exp μ` on every `μ`-eigenvector of `ad Z`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Progress in Mathematics 140,
  Birkhäuser, 2002, Chapter VI, §2, Theorem 6.16.
* S. Helgason, *Differential Geometry, Lie Groups, and Symmetric Spaces*, Graduate Studies in
  Mathematics 34, AMS, 2001, Chapter III, §7, Theorem 7.2.
-/

public section

open LieAlgebra Module
open scoped InnerProductSpace

namespace LieEquiv

section Helpers

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- For two involutive automorphisms `θ` and `θ'`, `θ ∘ θ'` is self-adjoint for
`θ.cartanBilinForm`. -/
private theorem cartanBilinForm_trans_left {θ θ' : L ≃ₗ⁅ℝ⁆ L}
    (hθ : Function.Involutive θ) (hθ' : Function.Involutive θ') (x y : L) :
    θ.cartanBilinForm (θ (θ' x)) y = θ.cartanBilinForm x (θ (θ' y)) := by
  simp only [cartanBilinForm_apply, hθ (θ' y)]
  rw [killingForm_of_equiv_apply θ (θ' x) y, ← killingForm_of_equiv_apply θ' x (θ' y), hθ' y]

/-- Diagonalizing `P = (θ ∘ θ')²` with respect to `B_θ`: produces a basis of `P`-eigenvectors
with strictly positive eigenvalues. -/
private theorem exists_basis_eigenvector_sq_trans {θ θ' : L ≃ₗ⁅ℝ⁆ L}
    (hθ : θ.IsCartanInvolution) (hθ' : θ'.IsCartanInvolution) :
    let P := (θ'.trans θ).trans (θ'.trans θ)
    ∃ (b : Module.Basis (Fin (finrank ℝ L)) ℝ L) (lam : Fin (finrank ℝ L) → ℝ),
      (∀ i, P (b i) = lam i • b i) ∧ (∀ i, 0 < lam i) := by
  have := hθ.finite
  let N : L ≃ₗ⁅ℝ⁆ L := θ'.trans θ
  let P : L ≃ₗ⁅ℝ⁆ L := N.trans N
  have hN_symm (x y : L) : θ.cartanBilinForm (N x) y = θ.cartanBilinForm x (N y) :=
    cartanBilinForm_trans_left hθ.involutive hθ'.involutive x y
  have hP_symm (x y : L) : θ.cartanBilinForm (P x) y = θ.cartanBilinForm x (P y) := by
    simp only [P, trans_apply]
    rw [hN_symm, hN_symm]
  obtain ⟨e, he⟩ := LinearMap.BilinForm.exists_linearEquiv_euclideanSpace_apply_apply
    hθ.isSymm_cartanBilinForm (fun v hv ↦ hθ.cartanBilinForm_self_pos hv)
  let T : Module.End ℝ (EuclideanSpace ℝ (Fin (finrank ℝ L))) :=
    e.symm.toLinearMap.comp ((P : L →ₗ[ℝ] L).comp e.toLinearMap)
  have hT : T.IsSymmetric := by
    intro x y
    rw [← he (T x) y, ← he x (T y)]
    simp only [T, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact hP_symm (e x) (e y)
  have hn : finrank ℝ (EuclideanSpace ℝ (Fin (finrank ℝ L))) = finrank ℝ L :=
    finrank_euclideanSpace_fin
  let ob := hT.eigenvectorBasis hn
  let lam := hT.eigenvalues hn
  let b : Module.Basis (Fin (finrank ℝ L)) ℝ L := ob.toBasis.map e
  have hbP (i : Fin (finrank ℝ L)) : P (b i) = lam i • b i := by
    have hi := hT.apply_eigenvectorBasis hn i
    have hmap : P (e (ob i)) = e (T (ob i)) := by simp [T]
    have heq := congrArg e hi
    rw [map_smul, ← hmap] at heq
    exact heq
  refine ⟨b, lam, hbP, fun i ↦ ?_⟩
  have hNne : N (b i) ≠ 0 := by
    intro h0
    exact b.ne_zero i (N.injective (h0.trans (map_zero N).symm))
  have hpos : 0 < θ.cartanBilinForm (P (b i)) (b i) := by
    simpa only [P, trans_apply, hN_symm] using hθ.cartanBilinForm_self_pos hNne
  rw [hbP i, map_smul, LinearMap.smul_apply, smul_eq_mul] at hpos
  exact pos_of_mul_pos_left hpos (hθ.cartanBilinForm_self_pos (b.ne_zero i)).le

/-- Conjugation of `P = (θ ∘ θ')²` by `θ` or `θ'` inverts `P`. -/
private theorem sq_trans_apply_inv_of_eigenvector {θ θ' : L ≃ₗ⁅ℝ⁆ L}
    (hθ : Function.Involutive θ) (hθ' : Function.Involutive θ')
    {v : L} {μ : ℝ} (hμ : μ ≠ 0)
    (hv : ((θ'.trans θ).trans (θ'.trans θ)) v = μ • v) :
    ((θ'.trans θ).trans (θ'.trans θ)) (θ v) = μ⁻¹ • θ v ∧
      ((θ'.trans θ).trans (θ'.trans θ)) (θ' v) = μ⁻¹ • θ' v := by
  let N : L ≃ₗ⁅ℝ⁆ L := θ'.trans θ
  let P : L ≃ₗ⁅ℝ⁆ L := N.trans N
  have hθN (x : L) : θ (N x) = N.symm (θ x) := by
    rw [eq_comm, symm_apply_eq]
    simp only [N, trans_apply]
    rw [hθ, hθ']
  have hθ'N (x : L) : θ' (N x) = N.symm (θ' x) := by
    rw [eq_comm, symm_apply_eq]
    simp only [N, trans_apply]
    rw [hθ', hθ]
  have hθP (x : L) : θ (P x) = P.symm (θ x) := by
    calc
      θ (P x) = θ (N (N x)) := rfl
      _ = N.symm (θ (N x)) := hθN (N x)
      _ = N.symm (N.symm (θ x)) := by rw [hθN]
      _ = P.symm (θ x) := rfl
  have hθ'P (x : L) : θ' (P x) = P.symm (θ' x) := by
    calc
      θ' (P x) = θ' (N (N x)) := rfl
      _ = N.symm (θ' (N x)) := hθ'N (N x)
      _ = N.symm (N.symm (θ' x)) := by rw [hθ'N]
      _ = P.symm (θ' x) := rfl
  constructor
  · have h := congrArg P (hθP v)
    rw [P.apply_symm_apply, hv, map_smul, map_smul] at h
    calc
      P (θ v) = μ⁻¹ • (μ • P (θ v)) := by rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]
      _ = μ⁻¹ • θ v := congrArg (μ⁻¹ • ·) h
  · have h := congrArg P (hθ'P v)
    rw [P.apply_symm_apply, hv, map_smul, map_smul] at h
    calc
      P (θ' v) = μ⁻¹ • (μ • P (θ' v)) := by rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]
      _ = μ⁻¹ • θ' v := congrArg (μ⁻¹ • ·) h

/-- Building the inner derivation generator `Z ∈ θ.cartanP` for `log P` scaled by `-(1 / 4)`. -/
private theorem exists_mem_cartanP_ad_basis {ι : Type*} [Finite ι]
    {θ θ' : L ≃ₗ⁅ℝ⁆ L} (hθ : θ.IsCartanInvolution) (hθ' : θ'.IsCartanInvolution)
    (b : Module.Basis ι ℝ L) {lam : ι → ℝ}
    (hb : ∀ i, ((θ'.trans θ).trans (θ'.trans θ)) (b i) = lam i • b i)
    (hlam : ∀ i, 0 < lam i) :
    ∃ Z ∈ θ.cartanP, ∀ i, ⁅Z, b i⁆ = (-(1 / 4 : ℝ) * Real.log (lam i)) • b i := by
  let _ := Fintype.ofFinite ι
  have := hθ.finite
  have := hθ.isKilling
  let P : L ≃ₗ⁅ℝ⁆ L := (θ'.trans θ).trans (θ'.trans θ)
  let Dlin : L →ₗ[ℝ] L := b.constr ℝ fun i ↦ Real.log (lam i) • b i
  have hD_basis (i : ι) : Dlin (b i) = Real.log (lam i) • b i := b.constr_basis ℝ _ i
  have hD_eig {v : L} {μ : ℝ} (hv : P v = μ • v) : Dlin v = Real.log μ • v :=
    b.apply_eq_smul_of_apply_eq_smul (f := (P : L →ₗ[ℝ] L)) hb hD_basis hv
  have hD_lie_basis (i j : ι) : Dlin ⁅b i, b j⁆ = ⁅Dlin (b i), b j⁆ + ⁅b i, Dlin (b j)⁆ := by
    have hP_lie : P ⁅b i, b j⁆ = (lam i * lam j) • ⁅b i, b j⁆ := by
      rw [map_lie, hb i, hb j, smul_lie, lie_smul, smul_smul]
    rw [hD_eig hP_lie, Real.log_mul (hlam i).ne' (hlam j).ne', add_smul,
      hD_basis, hD_basis, smul_lie, lie_smul]
  let D : LieDerivation ℝ L L :=
    { toLinearMap := Dlin
      leibniz' := fun x y ↦ by
        rw [← lie_skew y (Dlin x), sub_neg_eq_add, add_comm]
        conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
        conv_rhs => rw [← b.sum_repr x, ← b.sum_repr y]
        simp only [sum_lie_sum, map_sum, map_smul, smul_lie, lie_smul, hD_lie_basis, smul_add,
          Finset.sum_add_distrib] }
  obtain ⟨Z₀, hZ₀⟩ := LieDerivation.IsKilling.exists_eq_ad D
  have hZ₀_apply (y : L) : ⁅Z₀, y⁆ = Dlin y := by
    simpa [D] using congrArg (fun f : LieDerivation ℝ L L ↦ f y) hZ₀
  have hD_anti (y : L) : Dlin (θ y) = -θ (Dlin y) := by
    have hlin : Dlin.comp (θ : L →ₗ[ℝ] L) = -((θ : L →ₗ[ℝ] L).comp Dlin) := by
      refine b.ext fun i ↦ ?_
      have hPθ := (sq_trans_apply_inv_of_eigenvector hθ.involutive hθ'.involutive
        (hlam i).ne' (hb i)).1
      simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearEquiv.coe_coe,
        coe_toLinearEquiv, hD_eig hPθ, Real.log_inv, hD_basis, map_smul, neg_smul]
    simpa using LinearMap.congr_fun hlin y
  have hZ₀P : Z₀ ∈ θ.cartanP := by
    have hcent : θ Z₀ + Z₀ ∈ center ℝ L := by
      rw [LieModule.mem_maxTrivSubmodule]
      intro w
      have h1 : ⁅θ Z₀ + Z₀, w⁆ = 0 := by
        calc
          ⁅θ Z₀ + Z₀, w⁆ = ⁅θ Z₀, θ (θ w)⁆ + ⁅Z₀, w⁆ := by
            rw [add_lie, hθ.involutive w]
          _ = θ ⁅Z₀, θ w⁆ + Dlin w := by
            rw [← map_lie θ, hZ₀_apply w]
          _ = θ (Dlin (θ w)) + Dlin w := by rw [hZ₀_apply (θ w)]
          _ = θ (-θ (Dlin w)) + Dlin w := by rw [hD_anti]
          _ = 0 := by rw [map_neg, hθ.involutive, neg_add_cancel]
      rw [← lie_skew, h1, neg_zero]
    rw [hθ.center_eq_bot, LieSubmodule.mem_bot] at hcent
    exact mem_cartanP_iff.mpr (eq_neg_of_add_eq_zero_left hcent)
  refine ⟨(-(1 / 4 : ℝ)) • Z₀, θ.cartanP.smul_mem _ hZ₀P, fun i ↦ ?_⟩
  rw [smul_lie, hZ₀_apply, hD_basis, smul_smul]

/-- The Lie automorphism `φ = P^{-1/4}` built from a positive `P`-eigenbasis. -/
private noncomputable def rpowNegQuarterEquiv {ι : Type*} [Fintype ι]
    {P : L ≃ₗ⁅ℝ⁆ L} (b : Module.Basis ι ℝ L) {lam : ι → ℝ}
    (hb : ∀ i, P (b i) = lam i • b i) (hlam : ∀ i, 0 < lam i) : L ≃ₗ⁅ℝ⁆ L :=
  let φlin : L →ₗ[ℝ] L := b.constr ℝ fun i ↦ lam i ^ (-(1 / 4 : ℝ)) • b i
  let ψlin : L →ₗ[ℝ] L := b.constr ℝ fun i ↦ lam i ^ (1 / 4 : ℝ) • b i
  have hφ_basis (i : ι) : φlin (b i) = lam i ^ (-(1 / 4 : ℝ)) • b i := b.constr_basis ℝ _ i
  have hψ_basis (i : ι) : ψlin (b i) = lam i ^ (1 / 4 : ℝ) • b i := b.constr_basis ℝ _ i
  have hφ_eig {v : L} {μ : ℝ} (hv : P v = μ • v) : φlin v = μ ^ (-(1 / 4 : ℝ)) • v :=
    b.apply_eq_smul_of_apply_eq_smul (f := (P : L →ₗ[ℝ] L)) (φ := fun t ↦ t ^ (-(1 / 4 : ℝ)))
      hb hφ_basis hv
  have hleft : Function.LeftInverse ψlin φlin := by
    have hcomp : ψlin.comp φlin = LinearMap.id := b.ext fun i ↦ by
      rw [LinearMap.comp_apply, LinearMap.id_apply, hφ_basis, map_smul, hψ_basis, smul_smul,
        ← Real.rpow_add (hlam i), neg_add_cancel, Real.rpow_zero, one_smul]
    exact fun x ↦ LinearMap.congr_fun hcomp x
  have hright : Function.RightInverse ψlin φlin := by
    have hcomp : φlin.comp ψlin = LinearMap.id := b.ext fun i ↦ by
      rw [LinearMap.comp_apply, LinearMap.id_apply, hψ_basis, map_smul, hφ_basis, smul_smul,
        ← Real.rpow_add (hlam i), add_neg_cancel, Real.rpow_zero, one_smul]
    exact fun x ↦ LinearMap.congr_fun hcomp x
  have hlie (x y : L) : φlin ⁅x, y⁆ = ⁅φlin x, φlin y⁆ := by
    have hbasis (i j : ι) : φlin ⁅b i, b j⁆ = ⁅φlin (b i), φlin (b j)⁆ := by
      have hP_lie : P ⁅b i, b j⁆ = (lam i * lam j) • ⁅b i, b j⁆ := by
        rw [map_lie, hb i, hb j, smul_lie, lie_smul, smul_smul]
      rw [hφ_eig hP_lie, Real.mul_rpow (hlam i).le (hlam j).le,
        hφ_basis, hφ_basis, smul_lie, lie_smul, smul_smul]
    conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
    conv_rhs => rw [← b.sum_repr x, ← b.sum_repr y]
    simp only [sum_lie_sum, map_sum, map_smul, smul_lie, lie_smul, hbasis]
  { toFun := φlin
    invFun := ψlin
    left_inv := hleft
    right_inv := hright
    map_add' := φlin.map_add
    map_smul' := φlin.map_smul
    map_lie' := fun {x y} ↦ hlie x y }

private theorem rpowNegQuarterEquiv_basis {ι : Type*} [Fintype ι]
    {P : L ≃ₗ⁅ℝ⁆ L} (b : Module.Basis ι ℝ L) {lam : ι → ℝ}
    (hb : ∀ i, P (b i) = lam i • b i) (hlam : ∀ i, 0 < lam i) (i : ι) :
    rpowNegQuarterEquiv b hb hlam (b i) = lam i ^ (-(1 / 4 : ℝ)) • b i :=
  b.constr_basis ℝ (fun j ↦ lam j ^ (-(1 / 4 : ℝ)) • b j) i

private theorem rpowNegQuarterEquiv_symm_basis {ι : Type*} [Fintype ι]
    {P : L ≃ₗ⁅ℝ⁆ L} (b : Module.Basis ι ℝ L) {lam : ι → ℝ}
    (hb : ∀ i, P (b i) = lam i • b i) (hlam : ∀ i, 0 < lam i) (i : ι) :
    (rpowNegQuarterEquiv b hb hlam).symm (b i) = lam i ^ (1 / 4 : ℝ) • b i :=
  b.constr_basis ℝ (fun j ↦ lam j ^ (1 / 4 : ℝ) • b j) i

/-- The conjugate Cartan involution `φ ∘ θ ∘ φ⁻¹` commutes with `θ'`, hence equals `θ'`. -/
private theorem conj_rpowNegQuarterEquiv_eq {ι : Type*} [Fintype ι]
    {θ θ' : L ≃ₗ⁅ℝ⁆ L} (hθ : θ.IsCartanInvolution) (hθ' : θ'.IsCartanInvolution)
    (b : Module.Basis ι ℝ L) {lam : ι → ℝ}
    (hb : ∀ i, ((θ'.trans θ).trans (θ'.trans θ)) (b i) = lam i • b i)
    (hlam : ∀ i, 0 < lam i) :
    let φ := rpowNegQuarterEquiv b hb hlam
    φ.symm.trans (θ.trans φ) = θ' := by
  let N : L ≃ₗ⁅ℝ⁆ L := θ'.trans θ
  let P : L ≃ₗ⁅ℝ⁆ L := N.trans N
  let φ := rpowNegQuarterEquiv b hb hlam
  let θ₁ := φ.symm.trans (θ.trans φ)
  have hφ_eig {v : L} {μ : ℝ} (hv : P v = μ • v) : φ v = μ ^ (-(1 / 4 : ℝ)) • v :=
    b.apply_eq_smul_of_apply_eq_smul (f := (P : L →ₗ[ℝ] L)) (g := (φ : L →ₗ[ℝ] L))
      (φ := fun t ↦ t ^ (-(1 / 4 : ℝ))) hb (rpowNegQuarterEquiv_basis b hb hlam) hv
  have hφs_eig {v : L} {μ : ℝ} (hv : P v = μ • v) : φ.symm v = μ ^ (1 / 4 : ℝ) • v :=
    b.apply_eq_smul_of_apply_eq_smul (f := (P : L →ₗ[ℝ] L)) (g := (φ.symm : L →ₗ[ℝ] L))
      (φ := fun t ↦ t ^ (1 / 4 : ℝ)) hb (rpowNegQuarterEquiv_symm_basis b hb hlam) hv
  have hθ₁_eig {v : L} {μ : ℝ} (hμ : 0 < μ) (hv : P v = μ • v) :
      θ₁ v = μ ^ (1 / 2 : ℝ) • θ v := by
    have hPθ := (sq_trans_apply_inv_of_eigenvector hθ.involutive hθ'.involutive hμ.ne' hv).1
    simp only [θ₁, trans_apply]
    rw [hφs_eig hv, map_smul, map_smul, hφ_eig hPθ, Real.inv_rpow hμ.le, Real.rpow_neg hμ.le,
      inv_inv, smul_smul, ← Real.rpow_add hμ]
    norm_num
  have hcomm_basis (i : ι) : θ₁ (θ' (b i)) = θ' (θ₁ (b i)) := by
    have hPθ' := (sq_trans_apply_inv_of_eigenvector hθ.involutive hθ'.involutive
      (hlam i).ne' (hb i)).2
    rw [hθ₁_eig (inv_pos.mpr (hlam i)) hPθ', hθ₁_eig (hlam i) (hb i), map_smul,
      Real.inv_rpow (hlam i).le, ← Real.rpow_neg (hlam i).le]
    have hN : N (b i) = lam i • N.symm (b i) := by
      have hbi : N (N (b i)) = lam i • b i := hb i
      have := congrArg N.symm hbi
      simpa only [symm_apply_apply, map_smul] using this
    have hNval : θ (θ' (b i)) = lam i • θ' (θ (b i)) := by
      have hNs : N.symm (b i) = θ' (θ (b i)) := by
        rw [symm_apply_eq]
        simp only [N, trans_apply]
        rw [hθ'.involutive, hθ.involutive]
      simpa only [N, trans_apply, hNs] using hN
    rw [hNval, smul_smul]
    have hexp : lam i ^ (-(1 / 2 : ℝ)) * lam i = lam i ^ (1 / 2 : ℝ) := by
      calc
        lam i ^ (-(1 / 2 : ℝ)) * lam i = lam i ^ (-(1 / 2 : ℝ)) * lam i ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = lam i ^ (-(1 / 2 : ℝ) + 1) := (Real.rpow_add (hlam i) _ _).symm
        _ = lam i ^ (1 / 2 : ℝ) := by norm_num
    rw [hexp]
  have hcomm (x : L) : θ₁ (θ' x) = θ' (θ₁ x) := by
    have hlin : (θ₁ : L →ₗ[ℝ] L).comp (θ' : L →ₗ[ℝ] L) =
        (θ' : L →ₗ[ℝ] L).comp (θ₁ : L →ₗ[ℝ] L) := b.ext hcomm_basis
    exact LinearMap.congr_fun hlin x
  exact (hθ.conj φ).eq_of_commute hθ' hcomm

end Helpers

/-! ### Conjugacy of Cartan involutions -/

section Real

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- **Conjugacy of Cartan involutions**: any two Cartan involutions `θ` and `θ'` of a real Lie
algebra are conjugate by a Lie automorphism `φ` that acts as `Real.exp μ` on every `μ`-eigenvector
of `ad Z` for some `Z ∈ θ.cartanP`. -/
theorem IsCartanInvolution.exists_mem_cartanP_conj_eq
    {θ θ' : L ≃ₗ⁅ℝ⁆ L} (hθ : θ.IsCartanInvolution) (hθ' : θ'.IsCartanInvolution) :
    ∃ Z ∈ θ.cartanP, ∃ φ : L ≃ₗ⁅ℝ⁆ L,
      (∀ y, θ' (φ y) = φ (θ y)) ∧
      (∀ μ v, ⁅Z, v⁆ = μ • v → φ v = Real.exp μ • v) := by
  obtain ⟨b, lam, hb, hlam⟩ := exists_basis_eigenvector_sq_trans hθ hθ'
  obtain ⟨Z, hZP, hZb⟩ := exists_mem_cartanP_ad_basis hθ hθ' b hb hlam
  let φ := rpowNegQuarterEquiv b hb hlam
  have hconj := conj_rpowNegQuarterEquiv_eq hθ hθ' b hb hlam
  refine ⟨Z, hZP, φ, fun y ↦ ?_, fun μ v hv ↦ ?_⟩
  · have h := congrArg (fun e : L ≃ₗ⁅ℝ⁆ L ↦ e (φ y)) hconj.symm
    simpa only [φ, trans_apply, symm_apply_apply] using h
  · exact b.apply_eq_smul_of_apply_eq_smul (f := ad ℝ L Z) (g := (φ : L →ₗ[ℝ] L))
      (φ := Real.exp) hZb (fun i ↦ by
        rw [LinearEquiv.coe_coe, coe_toLinearEquiv, rpowNegQuarterEquiv_basis,
          Real.rpow_def_of_pos (hlam i), mul_comm]) hv

end Real

end LieEquiv
