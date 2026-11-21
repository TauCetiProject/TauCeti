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
import TauCeti.Algebra.Lie.Spectral
import TauCeti.Analysis.InnerProductSpace.Spectral.Relative

/-!
# Conjugacy of Cartan involutions

Any two Cartan involutions `θ` and `θ'` of a real semisimple Lie algebra `L` are conjugate by
`φ = P^{-1/4} = e^{ad Z}` with `P = (θ ∘ θ')²` and `Z ∈ θ.cartanP`
(`LieEquiv.IsCartanInvolution.exists_mem_cartanP_conj_eq`).

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Progress in Mathematics 140,
  Birkhäuser, 2002, Chapter VI, §2, Theorem 6.16.
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
  let N : L ≃ₗ⁅ℝ⁆ L := θ'.trans θ; let P : L ≃ₗ⁅ℝ⁆ L := N.trans N
  have hN_symm (x y : L) : θ.cartanBilinForm (N x) y = θ.cartanBilinForm x (N y) :=
    cartanBilinForm_trans_left hθ.involutive hθ'.involutive x y
  obtain ⟨e, he⟩ := LinearMap.BilinForm.exists_linearEquiv_euclideanSpace_apply_apply
    hθ.isSymm_cartanBilinForm (fun _ hv ↦ hθ.cartanBilinForm_self_pos hv)
  let T : Module.End ℝ (EuclideanSpace ℝ (Fin (finrank ℝ L))) :=
    e.symm.toLinearMap.comp ((P : L →ₗ[ℝ] L).comp e.toLinearMap)
  have hT : T.IsSymmetric := fun x y ↦ by
    rw [← he (T x) y, ← he x (T y)]
    simpa [T, P, trans_apply] using (hN_symm (N (e x)) (e y)).trans (hN_symm (e x) (N (e y)))
  have hn : finrank ℝ (EuclideanSpace ℝ (Fin (finrank ℝ L))) = finrank ℝ L :=
    finrank_euclideanSpace_fin
  let ob := hT.eigenvectorBasis hn; let lam := hT.eigenvalues hn
  let b : Module.Basis (Fin (finrank ℝ L)) ℝ L := ob.toBasis.map e
  have hbP (i : Fin (finrank ℝ L)) : P (b i) = lam i • b i := by
    have hmap : P (e (ob i)) = e (T (ob i)) := by simp [T]
    have heq := congrArg e (hT.apply_eigenvectorBasis hn i)
    rwa [map_smul, ← hmap] at heq
  refine ⟨b, lam, hbP, fun i ↦ ?_⟩
  have hNne : N (b i) ≠ 0 := fun h0 ↦ b.ne_zero i (N.injective (h0.trans (map_zero N).symm))
  have hpos : 0 < θ.cartanBilinForm (P (b i)) (b i) := by
    simpa only [P, trans_apply, hN_symm] using hθ.cartanBilinForm_self_pos hNne
  rw [hbP i, map_smul, LinearMap.smul_apply, smul_eq_mul] at hpos
  exact pos_of_mul_pos_left hpos (hθ.cartanBilinForm_self_pos (b.ne_zero i)).le

/-- Building the inner derivation generator `Z ∈ θ.cartanP` for `log P` scaled by `-(1 / 4)`. -/
private theorem exists_mem_cartanP_ad_basis {ι : Type*} [Finite ι]
    {θ θ' : L ≃ₗ⁅ℝ⁆ L} (hθ : θ.IsCartanInvolution) (hθ' : Function.Involutive θ')
    (b : Module.Basis ι ℝ L) {lam : ι → ℝ}
    (hb : ∀ i, ((θ'.trans θ).trans (θ'.trans θ)) (b i) = lam i • b i)
    (hlam : ∀ i, 0 < lam i) :
    ∃ Z ∈ θ.cartanP, ∀ i, ⁅Z, b i⁆ = (-(1 / 4 : ℝ) * Real.log (lam i)) • b i := by
  have := hθ.finite; have := hθ.isKilling
  let P : L ≃ₗ⁅ℝ⁆ L := (θ'.trans θ).trans (θ'.trans θ); let D := P.logDerivation b hb hlam
  obtain ⟨Z₀, hZ₀⟩ := LieDerivation.IsKilling.exists_eq_ad D
  have hZ₀_apply (y : L) : ⁅Z₀, y⁆ = D y := by
    simpa using congrArg (fun f : LieDerivation ℝ L L ↦ f y) hZ₀
  have hD_anti (y : L) : D (θ y) = -θ (D y) := P.logDerivation_apply_conj b hb hlam θ
    (fun x ↦ by rw [eq_symm_apply]; simp [P, hθ.involutive _, hθ' _]) y
  have hZ₀P : Z₀ ∈ θ.cartanP := by
    have hcent : θ Z₀ + Z₀ ∈ center ℝ L := (LieModule.mem_maxTrivSubmodule _ _ _ _).mpr fun w ↦ by
      rw [← lie_skew, add_lie, ← hθ.involutive w, ← map_lie θ, hZ₀_apply, hθ.involutive,
        hZ₀_apply, hD_anti, map_neg, hθ.involutive, neg_add_cancel, neg_zero]
    rw [hθ.center_eq_bot, LieSubmodule.mem_bot] at hcent
    exact mem_cartanP_iff.mpr (eq_neg_of_add_eq_zero_left hcent)
  refine ⟨(-(1 / 4 : ℝ)) • Z₀, θ.cartanP.smul_mem _ hZ₀P, fun i ↦ ?_⟩
  rw [smul_lie, hZ₀_apply, P.logDerivation_apply_basis b hb hlam i, smul_smul]

/-- The conjugate Cartan involution `φ ∘ θ ∘ φ⁻¹` for `φ = P^{-1/4}` commutes with `θ'`, hence
equals `θ'`. -/
private theorem conj_rpow_eq {ι : Type*} [Finite ι]
    {θ θ' : L ≃ₗ⁅ℝ⁆ L} (hθ : θ.IsCartanInvolution) (hθ' : θ'.IsCartanInvolution)
    (b : Module.Basis ι ℝ L) {lam : ι → ℝ}
    (hb : ∀ i, ((θ'.trans θ).trans (θ'.trans θ)) (b i) = lam i • b i)
    (hlam : ∀ i, 0 < lam i) :
    let P := (θ'.trans θ).trans (θ'.trans θ)
    (P.rpow b hb hlam (-(1 / 4 : ℝ))).symm.trans (θ.trans (P.rpow b hb hlam (-(1 / 4 : ℝ)))) =
      θ' := by
  let N : L ≃ₗ⁅ℝ⁆ L := θ'.trans θ; let P : L ≃ₗ⁅ℝ⁆ L := N.trans N
  let φ := P.rpow b hb hlam (-(1 / 4 : ℝ)); let θ₁ := φ.symm.trans (θ.trans φ)
  have hPinv {v : L} {μ : ℝ} (hμ : μ ≠ 0) (hv : P v = μ • v) :
      P (θ v) = μ⁻¹ • θ v ∧ P (θ' v) = μ⁻¹ • θ' v :=
    LinearEquiv.sq_trans_apply_inv_of_eigenvector θ.toLinearEquiv θ'.toLinearEquiv
      hθ.involutive hθ'.involutive hμ hv
  have hθ₁_eig {v : L} {μ : ℝ} (hμ : 0 < μ) (hv : P v = μ • v) :
      θ₁ v = μ ^ (1 / 2 : ℝ) • θ v := by
    simp only [θ₁, trans_apply, φ, rpow_symm]
    rw [P.rpow_apply_of_eigenvector b hb hlam _ hv, map_smul, map_smul,
      P.rpow_apply_of_eigenvector b hb hlam _ (hPinv hμ.ne' hv).1]
    simp only [neg_neg, Real.inv_rpow hμ.le, Real.rpow_neg hμ.le, inv_inv, smul_smul,
      ← Real.rpow_add hμ]; norm_num
  have hcomm_basis (i : ι) : θ₁ (θ' (b i)) = θ' (θ₁ (b i)) := by
    rw [hθ₁_eig (inv_pos.mpr (hlam i)) (hPinv (hlam i).ne' (hb i)).2,
      hθ₁_eig (hlam i) (hb i), map_smul, Real.inv_rpow (hlam i).le, ← Real.rpow_neg (hlam i).le]
    have hN : N (b i) = lam i • N.symm (b i) := by
      simpa only [symm_apply_apply, map_smul] using
        congrArg N.symm (show N (N (b i)) = lam i • b i from hb i)
    have hNs : N.symm (b i) = θ' (θ (b i)) := by
      rw [symm_apply_eq]; simp [N, hθ'.involutive _, hθ.involutive _]
    rw [show θ (θ' (b i)) = lam i • θ' (θ (b i)) by simpa only [N, trans_apply, hNs] using hN,
      smul_smul, ← Real.rpow_add_one (hlam i).ne']; norm_num
  have hlin : (θ₁ : L →ₗ[ℝ] L).comp (θ' : L →ₗ[ℝ] L) = (θ' : L →ₗ[ℝ] L).comp (θ₁ : L →ₗ[ℝ] L) :=
    b.ext hcomm_basis
  exact (hθ.conj φ).eq_of_commute hθ' (LinearMap.congr_fun hlin)

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
  obtain ⟨Z, hZP, hZb⟩ := exists_mem_cartanP_ad_basis hθ hθ'.involutive b hb hlam
  let P := (θ'.trans θ).trans (θ'.trans θ); let φ := P.rpow b hb hlam (-(1 / 4 : ℝ))
  have hconj := conj_rpow_eq hθ hθ' b hb hlam
  refine ⟨Z, hZP, φ, fun y ↦ ?_, fun μ v hv ↦ b.apply_eq_smul_of_apply_eq_smul
    (f := ad ℝ L Z) (g := (φ : L →ₗ[ℝ] L)) hZb
    (fun i hi ↦ by rw [LinearEquiv.coe_coe, coe_toLinearEquiv, rpow_apply_basis,
      Real.rpow_def_of_pos (hlam i), mul_comm, ← hi]) hv⟩
  simpa only [φ, P, trans_apply, symm_apply_apply] using
    congrArg (fun e : L ≃ₗ⁅ℝ⁆ L ↦ e (φ y)) hconj.symm

end Real

end LieEquiv
