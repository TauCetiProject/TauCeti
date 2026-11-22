/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Algebra.Lie.CartanInvolution.Basic
import Mathlib.Algebra.Lie.Derivation.Killing
import Mathlib.Analysis.InnerProductSpace.Spectrum
import TauCeti.Algebra.Lie.Spectral
import TauCeti.Analysis.InnerProductSpace.Spectral.Relative
import TauCeti.Analysis.Normed.Operator.Exponential

/-!
# Conjugacy of Cartan involutions

Any two Cartan involutions `θ` and `θ'` of a real semisimple Lie algebra `L` are conjugate by
`φ = P^{-1/4} = e^{ad Z}` with `P = (θ ∘ θ')²` and `Z ∈ θ.cartanP`
(`LieEquiv.IsCartanInvolution.exists_mem_cartanP_conj_eq`, and
`LieEquiv.IsCartanInvolution.exists_mem_cartanP_conj_exp` for finite-dimensional normed real Lie
algebras).

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
`θ.twistedKillingForm`. -/
private theorem twistedKillingForm_trans_left {θ θ' : L ≃ₗ⁅ℝ⁆ L}
    (hθ : Function.Involutive θ) (hθ' : Function.Involutive θ') (x y : L) :
    θ.twistedKillingForm (θ (θ' x)) y = θ.twistedKillingForm x (θ (θ' y)) := by
  simp only [twistedKillingForm_apply, hθ (θ' y)]
  rw [killingForm_of_equiv_apply θ (θ' x) y, ← killingForm_of_equiv_apply θ' x (θ' y), hθ' y]

/-- Diagonalizing `P = (θ ∘ θ')²` with respect to `B_θ`: produces a basis of `P`-eigenvectors
with strictly positive eigenvalues. -/
private theorem exists_basis_eigenvector_sq_trans {θ θ' : L ≃ₗ⁅ℝ⁆ L}
    (hθ : θ.IsCartanInvolution) (hθ' : θ'.IsCartanInvolution) :
    let P := (θ'.trans θ).trans (θ'.trans θ)
    ∃ (b : Module.Basis (Fin (finrank ℝ L)) ℝ L) (lam : Fin (finrank ℝ L) → ℝ),
      (∀ i, P (b i) = lam i • b i) ∧ (∀ i, 0 < lam i) := by
  have := hθ.finiteDimensional
  let N : L ≃ₗ⁅ℝ⁆ L := θ'.trans θ
  let P : L ≃ₗ⁅ℝ⁆ L := N.trans N
  have hN_symm (x y : L) : θ.twistedKillingForm (N x) y = θ.twistedKillingForm x (N y) :=
    twistedKillingForm_trans_left hθ.involutive hθ'.involutive x y
  obtain ⟨e, he⟩ := LinearMap.BilinForm.exists_linearEquiv_euclideanSpace_apply_apply
    hθ.isSymm_twistedKillingForm (fun _ hv ↦ hθ.twistedKillingForm_self_pos hv)
  let T : Module.End ℝ (EuclideanSpace ℝ (Fin (finrank ℝ L))) :=
    e.symm.toLinearMap.comp ((P : L →ₗ[ℝ] L).comp e.toLinearMap)
  have heT (x : EuclideanSpace ℝ (Fin (finrank ℝ L))) : e (T x) = P (e x) := by simp [T]
  have hT : T.IsSymmetric := fun x y ↦ by
    rw [← he (T x) y, ← he x (T y), heT x, heT y]
    simpa only [P, trans_apply] using (hN_symm (N (e x)) (e y)).trans (hN_symm (e x) (N (e y)))
  have hn : finrank ℝ (EuclideanSpace ℝ (Fin (finrank ℝ L))) = finrank ℝ L :=
    finrank_euclideanSpace_fin
  let ob := hT.eigenvectorBasis hn
  let lam := hT.eigenvalues hn
  let b : Module.Basis (Fin (finrank ℝ L)) ℝ L := ob.toBasis.map e
  have hbP (i : Fin (finrank ℝ L)) : P (b i) = lam i • b i := calc
    P (b i) = e (T (ob i)) := (heT (ob i)).symm
    _ = e (lam i • ob i) := congrArg e (hT.apply_eigenvectorBasis hn i)
    _ = lam i • b i := map_smul e _ _
  refine ⟨b, lam, hbP, fun i ↦ ?_⟩
  have hNne : N (b i) ≠ 0 := fun h0 ↦ b.ne_zero i (N.injective (h0.trans (map_zero N).symm))
  have hpos : 0 < θ.twistedKillingForm (P (b i)) (b i) := by
    simpa only [P, trans_apply, hN_symm] using hθ.twistedKillingForm_self_pos hNne
  rw [hbP i, map_smul, LinearMap.smul_apply, smul_eq_mul] at hpos
  exact pos_of_mul_pos_left hpos (hθ.twistedKillingForm_self_pos (b.ne_zero i)).le

/-- Building the inner derivation generator `Z ∈ θ.cartanP` for `log P` scaled by `-(1 / 4)`. -/
private theorem exists_mem_cartanP_ad_basis {ι : Type*}
    {θ θ' : L ≃ₗ⁅ℝ⁆ L} (hθ : θ.IsCartanInvolution) (hθ' : Function.Involutive θ')
    (b : Module.Basis ι ℝ L) {lam : ι → ℝ}
    (hb : ∀ i, ((θ'.trans θ).trans (θ'.trans θ)) (b i) = lam i • b i) (hlam : ∀ i, 0 < lam i) :
    ∃ Z ∈ θ.cartanP, ∀ i, ⁅Z, b i⁆ = (-(1 / 4 : ℝ) * Real.log (lam i)) • b i := by
  have := hθ.finiteDimensional
  have := hθ.isKilling
  let P : L ≃ₗ⁅ℝ⁆ L := (θ'.trans θ).trans (θ'.trans θ)
  let D := P.logDerivation b hb hlam
  obtain ⟨Z₀, hZ₀⟩ := LieDerivation.IsKilling.exists_eq_ad D
  have hZ₀_apply (y : L) : ⁅Z₀, y⁆ = D y := by
    simpa using congrArg (fun f : LieDerivation ℝ L L ↦ f y) hZ₀
  have hD_anti (y : L) : D (θ y) = -θ (D y) := P.logDerivation_apply_conj b hb hlam θ
    (LinearEquiv.involutive_sq_trans_conj_left θ.toLinearEquiv θ'.toLinearEquiv
      hθ.involutive hθ') y
  have hZ₀P : Z₀ ∈ θ.cartanP := by
    have hcent : θ Z₀ + Z₀ ∈ center ℝ L := (LieModule.mem_maxTrivSubmodule _ _ _ _).mpr fun w ↦ by
      have hθZ₀ : θ ⁅Z₀, θ w⁆ = ⁅θ Z₀, w⁆ := calc
        θ ⁅Z₀, θ w⁆ = ⁅θ Z₀, θ (θ w)⁆ := θ.map_lie Z₀ (θ w)
        _ = ⁅θ Z₀, w⁆ := by rw [hθ.involutive w]
      have hanti : ⁅θ Z₀, w⁆ = -⁅Z₀, w⁆ := calc
        ⁅θ Z₀, w⁆ = θ ⁅Z₀, θ w⁆ := hθZ₀.symm
        _ = θ (D (θ w)) := by rw [hZ₀_apply]
        _ = θ (-θ (D w)) := by rw [hD_anti]
        _ = -D w := by rw [map_neg, hθ.involutive]
        _ = -⁅Z₀, w⁆ := by rw [hZ₀_apply]
      rw [← lie_skew, add_lie, hanti, neg_add_cancel, neg_zero]
    rw [hθ.center_eq_bot, LieSubmodule.mem_bot] at hcent
    exact mem_cartanP.mpr (eq_neg_of_add_eq_zero_left hcent)
  refine ⟨(-(1 / 4 : ℝ)) • Z₀, θ.cartanP.smul_mem _ hZ₀P, fun i ↦ ?_⟩
  rw [smul_lie, hZ₀_apply, P.logDerivation_apply_basis b hb hlam i, smul_smul]

/-- The conjugate Cartan involution `φ ∘ θ ∘ φ⁻¹` for `φ = P^{-1/4}` commutes with `θ'`, hence
equals `θ'`. -/
private theorem conj_rpow_eq {ι : Type*}
    {θ θ' : L ≃ₗ⁅ℝ⁆ L} (hθ : θ.IsCartanInvolution) (hθ' : θ'.IsCartanInvolution)
    (b : Module.Basis ι ℝ L) {lam : ι → ℝ}
    (hb : ∀ i, ((θ'.trans θ).trans (θ'.trans θ)) (b i) = lam i • b i) (hlam : ∀ i, 0 < lam i) :
    let P := (θ'.trans θ).trans (θ'.trans θ)
    (P.rpow b hb hlam (-(1 / 4 : ℝ))).symm.trans (θ.trans (P.rpow b hb hlam (-(1 / 4 : ℝ)))) =
      θ' := by
  let N : L ≃ₗ⁅ℝ⁆ L := θ'.trans θ
  let P : L ≃ₗ⁅ℝ⁆ L := N.trans N
  let φ := P.rpow b hb hlam (-(1 / 4 : ℝ))
  let θ₁ := φ.symm.trans (θ.trans φ)
  have hPinv {v : L} {μ : ℝ} (hμ : μ ≠ 0) (hv : P v = μ • v) :
      P (θ v) = μ⁻¹ • θ v ∧ P (θ' v) = μ⁻¹ • θ' v :=
    LinearEquiv.sq_trans_apply_inv_of_eigenvector θ.toLinearEquiv θ'.toLinearEquiv
      hθ.involutive hθ'.involutive hμ hv
  have hθ₁_eig {v : L} {μ : ℝ} (hμ : 0 < μ) (hv : P v = μ • v) :
      θ₁ v = μ ^ (1 / 2 : ℝ) • θ v := by
    simp only [θ₁, trans_apply, φ, rpow_symm]
    rw [P.rpow_apply_of_eigenvector b hb hlam _ hv, map_smul, map_smul,
      P.rpow_apply_of_eigenvector b hb hlam _ (hPinv hμ.ne' hv).left]
    simp only [neg_neg, Real.inv_rpow hμ.le, Real.rpow_neg hμ.le, inv_inv, smul_smul,
      ← Real.rpow_add hμ]
    norm_num
  have hcomm_basis (i : ι) : θ₁ (θ' (b i)) = θ' (θ₁ (b i)) := by
    rw [hθ₁_eig (inv_pos.mpr (hlam i)) (hPinv (hlam i).ne' (hb i)).right,
      hθ₁_eig (hlam i) (hb i), map_smul, Real.inv_rpow (hlam i).le, ← Real.rpow_neg (hlam i).le]
    have hNN : N (N (b i)) = lam i • b i := by rw [← trans_apply]; exact hb i
    have hN : N (b i) = lam i • N.symm (b i) := by
      simpa only [symm_apply_apply, map_smul] using congrArg N.symm hNN
    have hNs : N.symm (b i) = θ' (θ (b i)) :=
      LinearEquiv.involutive_trans_symm θ.toLinearEquiv θ'.toLinearEquiv
        hθ.involutive hθ'.involutive (b i)
    have hθθ' : θ (θ' (b i)) = lam i • θ' (θ (b i)) := by simpa only [N, trans_apply, hNs] using hN
    rw [hθθ', smul_smul, ← Real.rpow_add_one (hlam i).ne']
    norm_num
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
      (∀ y, θ' (φ y) = φ (θ y)) ∧ (∀ μ v, ⁅Z, v⁆ = μ • v → φ v = Real.exp μ • v) := by
  obtain ⟨b, lam, hb, hlam⟩ := exists_basis_eigenvector_sq_trans hθ hθ'
  obtain ⟨Z, hZP, hZb⟩ := exists_mem_cartanP_ad_basis hθ hθ'.involutive b hb hlam
  let P := (θ'.trans θ).trans (θ'.trans θ)
  let φ := P.rpow b hb hlam (-(1 / 4 : ℝ))
  have hconj := conj_rpow_eq hθ hθ' b hb hlam
  refine ⟨Z, hZP, φ, fun y ↦ ?_, fun μ v hv ↦ b.apply_eq_smul_of_apply_eq_smul
    (f := ad ℝ L Z) (g := (φ : L →ₗ[ℝ] L)) hZb
    (fun i hi ↦ by rw [LinearEquiv.coe_coe, coe_toLinearEquiv, rpow_apply_basis,
      Real.rpow_def_of_pos (hlam i), mul_comm, ← hi]) hv⟩
  simpa only [φ, P, trans_apply, symm_apply_apply] using congrArg (fun e : L ≃ₗ⁅ℝ⁆ L ↦ e (φ y))
    hconj.symm

/-- **Operator-exponential conjugacy of Cartan involutions**: under any linear identification
`e : L ≃ₗ[ℝ] E` with a finite-dimensional normed real vector space `E` (specializing to
`LinearEquiv.refl ℝ L` when `L` itself carries a compatible norm), any two Cartan involutions
`θ` and `θ'` are conjugate by `exp (e.conj (ad Z))` for some `Z ∈ θ.cartanP`. -/
theorem IsCartanInvolution.exists_mem_cartanP_conj_exp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (e : L ≃ₗ[ℝ] E)
    {θ θ' : L ≃ₗ⁅ℝ⁆ L} (hθ : θ.IsCartanInvolution) (hθ' : θ'.IsCartanInvolution) :
    ∃ Z ∈ θ.cartanP, ∀ y,
      θ' (e.symm (NormedSpace.exp (LinearMap.toContinuousLinearMap (e.conj (ad ℝ L Z))) (e y))) =
        e.symm (NormedSpace.exp
          (LinearMap.toContinuousLinearMap (e.conj (ad ℝ L Z))) (e (θ y))) := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  obtain ⟨Z, hZP, φ, hconj, heig⟩ := hθ.exists_mem_cartanP_conj_eq hθ'
  let A : E →L[ℝ] E := LinearMap.toContinuousLinearMap (e.conj (ad ℝ L Z))
  have hexp_eq : ∀ y : L, e.symm (NormedSpace.exp A (e y)) = φ y := by
    have hle : ⨆ μ : ℝ, Module.End.eigenspace (ad ℝ L Z) μ ≤
        LinearMap.eqLocus ((e.symm.toLinearMap.comp (NormedSpace.exp A).toLinearMap).comp
          e.toLinearMap) φ.toLinearEquiv.toLinearMap := by
      refine iSup_le fun μ v hv ↦ ?_
      have hZv : ⁅Z, v⁆ = μ • v := Module.End.mem_eigenspace_iff.mp hv
      have hAv : A (e v) = μ • e v := by simp [A, LinearEquiv.conj_apply_apply, hZv]
      simp only [LinearMap.mem_eqLocus, LinearMap.comp_apply, LinearEquiv.coe_coe,
        ContinuousLinearMap.coe_coe, LieEquiv.coe_toLinearEquiv]
      rw [ContinuousLinearMap.exp_apply_of_apply_eq_smul A hAv, ← Real.exp_eq_exp_ℝ,
        ← map_smul, LinearEquiv.symm_apply_apply]
      exact (heig μ v hZv).symm
    rw [hθ.iSup_eigenspace_ad_eq_top hZP, top_le_iff] at hle
    exact fun y ↦ LinearMap.mem_eqLocus.mp (hle.symm ▸ Submodule.mem_top)
  exact ⟨Z, hZP, fun y ↦ by rw [hexp_eq y, hexp_eq (θ y), hconj y]⟩

end Real

end LieEquiv
