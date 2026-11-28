/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.HeisenbergModel.Fock.PolynomialVector
public import TauCeti.Analysis.HeisenbergModel.OrthogonalSum
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic
import Mathlib.MeasureTheory.Integral.Pi
import TauCeti.MeasureTheory.Constructions.Pi

/-!
# External products in the Fock model

This file treats the external products of the Fock model.

A splitting `e : ι₁ ⊕ ι₂ ≃ ι` of the coordinates compatible with the signs makes `β_ε` and the
Gaussian the orthogonal sum of those of the two parts (`TauCeti.Fock.coordSum`), so the tensor
product of `TauCeti.HeisenbergDatum.OrthogonalSum` gives the external product
`v ⊗ w ∈ 𝓕(ε)` of `v ∈ 𝓕(ε₁)` and `w ∈ 𝓕(ε₂)`, and `v_P ⊗ v_Q = v_{PQ}`.

For a finite type `T`, the external product `⊗_τ v_τ` of Fock vectors `v_τ ∈ 𝓕(ε)` is the function
`x ↦ ∏ τ, v_τ (x ⟨τ, ·⟩)` on `T × ι → ℂ`, a vector of the Fock space of the signs
`(τ, i) ↦ ε i`: the reproducing kernel, the Gaussian and the measure all factor over the blocks,
and an integral over `T × ι → ℂ` of a product of functions of the blocks is the product of the
integrals. The map is a bounded multilinear map with `‖⊗ v_τ‖ = ∏ ‖v_τ‖`,
`⟨⊗ v_τ, ⊗ w_τ⟩ = ∏ ⟨v_τ, w_τ⟩` and `⊗ v_{P_τ} = v_{∏ P_τ}`. Block diagonal elements `(u_τ)` of the
unitary group, Mathlib's `Matrix.blockDiagonal` reindexed from `ι × T` to `T × ι`, have multiplier
`∏ τ, Δ_∞(u_τ)` and act factor by factor: `ω((u_τ)) (⊗ v_τ) = ⊗ ω(u_τ) v_τ`.

## Main definitions

* `TauCeti.Fock.coordSum`, `TauCeti.Fock.boxProd`: the splitting of the coordinates as an orthogonal
  sum, and the external product along it.
* `TauCeti.Fock.piTensor`: the external product `⊗_τ v_τ` of a finite family.
* `TauCeti.Fock.blockDiagonalHom`: the block diagonal embedding `U(ε)^T → U(ε ∘ pr₂)`.

## Main results

* `TauCeti.Fock.boxProd_polyVector`: `v_P ⊗ v_Q = v_{PQ}`.
* `TauCeti.Fock.norm_piTensor`, `TauCeti.Fock.innerSL_piTensor`,
  `TauCeti.Fock.piTensor_polyVector`: `‖⊗ v_τ‖ = ∏ ‖v_τ‖`, `⟨⊗ v_τ, ⊗ w_τ⟩ = ∏ ⟨v_τ, w_τ⟩` and
  `⊗ v_{P_τ} = v_{∏ P_τ}`.
* `TauCeti.Fock.multiplier_blockDiagonalHom`, `TauCeti.Fock.weilRep_piTensor`: block diagonal
  elements have multiplier `∏ τ, Δ_∞(u_τ)` and act factor by factor.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic,
PBC), file `src/Lib/Weil/Fock/Basic.lean` (`New.Fock.realCoordSum`, `New.Fock.realBoxProd`,
`New.Fock.realBoxProd_polyVector`, `New.Fock.pi_normalizedVolume`, `New.Fock.piTensor`,
`New.Fock.fockInner_piTensor`, `New.Fock.piTensor_polyVector`, `New.Fock.blockMatrix`,
`New.Fock.blockU`, `New.Fock.realMultiplier_blockU`, `New.Fock.realWeil_piTensor`). The source's
identity of product measures is replaced by the integral identity
`TauCeti.Fock.integral_prod_block`, built on `TauCeti.measurePreserving_curry`, and its
`blockMatrix` by Mathlib's `Matrix.blockDiagonal` reindexed along `Equiv.prodComm`.
-/

public noncomputable section

open MeasureTheory Complex Finset MvPolynomial Matrix
open scoped ComplexConjugate

namespace TauCeti.Fock

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {ε : ι → ℤˣ}

/-! ### Splittings of the coordinates -/

section Splitting

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
  {ε₁ : ι₁ → ℤˣ} {ε₂ : ι₂ → ℤˣ}

variable (ι₁ ι₂) in
/-- The isomorphism `(ι₁ → ℂ) × (ι₂ → ℂ) ≃ (ι → ℂ)` of a splitting `e : ι₁ ⊕ ι₂ ≃ ι` of the
coordinates. -/
def coordSumEquiv (e : ι₁ ⊕ ι₂ ≃ ι) : (ι₁ → ℂ) × (ι₂ → ℂ) ≃ₜ+ (ι → ℂ) :=
  ((ContinuousLinearEquiv.sumPiEquivProdPi ℂ ι₁ ι₂ fun _ ↦ ℂ).symm.trans
    (ContinuousLinearEquiv.piCongrLeft ℂ (fun _ ↦ ℂ) e)).toContinuousAddEquiv

omit [Fintype ι] [DecidableEq ι] [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] in
@[simp]
theorem coordSumEquiv_apply (e : ι₁ ⊕ ι₂ ≃ ι) (x : (ι₁ → ℂ) × (ι₂ → ℂ)) (j : ι₁ ⊕ ι₂) :
    coordSumEquiv ι₁ ι₂ e x (e j) = Sum.elim x.1 x.2 j := by
  cases j <;> exact Equiv.piCongrLeft_apply_apply (P := fun _ ↦ ℂ) e _ _

omit [DecidableEq ι] [DecidableEq ι₁] [DecidableEq ι₂] in
/-- A sum over `ι` of a function of the coordinates of `coordSumEquiv e x` splits along `e`. -/
private theorem sum_coordSumEquiv (e : ι₁ ⊕ ι₂ ≃ ι) (f : ι → ℂ) :
    ∑ i, f i = ∑ j, f (e (Sum.inl j)) + ∑ j, f (e (Sum.inr j)) := by
  rw [← e.sum_comp, Fintype.sum_sum_type]

variable {e : ι₁ ⊕ ι₂ ≃ ι}

omit [Fintype ι] [DecidableEq ι] [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] in
theorem holomorphicCoord_coordSumEquiv_inl (he : ε ∘ e = Sum.elim ε₁ ε₂)
    (x : (ι₁ → ℂ) × (ι₂ → ℂ)) (j : ι₁) :
    holomorphicCoord ε (coordSumEquiv ι₁ ι₂ e x) (e (Sum.inl j)) = holomorphicCoord ε₁ x.1 j := by
  have := congrFun he (Sum.inl j)
  simp only [Function.comp_apply, Sum.elim_inl] at this
  simp [holomorphicCoord_apply, this]

omit [Fintype ι] [DecidableEq ι] [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] in
theorem holomorphicCoord_coordSumEquiv_inr (he : ε ∘ e = Sum.elim ε₁ ε₂)
    (x : (ι₁ → ℂ) × (ι₂ → ℂ)) (j : ι₂) :
    holomorphicCoord ε (coordSumEquiv ι₁ ι₂ e x) (e (Sum.inr j)) = holomorphicCoord ε₂ x.2 j := by
  have := congrFun he (Sum.inr j)
  simp only [Function.comp_apply, Sum.elim_inr] at this
  simp [holomorphicCoord_apply, this]

/-- A splitting `e : ι₁ ⊕ ι₂ ≃ ι` of the coordinates compatible with the signs makes `β_ε` and the
Gaussian the orthogonal sum of those of `ε₁` and `ε₂`. -/
def coordSum (he : ε ∘ e = Sum.elim ε₁ ε₂) :
    (heisenbergDatum ε).OrthogonalSum (heisenbergDatum ε₁) (heisenbergDatum ε₂) (gaussian ι)
      (gaussian ι₁) (gaussian ι₂) where
  equiv := coordSumEquiv ι₁ ι₂ e
  apply_equiv_equiv x y := by
    have h₁ (j : ι₁) : ε (e (Sum.inl j)) = ε₁ j := congrFun he (Sum.inl j)
    have h₂ (j : ι₂) : ε (e (Sum.inr j)) = ε₂ j := congrFun he (Sum.inr j)
    simp only [heisenbergDatum_apply, star_dotProduct_signMatrix_mulVec, ← Complex.exp_add]
    congr 1
    rw [sum_coordSumEquiv e, sum_coordSumEquiv e]
    simp only [coordSumEquiv_apply, Sum.elim_inl, Sum.elim_inr, h₁, h₂]
    ring
  vacuum_equiv x := by
    simp only [gaussian_apply, ← Complex.exp_add]
    congr 1
    rw [sum_coordSumEquiv e]
    simp only [coordSumEquiv_apply, Sum.elim_inl, Sum.elim_inr]
    ring

variable (he : ε ∘ e = Sum.elim ε₁ ε₂)

@[simp]
theorem coordSum_equiv : (coordSum he).equiv = coordSumEquiv ι₁ ι₂ e := (rfl)

/-- The *external product* `v ⊗ w` of Fock vectors along a splitting of the coordinates, the
tensor product of the orthogonal sum `TauCeti.Fock.coordSum`. -/
def boxProd : FockSpace ε₁ →L[ℂ] FockSpace ε₂ →L[ℂ] FockSpace ε :=
  (coordSum he).tmul (measure ι)

theorem boxProd_apply (v : FockSpace ε₁) (w : FockSpace ε₂) (x : (ι₁ → ℂ) × (ι₂ → ℂ)) :
    boxProd he v w (coordSumEquiv ι₁ ι₂ e x) = v x.1 * w x.2 := by
  rw [boxProd, HeisenbergDatum.OrthogonalSum.tmul_apply, coordSum_equiv,
    ContinuousAddEquiv.symm_apply_apply]

/-- Along a splitting compatible with the signs, `v_P ⊗ v_Q = v_{PQ}`. -/
theorem boxProd_polyVector (P : MvPolynomial ι₁ ℂ) (Q : MvPolynomial ι₂ ℂ) :
    boxProd he (polyVector ε₁ P) (polyVector ε₂ Q) =
      polyVector ε (rename (e ∘ Sum.inl) P * rename (e ∘ Sum.inr) Q) := by
  ext y
  obtain ⟨x, rfl⟩ := (coordSumEquiv ι₁ ι₂ e).surjective y
  have h₁ : holomorphicCoord ε (coordSumEquiv ι₁ ι₂ e x) ∘ e ∘ Sum.inl = holomorphicCoord ε₁ x.1 :=
    funext (holomorphicCoord_coordSumEquiv_inl he x)
  have h₂ : holomorphicCoord ε (coordSumEquiv ι₁ ι₂ e x) ∘ e ∘ Sum.inr = holomorphicCoord ε₂ x.2 :=
    funext (holomorphicCoord_coordSumEquiv_inr he x)
  rw [boxProd_apply, polyVector_apply, polyVector_apply, polyVector_apply, eval_mul, eval_rename,
    eval_rename, h₁, h₂, ← coordSum_equiv he, (coordSum he).vacuum_equiv x]
  ring

end Splitting

/-! ### Products over a finite set -/

section Product

/-- The signs `(τ, i) ↦ ε i` on `T × ι`. -/
abbrev blockSign (S : Type*) (ε : ι → ℤˣ) : S × ι → ℤˣ := fun p ↦ ε p.2

variable {T : Type*} [Fintype T] [DecidableEq T]

omit [DecidableEq ι] [DecidableEq T] in
/-- Currying `T × ι → ℂ ≃ T → ι → ℂ` carries Lebesgue measure to the product of Lebesgue
measures. -/
private theorem measurePreserving_curry_volume :
    MeasurePreserving (MeasurableEquiv.curry T ι ℂ) (volume : Measure (T × ι → ℂ))
      (Measure.pi fun _ : T ↦ (volume : Measure (ι → ℂ))) :=
  TauCeti.measurePreserving_curry fun _ _ ↦ volume

omit [DecidableEq ι] [DecidableEq T] in
private theorem measure_prod_const :
    (ENNReal.ofReal ((1 / Real.pi) ^ Fintype.card (T × ι))).toReal =
      ∏ _τ : T, (ENNReal.ofReal ((1 / Real.pi) ^ Fintype.card ι)).toReal := by
  rw [prod_const, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity),
    Fintype.card_prod, ← pow_mul, mul_comm, Finset.card_univ]

omit [DecidableEq ι] [DecidableEq T] in
/-- A product of integrable functions of the blocks `x ⟨τ, ·⟩` is integrable on `T × ι → ℂ`. -/
theorem integrable_prod_block {𝕜 : Type*} [RCLike 𝕜] {f : T → (ι → ℂ) → 𝕜}
    (hf : ∀ τ, Integrable (f τ) (measure ι)) :
    Integrable (fun x : T × ι → ℂ ↦ ∏ τ, f τ fun i ↦ x (τ, i)) (measure (T × ι)) := by
  simp only [measure_def] at hf ⊢
  have h : Integrable (fun y : T → ι → ℂ ↦ ∏ τ, f τ (y τ))
      (Measure.pi fun _ : T ↦ (volume : Measure (ι → ℂ))) :=
    Integrable.fintype_prod fun τ ↦ (integrable_smul_measure (by simp [Real.pi_pos])
      ENNReal.ofReal_ne_top).1 (hf τ)
  exact ((measurePreserving_curry_volume.integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)).2 h).smul_measure ENNReal.ofReal_ne_top

omit [DecidableEq ι] [DecidableEq T] in
/-- The integral over `T × ι → ℂ` of a product of functions of the blocks is the product of
the integrals. -/
theorem integral_prod_block {𝕜 : Type*} [RCLike 𝕜] (f : T → (ι → ℂ) → 𝕜) :
    ∫ x : T × ι → ℂ, ∏ τ, f τ (fun i ↦ x (τ, i)) ∂measure (T × ι) =
      ∏ τ, ∫ y, f τ y ∂measure ι := by
  have h : ∫ x : T × ι → ℂ, ∏ τ, f τ (fun i ↦ x (τ, i)) = ∏ τ, ∫ y, f τ y := by
    rw [← integral_fintype_prod_eq_prod (μ := fun _ : T ↦ (volume : Measure (ι → ℂ))),
      ← measurePreserving_curry_volume.integral_comp' (fun y : T → ι → ℂ ↦ ∏ τ, f τ (y τ))]
    -- `MeasurableEquiv.curry` is `Function.curry`, and `Function.curry x τ` is `fun i ↦ x (τ, i)`.
    simp only [MeasurableEquiv.coe_curry]
    rfl
  simp only [measure_def, integral_smul_measure]
  rw [h, measure_prod_const]
  simp only [RCLike.real_smul_eq_coe_mul, map_prod, prod_mul_distrib]


/-- The reproducing kernel on `T × ι → ℂ` is the product of the kernels of the blocks. -/
private theorem heisenbergDatum_mul_gaussian_block (x y : T × ι → ℂ) :
    heisenbergDatum (blockSign T ε) y x * gaussian (T × ι) (x - y) =
      ∏ τ, (heisenbergDatum ε (fun i ↦ y (τ, i)) (fun i ↦ x (τ, i)) *
        gaussian ι ((fun i ↦ x (τ, i)) - fun i ↦ y (τ, i))) := by
  simp only [heisenbergDatum_apply, gaussian_apply, star_dotProduct_signMatrix_mulVec,
    ← Complex.exp_add, ← Complex.exp_sum, Pi.sub_apply]
  congr 1
  simp only [Fintype.sum_prod_type, sum_div, ← sum_neg_distrib, ← sum_sub_distrib,
    ← sum_add_distrib]

omit [DecidableEq ι] [DecidableEq T] in
/-- The Gaussian on `T × ι → ℂ` is the product of the Gaussians of the blocks. -/
theorem gaussian_block (x : T × ι → ℂ) : gaussian (T × ι) x = ∏ τ, gaussian ι fun i ↦ x (τ, i) := by
  simp only [gaussian_apply, ← Complex.exp_sum]
  congr 1
  simp only [Fintype.sum_prod_type, ← sum_neg_distrib, sum_div]

omit [Fintype ι] [DecidableEq ι] [Fintype T] [DecidableEq T] in
theorem holomorphicCoord_block (x : T × ι → ℂ) (τ : T) :
    (fun i ↦ holomorphicCoord (blockSign T ε) x (τ, i)) = holomorphicCoord ε fun i ↦ x (τ, i) :=
  funext fun i ↦ by simp only [holomorphicCoord_apply]

/-- The multilinear form `v ↦ ∏ τ, v τ (x ⟨τ, ·⟩)`. -/
private def prodAt (x : T × ι → ℂ) : ((_ : T) → FockSpace ε) →ₘₗ[ℂ] ℂ :=
  (MultilinearMap.mkPiAlgebra ℂ T ℂ).compLinearMap fun τ ↦
    (ReproducingModel.evalCLM (fun i ↦ x (τ, i))).toLinearMap

omit [DecidableEq T] in
private theorem prodAt_apply (x : T × ι → ℂ) (v : T → FockSpace ε) :
    prodAt x v = ∏ τ, v τ (fun i ↦ x (τ, i)) := by
  simp [prodAt]

/-- The product `∏ τ, v τ (x ⟨τ, ·⟩)` of Fock vectors is reproduced by the kernel on `T × ι`. -/
private theorem integral_prod_mul_kernel (v : T → FockSpace ε) (x : T × ι → ℂ) :
    ∫ y, (∏ τ, v τ fun i ↦ y (τ, i)) *
        (heisenbergDatum (blockSign T ε) y x * gaussian (T × ι) (x - y)) ∂measure (T × ι) =
      ∏ τ, v τ fun i ↦ x (τ, i) := by
  simp_rw [heisenbergDatum_mul_gaussian_block, ← prod_mul_distrib]
  rw [integral_prod_block fun τ y ↦ v τ y * (heisenbergDatum ε y (fun i ↦ x (τ, i)) *
    gaussian ι ((fun i ↦ x (τ, i)) - y))]
  exact prod_congr rfl fun τ _ ↦ (v τ).integral_mul_kernel _

/-- The product of Fock vectors as a multilinear map. -/
private def piTensorAux : ((_ : T) → FockSpace ε) →ₘₗ[ℂ] FockSpace (blockSign T ε) where
  toFun v := ReproducingModel.mk (fun x ↦ ∏ τ, v τ fun i ↦ x (τ, i))
    (integrable_prod_block fun τ ↦ (v τ).integrable) (integral_prod_mul_kernel v)
  map_update_add' v σ a b := ReproducingModel.ext fun x ↦ by
    simp only [ReproducingModel.mk_apply, ReproducingModel.add_apply, ← prodAt_apply]
    exact (prodAt x).map_update_add v σ a b
  map_update_smul' v σ c a := ReproducingModel.ext fun x ↦ by
    simp only [ReproducingModel.mk_apply, ReproducingModel.smul_apply, RingHom.id_apply,
      ← prodAt_apply]
    exact (prodAt x).map_update_smul v σ c a

private theorem norm_piTensorAux (v : T → FockSpace ε) : ‖piTensorAux v‖ = ∏ τ, ‖v τ‖ := by
  rw [ReproducingModel.norm_eq_integral_norm]
  simp only [piTensorAux, MultilinearMap.coe_mk, ReproducingModel.mk_apply, norm_prod]
  rw [integral_prod_block fun τ y ↦ ‖v τ y‖]
  simp only [← ReproducingModel.norm_eq_integral_norm]

variable (T ε) in
/-- The *external product* `⊗_τ v_τ` of a family of Fock vectors indexed by a finite type `T`:
the Fock vector `x ↦ ∏ τ, v τ (x ⟨τ, ·⟩)` for the signs `(τ, i) ↦ ε i` on `T × ι`, a bounded
multilinear map. -/
def piTensor :
    ContinuousMultilinearMap ℂ (fun _ : T ↦ FockSpace ε) (FockSpace (blockSign T ε)) :=
  piTensorAux.mkContinuous 1 fun v ↦ by rw [one_mul, norm_piTensorAux]

@[simp]
theorem piTensor_apply (v : T → FockSpace ε) (x : T × ι → ℂ) :
    piTensor ε T v x = ∏ τ, v τ fun i ↦ x (τ, i) := by
  simp [piTensor, piTensorAux]

theorem norm_piTensor (v : T → FockSpace ε) : ‖piTensor ε T v‖ = ∏ τ, ‖v τ‖ :=
  norm_piTensorAux v

/-- `⟨⊗ v_τ, ⊗ w_τ⟩ = ∏ τ, ⟨v_τ, w_τ⟩`. -/
theorem innerSL_piTensor (v w : T → FockSpace ε) :
    ReproducingModel.innerSL (piTensor ε T v) (piTensor ε T w) =
      ∏ τ, ReproducingModel.innerSL (v τ) (w τ) := by
  simp only [ReproducingModel.innerSL_apply, piTensor_apply, map_prod, ← prod_mul_distrib]
  exact integral_prod_block fun τ y ↦ conj (v τ y) * w τ y

/-- `⊗ v_{P_τ} = v_{∏ P_τ}`, each `P_τ` renamed into the variables `(τ, ·)`. -/
theorem piTensor_polyVector (P : T → MvPolynomial ι ℂ) :
    piTensor ε T (fun τ ↦ polyVector ε (P τ)) =
      polyVector (blockSign T ε) (∏ τ, rename (fun i ↦ (τ, i)) (P τ)) := by
  ext x
  simp only [piTensor_apply, polyVector_apply, map_prod, eval_rename, gaussian_block,
    prod_mul_distrib, Function.comp_def, ← holomorphicCoord_block]

/-! ### Block diagonal elements of `U(ε)` -/

omit [Fintype ι] [DecidableEq ι] [Fintype T] in
private theorem reindex_blockDiagonal_apply (M : T → Matrix ι ι ℂ) (p q : T × ι) :
    reindex (Equiv.prodComm ι T) (Equiv.prodComm ι T) (blockDiagonal M) p q =
      if p.1 = q.1 then M p.1 p.2 q.2 else 0 := by
  simp [blockDiagonal_apply]

omit [Fintype ι] [Fintype T] in
private theorem signMatrix_blockSign :
    signMatrix (blockSign T ε) =
      reindex (Equiv.prodComm ι T) (Equiv.prodComm ι T) (blockDiagonal fun _ ↦ signMatrix ε) := by
  ext ⟨τ, i⟩ ⟨σ, j⟩
  simp only [signMatrix_eq_diagonal, diagonal_apply, reindex_blockDiagonal_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

variable (T) in
/-- The block diagonal embedding `U(ε)^T → U(ε ∘ pr₂)`: `(u_τ)` acts on `T × ι → ℂ` by Mathlib's
`Matrix.blockDiagonal` of the `u_τ`, with rows and columns reindexed from `ι × T` to `T × ι`. -/
def blockDiagonalHom : (T → unitaryGroup ε) →* unitaryGroup (blockSign T ε) where
  toFun u := unitaryGroupOf.ofMatrix isUnit_signMatrix
    (reindex (Equiv.prodComm ι T) (Equiv.prodComm ι T)
      (blockDiagonal fun τ ↦ ((u τ : GL ι ℂ) : Matrix ι ι ℂ))) (by
      rw [signMatrix_blockSign, star_eq_conjTranspose, conjTranspose_reindex,
        blockDiagonal_conjTranspose, ← coe_reindexRingEquiv, ← map_mul, ← map_mul,
        ← blockDiagonal_mul, ← blockDiagonal_mul]
      exact congrArg _ (congrArg _ (funext fun τ ↦ by
        simpa [star_eq_conjTranspose] using mem_unitaryGroupOf_iff.mp (u τ).property)))
  map_one' := Subtype.ext (Units.ext (by
    simp only [unitaryGroupOf.val_ofMatrix, Pi.one_apply, OneMemClass.coe_one, Units.val_one]
    rw [← Pi.one_def, blockDiagonal_one, ← coe_reindexRingEquiv, map_one]))
  map_mul' u u' := Subtype.ext (Units.ext (by
    simp only [unitaryGroupOf.val_ofMatrix, Pi.mul_apply, Subgroup.coe_mul, Units.val_mul]
    rw [← coe_reindexRingEquiv, ← map_mul, ← blockDiagonal_mul]))

@[simp]
theorem val_blockDiagonalHom (u : T → unitaryGroup ε) :
    (((blockDiagonalHom T u : unitaryGroup (blockSign T ε)) : GL (T × ι) ℂ) :
        Matrix (T × ι) (T × ι) ℂ) =
      reindex (Equiv.prodComm ι T) (Equiv.prodComm ι T)
        (blockDiagonal fun τ ↦ ((u τ : GL ι ℂ) : Matrix ι ι ℂ)) :=
  unitaryGroupOf.val_ofMatrix _ _ _

/-- A block diagonal element acts block by block. -/
theorem blockDiagonalHom_smul_apply (u : T → unitaryGroup ε) (y : T × ι → ℂ) (τ : T) :
    (fun i ↦ (blockDiagonalHom T u • y) (τ, i)) = u τ • fun i ↦ y (τ, i) := by
  ext i
  simp [smul_def, mulVec, dotProduct, Fintype.sum_prod_type, reindex_blockDiagonal_apply, ite_mul]

/-- The bijection between the negative indices of `T × ι` and `T` times those of `ι`. -/
private def negIndexEquiv :
    {p : T × ι // blockSign T ε p = -1} ≃ T × {i // ε i = -1} where
  toFun p := (p.val.1, ⟨p.val.2, p.property⟩)
  invFun q := ⟨(q.1, q.2.val), q.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `Δ_∞` is multiplicative on block diagonal elements: `Δ_∞((u_τ)) = ∏ τ, Δ_∞(u_τ)`. -/
theorem multiplier_blockDiagonalHom (u : T → unitaryGroup ε) :
    multiplier (blockSign T ε) (blockDiagonalHom T u) = ∏ τ, multiplier ε (u τ) := by
  have h_block : negBlock (blockSign T ε) (reindex (Equiv.prodComm ι T) (Equiv.prodComm ι T)
      (blockDiagonal fun τ ↦ ((u τ : GL ι ℂ) : Matrix ι ι ℂ))) =
      (reindex (Equiv.prodComm _ T) (Equiv.prodComm _ T)
        (blockDiagonal fun τ ↦ negBlock ε ((u τ : GL ι ℂ) : Matrix ι ι ℂ))).submatrix
          negIndexEquiv negIndexEquiv := by
    ext p q
    simp only [negBlock_apply, submatrix_apply, reindex_blockDiagonal_apply, negIndexEquiv,
      Equiv.coe_fn_mk]
  simp only [multiplier_apply, val_blockDiagonalHom, h_block, det_submatrix_equiv_self,
    det_reindex_self, det_blockDiagonal, map_prod]

/-- Block diagonal elements act on external products factor by factor:
`ω((u_τ)) (⊗ v_τ) = ⊗ ω(u_τ) v_τ`. -/
theorem weilRep_piTensor (u : T → unitaryGroup ε) (v : T → FockSpace ε) :
    weilRep (blockSign T ε) (blockDiagonalHom T u) (piTensor ε T v) =
      piTensor ε T fun τ ↦ weilRep ε (u τ) (v τ) := by
  ext x
  simp only [ReproducingModel.weilRep_apply, piTensor_apply, multiplier_blockDiagonalHom]
  rw [prod_mul_distrib]
  congr 1
  simp_rw [heisenbergDatum_mul_gaussian_block, blockDiagonalHom_smul_apply, ← prod_mul_distrib]
  exact integral_prod_block fun τ y ↦ v τ y * (heisenbergDatum ε (u τ • y) (fun i ↦ x (τ, i)) *
    gaussian ι ((fun i ↦ x (τ, i)) - u τ • y))

end Product

end TauCeti.Fock
