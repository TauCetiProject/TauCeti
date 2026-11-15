/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.LadderModule.Basic
public import TauCeti.QuantumGroups.UqSl2.TensorProduct

import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Tensoring signed ladder modules with the sign representation

The one-dimensional signed ladder module `L_0^-`, on which `K` acts by `-1` and `E`, `F` act by
zero, is the sign representation of `U_q(sl₂)`. Tensoring with it on either side reverses the
sign of a signed ladder module:

`L_0^- ⊗ L_m^ε ≃ L_m^(-ε) ≃ L_m^ε ⊗ L_0^-`,

for the coproduct action `ΔE = E ⊗ 1 + K ⊗ E`, `ΔF = F ⊗ K⁻¹ + 1 ⊗ F`, `ΔK = K ⊗ K`.

The two tensor orders need different basis rescalings. Write `w = v₀` for the basis vector of
`L_0^-` and `v_j` for the ladder vectors of `L_m^ε` and of `L_m^(-ε)`.

* `signTensorEquiv : L_0^- ⊗ L_m^ε ≃ L_m^(-ε)` sends `w ⊗ v_j` to `v_j`. The sign of the left
  factor flips the sign of `K` through `ΔK = K ⊗ K`; among the `E` and `F` actions it enters
  only through the `K ⊗ E` term of `ΔE`, which already matches the sign change
  `E v_j = -ε [m - j + 1]_q v_(j - 1)` of `L_m^(-ε)`.
* `tensorSignEquiv : L_m^ε ⊗ L_0^- ≃ L_m^(-ε)` sends `v_j ⊗ w` to `(-1)^j v_j`. Here the sign of
  the right factor enters through the `F ⊗ K⁻¹` term of `ΔF`, and the alternating rescaling
  moves it from `F` to `E`.

Consequently `signTensorCommEquiv : L_0^- ⊗ L_m^ε ≃ L_m^ε ⊗ L_0^-` sends `w ⊗ v_j` to
`(-1)^j v_j ⊗ w`. The rescaling cannot be dropped: for `m ≥ 1` (and `q ≠ ±1`) no module map sends
every `x ⊗ y` to `y ⊗ x` (`not_exists_linearMap_tmul_eq_tmul`).

Only `q ≠ 0` is needed for the isomorphisms; no genericity hypothesis is used.

## Main definitions

* `TauCeti.UqSl2.LadderModule.signTensorEquiv`: `L_0^- ⊗ L_m^ε ≃ L_m^(-ε)`.
* `TauCeti.UqSl2.LadderModule.tensorSignEquiv`: `L_m^ε ⊗ L_0^- ≃ L_m^(-ε)`.
* `TauCeti.UqSl2.LadderModule.signTensorCommEquiv`: `L_0^- ⊗ L_m^ε ≃ L_m^ε ⊗ L_0^-`.

## Main results

* `TauCeti.UqSl2.LadderModule.signTensorEquiv_tmul_vec`: `w ⊗ v_j ↦ v_j`.
* `TauCeti.UqSl2.LadderModule.tensorSignEquiv_tmul_vec`: `v_j ⊗ w ↦ (-1)^j v_j`.
* `TauCeti.UqSl2.LadderModule.signTensorCommEquiv_tmul_vec`: `w ⊗ v_j ↦ (-1)^j v_j ⊗ w`.
* `TauCeti.UqSl2.LadderModule.signTensorCommEquiv_symm_tmul_vec`: `v_j ⊗ w ↦ (-1)^j w ⊗ v_j`.
* `TauCeti.UqSl2.LadderModule.not_exists_linearMap_tmul_eq_tmul`: the flip of tensor factors is
  not a module map `L_0^- ⊗ L_m^ε → L_m^ε ⊗ L_0^-` for `m ≥ 1`.

## References

* A. Virelizier, *Quantum groups*, Sections 2.3--2.4, for the coproduct convention.
* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Chapter VII, for tensor
  products of the modules `V_(ε,n)`, which are the modules `L_n^ε` here.
-/

public noncomputable section

namespace TauCeti.UqSl2.LadderModule

open Module BialgebraModule

variable {q : ℂ} [Fact (q ≠ 0)] {m : ℕ} {ε : ℤˣ}

omit [Fact (q ≠ 0)] in
/-- The basis vector of the sign representation is the ladder basis vector. -/
private theorem vec_sign : vec q 0 (-1) 0 = basis q 0 (-1) 0 := by
  simpa using vec_coe (q := q) (m := 0) (ε := -1) 0

/-! ### The sign representation on the left -/

variable (q m ε) in
/-- The basis `w ⊗ v_j` of `L_0^- ⊗ L_m^ε`. -/
private def signTensorBasis :
    Basis (Fin (m + 1)) ℂ (Tensor ℂ (UqSl2 q) (LadderModule q 0 (-1)) (LadderModule q m ε)) :=
  (((basis q 0 (-1)).tensorProduct (basis q m ε)).reindex
    (Equiv.uniqueProd (Fin (m + 1)) (Fin 1))).map (tensorEquiv ℂ (UqSl2 q) _ _).symm

variable (q m ε) in
/-- The complex-linear map `v_j ↦ w ⊗ v_j`. -/
private def signTensorLinearEquiv :
    LadderModule q m (-ε) ≃ₗ[ℂ]
      Tensor ℂ (UqSl2 q) (LadderModule q 0 (-1)) (LadderModule q m ε) :=
  (basis q m (-ε)).equiv (signTensorBasis q m ε) (Equiv.refl _)

private theorem signTensorLinearEquiv_vec (j : ℤ) :
    signTensorLinearEquiv q m ε (vec q m (-ε) j) =
      tmul ℂ (UqSl2 q) (vec q 0 (-1) 0) (vec q m ε j) := by
  by_cases hj : 0 ≤ j ∧ j ≤ m
  · obtain ⟨i, rfl⟩ : ∃ i : Fin (m + 1), (i : ℤ) = j := ⟨⟨j.toNat, by omega⟩, by simp; omega⟩
    simp [signTensorLinearEquiv, signTensorBasis, vec_coe, vec_sign, Basis.tensorProduct_apply]
  · have h₁ : vec q m (-ε) j = 0 := vec_eq_zero_iff.mpr (by omega)
    have h₂ : vec q m ε j = 0 := vec_eq_zero_iff.mpr (by omega)
    rw [h₁, h₂, map_zero, tmul_zero]

private theorem signTensorLinearEquiv_e_smul (j : ℤ) :
    signTensorLinearEquiv q m ε (e q • vec q m (-ε) j) =
      e q • signTensorLinearEquiv q m ε (vec q m (-ε) j) := by
  simp [signTensorLinearEquiv_vec, smul_tmul']

private theorem signTensorLinearEquiv_f_smul (j : ℤ) :
    signTensorLinearEquiv q m ε (f q • vec q m (-ε) j) =
      f q • signTensorLinearEquiv q m ε (vec q m (-ε) j) := by
  simp [signTensorLinearEquiv_vec]

private theorem signTensorLinearEquiv_k_smul (j : ℤ) :
    signTensorLinearEquiv q m ε (k q • vec q m (-ε) j) =
      k q • signTensorLinearEquiv q m ε (vec q m (-ε) j) := by
  simp [signTensorLinearEquiv_vec, smul_tmul']

variable (q m ε) in
/-- Tensoring with the sign representation on the left reverses the sign of a ladder module:
`L_0^- ⊗ L_m^ε ≃ L_m^(-ε)`, sending `w ⊗ v_j` to `v_j`. -/
def signTensorEquiv :
    Tensor ℂ (UqSl2 q) (LadderModule q 0 (-1)) (LadderModule q m ε) ≃ₗ[UqSl2 q]
      LadderModule q m (-ε) :=
  (LinearEquiv.ofBijective
    (homOfVec (signTensorLinearEquiv q m ε).toLinearMap
      (fun j _ => signTensorLinearEquiv_e_smul j) (fun j _ => signTensorLinearEquiv_f_smul j)
      (fun j _ => signTensorLinearEquiv_k_smul j))
    (by
      convert (signTensorLinearEquiv q m ε).bijective
      exact funext (homOfVec_apply _ _ _ _))).symm

/-- The inverse of `signTensorEquiv` sends `v_j` to `w ⊗ v_j`. -/
@[simp]
theorem signTensorEquiv_symm_vec (j : ℤ) :
    (signTensorEquiv q m ε).symm (vec q m (-ε) j) =
      tmul ℂ (UqSl2 q) (vec q 0 (-1) 0) (vec q m ε j) := by
  rw [signTensorEquiv, LinearEquiv.symm_symm, LinearEquiv.ofBijective_apply, homOfVec_apply,
    LinearEquiv.coe_coe, signTensorLinearEquiv_vec]

/-- `signTensorEquiv` sends `w ⊗ v_j` to `v_j`. -/
@[simp]
theorem signTensorEquiv_tmul_vec (j : ℤ) :
    signTensorEquiv q m ε (tmul ℂ (UqSl2 q) (vec q 0 (-1) 0) (vec q m ε j)) = vec q m (-ε) j := by
  rw [← signTensorEquiv_symm_vec, LinearEquiv.apply_symm_apply]

/-! ### The sign representation on the right -/

variable (q m ε) in
/-- The basis `(-1)^j v_j ⊗ w` of `L_m^ε ⊗ L_0^-`. -/
private def tensorSignBasis :
    Basis (Fin (m + 1)) ℂ (Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q 0 (-1))) :=
  ((((basis q m ε).tensorProduct (basis q 0 (-1))).reindex
    (Equiv.prodUnique (Fin (m + 1)) (Fin 1))).map (tensorEquiv ℂ (UqSl2 q) _ _).symm).unitsSMul
    fun i => (-1) ^ (i : ℕ)

variable (q m ε) in
/-- The complex-linear map `v_j ↦ (-1)^j v_j ⊗ w`. -/
private def tensorSignLinearEquiv :
    LadderModule q m (-ε) ≃ₗ[ℂ]
      Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q 0 (-1)) :=
  (basis q m (-ε)).equiv (tensorSignBasis q m ε) (Equiv.refl _)

private theorem tensorSignLinearEquiv_vec (j : ℤ) :
    tensorSignLinearEquiv q m ε (vec q m (-ε) j) =
      (-1 : ℂ) ^ j • tmul ℂ (UqSl2 q) (vec q m ε j) (vec q 0 (-1) 0) := by
  by_cases hj : 0 ≤ j ∧ j ≤ m
  · obtain ⟨i, rfl⟩ : ∃ i : Fin (m + 1), (i : ℤ) = j := ⟨⟨j.toNat, by omega⟩, by simp; omega⟩
    simp [tensorSignLinearEquiv, tensorSignBasis, vec_coe, vec_sign, Basis.tensorProduct_apply,
      Basis.unitsSMul_apply, Units.smul_def]
  · have h₁ : vec q m (-ε) j = 0 := vec_eq_zero_iff.mpr (by omega)
    have h₂ : vec q m ε j = 0 := vec_eq_zero_iff.mpr (by omega)
    rw [h₁, h₂, map_zero, zero_tmul, smul_zero]

private theorem tensorSignLinearEquiv_e_smul (j : ℤ) :
    tensorSignLinearEquiv q m ε (e q • vec q m (-ε) j) =
      e q • tensorSignLinearEquiv q m ε (vec q m (-ε) j) := by
  simp [tensorSignLinearEquiv_vec, smul_tmul', smul_smul, smul_algebra_smul_comm,
    zpow_sub_one₀ (neg_ne_zero.mpr one_ne_zero : (-1 : ℂ) ≠ 0), mul_comm]

private theorem tensorSignLinearEquiv_f_smul (j : ℤ) :
    tensorSignLinearEquiv q m ε (f q • vec q m (-ε) j) =
      f q • tensorSignLinearEquiv q m ε (vec q m (-ε) j) := by
  simp [tensorSignLinearEquiv_vec, smul_tmul', smul_smul, smul_algebra_smul_comm,
    zpow_add_one₀ (neg_ne_zero.mpr one_ne_zero : (-1 : ℂ) ≠ 0), mul_comm]

private theorem tensorSignLinearEquiv_k_smul (j : ℤ) :
    tensorSignLinearEquiv q m ε (k q • vec q m (-ε) j) =
      k q • tensorSignLinearEquiv q m ε (vec q m (-ε) j) := by
  simp [tensorSignLinearEquiv_vec, smul_tmul', smul_smul, smul_algebra_smul_comm, mul_comm]

variable (q m ε) in
/-- Tensoring with the sign representation on the right reverses the sign of a ladder module:
`L_m^ε ⊗ L_0^- ≃ L_m^(-ε)`, sending `v_j ⊗ w` to `(-1)^j v_j`. -/
def tensorSignEquiv :
    Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q 0 (-1)) ≃ₗ[UqSl2 q]
      LadderModule q m (-ε) :=
  (LinearEquiv.ofBijective
    (homOfVec (tensorSignLinearEquiv q m ε).toLinearMap
      (fun j _ => tensorSignLinearEquiv_e_smul j) (fun j _ => tensorSignLinearEquiv_f_smul j)
      (fun j _ => tensorSignLinearEquiv_k_smul j))
    (by
      convert (tensorSignLinearEquiv q m ε).bijective
      exact funext (homOfVec_apply _ _ _ _))).symm

/-- The inverse of `tensorSignEquiv` sends `v_j` to `(-1)^j v_j ⊗ w`. -/
@[simp]
theorem tensorSignEquiv_symm_vec (j : ℤ) :
    (tensorSignEquiv q m ε).symm (vec q m (-ε) j) =
      (-1 : ℂ) ^ j • tmul ℂ (UqSl2 q) (vec q m ε j) (vec q 0 (-1) 0) := by
  rw [tensorSignEquiv, LinearEquiv.symm_symm, LinearEquiv.ofBijective_apply, homOfVec_apply,
    LinearEquiv.coe_coe, tensorSignLinearEquiv_vec]

/-- `tensorSignEquiv` sends `v_j ⊗ w` to `(-1)^j v_j`. -/
@[simp]
theorem tensorSignEquiv_tmul_vec (j : ℤ) :
    tensorSignEquiv q m ε (tmul ℂ (UqSl2 q) (vec q m ε j) (vec q 0 (-1) 0)) =
      (-1 : ℂ) ^ j • vec q m (-ε) j := by
  rw [← LinearEquiv.eq_symm_apply, LinearMapClass.map_smul_of_tower, tensorSignEquiv_symm_vec,
    smul_smul, ← mul_zpow]
  simp

/-! ### Comparing the two tensor orders -/

variable (q m ε) in
/-- The two tensor orders of the sign representation with a ladder module are isomorphic:
`L_0^- ⊗ L_m^ε ≃ L_m^ε ⊗ L_0^-`, sending `w ⊗ v_j` to `(-1)^j v_j ⊗ w`. -/
def signTensorCommEquiv :
    Tensor ℂ (UqSl2 q) (LadderModule q 0 (-1)) (LadderModule q m ε) ≃ₗ[UqSl2 q]
      Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q 0 (-1)) :=
  (signTensorEquiv q m ε).trans (tensorSignEquiv q m ε).symm

/-- `signTensorCommEquiv` sends `w ⊗ v_j` to `(-1)^j v_j ⊗ w`. -/
@[simp]
theorem signTensorCommEquiv_tmul_vec (j : ℤ) :
    signTensorCommEquiv q m ε (tmul ℂ (UqSl2 q) (vec q 0 (-1) 0) (vec q m ε j)) =
      (-1 : ℂ) ^ j • tmul ℂ (UqSl2 q) (vec q m ε j) (vec q 0 (-1) 0) := by
  simp [signTensorCommEquiv]

/-- The inverse of `signTensorCommEquiv` sends `v_j ⊗ w` to `(-1)^j w ⊗ v_j`. -/
@[simp]
theorem signTensorCommEquiv_symm_tmul_vec (j : ℤ) :
    (signTensorCommEquiv q m ε).symm (tmul ℂ (UqSl2 q) (vec q m ε j) (vec q 0 (-1) 0)) =
      (-1 : ℂ) ^ j • tmul ℂ (UqSl2 q) (vec q 0 (-1) 0) (vec q m ε j) := by
  rw [LinearEquiv.symm_apply_eq, LinearMapClass.map_smul_of_tower, signTensorCommEquiv_tmul_vec,
    smul_smul, ← mul_zpow]
  simp

/-- For `m ≥ 1` and `q ≠ ±1`, no module map `L_0^- ⊗ L_m^ε → L_m^ε ⊗ L_0^-` flips the tensor
factors: the flip does not commute with `F`. Hence the alternating rescaling in
`signTensorCommEquiv` cannot be dropped. -/
theorem not_exists_linearMap_tmul_eq_tmul (hq : q - q⁻¹ ≠ 0) (hm : 1 ≤ m) :
    ¬ ∃ φ : Tensor ℂ (UqSl2 q) (LadderModule q 0 (-1)) (LadderModule q m ε) →ₗ[UqSl2 q]
        Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q 0 (-1)),
      ∀ x y, φ (tmul ℂ (UqSl2 q) x y) = tmul ℂ (UqSl2 q) y x := by
  rintro ⟨φ, hφ⟩
  -- Applying `tensorSignEquiv` to `φ (F • (w ⊗ v₀)) = F • φ (w ⊗ v₀)` gives `-v₁ = v₁`.
  have h : -vec q m (-ε) 1 = vec q m (-ε) 1 := by
    simpa [hφ, quantumInteger_one hq] using congrArg (tensorSignEquiv q m ε)
      (φ.map_smul (f q) (tmul ℂ (UqSl2 q) (vec q 0 (-1) 0) (vec q m ε 0)))
  have h₁ := congrArg (fun x => (basis q m (-ε)).repr x ⟨1, by omega⟩) h
  norm_num at h₁

end TauCeti.UqSl2.LadderModule
