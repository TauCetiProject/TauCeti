/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Basic

/-!
# Antipode identities for comodules over a commutative Hopf algebra

Let `N` be a right comodule over a commutative Hopf algebra `H`. The map
`TauCeti.Comodule.mulCoact : H ⊗[R] N → N ⊗[R] H`, `h ⊗ n ↦ ∑ n₀ ⊗ h n₁`, multiplies the coaction
by `h` in the `H` factor. Geometrically, for `G = Spec H` acting on `N`, it is the shear
`(g, n) ↦ (g n, g)`. Its inverse is built from the antipode `S`: it is the composite of the
coaction on the `N` factor with `TauCeti.Comodule.antipodeShear`, `(n ⊗ c) ⊗ h ↦ S c h ⊗ n`,
so that `n ⊗ h ↦ ∑ S n₁ h ⊗ n₀`.

## Main definitions

* `TauCeti.Comodule.antipodeShear`: the map `(n ⊗ c) ⊗ h ↦ S c h ⊗ n`.
* `TauCeti.Comodule.mulCoact`: the map `h ⊗ n ↦ ∑ n₀ ⊗ h n₁`.
* `TauCeti.Comodule.mulCoactEquiv`: `TauCeti.Comodule.mulCoact` as a linear equivalence.

## Main results

* `TauCeti.Comodule.mulCoact_antipodeShear_coact` and `TauCeti.Comodule.antipodeShear_mulCoact`:
  `n ⊗ h ↦ ∑ S n₁ h ⊗ n₀` is a two-sided inverse of `TauCeti.Comodule.mulCoact`.
-/

public section

open scoped TensorProduct

namespace TauCeti

namespace Comodule

variable {R H N : Type*} [CommSemiring R] [AddCommMonoid N] [Module R N]

section Bialgebra

variable [Semiring H] [Bialgebra R H] [Comodule R H N]

variable (R H N) in
/-- The map `h ⊗ n ↦ (1 ⊗ h) • coact n = ∑ n₀ ⊗ h n₁`. -/
noncomputable def mulCoact : H ⊗[R] N →ₗ[R] N ⊗[R] H :=
  TensorProduct.lift ((LinearMap.lTensorHom N ∘ₗ LinearMap.mul R H).compl₂
    (Comodule.coact (R := R) (C := H)))

@[simp]
theorem mulCoact_tmul (h : H) (n : N) :
    mulCoact R H N (h ⊗ₜ n) =
      (LinearMap.mulLeft R h).lTensor N (Comodule.coact (R := R) (C := H) n) :=
  (rfl)

end Bialgebra

section HopfAlgebra

variable [Semiring H] [HopfAlgebra R H]

variable (R H N) in
/-- The map `(n ⊗ c) ⊗ h ↦ S c * h ⊗ n`, where `S` is the antipode. -/
noncomputable def antipodeShear : (N ⊗[R] H) ⊗[R] H →ₗ[R] H ⊗[R] N :=
  (TensorProduct.comm R N H).toLinearMap ∘ₗ
    (LinearMap.mul' R H ∘ₗ (HopfAlgebra.antipode R).rTensor H).lTensor N ∘ₗ
    (TensorProduct.assoc R N H H).toLinearMap

@[simp]
theorem antipodeShear_tmul (n : N) (c h : H) :
    antipodeShear R H N ((n ⊗ₜ c) ⊗ₜ h) = (HopfAlgebra.antipode R c * h) ⊗ₜ[R] n := by
  simp [antipodeShear]

end HopfAlgebra

section CommHopfAlgebra

variable [CommSemiring H] [HopfAlgebra R H] [Comodule R H N]

/-- `∑ (1 ⊗ S n₁ h) • coact n₀ = n ⊗ h`: the map `n ⊗ h ↦ ∑ S n₁ h ⊗ n₀` is a right inverse of
`TauCeti.Comodule.mulCoact`. -/
theorem mulCoact_antipodeShear_coact (n : N) (h : H) :
    mulCoact R H N (antipodeShear R H N (Comodule.coact (R := R) (C := H) n ⊗ₜ h)) =
      n ⊗ₜ h := by
  -- `(m ⊗ c) ⊗ d ↦ m ⊗ h (c S d)`, to be evaluated on `(coact ⊗ id) (coact n) = ∑ n₀ ⊗ Δ n₁`.
  let K : (N ⊗[R] H) ⊗[R] H →ₗ[R] N ⊗[R] H :=
    (LinearMap.mulLeft R h ∘ₗ LinearMap.mul' R H ∘ₗ
      (HopfAlgebra.antipode R).lTensor H).lTensor N ∘ₗ (TensorProduct.assoc R N H H).toLinearMap
  have hK (t : N ⊗[R] H) : mulCoact R H N (antipodeShear R H N (t ⊗ₜ h)) =
      K ((Comodule.coact (R := R) (C := H)).rTensor H t) := by
    induction t with
    | add t t' ht ht' => simp only [TensorProduct.add_tmul, map_add, ht, ht']
    | tmul m c =>
      rw [antipodeShear_tmul, mulCoact_tmul, LinearMap.rTensor_tmul]
      induction Comodule.coact (R := R) (C := H) m with
      | add t t' ht ht' => simp only [TensorProduct.add_tmul, map_add, ht, ht']
      | tmul m' c' => simp [K, mul_comm]
  rw [hK, ← (TensorProduct.assoc R N H H).symm_apply_apply
    ((Comodule.coact (R := R) (C := H)).rTensor H (Comodule.coact n)), Comodule.coassoc_apply]
  simp only [K, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    ← LinearMap.lTensor_comp_apply, LinearMap.comp_assoc, HopfAlgebra.mul_antipode_lTensor_comul]
  rw [← LinearMap.comp_assoc, LinearMap.lTensor_comp_apply, Comodule.lTensor_counit_coact]
  simp

/-- The antipode shear of `(1 ⊗ h) • coact m = ∑ m₀ ⊗ h m₁` is `∑ S m₁ h m₂ ⊗ m₀ = h ⊗ m`: the map
`n ⊗ h ↦ ∑ S n₁ h ⊗ n₀` is a left inverse of `TauCeti.Comodule.mulCoact`. -/
theorem antipodeShear_mulCoact (h : H) (m : N) :
    antipodeShear R H N
        ((Comodule.coact (R := R) (C := H)).rTensor H (mulCoact R H N (h ⊗ₜ m))) =
      h ⊗ₜ[R] m := by
  have hshear : antipodeShear R H N ∘ₗ (LinearMap.mulLeft R h).lTensor (N ⊗[R] H) ∘ₗ
      (TensorProduct.assoc R N H H).symm.toLinearMap =
      (LinearMap.mulLeft R h ∘ₗ LinearMap.mul' R H ∘ₗ
        (HopfAlgebra.antipode R).rTensor H).rTensor N ∘ₗ
          (TensorProduct.comm R N (H ⊗[R] H)).toLinearMap := by
    refine TensorProduct.ext_threefold' fun n x y ↦ ?_
    simp [antipodeShear, mul_left_comm]
  rw [mulCoact_tmul, ← LinearMap.comp_apply (g := (LinearMap.mulLeft R h).lTensor N),
    LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply,
    ← (TensorProduct.assoc R N H H).symm_apply_apply
      ((Comodule.coact (R := R) (C := H)).rTensor H (Comodule.coact m)), Comodule.coassoc_apply]
  have := congr($hshear ((Coalgebra.comul (R := R) (A := H)).lTensor N (Comodule.coact m)))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at this
  have hm : m = TensorProduct.rid R N ((Coalgebra.counit (R := R) (A := H)).lTensor N
      (Comodule.coact (R := R) (C := H) m)) := by simp
  rw [this]
  conv_rhs => rw [hm]
  induction Comodule.coact (R := R) (C := H) m with
  | add t t' ht ht' => simp only [map_add, ht, ht', TensorProduct.tmul_add]
  | tmul n c =>
    simp [HopfAlgebra.mul_antipode_rTensor_comul_apply, ← Algebra.commutes, ← Algebra.smul_def,
      TensorProduct.smul_tmul]

variable (R H N) in
/-- `TauCeti.Comodule.mulCoact` as a linear equivalence, with inverse `n ⊗ h ↦ ∑ S n₁ h ⊗ n₀`. -/
noncomputable def mulCoactEquiv : H ⊗[R] N ≃ₗ[R] N ⊗[R] H :=
  LinearEquiv.ofLinearMap (mulCoact R H N)
    (antipodeShear R H N ∘ₗ (Comodule.coact (R := R) (C := H)).rTensor H)
    (TensorProduct.ext' fun n h ↦ by
      simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearMap.id_apply,
        mulCoact_antipodeShear_coact])
    (TensorProduct.ext' fun h m ↦ by
      simp only [LinearMap.comp_apply, LinearMap.id_apply, antipodeShear_mulCoact])

@[simp]
theorem coe_mulCoactEquiv : (mulCoactEquiv R H N : H ⊗[R] N →ₗ[R] N ⊗[R] H) = mulCoact R H N :=
  (rfl)

@[simp]
theorem mulCoactEquiv_apply (t : H ⊗[R] N) : mulCoactEquiv R H N t = mulCoact R H N t :=
  (rfl)

@[simp]
theorem mulCoactEquiv_symm_tmul (n : N) (h : H) :
    (mulCoactEquiv R H N).symm (n ⊗ₜ h) =
      antipodeShear R H N (Comodule.coact (R := R) (C := H) n ⊗ₜ h) :=
  (rfl)

end CommHopfAlgebra

end Comodule

end TauCeti
