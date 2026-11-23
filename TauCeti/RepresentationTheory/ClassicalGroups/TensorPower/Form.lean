/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import TauCeti.RepresentationTheory.ClassicalGroups.TensorPower.Basic

/-!
# The standard Hermitian form on a tensor power

The tensor power `(𝕜ⁿ)^{⊗d}` over `𝕜 = ℝ` or `ℂ` carries the positive definite Hermitian form
`TauCeti.tensorPowerForm` for which the monomial basis is orthonormal; on pure tensors it is the
product of the standard Hermitian forms of the factors. It is **contravariant**: the adjoint of the
action of `g : GL n 𝕜` is the action of the conjugate transpose `star g`.

## Main definitions

* `TauCeti.tensorPowerForm`: the standard Hermitian form on `(𝕜ⁿ)^{⊗d}`.

## Main results

* `TauCeti.tensorPowerForm_tprod_tprod`: its value on pure tensors.
* `TauCeti.isSymm_tensorPowerForm`, `TauCeti.tensorPowerForm_apply_self_pos`: it is Hermitian and
  positive definite.
* `TauCeti.tensorPowerForm_tensorPowerRep_apply`: contravariance.
-/

public section

open Matrix Module
open scoped ComplexOrder TensorProduct

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] (n d : ℕ)

/-- **The standard Hermitian form on a tensor power**: the form on `(𝕜ⁿ)^{⊗d}` for which the
monomial basis `TauCeti.tensorPowerBasis` is orthonormal. By `TauCeti.tensorPowerForm_tprod_tprod`
it is the product of the standard Hermitian forms of the tensor factors, so it does not depend on
the basis. -/
noncomputable def tensorPowerForm :
    (⨂[𝕜]^d (Fin n → 𝕜)) →ₗ⋆[𝕜] (⨂[𝕜]^d (Fin n → 𝕜)) →ₗ[𝕜] 𝕜 :=
  Matrix.toLinearMapₛₗ₂ (starRingEnd 𝕜) (tensorPowerBasis 𝕜 n d) (tensorPowerBasis 𝕜 n d) 1

variable {n d}

/-- The value of the standard Hermitian form in the coordinates of the monomial basis. -/
theorem tensorPowerForm_apply (x y : ⨂[𝕜]^d (Fin n → 𝕜)) :
    tensorPowerForm n d x y =
      ∑ w, star ((tensorPowerBasis 𝕜 n d).repr x w) * (tensorPowerBasis 𝕜 n d).repr y w := by
  simp [tensorPowerForm, Matrix.one_apply]

/-- On pure tensors, the standard Hermitian form of a tensor power is the product of the standard
Hermitian forms of the factors. -/
@[simp]
theorem tensorPowerForm_tprod_tprod (x y : Fin d → Fin n → 𝕜) :
    tensorPowerForm n d (PiTensorProduct.tprod 𝕜 x) (PiTensorProduct.tprod 𝕜 y) =
      ∏ i, star (x i) ⬝ᵥ y i := by
  simp only [tensorPowerForm_apply, tensorPowerBasis_def, Basis.piTensorProduct_repr_tprod_apply,
    dotProduct, Finset.prod_univ_sum, Fintype.piFinset_univ, star_prod, ← Finset.prod_mul_distrib]
  simp

/-- The standard form of a tensor power is Hermitian. -/
theorem isSymm_tensorPowerForm : (tensorPowerForm (𝕜 := 𝕜) n d).IsSymm where
  eq x y := by
    simp [tensorPowerForm_apply, mul_comm]

/-- The standard form of a tensor power is positive definite. -/
theorem tensorPowerForm_apply_self_pos {x : ⨂[𝕜]^d (Fin n → 𝕜)} (hx : x ≠ 0) :
    0 < tensorPowerForm n d x x := by
  obtain ⟨w, hw⟩ : ∃ w, (tensorPowerBasis 𝕜 n d).repr x w ≠ 0 := by
    contrapose! hx
    exact (tensorPowerBasis 𝕜 n d).repr.map_eq_zero_iff.mp (Finsupp.ext hx)
  rw [tensorPowerForm_apply]
  exact Finset.sum_pos' (fun _ _ ↦ star_mul_self_nonneg _)
    ⟨w, Finset.mem_univ w, by
      rw [RCLike.star_def, RCLike.conj_mul]
      exact_mod_cast pow_pos (norm_pos_iff.mpr hw) 2⟩

/-- **Contravariance of the standard form.** The adjoint of the action of `g` on a tensor power is
the action of the conjugate transpose `star g`. -/
theorem tensorPowerForm_tensorPowerRep_apply (g : GL (Fin n) 𝕜) (x y : ⨂[𝕜]^d (Fin n → 𝕜)) :
    tensorPowerForm n d (tensorPowerRep 𝕜 n d g x) y =
      tensorPowerForm n d x (tensorPowerRep 𝕜 n d (star g) y) := by
  have h : (tensorPowerForm n d).comp (tensorPowerRep 𝕜 n d g) =
      (tensorPowerForm n d).compl₂ (tensorPowerRep 𝕜 n d (star g)) := by
    refine (tensorPowerBasis 𝕜 n d).ext fun u ↦ (tensorPowerBasis 𝕜 n d).ext fun v ↦ ?_
    simp [Representation.tensorPower_apply, PiTensorProduct.map_tprod, star_eq_conjTranspose,
      Units.coe_star]
  exact LinearMap.congr_fun₂ h x y

end TauCeti
