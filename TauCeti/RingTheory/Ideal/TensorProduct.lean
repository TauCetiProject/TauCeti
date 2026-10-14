/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Kernel

/-!
# Extended ideals as tensor images

The scalar multiplication equivalence `S ⊗[R] R ≃ₗ[S] S` identifies the base change of
an ideal with its extension along `algebraMap R S`. This permits kernel computations
on tensor products to be read as membership statements in extended ideals.
-/

public section

open TensorProduct

namespace Ideal

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- The extended ideal is the image of its tensor base change under scalar multiplication. -/
theorem map_eq_baseChange_map_rid (I : Ideal R) :
    I.map (algebraMap R S) =
      (I.baseChange S).map (AlgebraTensorModule.rid R S S).toLinearMap := by
  rw [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe,
    Set.image_image]
  simp only [LinearEquiv.coe_coe, TensorProduct.mk_apply,
    AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_one]
  rfl

end Ideal

namespace LinearMap

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/-- Flatness tests membership in an extended scalar-source kernel on `s ⊗ₜ 1`. -/
theorem mem_map_ker_iff_of_flat [Module.Flat R S] (f : R →ₗ[R] M) (s : S) :
    s ∈ Ideal.map (algebraMap R S) (ker f) ↔ f.baseChange S (s ⊗ₜ[R] 1) = 0 := by
  rw [Ideal.map_eq_baseChange_map_rid, ← f.ker_baseChange_of_flat S,
    Submodule.mem_map_equiv, AlgebraTensorModule.rid_symm_apply, mem_ker]

end LinearMap
