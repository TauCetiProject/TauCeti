/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import TauCeti.Algebra.HopfAlgebra
import TauCeti.Algebra.HopfAlgebra.HopfIdeal

/-!
# Kernels of Hopf algebra morphisms

This file records that the kernel of a surjective morphism of commutative Hopf algebras is a
Hopf ideal. The surjectivity hypothesis is the exactness input needed to identify the kernel
of the tensor-square map with `ker f ⊗ H + H ⊗ ker f`.

This is a Layer 3 prerequisite for the reductive-groups roadmap target "Hopf ideals ↔ closed
subgroup schemes", specifically the "kernels" part of the Hopf-ideal/closed-subgroup
dictionary.

## Main declarations

* `TauCeti.HopfIdeal.ker`: the Hopf ideal given by the kernel of a surjective bialgebra
  morphism between commutative Hopf algebras.
* `TauCeti.HopfIdeal.ker_toIdeal` and `TauCeti.HopfIdeal.mem_ker`: its characteristic API.

## References

The construction is the standard kernel Hopf ideal. The tensor-kernel exactness step uses
Mathlib's `Algebra.TensorProduct.map_ker`.
-/

open scoped TensorProduct

namespace TauCeti

universe u v w

namespace HopfIdeal

variable {R : Type u} {H : Type v} {K : Type w}
variable [CommRing R] [CommRing H] [CommRing K]
variable [HopfAlgebra R H] [HopfAlgebra R K]

/-- The tensor-square map sends the comultiplication of an element in the kernel of a
bialgebra morphism to zero. -/
private theorem comul_mem_tensor_map_ker (f : H →ₐc[R] K) {x : H}
    (hx : x ∈ RingHom.ker (f : H →ₐ[R] K)) :
    Coalgebra.comul (R := R) x ∈
      RingHom.ker
        (Algebra.TensorProduct.map (f : H →ₐ[R] K) (f : H →ₐ[R] K)).toRingHom := by
  rw [RingHom.mem_ker]
  calc
    Algebra.TensorProduct.map (f : H →ₐ[R] K) (f : H →ₐ[R] K) (Coalgebra.comul (R := R) x)
        = Coalgebra.comul (R := R) (f x) := CoalgHomClass.map_comp_comul_apply f x
    _ = 0 := by
      have hfx : f x = 0 := RingHom.mem_ker.mp hx
      simpa using congrArg (Coalgebra.comul (R := R) (A := K)) hfx

/-- The kernel of a surjective bialgebra morphism of commutative Hopf algebras, as a
Hopf ideal. -/
def ker (f : H →ₐc[R] K) (hf : Function.Surjective f) : HopfIdeal R H :=
  ofIdeal (RingHom.ker (f : H →ₐ[R] K))
    (by
      intro x hx
      have hker := comul_mem_tensor_map_ker (R := R) f hx
      change Coalgebra.comul (R := R) x ∈
        RingHom.ker (Algebra.TensorProduct.map (f : H →ₐ[R] K) (f : H →ₐ[R] K)) at hker
      rw [Algebra.TensorProduct.map_ker (f := (f : H →ₐ[R] K)) (g := (f : H →ₐ[R] K))
        hf hf] at hker
      change Coalgebra.comul (R := R) x ∈
        Ideal.map Algebra.TensorProduct.includeLeft (RingHom.ker (f : H →ₐ[R] K)) ⊔
          Ideal.map Algebra.TensorProduct.includeRight (RingHom.ker (f : H →ₐ[R] K))
      exact hker)
    (by
      intro x hx
      have h := LinearMap.congr_fun (CoalgHomClass.counit_comp f) x
      change Coalgebra.counit (R := R) (f x) = Coalgebra.counit (R := R) x at h
      have hfx : f x = 0 := RingHom.mem_ker.mp hx
      simpa [hfx] using h.symm)
    (by
      intro x hx
      rw [RingHom.mem_ker]
      change f (HopfAlgebra.antipode R x) = 0
      have hfx : f x = 0 := RingHom.mem_ker.mp hx
      rw [BialgHom.map_antipode, hfx]
      simp)

/-- The underlying ideal of the kernel Hopf ideal is the ring-hom kernel. -/
@[simp]
theorem ker_toIdeal (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    (ker f hf).toIdeal = RingHom.ker (f : H →ₐ[R] K) :=
  rfl

/-- Membership in the kernel Hopf ideal is vanishing under the bialgebra morphism. -/
@[simp]
theorem mem_ker (f : H →ₐc[R] K) (hf : Function.Surjective f) {x : H} :
    x ∈ ker f hf ↔ f x = 0 := by
  rw [← mem_toIdeal, ker_toIdeal, RingHom.mem_ker]
  rfl

/-- The kernel Hopf ideal is bottom exactly when the morphism is injective. -/
theorem ker_eq_bot_iff (f : H →ₐc[R] K) (hf : Function.Surjective f) :
    ker f hf = ⊥ ↔ Function.Injective f := by
  constructor
  · intro h x y hxy
    have hmem : x - y ∈ ker f hf := by
      rw [mem_ker, map_sub, hxy, sub_self]
    have hzero : x - y = 0 := by
      rw [h] at hmem
      exact (HopfIdeal.mem_bot (R := R) (H := H)).mp hmem
    exact sub_eq_zero.mp hzero
  · intro hinj
    ext x
    rw [mem_ker, mem_bot]
    exact ⟨fun hx => hinj (by simpa using hx), fun hx => by rw [hx, map_zero]⟩

end HopfIdeal

end TauCeti
