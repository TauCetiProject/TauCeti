/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Integrality of tensor products of algebra morphisms

If `f : S →ₐ[R] S'` and `g : T →ₐ[R] T'` are integral `R`-algebra homomorphisms, then their tensor
product `Algebra.TensorProduct.map f g : S ⊗[R] T →ₐ[R] S' ⊗[R] T'` is also integral
(`RingHom.IsIntegral.tensorProductMap`). This is the integrality counterpart of
`RingHom.Finite.tensorProductMap`.

## Main results

* `RingHom.IsIntegral.tensorProductMap`: tensor product of two integral `R`-algebra homomorphisms
  is integral.
-/

public section

open scoped TensorProduct

/-- The tensor product `Algebra.TensorProduct.map f g : S ⊗[R] T →ₐ[R] S' ⊗[R] T'` of two integral
`R`-algebra homomorphisms `f : S →ₐ[R] S'` and `g : T →ₐ[R] T'` is integral. -/
theorem RingHom.IsIntegral.tensorProductMap
    {R S S' T T' : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing S'] [CommRing T']
    [Algebra R S] [Algebra R T] [Algebra R S'] [Algebra R T']
    {f : S →ₐ[R] S'} (hf : f.toRingHom.IsIntegral) {g : T →ₐ[R] T'} (hg : g.toRingHom.IsIntegral) :
    (Algebra.TensorProduct.map f g).toRingHom.IsIntegral := by
  intro z
  refine z.inductionOn (fun s' t' ↦ ?_) (fun _ _ hu hv ↦ RingHom.IsIntegralElem.add _ hu hv)
  have hs' : (Algebra.TensorProduct.map f g).toRingHom.IsIntegralElem (s' ⊗ₜ[R] (1 : T')) := by
    have h := (hf s').map
      (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S') (B := T')).toRingHom
    rw [AlgHom.toRingHom_eq_coe, AlgHom.toRingHom_eq_coe, ← AlgHom.comp_toRingHom,
      ← Algebra.TensorProduct.map_comp_includeLeft f g, AlgHom.comp_toRingHom] at h
    simpa using h.of_comp
  have ht' : (Algebra.TensorProduct.map f g).toRingHom.IsIntegralElem ((1 : S') ⊗ₜ[R] t') := by
    have h := (hg t').map
      (Algebra.TensorProduct.includeRight (R := R) (A := S') (B := T')).toRingHom
    rw [AlgHom.toRingHom_eq_coe, AlgHom.toRingHom_eq_coe, ← AlgHom.comp_toRingHom,
      ← Algebra.TensorProduct.map_comp_includeRight f g, AlgHom.comp_toRingHom] at h
    simpa using h.of_comp
  simpa [Algebra.TensorProduct.tmul_mul_tmul] using RingHom.IsIntegralElem.mul _ hs' ht'
