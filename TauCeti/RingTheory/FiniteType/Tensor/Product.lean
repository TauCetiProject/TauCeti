/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.FiniteType.PointSeparation
import TauCeti.LinearAlgebra.TensorProduct.Separation
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Reduced tensor products over an algebraically closed field

A reduced finite-type algebra over an algebraically closed field stays reduced after tensoring
with any reduced algebra. This applies in particular to the tensor square of a coordinate ring
modulo its nilradical, before any Hopf structure has been constructed on that quotient.

The argument uses the Nullstellensatz point-separation theorem from
`TauCeti.RingTheory.FiniteType.PointSeparation`. Specializing the finite-type factor at each
rational point kills a nilpotent tensor. The shared linear separation lemma
in `TauCeti.LinearAlgebra.TensorProduct.Separation` then detects that the tensor is zero.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §11.4, for the application to
  reductions of affine groups.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w

/-- The tensor product of a reduced finite-type algebra over an algebraically closed field
with any reduced algebra is reduced. Only the first factor needs to be of finite type. -/
instance instIsReducedTensorProductOfIsAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type v) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsReduced A]
    (B : Type w) [CommRing B] [Algebra k B] [IsReduced B] :
    IsReduced (A ⊗[k] B) := by
  refine ⟨fun x hx ↦ ?_⟩
  apply tensor_eq_zero_of_forall_lid_rTensor_eq_zero (fun f : A →ₐ[k] k ↦ f.toLinearMap)
    (fun a ha ↦ eq_of_forall_algHom_apply_eq (k := k) (K := k)
      (fun f ↦ (ha f).trans (map_zero f).symm)) x
  intro f
  exact (hx.map ((Algebra.TensorProduct.lid k B).toAlgHom.comp
    (Algebra.TensorProduct.map f (AlgHom.id k B)))).eq_zero

end TauCeti
