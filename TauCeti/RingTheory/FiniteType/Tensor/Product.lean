/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.FiniteType.PointSeparation
import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Reduced tensor products over an algebraically closed field

A reduced finite-type algebra over an algebraically closed field stays reduced after tensoring
with any reduced algebra. This applies in particular to the tensor square of a coordinate ring
modulo its nilradical, before any Hopf structure has been constructed on that quotient.

The argument uses the Nullstellensatz point-separation theorem from
`TauCeti.RingTheory.FiniteType.PointSeparation`. Specializing the finite-type factor at each
rational point kills a nilpotent tensor. Expanding in a basis of the other factor then shows
that every coefficient vanishes at all rational points, hence is zero.

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
  classical
  let b := Module.Free.chooseBasis k B
  let c := b.baseChange A
  refine ⟨fun x hx ↦ ?_⟩
  apply c.repr.injective
  ext i
  simp only [map_zero, Finsupp.zero_apply]
  apply eq_of_forall_algHom_apply_eq (k := k) (K := k)
  intro f
  let F : A ⊗[k] B →ₐ[k] B := Algebra.TensorProduct.lift
    ((Algebra.ofId k B).comp f) (AlgHom.id k B) (fun _ _ ↦ Commute.all _ _)
  have hcoord (z : A ⊗[k] B) : b.repr (F z) i = f (c.repr z i) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' => simp [hz, hz']
    | tmul a d =>
      simp only [F, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply,
        Algebra.ofId_apply, AlgHom.id_apply, ← Algebra.smul_def, c,
        Module.Basis.baseChange_repr_tmul]
      simp [mul_comm]
  have hzero : F x = 0 := (hx.map F).eq_zero
  simpa [hzero] using (hcoord x).symm

end TauCeti
