/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Scalar torsion in torsion-free modules

Over a commutative semiring with cancellation away from zero, the torsion by a nonzero
scalar in a torsion-free module is trivial. Record this as a subsingleton instance so that
the finiteness and vanishing of these torsion modules follow by typeclass inference.
-/

public section

namespace TauCeti.Submodule

/-- Torsion by a nonzero scalar in a torsion-free module over a commutative semiring with
cancellation away from zero is trivial. -/
instance instSubsingletonTorsionBy {R M : Type*} [CommSemiring R] [IsCancelMulZero R]
    [AddCommMonoid M] [Module R M] [Module.IsTorsionFree R M] (r : R) [NeZero r] :
    Subsingleton (_root_.Submodule.torsionBy R M r) :=
  ⟨fun x y ↦ Subtype.ext <| IsSMulRegular.of_ne_zero (NeZero.ne r)
    (((_root_.Submodule.mem_torsionBy_iff _ _).mp x.property).trans
      ((_root_.Submodule.mem_torsionBy_iff _ _).mp y.property).symm)⟩

end TauCeti.Submodule
