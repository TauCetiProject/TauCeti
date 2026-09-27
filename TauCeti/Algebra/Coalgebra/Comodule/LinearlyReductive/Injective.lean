/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive

/-!
# Linear reductivity and injective coalgebra morphisms

Over a field, corestriction along an injective coalgebra morphism does not change the
invariant subspaces of a comodule. A linear retraction of the coalgebra morphism recovers
the original coaction from its corestriction. Consequently complete reducibility of the
corestricted comodule implies complete reducibility of the original one, and linear
reductivity passes from a coalgebra to its subcoalgebras.

For coordinate Hopf algebras, this applies to the injective coordinate morphism of a
quotient-group projection. It is the complete-reducibility input for passing linear
reductivity to quotients in the characteristic-zero reductive-group comparison.

## References

* J. S. Milne, *Algebraic Groups* (2017), §12.
* M. Sweedler, *Hopf Algebras*, Chapter 2.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w x

namespace Comodule

variable {k : Type u} [CommSemiring k]
variable {C : Type v} {D : Type w}
variable [AddCommMonoid C] [Module k C] [Coalgebra k C]
variable [AddCommMonoid D] [Module k D] [Coalgebra k D]
variable {V : Type x} [AddCommMonoid V] [Module k V] [Comodule k C V]

/-- Complete reducibility descends along a coalgebra morphism with a linear retraction. -/
theorem IsCompletelyReducible.of_corestrict_of_split (f : C →ₗc[k] D)
    (r : D →ₗ[k] C) (hr : r.comp f.toLinearMap = LinearMap.id)
    (h : letI : Comodule k D V := Comodule.Corestrict f
      IsCompletelyReducible k D V) :
    IsCompletelyReducible k C V := by
  let _ : Comodule k D V := Comodule.Corestrict f
  exact isCompletelyReducible_of_orderIso k
    (Subcomodule.corestrictOrderIsoOfSplit f r hr).symm (OrderIso.refl _)
    (fun A ↦ by simp) h

end Comodule

namespace Comodule

variable {k : Type u} [Field k]
variable {C : Type v} {D : Type w}
variable [AddCommMonoid C] [Module k C] [Coalgebra k C]
variable [AddCommMonoid D] [Module k D] [Coalgebra k D]
variable {V : Type x} [AddCommMonoid V] [Module k V] [Comodule k C V]

/-- Complete reducibility descends along an injective coalgebra morphism. -/
theorem IsCompletelyReducible.of_corestrict_of_injective (f : C →ₗc[k] D)
    (h : letI : Comodule k D V := Comodule.Corestrict f
      IsCompletelyReducible k D V) (hf : Function.Injective f) :
    IsCompletelyReducible k C V := by
  let _ : AddCommGroup C := Module.addCommMonoidToAddCommGroup k
  let _ : AddCommGroup D := Module.addCommMonoidToAddCommGroup k
  let l : C →ₗ[k] D := f.toLinearMap
  have hker : LinearMap.ker l = ⊥ :=
    LinearMap.ker_eq_bot_of_injective (f := l) (by
      intro x y hxy
      exact hf hxy)
  let r : D →ₗ[k] C := l.leftInverse
  have hr : r.comp f.toLinearMap = LinearMap.id :=
    LinearMap.leftInverse_comp_of_inj hker
  exact IsCompletelyReducible.of_corestrict_of_split f r hr h

end Comodule

namespace Coalgebra

variable {k : Type u} [Field k]
variable {C : Type v} {D : Type w}
variable [AddCommMonoid C] [Module k C] [Coalgebra k C]
variable [AddCommMonoid D] [Module k D] [Coalgebra k D]

/-- A subcoalgebra of a linearly reductive coalgebra is linearly reductive. -/
theorem IsLinearlyReductive.of_injective (f : C →ₗc[k] D)
    (hf : Function.Injective f) (hD : IsLinearlyReductive.{u, w, x} k D) :
    IsLinearlyReductive.{u, v, x} k C := by
  apply IsLinearlyReductive.of_forall_isCompletelyReducible
  intro V _ _ _ _
  let _ : Comodule k D V := Comodule.Corestrict f
  exact Comodule.IsCompletelyReducible.of_corestrict_of_injective f
    (hD.isCompletelyReducible_sameUniverse k V) hf

end Coalgebra

end TauCeti
