/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.GroupTheory.GroupAction.Hom

/-!
# Equivariant equivalences of additive groups

This file records elementary facts about additive equivalences that intertwine group actions.

## Main results

* `AddEquiv.symm_map_smul_of_map_smul`: the inverse of an equivariant additive
  equivalence is equivariant.
* `AddEquiv.symm_map_smul_of_map_mulEquiv_smul`: the same along a change of the acting group by a
  multiplicative equivalence.
* `AddEquiv.ofBijective_smul`: the additive equivalence of a bijective equivariant homomorphism is
  equivariant, and `AddEquiv.ofBijective_toDistribMulActionHom` identifies the equivariant
  homomorphism it carries with the original one.
-/

public section

namespace AddEquiv

section

variable {G M N : Type*} [Add M] [Add N] [SMul G M] [SMul G N]

/-- The inverse of an equivariant additive equivalence is equivariant. -/
theorem symm_map_smul_of_map_smul (e : M ≃+ N)
    (hequiv : ∀ (g : G) (m : M), e (g • m) = g • e m) (g : G) (n : N) :
    e.symm (g • n) = g • e.symm n := by
  apply e.injective
  rw [e.apply_symm_apply, hequiv, e.apply_symm_apply]

end

section ChangeOfGroup

variable {G H M N : Type*} [Mul G] [Mul H] [Add M] [Add N] [SMul G M] [SMul H N]

/-- The inverse of an additive equivalence compatible with a change of the acting group is
compatible with the inverse change: if `e (φ h • m) = h • e m` for a multiplicative equivalence
`φ : H ≃* G`, then `e.symm (φ.symm g • n) = g • e.symm n`. -/
theorem symm_map_smul_of_map_mulEquiv_smul (e : M ≃+ N) (φ : H ≃* G)
    (hequiv : ∀ (h : H) (m : M), e (φ h • m) = h • e m) (g : G) (n : N) :
    e.symm (φ.symm g • n) = g • e.symm n := by
  apply e.injective
  rw [e.apply_symm_apply]
  conv_rhs => rw [← φ.apply_symm_apply g, hequiv, e.apply_symm_apply]

end ChangeOfGroup

section OfBijective

variable {G M N : Type*} [Monoid G] [AddMonoid M] [AddMonoid N] [DistribMulAction G M]
  [DistribMulAction G N]

/-- The additive equivalence of a bijective equivariant homomorphism is equivariant. The statement
is spelled on the equivalence so that it can be fed to constructions that take an equivariant
additive equivalence. -/
theorem ofBijective_smul {f : M →+[G] N} (hf : Function.Bijective f) (g : G) (m : M) :
    AddEquiv.ofBijective (f : M →+ N) hf (g • m) = g • AddEquiv.ofBijective (f : M →+ N) hf m :=
  map_smul f g m

/-- The equivariant homomorphism carried by the additive equivalence of a bijective equivariant
homomorphism is that homomorphism. -/
theorem ofBijective_toDistribMulActionHom {f : M →+[G] N} (hf : Function.Bijective f) :
    ({ (AddEquiv.ofBijective (f : M →+ N) hf).toAddMonoidHom with
      map_smul' := ofBijective_smul hf } : M →+[G] N) = f :=
  DistribMulActionHom.ext fun _ => rfl

end OfBijective

end AddEquiv

end
