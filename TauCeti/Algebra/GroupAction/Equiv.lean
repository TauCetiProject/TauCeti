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

* `AddEquiv.symm_map_smul_of_map_smul_of_rightInverse`: if `e (φ h • m) = h • e m` for a map
  `φ : H → G` with a right inverse `ψ`, then `e.symm (ψ g • n) = g • e.symm n`. This covers a
  change of the acting group along a multiplicative equivalence.
* `AddEquiv.symm_map_smul_of_map_smul`: the inverse of an equivariant additive
  equivalence is equivariant.
* `AddEquiv.ofBijective_smul`: the additive equivalence of a bijective equivariant homomorphism is
  equivariant, and `AddEquiv.ofBijective_toDistribMulActionHom` identifies the equivariant
  homomorphism it carries with the original one.
-/

public section

namespace AddEquiv

section Symm

variable {G H M N : Type*} [Add M] [Add N] [SMul G M] [SMul H N]

/-- The inverse of an additive equivalence compatible with a change of the acting group is
compatible with a right inverse of that change: if `e (φ h • m) = h • e m` for a map `φ : H → G`
and `ψ : G → H` satisfies `φ (ψ g) = g`, then `e.symm (ψ g • n) = g • e.symm n`. For a
multiplicative equivalence `φ`, take `ψ = φ.symm` and `hφψ = φ.apply_symm_apply`. -/
theorem symm_map_smul_of_map_smul_of_rightInverse (e : M ≃+ N) (φ : H → G) (ψ : G → H)
    (hφψ : Function.RightInverse ψ φ) (hequiv : ∀ (h : H) (m : M), e (φ h • m) = h • e m)
    (g : G) (n : N) :
    e.symm (ψ g • n) = g • e.symm n := by
  simpa [hφψ g] using (congrArg e.symm (hequiv (ψ g) (e.symm n))).symm

/-- The inverse of an equivariant additive equivalence is equivariant. -/
theorem symm_map_smul_of_map_smul [SMul G N] (e : M ≃+ N)
    (hequiv : ∀ (g : G) (m : M), e (g • m) = g • e m) (g : G) (n : N) :
    e.symm (g • n) = g • e.symm n :=
  e.symm_map_smul_of_map_smul_of_rightInverse id id (fun _ ↦ rfl) hequiv g n

end Symm

section OfBijective

variable {G M N F : Type*} [Add M] [Add N] [SMul G M] [SMul G N] [FunLike F M N]
  [AddHomClass F M N] [MulActionHomClass F G M N]

/-- The additive equivalence of a bijective equivariant homomorphism is equivariant. The statement
is spelled on the equivalence so that it can be fed to constructions that take an equivariant
additive equivalence. -/
theorem ofBijective_smul {f : F} (hf : Function.Bijective f) (g : G) (m : M) :
    AddEquiv.ofBijective f hf (g • m) = g • AddEquiv.ofBijective f hf m :=
  map_smul f g m

end OfBijective

section DistribMulActionHom

variable {G M N : Type*} [Monoid G] [AddMonoid M] [AddMonoid N] [DistribMulAction G M]
  [DistribMulAction G N]

/-- The equivariant homomorphism carried by the additive equivalence of a bijective equivariant
homomorphism is that homomorphism. -/
theorem ofBijective_toDistribMulActionHom {f : M →+[G] N} (hf : Function.Bijective f) :
    ({ (AddEquiv.ofBijective f hf).toAddMonoidHom with
      map_smul' := ofBijective_smul hf } : M →+[G] N) = f :=
  DistribMulActionHom.ext fun _ => rfl

end DistribMulActionHom

end AddEquiv

end
