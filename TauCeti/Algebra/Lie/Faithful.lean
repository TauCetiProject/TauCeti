/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Abelian

/-!
# The faithfulness dictionary for Lie representations

A representation of a Lie algebra `L` on a module `M` can be given in two equivalent ways: as a
Lie algebra homomorphism `ρ : L →ₗ⁅R⁆ Module.End R M`, or as a Lie module structure on `M`. The
two passages are Mathlib's definitions

* `LieRingModule.compLieHom M ρ` (with `LieModule.compLieHom M ρ`), the action `⁅x, m⁆ = ρ x m`
  obtained by pulling back the tautological action of `Module.End R M` along `ρ`; and
* `LieModule.toEnd R L M`, the representation `x ↦ ⁅x, ·⁆` of a Lie module.

Neither is an instance, so that a homomorphism into `Module.End R M` never silently becomes a
module structure. This file proves that the two passages are mutually inverse
(`LieModule.toEnd_compLieHom_moduleEnd` and `LieRingModule.compLieHom_toEnd`), and that they
match the notions of faithfulness on the two sides: the action through `ρ` is
`LieModule.IsFaithful` exactly when `ρ` is injective, exactly when `ρ.ker = ⊥`, and its kernel
`LieModule.ker` is `ρ.ker`. In the other direction, Mathlib's `LieModule.isFaithful_iff` and
`LieModule.isFaithful_iff_ker_eq_bot` say that a Lie module is faithful exactly when its
representation `LieModule.toEnd` is injective, exactly when its kernel is trivial.

These statements are special cases of the corresponding facts for the pull-back of an arbitrary
Lie module along an arbitrary Lie algebra homomorphism `f : L₁ →ₗ⁅R⁆ L₂`, which are proved first:
the pulled-back representation is `toEnd R L₂ M ∘ f`, its kernel is the preimage of the kernel of
the `L₂`-action, and it is faithful exactly when `toEnd R L₂ M ∘ f` is injective.

Faithfulness is injectivity, not merely nonvanishing: the adjoint representation of the Heisenberg
algebra is nonzero yet kills the centre (`TauCeti.not_isFaithful_self_heisenberg`), and so does
the adjoint representation of `sl₂` in characteristic two
(`TauCeti.isFaithful_self_slFinTwo_iff_two_ne_zero`).

## Main results

* `LieModule.toEnd_compLieHom`, `LieModule.ker_compLieHom`, `LieModule.isFaithful_compLieHom_iff`:
  the representation, kernel and faithfulness of a Lie module pulled back along a homomorphism.
* `LieModule.toEnd_compLieHom_moduleEnd`: the Lie module defined by a representation `ρ` has
  representation `ρ`.
* `LieRingModule.compLieHom_toEnd`: pulling the tautological action back along the representation
  of a Lie module recovers its Lie module structure.
* `LieModule.ker_compLieHom_moduleEnd`: the kernel of the action through `ρ` is `ρ.ker`.
* `LieModule.isFaithful_compLieHom_moduleEnd_iff` and
  `LieModule.isFaithful_compLieHom_moduleEnd_iff_ker_eq_bot`: the action through `ρ` is faithful
  exactly when `ρ` is injective, exactly when `ρ.ker = ⊥`.
-/

public section

universe u v w w₁

attribute [local instance 100] LieRing.ofAssociativeRing

namespace LieModule

section CompLieHom

variable {R : Type u} {L₁ : Type v} {L₂ : Type w} (M : Type w₁)
variable [CommRing R] [LieRing L₁] [LieAlgebra R L₁] [LieRing L₂] [LieAlgebra R L₂]
variable [AddCommGroup M] [Module R M] [LieRingModule L₂ M] [LieModule R L₂ M]

/-! ### Pulling a Lie module back along a homomorphism -/

/-- The representation of a Lie module pulled back along `f : L₁ →ₗ⁅R⁆ L₂` is the composite of
the representation of the original module with `f`. -/
theorem toEnd_compLieHom (f : L₁ →ₗ⁅R⁆ L₂) :
    letI := LieRingModule.compLieHom M f
    haveI := LieModule.compLieHom (R := R) M f
    toEnd R L₁ M = (toEnd R L₂ M).comp f := by
  let _ := LieRingModule.compLieHom M f
  have _ := LieModule.compLieHom (R := R) M f
  ext x m
  rw [toEnd_apply_apply, LieHom.comp_apply, toEnd_apply_apply]
  exact LieRingModule.compLieHom_apply M f x m

/-- The kernel of the action of `L₁` on a Lie module pulled back along `f : L₁ →ₗ⁅R⁆ L₂` is the
preimage under `f` of the kernel of the action of `L₂`. -/
theorem ker_compLieHom (f : L₁ →ₗ⁅R⁆ L₂) :
    letI := LieRingModule.compLieHom M f
    haveI := LieModule.compLieHom (R := R) M f
    LieModule.ker R L₁ M = (LieModule.ker R L₂ M).comap f := by
  let _ := LieRingModule.compLieHom M f
  have _ := LieModule.compLieHom (R := R) M f
  rw [LieModule.ker, toEnd_compLieHom, LieHom.ker_comp, LieModule.ker]

/-- A Lie module pulled back along `f : L₁ →ₗ⁅R⁆ L₂` is faithful exactly when the composite of `f`
with the representation of the original module is injective. -/
theorem isFaithful_compLieHom_iff (f : L₁ →ₗ⁅R⁆ L₂) :
    letI := LieRingModule.compLieHom M f
    haveI := LieModule.compLieHom (R := R) M f
    IsFaithful R L₁ M ↔ Function.Injective (toEnd R L₂ M ∘ f) := by
  let _ := LieRingModule.compLieHom M f
  have _ := LieModule.compLieHom (R := R) M f
  rw [isFaithful_iff, toEnd_compLieHom, LieHom.coe_comp]

end CompLieHom

/-! ### Representations and Lie modules -/

section Representation

variable {R : Type u} {L : Type v} {M : Type w₁}
variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

/-- **A representation is the representation of its Lie module.** Letting `L` act on `M` through
`ρ : L →ₗ⁅R⁆ Module.End R M`, the representation `LieModule.toEnd` of the resulting Lie module is
`ρ` itself. -/
theorem toEnd_compLieHom_moduleEnd (ρ : L →ₗ⁅R⁆ Module.End R M) :
    letI := LieRingModule.compLieHom M ρ
    haveI := LieModule.compLieHom (R := R) M ρ
    toEnd R L M = ρ := by
  rw [toEnd_compLieHom, toEnd_module_end, LieHom.id_comp]

/-- The kernel of the action of `L` on `M` through `ρ : L →ₗ⁅R⁆ Module.End R M` is the kernel of
`ρ`. -/
theorem ker_compLieHom_moduleEnd (ρ : L →ₗ⁅R⁆ Module.End R M) :
    letI := LieRingModule.compLieHom M ρ
    haveI := LieModule.compLieHom (R := R) M ρ
    LieModule.ker R L M = ρ.ker := by
  rw [LieModule.ker, toEnd_compLieHom_moduleEnd]

/-- **The faithfulness dictionary.** The action of `L` on `M` through
`ρ : L →ₗ⁅R⁆ Module.End R M` is faithful exactly when `ρ` is injective. -/
theorem isFaithful_compLieHom_moduleEnd_iff (ρ : L →ₗ⁅R⁆ Module.End R M) :
    letI := LieRingModule.compLieHom M ρ
    haveI := LieModule.compLieHom (R := R) M ρ
    IsFaithful R L M ↔ Function.Injective ρ := by
  rw [isFaithful_iff, toEnd_compLieHom_moduleEnd]

/-- The action of `L` on `M` through `ρ : L →ₗ⁅R⁆ Module.End R M` is faithful exactly when `ρ` has
trivial kernel. -/
theorem isFaithful_compLieHom_moduleEnd_iff_ker_eq_bot (ρ : L →ₗ⁅R⁆ Module.End R M) :
    letI := LieRingModule.compLieHom M ρ
    haveI := LieModule.compLieHom (R := R) M ρ
    IsFaithful R L M ↔ ρ.ker = ⊥ := by
  rw [isFaithful_compLieHom_moduleEnd_iff, LieHom.ker_eq_bot]

end Representation

end LieModule

namespace LieRingModule

variable (R : Type u) (L : Type v) (M : Type w₁)
variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
variable [LieRingModule L M] [LieModule R L M]

/-- **A Lie module is the module of its representation.** Pulling the tautological action of
`Module.End R M` on `M` back along the representation `LieModule.toEnd R L M` of a Lie module
recovers the given Lie module structure. Together with `LieModule.toEnd_compLieHom_moduleEnd`, this
says that the passages between representations and Lie modules are mutually inverse. -/
theorem compLieHom_toEnd :
    LieRingModule.compLieHom M (LieModule.toEnd R L M) = ‹LieRingModule L M› := by
  -- Both structures have the bracket `⁅x, m⁆`: the pulled-back bracket is `toEnd R L M x m`,
  -- which is `⁅x, m⁆` by the definition of `LieModule.toEnd` (`LieModule.toEnd_apply_apply` is
  -- proved by `rfl`); the remaining fields are propositions, so structure eta closes the goal.
  rfl

end LieRingModule
