/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Left `Unitization` module actions on submodules

Given a commutative semiring `R` and a nonunital associative semiring `A` with an `R`-module
structure satisfying `[IsScalarTower R A A]` and `[SMulCommClass R A A]`, any `R`-submodule
`L : Submodule R A` closed under left multiplication by `A` carries a left `Unitization R A`-module
structure given by `(r, a) • x = r • x + a * x`. This action is compatible with multiplication in
`Unitization R A` via `Unitization.inr` and with the `R`-module structure on `L`
(`IsScalarTower R (Unitization R A) L`), and elements of `Module.annihilator (Unitization R A) L`
are characterized by `∀ x ∈ L, u.fst • x + u.snd * x = 0`.

`Submodule.unitizationModule` is provided as an `@[instance_reducible]` definition taking the
left-absorption hypothesis explicitly rather than as a global typeclass instance.

## Main definitions and results

* `Submodule.unitizationModule`: the left `Unitization R A`-module structure
  `(r, a) • x = r • x + a * x` on an `R`-submodule `L : Submodule R A` closed under left
  multiplication by `A`.
* `Submodule.coe_unitizationModule_smul` and `Submodule.inr_coe_unitizationModule_smul`: coercion
  formulas for `(r, a) • x` into `A` and into `Unitization R A`.
* `Submodule.isScalarTower_unitizationModule`: scalar compatibility
  `IsScalarTower R (Unitization R A) L`.
* `Submodule.mem_annihilator_unitization_iff`: membership characterization for
  `Module.annihilator (Unitization R A) L`.
-/

public section

namespace Submodule

section Semiring

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]

/-- Left scalar action `(r, a) • x = r • x + a * x` of `Unitization R A` on an `R`-submodule
`L : Submodule R A` closed under left multiplication by `A`. -/
@[instance_reducible]
private def unitizationSMul (L : Submodule R A) (hmul : ∀ a : A, ∀ x ∈ L, a * x ∈ L) :
    SMul (Unitization R A) L where
  smul u x := ⟨u.fst • (x : A) + u.snd * (x : A),
    L.add_mem (L.smul_mem u.fst x.property) (hmul u.snd x x.property)⟩

/-- Left `Unitization R A`-module structure `(r, a) • x = r • x + a * x` on an `R`-submodule
`L : Submodule R A` closed under left multiplication by `A`. Provided as an `@[instance_reducible]`
definition taking the left-absorption hypothesis explicitly rather than a global instance. -/
@[instance_reducible]
def unitizationModule (L : Submodule R A) (hmul : ∀ a : A, ∀ x ∈ L, a * x ∈ L) :
    Module (Unitization R A) L :=
  letI := L.unitizationSMul hmul
  Function.Injective.module (Unitization R A)
    ((Unitization.inrHom R R A).toAddMonoidHom.comp L.subtype.toAddMonoidHom)
    (Unitization.inr_injective.comp Subtype.coe_injective)
    (fun u x => by
      ext
      · simp
      · simp; rfl)

@[simp]
theorem coe_unitizationModule_smul (L : Submodule R A) (hmul : ∀ a : A, ∀ x ∈ L, a * x ∈ L)
    (u : Unitization R A) (x : L) :
    (letI := L.unitizationModule hmul; ((u • x : L) : A)) = u.fst • (x : A) + u.snd * (x : A) :=
  (rfl)

/-- Coercing `(r, a) • x` from `L` into `Unitization R A` agrees with multiplication in
`Unitization R A`. -/
theorem inr_coe_unitizationModule_smul (L : Submodule R A) (hmul : ∀ a : A, ∀ x ∈ L, a * x ∈ L)
    (u : Unitization R A) (x : L) :
    (letI := L.unitizationModule hmul; (((u • x : L) : A) : Unitization R A)) =
      u * ((x : A) : Unitization R A) := by
  let _ := L.unitizationModule hmul
  ext
  · simp
  · simp

/-- The left `Unitization R A`-module structure on `L` is compatible with its `R`-module
structure. -/
theorem isScalarTower_unitizationModule (L : Submodule R A) (hmul : ∀ a : A, ∀ x ∈ L, a * x ∈ L) :
    letI := L.unitizationModule hmul
    IsScalarTower R (Unitization R A) L := by
  let _ := L.unitizationModule hmul
  exact ⟨fun r u x => Subtype.ext <| by simp [smul_add, mul_smul, smul_mul_assoc]⟩

/-- Membership in `Module.annihilator (Unitization R A) L` for the unitization left action. -/
theorem mem_annihilator_unitization_iff (L : Submodule R A) (hmul : ∀ a : A, ∀ x ∈ L, a * x ∈ L)
    {u : Unitization R A} :
    (letI := L.unitizationModule hmul; u ∈ Module.annihilator (Unitization R A) L) ↔
      ∀ x ∈ L, u.fst • x + u.snd * x = 0 := by
  let _ := L.unitizationModule hmul
  rw [Module.mem_annihilator]
  refine ⟨fun h x hx => congrArg Subtype.val (h ⟨x, hx⟩), fun h x => Subtype.ext (h x x.property)⟩

end Semiring

end Submodule
