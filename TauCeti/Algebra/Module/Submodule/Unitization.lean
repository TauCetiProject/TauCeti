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

Given a semiring `R` and a nonunital nonassociative semiring `A` with an `R`-module structure, any
`R`-submodule `L : Submodule R A` closed under left multiplication by `A` carries a left action of
the forced unitization `Unitization R A` given by `(r, a) • x = r • x + a * x`. When `R` is a
commutative semiring and `A` is an associative nonunital semiring with `[IsScalarTower R A A]` and
`[SMulCommClass R A A]`, this action defines a left `Unitization R A`-module structure on `L`
compatible with multiplication in `Unitization R A` via `Unitization.inr`, and elements of
`Module.annihilator (Unitization R A) L` are characterized by `∀ x ∈ L, u.fst • x + u.snd * x = 0`.

Both `Submodule.unitizationSMul` and `Submodule.unitizationModule` are provided as
`@[instance_reducible]` definitions taking the left-absorption hypothesis explicitly rather than as
global typeclass instances.

## Main definitions and results

* `Submodule.unitizationSMul`: the left scalar action `(r, a) • x = r • x + a * x` of
  `Unitization R A` on an `R`-submodule `L : Submodule R A` closed under left multiplication by `A`.
* `Submodule.inr_coe_unitizationSMul`: coercing `(r, a) • x` into `Unitization R A` agrees with
  multiplication in `Unitization R A`.
* `Submodule.unitizationModule`: the left `Unitization R A`-module structure on `L`.
* `Submodule.mem_annihilator_unitization_iff`: membership characterization for
  `Module.annihilator (Unitization R A) L`.
-/

public section

namespace Submodule

section NonAssocSemiring

variable {R A : Type*} [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]

/-- Left scalar action `(r, a) • x = r • x + a * x` of `Unitization R A` on an `R`-submodule
`L : Submodule R A` closed under left multiplication by `A`. Provided as a definition taking the
left-absorption hypothesis rather than a global instance. -/
@[instance_reducible]
def unitizationSMul (L : Submodule R A) (hmul : ∀ a : A, ∀ x ∈ L, a * x ∈ L) :
    SMul (Unitization R A) L where
  smul u x := ⟨u.fst • (x : A) + u.snd * (x : A),
    L.add_mem (L.smul_mem u.fst x.2) (hmul u.snd x x.2)⟩

theorem coe_unitizationSMul (L : Submodule R A) (hmul : ∀ a : A, ∀ x ∈ L, a * x ∈ L)
    (u : Unitization R A) (x : L) :
    (letI := L.unitizationSMul hmul; ((u • x : L) : A)) = u.fst • (x : A) + u.snd * (x : A) :=
  (rfl)

/-- Coercing `(r, a) • x` from `L` into `Unitization R A` agrees with multiplication in
`Unitization R A`. -/
theorem inr_coe_unitizationSMul (L : Submodule R A) (hmul : ∀ a : A, ∀ x ∈ L, a * x ∈ L)
    (u : Unitization R A) (x : L) :
    (letI := L.unitizationSMul hmul; (((u • x : L) : A) : Unitization R A)) =
      u * ((x : A) : Unitization R A) := by
  let _ := L.unitizationSMul hmul
  ext
  · simp
  · simp [coe_unitizationSMul]

end NonAssocSemiring

section Semiring

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]

/-- Left `Unitization R A`-module structure on an `R`-submodule `L : Submodule R A` closed under
left multiplication by `A`, induced by multiplication in `Unitization R A`. -/
@[instance_reducible]
def unitizationModule (L : Submodule R A) (hmul : ∀ a : A, ∀ x ∈ L, a * x ∈ L) :
    Module (Unitization R A) L :=
  letI := L.unitizationSMul hmul
  Function.Injective.module (Unitization R A)
    ((Unitization.inrHom R R A).toAddMonoidHom.comp L.subtype.toAddMonoidHom)
    (Unitization.inr_injective.comp Subtype.coe_injective)
    (L.inr_coe_unitizationSMul hmul)

/-- Membership in `Module.annihilator (Unitization R A) L` for the unitization left action. -/
theorem mem_annihilator_unitization_iff (L : Submodule R A) (hmul : ∀ a : A, ∀ x ∈ L, a * x ∈ L)
    {u : Unitization R A} :
    (letI := L.unitizationModule hmul; u ∈ Module.annihilator (Unitization R A) L) ↔
      ∀ x ∈ L, u.fst • x + u.snd * x = 0 := by
  let _ := L.unitizationModule hmul
  rw [Module.mem_annihilator]
  refine ⟨fun h x hx => congrArg Subtype.val (h ⟨x, hx⟩), fun h x => Subtype.ext (h x x.2)⟩

end Semiring

end Submodule
