/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Semilinear maps and scalars acting through a ring homomorphism

Let `σ : R →+* S` be a ring homomorphism. A map semilinear along `σ` kills `ker σ • P`
(`LinearMap.map_eq_zero_of_mem_ker_smul_top`). When `R` acts on `S`-modules through `σ`, a
`σ`-semilinear map into such a module is `R`-linear (`LinearMap.toLinearMapOfCompHom`), and an
`S`-linear map between such modules restricts to an `R`-linear map through Mathlib's
`LinearMap.restrictScalars` (`LinearMap.CompatibleSMul.of_compHom`). In these results the action
of `R` is given by hypotheses `a • m = σ a • m` rather than by `Module.compHom`, so they also apply
to modules whose `R`-module structure is already present.

Finally, when `R` acts on an `S`-module `M` through a representation `ρ : R →+* End_S(M)`, that is
under the module structure `Module.compHom M ρ`, the element `a ∈ R` acts as the `S`-linear map
`ρ a` (`DistribSMul.toLinearMap_compHom`).

## Main definitions

* `LinearMap.toLinearMapOfCompHom`: a `σ`-semilinear map into a module on which `R` acts through
  `σ`, as an `R`-linear map.

## Main results

* `LinearMap.map_eq_zero_of_mem_ker_smul_top`: a map semilinear along `σ` kills `ker σ • P`.
* `LinearMap.CompatibleSMul.of_compHom`: `S`-linear maps between modules on which `R` acts through
  `σ` commute with the action of `R`.
* `DistribSMul.toLinearMap_compHom`: under the module structure `Module.compHom M ρ` given by a
  representation `ρ : R →+* End_S(M)`, whose action commutes with that of `S`
  (`SMul.comp.smulCommClass`), `a ∈ R` acts as `ρ a`.
-/

public section

namespace LinearMap

variable {R S : Type*} [Semiring R] [Semiring S] {σ : R →+* S}
  {P : Type*} [AddCommMonoid P] [Module R P]
  {M N : Type*} [AddCommMonoid M] [Module S M] [AddCommMonoid N] [Module S N]

/-- A map semilinear along `σ` kills `ker σ • P`. -/
theorem map_eq_zero_of_mem_ker_smul_top (h : P →ₛₗ[σ] M) {x : P}
    (hx : x ∈ RingHom.ker σ • (⊤ : Submodule R P)) : h x = 0 :=
  Submodule.smul_induction_on hx (fun r hr n _ ↦ by rw [h.map_smulₛₗ, hr, zero_smul])
    fun x y hx hy ↦ by rw [map_add, hx, hy, add_zero]

variable [Module R M] [Module R N]

/-- A map semilinear along `σ` into a module on which `R` acts through `σ`, as an `R`-linear
map. -/
def toLinearMapOfCompHom (g : P →ₛₗ[σ] M) (hM : ∀ (a : R) (m : M), a • m = σ a • m) :
    P →ₗ[R] M where
  toFun := g
  map_add' := g.map_add
  map_smul' a x := by rw [g.map_smulₛₗ, hM, RingHom.id_apply]

@[simp]
theorem coe_toLinearMapOfCompHom (g : P →ₛₗ[σ] M) (hM : ∀ (a : R) (m : M), a • m = σ a • m) :
    ⇑(g.toLinearMapOfCompHom hM) = g :=
  (rfl)

/-- An `S`-linear map between modules on which `R` acts through `σ` commutes with the action of
`R`, so it restricts to an `R`-linear map (`LinearMap.restrictScalars`). -/
theorem CompatibleSMul.of_compHom (hM : ∀ (a : R) (m : M), a • m = σ a • m)
    (hN : ∀ (a : R) (n : N), a • n = σ a • n) : CompatibleSMul M N R S :=
  ⟨fun g a m ↦ by rw [hM, hN, g.map_smul]⟩

end LinearMap

namespace DistribSMul

variable {R S M : Type*} [Semiring R] [Semiring S] [AddCommMonoid M] [Module S M]

/-- Under the `R`-module structure `Module.compHom M ρ` given by a representation
`ρ : R →+* End_S(M)`, `a ∈ R` acts on `M` as `ρ a`. -/
theorem toLinearMap_compHom (ρ : R →+* Module.End S M) (a : R) :
    letI := Module.compHom M ρ
    haveI := SMul.comp.smulCommClass (α := M) (β := S) ρ
    DistribSMul.toLinearMap S M a = ρ a :=
  -- `Module.compHom` defines `a • m` as `ρ a m`.
  rfl

end DistribSMul
