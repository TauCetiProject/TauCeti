/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Cochain
public import Mathlib.Algebra.Lie.Derivation.Basic
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# Lie derivations as 1-cocycles

A Lie derivation `D : L → M` into an `L`-module `M` is a 1-cocycle of `L` with values in `M`, and
it shears the action of `L` on `M × R` to `⁅x, (m, t)⁆ = (⁅x, m⁆ + t • D x, 0)`, an extension of
the trivial module `R` by `M`. This file supplies:

* `LieDerivation.d₁₂_eq_zero`: a Lie derivation is a 1-cocycle, `d₁₂ D = 0`;
* `LieDerivation.ofD₁₂EqZero`: conversely, a 1-cochain `f` with `d₁₂ f = 0` as a Lie derivation;
* `LieDerivation.ShearedModule D`: the module `M × R` sheared by a Lie derivation `D`, with its
  identification `LieDerivation.ShearedModule.ofProd` with `M × R`.

These let structure theorems about Lie modules, such as Weyl's theorem, be applied to the sheared
module, for instance to show that a Lie derivation is inner.

## Implementation notes

`LieDerivation.ShearedModule D` is a type synonym for `M × R`, so that the action sheared by `D` is
a global instance on its own carrier rather than a local structure on `M × R`. As with Mathlib's
`LieAlgebra.ofProd`, all access goes through the linear equivalence
`LieDerivation.ShearedModule.ofProd`, which is the identity, and
`LieDerivation.ShearedModule.ofProd_symm_lie` restates the bracket field of the instance, so it is
proved by `rfl`.
-/

public section

open LieModule.Cohomology

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M]

namespace LieDerivation

/-- A Lie derivation is a 1-cocycle. -/
@[simp]
lemma d₁₂_eq_zero (D : LieDerivation R L M) : d₁₂ R L M (D : L →ₗ[R] M) = 0 := by
  ext x y
  simp [D.apply_lie_eq_sub]

/-- A 1-cochain `f` with `d₁₂ f = 0` satisfies the Leibniz rule, so it is a Lie derivation. -/
def ofD₁₂EqZero (f : oneCochain R L M) (hf : d₁₂ R L M f = 0) : LieDerivation R L M where
  toLinearMap := f
  leibniz' x y := by
    have h : d₁₂ R L M f x y = 0 := by simp [hf, ← twoCochain_val_apply]
    rw [d₁₂_apply_apply, sub_eq_zero] at h
    exact h.symm

@[simp]
lemma coe_ofD₁₂EqZero (f : oneCochain R L M) (hf : d₁₂ R L M f = 0) :
    ⇑(ofD₁₂EqZero f hf) = f := (rfl)

/-- The module `M × R` with the action of `L` sheared by a Lie derivation `D`:
`⁅x, (m, t)⁆ = (⁅x, m⁆ + t • D x, 0)`. Use `LieDerivation.ShearedModule.ofProd` to pass between it
and `M × R`. -/
@[expose] def ShearedModule (_D : LieDerivation R L M) : Type _ := M × R

namespace ShearedModule

variable (D : LieDerivation R L M)

instance : AddCommGroup D.ShearedModule := inferInstanceAs (AddCommGroup (M × R))

instance : Module R D.ShearedModule := inferInstanceAs (Module R (M × R))

/-- The identification of `M × R` with the module sheared by `D`, as a linear equivalence. -/
def ofProd : (M × R) ≃ₗ[R] D.ShearedModule := LinearEquiv.refl R (M × R)

instance [Module.Finite R M] : Module.Finite R D.ShearedModule :=
  Module.Finite.equiv (ofProd D)

instance : LieRingModule L D.ShearedModule where
  bracket x v := ofProd D (⁅x, ((ofProd D).symm v).1⁆ + ((ofProd D).symm v).2 • D x, 0)
  add_lie x y v := by
    apply (ofProd D).symm.injective
    simp only [LinearEquiv.symm_apply_apply, map_add, add_lie, smul_add, Prod.mk_add_mk, add_zero]
    abel_nf
  lie_add x v w := by
    apply (ofProd D).symm.injective
    simp only [LinearEquiv.symm_apply_apply, map_add, Prod.fst_add, Prod.snd_add, lie_add,
      add_smul, Prod.mk_add_mk, add_zero]
    abel_nf
  leibniz_lie x y v := by
    apply (ofProd D).symm.injective
    simp only [LinearEquiv.symm_apply_apply, map_add, lie_add, lie_smul, D.apply_lie_eq_sub,
      zero_smul, add_zero, Prod.mk_add_mk, smul_sub, leibniz_lie x y ((ofProd D).symm v).1]
    abel_nf

@[simp]
lemma ofProd_symm_lie (x : L) (v : D.ShearedModule) :
    (ofProd D).symm ⁅x, v⁆ = (⁅x, ((ofProd D).symm v).1⁆ + ((ofProd D).symm v).2 • D x, 0) :=
  (rfl)

instance : LieModule R L D.ShearedModule where
  smul_lie t x v := (ofProd D).symm.injective <| by simp [smul_add, smul_comm t]
  lie_smul t x v := (ofProd D).symm.injective <| by simp [smul_add, smul_smul, mul_comm t]

end ShearedModule

end LieDerivation
