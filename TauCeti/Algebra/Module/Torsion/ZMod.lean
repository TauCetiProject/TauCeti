/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# `ZMod n`-linear restriction of additive homomorphisms to `n`-torsion

Any additive homomorphism `f : A →+ B` between additive commutative groups carries the `n`-torsion
subgroup `A[n] = AddSubgroup.torsionBy A (n : ℤ)` into `B[n] = AddSubgroup.torsionBy B (n : ℤ)`.
When both torsion subgroups are equipped with `ZMod n`-module structures (for instance
`AddSubgroup.torsionBy.zmodModule`), this restriction upgrades via `AddMonoidHom.toZModLinearMap`
to a `ZMod n`-linear map `f.torsionByZModLinearMap n : A[n] →ₗ[ZMod n] B[n]`.

## Main definitions

* `AddMonoidHom.torsionByZModLinearMap`: the `ZMod n`-linear restriction of `f : A →+ B` to
  `AddSubgroup.torsionBy A (n : ℤ) →ₗ[ZMod n] AddSubgroup.torsionBy B (n : ℤ)`.

## Main results

* `AddMonoidHom.coe_torsionByZModLinearMap_apply`: the coercion of `f.torsionByZModLinearMap n x`
  to `B` is `f x`.
* `AddMonoidHom.torsionByZModLinearMap_id`, `AddMonoidHom.torsionByZModLinearMap_comp`:
  functoriality of `torsionByZModLinearMap`.
* `AddMonoidHom.torsionByZModLinearMap_zero`, `AddMonoidHom.torsionByZModLinearMap_add`,
  `AddMonoidHom.torsionByZModLinearMap_neg`: additivity of `torsionByZModLinearMap`.
* `AddMonoidHom.injective_torsionByZModLinearMap`: injectivity is preserved on `n`-torsion.
* `LinearMap.toAddMonoidHom_torsionByZModLinearMap_id`,
  `LinearMap.toAddMonoidHom_torsionByZModLinearMap_comp`: restriction laws for `ℤ`-linear maps.
* `AddEquiv.torsionByZModLinearEquiv`: the `ZMod n`-linear equivalence induced by `e : A ≃+ B`
  on `n`-torsion subgroups.
-/

public section

namespace AddMonoidHom

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- Restrict an additive homomorphism `f : A →+ B` to a `ZMod n`-linear map
`AddSubgroup.torsionBy A (n : ℤ) →ₗ[ZMod n] AddSubgroup.torsionBy B (n : ℤ)`. -/
def torsionByZModLinearMap (f : A →+ B) (n : ℕ)
    [Module (ZMod n) (AddSubgroup.torsionBy A (n : ℤ))]
    [Module (ZMod n) (AddSubgroup.torsionBy B (n : ℤ))] :
    AddSubgroup.torsionBy A (n : ℤ) →ₗ[ZMod n] AddSubgroup.torsionBy B (n : ℤ) :=
  AddMonoidHom.toZModLinearMap n
    (M := AddSubgroup.torsionBy A (n : ℤ))
    (M₁ := AddSubgroup.torsionBy B (n : ℤ))
    ((f.domRestrict (AddSubgroup.torsionBy A (n : ℤ))).codRestrict
      (AddSubgroup.torsionBy B (n : ℤ)) fun x ↦ by
        rw [AddSubgroup.torsionBy.nsmul_iff, AddMonoidHom.domRestrict_apply, ← map_nsmul,
          AddSubgroup.torsionBy.nsmul_iff.mp x.property, map_zero])

/-- Evaluating `f.torsionByZModLinearMap n` and coercing to `B` agrees with `f`. -/
@[simp]
theorem coe_torsionByZModLinearMap_apply (f : A →+ B) (n : ℕ)
    [Module (ZMod n) (AddSubgroup.torsionBy A (n : ℤ))]
    [Module (ZMod n) (AddSubgroup.torsionBy B (n : ℤ))]
    (x : AddSubgroup.torsionBy A (n : ℤ)) :
    (f.torsionByZModLinearMap n x : B) = f x := by
  rw [torsionByZModLinearMap, AddMonoidHom.coe_toZModLinearMap,
    AddMonoidHom.codRestrict_apply, AddSubgroup.coe_mk, AddMonoidHom.domRestrict_apply]

/-- The identity additive homomorphism restricts to the identity `ZMod n`-linear map on
`n`-torsion. -/
@[simp]
theorem torsionByZModLinearMap_id (n : ℕ)
    [Module (ZMod n) (AddSubgroup.torsionBy A (n : ℤ))] :
    (AddMonoidHom.id A).torsionByZModLinearMap n = LinearMap.id := by
  ext x
  rw [coe_torsionByZModLinearMap_apply, AddMonoidHom.id_apply, LinearMap.id_apply]

/-- Restriction to `n`-torsion commutes with composition of additive homomorphisms. -/
@[simp]
theorem torsionByZModLinearMap_comp (g : B →+ C) (f : A →+ B) (n : ℕ)
    [Module (ZMod n) (AddSubgroup.torsionBy A (n : ℤ))]
    [Module (ZMod n) (AddSubgroup.torsionBy B (n : ℤ))]
    [Module (ZMod n) (AddSubgroup.torsionBy C (n : ℤ))] :
    (g.comp f).torsionByZModLinearMap n =
      g.torsionByZModLinearMap n ∘ₗ f.torsionByZModLinearMap n := by
  ext x
  rw [coe_torsionByZModLinearMap_apply, AddMonoidHom.comp_apply, LinearMap.comp_apply,
    coe_torsionByZModLinearMap_apply, coe_torsionByZModLinearMap_apply]

/-- The zero additive homomorphism restricts to the zero `ZMod n`-linear map on `n`-torsion. -/
@[simp]
theorem torsionByZModLinearMap_zero (n : ℕ)
    [Module (ZMod n) (AddSubgroup.torsionBy A (n : ℤ))]
    [Module (ZMod n) (AddSubgroup.torsionBy B (n : ℤ))] :
    (0 : A →+ B).torsionByZModLinearMap n = 0 := by
  ext x
  rw [coe_torsionByZModLinearMap_apply, AddMonoidHom.zero_apply, LinearMap.zero_apply,
    AddSubgroup.coe_zero]

/-- Restriction to `n`-torsion preserves addition of additive homomorphisms. -/
@[simp]
theorem torsionByZModLinearMap_add (f g : A →+ B) (n : ℕ)
    [Module (ZMod n) (AddSubgroup.torsionBy A (n : ℤ))]
    [Module (ZMod n) (AddSubgroup.torsionBy B (n : ℤ))] :
    (f + g).torsionByZModLinearMap n =
      f.torsionByZModLinearMap n + g.torsionByZModLinearMap n := by
  ext x
  rw [coe_torsionByZModLinearMap_apply, AddMonoidHom.add_apply, LinearMap.add_apply,
    AddSubgroup.coe_add, coe_torsionByZModLinearMap_apply, coe_torsionByZModLinearMap_apply]

/-- Restriction to `n`-torsion preserves negation of additive homomorphisms. -/
@[simp]
theorem torsionByZModLinearMap_neg (f : A →+ B) (n : ℕ)
    [Module (ZMod n) (AddSubgroup.torsionBy A (n : ℤ))]
    [Module (ZMod n) (AddSubgroup.torsionBy B (n : ℤ))] :
    (-f).torsionByZModLinearMap n = -(f.torsionByZModLinearMap n) := by
  ext x
  rw [coe_torsionByZModLinearMap_apply, AddMonoidHom.neg_apply, LinearMap.neg_apply,
    AddSubgroup.coe_neg, coe_torsionByZModLinearMap_apply]

/-- If `f : A →+ B` is injective, then its `ZMod n`-linear restriction to `n`-torsion is
injective. -/
theorem injective_torsionByZModLinearMap {f : A →+ B} (hf : Function.Injective f) (n : ℕ)
    [Module (ZMod n) (AddSubgroup.torsionBy A (n : ℤ))]
    [Module (ZMod n) (AddSubgroup.torsionBy B (n : ℤ))] :
    Function.Injective (f.torsionByZModLinearMap n) := fun _ _ h ↦
  Subtype.ext <| hf <| by
    simpa only [coe_torsionByZModLinearMap_apply] using congrArg Subtype.val h

end AddMonoidHom

namespace LinearMap

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- The identity `ℤ`-linear map restricts to the identity `ZMod n`-linear map on `n`-torsion. -/
@[simp]
theorem toAddMonoidHom_torsionByZModLinearMap_id (n : ℕ)
    [Module (ZMod n) (AddSubgroup.torsionBy A (n : ℤ))] :
    (LinearMap.id (R := ℤ) (M := A)).toAddMonoidHom.torsionByZModLinearMap n = LinearMap.id := by
  ext x
  rw [AddMonoidHom.coe_torsionByZModLinearMap_apply, LinearMap.toAddMonoidHom_coe,
    LinearMap.id_apply, LinearMap.id_apply]

/-- Restriction of `ℤ`-linear maps to `n`-torsion commutes with composition. -/
@[simp]
theorem toAddMonoidHom_torsionByZModLinearMap_comp (g : B →ₗ[ℤ] C) (f : A →ₗ[ℤ] B) (n : ℕ)
    [Module (ZMod n) (AddSubgroup.torsionBy A (n : ℤ))]
    [Module (ZMod n) (AddSubgroup.torsionBy B (n : ℤ))]
    [Module (ZMod n) (AddSubgroup.torsionBy C (n : ℤ))] :
    (g.comp f).toAddMonoidHom.torsionByZModLinearMap n =
      g.toAddMonoidHom.torsionByZModLinearMap n ∘ₗ f.toAddMonoidHom.torsionByZModLinearMap n := by
  ext x
  rw [AddMonoidHom.coe_torsionByZModLinearMap_apply, LinearMap.toAddMonoidHom_coe,
    LinearMap.comp_apply, LinearMap.comp_apply, AddMonoidHom.coe_torsionByZModLinearMap_apply,
    AddMonoidHom.coe_torsionByZModLinearMap_apply, LinearMap.toAddMonoidHom_coe,
    LinearMap.toAddMonoidHom_coe]

end LinearMap

namespace AddEquiv

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- Restrict an additive equivalence `e : A ≃+ B` to a `ZMod n`-linear equivalence
`AddSubgroup.torsionBy A (n : ℤ) ≃ₗ[ZMod n] AddSubgroup.torsionBy B (n : ℤ)`. -/
def torsionByZModLinearEquiv (e : A ≃+ B) (n : ℕ)
    [Module (ZMod n) (AddSubgroup.torsionBy A (n : ℤ))]
    [Module (ZMod n) (AddSubgroup.torsionBy B (n : ℤ))] :
    AddSubgroup.torsionBy A (n : ℤ) ≃ₗ[ZMod n] AddSubgroup.torsionBy B (n : ℤ) :=
  LinearEquiv.ofLinearMap
    (e.toAddMonoidHom.torsionByZModLinearMap n)
    (e.symm.toAddMonoidHom.torsionByZModLinearMap n)
    (by
      rw [← AddMonoidHom.torsionByZModLinearMap_comp]
      ext x
      simp)
    (by
      rw [← AddMonoidHom.torsionByZModLinearMap_comp]
      ext x
      simp)

/-- The underlying `ZMod n`-linear map of `e.torsionByZModLinearEquiv n` is
`e.toAddMonoidHom.torsionByZModLinearMap n`. -/
@[simp]
theorem toLinearMap_torsionByZModLinearEquiv (e : A ≃+ B) (n : ℕ)
    [Module (ZMod n) (AddSubgroup.torsionBy A (n : ℤ))]
    [Module (ZMod n) (AddSubgroup.torsionBy B (n : ℤ))] :
    (e.torsionByZModLinearEquiv n).toLinearMap = e.toAddMonoidHom.torsionByZModLinearMap n := by
  ext x
  simp [torsionByZModLinearEquiv]

/-- Applying `e.torsionByZModLinearEquiv n` agrees with `e.toAddMonoidHom.torsionByZModLinearMap n`.
-/
@[simp]
theorem torsionByZModLinearEquiv_apply (e : A ≃+ B) (n : ℕ)
    [Module (ZMod n) (AddSubgroup.torsionBy A (n : ℤ))]
    [Module (ZMod n) (AddSubgroup.torsionBy B (n : ℤ))]
    (x : AddSubgroup.torsionBy A (n : ℤ)) :
    e.torsionByZModLinearEquiv n x = e.toAddMonoidHom.torsionByZModLinearMap n x := by
  simp [torsionByZModLinearEquiv]

/-- Evaluating `e.torsionByZModLinearEquiv n` and coercing to `B` agrees with `e`. -/
theorem coe_torsionByZModLinearEquiv_apply (e : A ≃+ B) (n : ℕ)
    [Module (ZMod n) (AddSubgroup.torsionBy A (n : ℤ))]
    [Module (ZMod n) (AddSubgroup.torsionBy B (n : ℤ))]
    (x : AddSubgroup.torsionBy A (n : ℤ)) :
    (e.torsionByZModLinearEquiv n x : B) = e x := by
  rw [torsionByZModLinearEquiv_apply, AddMonoidHom.coe_torsionByZModLinearMap_apply,
    AddEquiv.coe_toAddMonoidHom]

/-- The inverse of `e.torsionByZModLinearEquiv n` is `e.symm.torsionByZModLinearEquiv n`. -/
@[simp]
theorem torsionByZModLinearEquiv_symm (e : A ≃+ B) (n : ℕ)
    [Module (ZMod n) (AddSubgroup.torsionBy A (n : ℤ))]
    [Module (ZMod n) (AddSubgroup.torsionBy B (n : ℤ))] :
    (e.torsionByZModLinearEquiv n).symm = e.symm.torsionByZModLinearEquiv n := by
  ext x
  simp [torsionByZModLinearEquiv]

/-- The identity additive equivalence restricts to the identity `ZMod n`-linear equivalence on
`n`-torsion. -/
@[simp]
theorem torsionByZModLinearEquiv_refl (n : ℕ)
    [Module (ZMod n) (AddSubgroup.torsionBy A (n : ℤ))] :
    (AddEquiv.refl A).torsionByZModLinearEquiv n = LinearEquiv.refl (ZMod n) _ := by
  ext x
  simp

/-- Restriction of additive equivalences to `n`-torsion respects composition. -/
@[simp]
theorem torsionByZModLinearEquiv_trans (e₁ : A ≃+ B) (e₂ : B ≃+ C) (n : ℕ)
    [Module (ZMod n) (AddSubgroup.torsionBy A (n : ℤ))]
    [Module (ZMod n) (AddSubgroup.torsionBy B (n : ℤ))]
    [Module (ZMod n) (AddSubgroup.torsionBy C (n : ℤ))] :
    (e₁.trans e₂).torsionByZModLinearEquiv n =
      (e₁.torsionByZModLinearEquiv n).trans (e₂.torsionByZModLinearEquiv n) := by
  ext x
  simp

end AddEquiv
