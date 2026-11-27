/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Torsion.Basic
public import TauCeti.Algebra.Module.Torsion.Map

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
  (TauCeti.torsionByMap (n : ℤ) f.toIntLinearMap).toAddMonoidHom.toZModLinearMap n

/-- Evaluating `f.torsionByZModLinearMap n` and coercing to `B` agrees with `f`. -/
@[simp]
theorem coe_torsionByZModLinearMap_apply (f : A →+ B) (n : ℕ)
    [Module (ZMod n) (AddSubgroup.torsionBy A (n : ℤ))]
    [Module (ZMod n) (AddSubgroup.torsionBy B (n : ℤ))]
    (x : AddSubgroup.torsionBy A (n : ℤ)) :
    (f.torsionByZModLinearMap n x : B) = f x := by
  rw [torsionByZModLinearMap, AddMonoidHom.coe_toZModLinearMap, LinearMap.toAddMonoidHom_coe,
    TauCeti.coe_torsionByMap_apply, AddMonoidHom.coe_toIntLinearMap]

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
    Function.Injective (f.torsionByZModLinearMap n) :=
  TauCeti.injective_torsionByMap (f := f.toIntLinearMap) hf

end AddMonoidHom

namespace AddEquiv

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- Restrict an additive equivalence `e : A ≃+ B` to a `ZMod n`-linear equivalence
`AddSubgroup.torsionBy A (n : ℤ) ≃ₗ[ZMod n] AddSubgroup.torsionBy B (n : ℤ)`. -/
def torsionByZModLinearEquiv (e : A ≃+ B) (n : ℕ)
    [Module (ZMod n) (AddSubgroup.torsionBy A (n : ℤ))]
    [Module (ZMod n) (AddSubgroup.torsionBy B (n : ℤ))] :
    AddSubgroup.torsionBy A (n : ℤ) ≃ₗ[ZMod n] AddSubgroup.torsionBy B (n : ℤ) :=
  { e.torsionByCongr (n : ℤ) with
    map_smul' := ZMod.map_smul (e.torsionByCongr (n : ℤ)).toAddMonoidHom }

/-- The underlying `ZMod n`-linear map of `e.torsionByZModLinearEquiv n` is
`e.toAddMonoidHom.torsionByZModLinearMap n`. -/
@[simp]
theorem toLinearMap_torsionByZModLinearEquiv (e : A ≃+ B) (n : ℕ)
    [Module (ZMod n) (AddSubgroup.torsionBy A (n : ℤ))]
    [Module (ZMod n) (AddSubgroup.torsionBy B (n : ℤ))] :
    (e.torsionByZModLinearEquiv n).toLinearMap = e.toAddMonoidHom.torsionByZModLinearMap n := by
  ext x
  rw [LinearEquiv.coe_toLinearMap, AddMonoidHom.coe_torsionByZModLinearMap_apply,
    AddEquiv.coe_toAddMonoidHom]
  exact AddEquiv.torsionByCongr_apply_coe e (n : ℤ) x

/-- Applying `e.torsionByZModLinearEquiv n` agrees with `e.toAddMonoidHom.torsionByZModLinearMap n`.
-/
@[simp]
theorem torsionByZModLinearEquiv_apply (e : A ≃+ B) (n : ℕ)
    [Module (ZMod n) (AddSubgroup.torsionBy A (n : ℤ))]
    [Module (ZMod n) (AddSubgroup.torsionBy B (n : ℤ))]
    (x : AddSubgroup.torsionBy A (n : ℤ)) :
    e.torsionByZModLinearEquiv n x = e.toAddMonoidHom.torsionByZModLinearMap n x :=
  LinearMap.congr_fun (e.toLinearMap_torsionByZModLinearEquiv n) x

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
  rw [coe_torsionByZModLinearEquiv_apply]
  exact AddEquiv.torsionByCongr_symm_apply_coe e (n : ℤ) x

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
