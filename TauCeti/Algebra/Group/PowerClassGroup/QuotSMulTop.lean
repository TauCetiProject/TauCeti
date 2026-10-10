/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.QuotSMulTop
public import TauCeti.Algebra.Group.PowerClassGroup.Basic

/-!
# Power classes as reduction modulo `n`

For a commutative group `G`, written additively, the integer multiples `n • G` are the additive
form of the `n`th powers `Gⁿ`. Hence the reduction `QuotSMulTop n (Additive G)` of `G` modulo `n`
is the group `G ⧸ Gⁿ` of `n`th power classes, written additively.

## Main results

* `TauCeti.zsmulTop_toAddSubgroup_eq_powerSubgroup`: `n • G` is the additive form of `Gⁿ`.
* `TauCeti.quotSMulTopPowerClassEquiv`: the additive equivalence between reduction modulo `n` and
  the group of `n`th power classes.
-/

public section

open scoped Pointwise

namespace TauCeti

/-- In the additive group of a commutative group, the subgroup of integer multiples by `n` is the
additive form of the subgroup of `n`th powers. -/
theorem zsmulTop_toAddSubgroup_eq_powerSubgroup {G : Type*} [CommGroup G] (n : ℕ) :
    ((n : ℤ) • (⊤ : Submodule ℤ (Additive G))).toAddSubgroup =
      (powerSubgroup G n).toAddSubgroup := by
  ext x
  simp only [Submodule.mem_toAddSubgroup, Submodule.mem_smul_pointwise_iff_exists,
    Submodule.mem_top, true_and, Additive.mem_toAddSubgroup, mem_powerSubgroup_iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.toMul, by simp [natCast_zsmul]⟩
  · rintro ⟨y, hy⟩
    exact ⟨Additive.ofMul y, by simpa [natCast_zsmul] using congrArg Additive.ofMul hy⟩

/-- Reduction modulo `n` of a commutative group, written additively, is its group of `n`th power
classes. -/
noncomputable def quotSMulTopPowerClassEquiv {G : Type*} [CommGroup G] (n : ℕ) :
    QuotSMulTop (n : ℤ) (Additive G) ≃+ Additive (powerClassQuotient G n) := by
  let f : Additive G →+ Additive (powerClassQuotient G n) :=
    MonoidHom.toAdditive (powerClassHom G n)
  have hker : ((n : ℤ) • (⊤ : Submodule ℤ (Additive G))).toAddSubgroup = f.ker := by
    rw [zsmulTop_toAddSubgroup_eq_powerSubgroup]
    ext x
    -- Membership in `Additive.toAddSubgroup` and in the kernel of `toAdditive` unfold to these.
    change x.toMul ∈ powerSubgroup G n ↔ powerClassHom G n x.toMul = 1
    rw [← MonoidHom.mem_ker, ker_powerClassHom]
  exact (QuotientAddGroup.quotientAddEquivOfEq hker).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective f (powerClassHom_surjective G n))

/-- The reduction/power-class equivalence sends the class of `x` to its power class. -/
@[simp]
theorem quotSMulTopPowerClassEquiv_mk {G : Type*} [CommGroup G] (n : ℕ) (x : Additive G) :
    quotSMulTopPowerClassEquiv n (Submodule.Quotient.mk x) =
      Additive.ofMul (powerClassHom G n x.toMul) := by
  -- Both quotient equivalences are `lift`s, which compute on classes by definition.
  rfl

end TauCeti
