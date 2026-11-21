/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Data.PNat.Basic
public import Mathlib.GroupTheory.Divisible

import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Algebra.Module.Injective
import Mathlib.Data.Rat.Cast.CharZero

/-!
# Divisibility on `Additive`, compatible root families, and character extensions

An `ℕ`-rootable monoid `G` becomes an `ℕ`-divisible additive monoid under `Additive G`:
`Additive.instDivisibleByNat` transfers `RootableBy G ℕ` to `DivisibleBy (Additive G) ℕ`.

In an `ℕ`-divisible additive commutative group `A`, injectivity of `A` as a `ℤ`-module
(`Module.Baer.of_divisible`) extends the map `1 ↦ x` along `ℤ ↪ ℚ`, yielding a compatible family
`y : ℕ+ → A` with `y 1 = x` and `d • y (n * d) = y n` for all `n d : ℕ+`. Transporting along
`Additive` gives the multiplicative counterpart for `ℕ`-rootable commutative groups `G`, and
handling zero separately extends this to commutative groups with zero `M₀` whose unit group `M₀ˣ`
is `ℕ`-rootable.

Similarly, injectivity of `Additive U` for an `ℕ`-rootable commutative group `U` allows any
character `Multiplicative H →* U` to extend along any injective additive group homomorphism
`f : H →+ L` (`RootableBy.exists_monoidHom_comp_toMultiplicative_eq`).

## Main definitions

* `Additive.instDivisibleByNat`: transfers `RootableBy G ℕ` on a monoid `G` to
  `DivisibleBy (Additive G) ℕ`.

## Main results

* `TauCeti.exists_apply_one_eq_and_forall_nsmul_eq`: compatible `ℕ+`-indexed multiples in an
  `ℕ`-divisible additive commutative group.
* `TauCeti.exists_apply_one_eq_and_forall_pow_eq`: compatible `ℕ+`-indexed roots in an `ℕ`-rootable
  commutative group.
* `TauCeti.exists_apply_one_eq_and_forall_pow_eq_of_rootableBy_units`: compatible `ℕ+`-indexed roots
  in a commutative group with zero whose unit group is `ℕ`-rootable.
* `RootableBy.exists_monoidHom_comp_toMultiplicative_eq`: extending a character
  `Multiplicative H →* U` along an injective `f : H →+ L` when `[RootableBy U ℕ]`.

## References

* W. Bruns and J. Gubeladze, *Polytopes, Rings, and K-Theory*, Chapter 2.
* S. Lang, *Algebra*, Chapter III (divisible abelian groups and injectivity).
-/

public section

namespace Additive

/-- An `ℕ`-rootable monoid becomes `ℕ`-divisible when viewed additively via `Additive`. -/
instance instDivisibleByNat {G : Type*} [Monoid G] [RootableBy G ℕ] :
    DivisibleBy (Additive G) ℕ where
  div a n := Additive.ofMul (RootableBy.root a.toMul n)
  div_zero a := congrArg Additive.ofMul (RootableBy.root_zero a.toMul)
  div_cancel a hn := congrArg Additive.ofMul (RootableBy.root_cancel a.toMul hn)

end Additive

namespace TauCeti

/-- Every element of an `ℕ`-divisible additive commutative group admits a compatible `ℕ+`-indexed
family of divisions: `y 1 = x` and `d • y (n * d) = y n` for all `n d : ℕ+`. -/
theorem exists_apply_one_eq_and_forall_nsmul_eq {A : Type*} [AddCommGroup A] [DivisibleBy A ℕ]
    (x : A) :
    ∃ y : ℕ+ → A, y 1 = x ∧ ∀ n d : ℕ+, (d : ℕ) • y (n * d) = y n := by
  let : DivisibleBy A ℤ := AddGroup.divisibleByIntOfDivisibleByNat A
  obtain ⟨χ, hχ⟩ := (Module.Baer.of_divisible A).extension_property_addMonoidHom
    (Int.castAddHom ℚ) Int.cast_injective (zmultiplesHom A x)
  refine ⟨fun n ↦ χ (1 / (n : ℚ)), ?_, fun n d ↦ ?_⟩
  · have h1 := DFunLike.congr_fun hχ 1
    simp only [AddMonoidHom.comp_apply, Int.coe_castAddHom, Int.cast_one, zmultiplesHom_apply,
      one_smul] at h1
    simp [h1]
  · have hq : (d : ℕ) • (1 / ((n * d : ℕ+) : ℚ)) = 1 / (n : ℚ) := by
      have hd : ((d : ℕ) : ℚ) ≠ 0 := by exact_mod_cast d.ne_zero
      rw [nsmul_eq_mul, PNat.mul_coe, Nat.cast_mul, mul_one_div, div_mul_eq_div_div_swap,
        div_self hd]
    simpa only [map_nsmul] using congrArg χ hq

/-- Every element of an `ℕ`-rootable commutative group admits a compatible `ℕ+`-indexed family of
roots: `y 1 = x` and `y (n * d) ^ (d : ℕ) = y n` for all `n d : ℕ+`. -/
theorem exists_apply_one_eq_and_forall_pow_eq {G : Type*} [CommGroup G] [RootableBy G ℕ] (x : G) :
    ∃ y : ℕ+ → G, y 1 = x ∧ ∀ n d : ℕ+, y (n * d) ^ (d : ℕ) = y n := by
  obtain ⟨y, hy1, hyd⟩ := exists_apply_one_eq_and_forall_nsmul_eq (Additive.ofMul x)
  exact ⟨fun n ↦ (y n).toMul, congrArg Additive.toMul hy1,
    fun n d ↦ by simpa only [toMul_nsmul] using congrArg Additive.toMul (hyd n d)⟩

/-- Every element of a commutative group with zero whose unit group is `ℕ`-rootable admits a
compatible `ℕ+`-indexed family of roots: `y 1 = x` and `y (n * d) ^ (d : ℕ) = y n` for all
`n d : ℕ+`. -/
theorem exists_apply_one_eq_and_forall_pow_eq_of_rootableBy_units {M₀ : Type*}
    [CommGroupWithZero M₀] [RootableBy M₀ˣ ℕ] (x : M₀) :
    ∃ y : ℕ+ → M₀, y 1 = x ∧ ∀ n d : ℕ+, y (n * d) ^ (d : ℕ) = y n := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨0, rfl, fun _ d ↦ zero_pow d.ne_zero⟩
  obtain ⟨y, hy1, hyd⟩ := exists_apply_one_eq_and_forall_pow_eq (Units.mk0 x hx)
  exact ⟨fun n ↦ (y n : M₀), by simpa using congrArg Units.val hy1,
    fun n d ↦ by simpa only [Units.val_pow_eq_pow_val] using congrArg Units.val (hyd n d)⟩

end TauCeti

namespace RootableBy

/-- Into any commutative group `U` that is `ℕ`-rootable (for instance `Kˣ` for an algebraically
closed field `K` via `TauCeti.IsAlgClosed.unitsRootableByNat`), every character
`Multiplicative H →* U` extends along any injective additive group homomorphism `f : H →+ L`. -/
theorem exists_monoidHom_comp_toMultiplicative_eq {H L U : Type*} [AddCommGroup H]
    [AddCommGroup L] [CommGroup U] [RootableBy U ℕ] {f : H →+ L} (hf : Function.Injective f)
    (ψ : Multiplicative H →* U) :
    ∃ χ : Multiplicative L →* U, χ.comp f.toMultiplicative = ψ := by
  let : DivisibleBy (Additive U) ℤ := AddGroup.divisibleByIntOfDivisibleByNat (Additive U)
  obtain ⟨g, hg⟩ := (Module.Baer.of_divisible (Additive U)).extension_property_addMonoidHom
    f hf ψ.toAdditiveRight
  exact ⟨AddMonoidHom.toMultiplicativeLeft g, MonoidHom.ext fun x ↦ by
    simpa using congrArg Additive.toMul (DFunLike.congr_fun hg x.toAdd)⟩

end RootableBy
