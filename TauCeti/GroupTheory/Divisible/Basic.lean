/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.GroupTheory.Divisible
public import Mathlib.GroupTheory.Torsion

import Mathlib.Algebra.Category.Grp.Injective
import TauCeti.Algebra.Module.Rat
import TauCeti.GroupTheory.Torsion.Basic

/-!
# Divisible subgroups and compatible root families

`AddSubgroup.IsDivisible` expresses divisibility of a subgroup without choosing division
operations. The torsion subgroup and prime-primary components of a divisible abelian group are
divisible. The quotient by the torsion subgroup admits a rational module structure. This is an
existence theorem: callers may choose that structure locally and retain their own bases.

An `ℕ`-rootable monoid `G` becomes an `ℕ`-divisible additive monoid under `Additive G`:
`Additive.instDivisibleByNat` transfers `RootableBy G ℕ` to `DivisibleBy (Additive G) ℕ`.

In an `ℕ`-divisible additive commutative group `A`, injectivity of `A` as a `ℤ`-module
(`Module.Baer.of_divisible`) extends the map `1 ↦ x` along `ℤ ↪ ℚ`, yielding a compatible family
`y : ℕ+ → A` with `y 1 = x` and `d • y (n * d) = y n` for all `n d : ℕ+`. Transporting along
`Additive` gives the multiplicative counterpart for `ℕ`-rootable commutative groups `G`, and
handling zero separately extends this to commutative groups with zero `M₀` whose unit group `M₀ˣ`
is `ℕ`-rootable. More generally, for a `ℤ`-divisible additive commutative group `A` and an element
`d` of an additive commutative group `L` with no nonzero integer multiple in an additive subgroup
`S`, Baer's criterion extends `1 ↦ c` along `ℤ ↪ L ⧸ S` to an additive homomorphism `L →+ A`
vanishing on `S` and sending `d` to `c`.

## Main definitions

* `AddSubgroup.IsDivisible`: a subgroup in which multiplication by every `n ≠ 0` is surjective.
* `Additive.instDivisibleByNat`: transfers `RootableBy G ℕ` on a monoid `G` to
  `DivisibleBy (Additive G) ℕ`.

## Main results

* `TauCeti.nonempty_ratModule_quotient_torsion`: the torsion-free quotient of a divisible group
  admits a rational module structure, without choosing one globally.

* `TauCeti.AddCommGroup.isDivisible_torsion` and
  `TauCeti.AddCommGroup.isDivisible_primaryComponent`: the torsion subgroup and the prime-primary
  components of a divisible group are divisible.
* `AddSubgroup.exists_addMonoidHom_eq_zero_and_apply_eq`,
  `TauCeti.exists_addMonoidHom_apply_eq_zero_and_apply_eq`: additive homomorphisms `L →+ A` into a
  `ℤ`-divisible group vanishing on a subgroup `S` (or on `a`) and taking a prescribed value at an
  element `d` with no nonzero integer multiple in `S` (or in `ℤ • a`).
* `TauCeti.exists_apply_one_eq_and_forall_nsmul_eq`: compatible `ℕ+`-indexed multiples in an
  `ℕ`-divisible additive commutative group.
* `TauCeti.exists_apply_one_eq_and_forall_pow_eq`: compatible `ℕ+`-indexed roots in an `ℕ`-rootable
  commutative group.
* `TauCeti.exists_apply_one_eq_and_forall_pow_eq_of_rootableBy_units`: compatible `ℕ+`-indexed roots
  in a commutative group with zero whose unit group is `ℕ`-rootable.
-/

public section

open Function

namespace AddSubgroup

section AddGroup

variable {A B : Type*} [AddGroup A] [AddGroup B]

/-- An additive subgroup `D` is **divisible** if every element of `D` is an `n`-fold multiple of
an element of `D` for every `n ≠ 0`. -/
def IsDivisible (D : AddSubgroup A) : Prop :=
  ∀ n : ℕ, n ≠ 0 → ∀ x ∈ D, ∃ y ∈ D, n • y = x

theorem isDivisible_def {D : AddSubgroup A} :
    D.IsDivisible ↔ ∀ n : ℕ, n ≠ 0 → ∀ x ∈ D, ∃ y ∈ D, n • y = x :=
  Iff.rfl

/-- A subgroup is divisible exactly when multiplication by every `n ≠ 0` is surjective on it. -/
theorem isDivisible_iff_surjective_nsmul {D : AddSubgroup A} :
    D.IsDivisible ↔ ∀ n : ℕ, n ≠ 0 → Surjective fun y : D ↦ n • y := by
  refine ⟨fun hD n hn x ↦ ?_, fun hD n hn x hx ↦ ?_⟩
  · obtain ⟨y, hy, hyx⟩ := hD n hn x x.property
    exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
  · obtain ⟨y, hy⟩ := hD n hn ⟨x, hx⟩
    exact ⟨y, y.property, congrArg Subtype.val hy⟩

/-- A subgroup is divisible exactly when it carries a Mathlib `DivisibleBy _ ℕ` structure. -/
theorem isDivisible_iff_nonempty_divisibleBy {D : AddSubgroup A} :
    D.IsDivisible ↔ Nonempty (DivisibleBy D ℕ) := by
  rw [isDivisible_iff_surjective_nsmul]
  exact ⟨fun h ↦ ⟨divisibleByOfSMulRightSurj D ℕ fun hn ↦ h _ hn⟩,
    fun ⟨_⟩ _ hn ↦ DivisibleBy.surjective_smul D ℕ hn⟩

/-- The whole group is divisible exactly when multiplication by every `n ≠ 0` is surjective. -/
theorem isDivisible_top_iff :
    (⊤ : AddSubgroup A).IsDivisible ↔ ∀ n : ℕ, n ≠ 0 → Surjective fun x : A ↦ n • x :=
  ⟨fun h n hn x ↦ (h n hn x trivial).imp fun _ hy ↦ hy.2,
    fun h n hn x _ ↦ (h n hn x).imp fun _ hy ↦ ⟨trivial, hy⟩⟩

@[simp]
theorem isDivisible_bot : (⊥ : AddSubgroup A).IsDivisible := fun _ _ x hx ↦
  ⟨0, zero_mem _, by rw [(mem_bot).1 hx, smul_zero]⟩

namespace IsDivisible

/-- The image of a divisible subgroup under an additive homomorphism is divisible. -/
theorem map {D : AddSubgroup A} (hD : D.IsDivisible) (f : A →+ B) : (D.map f).IsDivisible := by
  rintro n hn _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, rfl⟩ := hD n hn x hx
  exact ⟨f y, mem_map_of_mem f hy, (map_nsmul f n y).symm⟩

end IsDivisible

end AddGroup

end AddSubgroup

namespace Additive

/-- An `ℕ`-rootable monoid becomes `ℕ`-divisible when viewed additively via `Additive`. -/
instance instDivisibleByNat {G : Type*} [Monoid G] [RootableBy G ℕ] :
    DivisibleBy (Additive G) ℕ where
  div a n := Additive.ofMul (RootableBy.root a.toMul n)
  div_zero a := congrArg Additive.ofMul (RootableBy.root_zero a.toMul)
  div_cancel a hn := congrArg Additive.ofMul (RootableBy.root_cancel a.toMul hn)

end Additive

namespace AddSubgroup

/-- If no nonzero integer multiple of `d` lies in the additive subgroup `S`, then any element `c`
of a `ℤ`-divisible additive commutative group `A` is the value at `d` of an additive homomorphism
`L →+ A` vanishing on `S` (constructed via Baer's criterion on `L ⧸ S`). -/
theorem exists_addMonoidHom_eq_zero_and_apply_eq {L A : Type*} [AddCommGroup L] [AddCommGroup A]
    [DivisibleBy A ℤ] (S : AddSubgroup L) {d : L} (hd : ∀ n : ℤ, n ≠ 0 → n • d ∉ S) (c : A) :
    ∃ w : L →+ A, (∀ s ∈ S, w s = 0) ∧ w d = c := by
  let π : L →+ L ⧸ S := QuotientAddGroup.mk' S
  let f : ℤ →+ L ⧸ S := zmultiplesHom (L ⧸ S) (π d)
  have hf : Function.Injective f := (injective_iff_map_eq_zero f).mpr fun n hn ↦
    by_contra fun hn0 ↦ hd n hn0 <| (QuotientAddGroup.eq_zero_iff (n • d)).mp <| by
      simpa [f, π, map_zsmul] using hn
  obtain ⟨φ, hφ⟩ :=
    (Module.Baer.of_divisible A).extension_property_addMonoidHom f hf (zmultiplesHom A c)
  refine ⟨φ.comp π, fun s hs ↦ ?_, ?_⟩
  · simp [π, (QuotientAddGroup.eq_zero_iff s).mpr hs]
  · simpa [f, π] using DFunLike.congr_fun hφ 1

end AddSubgroup

namespace TauCeti

/-- The torsion-free quotient of a divisible abelian group admits a rational module structure.
This existence theorem leaves callers free to choose the structure and its basis. -/
theorem nonempty_ratModule_quotient_torsion (A : Type*) [AddCommGroup A] [DivisibleBy A ℕ] :
    Nonempty (Module ℚ (A ⧸ AddCommGroup.torsion A)) :=
  nonempty_ratModule _

/-- If no nonzero integer multiple of `d` lies in `ℤ • a`, then any element `c` of a `ℤ`-divisible
additive commutative group `A` is the value at `d` of an additive homomorphism `L →+ A` sending `a`
to `0`. -/
theorem exists_addMonoidHom_apply_eq_zero_and_apply_eq {L A : Type*} [AddCommGroup L]
    [AddCommGroup A] [DivisibleBy A ℤ] {a d : L}
    (hd : ∀ (n k : ℤ), n ≠ 0 → n • d ≠ k • a) (c : A) :
    ∃ w : L →+ A, w a = 0 ∧ w d = c := by
  obtain ⟨w, hwS, hwd⟩ := (AddSubgroup.zmultiples a).exists_addMonoidHom_eq_zero_and_apply_eq
    (fun n hn hmem ↦ by
      obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
      exact hd n k hn hk.symm) c
  exact ⟨w, hwS a (AddSubgroup.mem_zmultiples a), hwd⟩

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

namespace TauCeti.AddCommGroup

open AddSubgroup

/-- The torsion subgroup of a divisible abelian group is divisible. -/
theorem isDivisible_torsion {A : Type*} [AddCommGroup A] [DivisibleBy A ℕ] :
    (AddCommGroup.torsion A).IsDivisible := by
  rw [isDivisible_def]
  intro n hn x hx
  obtain ⟨y, hy⟩ : ∃ y : A, n • y = x := DivisibleBy.surjective_smul A ℕ hn x
  obtain ⟨k, hk, hkx⟩ := (AddCommGroup.mem_torsion x).mp hx |>.exists_nsmul_eq_zero
  refine ⟨y, ?_, hy⟩
  exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    ⟨k * n, Nat.mul_pos hk (Nat.pos_of_ne_zero hn), by rw [← smul_smul, hy, hkx]⟩

/-- A prime-primary component of a divisible abelian group is divisible. -/
theorem isDivisible_primaryComponent {A : Type*} [AddCommGroup A] [DivisibleBy A ℕ]
    (p : ℕ) (hp : p.Prime) : (AddCommGroup.primaryComponent A p).IsDivisible := by
  rw [AddSubgroup.isDivisible_def]
  intro n hn x hx
  obtain ⟨y, hy⟩ : ∃ y : A, n • y = x := DivisibleBy.surjective_smul A ℕ hn x
  obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp hx
  have hyfin : IsOfFinAddOrder y := isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    ⟨p ^ k * n, Nat.mul_pos (pow_pos hp.pos _) (Nat.pos_of_ne_zero hn), by
      rw [← smul_smul, hy, hk]⟩
  obtain ⟨y', hy', heq⟩ := exists_mem_primaryComponent_apply_eq
    (nsmulAddMonoidHom (α := A) n) hp hyfin (AddCommMonoid.mem_primaryComponent.mpr ⟨k, by
      simpa only [nsmulAddMonoidHom_apply, hy] using hk⟩)
  exact ⟨y', hy', heq.trans hy⟩

end TauCeti.AddCommGroup
