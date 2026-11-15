/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import TauCeti.Algebra.Module.ZMod.TensorProduct

/-!
# Divisible groups and Serre classes

For a natural number `n`, an abelian group `G` is `n`-divisible when multiplication by `n` on `G`
is surjective; equivalently `G ⊗ ℤ/n = 0` (`TauCeti.subsingleton_zmod_tensorProduct_iff`). This
file records the `n`-divisible groups as an object property of `AddCommGrpCat` and determines which
of Serre's closure properties they have.

They contain the zero group and are closed under quotients and extensions. For `n ≥ 2` they are
not closed under subgroups: `ℚ` is `n`-divisible and its subgroup `ℤ` is not. So for `n ≥ 2`
the class `{G | G ⊗ ℤ/n = 0}` is **not** a Serre class; for `n = 0` it consists of the zero groups
and for `n = 1` of all groups, and both are Serre classes. In particular a theorem modulo a Serre
class does not apply to the class `{G | G ⊗ ℤ/2 = 0}`; vanishing of `π_i ⊗ ℤ/2` is instead
reached through unique two-divisibility, which implies it.

## Main definitions

* `AddCommGrpCat.isDivisibleBy n`: the `n`-divisible abelian groups, as an object property.

## Main results

* `AddCommGrpCat.prop_isDivisibleBy_iff_subsingleton_tensorProduct`: `G` is `n`-divisible exactly
  when `ℤ/n ⊗ G = 0`.
* `AddCommGrpCat.isDivisibleBy` contains the zero group and is closed under quotients and
  extensions (instances).
* `AddCommGrpCat.isClosedUnderSubobjects_isDivisibleBy_iff`: it is closed under subgroups exactly
  when `n ≤ 1`.
* `AddCommGrpCat.isSerreClass_isDivisibleBy_iff`: it is a Serre class exactly when `n ≤ 1`.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  Chapter I.
-/

public section

universe u

open CategoryTheory Limits

namespace AddCommGrpCat

/-- The `n`-divisible abelian groups, those on which multiplication by `n` is surjective, as an
object property of `AddCommGrpCat`. -/
def isDivisibleBy (n : ℕ) : ObjectProperty AddCommGrpCat.{u} := fun M ↦
  Function.Surjective fun x : M ↦ (n : ℤ) • x

/-- An abelian group belongs to `isDivisibleBy n` exactly when every element is `n` times some
element. -/
@[simp]
lemma prop_isDivisibleBy_iff (n : ℕ) (M : AddCommGrpCat.{u}) :
    isDivisibleBy n M ↔ ∀ x : M, ∃ y : M, (n : ℤ) • y = x :=
  Iff.rfl

/-- An abelian group is `n`-divisible exactly when its tensor product with `ℤ/n` vanishes. -/
lemma prop_isDivisibleBy_iff_subsingleton_tensorProduct (n : ℕ) (M : AddCommGrpCat.{u}) :
    isDivisibleBy n M ↔ Subsingleton (TensorProduct ℤ (ZMod n) M) :=
  (TauCeti.subsingleton_zmod_tensorProduct_iff n).symm

instance (n : ℕ) : (isDivisibleBy.{u} n).ContainsZero where
  exists_zero := ⟨AddCommGrpCat.of PUnit, isZero_of_subsingleton _,
    fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

/-- A quotient of an `n`-divisible group is `n`-divisible. -/
instance (n : ℕ) : (isDivisibleBy.{u} n).IsClosedUnderQuotients where
  prop_of_epi {M N} f hf hM y := by
    obtain ⟨x, rfl⟩ := (AddCommGrpCat.epi_iff_surjective f).1 hf y
    obtain ⟨z, rfl⟩ := hM x
    exact ⟨f z, (map_zsmul f.hom _ z).symm⟩

/-- An extension of an `n`-divisible group by an `n`-divisible group is `n`-divisible. -/
instance (n : ℕ) : (isDivisibleBy.{u} n).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    rw [prop_isDivisibleBy_iff] at h₁ h₃ ⊢
    intro x₂
    -- Divide the image of `x₂` in `S.X₃`, lift the quotient to `y₂`, and divide the error
    -- `x₂ - n • y₂`, which comes from `S.X₁`.
    obtain ⟨y₃, hy₃⟩ := h₃ (S.g x₂)
    obtain ⟨y₂, rfl⟩ := (AddCommGrpCat.epi_iff_surjective S.g).1 hS.epi_g y₃
    obtain ⟨x₁, hx₁⟩ := (ShortComplex.ab_exact_iff S).1 hS.exact ((n : ℤ) • y₂ - x₂) (by
      rw [map_sub, map_zsmul, hy₃, sub_self])
    obtain ⟨z₁, rfl⟩ := h₁ x₁
    refine ⟨y₂ - S.f z₁, ?_⟩
    rw [smul_sub, ← map_zsmul, hx₁, sub_sub_cancel]

/-- The inclusion `ℤ → ℚ`, in an arbitrary universe. -/
private def intToRat : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ AddCommGrpCat.of (ULift.{u} ℚ) :=
  ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp
    ((Int.castAddHom ℚ).comp AddEquiv.ulift.toAddMonoidHom))

private lemma injective_intToRat : Function.Injective intToRat.{u} := fun _ _ h ↦
  ULift.ext (Int.cast_injective (α := ℚ) (congrArg ULift.down h))

private lemma isDivisibleBy_rat {n : ℕ} (hn : n ≠ 0) :
    isDivisibleBy n (AddCommGrpCat.of (ULift.{u} ℚ)) := fun x ↦
  ⟨⟨x.down / n⟩, ULift.ext (by
    rw [ULift.smul_down, zsmul_eq_mul, Int.cast_natCast,
      mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hn)])⟩

private lemma not_isDivisibleBy_int {n : ℕ} (hn : 2 ≤ n) :
    ¬ isDivisibleBy n (AddCommGrpCat.of (ULift.{u} ℤ)) := fun h ↦ by
  obtain ⟨y, hy⟩ := h ⟨1⟩
  have h1 : (n : ℤ) * y.down = 1 := by
    rw [← smul_eq_mul]
    exact congrArg ULift.down hy
  have := Int.eq_one_of_mul_eq_one_right (by positivity) h1
  omega

/-- The `n`-divisible groups are closed under subgroups exactly when `n ≤ 1`: for `n = 0` they are
the zero groups and for `n = 1` all groups, while for `n ≥ 2` the subgroup `ℤ` of the
`n`-divisible group `ℚ` is not `n`-divisible. -/
theorem isClosedUnderSubobjects_isDivisibleBy_iff (n : ℕ) :
    (isDivisibleBy.{u} n).IsClosedUnderSubobjects ↔ n ≤ 1 := by
  refine ⟨fun h ↦ ?_, fun hn ↦ ⟨fun {M N} f hf hN x ↦ ?_⟩⟩
  · by_contra! hn
    have : Mono intToRat.{u} := (AddCommGrpCat.mono_iff_injective _).2 injective_intToRat
    exact not_isDivisibleBy_int hn ((isDivisibleBy n).prop_of_mono intToRat
      (isDivisibleBy_rat (by omega)))
  · obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
    · -- Multiplication by `0` is surjective only on the zero group, and `M` injects into `N`.
      obtain ⟨y, hy⟩ := hN (f x)
      refine ⟨x, (AddCommGrpCat.mono_iff_injective f).1 hf ?_⟩
      rw [← hy]
      simp
    · exact ⟨x, by simp⟩

/-- The `n`-divisible groups form a Serre class exactly when `n ≤ 1`. In particular the groups
`G` with `G ⊗ ℤ/2 = 0` do not form a Serre class. -/
theorem isSerreClass_isDivisibleBy_iff (n : ℕ) :
    (isDivisibleBy.{u} n).IsSerreClass ↔ n ≤ 1 :=
  ⟨fun _ ↦ (isClosedUnderSubobjects_isDivisibleBy_iff n).1 inferInstance,
    fun hn ↦ have := (isClosedUnderSubobjects_isDivisibleBy_iff n).2 hn; { }⟩

end AddCommGrpCat
