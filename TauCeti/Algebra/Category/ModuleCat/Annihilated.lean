/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.CategoryTheory.ObjectProperty.KilledBy
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.IdempotentFG
import TauCeti.Algebra.Module.Annihilator

/-!
# Serre classes of modules annihilated by ideals

For an idempotent ideal `I` of a ring `R`, modules annihilated by `I` form a
Serre class. This supplies the Serre class of almost zero modules used to construct the
almost category. No flatness assumption on `I` or its tensor square is needed.

Modules annihilated by some positive power of any ideal also form a Serre class, with no
finiteness or noetherianity assumption. Both cases use the product of annihilating ideals
as a bound for the annihilator of an extension.

For a commutative ring, idempotence is necessary: closure under extensions, applied to the
kernel sequence of `R / I² → R / I`, forces `I` to annihilate `R / I²`, hence `I ⊆ I²`.
Thus, for `R`-modules in the universe of `R`, annihilation by an ideal of a commutative ring
is a Serre property exactly for idempotent ideals.

Over a domain the only idempotent principal ideals are `0` and `R`, so annihilation by a single
element `a` is a Serre property exactly when `a` is zero or a unit. For `R = ℤ`: abelian groups
killed by a fixed integer `n` form a Serre class only for `n ∈ {0, 1, -1}`. In particular, for
`d ≥ 2` and `m ≥ 1`, the groups killed by `dᵐ` are not closed under extensions (`ℤ/d²ᵐ` is an
extension of `ℤ/dᵐ` by itself), whereas the groups killed by some power of `d` are a Serre class.

A natural number `e` kills a module in the categorical sense of
`CategoryTheory.ObjectProperty.isKilledBy`, `e • 𝟙 M = 0`, exactly when it annihilates every
element (`ModuleCat.prop_isKilledBy_iff`).

## References

* O. Gabber and L. Ramero, *Almost ring theory*, §2.2, (2.2.2).
* P. Scholze, *Perfectoid spaces*, §4, Lemma 4.2.
-/

public section

universe u v

open CategoryTheory

namespace TauCeti

/-- Modules killed by some member of a nonempty family of ideals form a Serre class if
every product of two members contains a member of the family. -/
theorem isSerreClass_exists_le_annihilator {R : Type u} [Ring R] {ι : Type*}
    (F : ι → Ideal R) (hne : Nonempty ι) (hmul : ∀ i j, ∃ k, F k ≤ F i * F j) :
    ObjectProperty.IsSerreClass
      (fun M : ModuleCat.{v} R ↦ ∃ i, F i ≤ Module.annihilator R M) where
  exists_zero := by
    obtain ⟨i⟩ := hne
    exact ⟨ModuleCat.of R PUnit, ModuleCat.isZero_of_subsingleton _, i,
      fun _ _ ↦ Module.mem_annihilator.mpr fun _ ↦ Subsingleton.elim _ _⟩
  prop_of_mono f hf := fun ⟨i, hi⟩ ↦
    ⟨i, hi.trans (f.hom.annihilator_le_of_injective ((ModuleCat.mono_iff_injective f).mp hf))⟩
  prop_of_epi f hf := fun ⟨i, hi⟩ ↦
    ⟨i, hi.trans (f.hom.annihilator_le_of_surjective ((ModuleCat.epi_iff_surjective f).mp hf))⟩
  prop_X₂_of_shortExact {S} hS := fun ⟨i, hi⟩ ⟨j, hj⟩ ↦ by
    obtain ⟨k, hk⟩ := hmul i j
    exact ⟨k, hk.trans (S.f.hom.mul_le_annihilator_of_exact S.g.hom
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact) hi hj)⟩

end TauCeti

namespace Ideal

/-- Modules killed by an idempotent ideal form a Serre class, in any module universe. -/
theorem isSerreClass_isTorsionBySet {R : Type u} [Ring R] (I : Ideal R)
    (hI : IsIdempotentElem I) :
    ObjectProperty.IsSerreClass
      (fun M : ModuleCat.{v} R ↦ Module.IsTorsionBySet R M (I : Set R)) := by
  simp only [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe]
  simpa only [exists_const] using
    (TauCeti.isSerreClass_exists_le_annihilator (fun _ : Unit ↦ I) ⟨()⟩
      (fun _ _ ↦ ⟨(), hI.eq.ge⟩))

/-- Modules annihilated by some positive power of an ideal form a Serre class. -/
theorem isSerreClass_exists_pow_le_annihilator {R : Type u} [Ring R] (I : Ideal R) :
    ObjectProperty.IsSerreClass
      (fun M : ModuleCat.{v} R ↦ ∃ n : ℕ, 0 < n ∧ I ^ n ≤ Module.annihilator R M) := by
  simpa only [Subtype.exists, exists_prop] using
    (TauCeti.isSerreClass_exists_le_annihilator (fun n : {n : ℕ // 0 < n} ↦ I ^ n.val)
      ⟨⟨1, Nat.one_pos⟩⟩ (fun a b ↦ ⟨⟨a.val + b.val, Nat.add_pos_left a.property b.val⟩,
        (Submodule.pow_add I b.property.ne').le⟩))

variable {R : Type u} [CommRing R]

/-- If modules in the universe of `R` killed by `I` are closed under extensions,
then `I` is idempotent. -/
theorem isIdempotentElem_of_isClosedUnderExtensions_isTorsionBySet (I : Ideal R)
    (h : ObjectProperty.IsClosedUnderExtensions
      (fun M : ModuleCat.{u} R ↦ Module.IsTorsionBySet R M (I : Set R))) : IsIdempotentElem I := by
  let f := (Quotient.factorₐ R (mul_le_left : I * I ≤ I)).toLinearMap
  have hf (r : R) : f (Quotient.mk (I * I) r) = Quotient.mk I r :=
    Quotient.factorₐ_apply_mk R (mul_le_left : I * I ≤ I) r
  have hker : Module.IsTorsionBySet R (LinearMap.ker f) (I : Set R) := by
    intro x a
    apply Subtype.ext
    obtain ⟨r, hr⟩ := Quotient.mk_surjective (x : R ⧸ (I * I))
    have hrI : r ∈ I := Quotient.eq_zero_iff_mem.mp (by
      rw [← hf, hr]
      exact x.property)
    simpa [← hr, Algebra.smul_def] using
      (Quotient.eq_zero_iff_mem.mpr (mul_mem_mul a.property hrI))
  have hquot : Module.IsTorsionBySet R (R ⧸ I) (I : Set R) :=
    (Module.isTorsionBySet_quotient_iff I (I : Set R)).mpr fun r a ha ↦ I.mul_mem_right r ha
  have hmid : Module.IsTorsionBySet R (R ⧸ (I * I)) (I : Set R) :=
    h.prop_X₂_of_shortExact
      (LinearMap.shortExact_shortComplexKer (f := f)
        (Quotient.factor_surjective (mul_le_left : I * I ≤ I))) hker hquot
  exact (mul_le_left.antisymm fun r hr ↦ Quotient.eq_zero_iff_mem.mp (by
    simpa [Algebra.smul_def] using
      (hmid (x := Quotient.mk (I * I) 1) (a := ⟨r, hr⟩))) : I * I = I)

/-- Modules in the universe of `R` annihilated by `I` form a Serre class exactly when
`I` is idempotent. -/
theorem isSerreClass_isTorsionBySet_iff (I : Ideal R) :
    ObjectProperty.IsSerreClass
      (fun M : ModuleCat.{u} R ↦ Module.IsTorsionBySet R M (I : Set R)) ↔
      IsIdempotentElem I :=
  ⟨fun h ↦ I.isIdempotentElem_of_isClosedUnderExtensions_isTorsionBySet
    h.toIsClosedUnderExtensions, I.isSerreClass_isTorsionBySet⟩

end Ideal

namespace ModuleCat

/-- A natural number `e` kills a module, as an object of `ModuleCat R`, exactly when it annihilates
every element. -/
theorem prop_isKilledBy_iff {R : Type u} [Ring R] (e : ℕ) (M : ModuleCat.{v} R) :
    ObjectProperty.isKilledBy (ModuleCat.{v} R) e M ↔ ∀ x : M, e • x = 0 := by
  rw [ObjectProperty.prop_isKilledBy_iff]
  refine ⟨fun h x ↦ by simpa using congr(($h).hom x), fun h ↦ ?_⟩
  ext x
  simpa using h x

end ModuleCat

namespace TauCeti

/-- Over a domain, modules in the universe of `R` killed by a single element `a` form a Serre
class exactly when `a` is zero or a unit. -/
theorem isSerreClass_isTorsionBy_iff {R : Type u} [CommRing R] [IsDomain R] (a : R) :
    ObjectProperty.IsSerreClass (fun M : ModuleCat.{u} R ↦ Module.IsTorsionBy R M a) ↔
      a = 0 ∨ IsUnit a := by
  simp_rw [← Module.isTorsionBySet_span_singleton_iff]
  rw [(Ideal.span {a}).isSerreClass_isTorsionBySet_iff,
    Ideal.isIdempotentElem_iff_eq_bot_or_top _ (Submodule.fg_span_singleton a),
    Ideal.span_singleton_eq_bot, Ideal.span_singleton_eq_top]

end TauCeti
