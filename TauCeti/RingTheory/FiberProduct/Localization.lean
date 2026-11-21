/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Principal localization of a ring pullback

Localizing a pullback square of commutative rings at an element of the upper-left ring and
at its images gives another pullback square. The localization carriers can be any actual
localizations, including section rings on basic opens.

This is [Stacks Project, Lemma 15.5.3, tag 01Z8](https://stacks.math.columbia.edu/tag/01Z8).
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat

universe u

private def powerDenominator {R : Type*} [CommMonoid R] (r : R) (n : ℕ) :
    Submonoid.powers r :=
  ⟨r ^ n, n, rfl⟩

private theorem exists_fraction {R L : Type*} [CommRing R] [CommRing L] [Algebra R L]
    (r : R) [IsLocalization.Away r L] (z : L) :
    ∃ x n, IsLocalization.mk' L x (powerDenominator r n) = z := by
  obtain ⟨x, ⟨_, n, rfl⟩, hx⟩ := IsLocalization.exists_mk'_eq (.powers r) z
  exact ⟨x, n, hx⟩

private theorem map_fraction {R S L M : Type*} [CommRing R] [CommRing S]
    [CommRing L] [CommRing M] [Algebra R L] [Algebra S M]
    {r : R} {s : S} [IsLocalization.Away r L] [IsLocalization.Away s M]
    (f : R →+* S) (F : L →+* M) (hr : f r = s)
    (h : ∀ x, F (algebraMap R L x) = algebraMap S M (f x)) (x : R) (n : ℕ) :
    F (IsLocalization.mk' L x (powerDenominator r n)) =
      IsLocalization.mk' M (f x) (powerDenominator s n) := by
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  have hn := congrArg F (IsLocalization.mk'_spec L x (powerDenominator r n))
  simpa only [map_mul, h, powerDenominator, map_pow, hr] using hn

private theorem scale_fraction {R L : Type*} [CommRing R] [CommRing L] [Algebra R L]
    {r : R} [IsLocalization.Away r L] (x : R) (n m : ℕ) :
    IsLocalization.mk' L (r ^ m * x) (powerDenominator r (n + m)) =
      IsLocalization.mk' L x (powerDenominator r n) := by
  convert IsLocalization.mk'_cancel (S := L) x (powerDenominator r n)
    (powerDenominator r m) using 2
  · exact mul_comm _ _
  · apply Subtype.ext
    exact pow_add r n m

private theorem injective_prod_away {A B C D A' B' C' : CommRingCat.{u}}
    {i : A ⟶ B} {j : A ⟶ C} {f : B ⟶ D} {g : C ⟶ D} (h : IsPullback i j f g)
    (r : A) [Algebra A A'] [Algebra B B'] [Algebra C C']
    [IsLocalization.Away r A'] [IsLocalization.Away (i r) B'] [IsLocalization.Away (j r) C']
    {i' : A' ⟶ B'} {j' : A' ⟶ C'}
    (hi : ∀ x, i' (algebraMap A A' x) = algebraMap B B' (i x))
    (hj : ∀ x, j' (algebraMap A A' x) = algebraMap C C' (j x)) :
    Function.Injective (i'.hom.prod j'.hom) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  have hiz : i' z = 0 := congrArg Prod.fst hz
  have hjz : j' z = 0 := congrArg Prod.snd hz
  obtain ⟨a, n, rfl⟩ := exists_fraction r z
  rw [map_fraction (r := r) i.hom i'.hom rfl hi, IsLocalization.mk'_eq_zero_iff] at hiz
  rw [map_fraction (r := r) j.hom j'.hom rfl hj, IsLocalization.mk'_eq_zero_iff] at hjz
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := hiz
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := hjz
  apply (IsLocalization.mk'_eq_zero_iff _ _).mpr
  -- Pullback extensionality is in Types. Recover the ring morphisms to use their map laws.
  refine ⟨powerDenominator r (m + k),
    Types.ext_of_isPullback (h.map (forget CommRingCat.{u})) ?_ ?_⟩
  · change i (r ^ (m + k) * a) = i 0
    rw [Nat.add_comm m k]
    simp [pow_add, mul_assoc, hm]
  · change j (r ^ (m + k) * a) = j 0
    simp [pow_add, mul_assoc, hk]

/-- A pullback square of commutative rings stays a pullback when localizing at an element of the
upper-left ring. The four given maps on localizations agree with the original arrows on numerators,
so the statement also applies to the section maps on principal opens. -/
theorem isPullback_of_away {A B C D A' B' C' D' : CommRingCat.{u}}
    {i : A ⟶ B} {j : A ⟶ C} {f : B ⟶ D} {g : C ⟶ D} (h : IsPullback i j f g)
    (r : A) [Algebra A A'] [Algebra B B'] [Algebra C C'] [Algebra D D']
    [IsLocalization.Away r A'] [IsLocalization.Away (i r) B']
    [IsLocalization.Away (j r) C'] [IsLocalization.Away (f (i r)) D']
    {i' : A' ⟶ B'} {j' : A' ⟶ C'} {f' : B' ⟶ D'} {g' : C' ⟶ D'}
    (hi : ∀ x, i' (algebraMap A A' x) = algebraMap B B' (i x))
    (hj : ∀ x, j' (algebraMap A A' x) = algebraMap C C' (j x))
    (hf : ∀ x, f' (algebraMap B B' x) = algebraMap D D' (f x))
    (hg : ∀ x, g' (algebraMap C C' x) = algebraMap D D' (g x)) :
    IsPullback i' j' f' g' := by
  let F := forget CommRingCat.{u}
  let : ReflectsLimitsOfShape WalkingCospan F := reflectsLimitsOfShape_of_reflectsIsomorphisms
  have hRing (a : A) : f (i a) = g (j a) :=
    ConcreteCategory.congr_hom h.w a
  have hTypes := h.map F
  have hi' := map_fraction (r := r) i.hom i'.hom rfl hi
  have hj' := map_fraction (r := r) j.hom j'.hom rfl hj
  have hf' := map_fraction (r := i r) f.hom f'.hom rfl hf
  have hg' := map_fraction (r := j r) g.hom g'.hom (hRing r).symm hg
  -- Check the underlying pullback in Types. The `change` steps recover the ring morphisms
  -- from their images under the forgetful functor.
  apply IsPullback.of_map_of_faithful F
  refine (Types.isPullback_iff ..).mpr ⟨?_, ?_, ?_⟩
  · ext z
    obtain ⟨a, n, rfl⟩ := exists_fraction r z
    change f' (i' _) = g' (j' _)
    rw [hi', hf', hj', hg']
    -- Fix the denominator to keep its localization instance in the numerator rewrite.
    exact congrArg (fun a : D ↦ IsLocalization.mk' D' a (powerDenominator (f (i r)) n)) (hRing a)
  · rintro x y ⟨hixy, hjxy⟩
    exact injective_prod_away h r hi hj (Prod.ext hixy hjxy)
  · intro x y hxy
    change f' x = g' y at hxy
    obtain ⟨b, n, rfl⟩ := exists_fraction (i r) x
    obtain ⟨c, m, rfl⟩ := exists_fraction (j r) y
    let b₀ := i r ^ m * b
    let c₀ := j r ^ n * c
    have hb := scale_fraction (L := B') (r := i r) b n m
    have hc := scale_fraction (L := C') (r := j r) c m n
    rw [Nat.add_comm m n] at hc
    rw [← hb, ← hc, hf', hg'] at hxy
    have hnum : algebraMap D D' (f b₀) = algebraMap D D' (g c₀) := by
      simpa only [IsLocalization.mk'_spec] using
        congrArg (fun z ↦ z * algebraMap D D' ((powerDenominator (f (i r)) (n + m)) : D)) hxy
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.eq_iff_exists (.powers (f (i r))) D').mp hnum
    have hpair : f (i r ^ k * b₀) = g (j r ^ k * c₀) := by
      simpa only [map_mul, map_pow, ← hRing r] using hk
    obtain ⟨a, ha, ha'⟩ := Types.exists_of_isPullback hTypes _ _ hpair
    change i a = _ at ha
    change j a = _ at ha'
    refine ⟨IsLocalization.mk' A' a (powerDenominator r (n + m + k)), ?_, ?_⟩
    · change i' _ = _
      rw [hi', ha, scale_fraction, hb]
    · change j' _ = _
      rw [hj', ha', scale_fraction, hc]

end CommRingCat
