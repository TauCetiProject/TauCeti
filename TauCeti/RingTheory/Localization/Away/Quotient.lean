/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Tactic.LinearCombination

/-!
# Away localizations of quotients

Let `B → A` be a surjective ring map whose kernel is annihilated by some `b ∈ B`. Inverting `b`
kills the kernel, so a localization of `A` away from the image of `b` is already a localization
of `B` away from `b`.

In the other direction, localization away from an element commutes with quotients: if `S` is a
localization of `R` away from `f`, then `S ⧸ I S` is a localization of `R ⧸ I` away from the
image of `f`. Moreover, if `A → B` is a localization at `M` factoring through `A ⧸ I`, then `B` is
a localization of `A ⧸ I` at the image of `M`.

## Main results

* `IsLocalization.Away.of_surjective_of_mul_eq_zero`: a localization of `A` away from the image
  of `b` is a localization of `B` away from `b`.
* `IsLocalization.Away.quotient`: `S ⧸ I S` is a localization of `R ⧸ I` away from the image of
  `f` whenever `S` is a localization of `R` away from `f`.
* `IsLocalization.of_quotient` and `IsLocalization.Away.of_quotient`: if a localization `B` of `A`
  at `M` (or away from `r`) factors through `A ⧸ I`, then `B` is a localization of `A ⧸ I` at the
  image of `M` (or away from the image of `r`).
-/

public section

/-- Let `B → A` be surjective, with kernel annihilated by `b ∈ B`. Then a localization of `A` away
from the image of `b` is a localization of `B` away from `b`. -/
theorem IsLocalization.Away.of_surjective_of_mul_eq_zero {B A T : Type*} [CommRing B]
    [CommRing A] [CommRing T] [Algebra B A] [Algebra A T] [Algebra B T] [IsScalarTower B A T]
    (hBA : Function.Surjective (algebraMap B A)) {b : B}
    (hb : ∀ x ∈ RingHom.ker (algebraMap B A), b * x = 0)
    [IsLocalization.Away (algebraMap B A b) T] : IsLocalization.Away b T := by
  refine .mk b ?_ (fun t ↦ ?_) fun x y h ↦ ?_
  · rw [IsScalarTower.algebraMap_apply B A T]
    exact IsLocalization.Away.algebraMap_isUnit _
  · obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (algebraMap B A b) t
    obtain ⟨x, rfl⟩ := hBA a
    exact ⟨n, x, by simpa [← IsScalarTower.algebraMap_apply] using ha⟩
  · rw [IsScalarTower.algebraMap_apply B A T, IsScalarTower.algebraMap_apply B A T y] at h
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (algebraMap B A b) h
    refine ⟨n + 1, ?_⟩
    have := hb (b ^ n * (x - y)) (by simp [mul_sub, hn])
    linear_combination this

/-- Localization away from an element commutes with quotients: if `S` is a localization of `R`
away from `f`, then `S ⧸ I S` is a localization of `R ⧸ I` away from the image of `f`. -/
instance IsLocalization.Away.quotient {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (f : R) [IsLocalization.Away f S] (I : Ideal R) :
    IsLocalization.Away (Ideal.Quotient.mk I f) (S ⧸ I.map (algebraMap R S)) := by
  have := (inferInstance : IsLocalization
    (Algebra.algebraMapSubmonoid (R ⧸ I) (Submonoid.powers f)) (S ⧸ I.map (algebraMap R S)))
  rwa [Algebra.algebraMapSubmonoid, Submonoid.map_powers] at this

/-- If `B` is a localization of `A` at `M` and `A → B` factors through `A ⧸ I`, then `B` is a
localization of `A ⧸ I` at the image of `M`. -/
theorem IsLocalization.of_quotient {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B] (I : Ideal A) [Algebra (A ⧸ I) B]
    [IsScalarTower A (A ⧸ I) B] :
    IsLocalization (Algebra.algebraMapSubmonoid (A ⧸ I) M) B := by
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · rintro ⟨_, m, hm, rfl⟩
    rw [← IsScalarTower.algebraMap_apply A (A ⧸ I) B]
    exact IsLocalization.map_units B ⟨m, hm⟩
  · intro b
    obtain ⟨⟨a, m⟩, ha⟩ := IsLocalization.surj M b
    refine ⟨⟨algebraMap A (A ⧸ I) a, algebraMap A (A ⧸ I) m, m, m.property, rfl⟩, ?_⟩
    simpa only [← IsScalarTower.algebraMap_apply A (A ⧸ I) B] using ha
  · intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply A (A ⧸ I) B,
      ← IsScalarTower.algebraMap_apply A (A ⧸ I) B] at hxy
    obtain ⟨m, hm⟩ := IsLocalization.exists_of_eq (M := M) hxy
    refine ⟨⟨algebraMap A (A ⧸ I) m, m, m.property, rfl⟩, ?_⟩
    simpa only [← map_mul, Ideal.Quotient.algebraMap_eq] using congrArg (Ideal.Quotient.mk I) hm

/-- If `B` is a localization of `A` away from `r` and `A → B` factors through `A ⧸ I`, then `B` is
a localization of `A ⧸ I` away from the image of `r`. -/
theorem IsLocalization.Away.of_quotient {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (r : A) [IsLocalization.Away r B] (I : Ideal A) [Algebra (A ⧸ I) B]
    [IsScalarTower A (A ⧸ I) B] :
    IsLocalization.Away (Ideal.Quotient.mk I r) B := by
  have h := IsLocalization.of_quotient (Submonoid.powers r) I (B := B)
  rwa [Algebra.algebraMapSubmonoid, Submonoid.map_powers, Ideal.Quotient.algebraMap_eq] at h
