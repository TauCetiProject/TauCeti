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
image of `f`.

Combining a quotient comparison with localization lifts primes: if `R → R'` induces an isomorphism
`R ⧸ (f) ≃ R' ⧸ (f')`, then a prime of `R` containing `f` comes from `R'` and a prime avoiding `f`
comes from `R_f`, a localization of `R` away from `f`.

## Main results

* `IsLocalization.Away.of_surjective_of_mul_eq_zero`: a localization of `A` away from the image
  of `b` is a localization of `B` away from `b`.
* `IsLocalization.Away.quotient`: `S ⧸ I S` is a localization of `R ⧸ I` away from the image of
  `f` whenever `S` is a localization of `R` away from `f`.
* `TauCeti.exists_isPrime_comap_eq_of_bijective_quotientMap`: if `R → R'` induces an isomorphism
  `R ⧸ (f) ≃ R' ⧸ (f')`, then every prime of `R` comes from a prime of `R'` or of `R_f`.

## References

* [The Stacks Project, Section 15.92](https://stacks.math.columbia.edu/tag/0BNI), Lemma 15.92.3.
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

namespace TauCeti

/-- If `R → R'` induces an isomorphism `R ⧸ (f) ≃ R' ⧸ (f')`, then every prime ideal of `R` is the
contraction of a prime ideal of `R'` or of `R_f`: the maps `Spec R' → Spec R` and
`Spec R_f → Spec R` are jointly surjective (Stacks, Lemma 15.92.3). A prime containing `f` comes
from `R'` through the isomorphism, and a prime avoiding `f` comes from `R_f`. -/
theorem exists_isPrime_comap_eq_of_bijective_quotientMap {R R' R₂ : Type*} [CommRing R]
    [CommRing R'] [CommRing R₂] [Algebra R R'] [Algebra R R₂] {f : R} [IsLocalization.Away f R₂]
    {H : Ideal.span {f} ≤ (Ideal.span {algebraMap R R' f}).comap (algebraMap R R')}
    (hg : Function.Bijective (Ideal.quotientMap _ (algebraMap R R') H)) (p : Ideal R) [p.IsPrime] :
    (∃ P : Ideal R', P.IsPrime ∧ P.comap (algebraMap R R') = p) ∨
      ∃ P : Ideal R₂, P.IsPrime ∧ P.comap (algebraMap R R₂) = p := by
  by_cases hf : f ∈ p
  · left
    have hle : Ideal.span {f} ≤ p := by simpa [Ideal.span_le] using hf
    set g := Ideal.quotientMap _ (algebraMap R R') H
    have : (p.map (Ideal.Quotient.mk (Ideal.span {f}))).IsPrime :=
      Ideal.isPrime_map_quotientMk_of_isPrime hle
    have : ((p.map (Ideal.Quotient.mk _)).map g).IsPrime :=
      Ideal.map_isPrime_of_surjective hg.2 (by simp [(RingHom.injective_iff_ker_eq_bot g).mp hg.1])
    refine ⟨((p.map (Ideal.Quotient.mk _)).map g).comap (Ideal.Quotient.mk _), inferInstance, ?_⟩
    rw [Ideal.comap_comap, ← Ideal.quotientMap_comp_mk H, ← Ideal.comap_comap,
      Ideal.comap_map_of_bijective g hg, Ideal.comap_map_mk hle]
  · right
    have hd : Disjoint (Submonoid.powers f : Set R) p :=
      (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hf
    exact ⟨_, IsLocalization.isPrime_of_isPrime_disjoint _ R₂ p ‹_› hd,
      IsLocalization.under_map_of_isPrime_disjoint _ R₂ ‹_› hd⟩

end TauCeti
