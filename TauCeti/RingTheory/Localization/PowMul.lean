/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Ideal

/-!
# Localization of power-twisted additive endomorphisms

An additive endomorphism `φ` satisfying `φ (a ^ n * b) = a * φ b` for a nonzero
exponent `n` localizes by `φ(a / s ^ n) = φ(a) / s`. The localized map satisfies the
same scalar identity, is determined by agreement on the base semiring, and preserves
extensions of ideals preserved by `φ`.
-/

public section

namespace IsLocalization

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  (M : Submonoid R) [IsLocalization M S] {n : ℕ} [NeZero n]

variable {M} in
private theorem mk'_eq_mk'_pow (a : R) (s : M) :
    IsLocalization.mk' S a s = IsLocalization.mk' S (a * (s : R) ^ (n - 1)) (s ^ n) := by
  simpa only [SubmonoidClass.coe_pow, mul_pow_sub_one (NeZero.ne n)] using
    (IsLocalization.mk'_cancel (S := S) a s (s ^ (n - 1))).symm

include M in
/-- A semiring homomorphism out of a localization intertwines two power-twisted maps
if it intertwines them on the image of the base semiring. -/
theorem map_apply_eq_of_map_pow_mul {T : Type*} [Semiring T]
    (f : S →+* T) {ψ : S → S} {χ : T → T}
    (hψ : ∀ x y, ψ (x ^ n * y) = x * ψ y) (hχ : ∀ x y, χ (x ^ n * y) = x * χ y)
    (h : ∀ a : R, f (ψ (algebraMap R S a)) = χ (f (algebraMap R S a))) (x : S) :
    f (ψ x) = χ (f x) := by
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
  rw [mk'_eq_mk'_pow (n := n) a s]
  generalize a * (s : R) ^ (n - 1) = b
  have he : algebraMap R S (s : R) ^ n * IsLocalization.mk' S b (s ^ n) =
      algebraMap R S b := by
    simpa only [SubmonoidClass.coe_pow, map_pow] using IsLocalization.mk'_spec' S b (s ^ n)
  apply ((IsLocalization.map_units S s).map f).mul_right_inj.mp
  rw [← map_mul f, ← hψ, ← hχ, ← map_pow f, ← map_mul f, he, h]

include M in
/-- Two power-twisted maps on a localization that agree on the base semiring are equal. -/
theorem eq_of_map_pow_mul {ψ χ : S → S}
    (hψ : ∀ x y, ψ (x ^ n * y) = x * ψ y) (hχ : ∀ x y, χ (x ^ n * y) = x * χ y)
    (h : ∀ a : R, ψ (algebraMap R S a) = χ (algebraMap R S a)) : ψ = χ :=
  funext (map_apply_eq_of_map_pow_mul M (RingHom.id S) hψ hχ h)

end IsLocalization

namespace AddMonoidHom

variable {R : Type*} [CommSemiring R] {n : ℕ} [NeZero n]
  (φ : R →+ R) (M : Submonoid R) (S : Type*) [CommSemiring S] [Algebra R S]
  [IsLocalization M S] (hφ : ∀ a b, φ (a ^ n * b) = a * φ b)

include M hφ in
private theorem map_apply_eq_of_algebraMap_eq {a b : R}
    (h : algebraMap R S a = algebraMap R S b) :
    algebraMap R S (φ a) = algebraMap R S (φ b) := by
  obtain ⟨s, hs⟩ := (IsLocalization.eq_iff_exists M S).mp h
  have he : (s : R) ^ n * a = (s : R) ^ n * b := by
    simpa only [← mul_assoc, pow_sub_one_mul (NeZero.ne n)] using
      congrArg ((s : R) ^ (n - 1) * ·) hs
  have he' := congrArg (algebraMap R S) (congrArg φ he)
  simp only [hφ, map_mul] at he'
  exact (IsLocalization.map_units S s).mul_right_inj.mp he'

include hφ in
private theorem fraction_eq_of_pow_fraction_eq {a b : R} {s t : M}
    (h : IsLocalization.mk' S a (s ^ n) = IsLocalization.mk' S b (t ^ n)) :
    IsLocalization.mk' S (φ a) s = IsLocalization.mk' S (φ b) t := by
  rw [IsLocalization.mk'_eq_iff_eq] at h ⊢
  simpa only [SubmonoidClass.coe_pow, hφ, map_mul] using
    φ.map_apply_eq_of_algebraMap_eq M S hφ h

private noncomputable def fractionMap (x : S) : S :=
  let q := IsLocalization.sec M x
  IsLocalization.mk' S (φ (q.1 * (q.2 : R) ^ (n - 1))) q.2

include hφ in
private theorem fractionMap_mk'_pow (a : R) (s : M) :
    φ.fractionMap M S (n := n) (IsLocalization.mk' S a (s ^ n)) =
      IsLocalization.mk' S (φ a) s := by
  unfold fractionMap
  apply φ.fraction_eq_of_pow_fraction_eq M S hφ
  exact (IsLocalization.mk'_eq_mk'_pow _ _).symm.trans (IsLocalization.mk'_sec S _)

include hφ in
private theorem fractionMap_add (x y : S) :
    φ.fractionMap M S (n := n) (x + y) =
      φ.fractionMap M S (n := n) x + φ.fractionMap M S (n := n) y := by
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
  obtain ⟨b, t, rfl⟩ := IsLocalization.exists_mk'_eq M y
  rw [IsLocalization.mk'_eq_mk'_pow (n := n) a s, IsLocalization.mk'_eq_mk'_pow (n := n) b t]
  generalize a * (s : R) ^ (n - 1) = c, b * (t : R) ^ (n - 1) = d
  rw [← IsLocalization.mk'_add, ← mul_pow, fractionMap_mk'_pow _ _ _ hφ,
    fractionMap_mk'_pow _ _ _ hφ, fractionMap_mk'_pow _ _ _ hφ, ← IsLocalization.mk'_add]
  congr 1
  simp only [map_add, SubmonoidClass.coe_pow, mul_comm c, mul_comm d, hφ]
  simp only [mul_comm]

/-- Localize an additive endomorphism satisfying `φ (a ^ n * b) = a * φ b`. -/
noncomputable def localizationOfPowMul : S →+ S where
  toFun := φ.fractionMap M S (n := n)
  map_zero' := by simpa using φ.fractionMap_mk'_pow M S hφ 0 1
  map_add' := φ.fractionMap_add M S hφ

-- Match the power before `SubmonoidClass.mk_pow` can rewrite it to a subtype constructor.
/-- The localized map removes an `n`-th power from the denominator. -/
@[simp↓]
theorem localizationOfPowMul_mk'_pow (a : R) (s : M) :
    φ.localizationOfPowMul M S hφ (IsLocalization.mk' S a (s ^ n)) =
      IsLocalization.mk' S (φ a) s :=
  φ.fractionMap_mk'_pow M S hφ a s

/-- The localized map agrees with the original map on the base semiring. -/
@[simp]
theorem localizationOfPowMul_algebraMap (a : R) :
    φ.localizationOfPowMul M S hφ (algebraMap R S a) = algebraMap R S (φ a) := by
  simpa only [one_pow, IsLocalization.mk'_one] using φ.localizationOfPowMul_mk'_pow M S hφ a 1

/-- The value of the localized map on a fraction with an arbitrary denominator. -/
theorem localizationOfPowMul_mk' (a : R) (s : M) :
    φ.localizationOfPowMul M S hφ (IsLocalization.mk' S a s) =
      IsLocalization.mk' S (φ (a * (s : R) ^ (n - 1))) s := by
  rw [IsLocalization.mk'_eq_mk'_pow (n := n) a s, localizationOfPowMul_mk'_pow]

/-- Localization preserves the power-twisted scalar identity. -/
theorem localizationOfPowMul_pow_mul (x y : S) :
    φ.localizationOfPowMul M S hφ (x ^ n * y) = x * φ.localizationOfPowMul M S hφ y := by
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
  obtain ⟨b, t, rfl⟩ := IsLocalization.exists_mk'_eq M y
  rw [IsLocalization.mk'_eq_mk'_pow (n := n) b t]
  generalize b * (t : R) ^ (n - 1) = c
  rw [← IsLocalization.mk'_pow, ← IsLocalization.mk'_mul, ← mul_pow,
    localizationOfPowMul_mk'_pow, localizationOfPowMul_mk'_pow, hφ, IsLocalization.mk'_mul]

/-- Two-stage localization agrees with direct localization of the same power-twisted map. -/
theorem localizationOfPowMul_localizationOfPowMul (N : Submonoid S) (L : Submonoid R)
    (T : Type*) [CommSemiring T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [IsLocalization N T] [IsLocalization L T] :
    (φ.localizationOfPowMul M S hφ).localizationOfPowMul N T
        (φ.localizationOfPowMul_pow_mul M S hφ) = φ.localizationOfPowMul L T hφ := by
  apply DFunLike.coe_injective
  refine IsLocalization.eq_of_map_pow_mul L
    (localizationOfPowMul_pow_mul _ _ _ _) (localizationOfPowMul_pow_mul _ _ _ _) fun a ↦ ?_
  rw [φ.localizationOfPowMul_algebraMap L T hφ, IsScalarTower.algebraMap_apply R S T,
    localizationOfPowMul_algebraMap, localizationOfPowMul_algebraMap,
    ← IsScalarTower.algebraMap_apply R S T]

/-- The extension of an invariant ideal is invariant under the localized map. -/
theorem localizationOfPowMul_mem_map {I : Ideal R} (hI : ∀ a ∈ I, φ a ∈ I) {x : S}
    (hx : x ∈ I.map (algebraMap R S)) :
    φ.localizationOfPowMul M S hφ x ∈ I.map (algebraMap R S) := by
  obtain ⟨⟨a, s⟩, hs⟩ := (IsLocalization.mem_map_algebraMap_iff M S).mp hx
  rw [IsLocalization.eq_mk'_iff_mul_eq.mpr hs, localizationOfPowMul_mk']
  exact IsLocalization.mk'_mem_iff.mpr
    (Ideal.mem_map_of_mem _ (hI _ (I.mul_mem_right _ a.prop)))

/-- A localized ideal is invariant under the localized map if and only if its contraction
is invariant under the original map. -/
theorem localizationOfPowMul_mem_iff (J : Ideal S) :
    (∀ x ∈ J, φ.localizationOfPowMul M S hφ x ∈ J) ↔
      ∀ a ∈ J.comap (algebraMap R S), φ a ∈ J.comap (algebraMap R S) := by
  constructor
  · intro h a ha
    simpa only [Ideal.mem_comap, localizationOfPowMul_algebraMap] using
      h (algebraMap R S a) (Ideal.mem_comap.mp ha)
  · intro h x hx
    rw [← IsLocalization.map_under M S J] at hx ⊢
    exact φ.localizationOfPowMul_mem_map M S hφ h hx

end AddMonoidHom
