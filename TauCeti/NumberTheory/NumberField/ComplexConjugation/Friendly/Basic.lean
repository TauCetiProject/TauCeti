/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import TauCeti.NumberTheory.NumberField.ComplexConjugation.MaximalRealOrCMSubfield
public import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
public import TauCeti.NumberTheory.NumberField.RingOfIntegers.Basic
public import TauCeti.NumberTheory.RamificationInertia.Tower
public import TauCeti.RingTheory.RamificationInertia.Bijective

/-!
# Friendly places

Let `K` be a number field, `E_K` its largest totally real or CM subfield
(`TauCeti.NumberField.maximalRealOrCMSubfield K`) and `K⁺` its maximal real subfield, which is
also the maximal real subfield of `E_K`. A finite place `v` of `K` is **friendly** when it is
unramified over `ℚ` and, if `E_K` is CM, the place of `K⁺` below `v` is inert in the quadratic
extension `E_K / K⁺` (Lawrence–Venkatesh, §2.4, Definition 2.7).

Since `[E_K : K⁺] = 2`, the place `w` of `K⁺` below `v` is inert in `E_K` exactly when the place
`u` of `E_K` below `v` has inertia degree `2` over `w`. By multiplicativity of inertia degrees in
the tower `ℤ ⊆ 𝓞 K⁺ ⊆ 𝓞 E_K`, this is `f(u | ℤ) = 2 f(w | ℤ)`, which is the form used in the
definition: it only needs the rings of integers of `E_K` and `K⁺` as algebras under `𝓞 K`.
Unramified over `ℚ` means ramification index `1` over `ℤ`.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.IsFriendly v`: the finite place `v` of `K` is friendly.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.IsFriendly.ramificationIdx_eq_one`: a friendly place is
  unramified over `ℚ`.
* `IsDedekindDomain.HeightOneSpectrum.isFriendly_iff_of_not_isCMField`,
  `IsDedekindDomain.HeightOneSpectrum.isFriendly_iff_of_forall_not_isCMField`: if `K` has no CM
  subfield, a place is friendly exactly when it is unramified over `ℚ`.
* `IsDedekindDomain.HeightOneSpectrum.isFriendly_iff_of_isTotallyReal`: in particular for totally
  real `K`.
* `IsDedekindDomain.HeightOneSpectrum.isFriendly_iff_of_odd_finrank`: in a field of odd degree,
  for instance `ℚ(2^(1/3))`, a place is friendly exactly when it is unramified over `ℚ`.
* `IsDedekindDomain.HeightOneSpectrum.isFriendly_rat`: every prime of `ℚ` is friendly.
* `IsDedekindDomain.HeightOneSpectrum.isFriendly_iff_inertiaDeg_eq_two`: in an imaginary quadratic
  field a place is friendly exactly when it is inert over `ℚ`.
* `IsDedekindDomain.HeightOneSpectrum.isFriendly_iff_mod_four_eq_three`: over `ℚ(i)`, a place is
  friendly exactly when it lies above a prime `p ≡ 3 mod 4`.

## References

* B. Lawrence and A. Venkatesh, *Diophantine problems and p-adic period mappings*, §2.4,
  Definition 2.7.
-/

public section

open NumberField TauCeti.NumberField

namespace IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K] [NumberField K]

/-- A finite place `v` of a number field `K` is **friendly** if it is unramified over `ℚ` and,
when the largest totally real or CM subfield `E_K` is CM, the place of the maximal real subfield
`K⁺` below `v` is inert in `E_K`. Inertness is expressed by inertia degrees over `ℤ`: the place
of `E_K` below `v` has twice the inertia degree of the place of `K⁺` below `v`, which says that
its relative inertia degree over `K⁺` is `[E_K : K⁺] = 2`. -/
def IsFriendly (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  v.asIdeal.ramificationIdx ℤ = 1 ∧
    (IsCMField (maximalRealOrCMSubfield K) →
      (v.asIdeal.under (𝓞 (maximalRealOrCMSubfield K))).inertiaDeg ℤ =
        2 * (v.asIdeal.under (𝓞 (maximalRealSubfield K))).inertiaDeg ℤ)

/-- Unfolding lemma for `IsFriendly`. -/
theorem isFriendly_iff (v : HeightOneSpectrum (𝓞 K)) :
    IsFriendly v ↔ v.asIdeal.ramificationIdx ℤ = 1 ∧
      (IsCMField (maximalRealOrCMSubfield K) →
        (v.asIdeal.under (𝓞 (maximalRealOrCMSubfield K))).inertiaDeg ℤ =
          2 * (v.asIdeal.under (𝓞 (maximalRealSubfield K))).inertiaDeg ℤ) :=
  Iff.rfl

/-- A friendly place is unramified over `ℚ`. -/
theorem IsFriendly.ramificationIdx_eq_one {v : HeightOneSpectrum (𝓞 K)} (h : IsFriendly v) :
    v.asIdeal.ramificationIdx ℤ = 1 :=
  h.1

/-- If `E_K` is CM, a friendly place lies over a place of `K⁺` inert in `E_K`, in the form of
inertia degrees over `ℤ`. -/
theorem IsFriendly.inertiaDeg_eq {v : HeightOneSpectrum (𝓞 K)} (h : IsFriendly v)
    (hK : IsCMField (maximalRealOrCMSubfield K)) :
    (v.asIdeal.under (𝓞 (maximalRealOrCMSubfield K))).inertiaDeg ℤ =
      2 * (v.asIdeal.under (𝓞 (maximalRealSubfield K))).inertiaDeg ℤ :=
  h.2 hK

/-- If `E_K` is not CM, a place is friendly exactly when it is unramified over `ℚ`. -/
theorem isFriendly_iff_of_not_isCMField (hK : ¬IsCMField (maximalRealOrCMSubfield K))
    (v : HeightOneSpectrum (𝓞 K)) : IsFriendly v ↔ v.asIdeal.ramificationIdx ℤ = 1 :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun h' ↦ (hK h').elim⟩⟩

/-- **Fields without CM subfields.** If `K` has no CM subfield, a place of `K` is friendly
exactly when it is unramified over `ℚ`. -/
theorem isFriendly_iff_of_forall_not_isCMField (hK : ∀ F : Subfield K, ¬IsCMField F)
    (v : HeightOneSpectrum (𝓞 K)) : IsFriendly v ↔ v.asIdeal.ramificationIdx ℤ = 1 :=
  isFriendly_iff_of_not_isCMField (fun h ↦ hK _ h) v

/-- In a totally real field `E_K = K⁺ = K` is not CM, so a place is friendly exactly when it is
unramified over `ℚ`. -/
theorem isFriendly_iff_of_isTotallyReal [IsTotallyReal K] (v : HeightOneSpectrum (𝓞 K)) :
    IsFriendly v ↔ v.asIdeal.ramificationIdx ℤ = 1 := by
  refine isFriendly_iff_of_not_isCMField (fun h ↦ ?_) v
  rw [isCMField_maximalRealOrCMSubfield_iff_ne_maximalRealSubfield,
    IsTotallyReal.maximalRealSubfield_eq_top] at h
  exact h maximalRealOrCMSubfield_eq_top_of_isTotallyReal

/-- **Fields of odd degree.** A number field of odd degree over `ℚ` has no CM subfield, so a place
is friendly exactly when it is unramified over `ℚ`. -/
theorem isFriendly_iff_of_odd_finrank (h : Odd (Module.finrank ℚ K))
    (v : HeightOneSpectrum (𝓞 K)) : IsFriendly v ↔ v.asIdeal.ramificationIdx ℤ = 1 :=
  isFriendly_iff_of_not_isCMField (fun hK ↦
    isCMField_maximalRealOrCMSubfield_iff_ne_maximalRealSubfield.mp hK
      (maximalRealOrCMSubfield_eq_maximalRealSubfield_of_odd h)) v

/-- **Every prime of `ℚ` is friendly.** -/
@[simp]
theorem isFriendly_rat (v : HeightOneSpectrum (𝓞 ℚ)) : IsFriendly v := by
  rw [isFriendly_iff_of_isTotallyReal]
  exact Ideal.ramificationIdx_eq_one v.asIdeal ℤ

/-- **Imaginary quadratic fields.** If `K` is CM of degree `2` over `ℚ`, then `E_K = K` and
`K⁺ = ℚ`, so a place of `K` is friendly exactly when it has inertia degree `2` over `ℚ`, that is,
when it is inert over `ℚ` (inertia degree `2` forces ramification index `1`). -/
theorem isFriendly_iff_inertiaDeg_eq_two [IsCMField K] (hK : Module.finrank ℚ K = 2)
    (v : HeightOneSpectrum (𝓞 K)) : IsFriendly v ↔ v.asIdeal.inertiaDeg ℤ = 2 := by
  have hKp : Module.finrank ℚ (maximalRealSubfield K) = 1 := by
    have h := Module.finrank_mul_finrank ℚ (maximalRealSubfield K) K
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield K) K, hK] at h
    omega
  -- The place of `K⁺ = ℚ` below `v` has inertia degree `1`.
  have hw : (v.asIdeal.under (𝓞 (maximalRealSubfield K))).inertiaDeg ℤ = 1 := by
    have h := TauCeti.RamificationInertia.inertiaDeg_le_finrank ℤ
      (v.asIdeal.under (𝓞 (maximalRealSubfield K)))
    rw [RingOfIntegers.rank, hKp] at h
    exact le_antisymm h (Ideal.inertiaDeg_pos _ ℤ)
  -- `e f ≤ [K : ℚ] = 2` at `v`.
  have hv : v.asIdeal.ramificationIdx ℤ * v.asIdeal.inertiaDeg ℤ ≤ 2 := by
    have h := TauCeti.RamificationInertia.ramificationIdx_mul_inertiaDeg_le_finrank ℤ v.asIdeal
    rwa [RingOfIntegers.rank, hK] at h
  have hv₀ := v.asIdeal.ramificationIdx_pos ℤ
  -- `E_K = K`, so the place of `E_K` below `v` has the inertia degree of `v`.
  have huv : v.asIdeal.inertiaDeg ℤ =
      (v.asIdeal.under (𝓞 (maximalRealOrCMSubfield K))).inertiaDeg ℤ := by
    rw [Ideal.inertiaDeg_tower (v.asIdeal.under (𝓞 (maximalRealOrCMSubfield K))) v.asIdeal,
      Ideal.inertiaDeg_eq_one_of_surjective (RingOfIntegers.algebraMap_surjective_of_eq_top
        maximalRealOrCMSubfield_eq_top_of_isCMField) v.asIdeal, mul_one]
  rw [isFriendly_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨?_, fun _ ↦ ?_⟩⟩
  · have := h.2 inferInstance
    omega
  · rw [h] at hv
    omega
  · omega

/-- **`ℚ(i)`: a place is friendly exactly when it lies above a prime `p ≡ 3 mod 4`.** Here `ℚ(i)`
is any `4`-th cyclotomic extension of `ℚ`. It is imaginary quadratic, so friendly places are the
places inert over `ℚ` (`isFriendly_iff_inertiaDeg_eq_two`); the place above `2` has inertia
degree `1`, and for odd `p` the inertia degree is the order of `p` modulo `4`. -/
theorem isFriendly_iff_mod_four_eq_three [IsCyclotomicExtension {4} ℚ K]
    (v : HeightOneSpectrum (𝓞 K)) (p : ℕ) [hp : Fact p.Prime]
    [v.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] : IsFriendly v ↔ p % 4 = 3 := by
  have : IsCMField K := IsCyclotomicExtension.Rat.isCMField K (S := {4}) ⟨4, rfl, by norm_num⟩
  have hK : Module.finrank ℚ K = 2 := by
    rw [IsCyclotomicExtension.Rat.finrank 4 K]
    decide
  rw [isFriendly_iff_inertiaDeg_eq_two hK]
  rcases hp.out.eq_two_or_odd' with rfl | hodd
  · rw [IsCyclotomicExtension.Rat.inertiaDeg_eq 4 K v.asIdeal (p := 2) (k := 1) (m := 1)
      rfl (by decide), orderOf_eq_one_iff.mpr (Subsingleton.elim _ _)]
    decide
  · -- An odd prime divisor of `4` would lie in `[2, 4]`, and none there is odd and divides `4`.
    have h4 : ¬p ∣ 4 := fun h ↦ by
      have := Nat.le_of_dvd (by norm_num) h
      have := hp.out.two_le
      have := Nat.odd_iff.mp hodd
      interval_cases p <;> omega
    rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd p K v.asIdeal h4, ← ZMod.natCast_mod]
    have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by
      rcases hodd with ⟨k, rfl⟩
      omega
    rcases hp4 with h | h <;> rw [h]
    · simp
    · simp only [Nat.cast_ofNat, iff_true]
      exact orderOf_eq_prime (by decide) (by decide)

end IsDedekindDomain.HeightOneSpectrum
