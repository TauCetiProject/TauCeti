/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.RingTheory.LocalProperties.Basic
import TauCeti.RingTheory.Localization.Annihilator
import TauCeti.RingTheory.Localization.Ideal

/-!
# Locally principal ideals over semilocal rings

Over a commutative ring `B` with finitely many maximal ideals, Chinese remainder across the maximal
ideals promotes stalkwise principal ideals—and stalkwise annihilator equations—to a single global
generator `u ∈ B`, even when `B` has zero-divisors and is not Noetherian. This gives the algebraic
local-to-global input for affine schemes with semilocal coordinate rings (e.g. finite over local).

## Main results

* `Ideal.exists_eq_span_singleton_of_finite_maximalSpectrum`: over a semilocal ring, an ideal that
  is principal at every maximal ideal is principal.
* `Ideal.exists_eq_span_singleton_and_annihilator_of_finite_maximalSpectrum`: if also `J` is locally
  the annihilator of `I` at every maximal ideal, the generator `u` of `I` has annihilator `J`.

## References

* N. Bourbaki, *Commutative Algebra*, Chapter II, §5, no. 3, Proposition 5.
-/

public section

open Function

namespace Ideal

private lemma span_singleton_sum_eq_atPrime {B : Type*} [CommRing B] [Fintype (MaximalSpectrum B)]
    (a c : MaximalSpectrum B → B) (m : MaximalSpectrum B)
    (hdiv : ∀ j, algebraMap B (Localization.AtPrime m.asIdeal) (a j) ∈
      Ideal.span {algebraMap B (Localization.AtPrime m.asIdeal) (a m)})
    (hcm : c m - 1 ∈ m.asIdeal) (hcj : ∀ {j}, j ≠ m → c j ∈ m.asIdeal) :
    Ideal.span {algebraMap B (Localization.AtPrime m.asIdeal) (∑ j, c j * a j)} =
      Ideal.span {algebraMap B (Localization.AtPrime m.asIdeal) (a m)} := by
  classical
  have := m.isMaximal; choose q hq using fun j ↦ Ideal.mem_span_singleton.mp (hdiv j)
  let f := algebraMap B (Localization.AtPrime m.asIdeal)
  set v : Localization.AtPrime m.asIdeal := f (c m) + ∑ j ∈ Finset.univ.erase m, f (c j) * q j
  have hsum : f (∑ j, c j * a j) = v * f (a m) := by
    rw [map_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ m), map_mul, add_mul, Finset.sum_mul]
    exact congrArg (f (c m) * f (a m) + ·) <|
      Finset.sum_congr rfl fun j _ ↦ by rw [map_mul, hq j]; ring
  have hv : IsUnit v := by
    rw [← IsLocalRing.notMem_maximalIdeal]; intro hvm
    have hv1 : v - 1 = f (c m - 1) + ∑ j ∈ Finset.univ.erase m, f (c j) * q j := by
      simp [v, sub_eq_add_neg, add_right_comm]
    have hm1 : v - 1 ∈ IsLocalRing.maximalIdeal (Localization.AtPrime m.asIdeal) := by
      rw [hv1, ← Localization.AtPrime.map_eq_maximalIdeal]
      exact add_mem (Ideal.mem_map_of_mem _ hcm) (Submodule.sum_mem _ fun j hj ↦
        Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hcj (Finset.ne_of_mem_erase hj))))
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      (Ideal.eq_top_of_isUnit_mem _ (sub_sub_cancel v 1 ▸ sub_mem hvm hm1) isUnit_one)
  rw [hsum, Ideal.span_singleton_mul_left_unit hv]

/-- **Locally principal ideals over a semilocal ring are principal.** Any ideal `I` of `B` whose
extension to `Localization.AtPrime M` is principal for every maximal ideal `M` is principal. -/
theorem exists_eq_span_singleton_of_finite_maximalSpectrum {B : Type*} [CommRing B]
    [Finite (MaximalSpectrum B)] (I : Ideal B)
    (hI : ∀ (M : Ideal B) [M.IsMaximal], ∃ x : Localization.AtPrime M,
      I.map (algebraMap B (Localization.AtPrime M)) = Ideal.span {x}) :
    ∃ u : B, I = Ideal.span {u} := by
  classical
  have := Fintype.ofFinite (MaximalSpectrum B)
  choose a haI ha using fun m : MaximalSpectrum B ↦
    have := m.isMaximal; let ⟨x, hx⟩ := hI m.asIdeal
    I.exists_mem_map_eq_span_singleton m.asIdeal.primeCompl hx
  have hcop : Pairwise (IsCoprime on fun m : MaximalSpectrum B ↦ m.asIdeal) := fun m₁ m₂ hm ↦
    have := m₁.isMaximal; have := m₂.isMaximal
    Ideal.isCoprime_of_isMaximal fun heq ↦ hm (MaximalSpectrum.ext heq)
  choose c hc using fun i : MaximalSpectrum B ↦ Ideal.pi_quotient_surjective hcop (Pi.single i 1)
  refine ⟨∑ j : MaximalSpectrum B, c j * a j, Ideal.eq_of_localization_maximal fun M hM ↦ ?_⟩
  let m : MaximalSpectrum B := ⟨M, hM⟩; rw [Ideal.map_span, Set.image_singleton, ha m, eq_comm]
  refine span_singleton_sum_eq_atPrime a c m (fun j ↦ ha m ▸ Ideal.mem_map_of_mem _ (haI j)) ?_
    fun {j} hj ↦ ?_
  · have h := hc m m
    rwa [Pi.single_eq_same, ← map_one (Ideal.Quotient.mk m.asIdeal), Ideal.Quotient.eq] at h
  · have h := hc j m; rwa [Pi.single_eq_of_ne' hj, Ideal.Quotient.eq_zero_iff_mem] at h

/-- **Locally principal ideals and their annihilators over a semilocal ring.** If `I` is principal
and `J` agrees with `Ann(I)` at every maximal ideal of `B`, then `I = (u)` and `J = Ann(u)`. -/
theorem exists_eq_span_singleton_and_annihilator_of_finite_maximalSpectrum {B : Type*} [CommRing B]
    [Finite (MaximalSpectrum B)] (I J : Ideal B)
    (hIJ : ∀ (M : Ideal B) [M.IsMaximal], ∃ x : Localization.AtPrime M,
      I.map (algebraMap B (Localization.AtPrime M)) = Ideal.span {x} ∧
        J.map (algebraMap B (Localization.AtPrime M)) = (Ideal.span {x}).annihilator) :
    ∃ u : B, I = Ideal.span {u} ∧ J = (Ideal.span {u}).annihilator := by
  obtain ⟨u, rfl⟩ := I.exists_eq_span_singleton_of_finite_maximalSpectrum
    fun M _ ↦ let ⟨x, hx, _⟩ := hIJ M; ⟨x, hx⟩
  refine ⟨u, rfl, Ideal.eq_of_localization_maximal fun M hM ↦ ?_⟩
  obtain ⟨x, hx, hJ⟩ := hIJ M; rw [Ideal.map_span, Set.image_singleton] at hx
  rw [hJ, ← hx, IsLocalization.map_annihilator_span_singleton M.primeCompl]

end Ideal
