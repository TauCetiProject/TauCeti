/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.RingTheory.LocalProperties.Basic
import TauCeti.RingTheory.Localization.Annihilator
import TauCeti.RingTheory.Localization.Ideal

/-!
# Locally principal ideals over semilocal rings

On an affine scheme `Z = V(I * J)` finite over `Spec R` with `R` local, an effective Cartier
divisor `I` and a residual ideal sheaf `J` satisfy stalkwise equations `I_z = (a_z)` and
`J_z = Ann(a_z)` inside a coordinate ring `B = Γ(Z, ⊤)` that may contain zero-divisors and need not
be Noetherian. Because `B` is finite over the local ring `R`, `B` is semilocal, and semilocality
promotes these stalkwise equations to a single global element `u ∈ B` with `I = (u)` and
`J = Ann(u)` — the algebraic input for splitting off one section at a time in Katz–Mazur 1.8.3.

## Main results

* `TauCeti.finite_maximalSpectrum_of_isIntegral_of_quasiFinite`: an integral quasi-finite algebra
  over a ring with finitely many maximal ideals has finitely many maximal ideals.
* `Ideal.exists_eq_span_singleton_of_finite_maximalSpectrum`: over a commutative ring with finitely
  many maximal ideals, an ideal that is principal at every maximal ideal is principal.
* `Ideal.exists_eq_span_singleton_and_annihilator_of_finite_maximalSpectrum`: if in addition `J` is
  locally the annihilator of `I` at every maximal ideal, the generator `u` of `I` has annihilator
  `J`.

## References

* N. Bourbaki, *Commutative Algebra*, Chapter II, §5, no. 3, Proposition 5.
-/

public section

open Function

namespace TauCeti

/-- **An integral quasi-finite algebra over a semilocal ring is semilocal**: if `R` has finitely
many maximal ideals and `B` is an integral quasi-finite `R`-algebra (in particular, a module-finite
`R`-algebra), then `B` has finitely many maximal ideals. -/
theorem finite_maximalSpectrum_of_isIntegral_of_quasiFinite (R : Type*) {B : Type*} [CommRing R]
    [Finite (MaximalSpectrum R)] [CommRing B] [Algebra R B] [Algebra.IsIntegral R B]
    [Algebra.QuasiFinite R B] : Finite (MaximalSpectrum B) := by
  -- Every maximal ideal `M` of `B` contracts to a maximal ideal of `R` by integrality, and each
  -- maximal ideal of `R` has only finitely many primes of `B` lying over it by quasi-finiteness.
  have : ∀ m : MaximalSpectrum R, Finite (m.asIdeal.primesOver B) :=
    fun m ↦ (Algebra.QuasiFinite.finite_primesOver m.asIdeal (S := B)).to_subtype
  refine Finite.of_injective (β := (m : MaximalSpectrum R) × m.asIdeal.primesOver B)
    (fun M ↦
      have := M.isMaximal
      ⟨⟨M.asIdeal.under R, inferInstance⟩, ⟨M.asIdeal, M.isMaximal.isPrime, ⟨rfl⟩⟩⟩)
    fun M₁ M₂ h ↦ MaximalSpectrum.ext (congrArg (fun x ↦ x.2.1) h)

end TauCeti

namespace Ideal

private lemma span_singleton_sum_eq_atPrime {B : Type*} [CommRing B] [Fintype (MaximalSpectrum B)]
    (a c : MaximalSpectrum B → B) (m : MaximalSpectrum B)
    (hdiv : ∀ j, algebraMap B (Localization.AtPrime m.asIdeal) (a j) ∈
      Ideal.span {algebraMap B (Localization.AtPrime m.asIdeal) (a m)})
    (hcm : c m - 1 ∈ m.asIdeal) (hcj : ∀ {j}, j ≠ m → c j ∈ m.asIdeal) :
    Ideal.span {algebraMap B (Localization.AtPrime m.asIdeal) (∑ j, c j * a j)} =
      Ideal.span {algebraMap B (Localization.AtPrime m.asIdeal) (a m)} := by
  classical
  have := m.isMaximal
  choose q hq using fun j ↦ Ideal.mem_span_singleton.mp (hdiv j)
  let f := algebraMap B (Localization.AtPrime m.asIdeal)
  set v : Localization.AtPrime m.asIdeal := f (c m) + ∑ j ∈ Finset.univ.erase m, f (c j) * q j
  have hsum : f (∑ j, c j * a j) = v * f (a m) := by
    rw [map_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ m), map_mul, add_mul, Finset.sum_mul]
    exact congrArg (f (c m) * f (a m) + ·)
      (Finset.sum_congr rfl fun j _ ↦ by rw [map_mul, hq j]; ring)
  have hv : IsUnit v := by
    rw [← IsLocalRing.notMem_maximalIdeal]; intro hvm
    have hm1 : v - 1 ∈ IsLocalRing.maximalIdeal (Localization.AtPrime m.asIdeal) := by
      rw [show v - 1 = f (c m - 1) + ∑ j ∈ Finset.univ.erase m, f (c j) * q j by
        simp [v, sub_eq_add_neg, add_right_comm], ← Localization.AtPrime.map_eq_maximalIdeal]
      exact add_mem (Ideal.mem_map_of_mem _ hcm) (Submodule.sum_mem _ fun j hj ↦
        Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hcj (Finset.ne_of_mem_erase hj))))
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      (Ideal.eq_top_of_isUnit_mem _ (sub_sub_cancel v 1 ▸ sub_mem hvm hm1) isUnit_one)
  rw [hsum, Ideal.span_singleton_mul_left_unit hv]

/-- **Locally principal ideals over a semilocal ring are principal.** Let `B` be a commutative ring
with finitely many maximal ideals. Any ideal `I` of `B` whose extension to `Localization.AtPrime M`
is principal for every maximal ideal `M` of `B` is generated by a single element. -/
theorem exists_eq_span_singleton_of_finite_maximalSpectrum {B : Type*} [CommRing B]
    [Finite (MaximalSpectrum B)] (I : Ideal B)
    (hI : ∀ (M : Ideal B) [M.IsMaximal], ∃ x : Localization.AtPrime M,
      I.map (algebraMap B (Localization.AtPrime M)) = Ideal.span {x}) :
    ∃ u : B, I = Ideal.span {u} := by
  classical
  have := Fintype.ofFinite (MaximalSpectrum B)
  choose a haI ha using fun m : MaximalSpectrum B ↦
    have := m.isMaximal
    let ⟨x, hx⟩ := hI m.asIdeal
    I.exists_mem_map_eq_span_singleton m.asIdeal.primeCompl hx
  have hcop : Pairwise (IsCoprime on fun m : MaximalSpectrum B ↦ m.asIdeal) := fun m₁ m₂ hm ↦
    have := m₁.isMaximal; have := m₂.isMaximal
    Ideal.isCoprime_of_isMaximal fun heq ↦ hm (MaximalSpectrum.ext heq)
  choose c hc using fun i : MaximalSpectrum B ↦
    Ideal.pi_quotient_surjective hcop (Pi.single i 1)
  refine ⟨∑ j : MaximalSpectrum B, c j * a j, Ideal.eq_of_localization_maximal fun M hM ↦ ?_⟩
  let m : MaximalSpectrum B := ⟨M, hM⟩
  rw [Ideal.map_span, Set.image_singleton, ha m, eq_comm]
  refine span_singleton_sum_eq_atPrime a c m (fun j ↦ ha m ▸ Ideal.mem_map_of_mem _ (haI j)) ?_
    fun {j} hj ↦ ?_
  · have h := hc m m
    rwa [Pi.single_eq_same, ← map_one (Ideal.Quotient.mk m.asIdeal), Ideal.Quotient.eq] at h
  · have h := hc j m
    rwa [Pi.single_eq_of_ne' hj, Ideal.Quotient.eq_zero_iff_mem] at h

/-- **Locally principal ideals and their annihilators over a semilocal ring.** If `B` has finitely
many maximal ideals, `I` is principal at every maximal ideal of `B`, and `J` agrees with the
annihilator of `I` at every maximal ideal of `B`, then `I = (u)` and `J = Ann(u)` for a single
element `u ∈ B`. -/
theorem exists_eq_span_singleton_and_annihilator_of_finite_maximalSpectrum {B : Type*} [CommRing B]
    [Finite (MaximalSpectrum B)] (I J : Ideal B)
    (hIJ : ∀ (M : Ideal B) [M.IsMaximal], ∃ x : Localization.AtPrime M,
      I.map (algebraMap B (Localization.AtPrime M)) = Ideal.span {x} ∧
        J.map (algebraMap B (Localization.AtPrime M)) = (Ideal.span {x}).annihilator) :
    ∃ u : B, I = Ideal.span {u} ∧ J = (Ideal.span {u}).annihilator := by
  obtain ⟨u, rfl⟩ := I.exists_eq_span_singleton_of_finite_maximalSpectrum
    fun M _ ↦ let ⟨x, hx, _⟩ := hIJ M; ⟨x, hx⟩
  refine ⟨u, rfl, Ideal.eq_of_localization_maximal fun M hM ↦ ?_⟩
  obtain ⟨x, hx, hJ⟩ := hIJ M
  rw [Ideal.map_span, Set.image_singleton] at hx
  rw [hJ, ← hx, IsLocalization.map_annihilator_span_singleton M.primeCompl]

end Ideal
