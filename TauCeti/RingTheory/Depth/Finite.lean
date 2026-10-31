/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Regular.RegularSequence
import TauCeti.RingTheory.Ideal.GoingUp

/-!
# Depth along a finite ring map

Let `R` be a Noetherian local ring with maximal ideal `𝔪`, let `S` be a finite `R`-algebra and let
`N` be a finite `S`-module. The depth of `N` as an `R`-module, that is its `𝔪`-depth, is the
minimum of the depths of the localizations `N_𝔫` over the maximal ideals `𝔫` of `S` (Stacks,
Lemma 10.72.11 (0AUK)). So a lower bound on the depth over the local ring `R` is the same as the
same lower bound at every closed point of the semi-local scheme `Spec S`. For instance, if `R`
has depth at least two and `S` is free over `R`, then every localization of `S` at a maximal ideal
has depth at least two.

## Main results

* `IsLocalRing.depth_eq_zero_iff_exists_isMaximal`: `N` has depth zero over `R` if and only if some
  localization `N_𝔫` at a maximal ideal of `S` has depth zero; this holds for every `S`-module `N`.
* `IsLocalRing.le_depth_iff_forall_isMaximal`: `n ≤ depth N` over `R` if and only if
  `n ≤ depth N_𝔫` for every maximal ideal `𝔫` of `S`.
* `IsLocalRing.depth_eq_iInf_localization_maximal`: the depth of `N` over `R` is the infimum of
  the depths of the localizations `N_𝔫` (Stacks, Lemma 10.72.11 (0AUK)).

## Proof

The maximal ideals of `S` are the primes lying over `𝔪`, because `S` is integral over `R`. So `𝔪`
is an associated prime of `N` over `R` if and only if some maximal ideal of `S` is an associated
prime of `N` over `S`, which gives the case of depth zero. Otherwise some `x ∈ 𝔪` is `N`-regular,
and dividing by `x` lowers both the depth over `R` and every depth `depth N_𝔫` by exactly one,
which gives the general case by induction.

## References

* [Stacks Project, Lemma 10.72.11](https://stacks.math.columbia.edu/tag/0AUK)
-/

public section

universe u v w

open IsLocalRing Pointwise

namespace IsLocalRing

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
  [Module.Finite R S]

variable [IsNoetherianRing R] [Small.{w} R] {N : Type w} [AddCommGroup N] [Module R N] [Module S N]
  [IsScalarTower R S N]

/-- Let `S` be a finite algebra over a Noetherian local ring `R` and `N` an `S`-module. Then `N`
has depth zero over `R` if and only if its localization at some maximal ideal of `S` has depth
zero. -/
theorem depth_eq_zero_iff_exists_isMaximal :
    depth (ModuleCat.of R N) = 0 ↔ ∃ (𝔫 : Ideal S) (_ : 𝔫.IsMaximal),
      depth (ModuleCat.of (Localization.AtPrime 𝔫) (LocalizedModule 𝔫.primeCompl N)) = 0 := by
  have : IsNoetherianRing S := .of_finite R S
  rw [depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes]
  refine ⟨fun h ↦ ?_, fun ⟨𝔫, _, h𝔫⟩ ↦ ?_⟩
  · obtain ⟨𝔫, h𝔫, hcomap⟩ := IsAssociatedPrime.exists_isAssociatedPrime_comap_eq (S := S) h
    have := h𝔫.isPrime
    -- `𝔫` lies over the maximal ideal of `R`, so it is maximal since `S` is integral over `R`.
    have : 𝔫.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) 𝔫
      (by rw [Ideal.under_def, hcomap]; exact maximalIdeal.isMaximal R)
    exact ⟨𝔫, this, TauCeti.depth_localizedModule_eq_zero_iff.2 h𝔫⟩
  · have hass := (TauCeti.depth_localizedModule_eq_zero_iff (M := N)).1 h𝔫
    exact Ideal.comap_eq_maximalIdeal_of_isIntegral (R := R) 𝔫 ▸ IsAssociatedPrime.comap hass

variable [Module.Finite S N]

/-- The localizations `N_𝔫` at maximal ideals, for a finite `S`-module `N`, and the `R`-module `N`
satisfy the same lower bounds `n ≤ depth` for natural numbers `n`. -/
private theorem natCast_le_depth_iff (n : ℕ) :
    (n : ℕ∞) ≤ depth (ModuleCat.of R N) ↔ ∀ (𝔫 : Ideal S) [𝔫.IsMaximal],
      (n : ℕ∞) ≤ depth (ModuleCat.of (Localization.AtPrime 𝔫)
        (LocalizedModule 𝔫.primeCompl N)) := by
  induction n generalizing N with
  | zero => simp
  | succ n ih =>
    have : IsNoetherianRing S := .of_finite R S
    have : Module.Finite R N := .trans S N
    by_cases h0 : depth (ModuleCat.of R N) = 0
    · -- Both sides fail: some localization at a maximal ideal has depth zero too.
      obtain ⟨𝔫, _, h𝔫⟩ := depth_eq_zero_iff_exists_isMaximal (S := S).1 h0
      rw [h0]
      exact ⟨fun h ↦ absurd h (by simp), fun h ↦ absurd (h𝔫 ▸ h 𝔫) (by simp)⟩
    -- Otherwise the maximal ideal of `R` contains an `N`-regular element `x`.
    obtain ⟨x, hx, reg⟩ := ((maximalIdeal R).exists_mem_isSMulRegular_iff (M := N)).2
      fun p hp hle ↦ h0 <| depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes.2 <|
        le_antisymm (le_maximalIdeal hp.isPrime.ne_top) hle ▸ hp
    let y := algebraMap R S x
    have regS : IsSMulRegular N y := fun a b hab ↦ reg (by simpa [y] using hab)
    -- Dividing by `x` over `R` and by its image `y` over `S` give the same `R`-module.
    have hquot : x • (⊤ : Submodule R N) = (y • (⊤ : Submodule S N)).restrictScalars R := by
      ext z
      simp [y, Submodule.mem_smul_pointwise_iff_exists]
    let e : QuotSMulTop x N ≃ₗ[R] QuotSMulTop y N :=
      Submodule.quotEquivOfEq _ _ hquot ≪≫ₗ Submodule.Quotient.restrictScalarsEquiv R _
    -- Both depths drop by exactly one, so the bound `n + 1` becomes the bound `n` on `N ⧸ y N`.
    have hR := depth_quotSMulTop_succ_eq_depth reg hx
    rw [depth_eq_of_linearEquiv e] at hR
    rw [← hR, Nat.cast_succ, ENat.add_le_add_iff_right ENat.one_ne_top,
      @ih (QuotSMulTop y N) _ _ _ _ _]
    refine forall_congr' fun 𝔫 ↦ forall_congr' fun _ ↦ ?_
    have hy : y ∈ 𝔫 := by
      rw [← Ideal.mem_comap, Ideal.comap_eq_maximalIdeal_of_isIntegral]
      exact hx
    rw [← TauCeti.depth_localizedModule_quotSMulTop_add_one regS 𝔫 hy,
      ENat.add_le_add_iff_right ENat.one_ne_top]

/-- Let `S` be a finite algebra over a Noetherian local ring `R` and `N` a finite `S`-module. A
lower bound holds for the depth of `N` over `R` if and only if it holds for the depth of the
localization of `N` at every maximal ideal of `S`. -/
theorem le_depth_iff_forall_isMaximal (n : ℕ∞) :
    n ≤ depth (ModuleCat.of R N) ↔ ∀ (𝔫 : Ideal S) [𝔫.IsMaximal],
      n ≤ depth (ModuleCat.of (Localization.AtPrime 𝔫) (LocalizedModule 𝔫.primeCompl N)) := by
  refine ⟨fun h 𝔫 _ ↦ ENat.forall_natCast_le_iff_le.1 fun k hk ↦
    (natCast_le_depth_iff k).1 (hk.trans h) 𝔫, fun h ↦ ENat.forall_natCast_le_iff_le.1 fun k hk ↦
      (natCast_le_depth_iff k).2 fun 𝔫 _ ↦ hk.trans (h 𝔫)⟩

/-- **Depth along a finite ring map.** Let `S` be a finite algebra over a Noetherian local ring
`R` and `N` a finite `S`-module. The depth of `N` as an `R`-module is the infimum of the depths of
its localizations at the maximal ideals of `S`. -/
@[stacks 0AUK]
theorem depth_eq_iInf_localization_maximal :
    depth (ModuleCat.of R N) = ⨅ 𝔫 : MaximalSpectrum S,
      depth (ModuleCat.of (Localization.AtPrime 𝔫.asIdeal)
        (LocalizedModule 𝔫.asIdeal.primeCompl N)) :=
  eq_of_forall_le_iff fun n ↦ by
    rw [le_depth_iff_forall_isMaximal (S := S), le_iInf_iff]
    exact ⟨fun h 𝔫 ↦ h 𝔫.asIdeal, fun h 𝔫 _ ↦ h ⟨𝔫, ‹_›⟩⟩

end IsLocalRing
