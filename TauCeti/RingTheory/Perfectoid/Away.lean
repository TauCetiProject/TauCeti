/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Away
public import TauCeti.RingTheory.Perfectoid.Basic
public import TauCeti.RingTheory.Perfectoid.Untilt

import TauCeti.Algebra.Ring.NonZeroDivisors

/-!
# Perfectoid Tate rings from integral perfectoid rings

Let `p` be a prime and `A₀` a commutative ring with a nonzerodivisor `π ∈ A₀` such that `π ^ p ∣ p`,
`A₀` is `π`-adically complete and separated, and relative Frobenius
`A₀ ⧸ (π) → A₀ ⧸ (π ^ p)` is bijective (so `A₀` is an integral perfectoid ring by
`TauCeti.Perfectoid.IsIntegralPerfectoid.of_bijective_frobeniusModPow`). Let `A = A₀[1/π]` carry a
topology whose neighbourhoods of zero have basis `πⁿ A₀`. Then `A` is automatically Tate, complete,
and Hausdorff (`TauCeti.Huber.isTateRing_of_hasBasis`, `completeSpace_of_hasBasis`,
`t2Space_of_hasBasis`) as well as uniform (`TauCeti.Huber.isUniform_of_dvd_of_pow_dvd_pow`), hence
a perfectoid Tate ring, and after replacing `π` by an associated element `ϖ.untilt` with compatible
`p`-power roots `wₙ = ((φ⁻¹)^[n] ϖ).untilt ∈ A₀` (`PreTilt.exists_associated_untilt`), the
power-bounded elements are `{x ∈ A | ∀ n, wₙ * x ∈ A₀}`, with `A₀ ⊆ A°` and `π A° ⊆ A₀`
(Bhatt–Morrow–Scholze, *Integral `p`-adic Hodge theory*, Lemma 3.21).

## Main results

* `TauCeti.Perfectoid.isPowerBounded_iff_forall_untilt_mul_mem_range`: under
  `[Fact ¬IsUnit (p : A₀)]`, `IsAdicComplete (span {(p : A₀)}) A₀`, regularity `π ∈ A₀⁰`, and
  the root condition `π ^ p ∣ a ^ p → π ∣ a`, if `ϖ : PreTilt A₀ p` satisfies
  `Associated π ϖ.untilt`, then `x ∈ A` is power-bounded iff `wₙ * x ∈ A₀` for all `n` along the
  compatible tower `wₙ = ((φ⁻¹)^[n] ϖ).untilt`.
* `TauCeti.Perfectoid.isPerfectoidTateRing_of_bijective_frobeniusModPow`: `A = A₀[1/π]` is a
  perfectoid Tate ring (with `IsTateRing`, `CompleteSpace`, and `T2Space` inferred from the basis)
  when `π ∈ A₀⁰`, `π ^ p ∣ p`, `A₀` is `π`-adically complete and separated, and relative Frobenius
  `A₀ ⧸ (π) → A₀ ⧸ (π ^ p)` is bijective.

## References

* B. Bhatt, M. Morrow, P. Scholze, *Integral `p`-adic Hodge theory*, Lemma 3.21.
* P. Scholze, *Perfectoid spaces*, Lemmas 5.6–5.7.
-/

public section

open Filter Ideal Topology TauCeti.Huber
open scoped nonZeroDivisors

namespace TauCeti.Perfectoid

section Roots

variable {p : ℕ} [hp : Fact p.Prime] {A₀ : Type*} [CommRing A₀] {π : A₀}
  {A : Type*} [CommRing A] [Algebra A₀ A]

/-- Regularity and the root condition `w ^ p ∣ a ^ p → w ∣ a` propagate along the `p`-power root
tower of `ϖ : PreTilt A₀ p`. -/
private theorem root_tower_step [Fact ¬IsUnit (p : A₀)] [IsAdicComplete (span {(p : A₀)}) A₀]
    (hπ : π ∈ A₀⁰) (hroot : ∀ a : A₀, π ^ p ∣ a ^ p → π ∣ a)
    {ϖ : PreTilt A₀ p} (hass : Associated π ϖ.untilt) (n : ℕ) :
    (((frobeniusEquiv (PreTilt A₀ p) p).symm^[n]) ϖ).untilt ∈ A₀⁰ ∧
      ∀ a : A₀, (((frobeniusEquiv (PreTilt A₀ p) p).symm^[n]) ϖ).untilt ^ p ∣ a ^ p →
        (((frobeniusEquiv (PreTilt A₀ p) p).symm^[n]) ϖ).untilt ∣ a := by
  induction n with
  | zero =>
    obtain ⟨u, hu⟩ := hass
    refine ⟨by simpa [← hu] using mul_mem hπ u.isUnit.mem_nonZeroDivisors, fun a ha ↦ ?_⟩
    simp only [Function.iterate_zero, id_eq] at ha ⊢
    rw [← hu, mul_pow] at ha
    rw [← hu]
    exact (Units.mul_right_dvd).mpr (hroot a ((dvd_mul_right (π ^ p) ((u : A₀) ^ p)).trans ha))
  | succ n ih =>
    set w1 := (((frobeniusEquiv (PreTilt A₀ p) p).symm^[n + 1]) ϖ).untilt
    set w0 := (((frobeniusEquiv (PreTilt A₀ p) p).symm^[n]) ϖ).untilt
    have hpow : w1 ^ p = w0 := PreTilt.untilt_iterate_frobeniusEquiv_symm_succ_pow ϖ n
    have hreg : w1 ∈ A₀⁰ :=
      (TauCeti.pow_mem_nonZeroDivisors_iff hp.out.ne_zero).mp (hpow.symm ▸ ih.1)
    exact ⟨hreg, fun a ha ↦
      TauCeti.dvd_of_pow_dvd_pow hp.out.ne_zero (hpow.symm ▸ ih.1) (hpow.symm ▸ ih.2) ha⟩

/-- **Characterisation of power-bounded elements of `A₀[1/π]`** (Bhatt–Morrow–Scholze, *Integral
`p`-adic Hodge theory*, Lemma 3.21): assuming `Fact ¬IsUnit (p : A₀)`, `A₀` `p`-adically complete,
`π ∈ A₀⁰`, and `π ^ p ∣ a ^ p → π ∣ a`, if `ϖ : PreTilt A₀ p` satisfies `Associated π ϖ.untilt`,
then an element `x ∈ A₀[1/π]` is power-bounded if and only if `wₙ * x ∈ A₀` for every `n` along the
compatible `p`-power root tower `wₙ = ((φ⁻¹)^[n] ϖ).untilt` of `ϖ.untilt`. -/
theorem isPowerBounded_iff_forall_untilt_mul_mem_range
    [IsLocalization.Away π A] [TopologicalSpace A] [IsTopologicalRing A]
    [Fact ¬IsUnit (p : A₀)] [IsAdicComplete (span {(p : A₀)}) A₀]
    (h : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ (awayNhd π A n : Set A))
    (hπ : π ∈ A₀⁰) (hroot : ∀ a : A₀, π ^ p ∣ a ^ p → π ∣ a)
    {ϖ : PreTilt A₀ p} (hass : Associated π ϖ.untilt) {x : A} :
    IsPowerBounded x ↔
      ∀ n : ℕ, algebraMap A₀ A (((frobeniusEquiv (PreTilt A₀ p) p).symm^[n]) ϖ).untilt * x ∈
        (algebraMap A₀ A).range := by
  set ψ := (frobeniusEquiv (PreTilt A₀ p) p).symm
  set w : ℕ → A₀ := fun n ↦ ((ψ^[n]) ϖ).untilt
  have hw_pow (n : ℕ) : w n ^ p ^ n = ϖ.untilt :=
    PreTilt.untilt_iterate_frobeniusEquiv_symm_pow ϖ n
  constructor
  · intro hx n
    have hass_n : Associated π (w n ^ p ^ n) := by rwa [hw_pow n]
    have : IsLocalization.Away (w n) A :=
      IsLocalization.Away.of_dvd_of_dvd_pow
        ((dvd_pow_self _ (pow_ne_zero n hp.out.ne_zero)).trans hass_n.symm.dvd) hass_n.dvd
    have hbasis_n := hasBasis_awayNhd_of_pow_associated h (pow_ne_zero n hp.out.ne_zero) hass_n
    have hstep := root_tower_step hπ hroot hass n
    exact algebraMap_mul_mem_range_of_isPowerBounded hbasis_n hp.out.one_lt
      hstep.1 hstep.2 hx
  · intro hx
    obtain ⟨u, hu⟩ := hass
    have hwu : IsUnit (algebraMap A₀ A ϖ.untilt) := by
      rw [← hu, map_mul]
      exact (IsLocalization.Away.algebraMap_isUnit π).mul (u.isUnit.map _)
    refine isPowerBounded_iff.mpr ?_
    refine ((isBounded_singleton (↑hwu.unit⁻¹ : A)).mul
      (isBounded_range_algebraMap_of_hasBasis h)).subset ?_
    rintro _ ⟨m, rfl⟩
    obtain ⟨b, hb⟩ := hx m
    have hle : m ≤ p ^ m := (Nat.lt_pow_self hp.out.one_lt).le
    have hmem : algebraMap A₀ A ϖ.untilt * x ^ m ∈ (algebraMap A₀ A).range := by
      refine ⟨w m ^ (p ^ m - m) * b ^ m, ?_⟩
      rw [map_mul, map_pow, map_pow, hb, mul_pow, ← mul_assoc, ← map_pow (algebraMap A₀ A) (w m) m,
        ← map_pow (algebraMap A₀ A) (w m) (p ^ m - m), ← map_mul, ← pow_add,
        Nat.sub_add_cancel hle, hw_pow m]
    refine Set.mem_mul.mpr ⟨↑hwu.unit⁻¹, Set.mem_singleton _, algebraMap A₀ A ϖ.untilt * x ^ m,
      hmem, ?_⟩
    exact hwu.unit.inv_mul_cancel_left (x ^ m)

/-- **Perfectoid Tate rings from integral perfectoid rings** (Bhatt–Morrow–Scholze, *Integral
`p`-adic Hodge theory*, Lemma 3.21): if `A₀` is `π`-adically complete for a nonzerodivisor `π` with
`π ^ p ∣ p` and bijective relative Frobenius `A₀ ⧸ (π) → A₀ ⧸ (π ^ p)`, then `A = A₀[1/π]` equipped
with its `π`-adic topology is automatically a complete Hausdorff Tate ring and is a perfectoid Tate
ring. -/
theorem isPerfectoidTateRing_of_bijective_frobeniusModPow
    [IsLocalization.Away π A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    (h : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ (awayNhd π A n : Set A))
    {hdvd : π ^ p ∣ (p : A₀)} [IsAdicComplete (span {π}) A₀]
    (hπ : π ∈ A₀⁰) (hbij : Function.Bijective (frobeniusModPow p hdvd)) :
    letI : IsTateRing A := isTateRing_of_hasBasis h
    letI : CompleteSpace A := completeSpace_of_hasBasis h hπ
    letI : T2Space A := t2Space_of_hasBasis h hπ
    IsPerfectoidTateRing p A := by
  let : IsTateRing A := isTateRing_of_hasBasis h
  let : CompleteSpace A := completeSpace_of_hasBasis h hπ
  let : T2Space A := t2Space_of_hasBasis h hπ
  let ϖ : (algebraMap A₀ A).range := ⟨algebraMap A₀ A π, π, rfl⟩
  have hϖp : ϖ ^ p ∣ (p : (algebraMap A₀ A).range) := by
    obtain ⟨c, hc⟩ := hdvd
    exact ⟨⟨algebraMap A₀ A c, c, rfl⟩, Subtype.ext (by
      simpa only [Subring.coe_natCast, Subring.coe_pow, Subring.coe_mul, ϖ, ← map_pow, ← map_mul,
        map_natCast] using congrArg (algebraMap A₀ A) hc)⟩
  have hbij' : Function.Bijective (frobeniusModPow p hϖp) := by
    refine ⟨(frobeniusModPow_injective_iff hϖp).mpr ?_,
      (frobeniusModPow_surjective_iff hϖp).mpr ?_⟩
    · rintro ⟨_, a, rfl⟩ ⟨⟨_, c, rfl⟩, hc⟩
      have hca : a ^ p = π ^ p * c := IsLocalization.injective A (Submonoid.powers_le.mpr hπ) <| by
        simpa [ϖ, map_pow, map_mul] using congrArg Subtype.val hc
      obtain ⟨d, hd⟩ := (frobeniusModPow_injective_iff hdvd).mp hbij.1 a ⟨c, hca⟩
      exact ⟨⟨algebraMap A₀ A d, d, rfl⟩, Subtype.ext (by simp [ϖ, hd])⟩
    · rintro ⟨_, a, rfl⟩
      obtain ⟨b, c, hbc⟩ := (frobeniusModPow_surjective_iff hdvd).mp hbij.2 a
      refine ⟨⟨algebraMap A₀ A b, b, rfl⟩, ⟨algebraMap A₀ A c, c, rfl⟩, Subtype.ext ?_⟩
      simpa [ϖ, map_sub, map_pow, map_mul] using congrArg (algebraMap A₀ A) hbc
  exact IsPerfectoidTateRing.of_bijective_frobeniusModPow
    (isOpen_range_algebraMap_of_hasBasis h) (isBounded_range_algebraMap_of_hasBasis h)
    (isPseudoUniformizer_algebraMap_of_hasBasis h) hϖp hbij'

end Roots

end TauCeti.Perfectoid
