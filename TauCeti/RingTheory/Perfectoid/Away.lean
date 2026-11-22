/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Away
public import TauCeti.RingTheory.Perfectoid.Basic
public import TauCeti.RingTheory.Perfectoid.Untilt

import TauCeti.RingTheory.AdicCompletion.Principal

/-!
# Perfectoid Tate rings from integral perfectoid rings

Let `p` be a prime and `A₀` a commutative ring with a nonzerodivisor `π ∈ A₀` such that `π ^ p ∣ p`,
`A₀` is `π`-adically complete and separated, and relative Frobenius
`A₀ ⧸ (π) → A₀ ⧸ (π ^ p)` is bijective (so `A₀` is an integral perfectoid ring by
`TauCeti.Perfectoid.IsIntegralPerfectoid.of_bijective_frobeniusModPow`). Let `A = A₀[1/π]` carry the
`π`-adic topology, whose neighbourhoods of zero have basis `πⁿ A₀`. If moreover `A` is complete
and Hausdorff, then `A` is a perfectoid Tate ring, and after replacing `π` by an associated
element `ϖ.untilt` with compatible `p`-power roots `wₙ = ((φ⁻¹)^[n] ϖ).untilt ∈ A₀`
(`PreTilt.exists_associated_untilt`), the power-bounded elements are `{x ∈ A | ∀ n, wₙ * x ∈ A₀}`,
with `A₀ ⊆ A°` and `π A° ⊆ A₀` (Bhatt–Morrow–Scholze, *Integral `p`-adic Hodge theory*, Lemma 3.21).

The inclusion `π A° ⊆ A₀` and uniformity of `A` require only regularity of `π` and the root
condition `π ^ p ∣ a ^ p → π ∣ a` (with `1 < p`), with no completeness or surjectivity hypothesis.

## Main results

* `TauCeti.Perfectoid.algebraMap_mul_mem_range_of_isPowerBounded`: `π x ∈ A₀` for every
  power-bounded `x ∈ A`, whenever `π` is a nonzerodivisor with `π ^ p ∣ a ^ p → π ∣ a`.
* `TauCeti.Perfectoid.isUniform_of_dvd_of_pow_dvd_pow`: `A = A₀[1/π]` is uniform under the same
  hypotheses.
* `TauCeti.Perfectoid.isPowerBounded_iff_forall_untilt_mul_mem_range`: for `ϖ : PreTilt A₀ p` with
  `Associated π ϖ.untilt`, `x` is power-bounded iff `wₙ * x ∈ A₀` for every `p ^ n`-th root `wₙ` of
  `ϖ.untilt`.
* `TauCeti.Perfectoid.isPerfectoidTateRing_of_bijective_frobeniusModPow`: `A = A₀[1/π]` is a
  perfectoid Tate ring when `A₀` is `π`-adically complete with `π ^ p ∣ p` and bijective relative
  Frobenius `A₀ ⧸ (π) → A₀ ⧸ (π ^ p)`.

## References

* B. Bhatt, M. Morrow, P. Scholze, *Integral `p`-adic Hodge theory*, Lemma 3.21.
* P. Scholze, *Perfectoid spaces*, Lemmas 5.6–5.7.
-/

public section

open Filter Ideal Topology TauCeti.Huber
open scoped nonZeroDivisors

namespace TauCeti.Perfectoid

section Uniform

variable {p : ℕ} {A₀ : Type*} [CommRing A₀] {π : A₀} {A : Type*} [CommRing A] [Algebra A₀ A]

/-- If `π` is a nonzerodivisor and `π ^ p ∣ a ^ p → π ∣ a`, then `π ^ (s * p) ∣ a ^ p → π ^ s ∣ a`.
-/
private theorem pow_dvd_of_pow_mul_dvd_pow (hπ : π ∈ A₀⁰)
    (hroot : ∀ a : A₀, π ^ p ∣ a ^ p → π ∣ a) :
    ∀ (s : ℕ) (a : A₀), π ^ (s * p) ∣ a ^ p → π ^ s ∣ a := by
  intro s
  induction s with
  | zero => intro a _; exact pow_zero π ▸ one_dvd a
  | succ s ih =>
    intro a ha
    have hsplit : π ^ ((s + 1) * p) = π ^ p * π ^ (s * p) := by
      rw [Nat.succ_mul, pow_add, mul_comm]
    rw [hsplit] at ha
    obtain ⟨b, rfl⟩ := hroot a ((dvd_mul_right (π ^ p) _).trans ha)
    rw [mul_pow] at ha
    have hb : π ^ (s * p) ∣ b ^ p := by
      obtain ⟨c, hc⟩ := ha
      refine ⟨c, (mul_cancel_left_mem_nonZeroDivisors (pow_mem hπ p)).mp ?_⟩
      simpa only [mul_assoc] using hc
    rw [pow_succ']
    exact mul_dvd_mul_left π (ih b hb)

/-- Iterating `pow_dvd_of_pow_mul_dvd_pow` along `p`-th powers:
`π ^ (s * p ^ m) ∣ a ^ p ^ m → π ^ s ∣ a`. -/
private theorem pow_dvd_of_pow_mul_pow_dvd_pow (hπ : π ∈ A₀⁰)
    (hroot : ∀ a : A₀, π ^ p ∣ a ^ p → π ∣ a) :
    ∀ (m s : ℕ) (a : A₀), π ^ (s * p ^ m) ∣ a ^ p ^ m → π ^ s ∣ a := by
  intro m
  induction m with
  | zero => intro s a ha; simpa using ha
  | succ m ih =>
    intro s a ha
    have h1 : π ^ (s * p * p ^ m) ∣ (a ^ p) ^ p ^ m := by
      rwa [mul_assoc, ← pow_succ', ← pow_mul, ← pow_succ']
    exact pow_dvd_of_pow_mul_dvd_pow hπ hroot s a (ih (s * p) (a ^ p) h1)

variable [IsLocalization.Away π A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **`π A° ⊆ A₀`**: in `A = A₀[1/π]` with the `π`-adic topology, if `π` is a nonzerodivisor
satisfying `π ^ p ∣ a ^ p → π ∣ a` for some `p > 1`, then multiplying any power-bounded element of
`A` by `π` lands in the image of `A₀`. -/
theorem algebraMap_mul_mem_range_of_isPowerBounded (hp : 1 < p)
    (h : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ (awayNhd π A n : Set A))
    (hπ : π ∈ A₀⁰) (hroot : ∀ a : A₀, π ^ p ∣ a ^ p → π ∣ a)
    {x : A} (hx : IsPowerBounded x) :
    algebraMap A₀ A π * x ∈ (algebraMap A₀ A).range := by
  have hopen := isOpen_range_algebraMap_of_hasBasis h
  have hϖ := isPseudoUniformizer_algebraMap_of_hasBasis h
  obtain ⟨k, hk⟩ := (isPowerBounded_iff.mp hx).exists_pow_mul_subset
    hϖ.isTopologicallyNilpotent (hopen.mem_nhds (zero_mem _))
  obtain ⟨r, a, ha⟩ := IsLocalization.Away.surj π x
  cases r with
  | zero =>
    rw [pow_zero, mul_one] at ha
    exact ⟨π * a, by rw [map_mul, ha]⟩
  | succ s =>
    have hle : k ≤ p ^ k := (Nat.lt_pow_self hp).le
    have hkx : algebraMap A₀ A π ^ k * x ^ p ^ k ∈ (algebraMap A₀ A).range :=
      hk (Set.mul_mem_mul (Set.mem_singleton _) (Set.mem_range_self (p ^ k)))
    obtain ⟨b, hb⟩ : ∃ b : A₀, algebraMap A₀ A b = (algebraMap A₀ A π * x) ^ p ^ k := by
      obtain ⟨b₀, hb₀⟩ := hkx
      refine ⟨π ^ (p ^ k - k) * b₀, ?_⟩
      rw [map_mul, map_pow, hb₀, mul_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    have hap : a ^ p ^ k = π ^ (s * p ^ k) * b := by
      apply IsLocalization.injective A (Submonoid.powers_le.mpr hπ)
      rw [map_pow, ← ha, map_mul, map_pow, hb, mul_pow, mul_pow, ← pow_mul,
        show (s + 1) * p ^ k = s * p ^ k + p ^ k by ring, pow_add]
      ring
    obtain ⟨c, hc⟩ := pow_dvd_of_pow_mul_pow_dvd_pow hπ hroot k s a ⟨b, hap⟩
    refine ⟨c, ?_⟩
    have hu : IsUnit (algebraMap A₀ A π ^ s) := (IsLocalization.Away.algebraMap_isUnit π).pow s
    refine hu.mul_right_cancel ?_
    rw [← map_pow, ← map_mul, mul_comm c, ← hc, ← ha, map_pow]
    ring

/-- **Uniformity of `A₀[1/π]`**: under the hypotheses of
`algebraMap_mul_mem_range_of_isPowerBounded`, the power-bounded elements lie in `π⁻¹ A₀` and are
therefore bounded, so `A` is uniform. -/
theorem isUniform_of_dvd_of_pow_dvd_pow (hp : 1 < p)
    (h : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ (awayNhd π A n : Set A))
    (hπ : π ∈ A₀⁰) (hroot : ∀ a : A₀, π ^ p ∣ a ^ p → π ∣ a) : IsUniform A := by
  let hunit := IsLocalization.Away.algebraMap_isUnit (S := A) π
  refine isUniform_iff.mpr <|
    ((isBounded_singleton (↑hunit.unit⁻¹ : A)).mul
      (isBounded_range_algebraMap_of_hasBasis h)).subset fun x hx ↦ ?_
  refine Set.mem_mul.mpr ⟨↑hunit.unit⁻¹, Set.mem_singleton _, algebraMap A₀ A π * x,
    algebraMap_mul_mem_range_of_isPowerBounded hp h hπ hroot hx, ?_⟩
  exact hunit.unit.inv_mul_cancel_left x

end Uniform

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
`p`-adic Hodge theory*, Lemma 3.21): if `ϖ : PreTilt A₀ p` satisfies `Associated π ϖ.untilt`, then
an element `x ∈ A₀[1/π]` is power-bounded if and only if `wₙ * x ∈ A₀` for every `p ^ n`-th root
`wₙ = ((φ⁻¹)^[n] ϖ).untilt` of `ϖ.untilt`. -/
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
    exact algebraMap_mul_mem_range_of_isPowerBounded hp.out.one_lt hbasis_n
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
with its `π`-adic topology is a perfectoid Tate ring. -/
theorem isPerfectoidTateRing_of_bijective_frobeniusModPow
    [IsLocalization.Away π A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [IsTateRing A] [CompleteSpace A] [T2Space A]
    (h : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ (awayNhd π A n : Set A))
    {hdvd : π ^ p ∣ (p : A₀)} [IsAdicComplete (span {π}) A₀]
    (hπ : π ∈ A₀⁰) (hbij : Function.Bijective (frobeniusModPow p hdvd)) :
    IsPerfectoidTateRing p A := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact isPerfectoidTateRing_of_subsingleton p A
  have hroot : ∀ a : A₀, π ^ p ∣ a ^ p → π ∣ a := (frobeniusModPow_injective_iff hdvd).mp hbij.1
  have hsurj : ∀ a : A₀, ∃ b : A₀, π ^ p ∣ a - b ^ p :=
    (frobeniusModPow_surjective_iff hdvd).mp hbij.2
  have : IsUniform A := isUniform_of_dvd_of_pow_dvd_pow hp.out.one_lt h hπ hroot
  have : Nontrivial A₀ := by
    by_contra hnot
    rw [not_nontrivial_iff_subsingleton] at hnot
    exact not_subsingleton A (algebraMap A₀ A).codomain_trivial
  have hπp : π ∣ (p : A₀) := (dvd_pow_self π hp.out.ne_zero).trans hdvd
  have : IsAdicComplete (span {(p : A₀)}) A₀ := .span_singleton_of_dvd hπp
  have : Fact ¬IsUnit (p : A₀) :=
    ⟨IsAdicComplete.not_isUnit_of_mem (I := span {π}) (mem_span_singleton.mpr hπp)⟩
  -- Replace `π` by an associated untilt `ϖ.untilt` with a `p`-th root `w₁`.
  obtain ⟨ϖ, -, hass⟩ := PreTilt.exists_associated_untilt hdvd hsurj
  have ⟨u, hu⟩ := hass
  set w0 : A₀ := ϖ.untilt
  set w1 : A₀ := ((frobeniusEquiv (PreTilt A₀ p) p).symm ϖ).untilt
  have hw1_pow : w1 ^ p = w0 := by
    simpa [w0, w1] using PreTilt.untilt_iterate_frobeniusEquiv_symm_succ_pow ϖ 0
  have hw0_pow_dvd : w0 ^ p ∣ π ^ p := by
    rw [← hu, mul_pow]
    exact ⟨(u⁻¹ : A₀ˣ) ^ p, by rw [mul_assoc, ← mul_pow, Units.mul_inv, one_pow, mul_one]⟩
  have hw0_dvd : w0 ^ p ∣ (p : A₀) := hw0_pow_dvd.trans hdvd
  have : IsAdicComplete (span {w0}) A₀ := by
    rwa [show span {w0} = span {π} by rw [← hu, span_singleton_mul_right_unit u.isUnit]]
  have hs0 : ∀ a : A₀, ∃ b : A₀, w0 ^ p ∣ a - b ^ p := fun a ↦
    (hsurj a).imp fun _ hb ↦ hw0_pow_dvd.trans hb
  have hrange_le : (algebraMap A₀ A).range ≤ powerBoundedSubring A := fun _ hx ↦
    mem_powerBoundedSubring.mpr
      ((isBounded_range_algebraMap_of_hasBasis h).isPowerBounded_of_mem hx)
  let ϖPB : powerBoundedSubring A := ⟨algebraMap A₀ A w0, hrange_le ⟨w0, rfl⟩⟩
  have hϖPB_pu : IsPseudoUniformizer (ϖPB : A) := by
    have hpu := isPseudoUniformizer_algebraMap_of_hasBasis h
    refine isPseudoUniformizer_iff.mpr ⟨?_, ?_⟩
    · dsimp only [ϖPB]
      rw [← hu, map_mul]
      exact hpu.isUnit.mul (u.isUnit.map _)
    · dsimp only [ϖPB]
      rw [← hu, map_mul, mul_comm]
      exact ((isBounded_range_algebraMap_of_hasBasis h).isPowerBounded_of_mem
        ⟨(u : A₀), rfl⟩).isTopologicallyNilpotent_mul hpu.isTopologicallyNilpotent
  have hϖPB_dvd : ϖPB ^ p ∣ (p : powerBoundedSubring A) := by
    obtain ⟨c, hc⟩ := hw0_dvd
    refine ⟨⟨algebraMap A₀ A c, hrange_le ⟨c, rfl⟩⟩, Subtype.ext ?_⟩
    simp only [Subring.coe_natCast, Subring.coe_mul, Subring.coe_pow, ϖPB, ← map_pow, ← map_mul,
      ← hc, map_natCast]
  have hw1_unit : IsUnit (algebraMap A₀ A w1) :=
    (isUnit_pow_iff hp.out.ne_zero).mp (by rw [← map_pow, hw1_pow]; exact hϖPB_pu.isUnit)
  -- Every `x ∈ A°` has `w0 * x = a ∈ A₀`, which is congruent to a `p`-th power `y₀ ^ p`
  -- mod `w0 * p`; dividing by `w1` gives `y = y₀ / w1 ∈ A°` with `w0 ^ p ∣ x - y ^ p` in `A°`.
  refine IsPerfectoidTateRing.of_surjective ϖPB hϖPB_pu hϖPB_dvd fun x ↦ ?_
  have hwx : algebraMap A₀ A w0 * (x : A) ∈ (algebraMap A₀ A).range := by
    simpa [w0] using (isPowerBounded_iff_forall_untilt_mul_mem_range h hπ hroot hass).mp
      (mem_powerBoundedSubring.mp x.property) 0
  obtain ⟨a, ha⟩ := hwx
  obtain ⟨f, c, hfc⟩ := PreTilt.exists_mul_natCast_dvd_sub_untilt hw0_dvd hs0 a
  set y0 : A₀ := ((frobeniusEquiv (PreTilt A₀ p) p).symm f).untilt
  have hy0_pow : y0 ^ p = f.untilt := by
    simpa [y0] using PreTilt.untilt_iterate_frobeniusEquiv_symm_succ_pow f 0
  set y : A := (↑hw1_unit.unit⁻¹ : A) * algebraMap A₀ A y0
  have hyp : y ^ p = (x : A) - (p : A) * algebraMap A₀ A c := by
    apply hϖPB_pu.isUnit.mul_left_cancel
    have h1 : algebraMap A₀ A w0 * y ^ p = algebraMap A₀ A f.untilt := by
      rw [← hw1_pow, map_pow, ← mul_pow, ← hy0_pow, map_pow]
      congr 1
      exact hw1_unit.unit.mul_inv_cancel_left (algebraMap A₀ A y0)
    dsimp only [ϖPB]
    rw [h1, mul_sub, ← ha, ← mul_assoc, mul_right_comm (algebraMap A₀ A w0),
      ← map_natCast (algebraMap A₀ A), ← map_mul, ← map_mul, ← map_sub]
    congr 1
    linear_combination -hfc
  have hy_pb : y ∈ powerBoundedSubring A := by
    refine mem_powerBoundedSubring.mpr (IsPowerBounded.of_pow hp.out.ne_zero ?_)
    rw [hyp]
    exact mem_powerBoundedSubring.mp
      (sub_mem x.property (mul_mem (natCast_mem _ p) (hrange_le ⟨c, rfl⟩)))
  refine ⟨⟨y, hy_pb⟩, hϖPB_dvd.trans ⟨⟨algebraMap A₀ A c, hrange_le ⟨c, rfl⟩⟩, Subtype.ext ?_⟩⟩
  simp only [AddSubgroupClass.coe_sub, Subring.coe_pow, Subring.coe_mul, Subring.coe_natCast]
  linear_combination -hyp

end Roots

end TauCeti.Perfectoid
