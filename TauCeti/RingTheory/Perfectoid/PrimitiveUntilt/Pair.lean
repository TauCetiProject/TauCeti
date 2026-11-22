/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.AlmostSetup
public import TauCeti.RingTheory.Perfectoid.PrimitiveUntilt.Perfectoid
public import TauCeti.RingTheory.Perfectoid.PseudoUniformizerRoots.Existence
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Pair
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Theta

import Mathlib.Algebra.CharP.Subring
import TauCeti.RingTheory.Huber.Pair.Complete
import TauCeti.RingTheory.Huber.Reduction
import TauCeti.RingTheory.Perfectoid.Pair
import TauCeti.RingTheory.WittVector.TeichmullerCoeff

/-!
# The Huber pair structure, Fontaine kernel, and almost vanishing of primitive untilts

Let `(R, R⁺)` be a perfect complete Hausdorff Tate Huber pair of characteristic `p`, and let
`ξ ∈ 𝕎 R⁺` be a primitive element. Building on
`TauCeti.RingTheory.Perfectoid.PrimitiveUntilt.Perfectoid` (which proves that the untilt
`A = untilt p P (Ideal.span {ξ})` is a perfectoid Tate ring with tilt `A♭ ≃+* R` via
`untilt.tiltEquiv`), this file establishes the Huber-pair and Fontaine-`θ` properties of `(A, A⁺)`:

* Using Fontaine's surjection `θ : 𝕎((A♭)°) → A°`, we prove that
  `A⁺ = untiltPlus p P (Ideal.span {ξ})` is integrally closed in `A`
  (`untilt.isIntegrallyClosedIn_untiltPlus`), hence a ring of integral elements
  (`untilt.isRingOfIntegralElements_untiltPlus`), yielding the Huber pair `untilt.pair`.
* Under `untilt.tiltEquiv`, the tilted plus ring `A♭⁺` identifies with `R⁺`
  (`untilt.mem_tilt_plus_iff`, `untilt.tiltPlusEquiv`), and Mathlib's `PreTilt A⁺ p` identifies
  with `R⁺` (`untilt.preTiltEquiv`).
* Fontaine's `θ` identifies with the quotient map `𝕎 R⁺ → A⁺`
  (`untilt.theta_comp_map_tiltPlusEquiv_symm`, `untilt.fontaineTheta_comp_map_preTiltEquiv_symm`),
  so `ker θ = (ξ)` (`untilt.ker_theta_eq`, `untilt.ker_fontaineTheta_eq`).
* The quotient `A° ⧸ A⁺` is almost zero for the almost setup `(A⁺, A°°)`
  (`untilt.isAlmostZero_powerBounded_quotient`).

## Main definitions

* `TauCeti.Perfectoid.untilt.pair`: the untilt as a `Huber.Pair A` with plus ring `A⁺`.
* `TauCeti.Perfectoid.untilt.tiltPlusEquiv`: the ring isomorphism `A♭⁺ ≃+* R⁺`.
* `TauCeti.Perfectoid.untilt.preTiltEquiv`: the ring isomorphism `PreTilt A⁺ p ≃+* R⁺`.

## Main results

* `TauCeti.Perfectoid.untilt.isIntegrallyClosedIn_untiltPlus`,
  `TauCeti.Perfectoid.untilt.isRingOfIntegralElements_untiltPlus`: `A⁺` is a ring of integral
  elements of `A`.
* `TauCeti.Perfectoid.untilt.mem_tilt_plus_iff`:
  `y ∈ (untilt.pair hξ).tilt.plus ↔ tiltEquiv hξ y ∈ R⁺`.
* `TauCeti.Perfectoid.untilt.ker_theta_eq`, `TauCeti.Perfectoid.untilt.ker_fontaineTheta_eq`:
  under the identification `A♭⁺ ≃+* R⁺` (resp. `PreTilt A⁺ p ≃+* R⁺`), `ker θ = (ξ)`.
* `TauCeti.Perfectoid.untilt.isAlmostZero_powerBounded_quotient`: `A° ⧸ A⁺` is almost zero.

## References

* P. Scholze, *Étale cohomology of diamonds*, Theorem 3.17.
* P. Scholze and J. Weinstein, *Berkeley lectures on `p`-adic geometry*, Theorem 6.2.11.
* K. S. Kedlaya, *Nonarchimedean geometry of Witt vectors and the tilting equivalence*,
  Arizona Winter School 2017, Lemmas 2.6.14, 2.7.9, and Theorem 2.3.9.
* B. Bhatt, M. Morrow, P. Scholze, *Integral `p`-adic Hodge theory*, Lemma 3.21.
-/

public section

open Filter Ideal Topology TauCeti.Huber WittVector
open scoped nonZeroDivisors Pointwise

namespace TauCeti.Perfectoid.untilt

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]
  [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R] [IsTateRing R]
  [CompleteSpace R] [T2Space R] [CharP R p] [PerfectRing R p]
  {P : Pair R} {ξ : WittVector p P.plus}

private theorem iterateFrobeniusEquiv_zero_symm_eq {S : Type*} [CommRing S] [CharP S p]
    [PerfectRing S p] (x : S) : (iterateFrobeniusEquiv S p 0).symm x = x := by
  simp

/-! ### Integral closedness of `A⁺` and the untilt Huber pair -/

private theorem perfectRing_tiltPowerBounded (hξ : ξ.IsPrimitive)
    [Nontrivial (untilt p P (Ideal.span {ξ}))] :
    letI := t2Space hξ
    letI := completeSpace hξ
    letI := isUniform hξ
    letI : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
      ⟨isTopologicallyNilpotent_natCast hξ⟩
    PerfectRing (uniformTilt.plusSubring p
      (isRingOfIntegralElements_powerBoundedSubring (untilt p P (Ideal.span {ξ})))) p := by
  have := t2Space hξ
  have := completeSpace hξ
  have := isUniform hξ
  have : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
    ⟨isTopologicallyNilpotent_natCast hξ⟩
  set A := untilt p P (Ideal.span {ξ})
  let hPB := isRingOfIntegralElements_powerBoundedSubring A
  let B₀ := uniformTilt.plusSubring p hPB
  have : IsReduced (uniformTilt p A) := isReduced_of_perfectRing (uniformTilt p A) p
  have : IsReduced B₀ := isReduced_of_injective B₀.subtype Subtype.val_injective
  exact PerfectRing.ofSurjective B₀ p fun x ↦ by
    let y : uniformTilt p A := (frobeniusEquiv (uniformTilt p A) p).symm x
    have hy : y ∈ B₀ := uniformTilt.mem_plusSubring_iff_coeff_zero.mpr <|
      mem_powerBoundedSubring.mpr <| IsPowerBounded.of_pow hp.out.ne_zero <| by
        rw [← map_pow, frobeniusEquiv_symm_pow_p]
        exact mem_powerBoundedSubring.mp (uniformTilt.mem_plusSubring_iff_coeff_zero.mp x.property)
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    change y ^ p = (x : uniformTilt p A)
    exact frobeniusEquiv_symm_pow_p (uniformTilt p A) p (x : uniformTilt p A)

/-- For Fontaine's map `Θ : 𝕎((A♭)°) → A°`, we have `Θ w ∈ A⁺ ↔ tiltEquiv (w.coeff 0) ∈ R⁺`. -/
private theorem theta_mem_untiltPlus_iff (hξ : ξ.IsPrimitive)
    [Nontrivial (untilt p P (Ideal.span {ξ}))] :
    letI := t2Space hξ
    letI := completeSpace hξ
    letI := isUniform hξ
    letI : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
      ⟨isTopologicallyNilpotent_natCast hξ⟩
    ∀ w : WittVector p (uniformTilt.plusSubring p
        (isRingOfIntegralElements_powerBoundedSubring (untilt p P (Ideal.span {ξ})))),
      (uniformTilt.theta p
        (isRingOfIntegralElements_powerBoundedSubring (untilt p P (Ideal.span {ξ}))) w :
          untilt p P (Ideal.span {ξ})) ∈ untiltPlus p P (Ideal.span {ξ}) ↔
        tiltEquiv hξ (w.coeff 0 : uniformTilt p (untilt p P (Ideal.span {ξ}))) ∈ P.plus := by
  have := t2Space hξ
  have := completeSpace hξ
  have := isUniform hξ
  have : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
    ⟨isTopologicallyNilpotent_natCast hξ⟩
  have := isTateRing_uniformTilt hξ
  have := perfectRing_tiltPowerBounded hξ
  set J := Ideal.span {ξ}
  set A := untilt p P J
  let hPB := isRingOfIntegralElements_powerBoundedSubring A
  let B₀ := uniformTilt.plusSubring p hPB
  let Θ : WittVector p B₀ →+* powerBoundedSubring A := uniformTilt.theta p hPB
  let e := tiltEquiv hξ
  have he_cont : Continuous e := (isHomeomorph_tiltEquiv hξ).continuous
  have hplus_le : untiltPlus p P J ≤ powerBoundedSubring A := fun _ hx ↦
    mem_powerBoundedSubring.mpr (isBounded_untiltPlus.isPowerBounded_of_mem hx)
  have he_open : ∀ V ∈ 𝓝 (0 : uniformTilt p A), e '' V ∈ 𝓝 (0 : R) := fun V hV ↦ by
    obtain ⟨U, hUV, hUo, h0U⟩ := mem_nhds_iff.mp hV
    exact mem_nhds_iff.mpr ⟨e '' U, Set.image_mono hUV,
      (isHomeomorph_tiltEquiv hξ).isOpenMap U hUo, ⟨0, h0U, map_zero e⟩⟩
  have he_pb (b : B₀) : e b ∈ powerBoundedSubring R :=
    mem_powerBoundedSubring.mpr ((mem_powerBoundedSubring.mp
      (uniformTilt.plusSubring_le_powerBoundedSubring hPB b.property)).map
        he_cont.continuousAt he_open)
  let ι : P.plus →+* B₀ :=
    (e.symm.toRingHom.comp P.plus.subtype).codRestrict B₀ fun a ↦
      uniformTilt.mem_plusSubring_iff_coeff_zero.mpr <| hplus_le <| by
        change uniformTilt.coeff p A 0 (e.symm a) ∈ untiltPlus p P J
        rw [coeff_tiltEquiv_symm, iterateFrobeniusEquiv_zero_symm_eq]
        change sharp p P J (a : R) ∈ _
        exact sharp_mem_untiltPlus a
  have hΘ_ι (w : WittVector p P.plus) :
      (Θ (WittVector.map ι w) : A) =
        algebraMap (WittVector p P.plus ⧸ J) A (Ideal.Quotient.mk J w) := by
    have := hPB.isAdicComplete_span_natCast p (isTopologicallyNilpotent_natCast hξ)
    let Φ : WittVector p P.plus →+* powerBoundedSubring A :=
      ((algebraMap (WittVector p P.plus ⧸ J) A).comp (Ideal.Quotient.mk J)).codRestrict
        (powerBoundedSubring A) fun w ↦ hplus_le (mem_untiltPlus.mpr ⟨_, rfl⟩)
    have heq : Θ.comp (WittVector.map ι) = Φ :=
      WittVector.ringHom_ext_teichmuller fun a ↦ Subtype.ext <| by
        dsimp only [Θ, Φ, B₀]
        rw [RingHom.comp_apply, WittVector.map_teichmuller, uniformTilt.theta_teichmuller,
          uniformTilt.coe_plusSharp, RingHom.codRestrict_apply, RingHom.comp_apply]
        change uniformTilt.coeff p A 0 (e.symm a) = _
        rw [coeff_tiltEquiv_symm, iterateFrobeniusEquiv_zero_symm_eq]
        change sharp p P J (a : R) = _
        rw [sharp_apply]
        rfl
    exact congrArg Subtype.val (RingHom.congr_fun heq w)
  have hΘ_p_mul (w₁ : WittVector p B₀) :
      (Θ ((p : WittVector p B₀) * w₁) : A) ∈ untiltPlus p P J := by
    obtain ⟨u, hu⟩ := isDistinguished_iff_exists_unit.mp hξ.isDistinguished
    let u' : (WittVector p B₀)ˣ := Units.map (WittVector.map ι).toMonoidHom u
    have hξ'_zero : Θ (WittVector.map ι ξ) = 0 := Subtype.ext <| by
      rw [hΘ_ι, Ideal.Quotient.mk_singleton_self, map_zero, ZeroMemClass.coe_zero]
    have hp_eq : Θ (p : WittVector p B₀) =
        -Θ (teichmuller p (ι (ξ.coeff 0)) * (↑u'⁻¹ : WittVector p B₀)) := by
      have h1 : Θ (teichmuller p (ι (ξ.coeff 0))) + Θ (p : WittVector p B₀) * Θ ↑u' = 0 := by
        have hu'val : (u' : WittVector p B₀) = WittVector.map ι ↑u := rfl
        rw [hu'val, ← map_mul, ← map_add, ← WittVector.map_teichmuller,
          ← map_natCast (WittVector.map ι), ← map_mul, ← map_add, ← hu, hξ'_zero]
      have hu' : Θ ↑u' * Θ ↑u'⁻¹ = 1 := by rw [← map_mul, u'.mul_inv, map_one]
      rw [map_mul]
      linear_combination Θ ↑u'⁻¹ * h1 - Θ (p : WittVector p B₀) * hu'
    set z : WittVector p B₀ := teichmuller p (ι (ξ.coeff 0)) * ((↑u'⁻¹ : WittVector p B₀) * w₁)
    have hcoeff_mem (i : ℕ) : e (z.coeff i : uniformTilt p A) ∈ P.plus := by
      have htc : z.coeff i =
          (ι (ξ.coeff 0)) ^ p ^ i * (((↑u'⁻¹ : WittVector p B₀) * w₁).coeff i) := by
        rw [← teichmullerCoeff_pow, teichmullerCoeff_teichmuller_mul, mul_pow, teichmullerCoeff_pow]
      rw [htc, Subring.coe_mul, Subring.coe_pow, map_mul, map_pow]
      have hι : e (ι (ξ.coeff 0) : uniformTilt p A) = (ξ.coeff 0 : R) :=
        e.apply_symm_apply _
      rw [hι]
      have hnil : IsTopologicallyNilpotent ((ξ.coeff 0 : R) ^ p ^ i) :=
        (hξ.isTopologicallyNilpotent_coeff_zero.map (φ := P.plus.subtype)
          continuous_subtypeVal).pow (pow_ne_zero i hp.out.ne_zero)
      rw [mul_comm]
      exact P.isRingOfIntegralElements.mem_of_isTopologicallyNilpotent
        ((mem_powerBoundedSubring.mp (he_pb _)).isTopologicallyNilpotent_mul hnil)
    let z₀ : WittVector p P.plus :=
      WittVector.mk p fun i ↦ ⟨e (z.coeff i : uniformTilt p A), hcoeff_mem i⟩
    have hz_eq : WittVector.map ι z₀ = z := by
      refine WittVector.ext fun i ↦ Subtype.ext <| e.injective ?_
      change e (e.symm (e (z.coeff i : uniformTilt p A))) = e (z.coeff i : uniformTilt p A)
      exact e.apply_symm_apply _
    have hval : Θ ((p : WittVector p B₀) * w₁) = -Θ z := by
      rw [map_mul, hp_eq, neg_mul, ← map_mul, mul_assoc]
    rw [hval, Subring.coe_neg, ← hz_eq, hΘ_ι]
    exact neg_mem (mem_untiltPlus.mpr ⟨_, rfl⟩)
  intro w
  obtain ⟨w₁, hw₁⟩ := exists_eq_sum_teichmullerCoeff_add_pow_mul w 1
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one, pow_one,
    teichmullerCoeff_zero] at hw₁
  have hw_eq : (Θ w : A) = sharp p P J (e (w.coeff 0 : uniformTilt p A)) +
      (Θ ((p : WittVector p B₀) * w₁) : A) := by
    conv_lhs => rw [hw₁]
    rw [map_add, Subring.coe_add, uniformTilt.theta_teichmuller, uniformTilt.coe_plusSharp,
      sharp_tiltEquiv hξ]
  rw [hw_eq, add_mem_cancel_right (hΘ_p_mul w₁), sharp_mem_untiltPlus_iff hξ]

/-- **`A⁺` is integrally closed in the untilt `A`** for a primitive element `ξ`. -/
theorem isIntegrallyClosedIn_untiltPlus (hξ : ξ.IsPrimitive) :
    IsIntegrallyClosedIn (untiltPlus p P (Ideal.span {ξ})) (untilt p P (Ideal.span {ξ})) := by
  set J := Ideal.span {ξ}
  set A := untilt p P J
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subring.isIntegrallyClosedIn_iff.mpr fun x _ ↦
      Subsingleton.elim x 0 ▸ zero_mem _
  have := t2Space hξ
  have := completeSpace hξ
  have := isUniform hξ
  have : Fact (IsTopologicallyNilpotent (p : A)) := ⟨isTopologicallyNilpotent_natCast hξ⟩
  have := isPerfectoidTateRing hξ
  have := isTateRing_uniformTilt hξ
  have := perfectRing_tiltPowerBounded hξ
  let hPB := isRingOfIntegralElements_powerBoundedSubring A
  let B₀ := uniformTilt.plusSubring p hPB
  let Θ : WittVector p B₀ →+* powerBoundedSubring A := uniformTilt.theta p hPB
  let e := tiltEquiv hξ
  have he_cont : Continuous e := (isHomeomorph_tiltEquiv hξ).continuous
  have hplus_le : untiltPlus p P J ≤ powerBoundedSubring A := fun _ hx ↦
    mem_powerBoundedSubring.mpr (isBounded_untiltPlus.isPowerBounded_of_mem hx)
  have he_open : ∀ V ∈ 𝓝 (0 : uniformTilt p A), e '' V ∈ 𝓝 (0 : R) := fun V hV ↦ by
    obtain ⟨U, hUV, hUo, h0U⟩ := mem_nhds_iff.mp hV
    exact mem_nhds_iff.mpr ⟨e '' U, Set.image_mono hUV,
      (isHomeomorph_tiltEquiv hξ).isOpenMap U hUo, ⟨0, h0U, map_zero e⟩⟩
  have he_pb (b : B₀) : e b ∈ powerBoundedSubring R :=
    mem_powerBoundedSubring.mpr ((mem_powerBoundedSubring.mp
      (uniformTilt.plusSubring_le_powerBoundedSubring hPB b.property)).map
        he_cont.continuousAt he_open)
  have hΘ_surj : Function.Surjective Θ :=
    uniformTilt.surjective_theta hPB
      (IsPerfectoidTateRing.exists_natCast_dvd_sub_pow (p := p) (R := A))
  -- Descend `w ↦ mk (topologicallyNilpotentIdeal R) (e (w.coeff 0))` along `Θ` to
  -- `A° →+* R° ⧸ R°°`.
  let qR := Ideal.Quotient.mk (topologicallyNilpotentIdeal R)
  let ePB : B₀ →+* powerBoundedSubring R :=
    (e.toRingHom.comp B₀.subtype).codRestrict (powerBoundedSubring R) he_pb
  let ψ₀ : WittVector p B₀ →+* CanonicalReduction R :=
    qR.comp (ePB.comp constantCoeff)
  have hker_le : RingHom.ker Θ ≤ RingHom.ker ψ₀ := by
    intro w hw
    rw [RingHom.mem_ker] at hw ⊢
    obtain ⟨w₁, hw₁⟩ := exists_eq_sum_teichmullerCoeff_add_pow_mul w 1
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one, pow_one,
      teichmullerCoeff_zero] at hw₁
    have hcoeff0 : uniformTilt.coeff p A 0 (w.coeff 0 : uniformTilt p A) =
        -((p : A) * (Θ w₁ : A)) := by
      have h0 : (Θ w : A) = 0 := congrArg Subtype.val hw
      rw [hw₁, map_add, map_mul, map_natCast, Subring.coe_add, Subring.coe_mul,
        Subring.coe_natCast, uniformTilt.theta_teichmuller, uniformTilt.coe_plusSharp] at h0
      exact eq_neg_of_add_eq_zero_left h0
    have hnilA :
        IsTopologicallyNilpotent (uniformTilt.coeff p A 0 (w.coeff 0 : uniformTilt p A)) := by
      rw [hcoeff0, show -((p : A) * (Θ w₁ : A)) =
          ((-(Θ w₁) : powerBoundedSubring A) : A) * (p : A) by rw [Subring.coe_neg]; ring]
      exact (mem_powerBoundedSubring.mp (-(Θ w₁)).property).isTopologicallyNilpotent_mul
        (isTopologicallyNilpotent_natCast hξ)
    have hnilTilt : IsTopologicallyNilpotent (w.coeff 0 : uniformTilt p A) :=
      uniformTilt.isTopologicallyNilpotent_iff_coeff_zero.mpr hnilA
    have hnilR : IsTopologicallyNilpotent (e (w.coeff 0 : uniformTilt p A)) :=
      hnilTilt.map he_cont
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (mem_topologicallyNilpotentIdeal.mpr hnilR)
  let ψ : powerBoundedSubring A →+* CanonicalReduction R :=
    (Ideal.Quotient.lift (RingHom.ker Θ) ψ₀ fun _ ha ↦
      (RingHom.mem_ker.mp (hker_le ha))).comp
      (RingHom.quotientKerEquivOfSurjective hΘ_surj).symm.toRingHom
  have hψ_Θ (w : WittVector p B₀) : ψ (Θ w) = ψ₀ w := by
    change Ideal.Quotient.lift (RingHom.ker Θ) ψ₀ (fun _ ha ↦ RingHom.mem_ker.mp (hker_le ha))
      ((RingHom.quotientKerEquivOfSurjective hΘ_surj).symm (Θ w)) = ψ₀ w
    have hmk : (RingHom.quotientKerEquivOfSurjective hΘ_surj).symm (Θ w) =
        Ideal.Quotient.mk (RingHom.ker Θ) w := by
      apply (RingHom.quotientKerEquivOfSurjective hΘ_surj).injective
      rw [RingEquiv.apply_symm_apply]
      rfl
    rw [hmk, Ideal.Quotient.lift_mk]
  -- Pull back integral closedness of `P.plus` through `CanonicalReduction R`.
  let DR := P.plus.comap (powerBoundedSubring R).subtype
  have hkerR : (RingHom.ker qR : Set (powerBoundedSubring R)) ⊆ DR := fun b hb ↦
    P.isRingOfIntegralElements.mem_of_isTopologicallyNilpotent
      (mem_topologicallyNilpotentIdeal.mp (Ideal.Quotient.eq_zero_iff_mem.mp hb))
  have := P.isRingOfIntegralElements.isIntegrallyClosedIn
  have hDR : IsIntegrallyClosedIn (DR.map qR) (CanonicalReduction R) :=
    DR.isIntegrallyClosedIn_map_of_ker_le qR Ideal.Quotient.mk_surjective hkerR
  have hψ_mem (b : powerBoundedSubring A) :
      ψ b ∈ DR.map qR ↔ (b : A) ∈ untiltPlus p P J := by
    obtain ⟨w, rfl⟩ := hΘ_surj b
    rw [hψ_Θ, theta_mem_untiltPlus_iff hξ]
    change qR (ePB (w.coeff 0)) ∈ DR.map qR ↔ _
    rw [← Subring.mem_comap, Subring.comap_map_eq_self hkerR]
    rfl
  let gA : untiltPlus p P J →+* DR.map qR :=
    (ψ.comp ((untiltPlus p P J).inclusion hplus_le)).codRestrict (DR.map qR) fun a ↦
      (hψ_mem _).mpr a.property
  refine Subring.isIntegrallyClosedIn_iff.mpr fun x hx ↦ ?_
  have hxpb : IsIntegral (powerBoundedSubring A) x :=
    RingHom.IsIntegralElem.of_comp (f := (untiltPlus p P J).inclusion hplus_le) hx
  have hx0 : x ∈ powerBoundedSubring A :=
    Subring.isIntegrallyClosedIn_iff.mp hPB.isIntegrallyClosedIn hxpb
  let y : powerBoundedSubring A := ⟨x, hx0⟩
  have hy : ((untiltPlus p P J).inclusion hplus_le).IsIntegralElem y :=
    RingHom.IsIntegralElem.of_map (powerBoundedSubring A).subtype_injective hx
  have hψy : IsIntegral (DR.map qR) (ψ y) :=
    RingHom.IsIntegralElem.of_comp (f := gA) (hy.map ψ)
  exact (hψ_mem y).mp (Subring.isIntegrallyClosedIn_iff.mp hDR hψy)

/-- **`A⁺` is a ring of integral elements of the untilt `A`** for a primitive element `ξ`. -/
theorem isRingOfIntegralElements_untiltPlus (hξ : ξ.IsPrimitive) :
    IsRingOfIntegralElements (untiltPlus p P (Ideal.span {ξ})) where
  isOpen := isOpen_untiltPlus
  isIntegrallyClosedIn := isIntegrallyClosedIn_untiltPlus hξ
  le_powerBoundedSubring := fun _ hx ↦
    mem_powerBoundedSubring.mpr (isBounded_untiltPlus.isPowerBounded_of_mem hx)

/-- **The untilt Huber pair `(A, A⁺)`** along a primitive element `ξ`. -/
noncomputable def pair (hξ : ξ.IsPrimitive) : Pair (untilt p P (Ideal.span {ξ})) where
  plus := untiltPlus p P (Ideal.span {ξ})
  isRingOfIntegralElements := isRingOfIntegralElements_untiltPlus hξ

/-- The plus ring of `untilt.pair` is `untiltPlus`. -/
@[simp]
theorem pair_plus (hξ : ξ.IsPrimitive) :
    (pair hξ).plus = untiltPlus p P (Ideal.span {ξ}) := by
  rfl

/-- An element of `A♭` lies in `(untilt.pair hξ).tilt.plus` iff its image under `tiltEquiv` lies
in `P.plus`. -/
theorem mem_tilt_plus_iff (hξ : ξ.IsPrimitive)
    (y : uniformTilt p (untilt p P (Ideal.span {ξ}))) :
    letI := t2Space hξ
    letI := completeSpace hξ
    letI := isUniform hξ
    letI : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
      ⟨isTopologicallyNilpotent_natCast hξ⟩
    letI := isTateRing_uniformTilt hξ
    y ∈ ((pair hξ).tilt (p := p)).plus ↔ tiltEquiv hξ y ∈ P.plus := by
  have := t2Space hξ
  have := completeSpace hξ
  have := isUniform hξ
  have : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
    ⟨isTopologicallyNilpotent_natCast hξ⟩
  have := isTateRing_uniformTilt hξ
  rw [Pair.tilt_plus, uniformTilt.mem_plusSubring_iff_coeff_zero, ← sharp_tiltEquiv hξ y,
    pair_plus, sharp_mem_untiltPlus_iff hξ]

/-- **Identification of the tilted plus ring `A♭⁺` with `R⁺`**. -/
noncomputable def tiltPlusEquiv (hξ : ξ.IsPrimitive) :
    letI := t2Space hξ
    letI := completeSpace hξ
    letI := isUniform hξ
    letI : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
      ⟨isTopologicallyNilpotent_natCast hξ⟩
    letI := isTateRing_uniformTilt hξ
    uniformTilt.plusSubring p (isRingOfIntegralElements_untiltPlus hξ) ≃+* P.plus :=
  letI := t2Space hξ
  letI := completeSpace hξ
  letI := isUniform hξ
  letI : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
    ⟨isTopologicallyNilpotent_natCast hξ⟩
  letI := isTateRing_uniformTilt hξ
  (tiltEquiv hξ).restrict (uniformTilt.plusSubring p (isRingOfIntegralElements_untiltPlus hξ))
    P.plus fun y ↦ by
      rw [uniformTilt.mem_plusSubring_iff_coeff_zero, ← sharp_tiltEquiv hξ y,
        sharp_mem_untiltPlus_iff hξ]

/-- `tiltPlusEquiv` is the restriction of `tiltEquiv`. -/
@[simp]
theorem coe_tiltPlusEquiv (hξ : ξ.IsPrimitive)
    (y : letI := t2Space hξ
      letI := completeSpace hξ
      letI := isUniform hξ
      letI : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
        ⟨isTopologicallyNilpotent_natCast hξ⟩
      letI := isTateRing_uniformTilt hξ
      uniformTilt.plusSubring p (isRingOfIntegralElements_untiltPlus hξ)) :
    letI := t2Space hξ
    letI := completeSpace hξ
    letI := isUniform hξ
    letI : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
      ⟨isTopologicallyNilpotent_natCast hξ⟩
    letI := isTateRing_uniformTilt hξ
    (tiltPlusEquiv hξ y : R) = tiltEquiv hξ y := by
  rfl

/-- `tiltPlusEquiv.symm` is the restriction of `tiltEquiv.symm`. -/
@[simp]
theorem coe_tiltPlusEquiv_symm (hξ : ξ.IsPrimitive) (a : P.plus) :
    letI := t2Space hξ
    letI := completeSpace hξ
    letI := isUniform hξ
    letI : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
      ⟨isTopologicallyNilpotent_natCast hξ⟩
    letI := isTateRing_uniformTilt hξ
    ((tiltPlusEquiv hξ).symm a : uniformTilt p (untilt p P (Ideal.span {ξ}))) =
      (tiltEquiv hξ).symm a := by
  have := t2Space hξ
  have := completeSpace hξ
  have := isUniform hξ
  have : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
    ⟨isTopologicallyNilpotent_natCast hξ⟩
  have := isTateRing_uniformTilt hξ
  apply (tiltEquiv hξ).injective
  rw [(tiltEquiv hξ).apply_symm_apply, ← coe_tiltPlusEquiv hξ,
    (tiltPlusEquiv hξ).apply_symm_apply]

/-- **Identification of `PreTilt A⁺ p` with `R⁺`**. -/
noncomputable def preTiltEquiv (hξ : ξ.IsPrimitive)
    [Fact ¬IsUnit (p : untiltPlus p P (Ideal.span {ξ}))] :
    PreTilt (untiltPlus p P (Ideal.span {ξ})) p ≃+* P.plus :=
  letI := t2Space hξ
  letI := completeSpace hξ
  letI := isUniform hξ
  letI : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
    ⟨isTopologicallyNilpotent_natCast hξ⟩
  letI := isTateRing_uniformTilt hξ
  (uniformTilt.plusEquivPreTilt p (isRingOfIntegralElements_untiltPlus hξ)).symm.trans
    (tiltPlusEquiv hξ)

/-! ### Fontaine's `θ` and `ker θ = (ξ)` -/

section Theta

/-- **Fontaine's `θ_A` coincides with the quotient map `𝕎 R⁺ → A⁺`** under `A♭⁺ ≃+* R⁺`. -/
theorem theta_comp_map_tiltPlusEquiv_symm (hξ : ξ.IsPrimitive)
    [Nontrivial (untilt p P (Ideal.span {ξ}))] :
    letI := t2Space hξ
    letI := completeSpace hξ
    letI := isUniform hξ
    letI : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
      ⟨isTopologicallyNilpotent_natCast hξ⟩
    letI := isTateRing_uniformTilt hξ
    (uniformTilt.theta p (isRingOfIntegralElements_untiltPlus hξ)).comp
        (WittVector.map (tiltPlusEquiv hξ).symm.toRingHom) =
      (quotientEquivUntiltPlus hξ).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {ξ})) := by
  have := t2Space hξ
  have := completeSpace hξ
  have := isUniform hξ
  have : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
    ⟨isTopologicallyNilpotent_natCast hξ⟩
  have := isTateRing_uniformTilt hξ
  have := (isRingOfIntegralElements_untiltPlus hξ).isAdicComplete_span_natCast p
    (isTopologicallyNilpotent_natCast hξ)
  refine WittVector.ringHom_ext_teichmuller fun a ↦ Subtype.ext ?_
  simp only [RingHom.comp_apply, WittVector.map_teichmuller, uniformTilt.theta_teichmuller,
    uniformTilt.coe_plusSharp]
  change uniformTilt.coeff p (untilt p P (Ideal.span {ξ})) 0 ((tiltPlusEquiv hξ).symm a) =
    (quotientEquivUntiltPlus hξ (Ideal.Quotient.mk (Ideal.span {ξ}) (teichmuller p a)) : _)
  rw [quotientEquivUntiltPlus_mk_teichmuller, coe_tiltPlusEquiv_symm, coeff_tiltEquiv_symm,
    iterateFrobeniusEquiv_zero_symm_eq]

/-- The kernel of `θ_A ∘ 𝕎 (tiltPlusEquiv.symm)` is `(ξ)`. -/
theorem ker_theta_comp_map_tiltPlusEquiv_symm (hξ : ξ.IsPrimitive)
    [Nontrivial (untilt p P (Ideal.span {ξ}))] :
    letI := t2Space hξ
    letI := completeSpace hξ
    letI := isUniform hξ
    letI : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
      ⟨isTopologicallyNilpotent_natCast hξ⟩
    letI := isTateRing_uniformTilt hξ
    RingHom.ker ((uniformTilt.theta p (isRingOfIntegralElements_untiltPlus hξ)).comp
        (WittVector.map (tiltPlusEquiv hξ).symm.toRingHom)) =
      Ideal.span {ξ} := by
  have := t2Space hξ
  have := completeSpace hξ
  have := isUniform hξ
  have : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
    ⟨isTopologicallyNilpotent_natCast hξ⟩
  have := isTateRing_uniformTilt hξ
  rw [theta_comp_map_tiltPlusEquiv_symm hξ,
    RingHom.ker_comp_of_injective _ (quotientEquivUntiltPlus hξ).injective, Ideal.mk_ker]

/-- **`ker θ_A = (ξ)`** under the Witt-vector isomorphism `𝕎(A♭⁺) ≃+* 𝕎(R⁺)` induced by
`tiltPlusEquiv`. -/
theorem ker_theta_eq (hξ : ξ.IsPrimitive) [Nontrivial (untilt p P (Ideal.span {ξ}))] :
    letI := t2Space hξ
    letI := completeSpace hξ
    letI := isUniform hξ
    letI : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
      ⟨isTopologicallyNilpotent_natCast hξ⟩
    letI := isTateRing_uniformTilt hξ
    (RingHom.ker (uniformTilt.theta p (isRingOfIntegralElements_untiltPlus hξ))).map
        (WittVector.map (tiltPlusEquiv hξ).toRingHom) =
      Ideal.span {ξ} := by
  have := t2Space hξ
  have := completeSpace hξ
  have := isUniform hξ
  have : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
    ⟨isTopologicallyNilpotent_natCast hξ⟩
  have := isTateRing_uniformTilt hξ
  let eW : WittVector p (uniformTilt.plusSubring p (isRingOfIntegralElements_untiltPlus hξ)) ≃+*
      WittVector p P.plus :=
    RingEquiv.ofRingHom (WittVector.map (tiltPlusEquiv hξ).toRingHom)
      (WittVector.map (tiltPlusEquiv hξ).symm.toRingHom)
      (RingHom.ext fun w ↦ WittVector.ext fun n ↦ by simp)
      (RingHom.ext fun w ↦ WittVector.ext fun n ↦ by simp)
  change (RingHom.ker (uniformTilt.theta p (isRingOfIntegralElements_untiltPlus hξ))).map
      (eW : _ →+* _) = Ideal.span {ξ}
  rw [Ideal.map_comap_of_equiv eW, ← Ideal.comap_coe, RingHom.comap_ker]
  exact ker_theta_comp_map_tiltPlusEquiv_symm hξ

/-- Mathlib's `WittVector.fontaineTheta` on `A⁺` coincides with the quotient map `𝕎 R⁺ → A⁺`
under `preTiltEquiv : PreTilt A⁺ p ≃+* R⁺`. -/
theorem fontaineTheta_comp_map_preTiltEquiv_symm (hξ : ξ.IsPrimitive)
    [Fact ¬IsUnit (p : untiltPlus p P (Ideal.span {ξ}))]
    [IsAdicComplete (Ideal.span {(p : untiltPlus p P (Ideal.span {ξ}))})
      (untiltPlus p P (Ideal.span {ξ}))] :
    (WittVector.fontaineTheta (untiltPlus p P (Ideal.span {ξ})) p).comp
        (WittVector.map (preTiltEquiv hξ).symm.toRingHom) =
      (quotientEquivUntiltPlus hξ).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {ξ})) := by
  have := t2Space hξ
  have := completeSpace hξ
  have := isUniform hξ
  have : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
    ⟨isTopologicallyNilpotent_natCast hξ⟩
  have := isTateRing_uniformTilt hξ
  have : Nontrivial (untilt p P (Ideal.span {ξ})) := by
    by_contra hnot
    rw [not_nontrivial_iff_subsingleton] at hnot
    exact (Fact.out : ¬IsUnit (p : untiltPlus p P (Ideal.span {ξ}))) (isUnit_of_subsingleton _)
  have hcomp : WittVector.map (p := p) (preTiltEquiv hξ).symm.toRingHom =
      (WittVector.map (p := p) (uniformTilt.plusEquivPreTilt p
          (isRingOfIntegralElements_untiltPlus hξ)).toRingHom).comp
        (WittVector.map (p := p) (tiltPlusEquiv hξ).symm.toRingHom) :=
    RingHom.ext fun w ↦ WittVector.ext fun n ↦ by simp [preTiltEquiv]
  rw [hcomp, ← RingHom.comp_assoc, ← uniformTilt.theta_eq_fontaineTheta,
    theta_comp_map_tiltPlusEquiv_symm hξ]

/-- **`ker (WittVector.fontaineTheta A⁺ p) = (ξ)`** under `preTiltEquiv : PreTilt A⁺ p ≃+* R⁺`. -/
theorem ker_fontaineTheta_eq (hξ : ξ.IsPrimitive)
    [Fact ¬IsUnit (p : untiltPlus p P (Ideal.span {ξ}))]
    [IsAdicComplete (Ideal.span {(p : untiltPlus p P (Ideal.span {ξ}))})
      (untiltPlus p P (Ideal.span {ξ}))] :
    (RingHom.ker (WittVector.fontaineTheta (untiltPlus p P (Ideal.span {ξ})) p)).map
        (WittVector.map (preTiltEquiv hξ).toRingHom) =
      Ideal.span {ξ} := by
  let eW : WittVector p (PreTilt (untiltPlus p P (Ideal.span {ξ})) p) ≃+* WittVector p P.plus :=
    RingEquiv.ofRingHom (WittVector.map (preTiltEquiv hξ).toRingHom)
      (WittVector.map (preTiltEquiv hξ).symm.toRingHom)
      (RingHom.ext fun w ↦ WittVector.ext fun n ↦ by simp)
      (RingHom.ext fun w ↦ WittVector.ext fun n ↦ by simp)
  change (RingHom.ker (WittVector.fontaineTheta (untiltPlus p P (Ideal.span {ξ})) p)).map
      (eW : _ →+* _) = Ideal.span {ξ}
  rw [Ideal.map_comap_of_equiv eW, ← Ideal.comap_coe, RingHom.comap_ker]
  change RingHom.ker ((WittVector.fontaineTheta (untiltPlus p P (Ideal.span {ξ})) p).comp
      (WittVector.map (preTiltEquiv hξ).symm.toRingHom)) = Ideal.span {ξ}
  rw [fontaineTheta_comp_map_preTiltEquiv_symm hξ,
    RingHom.ker_comp_of_injective _ (quotientEquivUntiltPlus hξ).injective, Ideal.mk_ker]

end Theta

/-! ### Almost vanishing of `A° ⧸ A⁺` -/

/-- **`A° ⧸ A⁺` is almost zero** for the almost setup `(A⁺, A°°)` of the untilt along a primitive
element `ξ`. -/
theorem isAlmostZero_powerBounded_quotient (hξ : ξ.IsPrimitive)
    [Algebra (untiltPlus p P (Ideal.span {ξ}))
      (powerBoundedSubring (untilt p P (Ideal.span {ξ})))]
    [IsScalarTower (untiltPlus p P (Ideal.span {ξ}))
      (powerBoundedSubring (untilt p P (Ideal.span {ξ}))) (untilt p P (Ideal.span {ξ}))] :
    letI : Fact (1 < p) := ⟨hp.out.one_lt⟩
    letI := t2Space hξ
    letI := completeSpace hξ
    letI := isPerfectoidTateRing hξ
    letI : Nonempty (PseudoUniformizerRoots p (untilt p P (Ideal.span {ξ}))) :=
      PseudoUniformizerRoots.nonempty
    (almostSetupPlus p (untilt p P (Ideal.span {ξ}))
        (isRingOfIntegralElements_untiltPlus hξ)).IsAlmostZero
      (powerBoundedSubring (untilt p P (Ideal.span {ξ})) ⧸
        LinearMap.range (Algebra.linearMap (untiltPlus p P (Ideal.span {ξ}))
          (powerBoundedSubring (untilt p P (Ideal.span {ξ}))))) := by
  have : Fact (1 < p) := ⟨hp.out.one_lt⟩
  have := t2Space hξ
  have := completeSpace hξ
  have := isPerfectoidTateRing hξ
  have : Nonempty (PseudoUniformizerRoots p (untilt p P (Ideal.span {ξ}))) :=
    PseudoUniformizerRoots.nonempty
  exact almostSetupPlus_isAlmostZero_powerBounded_quotient
    (isRingOfIntegralElements_untiltPlus hξ)

end TauCeti.Perfectoid.untilt
