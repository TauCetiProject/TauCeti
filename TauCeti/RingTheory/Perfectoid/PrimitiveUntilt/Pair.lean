/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.PrimitiveUntilt.Perfectoid
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Pair
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Theta

import Mathlib.Algebra.CharP.Subring
import TauCeti.RingTheory.Huber.OpenIdeal
import TauCeti.RingTheory.Huber.Pair.Complete
import TauCeti.RingTheory.Huber.Reduction
import TauCeti.RingTheory.Perfectoid.Pair
import TauCeti.RingTheory.WittVector.MapEquiv
import TauCeti.RingTheory.WittVector.TeichmullerCoeff

/-!
# The Huber pair structure and Fontaine kernel of primitive untilts

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

## Main definitions

* `TauCeti.Perfectoid.untilt.pair`: the untilt as a `Huber.Pair A` with plus ring `A⁺`.
* `TauCeti.Perfectoid.untilt.tiltPlusEquiv`: the ring isomorphism `A♭⁺ ≃+* R⁺`.
* `TauCeti.Perfectoid.untilt.preTiltEquiv`: the ring isomorphism `PreTilt A⁺ p ≃+* R⁺`.

## Main results

* `TauCeti.Perfectoid.untilt.isIntegrallyClosedIn_untiltPlus`,
  `TauCeti.Perfectoid.untilt.isRingOfIntegralElements_untiltPlus`: `A⁺` is a ring of integral
  elements of `A`.
* `TauCeti.Perfectoid.untilt.mem_tilt_plus_iff`:
  `y ∈ (untilt.pair hξ).tilt.plus ↔ tiltEquiv y ∈ R⁺`.
* `TauCeti.Perfectoid.untilt.ker_theta_eq`, `TauCeti.Perfectoid.untilt.ker_fontaineTheta_eq`:
  under the identification `A♭⁺ ≃+* R⁺` (resp. `PreTilt A⁺ p ≃+* R⁺`), `ker θ = (ξ)`.

## References

* P. Scholze, *Étale cohomology of diamonds*, Theorem 3.17.
* P. Scholze and J. Weinstein, *Berkeley lectures on `p`-adic geometry*, Theorem 6.2.11.
* K. S. Kedlaya, *Nonarchimedean geometry of Witt vectors and the tilting equivalence*,
  Arizona Winter School 2017, Lemmas 2.6.14 and 2.7.9.
* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, Theorem 2.3.9.
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

/-! ### Integral closedness of `A⁺` and the untilt Huber pair -/

omit [IsUniformAddGroup R] [CompleteSpace R] [T2Space R] [CharP R p] [PerfectRing R p] in
private theorem untiltPlus_le_powerBoundedSubring (J : Ideal (WittVector p P.plus)) :
    untiltPlus p P J ≤ powerBoundedSubring (untilt p P J) := fun _ hx ↦
  mem_powerBoundedSubring.mpr (isBounded_untiltPlus.isPowerBounded_of_mem hx)

private theorem tiltEquiv_mem_powerBoundedSubring [Fact ξ.IsPrimitive]
    (b : uniformTilt.plusSubring p
      (isRingOfIntegralElements_powerBoundedSubring (untilt p P (Ideal.span {ξ})))) :
    tiltEquiv (p := p) (P := P) (ξ := ξ) b ∈ powerBoundedSubring R :=
  mem_powerBoundedSubring.mpr <|
    (mem_powerBoundedSubring.mp (uniformTilt.plusSubring_le_powerBoundedSubring _
      b.property)).map_of_isTateRing
        (f := (tiltEquiv (p := p) (P := P) (ξ := ξ)).toRingHom)
        (isHomeomorph_tiltEquiv (p := p) (P := P) (ξ := ξ)).continuous.continuousAt

private noncomputable def liftToTiltPowerBounded [hξ : Fact ξ.IsPrimitive] :
    P.plus →+* uniformTilt.plusSubring p
      (isRingOfIntegralElements_powerBoundedSubring (untilt p P (Ideal.span {ξ}))) :=
  ((tiltEquiv (p := p) (P := P) (ξ := ξ)).symm.toRingHom.comp P.plus.subtype).codRestrict _
    fun a ↦ uniformTilt.mem_plusSubring_iff_coeff_zero.mpr <|
      untiltPlus_le_powerBoundedSubring _ <| by
        rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
          Subring.coe_subtype, coeff_tiltEquiv_symm, iterateFrobeniusEquiv_zero,
          RingEquiv.symm_refl, RingEquiv.refl_apply]
        exact sharp_mem_untiltPlus a

private theorem tiltEquiv_liftToTiltPowerBounded [Fact ξ.IsPrimitive] (a : P.plus) :
    tiltEquiv (p := p) (P := P) (ξ := ξ)
      ((liftToTiltPowerBounded (p := p) (P := P) (ξ := ξ) a : _)) = (a : R) := by
  dsimp only [liftToTiltPowerBounded, RingHom.codRestrict_apply, RingHom.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, Subring.coe_subtype]
  exact (tiltEquiv (p := p) (P := P) (ξ := ξ)).apply_symm_apply _

private theorem theta_map_liftToTiltPowerBounded [hξ : Fact ξ.IsPrimitive]
    [Nontrivial (untilt p P (Ideal.span {ξ}))] (w : WittVector p P.plus) :
    (uniformTilt.theta p (isRingOfIntegralElements_powerBoundedSubring
          (untilt p P (Ideal.span {ξ})))
        (WittVector.map (liftToTiltPowerBounded (p := p) (P := P) (ξ := ξ)) w) :
          untilt p P (Ideal.span {ξ})) =
      algebraMap (WittVector p P.plus ⧸ Ideal.span {ξ}) (untilt p P (Ideal.span {ξ}))
        (Ideal.Quotient.mk (Ideal.span {ξ}) w) := by
  let J := Ideal.span {ξ}
  let A := untilt p P J
  let hPB := isRingOfIntegralElements_powerBoundedSubring A
  have := hPB.isAdicComplete_span_natCast p (isTopologicallyNilpotent_natCast hξ.out)
  let Φ : WittVector p P.plus →+* powerBoundedSubring A :=
    ((algebraMap (WittVector p P.plus ⧸ J) A).comp (Ideal.Quotient.mk J)).codRestrict
      (powerBoundedSubring A) fun _ ↦
        untiltPlus_le_powerBoundedSubring J (mem_untiltPlus.mpr ⟨_, rfl⟩)
  have heq : (uniformTilt.theta p hPB).comp
      (WittVector.map (liftToTiltPowerBounded (p := p) (P := P) (ξ := ξ))) = Φ :=
    WittVector.ringHom_ext_teichmuller fun a ↦ Subtype.ext <| by
      rw [RingHom.comp_apply, WittVector.map_teichmuller, uniformTilt.theta_teichmuller,
        uniformTilt.coe_plusSharp, ← sharp_tiltEquiv, tiltEquiv_liftToTiltPowerBounded,
        sharp_apply]
      rfl
  exact congrArg Subtype.val (RingHom.congr_fun heq w)

private theorem theta_natCast_mul_mem_untiltPlus [hξ : Fact ξ.IsPrimitive]
    [Nontrivial (untilt p P (Ideal.span {ξ}))]
    (w₁ : WittVector p (uniformTilt.plusSubring p
      (isRingOfIntegralElements_powerBoundedSubring (untilt p P (Ideal.span {ξ}))))) :
    (uniformTilt.theta p (isRingOfIntegralElements_powerBoundedSubring
          (untilt p P (Ideal.span {ξ})))
        ((p : WittVector p _) * w₁) : untilt p P (Ideal.span {ξ})) ∈
      untiltPlus p P (Ideal.span {ξ}) := by
  let J := Ideal.span {ξ}
  let A := untilt p P J
  let hPB := isRingOfIntegralElements_powerBoundedSubring A
  let B₀ := uniformTilt.plusSubring p hPB
  let Θ : WittVector p B₀ →+* powerBoundedSubring A := uniformTilt.theta p hPB
  let ι := liftToTiltPowerBounded (p := p) (P := P) (ξ := ξ)
  let e := tiltEquiv (p := p) (P := P) (ξ := ξ)
  -- Express `Θ p` in terms of `Θ [ι ξ₀]` using `ξ = [ξ₀] + p * u`.
  obtain ⟨u, hu⟩ := isDistinguished_iff_exists_unit.mp hξ.out.isDistinguished
  let u' : (WittVector p B₀)ˣ := Units.map (WittVector.map ι).toMonoidHom u
  have hξ'_zero : Θ (WittVector.map ι ξ) = 0 := Subtype.ext <| by
    rw [theta_map_liftToTiltPowerBounded, Ideal.Quotient.mk_singleton_self, map_zero,
      ZeroMemClass.coe_zero]
  have hp_eq : Θ (p : WittVector p B₀) =
      -Θ (teichmuller p (ι (ξ.coeff 0)) * (↑u'⁻¹ : WittVector p B₀)) := by
    have h1 : Θ (teichmuller p (ι (ξ.coeff 0))) + Θ (p : WittVector p B₀) * Θ ↑u' = 0 := by
      have hu'val : (u' : WittVector p B₀) = WittVector.map ι ↑u := rfl
      rw [hu'val, ← map_mul, ← map_add, ← WittVector.map_teichmuller,
        ← map_natCast (WittVector.map ι), ← map_mul, ← map_add, ← hu, hξ'_zero]
    have hu' : Θ ↑u' * Θ ↑u'⁻¹ = 1 := by rw [← map_mul, u'.mul_inv, map_one]
    rw [map_mul]
    linear_combination Θ ↑u'⁻¹ * h1 - Θ (p : WittVector p B₀) * hu'
  -- Pull `z := [ι ξ₀] * (u'⁻¹ * w₁)` back to `𝕎 R⁺` via `e`; its coordinates lie in `R⁺` since
  -- `ξ₀` is topologically nilpotent and `e b ∈ R°`.
  set z : WittVector p B₀ := teichmuller p (ι (ξ.coeff 0)) * ((↑u'⁻¹ : WittVector p B₀) * w₁)
  have hcoeff_mem (i : ℕ) : e (z.coeff i : uniformTilt p A) ∈ P.plus := by
    have htc : z.coeff i =
        (ι (ξ.coeff 0)) ^ p ^ i * (((↑u'⁻¹ : WittVector p B₀) * w₁).coeff i) := by
      rw [← teichmullerCoeff_pow, teichmullerCoeff_teichmuller_mul, mul_pow, teichmullerCoeff_pow]
    rw [htc, Subring.coe_mul, Subring.coe_pow, map_mul, map_pow, tiltEquiv_liftToTiltPowerBounded]
    have hnil : IsTopologicallyNilpotent ((ξ.coeff 0 : R) ^ p ^ i) :=
      (hξ.out.isTopologicallyNilpotent_coeff_zero.map (φ := P.plus.subtype)
        continuous_subtypeVal).pow (pow_ne_zero i hp.out.ne_zero)
    rw [mul_comm]
    exact P.isRingOfIntegralElements.mem_of_isTopologicallyNilpotent
      ((mem_powerBoundedSubring.mp
        (tiltEquiv_mem_powerBoundedSubring _)).isTopologicallyNilpotent_mul hnil)
  let z₀ : WittVector p P.plus :=
    WittVector.mk p fun i ↦ ⟨e (z.coeff i : uniformTilt p A), hcoeff_mem i⟩
  have hz_eq : WittVector.map ι z₀ = z :=
    WittVector.ext fun i ↦ Subtype.ext <| e.injective <| by
      rw [WittVector.map_coeff, tiltEquiv_liftToTiltPowerBounded]
  have hval : Θ ((p : WittVector p B₀) * w₁) = -Θ z := by
    rw [map_mul, hp_eq, neg_mul, ← map_mul, mul_assoc]
  rw [hval, Subring.coe_neg, ← hz_eq, theta_map_liftToTiltPowerBounded]
  exact neg_mem (mem_untiltPlus.mpr ⟨_, rfl⟩)

/-- For Fontaine's map `Θ : 𝕎((A♭)°) → A°`, we have `Θ w ∈ A⁺ ↔ tiltEquiv (w.coeff 0) ∈ R⁺`. -/
private theorem theta_mem_untiltPlus_iff [hξ : Fact ξ.IsPrimitive]
    [Nontrivial (untilt p P (Ideal.span {ξ}))]
    (w : WittVector p (uniformTilt.plusSubring p
      (isRingOfIntegralElements_powerBoundedSubring (untilt p P (Ideal.span {ξ}))))) :
    (uniformTilt.theta p
      (isRingOfIntegralElements_powerBoundedSubring (untilt p P (Ideal.span {ξ}))) w :
        untilt p P (Ideal.span {ξ})) ∈ untiltPlus p P (Ideal.span {ξ}) ↔
      tiltEquiv (p := p) (P := P) (ξ := ξ)
        (w.coeff 0 : uniformTilt p (untilt p P (Ideal.span {ξ}))) ∈ P.plus := by
  -- Decompose `w = [w₀] + p * w₁`: the remainder `Θ (p * w₁)` lies in `A⁺`, leaving
  -- `Θ [w₀] = ♯(e w₀) ∈ A⁺ ↔ e w₀ ∈ R⁺`.
  obtain ⟨w₁, hw₁⟩ := exists_eq_sum_teichmullerCoeff_add_pow_mul w 1
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one, pow_one,
    teichmullerCoeff_zero] at hw₁
  conv_lhs =>
    rw [hw₁, map_add, Subring.coe_add, uniformTilt.theta_teichmuller, uniformTilt.coe_plusSharp,
      ← sharp_tiltEquiv]
  rw [add_mem_cancel_right (theta_natCast_mul_mem_untiltPlus w₁), sharp_mem_untiltPlus_iff hξ.out]

/-- **`A⁺` is integrally closed in the untilt `A`** for a primitive element `ξ`. -/
theorem isIntegrallyClosedIn_untiltPlus (hξ : ξ.IsPrimitive) :
    IsIntegrallyClosedIn (untiltPlus p P (Ideal.span {ξ})) (untilt p P (Ideal.span {ξ})) := by
  set J := Ideal.span {ξ}
  set A := untilt p P J
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subring.isIntegrallyClosedIn_iff.mpr fun x _ ↦
      Subsingleton.elim x 0 ▸ zero_mem _
  have : Fact ξ.IsPrimitive := ⟨hξ⟩
  have := isPerfectoidTateRing (p := p) (P := P) (ξ := ξ)
  let hPB := isRingOfIntegralElements_powerBoundedSubring A
  let B₀ := uniformTilt.plusSubring p hPB
  let Θ : WittVector p B₀ →+* powerBoundedSubring A := uniformTilt.theta p hPB
  let e := tiltEquiv (p := p) (P := P) (ξ := ξ)
  have hΘ_surj : Function.Surjective Θ :=
    uniformTilt.surjective_theta hPB
      (IsPerfectoidTateRing.exists_natCast_dvd_sub_pow (p := p) (R := A))
  -- Descend `w ↦ mk (topologicallyNilpotentIdeal R) (e (w.coeff 0))` along `Θ` to
  -- `A° →+* R° ⧸ R°°`.
  let qR := Ideal.Quotient.mk (topologicallyNilpotentIdeal R)
  let ePB : B₀ →+* powerBoundedSubring R :=
    (e.toRingHom.comp B₀.subtype).codRestrict (powerBoundedSubring R)
      tiltEquiv_mem_powerBoundedSubring
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
      hnilTilt.map (isHomeomorph_tiltEquiv (p := p) (P := P) (ξ := ξ)).continuous
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (mem_topologicallyNilpotentIdeal.mpr hnilR)
  let ψ : powerBoundedSubring A →+* CanonicalReduction R :=
    (Ideal.Quotient.lift (RingHom.ker Θ) ψ₀ fun _ ha ↦
      (RingHom.mem_ker.mp (hker_le ha))).comp
      (RingHom.quotientKerEquivOfSurjective hΘ_surj).symm.toRingHom
  have hψ_Θ (w : WittVector p B₀) : ψ (Θ w) = ψ₀ w := by
    dsimp only [ψ]
    have hmk : (RingHom.quotientKerEquivOfSurjective hΘ_surj).symm (Θ w) =
        Ideal.Quotient.mk (RingHom.ker Θ) w := by
      apply (RingHom.quotientKerEquivOfSurjective hΘ_surj).injective
      rw [RingEquiv.apply_symm_apply]
      rfl
    rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hmk,
      Ideal.Quotient.lift_mk]
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
    rw [hψ_Θ, theta_mem_untiltPlus_iff]
    dsimp only [ψ₀, RingHom.comp_apply, constantCoeff_apply]
    rw [← Subring.mem_comap, Subring.comap_map_eq_self hkerR]
    rfl
  let gA : untiltPlus p P J →+* DR.map qR :=
    (ψ.comp ((untiltPlus p P J).inclusion (untiltPlus_le_powerBoundedSubring J))).codRestrict
      (DR.map qR) fun a ↦ (hψ_mem _).mpr a.property
  refine Subring.isIntegrallyClosedIn_iff.mpr fun x hx ↦ ?_
  have hxpb : IsIntegral (powerBoundedSubring A) x :=
    RingHom.IsIntegralElem.of_comp
      (f := (untiltPlus p P J).inclusion (untiltPlus_le_powerBoundedSubring J)) hx
  have hx0 : x ∈ powerBoundedSubring A :=
    Subring.isIntegrallyClosedIn_iff.mp hPB.isIntegrallyClosedIn hxpb
  let y : powerBoundedSubring A := ⟨x, hx0⟩
  have hy : ((untiltPlus p P J).inclusion
      (untiltPlus_le_powerBoundedSubring J)).IsIntegralElem y :=
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
theorem mem_tilt_plus_iff [hξ : Fact ξ.IsPrimitive]
    (y : uniformTilt p (untilt p P (Ideal.span {ξ}))) :
    y ∈ ((pair hξ.out).tilt (p := p)).plus ↔
      tiltEquiv (p := p) (P := P) (ξ := ξ) y ∈ P.plus := by
  rw [Pair.tilt_plus, uniformTilt.mem_plusSubring_iff_coeff_zero, ← sharp_tiltEquiv y,
    pair_plus, sharp_mem_untiltPlus_iff hξ.out]

/-- **Identification of the tilted plus ring `A♭⁺` with `R⁺`**. -/
noncomputable def tiltPlusEquiv [hξ : Fact ξ.IsPrimitive] :
    uniformTilt.plusSubring p (isRingOfIntegralElements_untiltPlus hξ.out) ≃+* P.plus :=
  (tiltEquiv (p := p) (P := P) (ξ := ξ)).restrict
    (uniformTilt.plusSubring p (isRingOfIntegralElements_untiltPlus hξ.out))
    P.plus fun y ↦ by
      rw [uniformTilt.mem_plusSubring_iff_coeff_zero, ← sharp_tiltEquiv y,
        sharp_mem_untiltPlus_iff hξ.out]

/-- `tiltPlusEquiv` is the restriction of `tiltEquiv`. -/
@[simp]
theorem coe_tiltPlusEquiv [hξ : Fact ξ.IsPrimitive]
    (y : uniformTilt.plusSubring p (isRingOfIntegralElements_untiltPlus hξ.out)) :
    (tiltPlusEquiv (p := p) (P := P) (ξ := ξ) y : R) =
      tiltEquiv (p := p) (P := P) (ξ := ξ) y := by
  rfl

/-- `tiltPlusEquiv.symm` is the restriction of `tiltEquiv.symm`. -/
@[simp]
theorem coe_tiltPlusEquiv_symm [hξ : Fact ξ.IsPrimitive] (a : P.plus) :
    ((tiltPlusEquiv (p := p) (P := P) (ξ := ξ)).symm a :
        uniformTilt p (untilt p P (Ideal.span {ξ}))) =
      (tiltEquiv (p := p) (P := P) (ξ := ξ)).symm a := by
  apply (tiltEquiv (p := p) (P := P) (ξ := ξ)).injective
  rw [(tiltEquiv (p := p) (P := P) (ξ := ξ)).apply_symm_apply, ← coe_tiltPlusEquiv,
    (tiltPlusEquiv (p := p) (P := P) (ξ := ξ)).apply_symm_apply]

/-- **Identification of `PreTilt A⁺ p` with `R⁺`**. -/
noncomputable def preTiltEquiv [hξ : Fact ξ.IsPrimitive]
    [Fact ¬IsUnit (p : untiltPlus p P (Ideal.span {ξ}))] :
    PreTilt (untiltPlus p P (Ideal.span {ξ})) p ≃+* P.plus :=
  (uniformTilt.plusEquivPreTilt p (isRingOfIntegralElements_untiltPlus hξ.out)).symm.trans
    (tiltPlusEquiv (p := p) (P := P) (ξ := ξ))

/-- `preTiltEquiv` sends `x` to `tiltPlusEquiv (plusEquivPreTilt.symm x)`. -/
@[simp]
theorem preTiltEquiv_apply [hξ : Fact ξ.IsPrimitive]
    [Fact ¬IsUnit (p : untiltPlus p P (Ideal.span {ξ}))]
    (x : PreTilt (untiltPlus p P (Ideal.span {ξ})) p) :
    preTiltEquiv (p := p) (P := P) (ξ := ξ) x =
      tiltPlusEquiv
        ((uniformTilt.plusEquivPreTilt p (isRingOfIntegralElements_untiltPlus hξ.out)).symm x) := by
  rfl

/-- `preTiltEquiv.symm` sends `a` to `plusEquivPreTilt (tiltPlusEquiv.symm a)`. -/
@[simp]
theorem preTiltEquiv_symm_apply [hξ : Fact ξ.IsPrimitive]
    [Fact ¬IsUnit (p : untiltPlus p P (Ideal.span {ξ}))] (a : P.plus) :
    (preTiltEquiv (p := p) (P := P) (ξ := ξ)).symm a =
      uniformTilt.plusEquivPreTilt p (isRingOfIntegralElements_untiltPlus hξ.out)
        ((tiltPlusEquiv (p := p) (P := P) (ξ := ξ)).symm a) := by
  rfl

/-! ### Fontaine's `θ` and `ker θ = (ξ)` -/

section Theta

omit [IsUniformAddGroup R] [CompleteSpace R] [T2Space R] in
private theorem map_ker_eq_span_of_comp_map_symm {S : Type*} [CommRing S]
    (hξ : ξ.IsPrimitive) (e : S ≃+* P.plus)
    (f : WittVector p S →+* untiltPlus p P (Ideal.span {ξ}))
    (hf : f.comp (WittVector.map e.symm.toRingHom) =
      (quotientEquivUntiltPlus hξ).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {ξ}))) :
    (RingHom.ker f).map (WittVector.map e.toRingHom) = Ideal.span {ξ} := by
  let eW := WittVector.mapEquiv (p := p) e
  have hmap : WittVector.map (p := p) e.toRingHom =
      (eW : WittVector p S →+* WittVector p P.plus) :=
    RingHom.ext fun w ↦ (WittVector.mapEquiv_apply e w).symm
  have hsymm : (eW.symm : WittVector p P.plus →+* WittVector p S) =
      WittVector.map e.symm.toRingHom :=
    RingHom.ext fun w ↦ by simp [eW, WittVector.mapEquiv_apply]
  rw [hmap, Ideal.map_comap_of_equiv eW, ← Ideal.comap_coe, RingHom.comap_ker, hsymm, hf,
    RingHom.ker_comp_of_injective _ (quotientEquivUntiltPlus hξ).injective, Ideal.mk_ker]

/-- **Fontaine's `θ_A` coincides with the quotient map `𝕎 R⁺ → A⁺`** under `A♭⁺ ≃+* R⁺`. -/
theorem theta_comp_map_tiltPlusEquiv_symm [hξ : Fact ξ.IsPrimitive]
    [Nontrivial (untilt p P (Ideal.span {ξ}))] :
    (uniformTilt.theta p (isRingOfIntegralElements_untiltPlus hξ.out)).comp
        (WittVector.map (tiltPlusEquiv (p := p) (P := P) (ξ := ξ)).symm.toRingHom) =
      (quotientEquivUntiltPlus hξ.out).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {ξ})) := by
  have := (isRingOfIntegralElements_untiltPlus hξ.out).isAdicComplete_span_natCast p
    (isTopologicallyNilpotent_natCast hξ.out)
  refine WittVector.ringHom_ext_teichmuller fun a ↦ Subtype.ext ?_
  rw [RingHom.comp_apply, WittVector.map_teichmuller, uniformTilt.theta_teichmuller,
    uniformTilt.coe_plusSharp, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    coe_tiltPlusEquiv_symm, coeff_tiltEquiv_symm, iterateFrobeniusEquiv_zero,
    RingEquiv.symm_refl, RingEquiv.refl_apply, RingHom.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, quotientEquivUntiltPlus_mk_teichmuller]

/-- The kernel of `θ_A ∘ 𝕎 (tiltPlusEquiv.symm)` is `(ξ)`. -/
theorem ker_theta_comp_map_tiltPlusEquiv_symm [hξ : Fact ξ.IsPrimitive]
    [Nontrivial (untilt p P (Ideal.span {ξ}))] :
    RingHom.ker ((uniformTilt.theta p (isRingOfIntegralElements_untiltPlus hξ.out)).comp
        (WittVector.map (tiltPlusEquiv (p := p) (P := P) (ξ := ξ)).symm.toRingHom)) =
      Ideal.span {ξ} := by
  rw [theta_comp_map_tiltPlusEquiv_symm,
    RingHom.ker_comp_of_injective _ (quotientEquivUntiltPlus hξ.out).injective, Ideal.mk_ker]

/-- **`ker θ_A = (ξ)`** under the Witt-vector isomorphism `𝕎(A♭⁺) ≃+* 𝕎(R⁺)` induced by
`tiltPlusEquiv`. -/
theorem ker_theta_eq [hξ : Fact ξ.IsPrimitive] [Nontrivial (untilt p P (Ideal.span {ξ}))] :
    (RingHom.ker (uniformTilt.theta p (isRingOfIntegralElements_untiltPlus hξ.out))).map
        (WittVector.map (tiltPlusEquiv (p := p) (P := P) (ξ := ξ)).toRingHom) =
      Ideal.span {ξ} :=
  map_ker_eq_span_of_comp_map_symm hξ.out (tiltPlusEquiv (p := p) (P := P) (ξ := ξ)) _
    (theta_comp_map_tiltPlusEquiv_symm (p := p) (P := P) (ξ := ξ))

/-- Mathlib's `WittVector.fontaineTheta` on `A⁺` coincides with the quotient map `𝕎 R⁺ → A⁺`
under `preTiltEquiv : PreTilt A⁺ p ≃+* R⁺`. -/
theorem fontaineTheta_comp_map_preTiltEquiv_symm [hξ : Fact ξ.IsPrimitive]
    [Fact ¬IsUnit (p : untiltPlus p P (Ideal.span {ξ}))]
    [IsAdicComplete (Ideal.span {(p : untiltPlus p P (Ideal.span {ξ}))})
      (untiltPlus p P (Ideal.span {ξ}))] :
    (WittVector.fontaineTheta (untiltPlus p P (Ideal.span {ξ})) p).comp
        (WittVector.map (preTiltEquiv (p := p) (P := P) (ξ := ξ)).symm.toRingHom) =
      (quotientEquivUntiltPlus hξ.out).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {ξ})) := by
  have : Nontrivial (untilt p P (Ideal.span {ξ})) := by
    by_contra hnot
    rw [not_nontrivial_iff_subsingleton] at hnot
    exact (Fact.out : ¬IsUnit (p : untiltPlus p P (Ideal.span {ξ}))) (isUnit_of_subsingleton _)
  have hcomp :
      WittVector.map (p := p) (preTiltEquiv (p := p) (P := P) (ξ := ξ)).symm.toRingHom =
        (WittVector.map (p := p) (uniformTilt.plusEquivPreTilt p
            (isRingOfIntegralElements_untiltPlus hξ.out)).toRingHom).comp
          (WittVector.map (p := p)
            (tiltPlusEquiv (p := p) (P := P) (ξ := ξ)).symm.toRingHom) :=
    RingHom.ext fun w ↦ WittVector.ext fun n ↦ by simp
  rw [hcomp, ← RingHom.comp_assoc, ← uniformTilt.theta_eq_fontaineTheta,
    theta_comp_map_tiltPlusEquiv_symm]

/-- **`ker (WittVector.fontaineTheta A⁺ p) = (ξ)`** under `preTiltEquiv : PreTilt A⁺ p ≃+* R⁺`. -/
theorem ker_fontaineTheta_eq [hξ : Fact ξ.IsPrimitive]
    [Fact ¬IsUnit (p : untiltPlus p P (Ideal.span {ξ}))]
    [IsAdicComplete (Ideal.span {(p : untiltPlus p P (Ideal.span {ξ}))})
      (untiltPlus p P (Ideal.span {ξ}))] :
    (RingHom.ker (WittVector.fontaineTheta (untiltPlus p P (Ideal.span {ξ})) p)).map
        (WittVector.map (preTiltEquiv (p := p) (P := P) (ξ := ξ)).toRingHom) =
      Ideal.span {ξ} :=
  map_ker_eq_span_of_comp_map_symm hξ.out (preTiltEquiv (p := p) (P := P) (ξ := ξ)) _
    (fontaineTheta_comp_map_preTiltEquiv_symm (p := p) (P := P) (ξ := ξ))

end Theta

end TauCeti.Perfectoid.untilt
