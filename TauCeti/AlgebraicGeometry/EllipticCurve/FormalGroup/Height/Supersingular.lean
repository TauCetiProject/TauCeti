/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Ideal
public import TauCeti.AlgebraicGeometry.EllipticCurve.Supersingular
import Mathlib.RingTheory.Regular.Flat
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Isogeny
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Supersingular
import TauCeti.RingTheory.FormalGroup.NSMul.BaseChange

/-!
# Formal-group height two for elliptic curves and Landweber regularity

Let `W` be an elliptic curve over a field `K` of characteristic `p > 0` (including `p = 2` and
`p = 3`), with formal group `Ê = formalGroup W`. Multiplication by `p` on `W` has degree `p²` and
induces the `p`-series `[p]_Ê(T)`, whose order equals the inseparable degree of `[p]`
(`WeierstrassCurve.order_nsmulSeries_formalGroup`). Since `W` is ordinary when `[p]` has separable
degree `p` and supersingular when `[p]` has separable degree `1`, the inseparable degree of `[p]`
is `p` in the ordinary case and `p²` in the supersingular case. Hence `Ê` has height `1` when `W`
is ordinary and height `2` when `W` is supersingular (Silverman V.3.1), so the formal group of an
elliptic curve never has height exceeding `2`.

Combining this with the congruence modulo `p` between the `Tᵖ`-coefficient of `[p]_Ê` and the
`Tᵖ⁻¹`-coefficient `A` of the invariant differential
(`WeierstrassCurve.height_formalGroup_eq_one_iff`) recovers Deuring's Hasse-invariant criterion
uniformly at every prime `p`, in arbitrary Weierstrass coordinates and over arbitrary (not
necessarily perfect) fields of characteristic `p`: `W` is ordinary exactly when `A ≠ 0` and
supersingular exactly when `A = 0`.

Over an arbitrary commutative ring `R`, base-changing an elliptic Weierstrass curve `W` to residue
fields of characteristic `p` shows via `FormalGroup.heightIdeal_eq_top_iff_forall_height_lt` that
every higher Landweber height ideal `I_n(Ê)` with `n ≥ 3` is the unit ideal
(`WeierstrassCurve.heightIdeal_formalGroup_eq_top`). By Landweber's recursion
(`FormalGroup.heightIdeal_succ_eq_top_iff`), Landweber's generator `v₂`, the coefficient of `T^(p²)`
in `[p]_Ê`, is therefore a unit on the height-two quotient `R ⧸ I₂(Ê) = R ⧸ (p, A)`
(`WeierstrassCurve.isUnit_mk_coeff_nsmulSeries_formalGroup_pow_two`). Consequently:

* For any `R`-module `M` and `m ≥ 2`, the Landweber sequence `(v₀, v₁, …, v_(m-1))` of `Ê` is
  weakly regular on `M` if and only if `(p, A)` is weakly regular on `M`
  (`WeierstrassCurve.isWeaklyRegular_ofFn_coeff_nsmulSeries_formalGroup_iff`).
* On the universal elliptic Weierstrass curve over `ℤ[a₁, a₂, a₃, a₄, a₆][Δ⁻¹]`, and hence on
  every elliptic curve `W / R` whose classifying homomorphism `W.specializeElliptic` is flat, the
  Landweber sequence `(v₀, v₁, …, v_(m-1))` is weakly regular for every prime `p` and every `m`
  (`WeierstrassCurve.isWeaklyRegular_ofFn_coeff_nsmulSeries_formalGroup_of_flat`).

## Main results

* `WeierstrassCurve.isOrdinary_iff_height_formalGroup_eq_one` and
  `WeierstrassCurve.isSupersingular_iff_height_formalGroup_eq_two`: over a field of characteristic
  `p`, an elliptic curve is ordinary iff its formal group has height `1`, and supersingular iff its
  formal group has height `2`.
* `WeierstrassCurve.height_formalGroup_eq_one_or_eq_two` and
  `WeierstrassCurve.height_formalGroup_le_two`: the formal group of an elliptic curve over a field
  of characteristic `p` has height `1` or `2`.
* `WeierstrassCurve.isOrdinary_iff_coeff_invariantDifferential_ne_zero`,
  `WeierstrassCurve.isSupersingular_iff_coeff_invariantDifferential_eq_zero`, and
  `WeierstrassCurve.height_formalGroup_eq_two_iff`: Hasse-invariant criteria for ordinarity,
  supersingularity, and height `2` at every prime `p`.
* `WeierstrassCurve.heightIdeal_formalGroup_eq_top`: for an elliptic curve over any commutative
  ring and `n ≥ 3`, `I_n(Ê) = ⊤`.
* `WeierstrassCurve.isUnit_mk_coeff_nsmulSeries_formalGroup_pow_two` and
  `WeierstrassCurve.isUnit_mk_span_coeff_nsmulSeries_formalGroup_pow_two`: Landweber's `v₂` is a
  unit modulo `I₂(Ê) = (p, A)`.
* `WeierstrassCurve.isWeaklyRegular_ofFn_coeff_nsmulSeries_formalGroup_iff`: direct regular-sequence
  Landweber criterion in terms of `(p, A)` for any elliptic curve over a commutative ring.
* `WeierstrassCurve.Universal.isWeaklyRegular_ofFn_coeff_nsmulSeries_formalGroup_ellipticCurve` and
  `WeierstrassCurve.isWeaklyRegular_ofFn_coeff_nsmulSeries_formalGroup_of_flat`: Landweber
  regularity for the universal elliptic curve and for flat classifying morphisms.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.4, IV.7, V.3 and V.4.
* P. S. Landweber, *Homological properties of comodules over `MU_*(MU)` and `BP_*(BP)`*,
  Amer. J. Math. 98 (1976), 591–610.
* P. G. Goerss, *Topological modular forms [after Hopkins, Miller and Lurie]*, Séminaire
  Bourbaki 1005 (2009), §3.2.
-/

public section

open scoped Pointwise
open RingTheory.Sequence TauCeti.Isogeny

namespace WeierstrassCurve

section Field

variable {K : Type*} [Field K] {p : ℕ} [hp : Fact p.Prime] [CharP K p]
  (W : WeierstrassCurve K) [W.IsElliptic]

/-- **An elliptic curve is supersingular iff its formal group has height two** (Silverman V.3.1),
at every prime `p` (including `p = 2` and `p = 3`) and over an arbitrary field of characteristic
`p`. -/
theorem isSupersingular_iff_height_formalGroup_eq_two :
    W.IsSupersingular p ↔ (formalGroup W).height p = 2 := by
  have hp0 : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  set φ := mulByIntIsogenyOfNeZero W.toAffine hp0
  have hdeg : φ.separableDegree * φ.inseparableDegree = p ^ 2 := by
    rw [φ.separableDegree_mul_inseparableDegree, degree_mulByIntIsogenyOfNeZero,
      Int.natAbs_natCast]
  rw [isSupersingular_iff_separableDegree_mulByIntIsogenyOfNeZero_eq_one p W,
    ← Nat.cast_two, (formalGroup W).height_eq_natCast_iff,
    W.order_nsmulSeries_formalGroup hp.out.ne_zero, Nat.cast_inj (R := ℕ∞)]
  refine ⟨fun hsep ↦ ?_, fun hins ↦ ?_⟩
  · rw [hsep, one_mul] at hdeg
    exact hdeg
  · rw [hins] at hdeg
    exact (Nat.mul_eq_right (pow_ne_zero 2 hp.out.ne_zero)).mp hdeg

/-- **An elliptic curve is ordinary iff its formal group has height one** (Silverman V.3.1), at
every prime `p` and over an arbitrary field of characteristic `p`. -/
theorem isOrdinary_iff_height_formalGroup_eq_one :
    W.IsOrdinary p ↔ (formalGroup W).height p = 1 := by
  have hp0 : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  set φ := mulByIntIsogenyOfNeZero W.toAffine hp0
  have hdeg : φ.separableDegree * φ.inseparableDegree = p * p := by
    rw [φ.separableDegree_mul_inseparableDegree, degree_mulByIntIsogenyOfNeZero,
      Int.natAbs_natCast, sq]
  rw [isOrdinary_iff_separableDegree_mulByIntIsogenyOfNeZero_eq p W hp.out,
    ← Nat.cast_one, (formalGroup W).height_eq_natCast_iff, pow_one,
    W.order_nsmulSeries_formalGroup hp.out.ne_zero, Nat.cast_inj (R := ℕ∞)]
  refine ⟨fun hsep ↦ ?_, fun hins ↦ ?_⟩
  · rw [hsep] at hdeg
    exact Nat.eq_of_mul_eq_mul_left hp.out.pos hdeg
  · rw [hins] at hdeg
    exact Nat.eq_of_mul_eq_mul_right hp.out.pos hdeg

/-- **The formal group of an elliptic curve over a field of characteristic `p` has height `1` or
`2`.** -/
theorem height_formalGroup_eq_one_or_eq_two :
    (formalGroup W).height p = 1 ∨ (formalGroup W).height p = 2 := by
  by_cases h : W.IsSupersingular p
  · exact Or.inr (W.isSupersingular_iff_height_formalGroup_eq_two.mp h)
  · exact Or.inl (W.isOrdinary_iff_height_formalGroup_eq_one.mp (not_isSupersingular.mp h))

/-- **The formal group of an elliptic curve over a field of characteristic `p` has height at most
two.** -/
theorem height_formalGroup_le_two : (formalGroup W).height p ≤ 2 := by
  rcases W.height_formalGroup_eq_one_or_eq_two (p := p) with h | h
  · rw [h, ← Nat.cast_one, ← Nat.cast_two, Nat.cast_le]
    omega
  · exact h.le

/-- The formal group of an elliptic curve over a field of characteristic `p > 0` has finite
height. -/
theorem height_formalGroup_ne_top : (formalGroup W).height p ≠ ⊤ := by
  rcases W.height_formalGroup_eq_one_or_eq_two (p := p) with h | h <;> simp [h]

/-- An elliptic curve over a field of characteristic `p` is supersingular iff its formal group has
height greater than one. -/
theorem isSupersingular_iff_one_lt_height_formalGroup :
    W.IsSupersingular p ↔ 1 < (formalGroup W).height p := by
  rw [← not_isOrdinary, W.isOrdinary_iff_height_formalGroup_eq_one,
    (formalGroup W).one_le_height.lt_iff_ne', Ne]

/-- **Deuring's Hasse-invariant criterion for ordinarity**: an elliptic curve over a field of
characteristic `p` is ordinary exactly when the coefficient of `Tᵖ⁻¹` in the invariant differential
of its formal group is nonzero. -/
theorem isOrdinary_iff_coeff_invariantDifferential_ne_zero :
    W.IsOrdinary p ↔
      PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential ≠ 0 :=
  W.isOrdinary_iff_height_formalGroup_eq_one.trans W.height_formalGroup_eq_one_iff

/-- **Deuring's Hasse-invariant criterion for supersingularity**: an elliptic curve over a field of
characteristic `p` is supersingular exactly when the coefficient of `Tᵖ⁻¹` in the invariant
differential of its formal group vanishes (Silverman V.4.1). -/
theorem isSupersingular_iff_coeff_invariantDifferential_eq_zero :
    W.IsSupersingular p ↔
      PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential = 0 := by
  rw [← not_isOrdinary, W.isOrdinary_iff_coeff_invariantDifferential_ne_zero, not_not]

/-- Over a field of characteristic `p`, the formal group of an elliptic curve has height two
exactly when the coefficient of `Tᵖ⁻¹` in its invariant differential vanishes. -/
theorem height_formalGroup_eq_two_iff :
    (formalGroup W).height p = 2 ↔
      PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential = 0 :=
  W.isSupersingular_iff_height_formalGroup_eq_two.symm.trans
    W.isSupersingular_iff_coeff_invariantDifferential_eq_zero

end Field

section Ring

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] {p : ℕ}

/-- **Higher Landweber height ideals are the unit ideal for elliptic curves**: for any elliptic
Weierstrass curve over a commutative ring `R`, any prime `p`, and any `n ≥ 3`, the height ideal
`I_n(Ê)` is the unit ideal, since every specialization to a field of characteristic `p` has height
at most `2`. -/
theorem heightIdeal_formalGroup_eq_top (hp : p.Prime) {n : ℕ} (hn : 3 ≤ n) :
    (formalGroup W).heightIdeal p n = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  rw [(formalGroup W).heightIdeal_eq_top_iff_forall_height_lt hp (by omega)]
  intro K _ _ φ
  rw [← W.map_formalGroup φ]
  refine lt_of_le_of_lt ((W.map φ).height_formalGroup_le_two (p := p)) ?_
  rw [← Nat.cast_two, Nat.cast_lt]
  omega

/-- **Landweber's `v₂` is a unit on the height-two quotient** `R ⧸ I₂(Ê)` of any elliptic
Weierstrass curve over a commutative ring `R`. -/
theorem isUnit_mk_coeff_nsmulSeries_formalGroup_pow_two (hp : p.Prime) :
    IsUnit (Ideal.Quotient.mk ((formalGroup W).heightIdeal p 2)
      (PowerSeries.coeff (p ^ 2) ((formalGroup W).nsmulSeries p))) :=
  ((formalGroup W).heightIdeal_succ_eq_top_iff hp 2).mp
    (W.heightIdeal_formalGroup_eq_top hp le_rfl)

/-- **Landweber's `v₂` is a unit modulo `(p, A)`**: for any elliptic Weierstrass curve `W` over a
commutative ring `R` and any prime `p`, the coefficient of `T^(p²)` in `[p]_Ê` is a unit modulo
`(p, A)`, where `A` is the Hasse invariant (the coefficient of `Tᵖ⁻¹` in the invariant differential
of `Ê`). -/
theorem isUnit_mk_span_coeff_nsmulSeries_formalGroup_pow_two (hp : p.Prime) :
    IsUnit (Ideal.Quotient.mk
      (Ideal.span {(p : R), PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential})
      (PowerSeries.coeff (p ^ 2) ((formalGroup W).nsmulSeries p))) := by
  rw [← W.heightIdeal_formalGroup_two hp]
  exact W.isUnit_mk_coeff_nsmulSeries_formalGroup_pow_two hp

/-- **Direct regular-sequence Landweber criterion for an elliptic curve.** For `m ≥ 2`, a prime
`p`, an elliptic curve `W` over `R`, and an `R`-module `M`, the Landweber sequence
`(v₀, v₁, …, v_(m-1))` of `formalGroup W` is weakly regular on `M` if and only if `(p, A)` is
weakly regular on `M`, where `A` is the Hasse invariant in the coordinate `T = -x / y`. -/
theorem isWeaklyRegular_ofFn_coeff_nsmulSeries_formalGroup_iff (hp : p.Prime) (M : Type*)
    [AddCommGroup M] [Module R M] {m : ℕ} (hm : 2 ≤ m) :
    IsWeaklyRegular M
        (List.ofFn fun i : Fin m ↦
          PowerSeries.coeff (p ^ (i : ℕ)) ((formalGroup W).nsmulSeries p)) ↔
      IsWeaklyRegular M
        [(p : R), PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential] := by
  rw [(formalGroup W).isWeaklyRegular_ofFn_coeff_nsmulSeries_iff_of_heightIdeal_succ_eq_top
    hp M hm (W.heightIdeal_formalGroup_eq_top hp le_rfl),
    List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  simp only [Fin.val_zero, Fin.val_succ, zero_add, pow_zero, pow_one,
    (formalGroup W).coeff_one_nsmulSeries]
  exact W.isWeaklyRegular_natCast_coeff_nsmulSeries_iff hp M

end Ring

namespace Universal

/-- **Landweber regularity of the universal elliptic Weierstrass curve.** For every prime `p` and
every `m : ℕ`, the Landweber sequence `(v₀, v₁, …, v_(m-1))` of `formalGroup ellipticCurve` is
weakly regular on `ℤ[a₁, a₂, a₃, a₄, a₆][Δ⁻¹]`. -/
theorem isWeaklyRegular_ofFn_coeff_nsmulSeries_formalGroup_ellipticCurve {p : ℕ} (hp : p.Prime)
    (m : ℕ) :
    IsWeaklyRegular EllipticRing
      (List.ofFn fun i : Fin m ↦
        PowerSeries.coeff (p ^ (i : ℕ)) ((formalGroup ellipticCurve).nsmulSeries p)) := by
  have h2 : IsWeaklyRegular EllipticRing
      (List.ofFn fun i : Fin (max m 2) ↦
        PowerSeries.coeff (p ^ (i : ℕ)) ((formalGroup ellipticCurve).nsmulSeries p)) :=
    (ellipticCurve.isWeaklyRegular_ofFn_coeff_nsmulSeries_formalGroup_iff hp EllipticRing
      (le_max_right m 2)).mpr (isWeaklyRegular_natCast_coeff_invariantDifferential_ellipticCurve hp)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (le_max_left m 2)
  have hpre : (List.ofFn fun i : Fin (max m 2) ↦
        PowerSeries.coeff (p ^ (i : ℕ)) ((formalGroup ellipticCurve).nsmulSeries p)) =
      (List.ofFn fun i : Fin m ↦
        PowerSeries.coeff (p ^ (i : ℕ)) ((formalGroup ellipticCurve).nsmulSeries p)) ++
      (List.ofFn fun j : Fin k ↦
        PowerSeries.coeff (p ^ (m + j : ℕ)) ((formalGroup ellipticCurve).nsmulSeries p)) := by
    rw [hk, List.ofFn_add]
    simp
  rw [hpre, isWeaklyRegular_append_iff] at h2
  exact h2.1

end Universal

/-- **Landweber regularity for elliptic curves with flat classifying morphism.** If `W` is an
elliptic Weierstrass curve over `R` whose classifying ring homomorphism
`W.specializeElliptic : ℤ[a₁, a₂, a₃, a₄, a₆][Δ⁻¹] →+* R` is flat, then for every prime `p` and
every `m : ℕ`, the Landweber sequence `(v₀, v₁, …, v_(m-1))` of `formalGroup W` is weakly regular
on `R`. -/
theorem isWeaklyRegular_ofFn_coeff_nsmulSeries_formalGroup_of_flat {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic] (hflat : W.specializeElliptic.Flat)
    {p : ℕ} (hp : p.Prime) (m : ℕ) :
    IsWeaklyRegular R
      (List.ofFn fun i : Fin m ↦
        PowerSeries.coeff (p ^ (i : ℕ)) ((formalGroup W).nsmulSeries p)) := by
  algebraize [W.specializeElliptic]
  have h :=
    (Universal.isWeaklyRegular_ofFn_coeff_nsmulSeries_formalGroup_ellipticCurve hp m).of_flat
      (S := R)
  have hmap (j : ℕ) :
      algebraMap Universal.EllipticRing R
        (PowerSeries.coeff (p ^ j) ((formalGroup Universal.ellipticCurve).nsmulSeries p)) =
      PowerSeries.coeff (p ^ j) ((formalGroup W).nsmulSeries p) := by
    rw [RingHom.algebraMap_toAlgebra, ← PowerSeries.coeff_map, FormalGroup.map_nsmulSeries,
      ← Universal.ellipticCurve.map_formalGroup W.specializeElliptic, W.map_specializeElliptic]
  simpa [List.map_ofFn, Function.comp_def, hmap] using h

end WeierstrassCurve
