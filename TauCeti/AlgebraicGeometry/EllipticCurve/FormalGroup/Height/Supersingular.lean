/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.MapsInfinity
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Separability
public import TauCeti.RingTheory.FormalGroup.Height.Ideal
public import TauCeti.RingTheory.FormalGroup.ZSMul
import Mathlib.RingTheory.Ideal.Maximal
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Isogeny.Differential
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Isogeny.Hom
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Supersingular

/-!
# Height of the formal group of an elliptic curve at every prime

Let `W` be an elliptic curve over a field `K`, with formal group law `Ê = formalGroup W` in the
parameter `z = -x/y` at infinity. For any nonzero integer `n`, the formal series of `[n] : W → W`
is the `n`-multiplication series `[n]_Ê` (`TauCeti.Isogeny.formalSeries_mulByIntIsogeny`), and the
order of the formal series of an isogeny is its inseparable degree
(`TauCeti.Isogeny.order_formalSeries_eq_inseparableDegree`). Consequently the order of `[n]_Ê`
equals the inseparable degree of `[n]`.

Over a field `K` of prime characteristic `p`, multiplication by `p` has degree `p²`, and its
separable degree is `p` when `W` is ordinary and `1` when `W` is supersingular
(`WeierstrassCurve.isOrdinary_iff_separableDegree_mulByIntIsogenyOfNeZero_eq`,
`WeierstrassCurve.isSupersingular_iff_separableDegree_mulByIntIsogenyOfNeZero_eq_one`). Hence
`[p]_Ê` has order `p` when `W` is ordinary and `p²` when `W` is supersingular, which proves in
every prime characteristic (including `p = 2` and `p = 3`):

* `W` is ordinary if and only if `Ê` has height `1`
  (`WeierstrassCurve.isOrdinary_iff_height_formalGroup_eq_one`), and if and only if the Hasse
  invariant (the coefficient of `Tᵖ⁻¹` in the invariant differential of `Ê`) is nonzero
  (`WeierstrassCurve.isOrdinary_iff_coeff_invariantDifferential_ne_zero`);
* `W` is supersingular if and only if `Ê` has height `2`
  (`WeierstrassCurve.isSupersingular_iff_height_formalGroup_eq_two`), and if and only if the Hasse
  invariant vanishes (`WeierstrassCurve.isSupersingular_iff_coeff_invariantDifferential_eq_zero`);
* the height of `Ê` is always `1` or `2` (`WeierstrassCurve.height_formalGroup_eq_one_or_eq_two`),
  in particular at most `2` (`WeierstrassCurve.height_formalGroup_le_two`).

Passing to residue fields at maximal ideals carries this bound to an elliptic curve `W` over an
arbitrary commutative ring `R`: for every prime `p`, the Landweber height ideals `I_n(Ê)` equal `⊤`
for all `n ≥ 3` (`WeierstrassCurve.heightIdeal_formalGroup_eq_top`), and Landweber's `v₂` (the
coefficient of `T^(p²)` in `[p]_Ê`) is a unit modulo `I₂(Ê)`
(`WeierstrassCurve.isUnit_mk_coeff_nsmulSeries_formalGroup_sq`).

## Main results

* `WeierstrassCurve.order_zsmulSeries_formalGroup` and
  `WeierstrassCurve.order_nsmulSeries_formalGroup`: the order of `[n]_Ê` is the inseparable degree
  of `[n]`.
* `WeierstrassCurve.isOrdinary_iff_height_formalGroup_eq_one`: `W` is ordinary iff `Ê` has
  height `1`.
* `WeierstrassCurve.isSupersingular_iff_height_formalGroup_eq_two`: `W` is supersingular iff `Ê`
  has height `2`.
* `WeierstrassCurve.height_formalGroup_eq_one_or_eq_two` and
  `WeierstrassCurve.height_formalGroup_le_two`: the height of `Ê` is `1` or `2`, hence at most `2`.
* `WeierstrassCurve.isOrdinary_iff_coeff_invariantDifferential_ne_zero` and
  `WeierstrassCurve.isSupersingular_iff_coeff_invariantDifferential_eq_zero`: the Hasse-invariant
  criteria for ordinarity and supersingularity in every prime characteristic.
* `WeierstrassCurve.heightIdeal_formalGroup_eq_top` and
  `WeierstrassCurve.isUnit_mk_coeff_nsmulSeries_formalGroup_sq`: over any commutative ring, an
  elliptic curve has `I_n(Ê) = ⊤` for `n ≥ 3` and invertible `v₂` in `R ⧸ I₂(Ê)`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.7, V.3.1 and V.4.1.
* P. S. Landweber, *Homological properties of comodules over `MU_*(MU)` and `BP_*(BP)`*,
  Amer. J. Math. 98 (1976), 591–610.
-/

public section

namespace WeierstrassCurve

section Order

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- **The order of `[n]_Ê` is the inseparable degree of `[n]`**: for any elliptic curve over a
field and any nonzero integer `n`, the formal `n`-multiplication series has order equal to the
inseparable degree of the multiplication-by-`n` isogeny. -/
theorem order_zsmulSeries_formalGroup {n : ℤ} (hn : n ≠ 0) :
    ((formalGroup W).zsmulSeries n).order =
      ((TauCeti.Isogeny.mulByIntIsogenyOfNeZero W.toAffine hn).inseparableDegree : ℕ∞) := by
  rw [← TauCeti.Isogeny.formalSeries_mulByIntIsogeny,
    TauCeti.Isogeny.order_formalSeries_eq_inseparableDegree]

/-- **The order of `[n]_Ê` (`n : ℕ`) is the inseparable degree of `[n]`**, for `n ≠ 0`. -/
theorem order_nsmulSeries_formalGroup {n : ℕ} (hn : n ≠ 0) :
    ((formalGroup W).nsmulSeries n).order =
      ((TauCeti.Isogeny.mulByIntIsogenyOfNeZero W.toAffine
        (Nat.cast_ne_zero.mpr hn)).inseparableDegree : ℕ∞) := by
  rw [← FormalGroup.zsmulSeries_natCast, W.order_zsmulSeries_formalGroup]

end Order

section Field

variable {K : Type*} [Field K] {p : ℕ} [hp : Fact p.Prime] [CharP K p]
  (W : WeierstrassCurve K) [W.IsElliptic]

/-- **An elliptic curve in characteristic `p` is ordinary if and only if its formal group has height
one** (Silverman V.3.1), for every prime `p` including `2` and `3`. -/
theorem isOrdinary_iff_height_formalGroup_eq_one :
    W.IsOrdinary p ↔ (formalGroup W).height p = 1 := by
  have : ExpChar K p := .prime hp.out
  have hpz : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  let φ := TauCeti.Isogeny.mulByIntIsogenyOfNeZero W.toAffine hpz
  have hφ (h : (p : ℤ) ≠ 0) : TauCeti.Isogeny.mulByIntIsogenyOfNeZero W.toAffine h = φ := rfl
  have hdeg : φ.separableDegree * φ.inseparableDegree = p * p := by
    rw [φ.separableDegree_mul_inseparableDegree, TauCeti.Isogeny.degree_mulByIntIsogenyOfNeZero,
      Int.natAbs_natCast, sq]
  rw [W.isOrdinary_iff_separableDegree_mulByIntIsogenyOfNeZero_eq p hp.out, ← Nat.cast_one,
    FormalGroup.height_eq_natCast_iff, pow_one, W.order_nsmulSeries_formalGroup hp.out.ne_zero,
    Nat.cast_inj (R := ℕ∞)]
  simp only [hφ]
  exact ⟨fun hs ↦ Nat.mul_left_cancel hp.out.pos (hs ▸ hdeg),
    fun hi ↦ Nat.mul_right_cancel hp.out.pos (hi ▸ hdeg)⟩

/-- **An elliptic curve in characteristic `p` is supersingular if and only if its formal group has
height two** (Silverman V.3.1), for every prime `p` including `2` and `3`. -/
theorem isSupersingular_iff_height_formalGroup_eq_two :
    W.IsSupersingular p ↔ (formalGroup W).height p = 2 := by
  have : ExpChar K p := .prime hp.out
  have hpz : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  let φ := TauCeti.Isogeny.mulByIntIsogenyOfNeZero W.toAffine hpz
  have hφ (h : (p : ℤ) ≠ 0) : TauCeti.Isogeny.mulByIntIsogenyOfNeZero W.toAffine h = φ := rfl
  have hdeg : φ.separableDegree * φ.inseparableDegree = p ^ 2 := by
    rw [φ.separableDegree_mul_inseparableDegree, TauCeti.Isogeny.degree_mulByIntIsogenyOfNeZero,
      Int.natAbs_natCast]
  rw [W.isSupersingular_iff_separableDegree_mulByIntIsogenyOfNeZero_eq_one p,
    ← Nat.cast_ofNat (R := ℕ∞), FormalGroup.height_eq_natCast_iff,
    W.order_nsmulSeries_formalGroup hp.out.ne_zero, Nat.cast_inj (R := ℕ∞)]
  simp only [hφ]
  exact ⟨fun hs ↦ by rwa [hs, one_mul] at hdeg,
    fun hi ↦ Nat.mul_right_cancel (pow_pos hp.out.pos 2) (by rw [hi] at hdeg; linarith)⟩

/-- **The formal group of an elliptic curve in characteristic `p` has height `1` or `2`**
(Silverman IV.7.5 and V.3.1). -/
theorem height_formalGroup_eq_one_or_eq_two :
    (formalGroup W).height p = 1 ∨ (formalGroup W).height p = 2 := by
  by_cases h : W.IsOrdinary p
  · exact Or.inl (W.isOrdinary_iff_height_formalGroup_eq_one.mp h)
  · exact Or.inr (W.isSupersingular_iff_height_formalGroup_eq_two.mp (not_isOrdinary.mp h))

/-- **The formal group of an elliptic curve in characteristic `p` has height at most two.** -/
theorem height_formalGroup_le_two : (formalGroup W).height p ≤ 2 := by
  rcases W.height_formalGroup_eq_one_or_eq_two with h | h <;> rw [h]
  exact one_le_two

/-- The formal group of an elliptic curve in characteristic `p` has finite height. -/
theorem height_formalGroup_ne_top : (formalGroup W).height p ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) W.height_formalGroup_le_two

/-- **An elliptic curve in characteristic `p` is supersingular if and only if its formal group has
height strictly greater than one.** -/
theorem isSupersingular_iff_one_lt_height_formalGroup :
    W.IsSupersingular p ↔ 1 < (formalGroup W).height p := by
  rw [← not_isOrdinary, W.isOrdinary_iff_height_formalGroup_eq_one,
    (formalGroup W).one_le_height.lt_iff_ne', Ne]

/-- **Deuring's Hasse-invariant criterion for ordinarity**: an elliptic curve in characteristic `p`
is ordinary if and only if the coefficient of `Tᵖ⁻¹` in the invariant differential of its
formal group is nonzero (Silverman V.4.1). -/
theorem isOrdinary_iff_coeff_invariantDifferential_ne_zero :
    W.IsOrdinary p ↔
      PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential ≠ 0 := by
  rw [W.isOrdinary_iff_height_formalGroup_eq_one, W.height_formalGroup_eq_one_iff]

/-- **Deuring's Hasse-invariant criterion for supersingularity**: an elliptic curve in
characteristic `p` is supersingular if and only if the coefficient of `Tᵖ⁻¹` in the invariant
differential of its formal group vanishes (Silverman V.4.1). -/
theorem isSupersingular_iff_coeff_invariantDifferential_eq_zero :
    W.IsSupersingular p ↔
      PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential = 0 := by
  rw [← not_isOrdinary, W.isOrdinary_iff_coeff_invariantDifferential_ne_zero, not_not]

/-- Over a field of characteristic `p`, the formal group of an elliptic curve has height two if and
only if the coefficient of `Tᵖ⁻¹` in its invariant differential vanishes. -/
theorem height_formalGroup_eq_two_iff :
    (formalGroup W).height p = 2 ↔
      PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential = 0 := by
  rw [← W.isSupersingular_iff_height_formalGroup_eq_two,
    W.isSupersingular_iff_coeff_invariantDifferential_eq_zero]

end Field

section Ring

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] {p : ℕ}

/-- **Termination of the Landweber height tower for elliptic curves**: for an elliptic curve `W`
over any commutative ring `R`, every prime `p`, and every `n ≥ 3`, the `n`-th height ideal
`I_n(formalGroup W)` is the unit ideal. -/
theorem heightIdeal_formalGroup_eq_top (hp : p.Prime) {n : ℕ} (hn : 3 ≤ n) :
    (formalGroup W).heightIdeal p n = ⊤ := by
  by_contra hne
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
  let _ : Field (R ⧸ 𝔪) := @Ideal.Quotient.field R _ 𝔪 h𝔪
  have : Fact p.Prime := ⟨hp⟩
  have hp𝔪 : (p : R) ∈ 𝔪 := by
    have h1 : (formalGroup W).heightIdeal p 1 ≤ 𝔪 :=
      ((formalGroup W).heightIdeal_mono (by omega : 1 ≤ n)).trans hle
    rwa [(formalGroup W).heightIdeal_one hp, Ideal.span_singleton_le_iff_mem] at h1
  have : CharP (R ⧸ 𝔪) p := (CharP.charP_iff_prime_eq_zero hp).mpr <| by
    rwa [← map_natCast (Ideal.Quotient.mk 𝔪), Ideal.Quotient.eq_zero_iff_mem]
  have hbot : (formalGroup (W.map (Ideal.Quotient.mk 𝔪))).heightIdeal p n = ⊥ := by
    rw [W.map_formalGroup, ← FormalGroup.map_heightIdeal, Ideal.map_eq_bot_iff_le_ker,
      Ideal.mk_ker]
    exact hle
  have hge : (n : ℕ∞) ≤ (formalGroup (W.map (Ideal.Quotient.mk 𝔪))).height p :=
    ((formalGroup (W.map (Ideal.Quotient.mk 𝔪))).heightIdeal_eq_bot_iff_le_height).mp hbot
  have hle2 := (W.map (Ideal.Quotient.mk 𝔪)).height_formalGroup_le_two (p := p)
  have h32 : (3 : ℕ∞) ≤ 2 := (Nat.cast_le.mpr hn).trans (hge.trans hle2)
  exact absurd h32 (by decide)

/-- **Landweber's `v₂` is a unit modulo `I₂` for every elliptic curve**: over any commutative
ring `R` and for any prime `p`, the image of `coeff (p ^ 2) ((formalGroup W).nsmulSeries p)` in
`R ⧸ (formalGroup W).heightIdeal p 2` is a unit. -/
theorem isUnit_mk_coeff_nsmulSeries_formalGroup_sq (hp : p.Prime) :
    IsUnit (Ideal.Quotient.mk ((formalGroup W).heightIdeal p 2)
      (PowerSeries.coeff (p ^ 2) ((formalGroup W).nsmulSeries p))) := by
  set I := (formalGroup W).heightIdeal p 2
  set v₂ := PowerSeries.coeff (p ^ 2) ((formalGroup W).nsmulSeries p)
  have htop : I ⊔ Ideal.span {v₂} = ⊤ := by
    rw [← (formalGroup W).heightIdeal_succ hp 2]
    exact W.heightIdeal_formalGroup_eq_top hp le_rfl
  have hcomap : I ⊔ Ideal.span {v₂} =
      (Ideal.span {Ideal.Quotient.mk I v₂}).comap (Ideal.Quotient.mk I) := by
    rw [← Set.image_singleton (f := Ideal.Quotient.mk I), ← Ideal.map_span,
      Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_comm]
  rwa [hcomap, Ideal.comap_eq_top_iff, Ideal.span_singleton_eq_top] at htop

end Ring

end WeierstrassCurve

end
