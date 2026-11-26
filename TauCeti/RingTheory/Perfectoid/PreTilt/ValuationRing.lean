/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
public import Mathlib.RingTheory.Valuation.ValuationRing
public import TauCeti.RingTheory.Perfectoid.Untilt
public import TauCeti.RingTheory.Valuation.ValuationRing
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Valued.ValuedField

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Valued.LocallyCompact

/-!
# The tilt of a `p`-adically complete valuation ring

Let `V` be a `p`-adically complete commutative ring in which `p` is not a unit, with tilt
`V♭ = PreTilt V p` and sharp map `x ↦ x♯ = x.untilt`. Multiplicatively, `x ∈ V♭` is the compatible
system `(xₙ)ₙ` of `p`-power roots of `x♯` in `V` given by `xₙ = (x ^ (1 / p ^ n))♯`, whose reduction
modulo `p` is the `n`-th coordinate of `x`. Only this multiplicative description is used here; no
perfectoid hypothesis is made.

* If `V` is reduced, `x♯ = 0` forces every `xₙ` to vanish, so the sharp map detects zero, and if
  `V` is a domain, so is `V♭` (`PreTilt.untilt_eq_zero_iff` and `PreTilt.instIsDomain` in
  `TauCeti.RingTheory.Perfectoid.Untilt`).
* If `V` is an integrally closed domain, divisibility in `V♭` is detected after untilting: if
  `x♯ ∣ y♯` with `x ≠ 0`, then `xₙ ^ p ^ n ∣ yₙ ^ p ^ n`, hence `xₙ ∣ yₙ`, and the quotients
  `yₙ / xₙ` form a compatible system of roots, that is, an element `z ∈ V♭` with `x z = y`.
* If `V` is a valuation ring, so is `V♭`: any two sharps are comparable for divisibility.
* For the valuation ring `O_C` of a nontrivially normed ultrametric field `C`, the tilt is
  separated: if every power of a nonunit `c` divides `a`, then `a = 0`, because untilting gives
  `‖a♯‖ ≤ ‖c♯‖ ^ n` with `‖c♯‖ < 1`.
* For a valuation ring `V`, the sharp map induces an injective order-preserving homomorphism of
  value groups `Frac(V♭)ˣ / (V♭)ˣ → Frac(V)ˣ / Vˣ`, which need not be surjective: for `V = ℤ_p` the
  tilt is `𝔽_p`, with trivial value group.

Mathlib's `PreTilt.isDomain` is the case of the ring of integers of a field with a rank-one
valuation; here `V` is any `p`-adically complete domain.

## Main definitions

* `PreTilt.untiltFraction`: the extension `Frac(V♭) → Frac(V)`, `x / y ↦ x♯ / y♯`, of the sharp
  map of a `p`-adically complete domain.
* `PreTilt.valueGroupMap`: for a `p`-adically complete valuation ring, the induced homomorphism
  of value groups.

## Main results

* `PreTilt.untilt_dvd_untilt_iff`: for an integrally closed domain `V`, `x♯ ∣ y♯` if and only if
  `x ∣ y`.
* `PreTilt.instValuationRing`: the tilt of a `p`-adically complete valuation ring is a valuation
  ring.
* `PreTilt.eq_zero_of_forall_pow_dvd`: in the tilt of `O_C`, an element divisible by every power
  of a nonunit is zero.
* `PreTilt.valueGroupMap_le_valueGroupMap_iff`, `PreTilt.valueGroupMap_injective`,
  `PreTilt.valueGroupMap_inj`: the sharp map on value groups is an order embedding.

## References

* K. Česnavičius, P. Scholze, *Purity for flat cohomology*, proof of Proposition 2.1.9.
-/

public section

open Ideal

namespace PreTilt

variable {V : Type*} [CommRing V] {p : ℕ} [hp : Fact p.Prime] [Fact ¬IsUnit (p : V)]
  [IsAdicComplete (span {(p : V)}) V]

/-- Over an integrally closed domain, if `x♯ ∣ y♯` then `x ∣ y` in the tilt: the quotients of the
`p`-power roots of `y♯` by those of `x♯` form a compatible system of roots. -/
private theorem dvd_of_untilt_dvd_untilt [IsDomain V] [IsIntegrallyClosed V] {x y : PreTilt V p}
    (h : x.untilt ∣ y.untilt) : x ∣ y := by
  obtain rfl | hx := eq_or_ne x 0
  · rw [untilt_zero, zero_dvd_iff, untilt_eq_zero_iff] at h
    exact h ▸ dvd_refl _
  -- `r n` and `s n` are the `p ^ n`-th roots of `x♯` and `y♯` in `V` given by `x` and `y`.
  let F := (frobeniusEquiv (PreTilt V p) p).symm
  have hr (n : ℕ) : untilt (F^[n] x) ≠ 0 := fun h0 ↦ hx <| untilt_eq_zero_iff.mp <| by
    rw [← untilt_iterate_frobeniusEquiv_symm_pow x n]
    exact h0.symm ▸ zero_pow (pow_ne_zero n hp.out.ne_zero)
  have hdvd (n : ℕ) : untilt (F^[n] x) ∣ untilt (F^[n] y) := by
    rw [← IsIntegrallyClosed.pow_dvd_pow_iff (pow_ne_zero n hp.out.ne_zero)]
    simpa only [F, untilt_iterate_frobeniusEquiv_symm_pow] using h
  choose t ht using hdvd
  -- The quotients `t n` of the roots of `y♯` by those of `x♯` are compatible.
  have hcompat (n : ℕ) : t (n + 1) ^ p = t n := by
    refine mul_left_cancel₀ (hr n) ?_
    rw [← ht, ← untilt_iterate_frobeniusEquiv_symm_succ_pow x n,
      ← untilt_iterate_frobeniusEquiv_symm_succ_pow y n, ← mul_pow]
    exact (congrArg (· ^ p) (ht (n + 1))).symm
  let z : Perfection (ModP V p) p :=
    ⟨fun n ↦ Ideal.Quotient.mk _ (t n), fun n ↦ by rw [← map_pow, hcompat]⟩
  refine ⟨equivPerfection.symm z, ext fun n ↦ ?_⟩
  rw [map_mul, coeff_equivPerfection_symm, coeff_eq_mk_untilt_iterate,
    coeff_eq_mk_untilt_iterate]
  exact (congrArg _ (ht n)).trans (map_mul _ _ _)

/-- **Divisibility in the tilt is detected by the sharp map.** For a `p`-adically complete
integrally closed domain `V` and `x, y ∈ V♭`, `x♯ ∣ y♯` in `V` if and only if `x ∣ y` in `V♭`. -/
theorem untilt_dvd_untilt_iff [IsDomain V] [IsIntegrallyClosed V] {x y : PreTilt V p} :
    x.untilt ∣ y.untilt ↔ x ∣ y :=
  ⟨dvd_of_untilt_dvd_untilt, map_dvd untilt⟩

/-- **The tilt of a `p`-adically complete valuation ring is a valuation ring.** -/
instance instValuationRing [IsDomain V] [ValuationRing V] : ValuationRing (PreTilt V p) :=
  (ValuationRing.iff_dvd_total).mpr
    ⟨fun x y ↦ (ValuationRing.dvd_total x.untilt y.untilt).imp
      untilt_dvd_untilt_iff.mp untilt_dvd_untilt_iff.mp⟩

section ValueGroup

variable [IsDomain V] (K L : Type*) [Field K] [Algebra (PreTilt V p) K]
  [IsFractionRing (PreTilt V p) K] [Field L] [Algebra V L] [IsFractionRing V L]

variable (V p) in
/-- **The sharp map on fraction fields.** For a `p`-adically complete domain `V`, the sharp map
`V♭ → V` is multiplicative, preserves zero and sends nonzero elements to nonzero elements, so it
extends to a homomorphism of monoids with zero `Frac(V♭) → Frac(V)`, `x / y ↦ x♯ / y♯`. -/
noncomputable def untiltFraction : K →*₀ L :=
  (IsLocalization.toLocalizationMap (nonZeroDivisors (PreTilt V p)) K).lift₀
    ((algebraMap V L : V →*₀ L).comp { untilt with map_zero' := untilt_zero })
    fun y ↦ IsUnit.mk0 _ <| (map_ne_zero_iff _ (IsFractionRing.injective V L)).mpr <|
      untilt_ne_zero_iff.mpr (nonZeroDivisors.ne_zero y.property)

/-- `PreTilt.untiltFraction` extends the sharp map. -/
@[simp]
theorem untiltFraction_algebraMap (x : PreTilt V p) :
    untiltFraction V p K L (algebraMap (PreTilt V p) K x) = algebraMap V L x.untilt :=
  Submonoid.LocalizationMap.lift_eq _ _ x

variable [ValuationRing V]

variable (V p) in
/-- **The sharp map on value groups.** For a `p`-adically complete valuation ring `V`, the
extension of the sharp map to fraction fields induces a homomorphism of value groups
`Frac(V♭)ˣ / (V♭)ˣ → Frac(V)ˣ / Vˣ`, which is injective and order-preserving
(`PreTilt.valueGroupMap_le_valueGroupMap_iff`). -/
noncomputable def valueGroupMap :
    ValuationRing.ValueGroup (PreTilt V p) K →*₀ ValuationRing.ValueGroup V L where
  toFun := Quotient.map' (untiltFraction V p K L) <| by
    rintro _ z ⟨u, rfl⟩
    refine ⟨Units.map (untilt : PreTilt V p →* V) u, ?_⟩
    dsimp only
    rw [Units.smul_def, Units.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul,
      untiltFraction_algebraMap, Units.coe_map]
  map_zero' := congrArg Quotient.mk'' (map_zero (untiltFraction V p K L))
  map_one' := congrArg Quotient.mk'' (map_one (untiltFraction V p K L))
  map_mul' a b := Quotient.inductionOn₂' a b fun z w ↦
    congrArg Quotient.mk'' (map_mul (untiltFraction V p K L) z w)

/-- The sharp map on value groups sends the value of `z ∈ Frac(V♭)` to the value of its image in
`Frac(V)`. -/
@[simp]
theorem valueGroupMap_valuation (z : K) :
    valueGroupMap V p K L (ValuationRing.valuation (PreTilt V p) K z) =
      ValuationRing.valuation V L (untiltFraction V p K L z) := by
  rw [ValuationRing.valuation_apply, ValuationRing.valuation_apply]
  -- `rfl` holds because the underlying function of `valueGroupMap` is, by its definition,
  -- `Quotient.map' (untiltFraction V p K L)`, and `Quotient.map' f h (Quotient.mk'' z)` reduces to
  -- `Quotient.mk'' (f z)` (this is `Quotient.map'_mk''`).
  rfl

/-- **The sharp map on value groups is an order embedding.** -/
@[simp]
theorem valueGroupMap_le_valueGroupMap_iff {a b : ValuationRing.ValueGroup (PreTilt V p) K} :
    valueGroupMap V p K L a ≤ valueGroupMap V p K L b ↔ a ≤ b := by
  obtain ⟨z, rfl⟩ := ValuationRing.valuation_surjective a
  obtain ⟨w, rfl⟩ := ValuationRing.valuation_surjective b
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := PreTilt V p) z
  obtain ⟨x', y', hy', rfl⟩ := IsFractionRing.div_surjective (A := PreTilt V p) w
  have hy₀ := nonZeroDivisors.ne_zero hy
  have hy₀' := nonZeroDivisors.ne_zero hy'
  simp only [valueGroupMap_valuation, map_div₀ (untiltFraction V p K L), untiltFraction_algebraMap]
  rw [ValuationRing.valuation_div_le_valuation_div_iff_dvd (untilt_ne_zero_iff.mpr hy₀)
      (untilt_ne_zero_iff.mpr hy₀'),
    ValuationRing.valuation_div_le_valuation_div_iff_dvd hy₀ hy₀', ← map_mul, ← map_mul,
    untilt_dvd_untilt_iff]

/-- **The sharp map on value groups is injective.** -/
theorem valueGroupMap_injective : Function.Injective (valueGroupMap V p K L) :=
  fun _ _ h ↦ le_antisymm ((valueGroupMap_le_valueGroupMap_iff K L).mp h.le)
    ((valueGroupMap_le_valueGroupMap_iff K L).mp h.ge)

/-- Two values in `Frac(V♭)ˣ / (V♭)ˣ` are equal exactly when their images under the sharp map
on value groups are equal. -/
@[simp]
theorem valueGroupMap_inj {a b : ValuationRing.ValueGroup (PreTilt V p) K} :
    valueGroupMap V p K L a = valueGroupMap V p K L b ↔ a = b :=
  (valueGroupMap_injective K L).eq_iff

end ValueGroup

section RankOne

open scoped NormedField Valued

variable {p : ℕ} [Fact p.Prime] {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  [Fact ¬IsUnit (p : 𝒪[C])] [IsAdicComplete (Ideal.span {(p : 𝒪[C])}) (𝒪[C])]

/-- **Separatedness of the tilt of `O_C`.** If every power of a nonunit `c` of `O_C♭` divides `a`,
then `a = 0`. -/
theorem eq_zero_of_forall_pow_dvd (c : PreTilt (𝒪[C]) p) {a : PreTilt (𝒪[C]) p}
    (hc : ¬IsUnit c) (h : ∀ n, c ^ n ∣ a) : a = 0 := by
  -- untilting, `‖a♯‖ ≤ ‖c♯‖ ^ n` for every `n` while `‖c♯‖ < 1`
  by_contra ha
  have hc' : ‖(c.untilt : C)‖ < 1 := by
    refine lt_of_le_of_ne (Valued.integer.mem_iff.mp c.untilt.property) fun h1 ↦ hc ?_
    have hu : IsUnit c.untilt := Valued.integer.isUnit_iff_norm_eq_one.mpr h1
    rw [isUnit_iff_dvd_one, ← untilt_dvd_untilt_iff, map_one]
    exact hu.dvd
  have ha' : 0 < ‖(a.untilt : C)‖ := by
    rw [norm_pos_iff, ne_eq, ZeroMemClass.coe_eq_zero]
    exact untilt_ne_zero_iff.mpr ha
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one ha' hc'
  obtain ⟨t, ht⟩ := map_dvd untilt (h n)
  have hle : ‖(a.untilt : C)‖ ≤ ‖(c.untilt : C)‖ ^ n := by
    rw [ht, map_pow, MulMemClass.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (Valued.integer.mem_iff.mp t.property)
  exact absurd hn hle.not_gt

end RankOne

end PreTilt
