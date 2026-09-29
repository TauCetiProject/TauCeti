/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import TauCeti.Topology.Algebra.Ring.Ideal

/-!
# Congruence and continuity properties of the truncations of a `p`-adic integer

Mathlib's `PadicInt.appr x n` is the natural number below `p ^ n` congruent to `x` modulo
`p ^ n`, and `PadicInt.toZModPow n` is the induced ring homomorphism to `ZMod (p ^ n)`. This
file records the arithmetic dictionary between the two, the congruences that make `appr`
behave like a ring homomorphism modulo `p ^ n`, and the continuity of `toZModPow`.

The congruences are exactly what is needed to raise an element of `p`-power order in a monoid
to a `p`-adic exponent: `g ^ x.appr n` does not change when `n` grows past the order of `g`
(`PadicInt.pow_appr_eq_pow_appr`), so such powers assemble into a well-defined action of
`ℤ_[p]`.

## Main results

* `PadicInt.val_toZModPow_eq_appr`: `appr` computes the `ZMod (p ^ n)`-value of `toZModPow`.
* `PadicInt.continuous_toZModPow`, `PadicInt.continuous_toZMod`: truncation modulo `p ^ n` and
  reduction modulo `p` are continuous, `ZMod (p ^ n)` and `ZMod p` carrying the discrete
  topology.
* `PadicInt.cast_toZModPow_eq_toZMod`: reducing the truncation modulo `p ^ n` further modulo `p`
  recovers `toZMod`.
* `PadicInt.appr_modEq`, `PadicInt.appr_add_modEq`, `PadicInt.appr_mul_modEq`,
  `PadicInt.appr_natCast_modEq`: the truncations are compatible with each other and with the
  ring operations, modulo `p ^ n`.
* `PadicInt.pow_appr_eq_pow_appr`: raising an element of `p`-power order to the truncated
  exponent is independent of the truncation level, once that level is large enough.
* `PadicInt.quotientSpanPowEquivZMod`: `toZModPow n` identifies `ℤ_[p] ⧸ (p ^ n)` with
  `ZMod (p ^ n)`.
* `PadicInt.span_singleton_eq_span_pow_valuation`, `PadicInt.quotientSpanEquivZMod`,
  `PadicInt.natCard_quotient_span`, `PadicInt.isAddCyclic_quotient_span`: a nonzero `x` generates
  the same ideal as `p ^ v` for `v` its valuation, so `ℤ_[p] ⧸ (x)` is `ZMod (p ^ v)`, a finite
  ring of cardinality `p ^ v` whose additive group is cyclic.
* `PadicInt.quotientSpanToZMod`, `PadicInt.quotientSpanToZModPow`: for `p ∣ q`, respectively
  `p ^ n ∣ q`, reduction modulo `p`, respectively truncation modulo `p ^ n`, descends to a
  continuous ring homomorphism out of `ℤ_[p] ⧸ (q)`.
* `PadicInt.surjective_units_map_toZModPow`: every unit of `ZMod (p ^ n)` lifts to a unit of
  `ℤ_[p]`.
* `PadicInt.finite_residueField`, `PadicInt.card_residueField`: the residue field of `ℤ_[p]` is
  finite of cardinality `p`.
-/

public section

namespace PadicInt

variable {p : ℕ} [hp : Fact p.Prime]

/-- The residue field of `ℤ_p` is finite, being `ℤ/pℤ`. -/
instance finite_residueField : Finite (IsLocalRing.ResidueField ℤ_[p]) :=
  Finite.of_equiv _ residueField.symm.toEquiv

variable (p) in
/-- The residue field of `ℤ_p` has `p` elements. -/
theorem card_residueField : Nat.card (IsLocalRing.ResidueField ℤ_[p]) = p := by
  rw [Nat.card_congr residueField.toEquiv, Nat.card_zmod]

/-- The truncation `toZModPow n x` is the class of the natural number `x.appr n`. -/
theorem toZModPow_eq_natCast_appr (x : ℤ_[p]) (n : ℕ) :
    toZModPow n x = (x.appr n : ZMod (p ^ n)) :=
  (rfl)

/-- The `ZMod (p ^ n)`-value of the truncation `toZModPow n x` is `x.appr n`.

This is the `p ^ n` analogue of `PadicInt.val_toZMod_eq_zmodRepr`. -/
theorem val_toZModPow_eq_appr (x : ℤ_[p]) (n : ℕ) : (toZModPow n x).val = x.appr n := by
  rw [toZModPow_eq_natCast_appr, ZMod.val_natCast_of_lt (appr_lt x n)]

/-- Truncation modulo `p ^ n` is continuous: its fibres are the closed balls of radius
`p ^ (-n)`, which are open because the `p`-adic distance is ultrametric. -/
theorem continuous_toZModPow (n : ℕ) : Continuous (toZModPow (p := p) n) := by
  refine (IsLocallyConstant.iff_isOpen_fiber_apply.mpr fun x ↦ ?_).continuous
  have h : (toZModPow (p := p) n) ⁻¹' {toZModPow n x}
      = Metric.closedBall x ((p : ℝ) ^ (-n : ℤ)) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Metric.mem_closedBall, dist_eq_norm]
    rw [norm_le_pow_iff_mem_span_pow, ← ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  rw [h]
  exact IsUltrametricDist.isOpen_closedBall _ (zpow_ne_zero _ hp0.ne')

/-- Reduction modulo `p` is continuous: its fibres are those of the truncation `toZModPow 1`,
both kernels being the maximal ideal `(p)`. -/
theorem continuous_toZMod : Continuous (toZMod : ℤ_[p] → ZMod p) := by
  refine (IsLocallyConstant.iff_isOpen_fiber_apply.mpr fun x ↦ ?_).continuous
  have h : (toZMod : ℤ_[p] → ZMod p) ⁻¹' {toZMod x} = toZModPow 1 ⁻¹' {toZModPow 1 x} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, ← RingHom.sub_mem_ker_iff, ker_toZMod,
      ker_toZModPow, maximalIdeal_eq_span_p, pow_one]
  rw [h]
  exact (continuous_toZModPow 1).isOpen_preimage _ (isOpen_discrete _)

/-- Reducing the truncation `x mod p ^ n` further modulo `p` gives `x mod p`. -/
@[simp]
theorem cast_toZModPow_eq_toZMod {n : ℕ} (hn : n ≠ 0) (x : ℤ_[p]) :
    (ZMod.cast (toZModPow n x) : ZMod p) = toZMod x := by
  have h : toZMod (x - (x.appr n : ℤ_[p])) = 0 := by
    rw [← RingHom.mem_ker, ker_toZMod, maximalIdeal_eq_span_p]
    exact Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self (p : ℤ_[p]) hn) (appr_spec n x)
  rw [map_sub, sub_eq_zero] at h
  rw [h, toZModPow_eq_natCast_appr x n, ZMod.cast_natCast (dvd_pow_self p hn), map_natCast]

/-- A coarser truncation of `x` is a finer truncation of `x` read modulo the coarser
modulus. -/
theorem appr_modEq (x : ℤ_[p]) {m n : ℕ} (h : m ≤ n) : x.appr n ≡ x.appr m [MOD p ^ m] := by
  rw [← ZMod.natCast_eq_natCast_iff, ← ZMod.cast_natCast (pow_dvd_pow p h) (x.appr n),
    ← toZModPow_eq_natCast_appr, ← toZModPow_eq_natCast_appr, cast_toZModPow m n h]

/-- Truncation is additive modulo `p ^ n`. -/
theorem appr_add_modEq (x y : ℤ_[p]) (n : ℕ) :
    (x + y).appr n ≡ x.appr n + y.appr n [MOD p ^ n] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [← toZModPow_eq_natCast_appr, ← toZModPow_eq_natCast_appr, ← toZModPow_eq_natCast_appr,
    map_add]

/-- Truncation is multiplicative modulo `p ^ n`. -/
theorem appr_mul_modEq (x y : ℤ_[p]) (n : ℕ) :
    (x * y).appr n ≡ x.appr n * y.appr n [MOD p ^ n] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [← toZModPow_eq_natCast_appr, ← toZModPow_eq_natCast_appr, ← toZModPow_eq_natCast_appr,
    map_mul]

/-- Truncation fixes a natural number modulo `p ^ n`. -/
theorem appr_natCast_modEq (k n : ℕ) : ((k : ℤ_[p])).appr n ≡ k [MOD p ^ n] := by
  rw [← ZMod.natCast_eq_natCast_iff, ← toZModPow_eq_natCast_appr, map_natCast]

/-- The truncation `toZModPow n` identifies the quotient of `ℤ_[p]` by the ideal `(p ^ n)` with
`ZMod (p ^ n)`. This is the `p ^ n` analogue of `PadicInt.residueField`. -/
noncomputable def quotientSpanPowEquivZMod (n : ℕ) :
    ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ n} ≃+* ZMod (p ^ n) :=
  (Ideal.quotEquivOfEq (ker_toZModPow n).symm).trans
    (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective (toZModPow n)))

@[simp]
theorem quotientSpanPowEquivZMod_mk (n : ℕ) (x : ℤ_[p]) :
    quotientSpanPowEquivZMod n (Ideal.Quotient.mk _ x) = toZModPow n x := by
  simp [quotientSpanPowEquivZMod]

/-- A nonzero `p`-adic integer `x` generates the same ideal as `p ^ x.valuation`, since it is a
unit times that power of `p`. -/
theorem span_singleton_eq_span_pow_valuation {x : ℤ_[p]} (hx : x ≠ 0) :
    Ideal.span {x} = Ideal.span {(p : ℤ_[p]) ^ x.valuation} := by
  conv_lhs => rw [unitCoeff_spec hx]
  exact Ideal.span_singleton_mul_left_unit (unitCoeff hx).isUnit _

/-- The quotient of `ℤ_[p]` by the ideal generated by a nonzero element `x` is `ZMod (p ^ v)`,
where `v` is the valuation of `x`: the ideal `(x)` is `(p ^ v)`, and `toZModPow v` identifies the
quotient with `ZMod (p ^ v)`. -/
noncomputable def quotientSpanEquivZMod {x : ℤ_[p]} (hx : x ≠ 0) :
    ℤ_[p] ⧸ Ideal.span {x} ≃+* ZMod (p ^ x.valuation) :=
  (Ideal.quotEquivOfEq (span_singleton_eq_span_pow_valuation hx)).trans
    (quotientSpanPowEquivZMod _)

@[simp]
theorem quotientSpanEquivZMod_mk {x : ℤ_[p]} (hx : x ≠ 0) (y : ℤ_[p]) :
    quotientSpanEquivZMod hx (Ideal.Quotient.mk _ y) = toZModPow x.valuation y := by
  simp [quotientSpanEquivZMod]

/-- The quotient of `ℤ_[p]` by the ideal generated by a nonzero element is finite. -/
theorem finite_quotient_span {x : ℤ_[p]} (hx : x ≠ 0) : Finite (ℤ_[p] ⧸ Ideal.span {x}) :=
  have : NeZero p := ⟨hp.out.ne_zero⟩
  Finite.of_equiv _ (quotientSpanEquivZMod hx).symm.toEquiv

/-- The quotient of `ℤ_[p]` by the ideal generated by a nonzero element `x` has `p ^ v` elements,
where `v` is the valuation of `x`. -/
theorem natCard_quotient_span {x : ℤ_[p]} (hx : x ≠ 0) :
    Nat.card (ℤ_[p] ⧸ Ideal.span {x}) = p ^ x.valuation := by
  rw [Nat.card_congr (quotientSpanEquivZMod hx).toEquiv, Nat.card_zmod]

/-- The additive group of the quotient of `ℤ_[p]` by the ideal generated by a nonzero element is
cyclic, being that of `ZMod (p ^ v)`. -/
theorem isAddCyclic_quotient_span {x : ℤ_[p]} (hx : x ≠ 0) :
    IsAddCyclic (ℤ_[p] ⧸ Ideal.span {x}) :=
  isAddCyclic_of_surjective (quotientSpanEquivZMod hx).symm.toAddMonoidHom
    (quotientSpanEquivZMod hx).symm.surjective

/-- **Reduction modulo `p` of `ℤ_[p] ⧸ (q)`**, for `p ∣ q`: the ring homomorphism induced by
`toZMod`, whose kernel `(p)` contains `(q)`. -/
noncomputable def quotientSpanToZMod {q : ℤ_[p]} (hq : (p : ℤ_[p]) ∣ q) :
    ℤ_[p] ⧸ Ideal.span {q} →+* ZMod p :=
  Ideal.Quotient.lift _ toZMod fun a ha ↦ by
    rw [← RingHom.mem_ker, ker_toZMod, maximalIdeal_eq_span_p]
    exact Ideal.span_singleton_le_span_singleton.mpr hq ha

/-- Reduction modulo `p` of the class of `x` in `ℤ_[p] ⧸ (q)` is `x mod p`. -/
@[simp]
theorem quotientSpanToZMod_mk {q : ℤ_[p]} (hq : (p : ℤ_[p]) ∣ q) (x : ℤ_[p]) :
    quotientSpanToZMod hq (Ideal.Quotient.mk _ x) = toZMod x :=
  Ideal.Quotient.lift_mk _ _ _

/-- Reduction modulo `p` of `ℤ_[p] ⧸ (q)` is continuous for the quotient topology. -/
theorem continuous_quotientSpanToZMod {q : ℤ_[p]} (hq : (p : ℤ_[p]) ∣ q) :
    Continuous (quotientSpanToZMod hq) :=
  Ideal.Quotient.continuous_lift _ continuous_toZMod _

/-- **Truncation modulo `p ^ n` of `ℤ_[p] ⧸ (q)`**, for `p ^ n ∣ q`: the ring homomorphism
induced by `toZModPow n`, whose kernel `(p ^ n)` contains `(q)`. -/
noncomputable def quotientSpanToZModPow (n : ℕ) {q : ℤ_[p]} (hq : (p : ℤ_[p]) ^ n ∣ q) :
    ℤ_[p] ⧸ Ideal.span {q} →+* ZMod (p ^ n) :=
  Ideal.Quotient.lift _ (toZModPow n) fun a ha ↦ by
    rw [← RingHom.mem_ker, ker_toZModPow]
    exact Ideal.span_singleton_le_span_singleton.mpr hq ha

/-- Truncation modulo `p ^ n` of the class of `x` in `ℤ_[p] ⧸ (q)` is `x mod p ^ n`. -/
@[simp]
theorem quotientSpanToZModPow_mk (n : ℕ) {q : ℤ_[p]} (hq : (p : ℤ_[p]) ^ n ∣ q) (x : ℤ_[p]) :
    quotientSpanToZModPow n hq (Ideal.Quotient.mk _ x) = toZModPow n x :=
  Ideal.Quotient.lift_mk _ _ _

/-- Truncation modulo `p ^ n` of `ℤ_[p] ⧸ (q)` is continuous for the quotient topology. -/
theorem continuous_quotientSpanToZModPow (n : ℕ) {q : ℤ_[p]} (hq : (p : ℤ_[p]) ^ n ∣ q) :
    Continuous (quotientSpanToZModPow n hq) :=
  Ideal.Quotient.continuous_lift _ (continuous_toZModPow n) _

/-- Every unit of `ZMod (p ^ n)` lifts to a unit of `ℤ_[p]`. For `n > 0` this holds because
truncation is a surjective local homomorphism out of the local ring `ℤ_[p]`; for `n = 0` the
target `ZMod 1` is the trivial ring, so there is nothing to lift. -/
theorem surjective_units_map_toZModPow (n : ℕ) :
    Function.Surjective (Units.map (toZModPow n : ℤ_[p] →+* ZMod (p ^ n)).toMonoidHom) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
    exact fun u ↦ ⟨1, Subsingleton.elim _ _⟩
  · have : Fact (1 < p ^ n) := ⟨Nat.one_lt_pow hn.ne' hp.out.one_lt⟩
    exact IsLocalRing.surjective_units_map_of_local_ringHom _ (ZMod.ringHom_surjective _)
      (IsLocalHom.of_surjective _ (ZMod.ringHom_surjective _))

variable {M : Type*} [Monoid M] {g : M} {n : ℕ}

/-- Raising an element killed by `p ^ m` to the exponent `x.appr n` gives the same value for
every truncation level `n ≥ m`. This is what makes the `p`-adic power well defined. -/
theorem pow_appr_eq_pow_appr (x : ℤ_[p]) {m : ℕ} (hg : g ^ p ^ m = 1) (hmn : m ≤ n) :
    g ^ x.appr n = g ^ x.appr m :=
  pow_eq_pow_of_modEq (x.appr_modEq hmn) hg

end PadicInt
