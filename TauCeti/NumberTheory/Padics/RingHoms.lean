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
import Mathlib.RingTheory.LocalRing.RingHom.Basic

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
* `PadicInt.continuous_toZModPow`: truncation modulo `p ^ n` is continuous, `ZMod (p ^ n)`
  carrying the discrete topology.
* `PadicInt.appr_modEq`, `PadicInt.appr_add_modEq`, `PadicInt.appr_mul_modEq`,
  `PadicInt.appr_natCast_modEq`: the truncations are compatible with each other and with the
  ring operations, modulo `p ^ n`.
* `PadicInt.pow_appr_eq_pow_appr`: raising an element of `p`-power order to the truncated
  exponent is independent of the truncation level, once that level is large enough.
* `PadicInt.quotientSpanPowEquivZMod`: `toZModPow n` identifies `ℤ_[p] ⧸ (p ^ n)` with
  `ZMod (p ^ n)`.
* `PadicInt.surjective_units_map_toZModPow`: every unit of `ZMod (p ^ n)` lifts to a unit of
  `ℤ_[p]`.
-/

public section

namespace PadicInt

variable {p : ℕ} [hp : Fact p.Prime]

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
