/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Reconstruction
public import TauCeti.Analysis.PDE.Vortex.Symmetry
public import TauCeti.Analysis.PDE.Vortex.Uniqueness
public import TauCeti.Analysis.Complex.ZeroMultiplicity
public import Mathlib.Data.Sym.Basic

/-!
# The zero divisor of a framed plane vortex

In the coordinates of `TauCeti.Vortex.equation`, a field `x = (b₁, b₂, p, q)` has section
`α = 2 (p + i q)` (`TauCeti.Vortex.sectionValue`). Its degree-`m` end framing is
`α(z) (z / |z|)⁻ᵐ → 1` at infinity; every continuous field of the affine space `A_m^s`, `s > 1`,
has it (`TauCeti.Vortex.tendsto_sectionValue_mul_inv_pow`).

Under the holomorphicity rows `∂bar_a α = 0` with `Cᵏ` connection coefficients, `k ≥ 1`, the
section factors near every point as `(w - z) ^ n z * v w` with `v` of class `Cᵏ` at `z` and
nonzero there (`TauCeti.Vortex.exists_contDiffAt_section_eq_pow_mul`), so `n` is a zero
multiplicity function of the section (`TauCeti.IsZeroMultiplicity`). The topological argument
principle `TauCeti.finsum_eq_of_tendsto_mul_inv_pow` shows that the end framing forces the
multiplicities to add up to `m`. Hence the zeros of a framed degree-`m` vortex section, counted
with multiplicity, form an effective divisor of degree `m`, a point of `Sym ℂ m`
(`TauCeti.Vortex.exists_sym_sectionValue_eq_pow_count_mul`). Only the holomorphicity rows are
used; the curvature equation is not needed. The divisor is determined by the section, since zero
multiplicities are unique (`TauCeti.IsZeroMultiplicity.unique`).

The second part of the file proves how the divisor transforms, which is the action of the
symmetries of the vortex equations on `Sym^m ℂ`:

* translating a field by `a`, that is pulling it back by `z ↦ z + a`, moves its divisor by `-a`
  (`TauCeti.Vortex.isZeroMultiplicity_sectionValue_translateField`);
* rotating a field by `u`, that is pulling it back by `z ↦ u z`, rotates its divisor by `u⁻¹`
  (`TauCeti.Vortex.isZeroMultiplicity_sectionValue_rotateField`);
* continuous gauge transformations, in particular the smooth framed gauges and the constant
  line-frame gauges, do not change the divisor
  (`TauCeti.Vortex.isZeroMultiplicity_sectionValue_gaugeTransform`).

Conversely, by Taubes's uniqueness theorem
(`TauCeti.Vortex.existsUnique_framedGaugeGroup_smul_eq`), two smooth framed vortices with a common
end framing are related by a framed gauge exactly when their divisors are equal
(`TauCeti.Vortex.exists_framedGaugeGroup_smul_eq_iff`): the divisor is a complete invariant of
the framed gauge orbit. In the other direction, the field reconstructed from `∏_{a ∈ D} (w - a)`
and a continuous amplitude has divisor `D`
(`TauCeti.Vortex.isZeroMultiplicity_sectionValue_amplitudeField_prod_sub`). Existence of a
vortex for a given divisor is not proved here.

The identification of the framing degree with the flux `(2π)⁻¹ ∫ i F_a` (Jaffe–Taubes,
Chapter III) is `TauCeti.Vortex.integral_curvature_eq_of_tendsto_sectionValue_mul_inv_pow`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Birkhäuser, 1980, Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public noncomputable section

open Complex Filter Topology
open scoped ContDiff

namespace TauCeti.Vortex

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {k : ℕ∞} (hn : 1 ≤ k)
  (hb₁ : ContDiff ℝ k (fun w ↦ x w 0)) (hb₂ : ContDiff ℝ k (fun w ↦ x w 1))
  (hp : Differentiable ℝ (fun w ↦ x w 2)) (hq : Differentiable ℝ (fun w ↦ x w 3))
  (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)

include hn hb₁ hb₂ hp hq hhol

/-- **The zero divisor of a framed degree-`m` vortex lies in `Sym ℂ m`.** If the section of a
field with `Cᵏ` connection coefficients, `k ≥ 1`, satisfying the holomorphicity rows has the
end framing `α(z) (z / |z|)⁻ᵐ → 1`, then there is an effective divisor `D` of degree `m` whose
multiplicity at each `z` is the exponent of a local factorization `α(w) = (w - z) ^ D(z) v(w)`,
with `v` of class `Cᵏ` at `z` and nonzero there. -/
theorem exists_sym_sectionValue_eq_pow_count_mul {m : ℕ}
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    ∃ D : Sym ℂ m, ∀ z, ∃ v : ℂ → ℂ, ContDiffAt ℝ k v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, sectionValue x w = (w - z) ^ Multiset.count z (D : Multiset ℂ) * v w := by
  have htail : ∀ᶠ w in cocompact ℂ, sectionValue x w ≠ 0 := by
    filter_upwards [hframe.eventually_ne one_ne_zero] with w hw h0
    exact hw (by simp [h0])
  choose n v hvc hv₀ hvf using
    exists_contDiffAt_sectionValue_eq_pow_mul hn hb₁ hb₂ hp hq hhol htail.exists
  have hmult : IsZeroMultiplicity (sectionValue x) n :=
    isZeroMultiplicity_iff.2 fun z ↦ ⟨v z, (hvc z).continuousAt, hv₀ z, hvf z⟩
  obtain ⟨D, rfl⟩ := hmult.exists_eq_count htail
  exact ⟨⟨D, hmult.card_eq_of_tendsto_mul_inv_pow hframe⟩, fun z ↦ ⟨v z, hvc z, hv₀ z, hvf z⟩⟩

omit hn hb₁ hb₂ hp hq hhol

/-! ### The divisor under translations, rotations and gauge transformations -/

section Laws

variable {y : ℂ → EuclideanSpace ℝ (Fin 4)} {D D' : Multiset ℂ}

/-- **Translation law for the divisor.** Translating a field by `a`, that is pulling it back by
`z ↦ z + a`, moves its zero divisor `D` to `D - a`. -/
theorem isZeroMultiplicity_sectionValue_translateField
    (h : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) (a : ℂ) :
    IsZeroMultiplicity (sectionValue (translateField a x)) fun z ↦ (D.map (· - a)).count z := by
  convert h.comp_mul_add one_ne_zero a using 1
  · funext w
    rw [sectionValue_translateField, one_mul]
  · funext z
    rw [one_mul, ← Multiset.count_map_eq_count' (· - a) D (sub_left_injective (b := a)) (z + a),
      add_sub_cancel_right]

/-- **Rotation law for the divisor.** Rotating a field by `u`, that is pulling it back by
`z ↦ u z`, rotates its zero divisor `D` to `u⁻¹ D`. -/
theorem isZeroMultiplicity_sectionValue_rotateField
    (h : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) (u : Circle) :
    IsZeroMultiplicity (sectionValue (rotateField u x))
      fun z ↦ (D.map ((u : ℂ)⁻¹ * ·)).count z := by
  have hu := Circle.coe_ne_zero u
  convert h.comp_mul_add hu 0 using 1
  · funext w
    rw [sectionValue_rotateField, add_zero]
  · funext z
    rw [add_zero, ← Multiset.count_map_eq_count' ((u : ℂ)⁻¹ * ·) D
      (mul_right_injective₀ (inv_ne_zero hu)) (u * z), inv_mul_cancel_left₀ hu]

/-- **Gauge invariance of the divisor.** A continuous gauge transformation multiplies the
section by a function without zeros, so it does not change the zero multiplicities. This applies
to the smooth framed gauges and to the constant line-frame gauges. -/
theorem isZeroMultiplicity_sectionValue_gaugeTransform {n : ℂ → ℕ} {u : ℂ → Circle}
    (hu : Continuous fun z ↦ (u z : ℂ)) (h : IsZeroMultiplicity (sectionValue x) n) :
    IsZeroMultiplicity (sectionValue (gaugeTransform u x)) n := by
  rw [show sectionValue (gaugeTransform u x) = fun w ↦ (u w : ℂ) * sectionValue x w from
    funext (sectionValue_gaugeTransform u x)]
  exact h.mul_left_of_continuous hu fun z ↦ Circle.coe_ne_zero (u z)

/-- Smooth framed gauges do not change the zero multiplicities. -/
theorem isZeroMultiplicity_sectionValue_framedGaugeGroup_smul {n : ℂ → ℕ}
    (h : IsZeroMultiplicity (sectionValue x) n) (u : framedGaugeGroup) :
    IsZeroMultiplicity (sectionValue (u • x)) n :=
  isZeroMultiplicity_sectionValue_gaugeTransform
    ((mem_framedGaugeGroup _).1 u.property).1.continuous h

/-- **The divisor is a complete invariant of the framed gauge orbit.** Two smooth vortices `x`
and `y` with the same end framing `α (z) · phase (z) → 1`, where `|phase| → 1` at infinity, and
with zero divisors `D` and `D'`, are related by a smooth framed gauge exactly when `D = D'`. -/
theorem exists_framedGaugeGroup_smul_eq_iff (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hxsol : ∀ z, equation x z = 0) (hysol : ∀ z, equation y z = 0) {phase : ℂ → ℂ}
    (hphase : Tendsto (fun z ↦ ‖phase z‖) (cocompact ℂ) (𝓝 1))
    (hxfr : Tendsto (fun z ↦ sectionValue x z * phase z) (cocompact ℂ) (𝓝 1))
    (hyfr : Tendsto (fun z ↦ sectionValue y z * phase z) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z)
    (hD' : IsZeroMultiplicity (sectionValue y) fun z ↦ D'.count z) :
    (∃ u : framedGaugeGroup, u • y = x) ↔ D = D' := by
  refine ⟨fun ⟨u, hu⟩ ↦ Multiset.ext.2 fun z ↦ ?_, fun hDD' ↦ ?_⟩
  · have h := isZeroMultiplicity_sectionValue_framedGaugeGroup_smul hD' u
    rw [hu] at h
    exact congrFun (hD.unique h) z
  · subst hDD'
    exact (existsUnique_framedGaugeGroup_smul_eq hx hy hxsol hysol hphase hxfr hyfr
      (isZeroMultiplicity_iff.1 hD) (isZeroMultiplicity_iff.1 hD')).exists

/-- A reconstructed field with a continuous amplitude `u` has the zero multiplicities of the
function `f` it is built from, since its section is `exp(u) f`. -/
theorem isZeroMultiplicity_sectionValue_amplitudeField {u : ℂ → ℝ} (hu : Continuous u)
    {f : ℂ → ℂ} {n : ℂ → ℕ} (h : IsZeroMultiplicity f n) :
    IsZeroMultiplicity (sectionValue (amplitudeField u f)) n := by
  rw [show sectionValue (amplitudeField u f) = fun w ↦ (Real.exp (u w) : ℂ) * f w from
    funext (sectionValue_amplitudeField u f)]
  exact h.mul_left_of_continuous (by fun_prop) fun z ↦ by simp

/-- **The divisor of a reconstructed field.** The field reconstructed from `∏_{a ∈ D} (w - a)`
and a continuous amplitude has zero divisor `D`. -/
theorem isZeroMultiplicity_sectionValue_amplitudeField_prod_sub {u : ℂ → ℝ} (hu : Continuous u)
    (D : Multiset ℂ) :
    IsZeroMultiplicity (sectionValue (amplitudeField u fun w ↦ (D.map fun a ↦ w - a).prod))
      fun z ↦ D.count z :=
  isZeroMultiplicity_sectionValue_amplitudeField hu (isZeroMultiplicity_prod_sub D)

end Laws

end TauCeti.Vortex
