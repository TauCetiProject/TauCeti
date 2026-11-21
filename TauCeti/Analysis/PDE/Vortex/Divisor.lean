/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Dilation.Basic
public import TauCeti.Analysis.PDE.Vortex.Reconstruction
public import TauCeti.Analysis.PDE.Vortex.Symmetry
public import TauCeti.Analysis.PDE.Vortex.Uniqueness
public import TauCeti.Analysis.Complex.ZeroMultiplicity
public import Mathlib.Data.Sym.Basic
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import TauCeti.Topology.Sym.Basic
import TauCeti.Analysis.Complex.ContinuousLog.Rouche

/-!
# The zero divisor of a framed plane vortex

In the coordinates of `TauCeti.Vortex.equation`, a field `x = (b₁, b₂, p, q)` has section
`α = 2 (p + i q)` (`TauCeti.Vortex.sectionValue`). Its degree-`m` end framing is
`α(z) (z / |z|)⁻ᵐ → 1` at infinity; every continuous field of the affine space `A_m^s`, `s > 1`,
has it (`TauCeti.Vortex.tendsto_sectionValue_mul_inv_pow`).

Under the holomorphicity rows `∂bar_a α = 0` with `Cᵏ` connection coefficients, `k ≥ 1`, the
section factors near every point as `(w - z) ^ n z * v w` with `v` of class `Cᵏ` at `z` and
nonzero there (`TauCeti.Vortex.exists_contDiffAt_section_eq_pow_mul`), so `n` is a zero
multiplicity function of the section (`TauCeti.IsZeroMultiplicity`). When `α` is eventually nonzero
near infinity (in particular when `|α|² → 1`), the zeros are isolated and bounded, hence form an
effective divisor `D : Multiset ℂ`
(`TauCeti.Vortex.exists_multiset_sectionValue_eq_pow_count_mul`,
`TauCeti.Vortex.exists_multiset_isZeroMultiplicity_sectionValue`,
`TauCeti.Vortex.exists_multiset_isZeroMultiplicity_sectionValue_of_tendsto`). Under the degree-`m`
end framing, the topological argument principle `TauCeti.finsum_eq_of_tendsto_mul_inv_pow` shows
that the multiplicities add up to `m`. Hence the zeros of a framed degree-`m` vortex section,
counted with multiplicity, form an effective divisor of degree `m`, a point of `Sym ℂ m`
(`TauCeti.Vortex.exists_sym_sectionValue_eq_pow_count_mul`). Only the holomorphicity rows are
used; the curvature equation is not needed. The divisor is determined by the section, since zero
multiplicities are unique (`TauCeti.IsZeroMultiplicity.unique`).

The second part of the file proves how the divisor transforms, which is the action of the
symmetries of the vortex equations on `Sym^m ℂ`:

* translating a field by `a`, that is pulling it back by `z ↦ z + a`, moves its divisor by `-a`
  (`TauCeti.Vortex.isZeroMultiplicity_sectionValue_translateField`);
* rotating a field by `u`, that is pulling it back by `z ↦ u z`, rotates its divisor by `u⁻¹`
  (`TauCeti.Vortex.isZeroMultiplicity_sectionValue_rotateField`);
* dilating a field by `t ≠ 0`, that is pulling it back by `z ↦ t z`, divides its divisor by `t`
  (`TauCeti.Vortex.isZeroMultiplicity_sectionValue_dilateField`);
* continuous gauge transformations, in particular the smooth framed gauges and the constant
  line-frame gauges, do not change the divisor
  (`TauCeti.Vortex.isZeroMultiplicity_sectionValue_gaugeTransform`).

The divisor also depends continuously on the field: if fields converge locally uniformly, the
divisors of their sections converge in `Sym ℂ m`
(`TauCeti.Vortex.tendsto_of_tendstoLocallyUniformly`), by Hurwitz's theorem
`TauCeti.IsZeroMultiplicity.tendsto_of_tendstoLocallyUniformly`. Since `H^s(ℂ)`, `s > 1`, embeds
continuously in the bounded continuous functions, convergence in the affine field space `A_m^s` is
stronger than locally uniform convergence. The topology of `A_m^s` on its continuous fields, and the
resulting continuity of the divisor (`TauCeti.Vortex.SobolevFieldSpace.tendsto_of_tendsto`), are in
`TauCeti.Analysis.PDE.Vortex.FramedGauge.FieldTopology`.

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

/-- Local `Cᵏ` factorization and zero-multiplicity count of a section nonvanishing near infinity. -/
private theorem exists_multiset_isZeroMultiplicity_and_eq_pow_count_mul
    (htail : ∀ᶠ w in cocompact ℂ, sectionValue x w ≠ 0) :
    ∃ D : Multiset ℂ, IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) ∧
      ∀ z, ∃ v : ℂ → ℂ, ContDiffAt ℝ k v z ∧ v z ≠ 0 ∧
        ∀ᶠ w in 𝓝 z, sectionValue x w = (w - z) ^ D.count z * v w := by
  choose n v hvc hv₀ hvf using
    exists_contDiffAt_sectionValue_eq_pow_mul hn hb₁ hb₂ hp hq hhol htail.exists
  have hmult : IsZeroMultiplicity (sectionValue x) n :=
    isZeroMultiplicity_iff.2 fun z ↦ ⟨v z, (hvc z).continuousAt, hv₀ z, hvf z⟩
  obtain ⟨D, rfl⟩ := hmult.exists_eq_count htail
  exact ⟨D, hmult, fun z ↦ ⟨v z, hvc z, hv₀ z, hvf z⟩⟩

/-- **The zero divisor of a vortex section nonvanishing near infinity.** If the section of a field
with `Cᵏ` connection coefficients, `k ≥ 1`, satisfying the holomorphicity rows is eventually
nonzero near infinity, then there is an effective divisor `D : Multiset ℂ` whose multiplicity at
each `z` is the exponent of a local factorization `α(w) = (w - z) ^ D(z) v(w)`, with `v` of class
`Cᵏ` at `z` and nonzero there. -/
theorem exists_multiset_sectionValue_eq_pow_count_mul
    (htail : ∀ᶠ w in cocompact ℂ, sectionValue x w ≠ 0) :
    ∃ D : Multiset ℂ, ∀ z, ∃ v : ℂ → ℂ, ContDiffAt ℝ k v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, sectionValue x w = (w - z) ^ D.count z * v w :=
  let ⟨D, _, hD⟩ :=
    exists_multiset_isZeroMultiplicity_and_eq_pow_count_mul hn hb₁ hb₂ hp hq hhol htail
  ⟨D, hD⟩

omit hn hb₁ hb₂ hp hq hhol in
/-- The zero multiplicities of a field with `C¹` connection coefficients satisfying the
holomorphicity rows and nonvanishing near infinity are the counts of an effective divisor
`D : Multiset ℂ`: the form of `exists_multiset_sectionValue_eq_pow_count_mul` used by
`TauCeti.IsZeroMultiplicity`. -/
theorem exists_multiset_isZeroMultiplicity_sectionValue
    (hb₁ : ContDiff ℝ 1 (fun w ↦ x w 0)) (hb₂ : ContDiff ℝ 1 (fun w ↦ x w 1))
    (hp : Differentiable ℝ (fun w ↦ x w 2)) (hq : Differentiable ℝ (fun w ↦ x w 3))
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (htail : ∀ᶠ w in cocompact ℂ, sectionValue x w ≠ 0) :
    ∃ D : Multiset ℂ, IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z :=
  let ⟨D, hmult, _⟩ :=
    exists_multiset_isZeroMultiplicity_and_eq_pow_count_mul le_rfl hb₁ hb₂ hp hq hhol htail
  ⟨D, hmult⟩

omit hn hb₁ hb₂ hp hq hhol in
/-- The zero multiplicities of a field with `C¹` connection coefficients and differentiable section
satisfying the holomorphicity rows with `|α|² → 1` at infinity are the counts of an effective
divisor `D : Multiset ℂ`. -/
theorem exists_multiset_isZeroMultiplicity_sectionValue_of_tendsto
    (hb₁ : ContDiff ℝ 1 (fun w ↦ x w 0)) (hb₂ : ContDiff ℝ 1 (fun w ↦ x w 1))
    (hp : Differentiable ℝ (fun w ↦ x w 2)) (hq : Differentiable ℝ (fun w ↦ x w 3))
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    ∃ D : Multiset ℂ, IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z := by
  refine exists_multiset_isZeroMultiplicity_sectionValue hb₁ hb₂ hp hq hhol ?_
  filter_upwards [hlim.eventually (lt_mem_nhds zero_lt_one)] with w hw hz
  rw [sectionValue_eq_zero_iff] at hz
  simp [hz] at hw

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
  obtain ⟨D, hmult, hD⟩ :=
    exists_multiset_isZeroMultiplicity_and_eq_pow_count_mul hn hb₁ hb₂ hp hq hhol htail
  exact ⟨⟨D, hmult.card_eq_of_tendsto_mul_inv_pow hframe⟩, hD⟩

/-- The zero multiplicities of a framed degree-`m` field satisfying the holomorphicity rows are
the counts of an effective divisor of degree `m`: the form of
`exists_sym_sectionValue_eq_pow_count_mul` used by `TauCeti.IsZeroMultiplicity`. -/
theorem exists_sym_isZeroMultiplicity_sectionValue {m : ℕ}
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    ∃ D : Sym ℂ m, IsZeroMultiplicity (sectionValue x) fun z ↦ (D : Multiset ℂ).count z := by
  obtain ⟨D, hD⟩ := exists_sym_sectionValue_eq_pow_count_mul hn hb₁ hb₂ hp hq hhol hframe
  exact ⟨D, isZeroMultiplicity_iff.2 fun z ↦
    let ⟨v, hv, hv₀, hfac⟩ := hD z
    ⟨v, hv.continuousAt, hv₀, hfac⟩⟩

omit hn hb₁ hb₂ hp hq hhol

/-! ### The divisor under translations, rotations, dilations and gauge transformations -/

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
  convert h.comp_const_mul (Circle.coe_ne_zero u) using 1
  exact funext (sectionValue_rotateField u x)

/-- **Dilation law for the divisor.** Pulling a field back by `z ↦ t • z`, `t ≠ 0`, divides
its zero divisor `D` by `t`. -/
theorem isZeroMultiplicity_sectionValue_dilateField
    (h : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {t : ℝ}
    (ht : t ≠ 0) :
    IsZeroMultiplicity (sectionValue (dilateField t x))
      fun z ↦ (D.map ((t : ℂ)⁻¹ * ·)).count z := by
  convert h.comp_const_mul (Complex.ofReal_ne_zero.2 ht) using 1
  exact funext fun w ↦ by rw [sectionValue_dilateField, Complex.real_smul]

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

/-! ### Continuity of the divisor -/

/-- **Continuity of the divisor.** If fields `y i` converge locally uniformly to `x`, and the zero
multiplicities of their sections are the counts of `E i` and of `D` in `Sym ℂ m`, then `E i → D`
in `Sym ℂ m`. -/
theorem tendsto_of_tendstoLocallyUniformly {m : ℕ} {ι : Type*} {l : Filter ι}
    {y : ι → ℂ → EuclideanSpace ℝ (Fin 4)} {D : Sym ℂ m} {E : ι → Sym ℂ m}
    (hx : IsZeroMultiplicity (sectionValue x) fun z ↦ (D : Multiset ℂ).count z)
    (hy : ∀ᶠ i in l, IsZeroMultiplicity (sectionValue (y i)) fun z ↦ (E i : Multiset ℂ).count z)
    (hxy : TendstoLocallyUniformly y x l) : Tendsto E l (𝓝 D) := by
  -- the section is the value at the point of a `2`-Lipschitz function of the field
  set Φ : EuclideanSpace ℝ (Fin 4) → ℂ := fun v ↦ 2 * ((v 2 : ℂ) + (v 3 : ℂ) * I)
  have hΦ (u : ℂ → EuclideanSpace ℝ (Fin 4)) : Φ ∘ u = sectionValue u :=
    funext fun z ↦ (sectionValue_apply u z).symm
  have hlip : LipschitzWith 2 Φ := LipschitzWith.of_dist_le_mul fun v w ↦ by
    have h := norm_sectionValue_le ((fun _ ↦ v) - fun _ ↦ w) 0
    rw [sectionValue_sub, ← congrFun (hΦ _) 0, ← congrFun (hΦ _) 0] at h
    simpa [dist_eq_norm] using h
  have hsec := hlip.uniformContinuous.comp_tendstoLocallyUniformly hxy
  simp only [hΦ] at hsec
  exact hx.tendsto_of_tendstoLocallyUniformly hy hsec

end TauCeti.Vortex
