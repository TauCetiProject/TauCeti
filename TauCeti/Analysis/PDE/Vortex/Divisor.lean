/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Symmetry
public import TauCeti.Analysis.PDE.Vortex.Zeros
public import TauCeti.Analysis.Complex.ContinuousLog.ArgumentPrinciple
public import Mathlib.Data.Sym.Basic
import Mathlib.Data.Finsupp.Multiset

/-!
# The zero divisor of a framed plane vortex

In the coordinates of `TauCeti.Vortex.equation`, a field `x = (b₁, b₂, p, q)` has section
`α = 2 (p + i q)` (`TauCeti.Vortex.sectionValue`). A multiset `D` of points of the plane is the
zero divisor of `x` (`TauCeti.Vortex.HasZeroDivisor x D`) when it is the zero divisor of `α` in
the sense of `TauCeti.HasZeroDivisor`: near every point `z` the section factors as
`α(w) = (w - z) ^ D(z) v(w)`, with `v` continuous at `z` and nonzero there; here `D(z)` is the
multiplicity of `z` in `D`. The general theory applies: a field has at most one zero divisor
(`TauCeti.Vortex.HasZeroDivisor.unique`), and its points are the zeros of `α`
(`TauCeti.Vortex.HasZeroDivisor.sectionValue_eq_zero_iff`).

Under the holomorphicity rows `∂bar_a α = 0` with `Cᵏ` connection coefficients, `k ≥ 1`, a
section that is not identically zero factors near every point as `(w - z) ^ n z * v w` with `v` of
class `Cᵏ` at `z` and nonzero there (`TauCeti.Vortex.exists_contDiffAt_sectionValue_eq_pow_mul`).
If `α` does not vanish near infinity, only finitely many exponents are nonzero, so the zero
divisor exists (`TauCeti.Vortex.exists_hasZeroDivisor`), and its factors can be taken of class
`Cᵏ` (`TauCeti.Vortex.HasZeroDivisor.exists_contDiffAt`).

The degree-`m` end framing is `α(z) (z / |z|)⁻ᵐ → 1` at infinity; every continuous field of the
affine space `A_m^s`, `s > 1`, has it (`TauCeti.Vortex.tendsto_sectionValue_mul_inv_pow`). The
topological argument principle `TauCeti.finsum_eq_of_tendsto_mul_inv_pow` shows that the end
framing forces the zero divisor to have degree `m` (`TauCeti.Vortex.HasZeroDivisor.card_eq`).
Hence the zeros of a framed degree-`m` vortex section, counted with multiplicity, form a point of
`Sym ℂ m` (`TauCeti.Vortex.exists_sym_hasZeroDivisor`). Only the holomorphicity rows are used; the
curvature equation is not needed. The identification of the degree with the flux
`(2π)⁻¹ ∫ i F_a` (Jaffe–Taubes, Chapter III) is
`TauCeti.Vortex.integral_curvature_eq_of_tendsto_sectionValue_mul_inv_pow`. Existence of a vortex
for a given divisor is not proved here.

The symmetries of the plane vortex equations act on zero divisors as expected. The translation
`translateField a` moves the divisor by `-a`, the rotation `rotateField u` rotates it by `u⁻¹`,
and a continuous gauge transformation leaves it unchanged. In particular the constant line-frame
gauge, and every framed gauge, preserves the divisor.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Birkhäuser, 1980, Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public noncomputable section

open Complex Filter Topology
open scoped ContDiff

namespace TauCeti.Vortex

/-- `D` is the **zero divisor** of the field `x`: it is the zero divisor of the section `α`, so
near every point `z` the section factors as `α(w) = (w - z) ^ D(z) v(w)` with `v` continuous at
`z` and nonzero there, where `D(z)` is the multiplicity of `z` in the multiset `D`. -/
@[expose] def HasZeroDivisor (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ) : Prop :=
  TauCeti.HasZeroDivisor (sectionValue x) D

/-- Unfolding `HasZeroDivisor`: the zero divisor of the field is that of its section. -/
theorem hasZeroDivisor_iff {x : ℂ → EuclideanSpace ℝ (Fin 4)} {D : Multiset ℂ} :
    HasZeroDivisor x D ↔ TauCeti.HasZeroDivisor (sectionValue x) D := Iff.rfl

/-- The vacuum has the empty zero divisor. -/
@[simp]
theorem hasZeroDivisor_vacuumField : HasZeroDivisor vacuumField 0 := fun _ ↦
  ⟨fun _ ↦ 1, continuousAt_const, one_ne_zero, .of_forall fun _ ↦ by
    simp [sectionValue_apply, vacuumField_apply]⟩

namespace HasZeroDivisor

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {D D' : Multiset ℂ}

/-- **Uniqueness of the zero divisor.** A field has at most one zero divisor, so the assignment
of its zero divisor to a field is well defined. -/
theorem unique (hD : HasZeroDivisor x D) (hD' : HasZeroDivisor x D') : D = D' :=
  TauCeti.HasZeroDivisor.unique hD hD'

/-- The zeros of the section are the points of the zero divisor. -/
theorem sectionValue_eq_zero_iff (hD : HasZeroDivisor x D) {z : ℂ} :
    sectionValue x z = 0 ↔ z ∈ D :=
  TauCeti.HasZeroDivisor.apply_eq_zero_iff hD

/-- **The zero divisor of a framed field has degree `m`.** If the section has the end framing
`α(z) (z / |z|)⁻ᵐ → 1`, the zero divisor has `m` points, counted with multiplicity. -/
theorem card_eq (hD : HasZeroDivisor x D) {m : ℕ}
    (hm : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    Multiset.card D = m :=
  TauCeti.HasZeroDivisor.card_eq hD hm

/-- **Translation law.** The pullback by `z ↦ z + a` moves the zero divisor by `-a`. -/
theorem translateField (hD : HasZeroDivisor x D) (a : ℂ) :
    HasZeroDivisor (Vortex.translateField a x) (D.map (· - a)) := by
  rw [hasZeroDivisor_iff, funext (sectionValue_translateField a x)]
  exact TauCeti.HasZeroDivisor.comp_add hD a

/-- **Rotation law.** The pullback by `z ↦ u z` rotates the zero divisor by `u⁻¹`. -/
theorem rotateField (hD : HasZeroDivisor x D) (u : Circle) :
    HasZeroDivisor (Vortex.rotateField u x) (D.map ((u : ℂ)⁻¹ * ·)) := by
  rw [hasZeroDivisor_iff, funext (sectionValue_rotateField u x)]
  exact TauCeti.HasZeroDivisor.comp_const_mul hD (Circle.coe_ne_zero u)

end HasZeroDivisor

/-- **Gauge invariance of the zero divisor.** A continuous gauge transformation, in particular a
framed gauge or a constant change of line frame, does not change the zero divisor. -/
@[simp]
theorem hasZeroDivisor_gaugeTransform_iff {x : ℂ → EuclideanSpace ℝ (Fin 4)} {D : Multiset ℂ}
    {u : ℂ → Circle} (hu : Continuous u) :
    HasZeroDivisor (gaugeTransform u x) D ↔ HasZeroDivisor x D := by
  have hc : Continuous fun z ↦ (u z : ℂ) := continuous_subtype_val.comp hu
  refine ⟨fun h ↦ h.of_eq_mul (u := fun z ↦ (u z : ℂ)⁻¹)
    (hc.inv₀ fun z ↦ Circle.coe_ne_zero _)
    (fun z ↦ inv_ne_zero (Circle.coe_ne_zero _)) fun z ↦ ?_,
    fun h ↦ h.of_eq_mul hc (fun z ↦ Circle.coe_ne_zero _)
      (sectionValue_gaugeTransform u x)⟩
  rw [sectionValue_gaugeTransform, inv_mul_cancel_left₀ (Circle.coe_ne_zero _)]

section Existence

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {k : ℕ∞} (hn : 1 ≤ k)
  (hb₁ : ContDiff ℝ k (fun w ↦ x w 0)) (hb₂ : ContDiff ℝ k (fun w ↦ x w 1))
  (hp : Differentiable ℝ (fun w ↦ x w 2)) (hq : Differentiable ℝ (fun w ↦ x w 3))
  (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)

include hn hb₁ hb₂ hp hq hhol

/-- **Existence of the zero divisor.** If the section of a field with `Cᵏ` connection
coefficients, `k ≥ 1`, satisfying the holomorphicity rows does not vanish near infinity, then it
has a zero divisor. -/
theorem exists_hasZeroDivisor (htail : ∀ᶠ w in cocompact ℂ, sectionValue x w ≠ 0) :
    ∃ D, HasZeroDivisor x D := by
  classical
  choose n v hvc hv₀ hvf using
    exists_contDiffAt_sectionValue_eq_pow_mul hn hb₁ hb₂ hp hq hhol htail.exists
  have hmult : ∀ z, ∃ u : ℂ → ℂ, ContinuousAt u z ∧ u z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, sectionValue x w = (w - z) ^ n z * u w :=
    fun z ↦ ⟨v z, (hvc z).continuousAt, hv₀ z, hvf z⟩
  refine ⟨Finsupp.toMultiset (Finsupp.ofSupportFinite n
    (finite_support_of_eventually_eq_pow_mul hmult htail)), fun z ↦ ?_⟩
  simpa only [Finsupp.count_toMultiset, Finsupp.ofSupportFinite_coe] using hmult z

/-- The factors of the zero divisor can be chosen of class `Cᵏ`, the regularity of the
connection coefficients. -/
theorem HasZeroDivisor.exists_contDiffAt {D : Multiset ℂ} (hD : HasZeroDivisor x D) (z : ℂ) :
    ∃ v : ℂ → ℂ, ContDiffAt ℝ k v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, sectionValue x w = (w - z) ^ D.count z * v w := by
  obtain ⟨n, v, hvc, hv₀, hvf⟩ :=
    exists_contDiffAt_sectionValue_eq_pow_mul hn hb₁ hb₂ hp hq hhol
      hD.exists_ne_zero z
  exact ⟨v, hvc, hv₀, hD.count_eq_of_eventually_eq_pow_mul hvc.continuousAt hv₀ hvf ▸ hvf⟩

/-- **The zero divisor of a framed degree-`m` vortex lies in `Sym ℂ m`.** If the section of a
field with `Cᵏ` connection coefficients, `k ≥ 1`, satisfying the holomorphicity rows has the end
framing `α(z) (z / |z|)⁻ᵐ → 1`, then it has a zero divisor of degree `m`. -/
theorem exists_sym_hasZeroDivisor {m : ℕ}
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    ∃ D : Sym ℂ m, HasZeroDivisor x D := by
  have htail : ∀ᶠ w in cocompact ℂ, sectionValue x w ≠ 0 := by
    filter_upwards [hframe.eventually_ne one_ne_zero] with w hw h0
    exact hw (by simp [h0])
  obtain ⟨D, hD⟩ := exists_hasZeroDivisor hn hb₁ hb₂ hp hq hhol htail
  exact ⟨⟨D, hD.card_eq hframe⟩, hD⟩

end Existence

end TauCeti.Vortex
