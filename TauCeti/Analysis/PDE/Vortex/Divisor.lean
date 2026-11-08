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
import TauCeti.Algebra.BigOperators.Finprod

/-!
# The zero divisor of a framed plane vortex

In the coordinates of `TauCeti.Vortex.equation`, a field `x = (b₁, b₂, p, q)` has section
`α = 2 (p + i q)` (`TauCeti.Vortex.sectionValue`). A multiset `D` of points of the plane is the
zero divisor of `x` (`TauCeti.Vortex.IsZeroDivisor x D`) when near every point `z` the section
factors as `α(w) = (w - z) ^ D(z) v(w)`, with `v` continuous at `z` and nonzero there; here `D(z)`
is the multiplicity of `z` in `D`. Since the exponent of such a factorization is unique
(`TauCeti.eq_of_eventually_sub_pow_mul_eq`), a field has at most one zero divisor
(`TauCeti.Vortex.IsZeroDivisor.eq`), and its points are the zeros of `α`.

Under the holomorphicity rows `∂bar_a α = 0` with `Cᵏ` connection coefficients, `k ≥ 1`, a
section that is not identically zero factors near every point as `(w - z) ^ n z * v w` with `v` of
class `Cᵏ` at `z` and nonzero there (`TauCeti.Vortex.exists_contDiffAt_sectionValue_eq_pow_mul`).
If `α` does not vanish near infinity, only finitely many exponents are nonzero, so the zero
divisor exists (`TauCeti.Vortex.exists_isZeroDivisor`), and its factors can be taken of class
`Cᵏ` (`TauCeti.Vortex.IsZeroDivisor.exists_contDiffAt`).

The degree-`m` end framing is `α(z) (z / |z|)⁻ᵐ → 1` at infinity; every continuous field of the
affine space `A_m^s`, `s > 1`, has it (`TauCeti.Vortex.tendsto_sectionValue_mul_inv_pow`). The
topological argument principle `TauCeti.finsum_eq_of_tendsto_mul_inv_pow` shows that the end
framing forces the zero divisor to have degree `m` (`TauCeti.Vortex.IsZeroDivisor.card_eq`).
Hence the zeros of a framed degree-`m` vortex section, counted with multiplicity, form a point of
`Sym ℂ m` (`TauCeti.Vortex.exists_sym_isZeroDivisor`). Only the holomorphicity rows are used; the
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

/-- `D` is the **zero divisor** of the section `α` of the field `x`: near every point `z`, the
section factors as `α(w) = (w - z) ^ D(z) v(w)` with `v` continuous at `z` and nonzero there,
where `D(z)` is the multiplicity of `z` in the multiset `D`. -/
def IsZeroDivisor (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ) : Prop :=
  ∀ z, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧
    ∀ᶠ w in 𝓝 z, sectionValue x w = (w - z) ^ D.count z * v w

/-- Unfolding `IsZeroDivisor`: the local factorizations of the section. -/
theorem isZeroDivisor_iff {x : ℂ → EuclideanSpace ℝ (Fin 4)} {D : Multiset ℂ} :
    IsZeroDivisor x D ↔ ∀ z, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, sectionValue x w = (w - z) ^ D.count z * v w := Iff.rfl

/-- The vacuum has the empty zero divisor. -/
@[simp]
theorem isZeroDivisor_vacuumField : IsZeroDivisor vacuumField 0 := fun _ ↦
  ⟨fun _ ↦ 1, continuousAt_const, one_ne_zero, .of_forall fun _ ↦ by
    simp [sectionValue_apply, vacuumField_apply]⟩

namespace IsZeroDivisor

variable {x y : ℂ → EuclideanSpace ℝ (Fin 4)} {D D' : Multiset ℂ}

/-- **Uniqueness of the zero divisor.** The multiplicities are the exponents of the local
factorizations of the section, which are unique. -/
theorem eq (hD : IsZeroDivisor x D) (hD' : IsZeroDivisor x D') : D = D' := by
  refine Multiset.ext.2 fun z ↦ ?_
  obtain ⟨u, hu, hu₀, hfu⟩ := hD z
  obtain ⟨v, hv, hv₀, hfv⟩ := hD' z
  refine eq_of_eventually_sub_pow_mul_eq hu hu₀ hv hv₀ ?_
  filter_upwards [hfu, hfv] with w hwu hwv
  rw [← hwu, ← hwv]

/-- The zeros of the section are the points of its zero divisor. -/
theorem sectionValue_eq_zero_iff (hD : IsZeroDivisor x D) {z : ℂ} :
    sectionValue x z = 0 ↔ z ∈ D := by
  obtain ⟨v, -, hv₀, hfv⟩ := hD z
  simp [hfv.self_of_nhds, hv₀]

/-- A section with a zero divisor is not identically zero: it does not vanish off the finitely
many points of the divisor. -/
theorem exists_sectionValue_ne_zero (hD : IsZeroDivisor x D) : ∃ w, sectionValue x w ≠ 0 := by
  classical
  obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset D.toFinset
  exact ⟨w, fun h ↦ hw (Multiset.mem_toFinset.2 (hD.sectionValue_eq_zero_iff.1 h))⟩

/-- **The zero divisor of a framed field has degree `m`.** If the section has the degree-`m` end
framing `α(z) (z / |z|)⁻ᵐ → 1`, its zero divisor has `m` points, counted with multiplicity. This
is the topological argument principle. -/
theorem card_eq (hD : IsZeroDivisor x D) {m : ℕ}
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    Multiset.card D = m := by
  rw [← finsum_eq_of_tendsto_mul_inv_pow (n := fun z ↦ D.count z) hD hframe]
  simpa using (Multiset.finsum_count_eq_card (R := ℕ) D).symm

/-- Multiplying the section by a continuous nowhere-vanishing function preserves the zero
divisor. -/
theorem of_sectionValue_eq_mul (hD : IsZeroDivisor x D) {g : ℂ → ℂ} (hg : Continuous g)
    (hg₀ : ∀ z, g z ≠ 0) (hxy : ∀ z, sectionValue y z = g z * sectionValue x z) :
    IsZeroDivisor y D := fun z ↦ by
  obtain ⟨v, hv, hv₀, hfv⟩ := hD z
  refine ⟨fun w ↦ g w * v w, hg.continuousAt.mul hv, mul_ne_zero (hg₀ z) hv₀, ?_⟩
  filter_upwards [hfv] with w hw
  rw [hxy, hw]
  ring

/-- **Translation law.** The pullback by `z ↦ z + a` moves the zero divisor by `-a`. -/
theorem translateField (hD : IsZeroDivisor x D) (a : ℂ) :
    IsZeroDivisor (Vortex.translateField a x) (D.map (· - a)) := fun z ↦ by
  obtain ⟨v, hv, hv₀, hfv⟩ := hD (z + a)
  have hcount : (D.map (· - a)).count z = D.count (z + a) := by
    simpa using Multiset.count_map_eq_count' (· - a) D (sub_left_injective) (z + a)
  have ht : Tendsto (· + a) (𝓝 z) (𝓝 (z + a)) := (continuous_id.add continuous_const).tendsto z
  refine ⟨fun w ↦ v (w + a),
    hv.comp_of_eq (continuous_id.add continuous_const).continuousAt rfl, hv₀, ?_⟩
  filter_upwards [ht.eventually hfv] with w hw
  rw [sectionValue_translateField, hw, hcount, add_sub_add_right_eq_sub]

/-- **Rotation law.** The pullback by `z ↦ u z` rotates the zero divisor by `u⁻¹`. -/
theorem rotateField (hD : IsZeroDivisor x D) (u : Circle) :
    IsZeroDivisor (Vortex.rotateField u x) (D.map ((u : ℂ)⁻¹ * ·)) := fun z ↦ by
  have hu : (u : ℂ) ≠ 0 := Circle.coe_ne_zero u
  obtain ⟨v, hv, hv₀, hfv⟩ := hD (u * z)
  have hcount : (D.map ((u : ℂ)⁻¹ * ·)).count z = D.count (u * z) := by
    simpa [inv_mul_cancel_left₀ hu] using
      Multiset.count_map_eq_count' ((u : ℂ)⁻¹ * ·) D (mul_right_injective₀ (inv_ne_zero hu))
        (u * z)
  have ht : Tendsto ((u : ℂ) * ·) (𝓝 z) (𝓝 (u * z)) :=
    (continuous_const.mul continuous_id).tendsto z
  refine ⟨fun w ↦ (u : ℂ) ^ D.count (u * z) * v (u * w),
    continuousAt_const.mul
      (hv.comp_of_eq (continuous_const.mul continuous_id).continuousAt rfl),
    mul_ne_zero (pow_ne_zero _ hu) hv₀, ?_⟩
  filter_upwards [ht.eventually hfv] with w hw
  rw [sectionValue_rotateField, hw, hcount, ← mul_sub, mul_pow]
  ring

end IsZeroDivisor

/-- **Gauge invariance of the zero divisor.** A continuous gauge transformation, in particular a
framed gauge or a constant change of line frame, does not change the zero divisor. -/
@[simp]
theorem isZeroDivisor_gaugeTransform_iff {x : ℂ → EuclideanSpace ℝ (Fin 4)} {D : Multiset ℂ}
    {u : ℂ → Circle} (hu : Continuous u) :
    IsZeroDivisor (gaugeTransform u x) D ↔ IsZeroDivisor x D := by
  have hc : Continuous fun z ↦ (u z : ℂ) := continuous_subtype_val.comp hu
  refine ⟨fun h ↦ h.of_sectionValue_eq_mul (g := fun z ↦ (u z : ℂ)⁻¹)
    (hc.inv₀ fun z ↦ Circle.coe_ne_zero _)
    (fun z ↦ inv_ne_zero (Circle.coe_ne_zero _)) fun z ↦ ?_,
    fun h ↦ h.of_sectionValue_eq_mul hc (fun z ↦ Circle.coe_ne_zero _)
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
theorem exists_isZeroDivisor (htail : ∀ᶠ w in cocompact ℂ, sectionValue x w ≠ 0) :
    ∃ D, IsZeroDivisor x D := by
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
theorem IsZeroDivisor.exists_contDiffAt {D : Multiset ℂ} (hD : IsZeroDivisor x D) (z : ℂ) :
    ∃ v : ℂ → ℂ, ContDiffAt ℝ k v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, sectionValue x w = (w - z) ^ D.count z * v w := by
  obtain ⟨n, v, hvc, hv₀, hvf⟩ :=
    exists_contDiffAt_sectionValue_eq_pow_mul hn hb₁ hb₂ hp hq hhol
      hD.exists_sectionValue_ne_zero z
  obtain ⟨u, hu, hu₀, hfu⟩ := hD z
  have hcount : D.count z = n := eq_of_eventually_sub_pow_mul_eq hu hu₀ hvc.continuousAt hv₀ <| by
    filter_upwards [hfu, hvf] with w hwu hwv
    rw [← hwu, ← hwv]
  exact ⟨v, hvc, hv₀, hcount ▸ hvf⟩

/-- **The zero divisor of a framed degree-`m` vortex lies in `Sym ℂ m`.** If the section of a
field with `Cᵏ` connection coefficients, `k ≥ 1`, satisfying the holomorphicity rows has the end
framing `α(z) (z / |z|)⁻ᵐ → 1`, then it has a zero divisor of degree `m`. -/
theorem exists_sym_isZeroDivisor {m : ℕ}
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    ∃ D : Sym ℂ m, IsZeroDivisor x D := by
  have htail : ∀ᶠ w in cocompact ℂ, sectionValue x w ≠ 0 := by
    filter_upwards [hframe.eventually_ne one_ne_zero] with w hw h0
    exact hw (by simp [h0])
  obtain ⟨D, hD⟩ := exists_isZeroDivisor hn hb₁ hb₂ hp hq hhol htail
  exact ⟨⟨D, hD.card_eq hframe⟩, hD⟩

end Existence

end TauCeti.Vortex
