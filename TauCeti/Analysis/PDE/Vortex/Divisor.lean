/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Zeros
public import TauCeti.Analysis.Complex.ContinuousLog.ArgumentPrinciple
public import Mathlib.Data.Sym.Basic
import Mathlib.Data.Finsupp.Multiset

/-!
# The zero divisor of a framed plane vortex has degree `m`

In the coordinates of `TauCeti.Vortex.equation`, a field `x = (b₁, b₂, p, q)` has section
`α = 2 (p + i q)` (`TauCeti.Vortex.sectionValue`). Its degree-`m` end framing is
`α(z) (z / |z|)⁻ᵐ → 1` at infinity; every continuous field of the affine space `A_m^s`, `s > 1`,
has it (`TauCeti.Vortex.tendsto_sectionValue_mul_inv_pow`).

Under the holomorphicity rows `∂bar_a α = 0` with `Cᵏ` connection coefficients, `k ≥ 1`, the
section factors near every point as `(w - z) ^ n z * v w` with `v` of class `Cᵏ` at `z` and
nonzero there (`TauCeti.Vortex.exists_contDiffAt_section_eq_pow_mul`). The topological argument
principle `TauCeti.finsum_eq_of_tendsto_mul_inv_pow` shows that the end framing forces the
multiplicities to add up to `m`. Hence the zeros of a framed degree-`m` vortex section, counted
with multiplicity, form an effective divisor of degree `m`, a point of `Sym ℂ m`
(`TauCeti.Vortex.exists_sym_sectionValue_eq_pow_count_mul`). Any multiplicity function of the
section with continuous local factors sums to `m` as well, by the same argument principle. Only
the holomorphicity rows are used; the curvature equation is not needed.

This file proves that the total multiplicity of the zeros equals the framing degree `m`, so that
framed degree-`m` vortices have their divisors in `Sym^m ℂ`. The classical identification of
that total multiplicity with the flux `(2π)⁻¹ ∫ i F_a` (Jaffe–Taubes, Chapter III) is not proved
here, and neither is existence of a vortex for a given divisor.

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
  classical
  have htail : ∀ᶠ w in cocompact ℂ, sectionValue x w ≠ 0 := by
    filter_upwards [hframe.eventually_ne one_ne_zero] with w hw h0
    exact hw (by simp [h0])
  have hne : ∃ w, (x w 2 : ℂ) + I * x w 3 ≠ 0 := by
    obtain ⟨w, hw⟩ := htail.exists
    exact ⟨w, fun h ↦ hw (by rw [sectionValue_apply, mul_comm (x w 3 : ℂ), h, mul_zero])⟩
  choose n v hvc hv0 hvf using
    exists_contDiffAt_section_eq_pow_mul hn hb₁ hb₂ hp hq hhol hne
  have hvf' : ∀ z, ∀ᶠ w in 𝓝 z, sectionValue x w = (w - z) ^ n z * v z w := fun z ↦ by
    filter_upwards [hvf z] with w hw
    rw [sectionValue_apply, mul_comm (x w 3 : ℂ), hw]
  have hmult : ∀ z, ∃ u : ℂ → ℂ, ContinuousAt u z ∧ u z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, sectionValue x w = (w - z) ^ n z * u w :=
    fun z ↦ ⟨v z, (hvc z).continuousAt, hv0 z, hvf' z⟩
  have hfin := finite_support_of_eventually_eq_pow_mul hmult htail
  set N := Finsupp.ofSupportFinite n hfin with hNdef
  have hcard : Multiset.card (Finsupp.toMultiset N) = m := by
    rw [Finsupp.card_toMultiset, Finsupp.sum, ← finsum_eq_of_tendsto_mul_inv_pow hmult hframe,
      finsum_eq_sum_of_support_subset n (s := N.support) fun z hz ↦ ?_]
    · simp [hNdef, Finsupp.ofSupportFinite_coe]
    · simpa [hNdef, Finsupp.mem_support_iff, Finsupp.ofSupportFinite_coe] using hz
  refine ⟨⟨Finsupp.toMultiset N, hcard⟩, fun z ↦ ⟨v z, hvc z, hv0 z, ?_⟩⟩
  simpa only [Sym.coe_mk, Finsupp.count_toMultiset, hNdef, Finsupp.ofSupportFinite_coe] using
    hvf' z

end TauCeti.Vortex
