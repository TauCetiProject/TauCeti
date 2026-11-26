/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import TauCeti.Analysis.Complex.Theta.Factor
public import TauCeti.Analysis.Complex.Wirtinger.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import TauCeti.Analysis.Complex.UpperHalfPlane.PeriodPair

/-!
# The Hermitian metric and Chern connection of the level-`k` theta line

Fix `τ ∈ ℂ`, an integer level `k` and real characteristics `α, β`. For `Im τ ≠ 0`, the function
`h(z) = exp (-2πk (Im z)² / Im τ)` (`TauCeti.thetaMetric`) satisfies
`h(z + λ) |e_λ(z)|² = h(z)` (`TauCeti.thetaMetric_add_mul_norm_thetaFactor_sq`), so it is a
Hermitian metric on the theta line: for two sections `s, t` the pairing `h s conj t` is invariant
under the lattice, that is, it descends to the torus (`TauCeti.thetaMetric_add_mul_mul_conj`).
For `Im τ ≠ 0` the pointwise norm `h |s|²` of a continuous section is therefore bounded
(`TauCeti.exists_thetaMetric_mul_norm_sq_le`).

The Chern connection of `h` on holomorphic sections is `d + A dz` with
`A = ∂ log h = 2πik Im z / Im τ` (`TauCeti.thetaConnectionForm`,
`TauCeti.wirtingerDeriv_apply_one_log_thetaMetric`), computed from the Wirtinger derivatives
`∂ Im = -i/2` and `∂bar Im = i/2` (`TauCeti.wirtingerDeriv_apply_one_ofReal_im`,
`TauCeti.conjWirtingerDeriv_apply_one_ofReal_im`). It is compatible with the factor of automorphy:
`A(z + λ) + e_λ'(z) / e_λ(z) = A(z)` (`TauCeti.thetaConnectionForm_add_add_logDeriv_thetaFactor`),
which is the transformation law of a connection form under the transition function `e_λ`, so the
connection descends to the theta line. Its curvature is `∂bar A d(conj z) ∧ dz` with
`∂bar A = -πk / Im τ` (`TauCeti.conjWirtingerDeriv_apply_one_thetaConnectionForm`). In the real
coordinates `z = q + τ p`, `d(conj z) ∧ dz = 2i Im τ dq ∧ dp`, so the curvature is
`-2πik dq ∧ dp`; this is `-(i/ℏ) ω` for the symplectic form `ω = 2πℏk dq ∧ dp`, so the theta line
of level `k` is a prequantum line of `ω`.

## Main definitions

* `TauCeti.thetaMetric k τ z`: the Hermitian metric `exp (-2πk (Im z)² / Im τ)`.
* `TauCeti.thetaConnectionForm k τ z`: the `dz`-coefficient `2πik Im z / Im τ` of its Chern
  connection form.

## Main results

* `TauCeti.thetaMetric_add_mul_norm_thetaFactor_sq`, `TauCeti.thetaMetric_add_mul_mul_conj`,
  `TauCeti.thetaMetric_add_mul_norm_sq`: the metric descends to the torus.
* `TauCeti.exists_thetaMetric_mul_norm_sq_le`: continuous sections have bounded pointwise norm.
* `TauCeti.wirtingerDeriv_apply_one_log_thetaMetric`,
  `TauCeti.thetaConnectionForm_add_add_logDeriv_thetaFactor`,
  `TauCeti.conjWirtingerDeriv_apply_one_thetaConnectionForm`: the Chern connection form, its
  gauge law, and its curvature.

## References

* David Mumford, *Tata Lectures on Theta I*, Progress in Mathematics 28, Birkhäuser, 1983,
  Chapter I, §§1–3 (theta functions with characteristics and their functional equations).
* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 2 (factors of
  automorphy, the canonical factor and its Hermitian metric).
-/

public section

open Complex ComplexConjugate Real

namespace TauCeti

variable {k : ℤ} {τ : ℂ} {α β : ℝ}

/-- The **Hermitian metric** `h(z) = exp (-2πk (Im z)² / Im τ)` of the level-`k` theta line on
`ℂ / (ℤ + τℤ)`, in the trivialization of its pull-back to `ℂ`. -/
noncomputable def thetaMetric (k : ℤ) (τ z : ℂ) : ℝ :=
  Real.exp (-2 * π * k * z.im ^ 2 / τ.im)

theorem thetaMetric_def (z : ℂ) :
    thetaMetric k τ z = Real.exp (-2 * π * k * z.im ^ 2 / τ.im) :=
  (rfl)

theorem thetaMetric_pos (z : ℂ) : 0 < thetaMetric k τ z :=
  Real.exp_pos _

theorem continuous_thetaMetric : Continuous (thetaMetric k τ) := by
  simp only [funext thetaMetric_def]
  fun_prop

/-- **The metric descends**: `h(z + λ) |e_λ(z)|² = h(z)` for every lattice vector
`λ = m + nτ`. -/
theorem thetaMetric_add_mul_norm_thetaFactor_sq (hτ : τ.im ≠ 0) (m n : ℤ) (z : ℂ) :
    thetaMetric k τ (z + m + n * τ) * ‖thetaFactor k τ α β m n z‖ ^ 2 = thetaMetric k τ z := by
  rw [thetaMetric_def, thetaMetric_def, norm_thetaFactor, sq (Real.exp _), ← Real.exp_add,
    ← Real.exp_add]
  congr 1
  simp only [add_im, intCast_im, mul_im, intCast_re]
  field_simp
  ring

/-- **The Hermitian pairing of two sections descends to the torus**: if `s` and `t` satisfy the
automorphy law at the lattice vector `λ = m + nτ`, then
`h(z + λ) s(z + λ) conj (t (z + λ)) = h(z) s(z) conj (t z)`. -/
theorem thetaMetric_add_mul_mul_conj (hτ : τ.im ≠ 0) {s t : ℂ → ℂ} {m n : ℤ} {z : ℂ}
    (hs : s (z + m + n * τ) = thetaFactor k τ α β m n z * s z)
    (ht : t (z + m + n * τ) = thetaFactor k τ α β m n z * t z) :
    (thetaMetric k τ (z + m + n * τ) : ℂ) * (s (z + m + n * τ) * conj (t (z + m + n * τ))) =
      thetaMetric k τ z * (s z * conj (t z)) := by
  rw [hs, ht, map_mul, ← thetaMetric_add_mul_norm_thetaFactor_sq (α := α) (β := β) hτ m n z,
    ofReal_mul, ofReal_pow, ← Complex.mul_conj']
  ring

/-- **The pointwise norm of a section descends to the torus**: if `s` satisfies the automorphy
law at the lattice vector `λ = m + nτ`, then `h(z + λ) |s(z + λ)|² = h(z) |s(z)|²`. -/
theorem thetaMetric_add_mul_norm_sq (hτ : τ.im ≠ 0) {s : ℂ → ℂ} {m n : ℤ} {z : ℂ}
    (hs : s (z + m + n * τ) = thetaFactor k τ α β m n z * s z) :
    thetaMetric k τ (z + m + n * τ) * ‖s (z + m + n * τ)‖ ^ 2 =
      thetaMetric k τ z * ‖s z‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simpa only [Complex.mul_conj'] using thetaMetric_add_mul_mul_conj hτ hs hs

/-- **Sections have bounded pointwise norm.** For `Im τ ≠ 0`, a continuous function satisfying
the two automorphy laws of the theta line has bounded pointwise norm `h(z) |s(z)|²`, since that
norm is a continuous function on the compact torus. -/
theorem exists_thetaMetric_mul_norm_sq_le (hτ : τ.im ≠ 0) {s : ℂ → ℂ} (hc : Continuous s)
    (h1 : ∀ z, s (z + 1) = cexp (2 * π * I * α) * s z)
    (h2 : ∀ z, s (z + τ) = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) * s z) :
    ∃ C, ∀ z, thetaMetric k τ z * ‖s z‖ ^ 2 ≤ C := by
  have hs := forall_add_eq_thetaFactor_mul_iff.mpr ⟨h1, h2⟩
  -- The lattice `ℤ + τℤ` is that of the point `σ = ±τ` of the upper half-plane.
  obtain ⟨σ, ε, hε, rfl⟩ : ∃ (σ : UpperHalfPlane) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧ τ = ε * σ := by
    rcases hτ.lt_or_gt with h | h
    · exact ⟨⟨-τ, by simpa using h⟩, -1, Or.inr rfl, by simp⟩
    · exact ⟨⟨τ, h⟩, 1, Or.inl rfl, by simp⟩
  have hper : ∀ z, ∀ w ∈ σ.periodPair.lattice, thetaMetric k (ε * σ) (z + w) * ‖s (z + w)‖ ^ 2 =
      thetaMetric k (ε * σ) z * ‖s z‖ ^ 2 := by
    intro z w hw
    obtain ⟨n, m, rfl⟩ := PeriodPair.mem_lattice.mp hw
    have hεε : (ε : ℂ) * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
    have := thetaMetric_add_mul_norm_sq hτ (hs m (ε * n) z)
    rwa [show z + m + ↑(ε * n) * (ε * σ) = z + (n * σ.periodPair.ω₁ + m * σ.periodPair.ω₂) by
      simp only [UpperHalfPlane.periodPair_ω₁, UpperHalfPlane.periodPair_ω₂]
      push_cast
      linear_combination (n * σ : ℂ) * hεε] at this
  obtain ⟨C, hC⟩ := (IsZLattice.isCompact_range_of_periodic σ.periodPair.lattice _
    (continuous_thetaMetric.mul (hc.norm.pow 2)) hper).isBounded.bddAbove
  exact ⟨C, fun z ↦ hC ⟨z, rfl⟩⟩

/-- The `dz`-coefficient `A(z) = 2πik Im z / Im τ` of the Chern connection form of the metric
`TauCeti.thetaMetric` on the theta line: on holomorphic sections the Chern connection is
`d + A dz`, with `A = ∂ log h` (`TauCeti.wirtingerDeriv_apply_one_log_thetaMetric`). -/
noncomputable def thetaConnectionForm (k : ℤ) (τ z : ℂ) : ℂ :=
  2 * π * I * k * z.im / τ.im

theorem thetaConnectionForm_def (z : ℂ) :
    thetaConnectionForm k τ z = 2 * π * I * k * z.im / τ.im :=
  (rfl)

/-- **The Chern connection form**: `∂ log h = A`, where `h` is the theta metric. -/
theorem wirtingerDeriv_apply_one_log_thetaMetric (z : ℂ) :
    wirtingerDeriv (fun w ↦ (Real.log (thetaMetric k τ w) : ℂ)) z 1 =
      thetaConnectionForm k τ z := by
  have hfun : (fun w ↦ (Real.log (thetaMetric k τ w) : ℂ)) =
      (-2 * π * k / τ.im : ℂ) • fun w : ℂ ↦ (w.im : ℂ) • (w.im : ℂ) := by
    funext w
    simp only [thetaMetric_def, Real.log_exp, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hd : DifferentiableAt ℝ (fun w : ℂ ↦ (w.im : ℂ)) z := by fun_prop
  rw [hfun, wirtingerDeriv_const_smul, smul_apply,
    wirtingerDeriv_smul_apply hd hd, wirtingerDeriv_apply_one_ofReal_im,
    thetaConnectionForm_def]
  simp only [smul_eq_mul]
  ring

/-- **The Chern connection descends to the theta line**: `A(z + λ) + e_λ'(z) / e_λ(z) = A(z)`
for every lattice vector `λ = m + nτ`, the transformation law of a connection form under the
transition function `e_λ`. -/
theorem thetaConnectionForm_add_add_logDeriv_thetaFactor (hτ : τ.im ≠ 0) (m n : ℤ) (z : ℂ) :
    thetaConnectionForm k τ (z + m + n * τ) + logDeriv (thetaFactor k τ α β m n) z =
      thetaConnectionForm k τ z := by
  rw [logDeriv_thetaFactor, thetaConnectionForm_def, thetaConnectionForm_def]
  simp only [add_im, intCast_im, mul_im, intCast_re, zero_mul, add_zero]
  have : (τ.im : ℂ) ≠ 0 := ofReal_ne_zero.mpr hτ
  field_simp
  push_cast
  ring

/-- **The curvature of the theta line**: `∂bar A = -πk / Im τ`. The curvature form is
`∂bar A d(conj z) ∧ dz`, which in the coordinates `z = q + τ p` is `-2πik dq ∧ dp`. -/
theorem conjWirtingerDeriv_apply_one_thetaConnectionForm (z : ℂ) :
    conjWirtingerDeriv (thetaConnectionForm k τ) z 1 = -(π * k / τ.im) := by
  have hfun : thetaConnectionForm k τ = (2 * π * I * k / τ.im : ℂ) • fun w : ℂ ↦ (w.im : ℂ) := by
    funext w
    simp only [thetaConnectionForm_def, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun, conjWirtingerDeriv_const_smul, smul_apply,
    conjWirtingerDeriv_apply_one_ofReal_im, smul_eq_mul]
  linear_combination (π * k / τ.im : ℂ) * I_sq

end TauCeti
