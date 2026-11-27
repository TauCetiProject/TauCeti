/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.AdditionTheorem
public import TauCeti.Analysis.SpecialFunctions.Elliptic.Weierstrass.Sigma
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Addition and duplication formulas for the Weierstrass `ζ` and `σ` functions

For a pair of periods `L` with lattice `Λ`, this file proves the classical addition theorems of the
Weierstrass `ζ` and `σ` functions: for `u, v ∉ Λ`,

  `ζ(u + v) + ζ(u - v) = 2 ζ(u) + ℘'(u) / (℘(u) - ℘(v))` (when `℘(u) ≠ ℘(v)`),
  `ζ(u + v) = ζ(u) + ζ(v) + (℘'(u) - ℘'(v)) / (2 (℘(u) - ℘(v)))` (when `℘(u) ≠ ℘(v)`),
  `σ(u + v) σ(u - v) = (℘(v) - ℘(u)) σ(u)² σ(v)²`,

and the duplication formula `σ(2 z) = -℘'(z) σ(z)⁴`.

The addition formula for `σ` expresses `℘(v) - ℘(u)` through the zeros of `σ`; the duplication
formula is its limit as `v → u`. They are the identities from which the addition and duplication
formulas of the theta functions of a lattice, built from `σ` by a Gaussian factor and a translation,
are derived.

## Main results

* `PeriodPair.weierstrassZeta_add_add_weierstrassZeta_sub`:
  `ζ(u + v) + ζ(u - v) = 2 ζ(u) + ℘'(u) / (℘(u) - ℘(v))`.
* `PeriodPair.weierstrassZeta_add`: the addition theorem for `ζ`.
* `PeriodPair.weierstrassSigma_add_mul_weierstrassSigma_sub`: the addition formula for `σ`.
* `PeriodPair.weierstrassSigma_two_mul`: the duplication formula for `σ`.

## Implementation notes

As for the addition theorem of `℘` (`PeriodPair.weierstrassP_add`), the proofs use differentiation
and connectedness rather than Liouville's theorem. For fixed `v ∉ Λ`, the set of `u` with
`u, u + v, u - v ∉ Λ` is the complement of a countable set, hence open and connected. On it the
function `ζ(u + v) + ζ(u - v) - 2 ζ(u) - ℘'(u) / (℘(u) - ℘(v))` has derivative zero, by the addition
theorem of `℘` applied to `℘(u + v)` and `℘(u - v)` and by `℘'' = 6 ℘² - g₂ / 2`. It is therefore
constant, and being odd in `u` it vanishes. This identity says that `σ(u + v) σ(u - v)` and
`(℘(v) - ℘(u)) σ(u)² σ(v)²` have the same logarithmic derivative in `u`, as `σ' / σ = ζ`; so they
are proportional, and comparing them as `u → 0`, where both tend to `-σ(v)²`, shows that the
constant is `1`.

## References

* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, 4th ed., Cambridge University
  Press, 1927, §§20.41, 20.53.
* *NIST Digital Library of Mathematical Functions*, §23.10.
-/

public section

noncomputable section

open Complex Filter
open scoped Topology PeriodPair

namespace PeriodPair

variable (L : PeriodPair) {u v : ℂ}

/-- For `v ∈ ℂ`, the points `u` with `u, u + v, u - v ∉ Λ` form an open connected set: the
complement of three translates of the countable closed set `Λ`. -/
private lemma isOpen_isPreconnected_addition (v : ℂ) :
    IsOpen {u : ℂ | u ∉ L.lattice ∧ u + v ∉ L.lattice ∧ u - v ∉ L.lattice} ∧
      IsPreconnected {u : ℂ | u ∉ L.lattice ∧ u + v ∉ L.lattice ∧ u - v ∉ L.lattice} := by
  have heq : {u : ℂ | u ∉ L.lattice ∧ u + v ∉ L.lattice ∧ u - v ∉ L.lattice} =
      ((L.lattice : Set ℂ) ∪ (· + v) ⁻¹' L.lattice ∪ (· - v) ⁻¹' L.lattice)ᶜ := by
    ext u
    simp [and_assoc]
  rw [heq]
  exact ⟨((L.isClosed_lattice.union (L.isClosed_lattice.preimage (by fun_prop))).union
      (L.isClosed_lattice.preimage (by fun_prop))).isOpen_compl,
    (((L.countable_lattice.union (L.countable_lattice.preimage (add_left_injective v))).union
      (L.countable_lattice.preimage sub_left_injective)).isConnected_compl_of_one_lt_rank
        (by simp)).isPreconnected⟩

/-- Away from the lattice, `℘(u) ≠ ℘(v)` exactly when `u + v ∉ Λ` and `u - v ∉ Λ`. -/
private lemma weierstrassP_ne_iff (hu : u ∉ L.lattice) (hv : v ∉ L.lattice) :
    ℘[L] u ≠ ℘[L] v ↔ u + v ∉ L.lattice ∧ u - v ∉ L.lattice := by
  rw [Ne, L.weierstrassP_eq_weierstrassP_iff hu hv]
  tauto

/-- Along `u`, the function `ζ(u + v) + ζ(u - v) - 2 ζ(u) - ℘'(u) / (℘(u) - ℘(v))` has derivative
zero. -/
private lemma hasDerivAt_weierstrassZeta_addition (hu : u ∉ L.lattice) (hv : v ∉ L.lattice)
    (h : ℘[L] u ≠ ℘[L] v) :
    HasDerivAt (fun w ↦ L.weierstrassZeta (w + v) + L.weierstrassZeta (w - v) -
      2 * L.weierstrassZeta w - ℘'[L] w / (℘[L] w - ℘[L] v)) 0 u := by
  obtain ⟨hp, hm⟩ := (L.weierstrassP_ne_iff hu hv).mp h
  have hv' : -v ∉ L.lattice := by rwa [neg_mem_iff]
  have hne : ℘[L] u - ℘[L] v ≠ 0 := sub_ne_zero.mpr h
  have hadd := L.weierstrassP_add hu hv h
  have hsub := L.weierstrassP_add hu hv' (by rwa [weierstrassP_neg])
  rw [weierstrassP_neg, derivWeierstrassP_neg, ← sub_eq_add_neg] at hsub
  convert (((L.hasDerivAt_weierstrassZeta hp).comp_add_const u v).add
    ((L.hasDerivAt_weierstrassZeta hm).comp_sub_const u v) |>.sub
    ((L.hasDerivAt_weierstrassZeta hu).const_mul 2)).sub
    ((L.hasDerivAt_derivWeierstrassP hu).div
      ((L.hasDerivAt_weierstrassP hu).sub_const (℘[L] v)) hne) using 1
  rw [hadd, hsub]
  field_simp
  linear_combination -4 * (L.derivWeierstrassP_sq u hu - L.derivWeierstrassP_sq v hv)

/-- **A two-point identity for `ζ`.** If `v ∉ Λ` and `℘(u) ≠ ℘(v)`, then
`ζ(u + v) + ζ(u - v) = 2 ζ(u) + ℘'(u) / (℘(u) - ℘(v))`. For `u ∈ Λ` this holds with the values
`ζ(u) = η(u)` and `℘'(u) = 0` that `ζ` and `℘'` take at their poles. -/
theorem weierstrassZeta_add_add_weierstrassZeta_sub (hv : v ∉ L.lattice) (h : ℘[L] u ≠ ℘[L] v) :
    L.weierstrassZeta (u + v) + L.weierstrassZeta (u - v) =
      2 * L.weierstrassZeta u + ℘'[L] u / (℘[L] u - ℘[L] v) := by
  by_cases hu : u ∈ L.lattice
  · -- Both sides are `2 η(u)`, by the quasi-periodicity of `ζ`.
    have h₀ : ℘'[L] u = 0 := L.derivWeierstrassP_coe ⟨u, hu⟩
    have h₁ : L.weierstrassZeta (u + v) = L.weierstrassZeta v + L.quasiPeriod ⟨u, hu⟩ := by
      simpa [add_comm] using L.weierstrassZeta_add_coe v ⟨u, hu⟩
    have h₂ : L.weierstrassZeta (u - v) = L.weierstrassZeta (-v) + L.quasiPeriod ⟨u, hu⟩ := by
      simpa [neg_add_eq_sub] using L.weierstrassZeta_add_coe (-v) ⟨u, hu⟩
    rw [h₀, h₁, h₂, L.weierstrassZeta_neg, show L.weierstrassZeta u = L.quasiPeriod ⟨u, hu⟩ from
      L.weierstrassZeta_coe ⟨u, hu⟩]
    ring
  set S := {w : ℂ | w ∉ L.lattice ∧ w + v ∉ L.lattice ∧ w - v ∉ L.lattice}
  set ψ : ℂ → ℂ := fun w ↦ L.weierstrassZeta (w + v) + L.weierstrassZeta (w - v) -
    2 * L.weierstrassZeta w - ℘'[L] w / (℘[L] w - ℘[L] v)
  obtain ⟨hSo, hSc⟩ := L.isOpen_isPreconnected_addition v
  have hψ : ∀ w ∈ S, HasDerivAt ψ 0 w := fun w hw ↦
    L.hasDerivAt_weierstrassZeta_addition hw.1 hv ((L.weierstrassP_ne_iff hw.1 hv).mpr hw.2)
  obtain ⟨hp, hm⟩ := (L.weierstrassP_ne_iff hu hv).mp h
  have hu' : u ∈ S := ⟨hu, hp, hm⟩
  have hnu : -u ∈ S := by
    refine ⟨by rwa [neg_mem_iff], ?_, ?_⟩
    · rwa [show -u + v = -(u - v) by ring, neg_mem_iff]
    · rwa [show -u - v = -(u + v) by ring, neg_mem_iff]
  -- `ψ` is constant on the connected set `S`, and odd, so it vanishes.
  have hconst : ψ (-u) = ψ u := hSo.is_const_of_deriv_eq_zero hSc
    (fun w hw ↦ (hψ w hw).differentiableAt.differentiableWithinAt) (fun w hw ↦ (hψ w hw).deriv)
    hnu hu'
  have hodd : ψ (-u) = -ψ u := by
    simp only [ψ, show -u + v = -(u - v) by ring, show -u - v = -(u + v) by ring,
      weierstrassZeta_neg, weierstrassP_neg, derivWeierstrassP_neg]
    ring
  have h0 : ψ u = 0 := by linear_combination (hodd - hconst) / 2
  simp only [ψ] at h0
  linear_combination h0

/-- **The addition theorem for `ζ`.** If `u, v ∉ Λ` and `℘(u) ≠ ℘(v)`, then
`ζ(u + v) = ζ(u) + ζ(v) + (℘'(u) - ℘'(v)) / (2 (℘(u) - ℘(v)))`. -/
theorem weierstrassZeta_add (hu : u ∉ L.lattice) (hv : v ∉ L.lattice) (h : ℘[L] u ≠ ℘[L] v) :
    L.weierstrassZeta (u + v) = L.weierstrassZeta u + L.weierstrassZeta v +
      (℘'[L] u - ℘'[L] v) / (2 * (℘[L] u - ℘[L] v)) := by
  have h₁ := L.weierstrassZeta_add_add_weierstrassZeta_sub hv h
  have h₂ := L.weierstrassZeta_add_add_weierstrassZeta_sub hu (Ne.symm h)
  rw [add_comm v u, show v - u = -(u - v) by ring, weierstrassZeta_neg] at h₂
  have hne : ℘[L] u - ℘[L] v ≠ 0 := sub_ne_zero.mpr h
  have hne' : ℘[L] v - ℘[L] u ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  field_simp at h₁ h₂ ⊢
  linear_combination h₁ - h₂

/-- For fixed `v ∉ Λ`, the functions `σ(w + v) σ(w - v)` and `(℘(v) - ℘(w)) σ(w)² σ(v)²` of `w` are
proportional on the connected set of `w` with `w, w ± v ∉ Λ`: by `σ' = ζ σ` and the two-point
identity for `ζ`, both have logarithmic derivative `ζ(w + v) + ζ(w - v)`. -/
private lemma exists_weierstrassSigma_add_mul_weierstrassSigma_sub_eq (hv : v ∉ L.lattice) :
    ∃ c : ℂ, ∀ w ∉ L.lattice, w + v ∉ L.lattice → w - v ∉ L.lattice →
      L.weierstrassSigma (w + v) * L.weierstrassSigma (w - v) =
        c * ((℘[L] v - ℘[L] w) * L.weierstrassSigma w ^ 2 * L.weierstrassSigma v ^ 2) := by
  set S := {w : ℂ | w ∉ L.lattice ∧ w + v ∉ L.lattice ∧ w - v ∉ L.lattice}
  set f : ℂ → ℂ := fun w ↦ L.weierstrassSigma (w + v) * L.weierstrassSigma (w - v)
  set g : ℂ → ℂ := fun w ↦ (℘[L] v - ℘[L] w) * L.weierstrassSigma w ^ 2 * L.weierstrassSigma v ^ 2
  obtain ⟨hSo, hSc⟩ := L.isOpen_isPreconnected_addition v
  have hne : ∀ w ∈ S, ℘[L] w ≠ ℘[L] v := fun w hw ↦ (L.weierstrassP_ne_iff hw.1 hv).mpr hw.2
  have hf : ∀ w ∈ S, HasDerivAt f
      ((L.weierstrassZeta (w + v) + L.weierstrassZeta (w - v)) * f w) w := fun w hw ↦ by
    convert ((L.hasDerivAt_weierstrassSigma hw.2.1).comp_add_const w v).mul
      ((L.hasDerivAt_weierstrassSigma hw.2.2).comp_sub_const w v) using 1
    ring
  have hg : ∀ w ∈ S, HasDerivAt g
      ((℘'[L] w / (℘[L] w - ℘[L] v) + 2 * L.weierstrassZeta w) * g w) w := fun w hw ↦ by
    convert (((L.hasDerivAt_weierstrassP hw.1).const_sub (℘[L] v)).mul
      ((L.hasDerivAt_weierstrassSigma hw.1).pow 2)).mul_const (L.weierstrassSigma v ^ 2) using 1
    have h℘ := sub_ne_zero.mpr (hne w hw)
    simp only [g, Pi.pow_apply, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    field_simp
    ring
  have hfS : ∀ w ∈ S, f w ≠ 0 := fun w hw ↦
    mul_ne_zero (L.weierstrassSigma_ne_zero hw.2.1) (L.weierstrassSigma_ne_zero hw.2.2)
  have hgS : ∀ w ∈ S, g w ≠ 0 := fun w hw ↦ mul_ne_zero (mul_ne_zero
    (sub_ne_zero.mpr (hne w hw).symm) (pow_ne_zero _ (L.weierstrassSigma_ne_zero hw.1)))
    (pow_ne_zero _ (L.weierstrassSigma_ne_zero hv))
  obtain ⟨c, -, hc⟩ := (logDeriv_eqOn_iff
    (fun w hw ↦ (hf w hw).differentiableAt.differentiableWithinAt)
    (fun w hw ↦ (hg w hw).differentiableAt.differentiableWithinAt) hSo hSc hgS hfS).mp
    fun w hw ↦ by
      rw [logDeriv_apply, logDeriv_apply, (hf w hw).deriv, (hg w hw).deriv,
        mul_div_cancel_right₀ _ (hfS w hw), mul_div_cancel_right₀ _ (hgS w hw),
        L.weierstrassZeta_add_add_weierstrassZeta_sub hv (hne w hw), add_comm]
  exact ⟨c, fun w h₁ h₂ h₃ ↦ hc (show w ∈ S from ⟨h₁, h₂, h₃⟩)⟩

/-- As `w → 0`, `(℘(v) - ℘(w)) σ(w)² σ(v)² → -σ(v)²`, since `℘(w) ~ 1 / w²` and `σ(w) ~ w`. -/
private lemma tendsto_weierstrassP_sub_mul_weierstrassSigma_sq (v : ℂ) :
    Tendsto (fun w ↦ (℘[L] v - ℘[L] w) * L.weierstrassSigma w ^ 2 * L.weierstrassSigma v ^ 2)
      (𝓝[≠] 0) (𝓝 (-L.weierstrassSigma v ^ 2)) := by
  -- For `w ≠ 0`, the function is `(w² ℘(v) - w² ℘₀(w) - 1) (σ(w) / w)² σ(v)²`, where
  -- `℘₀ = ℘ - 1 / w²` is continuous at `0`.
  have hP := (L.analyticAt_weierstrassPExcept 0).continuousAt
  have hlim : Tendsto (fun w ↦ (w ^ 2 * ℘[L] v - w ^ 2 * L.weierstrassPExcept 0 w - 1) *
      slope L.weierstrassSigma 0 w ^ 2 * L.weierstrassSigma v ^ 2) (𝓝[≠] 0) (𝓝 ((0 ^ 2 * ℘[L] v -
        0 ^ 2 * L.weierstrassPExcept 0 0 - 1) * 1 ^ 2 * L.weierstrassSigma v ^ 2)) := by
    refine (((Tendsto.sub (Tendsto.sub ?_ ?_) tendsto_const_nhds).mul
      ((hasDerivAt_iff_tendsto_slope.mp L.hasDerivAt_weierstrassSigma_zero).pow 2)).mul
        tendsto_const_nhds)
    · exact ((continuous_pow 2).tendsto 0).mono_left nhdsWithin_le_nhds |>.mul_const _
    · exact (((continuous_pow 2).continuousAt.mul hP).tendsto).mono_left nhdsWithin_le_nhds
  rw [show ((0 : ℂ) ^ 2 * ℘[L] v - 0 ^ 2 * L.weierstrassPExcept 0 0 - 1) * 1 ^ 2 *
    L.weierstrassSigma v ^ 2 = -L.weierstrassSigma v ^ 2 by ring] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w (hw : w ≠ 0)
  rw [← L.weierstrassPExcept_add ⟨0, zero_mem _⟩ w, slope_def_field]
  simp only [sub_zero, weierstrassSigma_zero]
  field_simp
  ring

/-- The addition formula for `σ` when `℘(u) ≠ ℘(v)`: the constant of proportionality of
`PeriodPair.exists_weierstrassSigma_add_mul_weierstrassSigma_sub_eq` is `1`, as both sides tend to
`-σ(v)²` when `u → 0`. -/
private lemma weierstrassSigma_add_mul_weierstrassSigma_sub_of_ne (hu : u ∉ L.lattice)
    (hv : v ∉ L.lattice) (h : ℘[L] u ≠ ℘[L] v) :
    L.weierstrassSigma (u + v) * L.weierstrassSigma (u - v) =
      (℘[L] v - ℘[L] u) * L.weierstrassSigma u ^ 2 * L.weierstrassSigma v ^ 2 := by
  obtain ⟨c, hc⟩ := L.exists_weierstrassSigma_add_mul_weierstrassSigma_sub_eq hv
  have hσ : Continuous L.weierstrassSigma := L.differentiable_weierstrassSigma.continuous
  -- Near `0`, the points `w ≠ 0` satisfy `w, w ± v ∉ Λ`.
  have hS : ∀ᶠ w in 𝓝[≠] (0 : ℂ), w ∉ L.lattice ∧ w + v ∉ L.lattice ∧ w - v ∉ L.lattice := by
    have hopen := L.isClosed_lattice.isOpen_compl
    filter_upwards [L.eventually_notMem_lattice 0,
      nhdsWithin_le_nhds ((continuous_id.add continuous_const).continuousAt.preimage_mem_nhds
        (hopen.mem_nhds (by simpa using hv))),
      nhdsWithin_le_nhds ((continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
        (hopen.mem_nhds (by simpa using hv)))] with w h₁ h₂ h₃
    exact ⟨h₁, h₂, h₃⟩
  have hf0 : Tendsto (fun w ↦ L.weierstrassSigma (w + v) * L.weierstrassSigma (w - v)) (𝓝[≠] 0)
      (𝓝 (-L.weierstrassSigma v ^ 2)) := by
    have : Continuous fun w ↦ L.weierstrassSigma (w + v) * L.weierstrassSigma (w - v) := by
      fun_prop
    convert (this.tendsto 0).mono_left nhdsWithin_le_nhds using 2
    simp [sq]
  have hc1 : c = 1 := by
    have hlim := tendsto_nhds_unique
      (hf0.congr' (hS.mono fun w hw ↦ hc w hw.1 hw.2.1 hw.2.2))
      ((L.tendsto_weierstrassP_sub_mul_weierstrassSigma_sq v).const_mul c)
    have h' : (c - 1) * L.weierstrassSigma v ^ 2 = 0 := by linear_combination hlim
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right
      (pow_ne_zero _ (L.weierstrassSigma_ne_zero hv)))
  obtain ⟨hp, hm⟩ := (L.weierstrassP_ne_iff hu hv).mp h
  simpa [hc1] using hc u hu hp hm

/-- **The addition formula for `σ`.** For `u, v ∉ Λ`,
`σ(u + v) σ(u - v) = (℘(v) - ℘(u)) σ(u)² σ(v)²`. -/
theorem weierstrassSigma_add_mul_weierstrassSigma_sub (hu : u ∉ L.lattice) (hv : v ∉ L.lattice) :
    L.weierstrassSigma (u + v) * L.weierstrassSigma (u - v) =
      (℘[L] v - ℘[L] u) * L.weierstrassSigma u ^ 2 * L.weierstrassSigma v ^ 2 := by
  by_cases h : ℘[L] u = ℘[L] v
  · -- Then `u + v ∈ Λ` or `u - v ∈ Λ`, and both sides vanish.
    rw [h, sub_self, zero_mul, zero_mul]
    rcases (L.weierstrassP_eq_weierstrassP_iff hu hv).mp h with h | h
    · rw [L.weierstrassSigma_eq_zero_iff.mpr h, mul_zero]
    · rw [L.weierstrassSigma_eq_zero_iff.mpr h, zero_mul]
  · exact L.weierstrassSigma_add_mul_weierstrassSigma_sub_of_ne hu hv h

/-- **The duplication formula for `σ`.** `σ(2 z) = -℘'(z) σ(z)⁴`; for `z ∈ Λ` both sides
vanish. -/
theorem weierstrassSigma_two_mul (z : ℂ) :
    L.weierstrassSigma (2 * z) = -℘'[L] z * L.weierstrassSigma z ^ 4 := by
  by_cases hz : z ∈ L.lattice
  · have h2z : 2 * z ∈ L.lattice := by simpa [two_mul] using add_mem hz hz
    rw [L.weierstrassSigma_eq_zero_iff.mpr hz, L.weierstrassSigma_eq_zero_iff.mpr h2z]
    ring
  -- Divide the addition formula at `(z, z - h)` by `h` and let `h → 0`.
  have hz0 : z - 0 ∉ L.lattice := by simpa using hz
  have hσ : Continuous L.weierstrassSigma := L.differentiable_weierstrassSigma.continuous
  have h₁ : Tendsto (fun h ↦ L.weierstrassSigma (2 * z - h) * slope L.weierstrassSigma 0 h)
      (𝓝[≠] 0) (𝓝 (L.weierstrassSigma (2 * z) * 1)) := by
    refine Tendsto.mul ?_ (hasDerivAt_iff_tendsto_slope.mp L.hasDerivAt_weierstrassSigma_zero)
    have : Continuous fun h ↦ L.weierstrassSigma (2 * z - h) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have h₂ : Tendsto (fun h ↦ slope (fun h ↦ ℘[L] (z - h)) 0 h * L.weierstrassSigma z ^ 2 *
      L.weierstrassSigma (z - h) ^ 2) (𝓝[≠] 0)
      (𝓝 (-℘'[L] z * L.weierstrassSigma z ^ 2 * L.weierstrassSigma z ^ 2)) := by
    refine Tendsto.mul (Tendsto.mul_const _ ?_) ?_
    · simpa using
        hasDerivAt_iff_tendsto_slope.mp ((L.hasDerivAt_weierstrassP hz0).comp_const_sub z 0)
    · have : Continuous fun h ↦ L.weierstrassSigma (z - h) ^ 2 := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have heq : (fun h ↦ L.weierstrassSigma (2 * z - h) * slope L.weierstrassSigma 0 h) =ᶠ[𝓝[≠] 0]
      fun h ↦ slope (fun h ↦ ℘[L] (z - h)) 0 h * L.weierstrassSigma z ^ 2 *
        L.weierstrassSigma (z - h) ^ 2 := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds ((continuous_sub_left z).continuousAt
      |>.preimage_mem_nhds (L.isClosed_lattice.isOpen_compl.mem_nhds hz0))] with h (hh : h ≠ 0) hzh
    have := L.weierstrassSigma_add_mul_weierstrassSigma_sub hz hzh
    rw [show z + (z - h) = 2 * z - h by ring, show z - (z - h) = h by ring] at this
    simp only [slope_def_field, sub_zero, weierstrassSigma_zero]
    field_simp
    linear_combination this
  have := tendsto_nhds_unique (h₁.congr' heq) h₂
  linear_combination this

end PeriodPair
