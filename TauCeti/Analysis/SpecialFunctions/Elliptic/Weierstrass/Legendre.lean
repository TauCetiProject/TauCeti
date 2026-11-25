/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Defs
public import TauCeti.Analysis.Complex.UpperHalfPlane.PeriodPair
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Cotangent

/-!
# The Legendre relation for the quasi-periods of `ζ`

For a pair of periods `(ω₁, ω₂)` with lattice `Λ`, the quasi-periods `η(l) = ζ(z + l) - ζ(z)` of
the Weierstrass `ζ` function satisfy **Legendre's relation**

  `η(ω₁) ω₂ - η(ω₂) ω₁ = 2π i`  when `Im(ω₂ / ω₁) > 0`,

and `-2π i` for the opposite orientation (`PeriodPair.quasiPeriod_legendre`,
`PeriodPair.quasiPeriod_legendre_of_im_neg`). It is the input that turns the quasi-periodicity of
the Weierstrass `σ` function into the explicit value `e^(-2π i / N)` of the Weil pairing on the
`N`-torsion of `ℂ / Λ`.

For the lattice `ℤ z + ℤ` of a point `z` of the upper half-plane, the quasi-period of `1` is the
Eisenstein series `G₂(z) = ∑_m ∑_n (m z + n)⁻²` (`UpperHalfPlane.quasiPeriod_ω₂_periodPair`): in
the expansion of `ζ(x; ℤ z + ℤ)` along the rows of the lattice,
`ζ(x) = ∑_m (π cot (π (x - m z)) + π cot (π m z) + x ∑_n (m z + n)⁻²)`, translating `x` by `1`
leaves the `π`-periodic cotangents unchanged. Under `z ↦ -1 / z` the lattice is rescaled by
`z⁻¹` and the quasi-periods by `z`, which carries the quasi-modularity
`G₂(-1 / z) = z² G₂(z) - 2π i z` of Mathlib's `EisensteinSeries.G2_S_transform` to the relation
`η(z) = z η(1) - 2π i` (`UpperHalfPlane.quasiPeriod_ω₁_periodPair`). Every lattice is a rescaling
of some `ℤ τ + ℤ`, and rescaling multiplies `ω₁`, `ω₂` by `c` and `η` by `c⁻¹`, which gives the
general relation.

## Main results

* `UpperHalfPlane.hasSum_quasiPeriod_ω₂_periodPair`: `η(1; ℤ z + ℤ) = ∑_m ∑_n (m z + n)⁻²`,
  absolutely convergent in `m`.
* `UpperHalfPlane.quasiPeriod_ω₂_periodPair`: `η(1; ℤ z + ℤ) = G₂(z)`.
* `UpperHalfPlane.quasiPeriod_ω₁_periodPair`: `η(z; ℤ z + ℤ) = z η(1; ℤ z + ℤ) - 2π i`.
* `PeriodPair.quasiPeriod_legendre`: `η(ω₁) ω₂ - η(ω₂) ω₁ = 2π i` when `Im(ω₂ / ω₁) > 0`.
* `PeriodPair.quasiPeriod_legendre_of_im_neg`: `η(ω₁) ω₂ - η(ω₂) ω₁ = -2π i` when
  `Im(ω₂ / ω₁) < 0`.

## References

* *NIST Digital Library of Mathematical Functions*, §23.2, (23.2.14); its generators are the
  half-periods, so its `η` is half of the quasi-period here.
* N. Koblitz, *Introduction to elliptic curves and modular forms*, §III.2, which identifies
  `η(1)` with `G₂` and derives the relation from the quasi-modularity of `G₂`, as here.
-/

public section

noncomputable section

open Complex PeriodPair
open scoped Real UpperHalfPlane

namespace UpperHalfPlane

open TauCeti.UpperHalfPlane

variable (z : ℍ)

/-- **The quasi-period of `1` in `ℤ z + ℤ` as a sum over rows**:
`η(1; ℤ z + ℤ) = ∑_m ∑_n (m z + n)⁻²`, the outer sum over `m ∈ ℤ` converging absolutely. -/
theorem hasSum_quasiPeriod_ω₂_periodPair :
    HasSum (fun m : ℤ ↦ rowSum (m * z))
      (z.periodPair.quasiPeriod ⟨_, z.periodPair.ω₂_mem_lattice⟩) := by
  have hx := z.periodPair.ω₁_div_two_notMem_lattice
  have hx₁ : z.periodPair.ω₁ / 2 + z.periodPair.ω₂ ∉ z.periodPair.lattice := fun h ↦
    hx (by simpa using sub_mem h z.periodPair.ω₂_mem_lattice)
  have h := (hasSum_weierstrassZeta_periodPair_rows z hx₁).sub
    (hasSum_weierstrassZeta_periodPair_rows z hx)
  rw [weierstrassZeta_add_coe z.periodPair _ ⟨_, z.periodPair.ω₂_mem_lattice⟩,
    add_sub_cancel_left] at h
  refine h.congr_fun fun m ↦ ?_
  rw [periodPair_ω₂, show (π : ℂ) * (z.periodPair.ω₁ / 2 + 1 - m * z) =
    π * (z.periodPair.ω₁ / 2 - m * z) + π by ring, cot_add_pi]
  ring

/-- **The quasi-period of `1` in `ℤ z + ℤ` is the Eisenstein series `G₂(z)`** of Mathlib's
`EisensteinSeries.G2`. -/
theorem quasiPeriod_ω₂_periodPair :
    z.periodPair.quasiPeriod ⟨_, z.periodPair.ω₂_mem_lattice⟩ = EisensteinSeries.G2 z := by
  have h : HasSum (EisensteinSeries.e2Summand · z)
      (z.periodPair.quasiPeriod ⟨_, z.periodPair.ω₂_mem_lattice⟩) :=
    (hasSum_quasiPeriod_ω₂_periodPair z).congr_fun fun m ↦ by
      simp [EisensteinSeries.e2Summand, EisensteinSeries.eisSummand, rowSum_def, one_div]
  rw [EisensteinSeries.G2, tsum_eq_of_summable_unconditional h.summable, h.tsum_eq]

/-- **The Legendre relation for `ℤ z + ℤ`**: `η(z; ℤ z + ℤ) = z η(1; ℤ z + ℤ) - 2π i`. -/
theorem quasiPeriod_ω₁_periodPair :
    z.periodPair.quasiPeriod ⟨_, z.periodPair.ω₁_mem_lattice⟩ =
      z * z.periodPair.quasiPeriod ⟨_, z.periodPair.ω₂_mem_lattice⟩ - 2 * π * Complex.I := by
  have hz : (z : ℂ) ≠ 0 := ne_zero z
  -- `z ↦ -1 / z` carries `ℤ z + ℤ` to `z⁻¹ (ℤ z + ℤ)`, sending the period `z` to `1`
  have h := quasiPeriod_periodPair_smul ModularGroup.S z ⟨_, z.periodPair.ω₁_mem_lattice⟩
  have e : (⟨z.periodPair.ω₁ / denom ModularGroup.S z,
      (div_denom_mem_lattice_periodPair_smul_iff _ z _).mpr z.periodPair.ω₁_mem_lattice⟩ :
        (ModularGroup.S • z).periodPair.lattice) =
      ⟨_, (ModularGroup.S • z).periodPair.ω₂_mem_lattice⟩ :=
    Subtype.ext (by simp [hz])
  rw [e, quasiPeriod_ω₂_periodPair, ModularGroup.denom_S] at h
  have hG := EisensteinSeries.G2_S_transform z
  rw [quasiPeriod_ω₂_periodPair]
  apply mul_left_cancel₀ hz
  field_simp at hG
  linear_combination -h - hG

end UpperHalfPlane

namespace PeriodPair

/-- The Legendre determinant `η(ω₁) ω₂ - η(ω₂) ω₁` is unchanged by rescaling the periods. -/
private theorem quasiPeriod_legendre_smul (L : PeriodPair) (c : ℂˣ) :
    (c • L).quasiPeriod ⟨_, (c • L).ω₁_mem_lattice⟩ * (c • L).ω₂ -
        (c • L).quasiPeriod ⟨_, (c • L).ω₂_mem_lattice⟩ * (c • L).ω₁ =
      L.quasiPeriod ⟨_, L.ω₁_mem_lattice⟩ * L.ω₂ - L.quasiPeriod ⟨_, L.ω₂_mem_lattice⟩ * L.ω₁ := by
  have h₁ : (⟨_, (c • L).ω₁_mem_lattice⟩ : (c • L).lattice) =
      L.latticeSMulEquiv c ⟨_, L.ω₁_mem_lattice⟩ := Subtype.ext (by simp)
  have h₂ : (⟨_, (c • L).ω₂_mem_lattice⟩ : (c • L).lattice) =
      L.latticeSMulEquiv c ⟨_, L.ω₂_mem_lattice⟩ := Subtype.ext (by simp)
  rw [h₁, h₂, quasiPeriod_smul, quasiPeriod_smul, smul_ω₁, smul_ω₂]
  field_simp

/-- **Legendre's relation**, negative orientation: if `Im(ω₂ / ω₁) < 0`, then
`η(ω₁) ω₂ - η(ω₂) ω₁ = -2π i`. -/
theorem quasiPeriod_legendre_of_im_neg (L : PeriodPair) (h : (L.ω₂ / L.ω₁).im < 0) :
    L.quasiPeriod ⟨_, L.ω₁_mem_lattice⟩ * L.ω₂ - L.quasiPeriod ⟨_, L.ω₂_mem_lattice⟩ * L.ω₁ =
      -(2 * π * I) := by
  have h' : 0 < (L.ω₁ / L.ω₂).im := by
    rw [← inv_div, inv_im]
    exact div_pos (neg_pos.mpr h) (normSq_pos.mpr (div_ne_zero L.ω₂_ne_zero L.ω₁_ne_zero))
  have hL : L = Units.mk0 L.ω₂ L.ω₂_ne_zero • (⟨_, h'⟩ : ℍ).periodPair := by
    ext
    · simp [mul_div_cancel₀ _ L.ω₂_ne_zero]
    · simp
  rw [hL, quasiPeriod_legendre_smul, UpperHalfPlane.quasiPeriod_ω₁_periodPair]
  simp only [UpperHalfPlane.periodPair_ω₁, UpperHalfPlane.periodPair_ω₂]
  ring

/-- **Legendre's relation**: if `Im(ω₂ / ω₁) > 0`, then `η(ω₁) ω₂ - η(ω₂) ω₁ = 2π i`. -/
theorem quasiPeriod_legendre (L : PeriodPair) (h : 0 < (L.ω₂ / L.ω₁).im) :
    L.quasiPeriod ⟨_, L.ω₁_mem_lattice⟩ * L.ω₂ - L.quasiPeriod ⟨_, L.ω₂_mem_lattice⟩ * L.ω₁ =
      2 * π * I := by
  -- `L' = (ω₂, ω₁)` has the same lattice as `L` and the opposite orientation
  set L' := Units.mk0 L.ω₁ L.ω₁_ne_zero • (⟨_, h⟩ : ℍ).periodPair
  have hω₁ : L'.ω₁ = L.ω₂ := by simp [L', mul_div_cancel₀ _ L.ω₁_ne_zero]
  have hω₂ : L'.ω₂ = L.ω₁ := by simp [L']
  have hlat : L.lattice = L'.lattice := by
    simp only [lattice, hω₁, hω₂, Set.pair_comm]
  have h' : (L'.ω₂ / L'.ω₁).im < 0 := by
    rw [hω₁, hω₂, ← inv_div, inv_im]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos h)
      (normSq_pos.mpr (div_ne_zero L.ω₂_ne_zero L.ω₁_ne_zero))
  have key := L'.quasiPeriod_legendre_of_im_neg h'
  rw [quasiPeriod_eq_of_lattice_eq hlat ⟨_, L.ω₁_mem_lattice⟩,
    quasiPeriod_eq_of_lattice_eq hlat ⟨_, L.ω₂_mem_lattice⟩]
  have e₁ : (⟨L.ω₁, hlat ▸ L.ω₁_mem_lattice⟩ : L'.lattice) = ⟨_, L'.ω₂_mem_lattice⟩ :=
    Subtype.ext hω₂.symm
  have e₂ : (⟨L.ω₂, hlat ▸ L.ω₂_mem_lattice⟩ : L'.lattice) = ⟨_, L'.ω₁_mem_lattice⟩ :=
    Subtype.ext hω₁.symm
  rw [e₁, e₂, ← hω₁, ← hω₂]
  linear_combination -key

end PeriodPair
