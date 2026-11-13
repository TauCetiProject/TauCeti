/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RealPeriod
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.RealPeriod
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Separability

/-!
# The real period of an elliptic curve over `ℚ` under an isogeny

Let `φ : E₁ → E₂` be an isogeny of elliptic curves over `ℚ`, pulling the invariant differential
back as `φ^*ω₂ = c ω₁` with `c ∈ ℚ`. The real period `Ω(E)` that enters the Birch–Swinnerton-Dyer
quotient is the real period of a global minimal equation (`WeierstrassCurve.minimalRealPeriod`),
while `E₁` and `E₂` are arbitrary equations. If `C₁` and `C₂` carry them to globally minimal
equations, with scaling factors `u₁` and `u₂`, then
`|c u₂ / u₁| Ω(E₁) · [E₂(ℝ) : φ(E₁(ℝ))] = #ker φ(ℝ) · Ω(E₂)`.
A change of variables with scaling factor `u` pulls the invariant differential back to `u` times
the invariant differential
(`TauCeti.Isogeny.pullbackDifferential_variableChangeIsogeny_invariantDifferential`), so
`c u₂ / u₁` is the constant of `φ` read between the global minimal equations of `E₁` and `E₂`.

## Main results

* `TauCeti.Isogeny.abs_mul_minimalRealPeriod_mul_index_eq_card_ker_mul`: **the real period of an
  elliptic curve over `ℚ` under an isogeny**,
  `|c u₂ / u₁| Ω(E₁) · [E₂(ℝ) : φ(E₁(ℝ))] = #ker φ(ℝ) · Ω(E₂)`.
* `TauCeti.Isogeny.abs_mul_minimalRealPeriod_mul_index_eq_card_ker_mul_of_isGlobalMinimal`: the
  same between globally minimal equations, `|c| Ω(E₁) · [E₂(ℝ) : φ(E₁(ℝ))] = #ker φ(ℝ) · Ω(E₂)`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1, III.5 and VIII.8.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. reine angew. Math. 217 (1965), 180–199: the transformation of the real
  period under an isogeny, used in the isogeny invariance of the Birch–Swinnerton-Dyer quotient.
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine

namespace TauCeti.Isogeny

variable {E₁ E₂ : WeierstrassCurve ℚ} [E₁.IsElliptic] [E₂.IsElliptic]

/-- **The real period of an elliptic curve over `ℚ` under an isogeny.** Let `φ : E₁ → E₂` be an
isogeny over `ℚ` with `φ^*ω₂ = c ω₁`, and let `C₁`, `C₂` be changes of variables carrying `E₁`,
`E₂` to globally minimal equations, with scaling factors `u₁`, `u₂`. Then
`|c u₂ / u₁| Ω(E₁) · [E₂(ℝ) : φ(E₁(ℝ))] = #ker φ(ℝ) · Ω(E₂)`, where `Ω` is the real period of a
global minimal equation and the index and the kernel are those of the base change of `φ` on real
points. -/
theorem abs_mul_minimalRealPeriod_mul_index_eq_card_ker_mul (φ : Isogeny E₁.toAffine E₂.toAffine)
    {c : ℚ} (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    {C₁ C₂ : VariableChange ℚ} (hC₁ : IsGlobalMinimal ℤ (C₁ • E₁))
    (hC₂ : IsGlobalMinimal ℤ (C₂ • E₂)) :
    |((c * C₂.u / C₁.u : ℚ) : ℝ)| * E₁.minimalRealPeriod *
        (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.range.index =
      Nat.card (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.ker * E₂.minimalRealPeriod := by
  have h := abs_mul_realPeriod_mul_index_eq_card_ker_mul (φ.baseChange ℝ)
    (map_pullbackDifferential_invariantDifferential_eq_smul φ (algebraMap ℚ ℝ) hc)
  have hu₁ : ((C₁.u : ℚ) : ℝ) ≠ 0 := by exact_mod_cast C₁.u.ne_zero
  rw [E₁.minimalRealPeriod_eq_abs_mul hC₁, E₂.minimalRealPeriod_eq_abs_mul hC₂]
  rw [eq_ratCast] at h
  push_cast
  rw [abs_div, abs_mul]
  -- the scaling factor `|u₁|` cancels, and `|u₂|` multiplies both sides of the real formula
  calc _ = |((C₂.u : ℚ) : ℝ)| * (|(c : ℝ)| * ((E₁.baseChange ℝ).realPeriod) *
        (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.range.index) := by
        field_simp [abs_ne_zero.mpr hu₁]
    _ = _ := by rw [h]; ring

/-- **The real period of an elliptic curve over `ℚ` under an isogeny between global minimal
equations.** If `φ : E₁ → E₂` is an isogeny over `ℚ` between globally minimal equations with
`φ^*ω₂ = c ω₁`, then `|c| Ω(E₁) · [E₂(ℝ) : φ(E₁(ℝ))] = #ker φ(ℝ) · Ω(E₂)`. -/
theorem abs_mul_minimalRealPeriod_mul_index_eq_card_ker_mul_of_isGlobalMinimal
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : ℚ}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    (h₁ : IsGlobalMinimal ℤ E₁) (h₂ : IsGlobalMinimal ℤ E₂) :
    |(c : ℝ)| * E₁.minimalRealPeriod *
        (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.range.index =
      Nat.card (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.ker * E₂.minimalRealPeriod := by
  rw [h₁.minimalRealPeriod_eq, h₂.minimalRealPeriod_eq]
  simpa only [eq_ratCast] using abs_mul_realPeriod_mul_index_eq_card_ker_mul (φ.baseChange ℝ)
    (map_pullbackDifferential_invariantDifferential_eq_smul φ (algebraMap ℚ ℝ) hc)

end TauCeti.Isogeny

end
