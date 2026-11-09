/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.ActiveFace
public import TauCeti.NumberTheory.NewtonPolygon.Multiplicity
public import TauCeti.RingTheory.PowerSeries.Weierstrass.ZeroCount

/-!
# Slope multiplicities count zeros

Let `K` be a complete ultrametric normed field with a real additive valuation `v` such that
`‖x‖ = b ^ (-(v x).untop₀)` for nonzero `x` and a base `b > 1`, and let `L` be an algebraically
closed complete normed field extension of `K`. If the Newton polygon of a power series `f`
restricted at `b ^ σ` has a finite face of slope `σ`, the multiplicity of the slope `σ` is the
number of zeros of `f` in `L` on the sphere `‖x‖ = b ^ σ`, counted with multiplicity
(`PowerSeries.newtonSlopeMultiplicity_eq_card_filter_zeroMultiset_norm_eq`). Indeed, the endpoints
`l ≤ u` of the face are the lowest dominant and distinguished degrees of `f` at `b ^ σ`
(`PowerSeries.isLowestDominant_and_isDistinguished_of_isFiniteFace_newtonPolygon`), the slope
multiplicity is the width `u - l` of the face, and there are exactly `u - l` zeros on the sphere
(`TauCeti.PowerSeries.card_filter_zeroMultiset_norm_eq_eq`).

A nonzero entire series has a finite face of every slope, so every slope multiplicity of its
Newton polygon counts zeros of the corresponding norm
(`PowerSeries.IsEntire.newtonSlopeMultiplicity_eq_card_filter_zeroMultiset_norm_eq`). For the
Fredholm series `det (1 - T u)` of a compact operator, a zero of multiplicity `h` at `a`
corresponds to the eigenvalue `a⁻¹` of algebraic multiplicity `h`, so slope multiplicities then
count eigenvalues by valuation.

## Main results

* `PowerSeries.newtonSlopeMultiplicity_eq_card_filter_zeroMultiset_norm_eq`: the multiplicity of
  the slope of a finite face counts the zeros on the corresponding sphere.
* `PowerSeries.IsEntire.newtonSlopeMultiplicity_eq_card_filter_zeroMultiset_norm_eq`: every slope
  multiplicity of a nonzero entire series counts its zeros of the corresponding norm.

## References

* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §§1, 3.
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition, Graduate
  Texts in Mathematics 58, Springer, 1984, Chapter IV §4.
-/

public section

open TauCeti

namespace PowerSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) (L : Type*) [NormedField L] [NormedAlgebra K L]
  [CompleteSpace L] [IsAlgClosed L] {f : K⟦X⟧}

include hb hv

/-- **Slope multiplicities count zeros on a sphere.** If `f` is restricted at `b ^ σ` and its
Newton polygon has a finite face of slope `σ`, then in any algebraically closed complete normed
field extension `L` the multiplicity of the slope `σ` is the number of zeros of `f` with
`‖x‖ = b ^ σ`, counted with multiplicity. The radius may lie on the boundary of convergence. -/
theorem newtonSlopeMultiplicity_eq_card_filter_zeroMultiset_norm_eq {σ : ℝ} {l u : ℕ}
    (hfr : f.IsRestricted (b ^ σ)) (hface : IsFiniteFace (f.newtonPolygon v) σ l u) :
    f.newtonSlopeMultiplicity v σ = ((f.zeroMultiset (b ^ σ) L).filter (‖·‖ = b ^ σ)).card := by
  obtain ⟨hl, hu⟩ := isLowestDominant_and_isDistinguished_of_isFiniteFace_newtonPolygon f v hb hv
    (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted hfr) hface
  rw [newtonSlopeMultiplicity_eq_of_isFiniteFace hface,
    TauCeti.PowerSeries.card_filter_zeroMultiset_norm_eq_eq hu hl
      (Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ) hfr]

/-- **Slope multiplicities of entire series count zeros.** For a nonzero entire series `f` and any
algebraically closed complete normed field extension `L`, the multiplicity of every slope `σ` of
the Newton polygon of `f` is the number of zeros of `f` in `L` with `‖x‖ = b ^ σ`, counted with
multiplicity. -/
theorem IsEntire.newtonSlopeMultiplicity_eq_card_filter_zeroMultiset_norm_eq (hf : f.IsEntire)
    (hf0 : f ≠ 0) (σ : ℝ) :
    f.newtonSlopeMultiplicity v σ = ((f.zeroMultiset (b ^ σ) L).filter (‖·‖ = b ^ σ)).card := by
  obtain ⟨l, u, hface⟩ := hf.exists_isFiniteFace_newtonPolygon v hb hv hf0 σ
  exact PowerSeries.newtonSlopeMultiplicity_eq_card_filter_zeroMultiset_norm_eq v hb hv L
    (hf.isRestricted _) hface

end PowerSeries
