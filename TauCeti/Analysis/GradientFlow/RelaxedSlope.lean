/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.GradientFlow.Slope

/-!
# The relaxed slope of an energy

For an extended-real energy `φ : X → EReal` on an extended metric space, the *relaxed slope* of
`φ` at `x` is

`|∂⁻φ|(x) = inf { liminf_n |∂φ|(u n) : u n → x, sup_n φ (u n) < ∞ }`,

the infimum, over sequences converging to `x` with energies bounded above, of the lower limits of
the descending slope `|∂φ|` along the sequence. Ambrosio–Gigli–Savaré also bound the distances
`d(u n, x)`; for a convergent sequence this only discards finitely many terms, which changes
neither the lower limit nor the infimum, and the same holds for the energy bound, which we only
ask eventually.

The descending slope of an energy need not be lower semicontinuous, while the limit theorems for
discrete gradient flows only control lower limits of the slopes at approximating points of bounded
energy. The relaxed slope is the largest function with this lower limit property: it is at most
the lower limit of the descending slopes along every convergent sequence of eventually bounded
energy (`TauCeti.relaxedSlope_le_liminf`), hence at most the descending slope on the effective
domain `{x | φ x ≠ ⊤}` (`TauCeti.relaxedSlope_le_descendingSlope`), and it is at least every
function which is below the descending slope on the effective domain and lower semicontinuous
within it (`TauCeti.le_relaxedSlope_of_lowerSemicontinuousWithinAt`). In particular the two
slopes agree where the descending slope is lower semicontinuous within the effective domain
(`TauCeti.relaxedSlope_eq_descendingSlope`), as it is for lower semicontinuous geodesically
convex energies.

## Main definitions

* `TauCeti.relaxedSlope φ x`: the relaxed slope of `φ` at `x`, an extended nonnegative real.

## Main results

* `TauCeti.relaxedSlope_le_liminf`: the relaxed slope at `x` is at most the lower limit of the
  descending slopes along any sequence of eventually bounded energy converging to `x`.
* `TauCeti.relaxedSlope_le_descendingSlope`: on the effective domain the relaxed slope is at most
  the descending slope.
* `TauCeti.le_relaxedSlope_of_lowerSemicontinuousWithinAt`: a function below the descending slope
  on the effective domain and lower semicontinuous within it at `x` is at most the relaxed slope
  at `x`.
* `TauCeti.relaxedSlope_eq_descendingSlope`: the two slopes agree where the descending slope is
  lower semicontinuous within the effective domain.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Chapter 2, Definition 2.3.1.
-/

public section

noncomputable section

open Filter Set Topology
open scoped ENNReal

namespace TauCeti

variable {X : Type*} [EMetricSpace X] {φ : X → EReal} {x : X}

/-- The *relaxed slope* of an energy `φ` at `x`: the infimum, over sequences `u` converging to `x`
whose energies are eventually bounded above by a real number, of the lower limit of the descending
slopes `|∂φ|(u n)`. It is `⊤` if no such sequence exists. -/
def relaxedSlope (φ : X → EReal) (x : X) : ℝ≥0∞ :=
  ⨅ (u : ℕ → X) (_ : Tendsto u atTop (𝓝 x)) (_ : ∃ C : ℝ, ∀ᶠ n in atTop, φ (u n) ≤ C),
    liminf (fun n ↦ descendingSlope φ (u n)) atTop

/-- The defining formula of the relaxed slope, as an infimum over convergent sequences of
eventually bounded energy. -/
theorem relaxedSlope_def (φ : X → EReal) (x : X) :
    relaxedSlope φ x =
      ⨅ (u : ℕ → X) (_ : Tendsto u atTop (𝓝 x)) (_ : ∃ C : ℝ, ∀ᶠ n in atTop, φ (u n) ≤ C),
        liminf (fun n ↦ descendingSlope φ (u n)) atTop :=
  (rfl)

/-- A lower bound for the relaxed slope: it is at least `c` exactly when the descending slopes
have lower limit at least `c` along every sequence converging to `x` with eventually bounded
energy. -/
theorem le_relaxedSlope_iff {c : ℝ≥0∞} : c ≤ relaxedSlope φ x ↔
    ∀ u : ℕ → X, Tendsto u atTop (𝓝 x) → (∃ C : ℝ, ∀ᶠ n in atTop, φ (u n) ≤ C) →
      c ≤ liminf (fun n ↦ descendingSlope φ (u n)) atTop := by
  simp only [relaxedSlope_def, le_iInf_iff]

/-- **The relaxed slope is below the lower limit of the slopes.** Along a sequence converging to
`x` whose energies are eventually bounded above by a real number, the lower limit of the
descending slopes is at least the relaxed slope at `x`. -/
theorem relaxedSlope_le_liminf {u : ℕ → X} (hu : Tendsto u atTop (𝓝 x)) {C : ℝ}
    (hC : ∀ᶠ n in atTop, φ (u n) ≤ C) :
    relaxedSlope φ x ≤ liminf (fun n ↦ descendingSlope φ (u n)) atTop :=
  le_relaxedSlope_iff.1 le_rfl u hu ⟨C, hC⟩

/-- **The relaxed slope is below the descending slope** at every point of the effective domain
`{x | φ x ≠ ⊤}`: test the relaxed slope against the constant sequence. -/
theorem relaxedSlope_le_descendingSlope (hx : φ x ≠ ⊤) :
    relaxedSlope φ x ≤ descendingSlope φ x := by
  simpa using relaxedSlope_le_liminf (φ := φ) tendsto_const_nhds
    (.of_forall fun _ ↦ EReal.le_coe_toReal hx)

/-- **Lower semicontinuous minorants of the slope are below the relaxed slope.** If `g` is
below the descending slope on the effective domain `{y | φ y ≠ ⊤}` and lower semicontinuous at
`x` within that domain, then `g x` is at most the relaxed slope at `x`. -/
theorem le_relaxedSlope_of_lowerSemicontinuousWithinAt {g : X → ℝ≥0∞}
    (hg : ∀ y, φ y ≠ ⊤ → g y ≤ descendingSlope φ y)
    (hglsc : LowerSemicontinuousWithinAt g {y | φ y ≠ ⊤} x) : g x ≤ relaxedSlope φ x := by
  refine le_relaxedSlope_iff.2 fun u hu ⟨C, hC⟩ ↦ ?_
  have hdom : ∀ᶠ n in atTop, φ (u n) ≠ ⊤ :=
    hC.mono fun _ h ↦ ne_top_of_le_ne_top (EReal.coe_ne_top C) h
  have hu' : Tendsto u atTop (𝓝[{y | φ y ≠ ⊤}] x) := tendsto_nhdsWithin_iff.2 ⟨hu, hdom⟩
  exact (hglsc.le_liminf.trans hu'.liminf_le_liminf_comp).trans
    (liminf_le_liminf (hdom.mono fun n hn ↦ hg (u n) hn))

/-- **The relaxed slope equals the descending slope where the latter is lower semicontinuous.**
At a point `x` of the effective domain at which the descending slope is lower semicontinuous
within the effective domain, the relaxed and the descending slopes agree. -/
theorem relaxedSlope_eq_descendingSlope (hx : φ x ≠ ⊤)
    (h : LowerSemicontinuousWithinAt (descendingSlope φ) {y | φ y ≠ ⊤} x) :
    relaxedSlope φ x = descendingSlope φ x :=
  le_antisymm (relaxedSlope_le_descendingSlope hx)
    (le_relaxedSlope_of_lowerSemicontinuousWithinAt (fun _ _ ↦ le_rfl) h)

end TauCeti
