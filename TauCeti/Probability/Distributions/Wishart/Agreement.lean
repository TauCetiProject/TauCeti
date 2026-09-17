/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Wishart.CharFun

import Mathlib.MeasureTheory.Group.Convolution
import TauCeti.Probability.Distributions.Wishart.Congruence

/-!
# Identifying Wishart laws through their characteristic function

The symmetric-matrix subspace is a complete second-countable real inner-product space, so
`MeasureTheory.Measure.ext_of_charFun` identifies two laws on it that share a characteristic
function. The characteristic function of either Wishart family is an exponential whose exponent
is linear in the degree, so each comparison below is arithmetic in that exponent.

Two identities come out. The degrees of the nonsingular family add under convolution; and, at a
natural degree of at least the dimension, the Gaussian-Gram law of a positive-definite scale is
the nonsingular density law of the same degree and scale. The second says that the Gram sum of
`ν ≥ p` independent centred Gaussian vectors with a nondegenerate covariance has the classical
Wishart density. It is the positive half of a dichotomy whose negative half is
`TauCeti.mutuallySingular_wishartGramMeasure_symmetricLebesgue`: too few Gaussian factors, or a
degenerate covariance, leave the Gram law with no density at all.

## Main results

* `TauCeti.nonsingularWishartMeasure_conv_nonsingularWishartMeasure` — at a fixed scale the
  degrees of the nonsingular family add under convolution.
* `TauCeti.wishartGramMeasure_eq_nonsingularWishartMeasure` — the two families agree wherever
  both describe the same classical law.
* `TauCeti.hasLaw_wishartGram_gaussian_nonsingularWishartMeasure` — a Gaussian sample of size at
  least the dimension has a Gram sum with the nonsingular Wishart law.
* `TauCeti.ae_posDef_wishartGramMeasure` — such a Gram sum is almost surely nonsingular.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley (1982), §3.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

variable {p : ℕ}

/-- **At a fixed scale the degrees of the nonsingular Wishart family add under convolution.**
No hypothesis on the scale is needed: away from positive definiteness all three laws are zero.

The hypothesis on the sum of the degrees is not implied by the other two. In dimension zero the
valid degrees are those above `-1`, and two of them can still sum to `-1` or less, where the law
is zero by definition while the convolution of the two Dirac laws is again Dirac. In positive
dimension the valid degrees are positive, so the hypothesis is automatic. -/
theorem nonsingularWishartMeasure_conv_nonsingularWishartMeasure {n₁ n₂ : ℝ}
    (S : Matrix (Fin p) (Fin p) ℝ) (hn₁ : (p : ℝ) - 1 < n₁) (hn₂ : (p : ℝ) - 1 < n₂)
    (hn : (p : ℝ) - 1 < n₁ + n₂) :
    nonsingularWishartMeasure n₁ S ∗ nonsingularWishartMeasure n₂ S =
      nonsingularWishartMeasure (n₁ + n₂) S := by
  by_cases hS : S.PosDef
  · have := isProbabilityMeasure_nonsingularWishartMeasure hS hn₁
    have := isProbabilityMeasure_nonsingularWishartMeasure hS hn₂
    have := isProbabilityMeasure_nonsingularWishartMeasure hS hn
    refine Measure.ext_of_charFun (funext fun Θ => ?_)
    rw [charFun_conv, charFun_nonsingularWishartMeasure hS hn₁,
      charFun_nonsingularWishartMeasure hS hn₂, charFun_nonsingularWishartMeasure hS hn,
      ← Complex.exp_add]
    push_cast
    ring_nf
  · simp [nonsingularWishartMeasure_of_not_posDef _ hS]

/-- **The two Wishart families agree where both describe the same law.** With a positive-definite
scale and a natural degree at least the dimension, the Gaussian-Gram law of degree `ν` is the
nonsingular density law of the same degree and scale.

The bound `p ≤ ν` is exactly the range `(p : ℝ) - 1 < ν` of natural degrees on which a density
defines the nonsingular family. Below it that family is the zero measure, while the Gram law is
still a probability measure, carried by the singular matrices. -/
theorem wishartGramMeasure_eq_nonsingularWishartMeasure {ν : ℕ} {S : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) (hp : p ≤ ν) :
    wishartGramMeasure ν S = nonsingularWishartMeasure (ν : ℝ) S := by
  have hn : (p : ℝ) - 1 < (ν : ℝ) := by
    have : (p : ℝ) ≤ (ν : ℝ) := Nat.cast_le.2 hp
    linarith
  have := isProbabilityMeasure_nonsingularWishartMeasure hS hn
  refine Measure.ext_of_charFun (funext fun Θ => ?_)
  rw [charFun_wishartGramMeasure, charFun_nonsingularWishartMeasure hS hn]
  push_cast
  ring_nf

/-- **The Gram sum of a large enough independent centred Gaussian family has the nonsingular
Wishart law.** This is `TauCeti.hasLaw_wishartGram_gaussian` read through the agreement of the
two families: with a nondegenerate covariance and a sample of size at least the dimension, the
Gram sum has the classical Wishart density. -/
theorem hasLaw_wishartGram_gaussian_nonsingularWishartMeasure {ν : ℕ}
    {S : Matrix (Fin p) (Fin p) ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Fin ν → Ω → EuclideanSpace ℝ (Fin p)} (hS : S.PosDef) (hp : p ≤ ν)
    (hX : ∀ r, HasLaw (X r) (multivariateGaussian 0 S) P) (hindep : iIndepFun X P) :
    HasLaw (fun ω => wishartGram fun r => X r ω) (nonsingularWishartMeasure (ν : ℝ) S) P :=
  wishartGramMeasure_eq_nonsingularWishartMeasure hS hp ▸ hasLaw_wishartGram_gaussian hX hindep

/-- **A Gaussian sample of size at least the dimension has an almost surely nonsingular Gram
sum.** With fewer vectors, or a degenerate covariance, `TauCeti.ae_rank_le_wishartGramMeasure`
makes the Gram sum almost surely singular instead. -/
theorem ae_posDef_wishartGramMeasure {ν : ℕ} {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (hp : p ≤ ν) :
    ∀ᵐ A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ∂wishartGramMeasure ν S,
      (A : Matrix (Fin p) (Fin p) ℝ).PosDef := by
  rw [wishartGramMeasure_eq_nonsingularWishartMeasure hS hp]
  exact ae_posDef_nonsingularWishartMeasure _ S

end TauCeti
