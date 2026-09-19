/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Wishart.CharFun

import TauCeti.Probability.Distributions.Wishart.Congruence

/-!
# Identifying Wishart laws through their characteristic function

The symmetric-matrix subspace is a complete second-countable real inner-product space, so
`MeasureTheory.Measure.ext_of_charFun` identifies two laws on it that share a characteristic
function. The characteristic function of either Wishart family is an exponential whose exponent
is linear in the degree, so the comparison below is arithmetic in that exponent.

The identity that comes out is that at a natural degree of at least the dimension, the
Gaussian-Gram law of a positive-definite scale is the nonsingular density law of the same degree
and scale. So the Gram sum of `ν ≥ p` independent centred Gaussian vectors with a nondegenerate
covariance has the classical Wishart density. This is the positive half of a dichotomy whose
negative half is `TauCeti.mutuallySingular_wishartGramMeasure_symmetricLebesgue`: too few
Gaussian factors, or a degenerate covariance, leave the Gram law with no density at all.

## Main results

* `TauCeti.wishartGramMeasure_eq_nonsingularWishartMeasure` — the two families agree wherever
  both describe the same classical law.
* `TauCeti.hasLaw_wishartGram_gaussian_nonsingularWishartMeasure` — a Gaussian sample of size at
  least the dimension has a Gram sum with the nonsingular Wishart law.
* `TauCeti.ae_posDef_wishartGramMeasure` — such a Gram sum is almost surely nonsingular.
* `TauCeti.hasPDF_of_hasLaw_wishartGramMeasure` and `TauCeti.rnDeriv_wishartGramMeasure` — such
  a Gram law has a density against `TauCeti.symmetricLebesgue`, the nonsingular Wishart density.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley (1982), §3.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

variable {p : ℕ}

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

section Density

variable {ν : ℕ} {S : Matrix (Fin p) (Fin p) ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {X : Ω → selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}

/-- **A Gaussian-Gram random matrix of degree at least the dimension has a density** against
`TauCeti.symmetricLebesgue` when its scale is positive definite. With fewer Gaussian factors, or a
degenerate scale, `TauCeti.mutuallySingular_wishartGramMeasure_symmetricLebesgue` shows that it
has none. -/
theorem hasPDF_of_hasLaw_wishartGramMeasure (hS : S.PosDef) (hp : p ≤ ν)
    (hX : HasLaw X (wishartGramMeasure ν S) P) : HasPDF X P (symmetricLebesgue p) :=
  hasPDF_of_hasLaw_nonsingularWishartMeasure hS ((sub_one_lt _).trans_le (Nat.cast_le.2 hp))
    (wishartGramMeasure_eq_nonsingularWishartMeasure hS hp ▸ hX)

/-- The density against `TauCeti.symmetricLebesgue` of a Gaussian-Gram random matrix with a
positive-definite scale and a degree at least the dimension is the Wishart density
`TauCeti.nonsingularWishartPDF` of the same degree and scale. -/
theorem pdf_eq_nonsingularWishartPDF_of_hasLaw_wishartGramMeasure (hS : S.PosDef) (hp : p ≤ ν)
    (hX : HasLaw X (wishartGramMeasure ν S) P) :
    pdf X P (symmetricLebesgue p) =ᵐ[symmetricLebesgue p] nonsingularWishartPDF (ν : ℝ) S :=
  pdf_eq_nonsingularWishartPDF_of_hasLaw_nonsingularWishartMeasure hS
    ((sub_one_lt _).trans_le (Nat.cast_le.2 hp))
    (wishartGramMeasure_eq_nonsingularWishartMeasure hS hp ▸ hX)

/-- **The Radon–Nikodym derivative of the Gaussian-Gram law** against `TauCeti.symmetricLebesgue`
is the Wishart density `TauCeti.nonsingularWishartPDF` of the same degree and scale, for a
positive-definite scale and a degree at least the dimension. -/
theorem rnDeriv_wishartGramMeasure (hS : S.PosDef) (hp : p ≤ ν) :
    (wishartGramMeasure ν S).rnDeriv (symmetricLebesgue p) =ᵐ[symmetricLebesgue p]
      nonsingularWishartPDF (ν : ℝ) S := by
  rw [wishartGramMeasure_eq_nonsingularWishartMeasure hS hp]
  exact rnDeriv_nonsingularWishartMeasure hS ((sub_one_lt _).trans_le (Nat.cast_le.2 hp))

end Density

end TauCeti
