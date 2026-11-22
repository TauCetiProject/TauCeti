/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Wishart.CharFun

import TauCeti.Probability.Distributions.Wishart.Congruence
import TauCeti.Probability.Distributions.Wishart.Rank

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
negative half is `TauCeti.Probability.mutuallySingular_wishartGramMeasure_symmetricLebesgue`: too
few
Gaussian factors, or a degenerate covariance, leave the Gram law with no density at all.

## Main results

* `TauCeti.Probability.wishartGramMeasure_eq_nonsingularWishartMeasure` — the two families agree
  wherever
  both describe the same classical law.
* `TauCeti.Probability.hasLaw_wishartGram_gaussian_nonsingularWishartMeasure` — a Gaussian sample of
  size at
  least the dimension has a Gram sum with the nonsingular Wishart law.
* `TauCeti.Probability.ae_posDef_wishartGramMeasure` — such a Gram sum is almost surely nonsingular.
* `map_symmetricCongruenceLinearMap_nonsingularWishartMeasure_eq_wishartGramMeasure` and
  `ProbabilityTheory.HasLaw.symmetricCongruenceLinearMap_wishartGramMeasure` — at a natural degree
  at least the dimension, congruence by a matrix of any rank, including a rank-deficient one,
  carries a nonsingular Wishart law to a Gaussian-Gram law;
  `ae_rank_eq_map_symmetricCongruenceLinearMap_nonsingularWishartMeasure` gives the almost sure
  rank of that image.
* `TauCeti.Probability.hasPDF_of_hasLaw_wishartGramMeasure` and
  `TauCeti.Probability.rnDeriv_wishartGramMeasure` — such
  a Gram law has a density against `TauCeti.symmetricLebesgue`, the nonsingular Wishart density.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley (1982), §3.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace TauCeti.Probability

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
Wishart law.** This is `TauCeti.Probability.hasLaw_wishartGram_gaussian` read through the agreement
of the
two families: with a nondegenerate covariance and a sample of size at least the dimension, the
Gram sum has the classical Wishart density. -/
theorem hasLaw_wishartGram_gaussian_nonsingularWishartMeasure {ν : ℕ}
    {S : Matrix (Fin p) (Fin p) ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Fin ν → Ω → EuclideanSpace ℝ (Fin p)} (hS : S.PosDef) (hp : p ≤ ν)
    (hX : ∀ r, HasLaw (X r) (multivariateGaussian 0 S) P) (hindep : iIndepFun X P) :
    HasLaw (fun ω => wishartGram fun r => X r ω) (nonsingularWishartMeasure (ν : ℝ) S) P :=
  wishartGramMeasure_eq_nonsingularWishartMeasure hS hp ▸ hasLaw_wishartGram_gaussian hX hindep

/-- **A Gaussian sample of size at least the dimension has an almost surely nonsingular Gram
sum.** With fewer vectors, or a degenerate covariance,
`TauCeti.Probability.ae_rank_le_wishartGramMeasure`
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
degenerate scale, `TauCeti.Probability.mutuallySingular_wishartGramMeasure_symmetricLebesgue` shows
that it
has none. -/
theorem hasPDF_of_hasLaw_wishartGramMeasure (hS : S.PosDef) (hp : p ≤ ν)
    (hX : HasLaw X (wishartGramMeasure ν S) P) : HasPDF X P (symmetricLebesgue p) :=
  hasPDF_of_hasLaw_nonsingularWishartMeasure
    (wishartGramMeasure_eq_nonsingularWishartMeasure hS hp ▸ hX)

/-- The density against `TauCeti.symmetricLebesgue` of a Gaussian-Gram random matrix with a
positive-definite scale and a degree at least the dimension is the Wishart density
`TauCeti.Probability.nonsingularWishartPDF` of the same degree and scale. -/
theorem pdf_eq_nonsingularWishartPDF_of_hasLaw_wishartGramMeasure (hS : S.PosDef) (hp : p ≤ ν)
    (hX : HasLaw X (wishartGramMeasure ν S) P) :
    pdf X P (symmetricLebesgue p) =ᵐ[symmetricLebesgue p] nonsingularWishartPDF (ν : ℝ) S :=
  pdf_eq_nonsingularWishartPDF_of_hasLaw_nonsingularWishartMeasure hS
    ((sub_one_lt _).trans_le (Nat.cast_le.2 hp))
    (wishartGramMeasure_eq_nonsingularWishartMeasure hS hp ▸ hX)

/-- **The Radon–Nikodym derivative of the Gaussian-Gram law** against `TauCeti.symmetricLebesgue`
is the Wishart density `TauCeti.Probability.nonsingularWishartPDF` of the same degree and scale, for
a
positive-definite scale and a degree at least the dimension. -/
theorem rnDeriv_wishartGramMeasure (hS : S.PosDef) (hp : p ≤ ν) :
    (wishartGramMeasure ν S).rnDeriv (symmetricLebesgue p) =ᵐ[symmetricLebesgue p]
      nonsingularWishartPDF (ν : ℝ) S := by
  rw [wishartGramMeasure_eq_nonsingularWishartMeasure hS hp]
  exact rnDeriv_nonsingularWishartMeasure hS ((sub_one_lt _).trans_le (Nat.cast_le.2 hp))

end Density

/-! ### Congruence images at natural degrees

Congruence by a `q × p` matrix `M` of full row rank keeps a nonsingular Wishart law inside the
density family (`TauCeti.Probability.map_symmetricCongruenceLinearMap_nonsingularWishartMeasure`).
A congruence of smaller rank leaves it: its image is carried by the singular matrices
(`MeasureTheory.Measure.mutuallySingular_map_symmetricCongruenceLinearMap_symmetricLebesgue`), so
at a real degree it remains a pushforward with no density. At a natural degree it is still a named
law, because the nonsingular law is then Gaussian-Gram and the Gram family is closed under every
congruence. -/

section Congruence

variable {q ν : ℕ} {S : Matrix (Fin p) (Fin p) ℝ}

/-- **The congruence image of a nonsingular Wishart law of natural degree is Gaussian-Gram.** For
a positive-definite scale `S` and a natural degree `ν ≥ p`, congruence by any `q × p` matrix `M`,
of whatever rank, carries the nonsingular Wishart law of scale `S` to the Gaussian-Gram law of
scale `M * S * Mᵀ`. When `M` has rank below `q` this image is not a nonsingular Wishart law:
`MeasureTheory.Measure.mutuallySingular_map_symmetricCongruenceLinearMap_symmetricLebesgue` makes
it singular with respect to `TauCeti.symmetricLebesgue`. -/
theorem map_symmetricCongruenceLinearMap_nonsingularWishartMeasure_eq_wishartGramMeasure
    (M : Matrix (Fin q) (Fin p) ℝ) (hS : S.PosDef) (hp : p ≤ ν) :
    (nonsingularWishartMeasure (ν : ℝ) S).map (Matrix.symmetricCongruenceLinearMap M) =
      wishartGramMeasure ν (M * S * Mᵀ) := by
  rw [← wishartGramMeasure_eq_nonsingularWishartMeasure hS hp,
    map_symmetricCongruenceLinearMap_wishartGramMeasure ν M hS.posSemidef]

/-- **The congruence image of a nonsingular Wishart matrix of natural degree has the rank of the
congruence matrix almost surely.** For a positive-definite scale and a natural degree `ν ≥ p`,
congruence by a `q × p` matrix `M` gives a matrix of rank exactly `M.rank` almost surely. -/
theorem ae_rank_eq_map_symmetricCongruenceLinearMap_nonsingularWishartMeasure
    (M : Matrix (Fin q) (Fin p) ℝ) (hS : S.PosDef) (hp : p ≤ ν) :
    ∀ᵐ A : selfAdjoint.submodule ℝ (Matrix (Fin q) (Fin q) ℝ)
        ∂(nonsingularWishartMeasure (ν : ℝ) S).map (Matrix.symmetricCongruenceLinearMap M),
      (A : Matrix (Fin q) (Fin q) ℝ).rank = M.rank := by
  have hrank : (M * S * Mᵀ).rank = M.rank := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hS.rank_mul_mul_conjTranspose M
  have hmin : min ν (M * S * Mᵀ).rank = M.rank := by
    rw [hrank, min_eq_right]
    simpa using M.rank_le_width.trans hp
  have hPSD : (M * S * Mᵀ).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hS.posSemidef.mul_mul_conjTranspose_same M
  rw [map_symmetricCongruenceLinearMap_nonsingularWishartMeasure_eq_wishartGramMeasure M hS hp]
  simpa only [hmin] using ae_rank_eq_wishartGramMeasure ν hPSD

end Congruence

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

/-- **A congruence of a nonsingular Wishart matrix of natural degree is Gaussian-Gram Wishart.**
Congruence by a `q × p` matrix `M` of any rank turns a nonsingular Wishart matrix of natural degree
`ν ≥ p` and positive-definite scale `S` into a Gaussian-Gram Wishart matrix of scale
`M * S * Mᵀ`. -/
theorem HasLaw.symmetricCongruenceLinearMap_wishartGramMeasure {p q ν : ℕ}
    {S : Matrix (Fin p) (Fin p) ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hX : HasLaw X (nonsingularWishartMeasure (ν : ℝ) S) P)
    (M : Matrix (Fin q) (Fin p) ℝ) (hS : S.PosDef) (hp : p ≤ ν) :
    HasLaw (fun ω ↦ Matrix.symmetricCongruenceLinearMap M (X ω))
      (wishartGramMeasure ν (M * S * Mᵀ)) P := by
  rw [← map_symmetricCongruenceLinearMap_nonsingularWishartMeasure_eq_wishartGramMeasure M hS hp]
  exact (hasLaw_map (LinearMap.continuous_of_finiteDimensional _).measurable.aemeasurable).comp hX

end ProbabilityTheory
