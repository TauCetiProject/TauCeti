/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Diagonal.CupProduct
public import TauCeti.Geometry.Manifold.Morse.Boundary.Integral
import TauCeti.Data.Set.Card
import TauCeti.LinearAlgebra.DirectSum.Finsupp

/-!
# Broken Y-flow lines with signs and the Leibniz rule of the integral Morse cup product

Let `f₀`, `f₁` and `f₂` be Morse functions on a compact boundaryless manifold `M`, with Morse–Smale
pseudo-gradients `X₀`, `X₁` and `X₂` adapted to them and orientation data `𝔬₀`, `𝔬₁` and `𝔬₂`.
The integral Morse diagonal `Δ` (`TauCeti.IsAdaptedPseudoGradient.signedMorseDiagonalMap`) counts
with signs the Y-flow lines from a critical point `p` of `f₀` to critical points `q` of `f₁` and
`r` of `f₂`, recorded by their vertices in the Y-slices
`W^u_{X₀}(p) ∩ W^s_{X₁}(q) ∩ W^s_{X₂}(r)`. This file is the integral counterpart of the algebraic
half of `TauCeti.Geometry.Manifold.Morse.Boundary.Diagonal.Basic`: it reduces the Leibniz rule of
the integral cup product to signed counts of broken Y-flow lines.

**The Koszul tensor differential.** The boundary of the tensor product of the Morse complexes of
`f₁` and `f₂` is `∂₁ ⊗ 1 + ε₁ ⊗ ∂₂`, where `ε₁` multiplies a critical point `q` of `f₁` by the
Koszul sign `(-1) ^ ind q`, as for the Morse complex of a product
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseChainProdEquiv_comp_signedMorseBoundary`):
`∂ (q ⊗ r) = ∂q ⊗ r + (-1) ^ ind q q ⊗ ∂r`.

**Broken Y-flow lines with signs.** For `ind p = ind q + ind r + 1`, the Y-flow lines broken along
one edge are the points of the sets `TauCeti.morseRootBrokenDiagonalSet`,
`TauCeti.morseFirstLeafBrokenDiagonalSet` and `TauCeti.morseSecondLeafBrokenDiagonalSet` of the
Y-slices. Each carries the product of the sign of its trajectory
(`TauCeti.IsAdaptedPseudoGradient.trajectorySign`) and of the sign of its Y-flow line
(`TauCeti.IsAdaptedPseudoGradient.morseYSign`):
`TauCeti.IsAdaptedPseudoGradient.morseRootBrokenDiagonalSign`,
`TauCeti.IsAdaptedPseudoGradient.morseFirstLeafBrokenDiagonalSign` and
`TauCeti.IsAdaptedPseudoGradient.morseSecondLeafBrokenDiagonalSign`. When the Y-slices with
`ind p = ind q + ind r` are finite, the sums of these signs are the `(q, r)`-coefficients of
`Δ (∂₀ p)`, of `(∂₁ ⊗ 1) (Δ p)` and of `(1 ⊗ ∂₂) (Δ p)`, with coefficients in any commutative ring.
So `Δ` is a chain map, `Δ ∘ ∂₀ = (∂₁ ⊗ 1 + ε₁ ⊗ ∂₂) ∘ Δ`, exactly when for all `p`, `q` and `r`

`Σ root - Σ first leaf - (-1) ^ ind q Σ second leaf = 0`

(`TauCeti.IsAdaptedPseudoGradient.signedMorseDiagonalMap_comp_signedMorseBoundary_eq_iff`). The
geometric half, that the broken Y-flow lines are the oriented ends of the compactified
one-dimensional spaces of Y-flow lines so that these sums vanish, is not proved here.

**The integral cup product.** For the integral cup product
`a ∪ b = (a ⊗ b) ∘ Δ` (`TauCeti.IsAdaptedPseudoGradient.signedMorseCupProduct`) and the coboundary
`δa = a ∘ ∂`, the Leibniz rule

`δ(a ∪ b) = δa ∪ b + (a ∘ ε₁) ∪ δb`

holds for all `a` and `b` exactly when `Δ` is a chain map
(`signedMorseCupProduct_comp_signedMorseBoundary_eq_iff_signedMorseDiagonalMap_comp_eq`), hence
exactly when the signed counts of broken Y-flow lines vanish
(`signedMorseCupProduct_comp_signedMorseBoundary_eq_iff`).

## Main definitions

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `morseRootBrokenDiagonalSign`, `morseFirstLeafBrokenDiagonalSign`,
  `morseSecondLeafBrokenDiagonalSign`: the signs of the Y-flow lines broken at the root, at the
  first leaf and at the second leaf.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `finsuppTensorFinsupp'_signedMorseDiagonalMap_signedMorseBoundary_single_apply`,
  `finsuppTensorFinsupp'_rTensor_signedMorseBoundary_signedMorseDiagonalMap_single_apply`,
  `finsuppTensorFinsupp'_map_signEquiv_signedMorseBoundary_signedMorseDiagonalMap_single_apply`:
  the three terms of the chain-map identity count broken Y-flow lines with signs.
* `signedMorseDiagonalMap_comp_signedMorseBoundary_eq_iff`: the integral diagonal is a chain map
  for the Koszul tensor differential exactly when the signed counts of broken Y-flow lines vanish.
* `signedMorseCupProduct_comp_signedMorseBoundary_eq_iff`: the Leibniz rule of the integral cup
  product holds exactly when the signed counts of broken Y-flow lines vanish.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (signed counts of broken trajectories).
* S. Mescher, *Perturbed gradient flow trees and A∞-algebra structures in Morse cohomology*,
  arXiv:1611.07916, §§1–5 and Appendix A (the Morse cup product from Y-flow lines and its
  Leibniz rule with signs).
-/

public section

open Function Set
open scoped ContDiff Manifold TensorProduct

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f₀ f₁ f₂ : M → ℝ} {X₀ X₁ X₂ : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

/-! ### Signs of broken Y-flow lines -/

section Sign

variable (hX₀ : IsAdaptedPseudoGradient f₀ X₀) (hX₁ : IsAdaptedPseudoGradient f₁ X₁)
  (hX₂ : IsAdaptedPseudoGradient f₂ X₂) (𝔬₀ : MorseOrientation f₀ X₀)
  (𝔬₁ : MorseOrientation f₁ X₁) (𝔬₂ : MorseOrientation f₂ X₂)

/-- The **sign of a Y-flow line broken at the root** `x = (p', z, y)` from `p` to `q` and `r`: the
product of the sign of the trajectory of `X₀` from `p` to `p'` through `z` and the sign of the
Y-flow line from `p'` to `q` and `r` with vertex `y`, when `ind p = ind p' + 1` and
`ind p' = ind q + ind r`, and `0` otherwise. -/
noncomputable def morseRootBrokenDiagonalSign (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁) (r : criticalPoints 𝓘(ℝ, E) f₂)
    (x : criticalPoints 𝓘(ℝ, E) f₀ × M × M) : ℤ :=
  if h : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 + 1 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 =
        manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r then
    hX₀.trajectorySign (𝔬₀.chart p) (𝔬₀.chart x.1) (𝔬₀.orientation p) (𝔬₀.orientation x.1) h.1
        x.2.1 *
      hX₀.morseYSign hX₁ hX₂ (𝔬₀.chart x.1) (𝔬₁.chart q) (𝔬₂.chart r) (𝔬₀.orientation x.1)
        (𝔬₁.orientation q) (𝔬₂.orientation r) h.2 x.2.2
  else 0

/-- The **sign of a Y-flow line broken at the first leaf** `x = (q', y, z)` from `p` to `q` and
`r`: the product of the sign of the Y-flow line from `p` to `q'` and `r` with vertex `y` and the
sign of the trajectory of `X₁` from `q'` to `q` through `z`, when `ind p = ind q' + ind r` and
`ind q' = ind q + 1`, and `0` otherwise. -/
noncomputable def morseFirstLeafBrokenDiagonalSign (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁) (r : criticalPoints 𝓘(ℝ, E) f₂)
    (x : criticalPoints 𝓘(ℝ, E) f₁ × M × M) : ℤ :=
  if h : manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
        manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 + manifoldMorseIndex 𝓘(ℝ, E) f₂ r ∧
      manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₁ q + 1 then
    hX₀.morseYSign hX₁ hX₂ (𝔬₀.chart p) (𝔬₁.chart x.1) (𝔬₂.chart r) (𝔬₀.orientation p)
        (𝔬₁.orientation x.1) (𝔬₂.orientation r) h.1 x.2.1 *
      hX₁.trajectorySign (𝔬₁.chart x.1) (𝔬₁.chart q) (𝔬₁.orientation x.1) (𝔬₁.orientation q) h.2
        x.2.2
  else 0

/-- The **sign of a Y-flow line broken at the second leaf** `x = (r', y, z)` from `p` to `q` and
`r`: the product of the sign of the Y-flow line from `p` to `q` and `r'` with vertex `y` and the
sign of the trajectory of `X₂` from `r'` to `r` through `z`, when `ind p = ind q + ind r'` and
`ind r' = ind r + 1`, and `0` otherwise. -/
noncomputable def morseSecondLeafBrokenDiagonalSign (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁) (r : criticalPoints 𝓘(ℝ, E) f₂)
    (x : criticalPoints 𝓘(ℝ, E) f₂ × M × M) : ℤ :=
  if h : manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
        manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ x.1 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f₂ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₂ r + 1 then
    hX₀.morseYSign hX₁ hX₂ (𝔬₀.chart p) (𝔬₁.chart q) (𝔬₂.chart x.1) (𝔬₀.orientation p)
        (𝔬₁.orientation q) (𝔬₂.orientation x.1) h.1 x.2.1 *
      hX₂.trajectorySign (𝔬₂.chart x.1) (𝔬₂.chart r) (𝔬₂.orientation x.1) (𝔬₂.orientation r) h.2
        x.2.2
  else 0

variable {hX₀ hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂} {p : criticalPoints 𝓘(ℝ, E) f₀}
  {q : criticalPoints 𝓘(ℝ, E) f₁} {r : criticalPoints 𝓘(ℝ, E) f₂}

/-- When the indices fit, the sign of a Y-flow line broken at the root is the product of the signs
of its trajectory and of its Y-flow line. -/
theorem morseRootBrokenDiagonalSign_of_morseIndex_eq {x : criticalPoints 𝓘(ℝ, E) f₀ × M × M}
    (hpp : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 + 1)
    (hpqr : manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r) :
    hX₀.morseRootBrokenDiagonalSign hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ p q r x =
      hX₀.trajectorySign (𝔬₀.chart p) (𝔬₀.chart x.1) (𝔬₀.orientation p) (𝔬₀.orientation x.1)
          hpp x.2.1 *
        hX₀.morseYSign hX₁ hX₂ (𝔬₀.chart x.1) (𝔬₁.chart q) (𝔬₂.chart r) (𝔬₀.orientation x.1)
          (𝔬₁.orientation q) (𝔬₂.orientation r) hpqr x.2.2 :=
  dite_eq_left ⟨hpp, hpqr⟩

/-- The sign of a Y-flow line broken at the root vanishes unless the indices fit. -/
@[simp]
theorem morseRootBrokenDiagonalSign_of_not_morseIndex_eq
    {x : criticalPoints 𝓘(ℝ, E) f₀ × M × M}
    (h : ¬(manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 + 1 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 =
        manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r)) :
    hX₀.morseRootBrokenDiagonalSign hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ p q r x = 0 :=
  dite_eq_right h

/-- When the indices fit, the sign of a Y-flow line broken at the first leaf is the product of the
signs of its Y-flow line and of its trajectory. -/
theorem morseFirstLeafBrokenDiagonalSign_of_morseIndex_eq
    {x : criticalPoints 𝓘(ℝ, E) f₁ × M × M}
    (hpqr : manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 + manifoldMorseIndex 𝓘(ℝ, E) f₂ r)
    (hqq : manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₁ q + 1) :
    hX₀.morseFirstLeafBrokenDiagonalSign hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ p q r x =
      hX₀.morseYSign hX₁ hX₂ (𝔬₀.chart p) (𝔬₁.chart x.1) (𝔬₂.chart r) (𝔬₀.orientation p)
          (𝔬₁.orientation x.1) (𝔬₂.orientation r) hpqr x.2.1 *
        hX₁.trajectorySign (𝔬₁.chart x.1) (𝔬₁.chart q) (𝔬₁.orientation x.1) (𝔬₁.orientation q)
          hqq x.2.2 :=
  dite_eq_left ⟨hpqr, hqq⟩

/-- The sign of a Y-flow line broken at the first leaf vanishes unless the indices fit. -/
@[simp]
theorem morseFirstLeafBrokenDiagonalSign_of_not_morseIndex_eq
    {x : criticalPoints 𝓘(ℝ, E) f₁ × M × M}
    (h : ¬(manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
        manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 + manifoldMorseIndex 𝓘(ℝ, E) f₂ r ∧
      manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₁ q + 1)) :
    hX₀.morseFirstLeafBrokenDiagonalSign hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ p q r x = 0 :=
  dite_eq_right h

/-- When the indices fit, the sign of a Y-flow line broken at the second leaf is the product of
the signs of its Y-flow line and of its trajectory. -/
theorem morseSecondLeafBrokenDiagonalSign_of_morseIndex_eq
    {x : criticalPoints 𝓘(ℝ, E) f₂ × M × M}
    (hpqr : manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ x.1)
    (hrr : manifoldMorseIndex 𝓘(ℝ, E) f₂ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₂ r + 1) :
    hX₀.morseSecondLeafBrokenDiagonalSign hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ p q r x =
      hX₀.morseYSign hX₁ hX₂ (𝔬₀.chart p) (𝔬₁.chart q) (𝔬₂.chart x.1) (𝔬₀.orientation p)
          (𝔬₁.orientation q) (𝔬₂.orientation x.1) hpqr x.2.1 *
        hX₂.trajectorySign (𝔬₂.chart x.1) (𝔬₂.chart r) (𝔬₂.orientation x.1) (𝔬₂.orientation r)
          hrr x.2.2 :=
  dite_eq_left ⟨hpqr, hrr⟩

/-- The sign of a Y-flow line broken at the second leaf vanishes unless the indices fit. -/
@[simp]
theorem morseSecondLeafBrokenDiagonalSign_of_not_morseIndex_eq
    {x : criticalPoints 𝓘(ℝ, E) f₂ × M × M}
    (h : ¬(manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
        manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ x.1 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f₂ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₂ r + 1)) :
    hX₀.morseSecondLeafBrokenDiagonalSign hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ p q r x = 0 :=
  dite_eq_right h

end Sign

/-! ### Counting broken Y-flow lines with signs -/

section Count

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  {hX₂ : IsAdaptedPseudoGradient f₂ X₂} {𝔬₀ : MorseOrientation f₀ X₀}
  {𝔬₁ : MorseOrientation f₁ X₁} {𝔬₂ : MorseOrientation f₂ X₂}
  (h₀ : hX₀.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
  (h₁ : hX₁.IsMorseSmale) (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
  (h₂ : hX₂.IsMorseSmale) (hf₂ : IsMorse 𝓘(ℝ, E) f₂) {R : Type*} [CommRing R]
  (hS : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁)
    (r : criticalPoints 𝓘(ℝ, E) f₂), manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r →
    (hX₀.morseYSlice hX₁ hX₂ p q r).Finite)

/-- When `ind p = ind q + ind r` and the Y-slice is finite, the coefficient of the integral Morse
diagonal is the sum of the signs over the Y-slice, written with the index condition inside. -/
private theorem signedMorseDiagonalCoeff_eq_finsum_mem {p : criticalPoints 𝓘(ℝ, E) f₀}
    {q : criticalPoints 𝓘(ℝ, E) f₁} {r : criticalPoints 𝓘(ℝ, E) f₂}
    (hpqr : manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r) :
    hX₀.signedMorseDiagonalCoeff hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ p q r =
      ∑ᶠ y ∈ hX₀.morseYSlice hX₁ hX₂ p q r,
        if h : manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
            manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r then
          hX₀.morseYSign hX₁ hX₂ (𝔬₀.chart p) (𝔬₁.chart q) (𝔬₂.chart r) (𝔬₀.orientation p)
            (𝔬₁.orientation q) (𝔬₂.orientation r) h y
        else 0 := by
  rw [signedMorseDiagonalCoeff_eq_signedMorseYCount hpqr, signedMorseYCount_def]
  exact finsum_mem_congr rfl fun _ _ ↦ by rw [dite_eq_left hpqr]

include h₀ hS in
/-- **`Δ ∘ ∂₀` counts Y-flow lines broken at the root with signs.** When the Y-slices with
`ind p' = ind q + ind r` are finite, the `(q, r)`-coefficient of the integral Morse diagonal of the
integral Morse boundary of `p` is the sum of the signs of the Y-flow lines from `p` to `q` and `r`
broken at the root. -/
theorem finsuppTensorFinsupp'_signedMorseDiagonalMap_signedMorseBoundary_single_apply
    (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁)
    (r : criticalPoints 𝓘(ℝ, E) f₂) :
    finsuppTensorFinsupp' R _ _ (hX₀.signedMorseDiagonalMap hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R
        (hX₀.signedMorseBoundary 𝔬₀ hf₀ R (Finsupp.single p 1))) (q, r) =
      ((∑ᶠ x ∈ morseRootBrokenDiagonalSet f₁ f₂ (hX₀.morseYSlice hX₁ hX₂) hX₀ p q r,
        hX₀.morseRootBrokenDiagonalSign hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ p q r x : ℤ) : R) := by
  have := hf₀.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f₀)
  rw [finsuppTensorFinsupp'_signedMorseDiagonalMap_apply,
    Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _]
  simp_rw [signedMorseBoundary_single_apply, one_mul, ← Int.cast_mul, ← Int.cast_sum]
  congr 1
  -- Sort the broken Y-flow lines by their intermediate critical point `p'`: the sign splits as the
  -- product of the signs of the trajectory from `p` to `p'` and of the Y-flow line from `p'`.
  rw [← finsum_mem_setOf_and_and_mem_and_mem
    (P := fun p' : criticalPoints 𝓘(ℝ, E) f₀ ↦
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ p' + 1)
    (Q := fun p' ↦ manifoldMorseIndex 𝓘(ℝ, E) f₀ p' =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r)
    (A := (hX₀.morseTrajectorySlice p ·)) (B := (hX₀.morseYSlice hX₁ hX₂ · q r))
    (fun _ ↦ h₀.finite_morseTrajectorySlice hf₀) (fun p' ↦ hS p' q r)
    (fun _ ↦ signedMorseBoundaryCoeff_eq_finsum_mem)
    (fun _ ↦ signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one)
    (fun _ ↦ signedMorseDiagonalCoeff_eq_finsum_mem)
    (fun _ ↦ signedMorseDiagonalCoeff_eq_zero_of_manifoldMorseIndex_ne)]
  refine finsum_mem_congr (Set.ext fun _ ↦ (mem_morseRootBrokenDiagonalSet hX₀).symm) fun x hx ↦ ?_
  obtain ⟨hpp, hpqr, -⟩ := (mem_morseRootBrokenDiagonalSet hX₀).1 hx
  rw [morseRootBrokenDiagonalSign_of_morseIndex_eq hpp hpqr, dite_eq_left hpp, dite_eq_left hpqr]

include h₁ hS in
/-- **`(∂₁ ⊗ 1) ∘ Δ` counts Y-flow lines broken at the first leaf with signs.** When the Y-slices
with `ind p = ind q' + ind r` are finite, the `(q, r)`-coefficient of `(∂₁ ⊗ 1) (Δ p)` is the sum
of the signs of the Y-flow lines from `p` to `q` and `r` broken at the first leaf. -/
theorem finsuppTensorFinsupp'_rTensor_signedMorseBoundary_signedMorseDiagonalMap_single_apply
    (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁)
    (r : criticalPoints 𝓘(ℝ, E) f₂) :
    finsuppTensorFinsupp' R _ _ ((hX₁.signedMorseBoundary 𝔬₁ hf₁ R).rTensor _
        (hX₀.signedMorseDiagonalMap hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R (Finsupp.single p 1))) (q, r) =
      ((∑ᶠ x ∈ morseFirstLeafBrokenDiagonalSet f₀ f₂ (hX₀.morseYSlice hX₁ hX₂) hX₁ p q r,
        hX₀.morseFirstLeafBrokenDiagonalSign hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ p q r x : ℤ) : R) := by
  have := hf₁.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f₁)
  rw [finsuppTensorFinsupp'_rTensor_apply]
  simp_rw [finsuppTensorFinsupp'_signedMorseDiagonalMap_single_apply,
    signedMorseBoundary_single_apply, one_mul, ← Int.cast_mul, ← Int.cast_sum]
  congr 1
  -- Sort the broken Y-flow lines by their intermediate critical point `q'`.
  rw [← finsum_mem_setOf_and_and_mem_and_mem
    (P := fun q' : criticalPoints 𝓘(ℝ, E) f₁ ↦ manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q' + manifoldMorseIndex 𝓘(ℝ, E) f₂ r)
    (Q := fun q' ↦ manifoldMorseIndex 𝓘(ℝ, E) f₁ q' = manifoldMorseIndex 𝓘(ℝ, E) f₁ q + 1)
    (A := (hX₀.morseYSlice hX₁ hX₂ p · r)) (B := (hX₁.morseTrajectorySlice · q))
    (fun q' ↦ hS p q' r) (fun _ ↦ h₁.finite_morseTrajectorySlice hf₁)
    (fun _ ↦ signedMorseDiagonalCoeff_eq_finsum_mem)
    (fun _ ↦ signedMorseDiagonalCoeff_eq_zero_of_manifoldMorseIndex_ne)
    (fun _ ↦ signedMorseBoundaryCoeff_eq_finsum_mem)
    (fun _ ↦ signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one)]
  refine finsum_mem_congr (Set.ext fun _ ↦ (mem_morseFirstLeafBrokenDiagonalSet hX₁).symm)
    fun x hx ↦ ?_
  obtain ⟨hpqr, hqq, -⟩ := (mem_morseFirstLeafBrokenDiagonalSet hX₁).1 hx
  rw [morseFirstLeafBrokenDiagonalSign_of_morseIndex_eq hpqr hqq, dite_eq_left hpqr,
    dite_eq_left hqq]

include h₂ hS in
/-- **`(ε₁ ⊗ ∂₂) ∘ Δ` counts Y-flow lines broken at the second leaf with signs.** When the
Y-slices with `ind p = ind q + ind r'` are finite, the `(q, r)`-coefficient of `(ε₁ ⊗ ∂₂) (Δ p)`,
for the Koszul sign `ε₁ : q ↦ (-1) ^ ind q • q`, is `(-1) ^ ind q` times the sum of the signs of
the Y-flow lines from `p` to `q` and `r` broken at the second leaf. -/
theorem finsuppTensorFinsupp'_map_signEquiv_signedMorseBoundary_signedMorseDiagonalMap_single_apply
    (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁)
    (r : criticalPoints 𝓘(ℝ, E) f₂) :
    finsuppTensorFinsupp' R _ _ (TensorProduct.map
        (Finsupp.signEquiv (A := R) R
          fun q : criticalPoints 𝓘(ℝ, E) f₁ ↦ (-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f₁ q).toLinearMap
        (hX₂.signedMorseBoundary 𝔬₂ hf₂ R)
        (hX₀.signedMorseDiagonalMap hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R (Finsupp.single p 1))) (q, r) =
      (((-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f₁ q *
        ∑ᶠ x ∈ morseSecondLeafBrokenDiagonalSet f₀ f₁ (hX₀.morseYSlice hX₁ hX₂) hX₂ p q r,
          hX₀.morseSecondLeafBrokenDiagonalSign hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ p q r x : ℤ) : R) := by
  have := hf₂.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f₂)
  rw [finsuppTensorFinsupp'_map_signEquiv_apply, finsuppTensorFinsupp'_lTensor_apply, Int.cast_mul,
    Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  congr 1
  simp_rw [finsuppTensorFinsupp'_signedMorseDiagonalMap_single_apply,
    signedMorseBoundary_single_apply, one_mul, ← Int.cast_mul, ← Int.cast_sum]
  congr 1
  -- Sort the broken Y-flow lines by their intermediate critical point `r'`.
  rw [← finsum_mem_setOf_and_and_mem_and_mem
    (P := fun r' : criticalPoints 𝓘(ℝ, E) f₂ ↦ manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r')
    (Q := fun r' ↦ manifoldMorseIndex 𝓘(ℝ, E) f₂ r' = manifoldMorseIndex 𝓘(ℝ, E) f₂ r + 1)
    (A := (hX₀.morseYSlice hX₁ hX₂ p q ·)) (B := (hX₂.morseTrajectorySlice · r))
    (fun r' ↦ hS p q r') (fun _ ↦ h₂.finite_morseTrajectorySlice hf₂)
    (fun _ ↦ signedMorseDiagonalCoeff_eq_finsum_mem)
    (fun _ ↦ signedMorseDiagonalCoeff_eq_zero_of_manifoldMorseIndex_ne)
    (fun _ ↦ signedMorseBoundaryCoeff_eq_finsum_mem)
    (fun _ ↦ signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one)]
  refine finsum_mem_congr (Set.ext fun _ ↦ (mem_morseSecondLeafBrokenDiagonalSet hX₂).symm)
    fun x hx ↦ ?_
  obtain ⟨hpqr, hrr, -⟩ := (mem_morseSecondLeafBrokenDiagonalSet hX₂).1 hx
  rw [morseSecondLeafBrokenDiagonalSign_of_morseIndex_eq hpqr hrr, dite_eq_left hpqr,
    dite_eq_left hrr]

include h₀ h₁ h₂ hS in
/-- **The integral Morse diagonal is a chain map exactly when the signed counts of broken Y-flow
lines vanish.** When the Y-slices with `ind p = ind q + ind r` are finite, the integral Morse
diagonal `Δ` with coefficients in a commutative ring `R` satisfies
`Δ ∘ ∂₀ = (∂₁ ⊗ 1 + ε₁ ⊗ ∂₂) ∘ Δ`, for the Koszul sign `ε₁ : q ↦ (-1) ^ ind q • q`, exactly when
for all critical points `p`, `q` and `r` of `f₀`, `f₁` and `f₂` the signs of the Y-flow lines from
`p` to `q` and `r` broken at the root, minus those broken at the first leaf, minus `(-1) ^ ind q`
times those broken at the second leaf, sum to zero in `R`. In particular, if these integer sums
vanish, then the diagonal is a chain map over every commutative ring. -/
theorem signedMorseDiagonalMap_comp_signedMorseBoundary_eq_iff :
    hX₀.signedMorseDiagonalMap hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R ∘ₗ hX₀.signedMorseBoundary 𝔬₀ hf₀ R =
        ((hX₁.signedMorseBoundary 𝔬₁ hf₁ R).rTensor _ + TensorProduct.map
          (Finsupp.signEquiv (A := R) R fun q : criticalPoints 𝓘(ℝ, E) f₁ ↦
            (-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f₁ q).toLinearMap
          (hX₂.signedMorseBoundary 𝔬₂ hf₂ R)) ∘ₗ
          hX₀.signedMorseDiagonalMap hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R ↔
      ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁)
        (r : criticalPoints 𝓘(ℝ, E) f₂),
        ((∑ᶠ x ∈ morseRootBrokenDiagonalSet f₁ f₂ (hX₀.morseYSlice hX₁ hX₂) hX₀ p q r,
            hX₀.morseRootBrokenDiagonalSign hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ p q r x -
          ∑ᶠ x ∈ morseFirstLeafBrokenDiagonalSet f₀ f₂ (hX₀.morseYSlice hX₁ hX₂) hX₁ p q r,
            hX₀.morseFirstLeafBrokenDiagonalSign hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ p q r x -
          (-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f₁ q *
            ∑ᶠ x ∈ morseSecondLeafBrokenDiagonalSet f₀ f₁ (hX₀.morseYSlice hX₁ hX₂) hX₂ p q r,
              hX₀.morseSecondLeafBrokenDiagonalSign hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ p q r x : ℤ) : R) = 0 := by
  -- Compare the two sides coefficientwise on each critical point, through the identification of
  -- the tensor product with functions on pairs of critical points.
  have hcoeff : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁)
      (r : criticalPoints 𝓘(ℝ, E) f₂), finsuppTensorFinsupp' R _ _
        ((hX₀.signedMorseDiagonalMap hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R ∘ₗ
          hX₀.signedMorseBoundary 𝔬₀ hf₀ R) (Finsupp.single p 1)) (q, r) =
        finsuppTensorFinsupp' R _ _
          ((((hX₁.signedMorseBoundary 𝔬₁ hf₁ R).rTensor _ + TensorProduct.map
            (Finsupp.signEquiv (A := R) R fun q : criticalPoints 𝓘(ℝ, E) f₁ ↦
              (-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f₁ q).toLinearMap
            (hX₂.signedMorseBoundary 𝔬₂ hf₂ R)) ∘ₗ
            hX₀.signedMorseDiagonalMap hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R) (Finsupp.single p 1)) (q, r) ↔
      ((∑ᶠ x ∈ morseRootBrokenDiagonalSet f₁ f₂ (hX₀.morseYSlice hX₁ hX₂) hX₀ p q r,
            hX₀.morseRootBrokenDiagonalSign hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ p q r x -
          ∑ᶠ x ∈ morseFirstLeafBrokenDiagonalSet f₀ f₂ (hX₀.morseYSlice hX₁ hX₂) hX₁ p q r,
            hX₀.morseFirstLeafBrokenDiagonalSign hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ p q r x -
          (-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f₁ q *
            ∑ᶠ x ∈ morseSecondLeafBrokenDiagonalSet f₀ f₁ (hX₀.morseYSlice hX₁ hX₂) hX₂ p q r,
              hX₀.morseSecondLeafBrokenDiagonalSign hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ p q r x : ℤ) : R) = 0 := by
    intro p q r
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.add_apply, map_add, Finsupp.add_apply,
      finsuppTensorFinsupp'_signedMorseDiagonalMap_signedMorseBoundary_single_apply h₀ hf₀ hf₁ hf₂
        hS,
      finsuppTensorFinsupp'_rTensor_signedMorseBoundary_signedMorseDiagonalMap_single_apply h₁ hf₁
        hf₂ hS,
      finsuppTensorFinsupp'_map_signEquiv_signedMorseBoundary_signedMorseDiagonalMap_single_apply
        hf₁ h₂ hf₂ hS]
    push_cast
    constructor <;> intro h <;> linear_combination h
  refine ⟨fun h p q r ↦ (hcoeff p q r).1 (by rw [h]), fun h ↦
    Finsupp.lhom_ext' fun p ↦ LinearMap.ext_ring ?_⟩
  exact (finsuppTensorFinsupp' R _ _).injective
    (Finsupp.ext fun x ↦ (hcoeff p x.1 x.2).2 (h p x.1 x.2))

end Count

/-! ### The Leibniz rule of the integral cup product -/

section CupProduct

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  {hX₂ : IsAdaptedPseudoGradient f₂ X₂} {𝔬₀ : MorseOrientation f₀ X₀}
  {𝔬₁ : MorseOrientation f₁ X₁} {𝔬₂ : MorseOrientation f₂ X₂}
  (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (hf₂ : IsMorse 𝓘(ℝ, E) f₂)
  {R : Type*} [CommRing R] (h₀ : hX₀.IsMorseSmale) (h₁ : hX₁.IsMorseSmale)
  (h₂ : hX₂.IsMorseSmale)

include h₀ h₁ h₂ in
/-- **The Leibniz rule of the integral cup product holds exactly when the signed counts of broken
Y-flow lines vanish.** When the Y-slices with `ind p = ind q + ind r` are finite, the integral cup
product with coefficients in a commutative ring `R` satisfies `δ(a ∪ b) = δa ∪ b + (a ∘ ε₁) ∪ δb`
for all linear forms `a` and `b`, where `ε₁ : q ↦ (-1) ^ ind q • q` is the Koszul sign, exactly
when for all critical points `p`, `q` and `r` the signs of the Y-flow lines from `p` to `q` and `r`
broken at the root, minus those broken at the first leaf, minus `(-1) ^ ind q` times those broken
at the second leaf, sum to zero in `R`. -/
theorem signedMorseCupProduct_comp_signedMorseBoundary_eq_iff
    (hS : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁)
      (r : criticalPoints 𝓘(ℝ, E) f₂), manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
        manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r →
      (hX₀.morseYSlice hX₁ hX₂ p q r).Finite) :
    (∀ (a : (criticalPoints 𝓘(ℝ, E) f₁ →₀ R) →ₗ[R] R)
        (b : (criticalPoints 𝓘(ℝ, E) f₂ →₀ R) →ₗ[R] R),
        hX₀.signedMorseCupProduct hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R a b ∘ₗ
            hX₀.signedMorseBoundary 𝔬₀ hf₀ R =
          hX₀.signedMorseCupProduct hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R
              (a ∘ₗ hX₁.signedMorseBoundary 𝔬₁ hf₁ R) b +
            hX₀.signedMorseCupProduct hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R
              (a ∘ₗ (Finsupp.signEquiv (A := R) R fun q : criticalPoints 𝓘(ℝ, E) f₁ ↦
                (-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f₁ q).toLinearMap)
              (b ∘ₗ hX₂.signedMorseBoundary 𝔬₂ hf₂ R)) ↔
      ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁)
        (r : criticalPoints 𝓘(ℝ, E) f₂),
        ((∑ᶠ x ∈ morseRootBrokenDiagonalSet f₁ f₂ (hX₀.morseYSlice hX₁ hX₂) hX₀ p q r,
            hX₀.morseRootBrokenDiagonalSign hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ p q r x -
          ∑ᶠ x ∈ morseFirstLeafBrokenDiagonalSet f₀ f₂ (hX₀.morseYSlice hX₁ hX₂) hX₁ p q r,
            hX₀.morseFirstLeafBrokenDiagonalSign hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ p q r x -
          (-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f₁ q *
            ∑ᶠ x ∈ morseSecondLeafBrokenDiagonalSet f₀ f₁ (hX₀.morseYSlice hX₁ hX₂) hX₂ p q r,
              hX₀.morseSecondLeafBrokenDiagonalSign hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ p q r x : ℤ) : R) = 0 :=
  (signedMorseCupProduct_comp_signedMorseBoundary_eq_iff_signedMorseDiagonalMap_comp_eq hf₁ hf₂
    hf₀).trans (signedMorseDiagonalMap_comp_signedMorseBoundary_eq_iff h₀ hf₀ h₁ hf₁ h₂ hf₂ hS)

end CupProduct

end IsAdaptedPseudoGradient

end TauCeti
