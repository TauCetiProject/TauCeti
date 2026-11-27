/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Diagonal.Signed
import TauCeti.LinearAlgebra.DirectSum.Finsupp

/-!
# The integral Morse cup product

Let `f₀`, `f₁` and `f₂` be Morse functions on a compact boundaryless manifold `M`, with
pseudo-gradients `X₀`, `X₁` and `X₂` adapted to them and orientation data `𝔬₀`, `𝔬₁` and `𝔬₂` of
their unstable manifolds. The integral Morse diagonal
`Δ = TauCeti.IsAdaptedPseudoGradient.signedMorseDiagonalMap` counts the Y-shaped flow lines from a
critical point `p` of `f₀` to critical points `q` of `f₁` and `r` of `f₂` with signs. This file
dualizes it into the **integral Morse cup product**
(`TauCeti.IsAdaptedPseudoGradient.signedMorseCupProduct`): for a commutative ring `R`, the product
of a linear form `a` on the Morse chains of `f₁` and a linear form `b` on those of `f₂`, both with
coefficients in `R`, is the linear form

`a ∪ b = μ ∘ (a ⊗ b) ∘ Δ`

on the Morse chains of `f₀`, for the multiplication `μ` of `R`. Its value at `p` is the sum, over
the pairs `(q, r)` with `ind q + ind r = ind p`, of the signed count of the Y-slice from `p` to `q`
and `r` times `a q * b r` (`signedMorseCupProduct_apply_single`). It is `R`-bilinear and of degree
zero: if `a` has degree `k` and `b` has degree `l`, that is, they vanish on the critical points of
index other than `k` and `l`, then `a ∪ b` vanishes on the critical points of index other than
`k + l` (`signedMorseCupProduct_apply_single_eq_zero`).

**Orientations and coefficients.** Reversing the orientations at the critical points of sets
`S₀`, `S₁` and `S₂` changes the cup product by the involutions `Finsupp.signReversal`
(`signedMorseCupProduct_reverse`), as it does the diagonal. With coefficients in `ZMod 2`, on
finite transversal Y-slices, it is the mod-two cup product `TauCeti.morseCupProduct` of the
Y-slices, whatever the orientations (`signedMorseCupProduct_zmod_two`).

**The graded Leibniz rule.** The Morse coboundary of a linear form is `δa = a ∘ ∂`, for the integral
Morse boundary `∂ = TauCeti.IsAdaptedPseudoGradient.signedMorseBoundary`. The tensor product of the
Morse complexes of `f₁` and `f₂` carries the Koszul differential `∂₁ ⊗ 1 + σ₁ ⊗ ∂₂`, where `σ₁`
multiplies a critical point `q` of `f₁` by `(-1) ^ ind q` (`Finsupp.signEquiv`), as for the Morse
complex of a product (`morseChainProdEquiv_comp_signedMorseBoundary` in the namespace
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`). The cup product satisfies

`δ(a ∪ b) = δa ∪ b + (a ∘ σ₁) ∪ δb`

for all linear forms `a` and `b` exactly when the diagonal is a chain map for this differential,
`Δ ∘ ∂₀ = (∂₁ ⊗ 1 + σ₁ ⊗ ∂₂) ∘ Δ`
(`signedMorseCupProduct_comp_signedMorseBoundary_eq_iff_signedMorseDiagonalMap_comp_eq`).
For `a` of degree `k`, `a ∘ σ₁` is `(-1) ^ k a` (`LinearMap.comp_signEquiv_eq_smul`), so this is
the graded Leibniz rule

`δ(a ∪ b) = δa ∪ b + (-1) ^ k a ∪ δb`

(`signedMorseCupProduct_comp_signedMorseBoundary_of_degree`). Over `ZMod 2` the sign disappears and
the criterion has the form of the one for the mod-two cup product,
`TauCeti.morseCupProduct_comp_morseBoundary_eq_iff_morseDiagonalMap_comp_morseBoundary_eq`.

**Cohomology.** When the diagonal is a chain map, the cup product of two cocycles is a cocycle
(`signedMorseCupProduct_comp_signedMorseBoundary_eq_zero`), and the cup product of a cocycle and a
coboundary, in either order, is a coboundary
(`signedMorseCupProduct_comp_signedMorseBoundary_left`,
`signedMorseCupProduct_comp_signedMorseBoundary_right`). These are the identities by which the cup
product descends to Morse cohomology; the induced product on cohomology is not built here.

That the integral diagonal is a chain map, which needs the oriented ends of the one-dimensional
spaces of Y-flow lines, is not proved here.

## Main definitions

* `TauCeti.IsAdaptedPseudoGradient.signedMorseCupProduct`: the integral Morse cup product.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `signedMorseCupProduct_apply`, `signedMorseCupProduct_apply_single`: its values.
* `signedMorseCupProduct_apply_single_eq_zero`: it has degree zero.
* `signedMorseCupProduct_reverse`: change of orientations.
* `signedMorseCupProduct_zmod_two`: the mod-two reduction.
* `signedMorseCupProduct_comp_signedMorseBoundary_eq_iff_signedMorseDiagonalMap_comp_eq`:
  the Leibniz rule holds exactly when the diagonal is a chain map for the Koszul differential.
* `signedMorseCupProduct_comp_signedMorseBoundary_of_degree`: the graded Leibniz rule.
* `signedMorseCupProduct_comp_signedMorseBoundary_eq_zero`,
  `signedMorseCupProduct_comp_signedMorseBoundary_left`,
  `signedMorseCupProduct_comp_signedMorseBoundary_right`: cocycles and coboundaries.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (signed counts) and §3 (Morse cohomology).
* S. Mescher, *Perturbed gradient flow trees and A∞-algebra structures in Morse cohomology*,
  arXiv:1611.07916, §§1–5 and Appendix A (the cup product from Y-flow lines and its Leibniz rule).
-/

public section

open Function
open scoped ContDiff Manifold TensorProduct

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f₀ f₁ f₂ : M → ℝ} {X₀ X₁ X₂ : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

variable (hX₀ : IsAdaptedPseudoGradient f₀ X₀) (hX₁ : IsAdaptedPseudoGradient f₁ X₁)
  (hX₂ : IsAdaptedPseudoGradient f₂ X₂) (𝔬₀ : MorseOrientation f₀ X₀)
  (𝔬₁ : MorseOrientation f₁ X₁) (𝔬₂ : MorseOrientation f₂ X₂)
  (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (hf₂ : IsMorse 𝓘(ℝ, E) f₂)

/-! ### The cup product -/

section Definition

variable (R : Type*) [CommRing R]

/-- **The integral Morse cup product** with coefficients in a commutative ring `R`: the product of
a linear form `a` on the Morse chains of `f₁` and a linear form `b` on those of `f₂` is the linear
form `a ∪ b = μ ∘ (a ⊗ b) ∘ Δ` on the Morse chains of `f₀`, for the integral Morse diagonal `Δ`
(`TauCeti.IsAdaptedPseudoGradient.signedMorseDiagonalMap`) and the multiplication `μ` of `R`. Its
value at a critical point `p` is the sum, over the pairs `(q, r)` with `ind q + ind r = ind p`, of
the signed count of the Y-slice from `p` to `q` and `r` times `a q * b r`
(`TauCeti.IsAdaptedPseudoGradient.signedMorseCupProduct_apply_single`). It is bilinear in `a` and
`b`. -/
noncomputable def signedMorseCupProduct :
    ((criticalPoints 𝓘(ℝ, E) f₁ →₀ R) →ₗ[R] R) →ₗ[R]
      ((criticalPoints 𝓘(ℝ, E) f₂ →₀ R) →ₗ[R] R) →ₗ[R]
        ((criticalPoints 𝓘(ℝ, E) f₀ →₀ R) →ₗ[R] R) :=
  LinearMap.mk₂ R
    (fun a b ↦ LinearMap.mul' R R ∘ₗ TensorProduct.map a b ∘ₗ
      hX₀.signedMorseDiagonalMap hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R)
    (fun a a' b ↦ by rw [TensorProduct.map_add_left, LinearMap.add_comp, LinearMap.comp_add])
    (fun c a b ↦ by rw [TensorProduct.map_smul_left, LinearMap.smul_comp, LinearMap.comp_smul])
    (fun a b b' ↦ by rw [TensorProduct.map_add_right, LinearMap.add_comp, LinearMap.comp_add])
    (fun c a b ↦ by rw [TensorProduct.map_smul_right, LinearMap.smul_comp, LinearMap.comp_smul])

end Definition

variable {hX₀ hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂} {R : Type*} [CommRing R]

/-- The cup product `a ∪ b` is `μ ∘ (a ⊗ b) ∘ Δ`. -/
theorem signedMorseCupProduct_apply (a : (criticalPoints 𝓘(ℝ, E) f₁ →₀ R) →ₗ[R] R)
    (b : (criticalPoints 𝓘(ℝ, E) f₂ →₀ R) →ₗ[R] R) :
    hX₀.signedMorseCupProduct hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R a b =
      LinearMap.mul' R R ∘ₗ TensorProduct.map a b ∘ₗ
        hX₀.signedMorseDiagonalMap hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R :=
  (rfl)

/-- **The cup product on a critical point.** The value of `a ∪ b` at a critical point `p` of `f₀`
is the sum, over the critical points `q` of `f₁` and `r` of `f₂`, of the coefficient
`signedMorseDiagonalCoeff`, the signed count of the Y-slice when `ind p = ind q + ind r` and `0`
otherwise, times `a q * b r`. -/
theorem signedMorseCupProduct_apply_single [Fintype (criticalPoints 𝓘(ℝ, E) f₁)]
    [Fintype (criticalPoints 𝓘(ℝ, E) f₂)] (a : (criticalPoints 𝓘(ℝ, E) f₁ →₀ R) →ₗ[R] R)
    (b : (criticalPoints 𝓘(ℝ, E) f₂ →₀ R) →ₗ[R] R) (p : criticalPoints 𝓘(ℝ, E) f₀) :
    hX₀.signedMorseCupProduct hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R a b (Finsupp.single p 1) =
      ∑ x : criticalPoints 𝓘(ℝ, E) f₁ × criticalPoints 𝓘(ℝ, E) f₂,
        (hX₀.signedMorseDiagonalCoeff hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ p x.1 x.2 : R) *
          (a (Finsupp.single x.1 1) * b (Finsupp.single x.2 1)) := by
  rw [signedMorseCupProduct_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.mul'_map_apply_eq_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [finsuppTensorFinsupp'_signedMorseDiagonalMap_single_apply, one_mul]

/-- **The cup product has degree zero.** If the linear form `a` vanishes on the critical points of
`f₁` of index other than `k`, and `b` on those of `f₂` of index other than `l`, then `a ∪ b`
vanishes on the critical points of `f₀` of index other than `k + l`. -/
theorem signedMorseCupProduct_apply_single_eq_zero {k l : ℕ}
    {a : (criticalPoints 𝓘(ℝ, E) f₁ →₀ R) →ₗ[R] R} {b : (criticalPoints 𝓘(ℝ, E) f₂ →₀ R) →ₗ[R] R}
    (ha : ∀ q : criticalPoints 𝓘(ℝ, E) f₁, manifoldMorseIndex 𝓘(ℝ, E) f₁ q ≠ k →
      a (Finsupp.single q 1) = 0)
    (hb : ∀ r : criticalPoints 𝓘(ℝ, E) f₂, manifoldMorseIndex 𝓘(ℝ, E) f₂ r ≠ l →
      b (Finsupp.single r 1) = 0)
    {p : criticalPoints 𝓘(ℝ, E) f₀} (hp : manifoldMorseIndex 𝓘(ℝ, E) f₀ p ≠ k + l) :
    hX₀.signedMorseCupProduct hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R a b (Finsupp.single p 1) = 0 := by
  have := hf₁.finite_criticalPoints.to_subtype
  have := hf₂.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f₁)
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f₂)
  rw [signedMorseCupProduct_apply_single]
  refine Finset.sum_eq_zero fun x _ ↦ ?_
  -- A term survives only if `ind q = k`, `ind r = l` and `ind p = ind q + ind r`.
  by_cases hq : manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 = k
  · by_cases hr : manifoldMorseIndex 𝓘(ℝ, E) f₂ x.2 = l
    · rw [signedMorseDiagonalCoeff_eq_zero_of_manifoldMorseIndex_ne (by rwa [hq, hr]),
        Int.cast_zero, zero_mul]
    · rw [hb _ hr, mul_zero, mul_zero]
  · rw [ha _ hq, zero_mul, mul_zero]

/-- **Reversing orientations changes the cup product by sign reversals.** For the orientations
reversed at the critical points of `S₀`, `S₁` and `S₂`, the cup product of `a` and `b` is the cup
product, for the original orientations, of `a` and `b` composed with the involutions
`Finsupp.signReversal` on `S₁` and `S₂`, composed with the involution on `S₀`. -/
theorem signedMorseCupProduct_reverse (S₀ : Set (criticalPoints 𝓘(ℝ, E) f₀))
    [DecidablePred (· ∈ S₀)] (S₁ : Set (criticalPoints 𝓘(ℝ, E) f₁)) [DecidablePred (· ∈ S₁)]
    (S₂ : Set (criticalPoints 𝓘(ℝ, E) f₂)) [DecidablePred (· ∈ S₂)]
    (a : (criticalPoints 𝓘(ℝ, E) f₁ →₀ R) →ₗ[R] R)
    (b : (criticalPoints 𝓘(ℝ, E) f₂ →₀ R) →ₗ[R] R) :
    hX₀.signedMorseCupProduct hX₁ hX₂ (𝔬₀.reverse S₀) (𝔬₁.reverse S₁) (𝔬₂.reverse S₂) hf₁ hf₂ R
        a b =
      hX₀.signedMorseCupProduct hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R
          (a ∘ₗ (Finsupp.signReversal R S₁).toLinearMap)
          (b ∘ₗ (Finsupp.signReversal R S₂).toLinearMap) ∘ₗ
        (Finsupp.signReversal R S₀).toLinearMap := by
  rw [signedMorseCupProduct_apply, signedMorseCupProduct_apply, signedMorseDiagonalMap_reverse,
    TensorProduct.map_comp]
  simp only [LinearMap.comp_assoc]

/-- **The integral cup product modulo two is the mod-two cup product of the Y-slices.** If every
Y-slice `W^u_{X₀}(p) ∩ W^s_{X₁}(q) ∩ W^s_{X₂}(r)` with `ind p = ind q + ind r` is finite, with an
isomorphism as comparison map at each of its points, then the integral cup product with
coefficients in `ZMod 2` is the mod-two cup product `TauCeti.morseCupProduct` of the Y-slices,
whatever the orientations. -/
theorem signedMorseCupProduct_zmod_two
    (hfin : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁)
      (r : criticalPoints 𝓘(ℝ, E) f₂), manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
        manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r →
      (hX₀.morseYSlice hX₁ hX₂ p q r).Finite)
    (hbij : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁)
      (r : criticalPoints 𝓘(ℝ, E) f₂), manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
        manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r →
      ∀ y ∈ hX₀.morseYSlice hX₁ hX₂ p q r,
        Bijective (hX₀.morseYComparison hX₁ hX₂ (𝔬₀.chart p) (𝔬₁.chart q) (𝔬₂.chart r) y)) :
    hX₀.signedMorseCupProduct hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ (ZMod 2) =
      morseCupProduct f₀ hf₁ hf₂ (hX₀.morseYSlice hX₁ hX₂) := by
  refine LinearMap.ext₂ fun a b ↦ ?_
  rw [signedMorseCupProduct_apply, morseCupProduct_apply, signedMorseDiagonalMap_zmod_two hf₁ hf₂
    hfin hbij]

/-! ### The graded Leibniz rule -/

section Leibniz

variable (hf₀ : IsMorse 𝓘(ℝ, E) f₀)

/-- **The cup product satisfies the Leibniz rule exactly when the diagonal is a chain map.** For
the integral Morse boundaries `∂₀`, `∂₁` and `∂₂` and the parity sign `σ₁`, which multiplies a
critical point `q` of `f₁` by `(-1) ^ ind q`, the cup product satisfies
`δ(a ∪ b) = δa ∪ b + (a ∘ σ₁) ∪ δb` for all linear forms `a` and `b` on the Morse chains, where
`δa = a ∘ ∂` is the Morse coboundary, exactly when the integral Morse diagonal is a chain map for
the Koszul differential of the tensor product: `Δ ∘ ∂₀ = (∂₁ ⊗ 1 + σ₁ ⊗ ∂₂) ∘ Δ`. -/
theorem signedMorseCupProduct_comp_signedMorseBoundary_eq_iff_signedMorseDiagonalMap_comp_eq :
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
      hX₀.signedMorseDiagonalMap hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R ∘ₗ
          hX₀.signedMorseBoundary 𝔬₀ hf₀ R =
        ((hX₁.signedMorseBoundary 𝔬₁ hf₁ R).rTensor _ +
            TensorProduct.map
              (Finsupp.signEquiv (A := R) R fun q : criticalPoints 𝓘(ℝ, E) f₁ ↦
                (-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f₁ q).toLinearMap
              (hX₂.signedMorseBoundary 𝔬₂ hf₂ R)) ∘ₗ
          hX₀.signedMorseDiagonalMap hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R := by
  simpa only [signedMorseCupProduct_apply, LinearMap.comp_assoc] using
    LinearMap.mul'_comp_map_comp_comp_eq_iff_comp_eq_rTensor_add_map_comp _ _ _ _ _

variable {hf₀}
  (hΔ : hX₀.signedMorseDiagonalMap hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R ∘ₗ
      hX₀.signedMorseBoundary 𝔬₀ hf₀ R =
    ((hX₁.signedMorseBoundary 𝔬₁ hf₁ R).rTensor _ +
        TensorProduct.map
          (Finsupp.signEquiv (A := R) R fun q : criticalPoints 𝓘(ℝ, E) f₁ ↦
            (-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f₁ q).toLinearMap
          (hX₂.signedMorseBoundary 𝔬₂ hf₂ R)) ∘ₗ
      hX₀.signedMorseDiagonalMap hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R)
include hΔ

/-- **The graded Leibniz rule.** When the integral Morse diagonal is a chain map for the Koszul
differential, the cup product of a linear form `a` of degree `k`, vanishing on the critical points
of `f₁` of index other than `k`, with any linear form `b` satisfies
`δ(a ∪ b) = δa ∪ b + (-1) ^ k a ∪ δb`, where `δa = a ∘ ∂` is the Morse coboundary. -/
theorem signedMorseCupProduct_comp_signedMorseBoundary_of_degree {k : ℕ}
    {a : (criticalPoints 𝓘(ℝ, E) f₁ →₀ R) →ₗ[R] R}
    (ha : ∀ q : criticalPoints 𝓘(ℝ, E) f₁, manifoldMorseIndex 𝓘(ℝ, E) f₁ q ≠ k →
      a (Finsupp.single q 1) = 0)
    (b : (criticalPoints 𝓘(ℝ, E) f₂ →₀ R) →ₗ[R] R) :
    hX₀.signedMorseCupProduct hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R a b ∘ₗ
        hX₀.signedMorseBoundary 𝔬₀ hf₀ R =
      hX₀.signedMorseCupProduct hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R
          (a ∘ₗ hX₁.signedMorseBoundary 𝔬₁ hf₁ R) b +
        (-1 : ℤ) ^ k • hX₀.signedMorseCupProduct hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R a
          (b ∘ₗ hX₂.signedMorseBoundary 𝔬₂ hf₂ R) := by
  -- On the critical points where `a` does not vanish, the parity sign is `(-1) ^ k`.
  have hσ : a ∘ₗ (Finsupp.signEquiv (A := R) R fun q : criticalPoints 𝓘(ℝ, E) f₁ ↦
      (-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f₁ q).toLinearMap = (-1 : ℤ) ^ k • a := by
    refine (a.comp_signEquiv_eq_smul (u := (-1) ^ k) fun q hq c ↦ ?_).trans (by
      rw [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one])
    rw [← Finsupp.smul_single_one, map_smul, ha q fun hk ↦ hq (by rw [hk]), smul_zero]
  rw [(signedMorseCupProduct_comp_signedMorseBoundary_eq_iff_signedMorseDiagonalMap_comp_eq
    hf₁ hf₂ hf₀).2 hΔ a b, hσ,
    LinearMap.map_smul_of_tower, LinearMap.smul_apply]

/-- **The cup product of two cocycles is a cocycle.** When the integral Morse diagonal is a chain
map for the Koszul differential, if `δa = 0` and `δb = 0` then `δ(a ∪ b) = 0`. -/
theorem signedMorseCupProduct_comp_signedMorseBoundary_eq_zero
    {a : (criticalPoints 𝓘(ℝ, E) f₁ →₀ R) →ₗ[R] R} {b : (criticalPoints 𝓘(ℝ, E) f₂ →₀ R) →ₗ[R] R}
    (ha : a ∘ₗ hX₁.signedMorseBoundary 𝔬₁ hf₁ R = 0)
    (hb : b ∘ₗ hX₂.signedMorseBoundary 𝔬₂ hf₂ R = 0) :
    hX₀.signedMorseCupProduct hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R a b ∘ₗ
      hX₀.signedMorseBoundary 𝔬₀ hf₀ R = 0 := by
  rw [(signedMorseCupProduct_comp_signedMorseBoundary_eq_iff_signedMorseDiagonalMap_comp_eq
    hf₁ hf₂ hf₀).2 hΔ a b, ha, hb, map_zero, map_zero, LinearMap.zero_apply, add_zero]

/-- **The cup product of a coboundary and a cocycle is a coboundary.** When the integral Morse
diagonal is a chain map for the Koszul differential and `δb = 0`, the cup product `δa ∪ b` is the
coboundary `δ(a ∪ b)`. -/
theorem signedMorseCupProduct_comp_signedMorseBoundary_left
    (a : (criticalPoints 𝓘(ℝ, E) f₁ →₀ R) →ₗ[R] R) {b : (criticalPoints 𝓘(ℝ, E) f₂ →₀ R) →ₗ[R] R}
    (hb : b ∘ₗ hX₂.signedMorseBoundary 𝔬₂ hf₂ R = 0) :
    hX₀.signedMorseCupProduct hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R
        (a ∘ₗ hX₁.signedMorseBoundary 𝔬₁ hf₁ R) b =
      hX₀.signedMorseCupProduct hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R a b ∘ₗ
        hX₀.signedMorseBoundary 𝔬₀ hf₀ R := by
  rw [(signedMorseCupProduct_comp_signedMorseBoundary_eq_iff_signedMorseDiagonalMap_comp_eq
    hf₁ hf₂ hf₀).2 hΔ a b, hb, map_zero, add_zero]

/-- **The cup product of a cocycle and a coboundary is a coboundary.** When the integral Morse
diagonal is a chain map for the Koszul differential and `δa = 0`, the cup product `a ∪ δb` is the
coboundary `δ((a ∘ σ₁) ∪ b)`, where the parity sign `σ₁` multiplies a critical point `q` of `f₁`
by `(-1) ^ ind q`. The form `a ∘ σ₁` is again a cocycle, since the boundary anticommutes with the
parity sign (`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundary_comp_signEquiv`). -/
theorem signedMorseCupProduct_comp_signedMorseBoundary_right
    {a : (criticalPoints 𝓘(ℝ, E) f₁ →₀ R) →ₗ[R] R} (ha : a ∘ₗ hX₁.signedMorseBoundary 𝔬₁ hf₁ R = 0)
    (b : (criticalPoints 𝓘(ℝ, E) f₂ →₀ R) →ₗ[R] R) :
    hX₀.signedMorseCupProduct hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R a
        (b ∘ₗ hX₂.signedMorseBoundary 𝔬₂ hf₂ R) =
      hX₀.signedMorseCupProduct hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R
          (a ∘ₗ (Finsupp.signEquiv (A := R) R fun q : criticalPoints 𝓘(ℝ, E) f₁ ↦
            (-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f₁ q).toLinearMap) b ∘ₗ
        hX₀.signedMorseBoundary 𝔬₀ hf₀ R := by
  set σ := (Finsupp.signEquiv (A := R) R fun q : criticalPoints 𝓘(ℝ, E) f₁ ↦
    (-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f₁ q).toLinearMap
  -- The form `a ∘ σ` is a cocycle, and `σ` is an involution.
  have hσa : (a ∘ₗ σ) ∘ₗ hX₁.signedMorseBoundary 𝔬₁ hf₁ R = 0 := by
    have h : σ ∘ₗ hX₁.signedMorseBoundary 𝔬₁ hf₁ R = -(hX₁.signedMorseBoundary 𝔬₁ hf₁ R ∘ₗ σ) :=
      by rw [signedMorseBoundary_comp_signEquiv, neg_neg]
    rw [LinearMap.comp_assoc, h, LinearMap.comp_neg, ← LinearMap.comp_assoc, ha,
      LinearMap.zero_comp, neg_zero]
  have hσσ : (a ∘ₗ σ) ∘ₗ σ = a :=
    LinearMap.ext fun c ↦ congrArg a (Finsupp.signEquiv_signEquiv c)
  rw [(signedMorseCupProduct_comp_signedMorseBoundary_eq_iff_signedMorseDiagonalMap_comp_eq
    hf₁ hf₂ hf₀).2 hΔ (a ∘ₗ σ) b, hσa, hσσ, map_zero, LinearMap.zero_apply, zero_add]

end Leibniz

end IsAdaptedPseudoGradient

end TauCeti
