/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Diagonal.Basic
public import TauCeti.Geometry.Manifold.Morse.Boundary.Pair.Sign
public import TauCeti.LinearAlgebra.Finsupp.SignReversal
public import TauCeti.LinearAlgebra.Orientation.Prod
import TauCeti.Data.Set.Card
import TauCeti.LinearAlgebra.DirectSum.Finsupp
import TauCeti.LinearAlgebra.Finsupp.IntMatrixMap

/-!
# Signs of Y-flow lines and the integral Morse diagonal

Let `f₀`, `f₁` and `f₂` be Morse functions on a compact boundaryless manifold `M`, with
pseudo-gradients `X₀`, `X₁` and `X₂` adapted to them. The mod-two Morse diagonal
(`TauCeti.morseDiagonalMap`) counts the points of the Y-slices
`W^u_{X₀}(p) ∩ W^s_{X₁}(q) ∩ W^s_{X₂}(r)` (`TauCeti.IsAdaptedPseudoGradient.morseYSlice`), the
vertices of the Y-shaped flow lines from a critical point `p` of `f₀` to critical points `q` of
`f₁` and `r` of `f₂`. This file counts them with signs, which is what the Morse diagonal and the
cup product over `ℤ` need.

The signs come from orientations of the unstable manifolds at the three critical points, as for the
integral Morse boundary and the signed pair counts
(`TauCeti.IsAdaptedPseudoGradient.pairSign`). Fix Morse charts `φp`, `φq` and `φr` at `p`, `q` and
`r`, in which the pseudo-gradients are linear, and orientations `o₀`, `o₁` and `o₂` of their spaces
`Vp`, `Vq` and `Vr` of coordinates of negative weight. At a point `y` of the Y-slice:

* the unstable frame `Fp = hX₀.unstableFrame φp y : Vp → T_y M` carries `o₀` to the tangent space
  of `W^u_{X₀}(p)` at `y`;
* the normal coordinates `Nq = hX₁.stableNormal φq y` and `Nr = hX₂.stableNormal φr y` carry the
  normal spaces of `W^s_{X₁}(q)` and of `W^s_{X₂}(r)` at `y` onto `Vq` and `Vr`, cooriented by
  `o₁` and `o₂`.

The **comparison map** `v ↦ (Nq (Fp v), Nr (Fp v))` from `Vp` to `Vq × Vr`
(`TauCeti.IsAdaptedPseudoGradient.morseYComparison`) pairs the comparison maps
`TauCeti.IsAdaptedPseudoGradient.pairComparison` of `(X₀, X₁)` and of `(X₀, X₂)`. It is an
isomorphism when the tangent space of `W^u_{X₀}(p)` at `y` projects isomorphically onto the sum of
the normal spaces of the two stable manifolds, which is what a transversal Y-slice with
`ind p = ind q + ind r` provides. The **sign** of `y`
(`TauCeti.IsAdaptedPseudoGradient.morseYSign`) is then `+1` if the comparison map carries `o₀` to
the ordered product orientation `o₁ × o₂` (`Orientation.prod`) and `-1` otherwise: `y` counts
positively when a positive basis of the tangent space of `W^u_{X₀}(p)` projects to a positive basis
of the ordered sum of the normal spaces of `W^s_{X₁}(q)` and of `W^s_{X₂}(r)`. Where the comparison
map is not an isomorphism, the sign is `0`. The **signed count**
`TauCeti.IsAdaptedPseudoGradient.signedMorseYCount` sums the signs over the Y-slice.

The signs have the expected properties:

* where the comparison map is an isomorphism the sign is `±1`
  (`TauCeti.IsAdaptedPseudoGradient.morseYSign_eq_one_or_eq_neg_one_of_bijective`), so on a finite
  Y-slice cut out transversally the signed count reduces modulo two to the number of points
  (`TauCeti.IsAdaptedPseudoGradient.intCast_signedMorseYCount`);
* reversing any of the three orientations reverses every sign
  (`TauCeti.IsAdaptedPseudoGradient.morseYSign_neg_root`,
  `TauCeti.IsAdaptedPseudoGradient.morseYSign_neg_firstLeaf`,
  `TauCeti.IsAdaptedPseudoGradient.morseYSign_neg_secondLeaf`);
* the signs do not depend on the Morse charts, only on the orientations of the unstable manifolds
  which the charts induce (`TauCeti.IsAdaptedPseudoGradient.morseYSign_map_negativeChange`).

Given orientation data `𝔬₀`, `𝔬₁` and `𝔬₂` (`TauCeti.MorseOrientation`), the signed counts are
the coefficients (`TauCeti.IsAdaptedPseudoGradient.signedMorseDiagonalCoeff`) of the **integral
Morse diagonal** (`TauCeti.IsAdaptedPseudoGradient.signedMorseDiagonalMap`), the `R`-linear map,
for any commutative ring `R`, from the free `R`-module on the critical points of `f₀` to the tensor
product of those on the critical points of `f₁` and `f₂` sending `p` to the sum of the tensors
`q ⊗ r` with `ind q + ind r = ind p`, each weighted by the signed count of the Y-slice. It
preserves the total Morse index, reversing orientations at the critical points of sets `S₀`, `S₁`
and `S₂` conjugates it by the involutions `Finsupp.signReversal`
(`TauCeti.IsAdaptedPseudoGradient.signedMorseDiagonalMap_reverse`), and with coefficients in
`ZMod 2` it is the mod-two Morse diagonal of the Y-slices when those with
`ind p = ind q + ind r` are finite, with an isomorphism as comparison map at each of their points
(`TauCeti.IsAdaptedPseudoGradient.signedMorseDiagonalMap_zmod_two`).

That the integral Morse diagonal is a chain map for the Koszul-signed tensor differential, which
needs the oriented ends of the one-dimensional spaces of Y-flow lines, is not proved here.

## Main definitions

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `morseYComparison`: the comparison map `Vp → Vq × Vr` at a point of the Y-slice.
* `morseYSign`: the sign of such a point.
* `signedMorseYCount`: the number of points of the Y-slice counted with signs.
* `signedMorseDiagonalCoeff`: the signed count, or `0` unless `ind p = ind q + ind r`.
* `signedMorseDiagonalMap`: the integral Morse diagonal.

## Main results

* `morseYSign_eq_one_or_eq_neg_one_of_bijective`, `intCast_signedMorseYCount`: the signs are
  `±1` where the comparison map is an isomorphism, and the signed count of a finite transversal
  Y-slice reduces modulo two to its number of points.
* `exists_morseYSign_eq_and_map_eq`, `morseYSign_eq_of_map_eq`: where the comparison map is an
  isomorphism, the sign is the unit by which it scales the product orientation.
* `morseYSign_neg_root`, `morseYSign_neg_firstLeaf`, `morseYSign_neg_secondLeaf`: reversing an
  orientation reverses the signs.
* `morseYSign_map_negativeChange`, `signedMorseYCount_map_negativeChange`: the signs and the
  signed count do not depend on the Morse charts.
* `finsuppTensorFinsupp'_signedMorseDiagonalMap_apply`: the coefficients of the integral Morse
  diagonal.
* `signedMorseDiagonalMap_reverse`: change of orientations.
* `signedMorseDiagonalMap_zmod_two`: the mod-two reduction.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations of the descending manifolds and signed
  counts).
* S. Mescher, *Perturbed gradient flow trees and A∞-algebra structures in Morse cohomology*,
  arXiv:1611.07916, §§1–5 and Appendix A (Y-flow lines and their orientations by the unstable
  orientation of the root and the coorientations of the leaves).
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

/-! ### The comparison map and the sign of a point -/

section Sign

variable (hX₀ : IsAdaptedPseudoGradient f₀ X₀) (hX₁ : IsAdaptedPseudoGradient f₁ X₁)
  (hX₂ : IsAdaptedPseudoGradient f₂ X₂) {p q r : M}
  (φp : MorseChart E f₀ p) (φq : MorseChart E f₁ q) (φr : MorseChart E f₂ r)

/-- The **comparison map** of a Y-flow line at its vertex `y`: it sends `v` in the space of
coordinates of negative weight of the Morse chart `φp` of `f₀` to the pair of normal coordinates of
`W^s_{X₁}(q)` and of `W^s_{X₂}(r)`, read in the Morse charts `φq` of `f₁` and `φr` of `f₂`, of the
vector of the unstable frame of `W^u_{X₀}(p)` on `v`. Its two components are the comparison maps
`TauCeti.IsAdaptedPseudoGradient.pairComparison` of the pairs `(X₀, X₁)` and `(X₀, X₂)`. -/
noncomputable def morseYComparison (y : M) :
    ({i // φp.weight i < 0} → ℝ) →L[ℝ]
      ({i // φq.weight i < 0} → ℝ) × ({i // φr.weight i < 0} → ℝ) :=
  (hX₀.pairComparison hX₁ φp φq y).prod (hX₀.pairComparison hX₂ φp φr y)

/-- The comparison map is the pair of normal coordinates of the unstable frame. -/
@[simp]
theorem morseYComparison_apply (y : M) (v : {i // φp.weight i < 0} → ℝ) :
    hX₀.morseYComparison hX₁ hX₂ φp φq φr y v =
      (hX₁.stableNormal φq y (hX₀.unstableFrame φp y v),
        hX₂.stableNormal φr y (hX₀.unstableFrame φp y v)) := by
  rw [morseYComparison, ContinuousLinearMap.prod_apply, pairComparison_apply, pairComparison_apply]

/-- The **sign of a point** `y` of the Y-slice `W^u_{X₀}(p) ∩ W^s_{X₁}(q) ∩ W^s_{X₂}(r)`, for
orientations `o₀`, `o₁` and `o₂` of the unstable manifolds of `X₀` at `p`, of `X₁` at `q` and of
`X₂` at `r`, with `ind p = ind q + ind r`: the sign `Orientation.linearMapSign` of the comparison
map for `o₀` and the ordered product orientation `o₁ × o₂`, that is, `1` when it is an isomorphism
carrying `o₀` to `o₁ × o₂`, `-1` when it is an isomorphism reversing them, and `0` when it is not an
isomorphism. -/
noncomputable def morseYSign
    (o₀ : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₀ p)))
    (o₁ : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₁ q)))
    (o₂ : Orientation ℝ ({i // φr.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₂ r)))
    (hpqr : manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r) (y : M) : ℤ :=
  o₀.linearMapSign
    (Orientation.reindex ℝ _ (finCongr hpqr.symm)
      (o₁.prod o₂ φq.finrank_negativeWeight_fun φr.finrank_negativeWeight_fun))
    (hX₀.morseYComparison hX₁ hX₂ φp φq φr y).toLinearMap

/-- The sign of a point is the sign of the comparison map, with the product orientation of the
leaves reindexed by the index of the root. -/
theorem morseYSign_def
    (o₀ : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₀ p)))
    (o₁ : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₁ q)))
    (o₂ : Orientation ℝ ({i // φr.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₂ r)))
    (hpqr : manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r) (y : M) :
    hX₀.morseYSign hX₁ hX₂ φp φq φr o₀ o₁ o₂ hpqr y =
      o₀.linearMapSign
        (Orientation.reindex ℝ _ (finCongr hpqr.symm)
          (o₁.prod o₂ φq.finrank_negativeWeight_fun φr.finrank_negativeWeight_fun))
        (hX₀.morseYComparison hX₁ hX₂ φp φq φr y).toLinearMap :=
  (rfl)

/-- The number of points of the Y-slice `W^u_{X₀}(p) ∩ W^s_{X₁}(q) ∩ W^s_{X₂}(r)` counted with
their signs. When infinitely many points of the Y-slice have nonzero sign, this is the junk
value `0`. -/
noncomputable def signedMorseYCount
    (o₀ : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₀ p)))
    (o₁ : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₁ q)))
    (o₂ : Orientation ℝ ({i // φr.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₂ r)))
    (hpqr : manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r) : ℤ :=
  ∑ᶠ y ∈ hX₀.morseYSlice hX₁ hX₂ p q r, hX₀.morseYSign hX₁ hX₂ φp φq φr o₀ o₁ o₂ hpqr y

/-- The defining formula of the signed count. -/
theorem signedMorseYCount_def
    (o₀ : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₀ p)))
    (o₁ : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₁ q)))
    (o₂ : Orientation ℝ ({i // φr.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₂ r)))
    (hpqr : manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r) :
    hX₀.signedMorseYCount hX₁ hX₂ φp φq φr o₀ o₁ o₂ hpqr =
      ∑ᶠ y ∈ hX₀.morseYSlice hX₁ hX₂ p q r, hX₀.morseYSign hX₁ hX₂ φp φq φr o₀ o₁ o₂ hpqr y :=
  (rfl)

variable {hX₀ hX₁ hX₂ φp φq φr}
  {o₀ : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₀ p))}
  {o₁ : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₁ q))}
  {o₂ : Orientation ℝ ({i // φr.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₂ r))}
  {hpqr : manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
    manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r}

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- The index of the root is the dimension of the ordered sum of the coordinates of negative weight
of the two leaves. -/
private theorem card_fin_eq_finrank_prod (hpqr : manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r) :
    Fintype.card (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₀ p)) =
      Module.finrank ℝ (({i // φq.weight i < 0} → ℝ) × ({i // φr.weight i < 0} → ℝ)) := by
  rw [Fintype.card_fin, Module.finrank_prod, φq.finrank_negativeWeight_fun,
    φr.finrank_negativeWeight_fun, hpqr]

open scoped Classical in
/-- Where the comparison map is an isomorphism, the sign compares the orientation it carries `o₀`
to with the product orientation `o₁ × o₂`. -/
theorem morseYSign_of_bijective {y : M}
    (h : Bijective (hX₀.morseYComparison hX₁ hX₂ φp φq φr y)) :
    hX₀.morseYSign hX₁ hX₂ φp φq φr o₀ o₁ o₂ hpqr y =
      if Orientation.map _
          (LinearEquiv.ofBijective (hX₀.morseYComparison hX₁ hX₂ φp φq φr y).toLinearMap h) o₀ =
          Orientation.reindex ℝ _ (finCongr hpqr.symm)
            (o₁.prod o₂ φq.finrank_negativeWeight_fun φr.finrank_negativeWeight_fun) then 1
      else -1 :=
  Orientation.linearMapSign_of_bijective h

/-- Where the comparison map is not an isomorphism, the sign is `0`. -/
theorem morseYSign_of_not_bijective {y : M}
    (h : ¬Bijective (hX₀.morseYComparison hX₁ hX₂ φp φq φr y)) :
    hX₀.morseYSign hX₁ hX₂ φp φq φr o₀ o₁ o₂ hpqr y = 0 :=
  Orientation.linearMapSign_of_not_bijective h

/-- **The sign of a point is `±1`** wherever the comparison map is an isomorphism. -/
theorem morseYSign_eq_one_or_eq_neg_one_of_bijective {y : M}
    (h : Bijective (hX₀.morseYComparison hX₁ hX₂ φp φq φr y)) :
    hX₀.morseYSign hX₁ hX₂ φp φq φr o₀ o₁ o₂ hpqr y = 1 ∨
      hX₀.morseYSign hX₁ hX₂ φp φq φr o₀ o₁ o₂ hpqr y = -1 :=
  Orientation.linearMapSign_eq_one_or_eq_neg_one_of_bijective h

/-- **The sign as a unit.** Where the comparison map is an isomorphism, it carries `o₀` to the
product orientation `o₁ × o₂`, reindexed, scaled by a unit sign `u`, and the sign of the point
is `u`. -/
theorem exists_morseYSign_eq_and_map_eq {y : M}
    (h : Bijective (hX₀.morseYComparison hX₁ hX₂ φp φq φr y)) :
    ∃ u : ℤˣ, hX₀.morseYSign hX₁ hX₂ φp φq φr o₀ o₁ o₂ hpqr y = u ∧
      Orientation.map _
          (LinearEquiv.ofBijective (hX₀.morseYComparison hX₁ hX₂ φp φq φr y).toLinearMap h) o₀ =
        Units.map (Int.castRingHom ℝ).toMonoidHom u •
          Orientation.reindex ℝ _ (finCongr hpqr.symm)
            (o₁.prod o₂ φq.finrank_negativeWeight_fun φr.finrank_negativeWeight_fun) :=
  Orientation.exists_linearMapSign_eq_and_map_eq (card_fin_eq_finrank_prod hpqr) h

/-- **Reading off the sign.** If a linear equivalence `L` agrees with the comparison map and
carries `o₀` to the product orientation `o₁ × o₂`, reindexed, scaled by a unit sign `u`, the sign
of the point is `u`. -/
theorem morseYSign_eq_of_map_eq {y : M}
    (L : ({i // φp.weight i < 0} → ℝ) ≃ₗ[ℝ]
      ({i // φq.weight i < 0} → ℝ) × ({i // φr.weight i < 0} → ℝ))
    (hL : ∀ v, L v = hX₀.morseYComparison hX₁ hX₂ φp φq φr y v) {u : ℤˣ}
    (hu : Orientation.map _ L o₀ =
      Units.map (Int.castRingHom ℝ).toMonoidHom u •
        Orientation.reindex ℝ _ (finCongr hpqr.symm)
          (o₁.prod o₂ φq.finrank_negativeWeight_fun φr.finrank_negativeWeight_fun)) :
    hX₀.morseYSign hX₁ hX₂ φp φq φr o₀ o₁ o₂ hpqr y = u :=
  Orientation.linearMapSign_eq_of_map_eq L hL hu

/-- **Reversing the orientation at the root reverses the sign.** -/
@[simp]
theorem morseYSign_neg_root (y : M) :
    hX₀.morseYSign hX₁ hX₂ φp φq φr (-o₀) o₁ o₂ hpqr y =
      -hX₀.morseYSign hX₁ hX₂ φp φq φr o₀ o₁ o₂ hpqr y :=
  Orientation.linearMapSign_neg_left (card_fin_eq_finrank_prod hpqr)

/-- **Reversing the orientation at the first leaf reverses the sign.** -/
@[simp]
theorem morseYSign_neg_firstLeaf (y : M) :
    hX₀.morseYSign hX₁ hX₂ φp φq φr o₀ (-o₁) o₂ hpqr y =
      -hX₀.morseYSign hX₁ hX₂ φp φq φr o₀ o₁ o₂ hpqr y := by
  rw [morseYSign_def, morseYSign_def, Orientation.prod_neg_left, Orientation.reindex_neg]
  exact Orientation.linearMapSign_neg_right (card_fin_eq_finrank_prod hpqr)

/-- **Reversing the orientation at the second leaf reverses the sign.** -/
@[simp]
theorem morseYSign_neg_secondLeaf (y : M) :
    hX₀.morseYSign hX₁ hX₂ φp φq φr o₀ o₁ (-o₂) hpqr y =
      -hX₀.morseYSign hX₁ hX₂ φp φq φr o₀ o₁ o₂ hpqr y := by
  rw [morseYSign_def, morseYSign_def, Orientation.prod_neg_right, Orientation.reindex_neg]
  exact Orientation.linearMapSign_neg_right (card_fin_eq_finrank_prod hpqr)

/-- Reversing the orientation at the root reverses the signed count. -/
@[simp]
theorem signedMorseYCount_neg_root :
    hX₀.signedMorseYCount hX₁ hX₂ φp φq φr (-o₀) o₁ o₂ hpqr =
      -hX₀.signedMorseYCount hX₁ hX₂ φp φq φr o₀ o₁ o₂ hpqr := by
  simp only [signedMorseYCount_def, morseYSign_neg_root, finsum_neg_distrib]

/-- Reversing the orientation at the first leaf reverses the signed count. -/
@[simp]
theorem signedMorseYCount_neg_firstLeaf :
    hX₀.signedMorseYCount hX₁ hX₂ φp φq φr o₀ (-o₁) o₂ hpqr =
      -hX₀.signedMorseYCount hX₁ hX₂ φp φq φr o₀ o₁ o₂ hpqr := by
  simp only [signedMorseYCount_def, morseYSign_neg_firstLeaf, finsum_neg_distrib]

/-- Reversing the orientation at the second leaf reverses the signed count. -/
@[simp]
theorem signedMorseYCount_neg_secondLeaf :
    hX₀.signedMorseYCount hX₁ hX₂ φp φq φr o₀ o₁ (-o₂) hpqr =
      -hX₀.signedMorseYCount hX₁ hX₂ φp φq φr o₀ o₁ o₂ hpqr := by
  simp only [signedMorseYCount_def, morseYSign_neg_secondLeaf, finsum_neg_distrib]

/-- **The signed count reduces to the number of points modulo two** on a finite Y-slice at each
of whose points the comparison map is an isomorphism, that is, on which the unstable manifold of
`p` meets the stable manifolds of `q` and `r` transversally. -/
theorem intCast_signedMorseYCount (hfin : (hX₀.morseYSlice hX₁ hX₂ p q r).Finite)
    (hbij : ∀ y ∈ hX₀.morseYSlice hX₁ hX₂ p q r,
      Bijective (hX₀.morseYComparison hX₁ hX₂ φp φq φr y)) :
    (hX₀.signedMorseYCount hX₁ hX₂ φp φq φr o₀ o₁ o₂ hpqr : ZMod 2) =
      ((hX₀.morseYSlice hX₁ hX₂ p q r).ncard : ZMod 2) := by
  rw [signedMorseYCount_def]
  exact intCast_finsum_mem_eq_ncard_of_eq_one_or_eq_neg_one hfin fun y hy ↦
    morseYSign_eq_one_or_eq_neg_one_of_bijective (hbij y hy)

end Sign

/-! ### Changing the Morse charts -/

section ChartChange

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  {hX₂ : IsAdaptedPseudoGradient f₂ X₂} {p q r : M}
  {φp φp' : MorseChart E f₀ p} {φq φq' : MorseChart E f₁ q} {φr φr' : MorseChart E f₂ r}
  (hφp : ∀ y ∈ φp.toChart.source,
    φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart y (X₀ y)) =
      fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
  (hφp' : ∀ y ∈ φp'.toChart.source,
    φp'.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp'.toChart y (X₀ y)) =
      fun i ↦ -(φp'.weight i * φp'.coord (φp'.toChart y) i))
  (hφq : ∀ y ∈ φq.toChart.source,
    φq.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart y (X₁ y)) =
      fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))
  (hφq' : ∀ y ∈ φq'.toChart.source,
    φq'.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq'.toChart y (X₁ y)) =
      fun i ↦ -(φq'.weight i * φq'.coord (φq'.toChart y) i))
  (hφr : ∀ y ∈ φr.toChart.source,
    φr.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φr.toChart y (X₂ y)) =
      fun i ↦ -(φr.weight i * φr.coord (φr.toChart y) i))
  (hφr' : ∀ y ∈ φr'.toChart.source,
    φr'.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φr'.toChart y (X₂ y)) =
      fun i ↦ -(φr'.weight i * φr'.coord (φr'.toChart y) i))
include hφp hφp' hφq hφq' hφr hφr'

/-- **The comparison map in other Morse charts.** At a point of the Y-slice, replacing the Morse
charts `φp`, `φq` and `φr` by `φp'`, `φq'` and `φr'` composes the comparison map with the changes
of negative coordinates at the root and, componentwise, at the two leaves. -/
theorem morseYComparison_negativeChange (hf₀ : IsMorse 𝓘(ℝ, E) f₀) {y : M}
    (hy : y ∈ hX₀.morseYSlice hX₁ hX₂ p q r) (v : {i // φp.weight i < 0} → ℝ) :
    hX₀.morseYComparison hX₁ hX₂ φp' φq' φr' y (φp.negativeChange φp' v) =
      (φq.negativeChange φq').prodCongr (φr.negativeChange φr')
        (hX₀.morseYComparison hX₁ hX₂ φp φq φr y v) := by
  obtain ⟨hp, hq, hr⟩ := (hX₀.mem_morseYSlice hX₁ hX₂).1 hy
  exact Prod.ext (pairComparison_negativeChange hφp hφp' hφq hφq' hf₀ ⟨hp, hq⟩ v)
    (pairComparison_negativeChange hφp hφp' hφr hφr' hf₀ ⟨hp, hr⟩ v)

/-- **The sign of a point does not depend on the Morse charts.** At a point of the Y-slice, the sign
for the orientations `o₀`, `o₁` and `o₂` in the charts `φp`, `φq` and `φr` is the sign in the charts
`φp'`, `φq'` and `φr'` for the orientations transported along the changes of negative
coordinates. -/
theorem morseYSign_map_negativeChange (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (o₀ : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₀ p)))
    (o₁ : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₁ q)))
    (o₂ : Orientation ℝ ({i // φr.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₂ r)))
    (hpqr : manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r) {y : M}
    (hy : y ∈ hX₀.morseYSlice hX₁ hX₂ p q r) :
    hX₀.morseYSign hX₁ hX₂ φp' φq' φr' (Orientation.map _ (φp.negativeChange φp') o₀)
        (Orientation.map _ (φq.negativeChange φq') o₁)
        (Orientation.map _ (φr.negativeChange φr') o₂) hpqr y =
      hX₀.morseYSign hX₁ hX₂ φp φq φr o₀ o₁ o₂ hpqr y := by
  rw [morseYSign_def, morseYSign_def, ← Orientation.map_prod, ← Orientation.map_reindex]
  exact Orientation.linearMapSign_map_map _ _
    (morseYComparison_negativeChange hφp hφp' hφq hφq' hφr hφr' hf₀ hy)

/-- **The signed count does not depend on the Morse charts**: it is unchanged when the Morse
charts are changed and the orientations of their coordinates of negative weight are transported
along the changes of negative coordinates. -/
theorem signedMorseYCount_map_negativeChange (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (o₀ : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₀ p)))
    (o₁ : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₁ q)))
    (o₂ : Orientation ℝ ({i // φr.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₂ r)))
    (hpqr : manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r) :
    hX₀.signedMorseYCount hX₁ hX₂ φp' φq' φr' (Orientation.map _ (φp.negativeChange φp') o₀)
        (Orientation.map _ (φq.negativeChange φq') o₁)
        (Orientation.map _ (φr.negativeChange φr') o₂) hpqr =
      hX₀.signedMorseYCount hX₁ hX₂ φp φq φr o₀ o₁ o₂ hpqr := by
  rw [signedMorseYCount_def, signedMorseYCount_def]
  exact finsum_mem_congr rfl fun y hy ↦
    morseYSign_map_negativeChange hφp hφp' hφq hφq' hφr hφr' hf₀ o₀ o₁ o₂ hpqr hy

end ChartChange

/-! ### The integral Morse diagonal -/

section Map

variable (hX₀ : IsAdaptedPseudoGradient f₀ X₀) (hX₁ : IsAdaptedPseudoGradient f₁ X₁)
  (hX₂ : IsAdaptedPseudoGradient f₂ X₂) (𝔬₀ : MorseOrientation f₀ X₀)
  (𝔬₁ : MorseOrientation f₁ X₁) (𝔬₂ : MorseOrientation f₂ X₂)

/-- The coefficient of `q ⊗ r` in the image of the critical point `p` of `f₀` under the integral
Morse diagonal: `TauCeti.IsAdaptedPseudoGradient.signedMorseYCount` when `ind p = ind q + ind r`,
and `0` otherwise. On a finite Y-slice this is its number of points counted with their signs. -/
noncomputable def signedMorseDiagonalCoeff (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁) (r : criticalPoints 𝓘(ℝ, E) f₂) : ℤ :=
  if hpqr : manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r then
    hX₀.signedMorseYCount hX₁ hX₂ (𝔬₀.chart p) (𝔬₁.chart q) (𝔬₂.chart r) (𝔬₀.orientation p)
      (𝔬₁.orientation q) (𝔬₂.orientation r) hpqr
  else 0

variable {hX₀ hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂}

/-- When `ind p = ind q + ind r`, the coefficient is the signed count of the Y-slice. -/
theorem signedMorseDiagonalCoeff_eq_signedMorseYCount {p : criticalPoints 𝓘(ℝ, E) f₀}
    {q : criticalPoints 𝓘(ℝ, E) f₁} {r : criticalPoints 𝓘(ℝ, E) f₂}
    (hpqr : manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r) :
    hX₀.signedMorseDiagonalCoeff hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ p q r =
      hX₀.signedMorseYCount hX₁ hX₂ (𝔬₀.chart p) (𝔬₁.chart q) (𝔬₂.chart r) (𝔬₀.orientation p)
        (𝔬₁.orientation q) (𝔬₂.orientation r) hpqr :=
  dite_eq_left hpqr

/-- The coefficient vanishes unless `ind p = ind q + ind r`: the integral Morse diagonal preserves
the total Morse index. -/
@[simp]
theorem signedMorseDiagonalCoeff_eq_zero_of_manifoldMorseIndex_ne
    {p : criticalPoints 𝓘(ℝ, E) f₀} {q : criticalPoints 𝓘(ℝ, E) f₁}
    {r : criticalPoints 𝓘(ℝ, E) f₂}
    (hpqr : manifoldMorseIndex 𝓘(ℝ, E) f₀ p ≠
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r) :
    hX₀.signedMorseDiagonalCoeff hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ p q r = 0 :=
  dite_eq_right hpqr

/-- **Reversing orientations changes the signs of the coefficients.** Reversing the orientations of
`𝔬₀`, `𝔬₁` and `𝔬₂` at the critical points of `S₀`, `S₁` and `S₂` multiplies the coefficient of
`q ⊗ r` in the image of `p` by `-1` for `p ∈ S₀`, by `-1` for `q ∈ S₁` and by `-1` for
`r ∈ S₂`. -/
theorem signedMorseDiagonalCoeff_reverse (S₀ : Set (criticalPoints 𝓘(ℝ, E) f₀))
    [DecidablePred (· ∈ S₀)] (S₁ : Set (criticalPoints 𝓘(ℝ, E) f₁)) [DecidablePred (· ∈ S₁)]
    (S₂ : Set (criticalPoints 𝓘(ℝ, E) f₂)) [DecidablePred (· ∈ S₂)]
    (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁)
    (r : criticalPoints 𝓘(ℝ, E) f₂) :
    hX₀.signedMorseDiagonalCoeff hX₁ hX₂ (𝔬₀.reverse S₀) (𝔬₁.reverse S₁) (𝔬₂.reverse S₂) p q r =
      (if p ∈ S₀ then -1 else 1) * ((if q ∈ S₁ then -1 else 1) * (if r ∈ S₂ then -1 else 1)) *
        hX₀.signedMorseDiagonalCoeff hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ p q r := by
  by_cases hpqr : manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r
  · rw [signedMorseDiagonalCoeff_eq_signedMorseYCount hpqr,
      signedMorseDiagonalCoeff_eq_signedMorseYCount hpqr, MorseOrientation.reverse_orientation,
      MorseOrientation.reverse_orientation, MorseOrientation.reverse_orientation]
    by_cases hp : p ∈ S₀ <;> by_cases hq : q ∈ S₁ <;> by_cases hr : r ∈ S₂ <;>
      simp [hp, hq, hr, MorseOrientation.reverse_chart]
  · simp [hpqr]

/-- **The mod-two reduction of the coefficients.** When `ind p = ind q + ind r` and the Y-slice is
finite with an isomorphism as comparison map at each of its points, the coefficient of `q ⊗ r` in
the image of `p` is the number of points of the Y-slice modulo two, whatever the orientations: it is
the coefficient of the mod-two Morse diagonal of the Y-slices. -/
theorem intCast_signedMorseDiagonalCoeff {p : criticalPoints 𝓘(ℝ, E) f₀}
    {q : criticalPoints 𝓘(ℝ, E) f₁} {r : criticalPoints 𝓘(ℝ, E) f₂}
    (hpqr : manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r)
    (hfin : (hX₀.morseYSlice hX₁ hX₂ p q r).Finite)
    (hbij : ∀ y ∈ hX₀.morseYSlice hX₁ hX₂ p q r,
      Bijective (hX₀.morseYComparison hX₁ hX₂ (𝔬₀.chart p) (𝔬₁.chart q) (𝔬₂.chart r) y)) :
    (hX₀.signedMorseDiagonalCoeff hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ p q r : ZMod 2) =
      morseDiagonalCoeff f₀ f₁ f₂ (hX₀.morseYSlice hX₁ hX₂) p q r := by
  rw [signedMorseDiagonalCoeff_eq_signedMorseYCount hpqr, morseDiagonalCoeff_eq_ncard hpqr]
  exact intCast_signedMorseYCount hfin hbij

variable (hX₀ hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂) in
/-- **The integral Morse diagonal with coefficients in a commutative ring `R`.** The `R`-linear map
from the free module on the critical points of `f₀` to the tensor product of the free modules on
the critical points of `f₁` and of `f₂` sending a critical point `p` to the sum of the tensors
`q ⊗ r` with `ind q + ind r = ind p`, each weighted by `signedMorseDiagonalCoeff`. On finite
Y-slices that weight is the number of points of `W^u_{X₀}(p) ∩ W^s_{X₁}(q) ∩ W^s_{X₂}(r)` counted
with their signs. -/
noncomputable def signedMorseDiagonalMap (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (hf₂ : IsMorse 𝓘(ℝ, E) f₂)
    (R : Type*) [CommRing R] :
    (criticalPoints 𝓘(ℝ, E) f₀ →₀ R) →ₗ[R]
      (criticalPoints 𝓘(ℝ, E) f₁ →₀ R) ⊗[R] (criticalPoints 𝓘(ℝ, E) f₂ →₀ R) :=
  haveI := hf₁.finite_criticalPoints.to_subtype
  haveI := hf₂.finite_criticalPoints.to_subtype
  (finsuppTensorFinsupp' R _ _).symm.toLinearMap ∘ₗ
    Finsupp.intMatrixMap R fun p x ↦ hX₀.signedMorseDiagonalCoeff hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ p x.1 x.2

variable (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (hf₂ : IsMorse 𝓘(ℝ, E) f₂) {R : Type*} [CommRing R]

/-- The coefficient of `q ⊗ r` in the integral Morse diagonal of a chain `c` is the sum over the
critical points `p` of `c p` times the coefficient `signedMorseDiagonalCoeff`. -/
theorem finsuppTensorFinsupp'_signedMorseDiagonalMap_apply (c : criticalPoints 𝓘(ℝ, E) f₀ →₀ R)
    (q : criticalPoints 𝓘(ℝ, E) f₁) (r : criticalPoints 𝓘(ℝ, E) f₂) :
    finsuppTensorFinsupp' R _ _ (hX₀.signedMorseDiagonalMap hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R c) (q, r) =
      c.sum fun p a ↦ a * (hX₀.signedMorseDiagonalCoeff hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ p q r : R) := by
  have := hf₁.finite_criticalPoints.to_subtype
  have := hf₂.finite_criticalPoints.to_subtype
  rw [signedMorseDiagonalMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, Finsupp.intMatrixMap_apply]

/-- The coefficient of `q ⊗ r` in the integral Morse diagonal of `a • p` is `a` times the
coefficient `signedMorseDiagonalCoeff`. -/
@[simp]
theorem finsuppTensorFinsupp'_signedMorseDiagonalMap_single_apply (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁) (r : criticalPoints 𝓘(ℝ, E) f₂) (a : R) :
    finsuppTensorFinsupp' R _ _
        (hX₀.signedMorseDiagonalMap hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R (Finsupp.single p a)) (q, r) =
      a * (hX₀.signedMorseDiagonalCoeff hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ p q r : R) := by
  rw [finsuppTensorFinsupp'_signedMorseDiagonalMap_apply, Finsupp.sum_single_index (zero_mul _)]

/-- **Reversing orientations conjugates the integral Morse diagonal.** The integral Morse diagonal
for the orientations reversed at the critical points of `S₀`, `S₁` and `S₂` is the original
diagonal composed with the involution `Finsupp.signReversal` on `S₀` before it and with the tensor
product of the involutions on `S₁` and on `S₂` after it. -/
theorem signedMorseDiagonalMap_reverse (S₀ : Set (criticalPoints 𝓘(ℝ, E) f₀))
    [DecidablePred (· ∈ S₀)] (S₁ : Set (criticalPoints 𝓘(ℝ, E) f₁)) [DecidablePred (· ∈ S₁)]
    (S₂ : Set (criticalPoints 𝓘(ℝ, E) f₂)) [DecidablePred (· ∈ S₂)] :
    hX₀.signedMorseDiagonalMap hX₁ hX₂ (𝔬₀.reverse S₀) (𝔬₁.reverse S₁) (𝔬₂.reverse S₂) hf₁ hf₂ R =
      TensorProduct.map (Finsupp.signReversal R S₁).toLinearMap
          (Finsupp.signReversal R S₂).toLinearMap ∘ₗ
        hX₀.signedMorseDiagonalMap hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R ∘ₗ
          (Finsupp.signReversal R S₀).toLinearMap := by
  refine Finsupp.lhom_ext fun p a ↦
    (finsuppTensorFinsupp' R _ _).injective <| Finsupp.ext fun ⟨q, r⟩ ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, finsuppTensorFinsupp'_map_signReversal_apply,
    LinearEquiv.coe_coe, Finsupp.signReversal_single,
    finsuppTensorFinsupp'_signedMorseDiagonalMap_single_apply,
    finsuppTensorFinsupp'_signedMorseDiagonalMap_single_apply, signedMorseDiagonalCoeff_reverse]
  by_cases hp : p ∈ S₀ <;> by_cases hq : q ∈ S₁ <;> by_cases hr : r ∈ S₂ <;> simp [hp, hq, hr]

/-- **The integral Morse diagonal modulo two is the mod-two Morse diagonal of the Y-slices.** If
every Y-slice `W^u_{X₀}(p) ∩ W^s_{X₁}(q) ∩ W^s_{X₂}(r)` with `ind p = ind q + ind r` is finite,
with an isomorphism as comparison map at each of its points, then the integral Morse diagonal with
coefficients in `ZMod 2` is the mod-two Morse diagonal `TauCeti.morseDiagonalMap` of the Y-slices,
whatever the orientations. -/
theorem signedMorseDiagonalMap_zmod_two
    (hfin : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁)
      (r : criticalPoints 𝓘(ℝ, E) f₂), manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
        manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r →
      (hX₀.morseYSlice hX₁ hX₂ p q r).Finite)
    (hbij : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁)
      (r : criticalPoints 𝓘(ℝ, E) f₂), manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
        manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r →
      ∀ y ∈ hX₀.morseYSlice hX₁ hX₂ p q r,
        Bijective (hX₀.morseYComparison hX₁ hX₂ (𝔬₀.chart p) (𝔬₁.chart q) (𝔬₂.chart r) y)) :
    hX₀.signedMorseDiagonalMap hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ (ZMod 2) =
      morseDiagonalMap f₀ hf₁ hf₂ (hX₀.morseYSlice hX₁ hX₂) := by
  refine Finsupp.lhom_ext fun p a ↦
    (finsuppTensorFinsupp' (ZMod 2) _ _).injective <| Finsupp.ext fun ⟨q, r⟩ ↦ ?_
  rw [finsuppTensorFinsupp'_signedMorseDiagonalMap_single_apply,
    finsuppTensorFinsupp'_morseDiagonalMap_single_apply]
  by_cases hpqr : manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r
  · rw [intCast_signedMorseDiagonalCoeff hpqr (hfin p q r hpqr) (hbij p q r hpqr)]
  · rw [signedMorseDiagonalCoeff_eq_zero_of_manifoldMorseIndex_ne hpqr,
      morseDiagonalCoeff_eq_zero_of_manifoldMorseIndex_ne hpqr, Int.cast_zero]

end Map

end IsAdaptedPseudoGradient

end TauCeti
