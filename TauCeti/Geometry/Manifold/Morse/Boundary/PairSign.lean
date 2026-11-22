/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Integral
public import TauCeti.Geometry.Manifold.Morse.Stable.Pair
public import TauCeti.LinearAlgebra.Orientation.LinearMapSign

/-!
# Signed counts for a Morse–Smale pair of pseudo-gradients

Let `f₀` and `f₁` be Morse functions on a compact boundaryless manifold `M`, with pseudo-gradients
`X₀` and `X₁` adapted to them, and suppose that the pair `(X₀, X₁)` is Morse–Smale
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmalePair`). For a critical point `p` of `f₀` and a
critical point `q` of `f₁` of the same index, the intersection `W^u_{X₀}(p) ∩ W^s_{X₁}(q)` is
zero-dimensional, and finite when `X₀` and `X₁` are moreover Morse–Smale. For a continuation
from `X₀` to `X₁`, the coefficients of the mod-two continuation map count the points of
`W^u_{X₀}(p) ∩ Φ⁻¹ (W^s_{X₁}(q))` for the transition diffeomorphism `Φ` of the slab
(`TauCeti.IsContinuationField.eventually_morseContinuationCoeff_eq_ncard_inter_preimage`), and
`Φ⁻¹ (W^s_{X₁}(q))` is the stable manifold of `Φ⁻¹ q` for the pullback of `X₁` by `Φ`, a
pseudo-gradient adapted to `f₁ ∘ Φ`; that pullback is not constructed here. This file counts the
points of these intersections with signs, which is what a continuation map over `ℤ` needs.

Fix Morse charts `φp` at `p`, in which `X₀` is linear, and `φq` at `q`, in which `X₁` is linear,
and orientations `op` and `oq` of their spaces `Vp` and `Vq` of coordinates of negative weight;
these are orientations of the unstable manifolds of `X₀` at `p` and of `X₁` at `q`. At a point `y`
of `W^u_{X₀}(p) ∩ W^s_{X₁}(q)`:

* the unstable frame `Fp = hX₀.unstableFrame φp y : Vp → T_y M` of `X₀` carries `op` to the tangent
  space of `W^u_{X₀}(p)` at `y`;
* the normal coordinates `Nq = hX₁.stableNormal φq y : T_y M → Vq` of `X₁` carry the normal space
  of `W^s_{X₁}(q)` at `y` onto `Vq`, oriented by `oq`.

The **comparison map** `Nq ∘ Fp : Vp → Vq`
(`TauCeti.IsAdaptedPseudoGradient.pairComparison`) is an isomorphism when `ind p = ind q`
(`TauCeti.IsAdaptedPseudoGradient.bijective_pairComparison`): the two manifolds are transverse at
`y` and of complementary dimensions, so they meet only in `0` at the level of tangent spaces. The
**sign** of `y` (`TauCeti.IsAdaptedPseudoGradient.pairSign`), the sign
`Orientation.linearMapSign` of the comparison map, is `+1` if this isomorphism carries `op` to
`oq`, and `-1` otherwise: `y` counts positively when a positive basis of `T_y W^u_{X₀}(p)`
projects to a positive basis of the normal space of `W^s_{X₁}(q)`. Unlike the signs of the
trajectories counted by the Morse boundary (`TauCeti.IsAdaptedPseudoGradient.trajectorySign`),
there is no flow direction to split off, since the intersection is not invariant under a flow.
The **signed count** `TauCeti.IsAdaptedPseudoGradient.signedPairCount` sums the signs over the
intersection.

The signs have the expected properties:

* every point of the intersection has sign `±1`
  (`TauCeti.IsAdaptedPseudoGradient.pairSign_eq_one_or_eq_neg_one`), so the signed count reduces
  modulo two to the number of points (`TauCeti.IsAdaptedPseudoGradient.intCast_signedPairCount`);
* reversing either orientation reverses every sign
  (`TauCeti.IsAdaptedPseudoGradient.pairSign_neg_left`,
  `TauCeti.IsAdaptedPseudoGradient.pairSign_neg_right`);
* the signs do not depend on the Morse charts, only on the orientations of the unstable manifolds
  which the charts induce (`TauCeti.IsAdaptedPseudoGradient.pairSign_map_negativeChange`);
* for the pair `(X, X)` and the same chart and orientation at both ends, the critical point `p`
  itself, the only point of `W^u(p) ∩ W^s(p)`, has sign `1`
  (`TauCeti.IsAdaptedPseudoGradient.pairSign_self`,
  `TauCeti.IsAdaptedPseudoGradient.signedPairCount_self`).

Given orientation data `𝔬₀ : TauCeti.MorseOrientation f₀ X₀` and
`𝔬₁ : TauCeti.MorseOrientation f₁ X₁`, the signed counts are the coefficients
(`TauCeti.IsAdaptedPseudoGradient.signedPairCoeff`) of an `R`-linear map
(`TauCeti.IsAdaptedPseudoGradient.signedPairMap`) from the free `R`-module on the critical points
of `f₀` to that on the critical points of `f₁`, for any ring `R`. It preserves the Morse index, is
compatible with every change of coefficients along an additive map
(`TauCeti.IsAdaptedPseudoGradient.mapRange_signedPairMap`), and reversing the orientations at the
critical points of sets `S₀` and `S₁` conjugates it by the involutions `Finsupp.signReversal`
(`TauCeti.IsAdaptedPseudoGradient.signedPairMap_reverse`). For a Morse–Smale pair of Morse–Smale
pseudo-gradients its coefficients reduce modulo two to the numbers of points of the intersections
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmalePair.intCast_signedPairCoeff`), and for the pair
`(X, X)` with the same orientation data at both ends it is the identity
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.signedPairMap_self`). That it commutes with the
integral Morse boundaries needs the signed count of the ends of the one-dimensional intersections,
and is not proved here.

## Main definitions

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `pairComparison`: the comparison map `Vp → Vq` at a point of `W^u_{X₀}(p) ∩ W^s_{X₁}(q)`.
* `pairSign`: the sign of such a point.
* `signedPairCount`: the number of points of `W^u_{X₀}(p) ∩ W^s_{X₁}(q)` counted with signs.
* `signedPairCoeff`: the signed count, or `0` unless `ind p = ind q`.
* `signedPairMap`: the induced linear map between the free modules on the critical points.

## Main results

* `bijective_pairComparison`: the comparison map is an isomorphism at the points of
  `W^u_{X₀}(p) ∩ W^s_{X₁}(q)` when `ind p = ind q`.
* `pairSign_eq_one_or_eq_neg_one`, `intCast_signedPairCount`: the signs are `±1`, and the signed
  count reduces modulo two to the number of points.
* `exists_pairSign_eq_and_map_eq`, `pairSign_eq_of_map_eq`: where the comparison map is an
  isomorphism, the sign is the unit by which it scales the target orientation; the second reads it
  off any linear equivalence agreeing with the comparison map.
* `pairSign_neg_left`, `pairSign_neg_right`: reversing an orientation reverses the signs.
* `pairSign_map_negativeChange`, `signedPairCount_map_negativeChange`: the signs and the signed
  count do not depend on the Morse charts.
* `pairSign_self`, `signedPairCount_self`: for a single pseudo-gradient, a critical point counts
  once, with sign `1`.
* `mapRange_signedPairMap`, `signedPairMap_reverse`: change of coefficients and of orientations.
* `IsMorseSmalePair.intCast_signedPairCoeff`: the mod-two reduction of the coefficients.
* `IsMorseSmale.signedPairMap_self`: for a single Morse–Smale pseudo-gradient, the map is the
  identity.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations of the descending manifolds and signed
  counts) and §4.1 (continuation maps and their coefficients over `ℤ`).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapters 4 and 6 (orientations, and invariance of Morse homology by continuation).
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f f₀ f₁ : M → ℝ} {X X₀ X₁ : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

/-! ### The comparison map and the sign of a point -/

section Sign

variable (hX₀ : IsAdaptedPseudoGradient f₀ X₀) (hX₁ : IsAdaptedPseudoGradient f₁ X₁) {p q : M}
  (φp : MorseChart E f₀ p) (φq : MorseChart E f₁ q)

/-- The **comparison map** of a pair at a point `y`: it sends `v` in the space of coordinates of
negative weight of the Morse chart `φp` of `f₀` to the normal coordinates of `W^s_{X₁}(q)`, read in
the Morse chart `φq` of `f₁`, of the vector of the unstable frame of `W^u_{X₀}(p)` on `v`. -/
noncomputable def pairComparison (y : M) :
    ({i // φp.weight i < 0} → ℝ) →L[ℝ] ({i // φq.weight i < 0} → ℝ) :=
  (hX₁.stableNormal φq y).comp (hX₀.unstableFrame φp y)

/-- The comparison map is the normal coordinates of the unstable frame. -/
@[simp]
theorem pairComparison_apply (y : M) (v : {i // φp.weight i < 0} → ℝ) :
    hX₀.pairComparison hX₁ φp φq y v = hX₁.stableNormal φq y (hX₀.unstableFrame φp y v) :=
  (rfl)

/-- The **sign of a point** `y` of `W^u_{X₀}(p) ∩ W^s_{X₁}(q)`, for orientations `op` and `oq` of
the unstable manifolds of `X₀` at `p` and of `X₁` at `q`, of the same dimension: the sign
`Orientation.linearMapSign` of the comparison map, that is, `1` when it is an isomorphism carrying
`op` to `oq`, `-1` when it is an isomorphism reversing them, and `0` when it is not an
isomorphism. The last case does not happen on the intersection when the pair is Morse–Smale, `f₀`
is Morse and the pseudo-gradients are linear in the charts
(`TauCeti.IsAdaptedPseudoGradient.bijective_pairComparison`). -/
noncomputable def pairSign
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₀ p)))
    (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₁ q)))
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q) (y : M) : ℤ :=
  op.linearMapSign (Orientation.reindex ℝ _ (finCongr hpq.symm) oq)
    (hX₀.pairComparison hX₁ φp φq y).toLinearMap

/-- The sign of a point is the sign of the comparison map, with the target orientation reindexed
by the index of the source. -/
theorem pairSign_def
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₀ p)))
    (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₁ q)))
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q) (y : M) :
    hX₀.pairSign hX₁ φp φq op oq hpq y =
      op.linearMapSign (Orientation.reindex ℝ _ (finCongr hpq.symm) oq)
        (hX₀.pairComparison hX₁ φp φq y).toLinearMap :=
  (rfl)

/-- The number of points of `W^u_{X₀}(p) ∩ W^s_{X₁}(q)` counted with their signs. When
infinitely many points of the intersection have nonzero sign, this is the junk value `0`. For a
Morse–Smale pair of Morse–Smale pseudo-gradients adapted to Morse functions, the intersection is
finite (`IsMorseSmalePair.finite_unstableSet_inter_stableSet`). -/
noncomputable def signedPairCount
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₀ p)))
    (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₁ q)))
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q) : ℤ :=
  ∑ᶠ y ∈ hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet q, hX₀.pairSign hX₁ φp φq op oq hpq y

/-- The defining formula of the signed count. -/
theorem signedPairCount_def
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₀ p)))
    (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₁ q)))
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q) :
    hX₀.signedPairCount hX₁ φp φq op oq hpq =
      ∑ᶠ y ∈ hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet q, hX₀.pairSign hX₁ φp φq op oq hpq y :=
  (rfl)

variable {hX₀ hX₁ φp φq}
  {op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₀ p))}
  {oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₁ q))}
  {hpq : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q}

open scoped Classical in
/-- Where the comparison map is an isomorphism, the sign compares the orientation it carries `op`
to with `oq`. -/
theorem pairSign_of_bijective {y : M} (h : Bijective (hX₀.pairComparison hX₁ φp φq y)) :
    hX₀.pairSign hX₁ φp φq op oq hpq y =
      if Orientation.map _ (LinearEquiv.ofBijective (hX₀.pairComparison hX₁ φp φq y).toLinearMap h)
          op = Orientation.reindex ℝ _ (finCongr hpq.symm) oq then 1 else -1 :=
  Orientation.linearMapSign_of_bijective h

/-- Where the comparison map is not an isomorphism, the sign is `0`. -/
theorem pairSign_of_not_bijective {y : M} (h : ¬Bijective (hX₀.pairComparison hX₁ φp φq y)) :
    hX₀.pairSign hX₁ φp φq op oq hpq y = 0 :=
  Orientation.linearMapSign_of_not_bijective h

/-- **The sign of a point is `±1`** wherever the comparison map is an isomorphism. -/
theorem pairSign_eq_one_or_eq_neg_one_of_bijective {y : M}
    (h : Bijective (hX₀.pairComparison hX₁ φp φq y)) :
    hX₀.pairSign hX₁ φp φq op oq hpq y = 1 ∨ hX₀.pairSign hX₁ φp φq op oq hpq y = -1 :=
  Orientation.linearMapSign_eq_one_or_eq_neg_one_of_bijective h

/-- **The sign as a unit.** Where the comparison map is an isomorphism, it carries `op` to `oq`,
reindexed, scaled by a unit sign `u`, and the sign of the point is `u`. -/
theorem exists_pairSign_eq_and_map_eq {y : M} (h : Bijective (hX₀.pairComparison hX₁ φp φq y)) :
    ∃ u : ℤˣ, hX₀.pairSign hX₁ φp φq op oq hpq y = u ∧
      Orientation.map _ (LinearEquiv.ofBijective (hX₀.pairComparison hX₁ φp φq y).toLinearMap h)
          op =
        Units.map (Int.castRingHom ℝ).toMonoidHom u •
          Orientation.reindex ℝ _ (finCongr hpq.symm) oq :=
  Orientation.exists_linearMapSign_eq_and_map_eq
    (by rw [Fintype.card_fin, φq.finrank_negativeWeight_fun, hpq]) h

/-- **Reading off the sign.** If a linear equivalence `L` agrees with the comparison map and
carries `op` to `oq`, reindexed, scaled by a unit sign `u`, the sign of the point is `u`. -/
theorem pairSign_eq_of_map_eq {y : M}
    (L : ({i // φp.weight i < 0} → ℝ) ≃ₗ[ℝ] ({i // φq.weight i < 0} → ℝ))
    (hL : ∀ v, L v = hX₀.pairComparison hX₁ φp φq y v) {u : ℤˣ}
    (hu : Orientation.map _ L op =
      Units.map (Int.castRingHom ℝ).toMonoidHom u •
        Orientation.reindex ℝ _ (finCongr hpq.symm) oq) :
    hX₀.pairSign hX₁ φp φq op oq hpq y = u :=
  Orientation.linearMapSign_eq_of_map_eq L hL hu

/-- **Reversing the orientation at the source reverses the sign.** -/
@[simp]
theorem pairSign_neg_left (y : M) :
    hX₀.pairSign hX₁ φp φq (-op) oq hpq y = -hX₀.pairSign hX₁ φp φq op oq hpq y :=
  Orientation.linearMapSign_neg_left
    (by rw [Fintype.card_fin, φq.finrank_negativeWeight_fun, hpq])

/-- **Reversing the orientation at the target reverses the sign.** -/
@[simp]
theorem pairSign_neg_right (y : M) :
    hX₀.pairSign hX₁ φp φq op (-oq) hpq y = -hX₀.pairSign hX₁ φp φq op oq hpq y := by
  rw [pairSign_def, pairSign_def, Orientation.reindex_neg]
  exact Orientation.linearMapSign_neg_right
    (by rw [Fintype.card_fin, φq.finrank_negativeWeight_fun, hpq])

/-- Reversing the orientation at the source reverses the signed count. -/
@[simp]
theorem signedPairCount_neg_left :
    hX₀.signedPairCount hX₁ φp φq (-op) oq hpq = -hX₀.signedPairCount hX₁ φp φq op oq hpq := by
  simp only [signedPairCount_def, pairSign_neg_left, finsum_neg_distrib]

/-- Reversing the orientation at the target reverses the signed count. -/
@[simp]
theorem signedPairCount_neg_right :
    hX₀.signedPairCount hX₁ φp φq op (-oq) hpq = -hX₀.signedPairCount hX₁ φp φq op oq hpq := by
  simp only [signedPairCount_def, pairSign_neg_right, finsum_neg_distrib]

variable (hφp : ∀ y ∈ φp.toChart.source,
    φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart y (X₀ y)) =
      fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
  (hφq : ∀ y ∈ φq.toChart.source,
    φq.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart y (X₁ y)) =
      fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))
include hφp hφq

/-- **The comparison map is an isomorphism on a rigid intersection.** Let `(X₀, X₁)` be a
Morse–Smale pair, `f₀` Morse, and `p`, `q` critical points of `f₀` and `f₁` with `ind p = ind q`,
with Morse charts in which `X₀` and `X₁` are linear. At every point `y` of
`W^u_{X₀}(p) ∩ W^s_{X₁}(q)`, the comparison map `Vp → Vq` is bijective: a vector of the unstable
frame with vanishing normal coordinates is tangent to the intersection, which is
zero-dimensional. -/
theorem bijective_pairComparison (h : IsMorseSmalePair hX₀ hX₁) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q) {y : M}
    (hy : y ∈ hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet q) :
    Bijective (hX₀.pairComparison hX₁ φp φq y) := by
  have hinj : Injective (hX₀.pairComparison hX₁ φp φq y) := by
    refine (injective_iff_map_eq_zero (hX₀.pairComparison hX₁ φp φq y)).2 fun v hv ↦ ?_
    rw [pairComparison_apply] at hv
    have hdim :=
      h.finrank_span_mtangentConeAt_unstableSet_inter_stableSet_add_manifoldMorseIndex hf₀ hy
    have h0 : Submodule.span ℝ
        (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet q) y) = ⊥ :=
      Submodule.finrank_eq_zero.1 (by omega)
    -- `u = Fp v` is tangent to `W^u_{X₀}(p)` and to `W^s_{X₁}(q)`, hence to their
    -- zero-dimensional intersection. It is read as a vector of the model space `E`.
    obtain ⟨u, hu⟩ : ∃ u : E, hX₀.unstableFrame φp y v = u := ⟨_, rfl⟩
    have hu₁ : u ∈ Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet p) y) :=
      (Set.ext_iff.1 (hX₀.range_unstableFrame hφp hf₀ hy.1) u).1 ⟨v, hu⟩
    have hu₂ : u ∈ Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet q) y) :=
      (hX₁.stableNormal_eq_zero_iff hφq hy.2 u).1 (hu ▸ hv)
    have hu₃ : u ∈ Submodule.span ℝ
        (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet q) y) := by
      rw [h.span_mtangentConeAt_unstableSet_inter_stableSet hf₀ hy]
      exact ⟨hu₁, hu₂⟩
    rw [h0, Submodule.mem_bot] at hu₃
    exact hX₀.injective_unstableFrame_of_mem hφp hf₀ hy.1 (hu.trans (hu₃.trans (map_zero _).symm))
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj⟩
  rw [φp.finrank_negativeWeight_fun, φq.finrank_negativeWeight_fun, hpq]

/-- **The sign of a point of a rigid intersection is `±1`.** -/
theorem pairSign_eq_one_or_eq_neg_one (h : IsMorseSmalePair hX₀ hX₁) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    {y : M} (hy : y ∈ hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet q) :
    hX₀.pairSign hX₁ φp φq op oq hpq y = 1 ∨ hX₀.pairSign hX₁ φp φq op oq hpq y = -1 :=
  pairSign_eq_one_or_eq_neg_one_of_bijective (bijective_pairComparison hφp hφq h hf₀ hpq hy)

/-- **The signed count reduces to the number of points modulo two.** For a Morse–Smale pair of
Morse–Smale pseudo-gradients adapted to Morse functions, the signed count of
`W^u_{X₀}(p) ∩ W^s_{X₁}(q)`, for `ind p = ind q`, is its number of points modulo two. -/
theorem intCast_signedPairCount (h : IsMorseSmalePair hX₀ hX₁) (h₀ : hX₀.IsMorseSmale)
    (h₁ : hX₁.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hf₁ : IsMorse 𝓘(ℝ, E) f₁) :
    (hX₀.signedPairCount hX₁ φp φq op oq hpq : ZMod 2) =
      ((hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet q).ncard : ZMod 2) := by
  have hfin := h.finite_unstableSet_inter_stableSet h₀ h₁ hf₀ hf₁ hpq.le
  rw [signedPairCount_def, finsum_mem_eq_finite_toFinset_sum _ hfin, Int.cast_sum,
    ncard_eq_toFinset_card _ hfin, Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl fun y hy ↦ ?_
  rw [Finite.mem_toFinset] at hy
  rcases pairSign_eq_one_or_eq_neg_one hφp hφq h hf₀ hy with h | h <;> rw [h] <;> decide

end Sign

/-! ### A single pseudo-gradient -/

section Self

variable {hX : IsAdaptedPseudoGradient f X} {x : M} {φ : MorseChart E f x}
  (hφ : ∀ y ∈ φ.toChart.source,
    φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
include hφ

/-- **The comparison map at a critical point is the identity**, for a single pseudo-gradient and
the same Morse chart at both ends: the normal coordinates invert the unstable frame there. -/
theorem pairComparison_self : hX.pairComparison hX φ φ x = ContinuousLinearMap.id ℝ _ :=
  ContinuousLinearMap.ext fun c ↦ hX.stableNormal_unstableFrame_self hφ c

/-- **A critical point counts with sign `1`** in `W^u(x) ∩ W^s(x)`, for a single pseudo-gradient and
the same chart and orientation at both ends. -/
theorem pairSign_self
    (o : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x))) :
    hX.pairSign hX φ φ o o rfl x = 1 := by
  have h := pairSign_eq_of_map_eq (hX₀ := hX) (hX₁ := hX) (op := o) (oq := o) (hpq := rfl)
    (LinearEquiv.refl ℝ _)
    (fun v ↦ by rw [pairComparison_self hφ]; rfl) (u := 1)
    (by rw [Orientation.map_refl, finCongr_refl, Orientation.reindex_refl]; simp)
  exact h.trans Units.val_one

/-- **The signed count of a critical point to itself is `1`**, for a single pseudo-gradient and the
same chart and orientation at both ends: `W^u(x) ∩ W^s(x)` is the critical point `x` alone. -/
theorem signedPairCount_self (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0)
    (o : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x))) :
    hX.signedPairCount hX φ φ o o rfl = 1 := by
  have hset : hX.flow.unstableSet x ∩ hX.flow.stableSet x = {x} :=
    eq_singleton_iff_unique_mem.2
      ⟨hX.mem_unstableSet_inter_stableSet_self hx,
        fun _ hy ↦ hX.eq_of_mem_unstableSet_inter_stableSet hy⟩
  rw [signedPairCount_def, hset, finsum_mem_singleton, pairSign_self hφ]

end Self

/-! ### Changing the Morse charts -/

section ChartChange

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁} {p q : M}
  {φp φp' : MorseChart E f₀ p} {φq φq' : MorseChart E f₁ q}
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
include hφp hφp' hφq hφq'

/-- **The comparison map in other Morse charts.** At a point of `W^u_{X₀}(p) ∩ W^s_{X₁}(q)`,
replacing the Morse charts `φp` and `φq` by `φp'` and `φq'` composes the comparison map with the
changes of negative coordinates at both ends. -/
theorem pairComparison_negativeChange (hf₀ : IsMorse 𝓘(ℝ, E) f₀) {y : M}
    (hy : y ∈ hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet q) (v : {i // φp.weight i < 0} → ℝ) :
    hX₀.pairComparison hX₁ φp' φq' y (φp.negativeChange φp' v) =
      φq.negativeChange φq' (hX₀.pairComparison hX₁ φp φq y v) := by
  rw [pairComparison_apply, pairComparison_apply, unstableFrame_negativeChange hφp hφp' hf₀ hy.1,
    negativeChange_stableNormal hφq hφq' hy.2]

/-- **The sign of a point does not depend on the Morse charts.** At a point of
`W^u_{X₀}(p) ∩ W^s_{X₁}(q)`, the sign for the orientations `op` and `oq` in the charts `φp` and
`φq` is the sign in the charts `φp'` and `φq'` for the orientations transported along the changes
of negative coordinates. -/
theorem pairSign_map_negativeChange (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₀ p)))
    (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₁ q)))
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q) {y : M}
    (hy : y ∈ hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet q) :
    hX₀.pairSign hX₁ φp' φq' (Orientation.map _ (φp.negativeChange φp') op)
        (Orientation.map _ (φq.negativeChange φq') oq) hpq y =
      hX₀.pairSign hX₁ φp φq op oq hpq y := by
  rw [pairSign_def, pairSign_def, ← Orientation.map_reindex]
  exact Orientation.linearMapSign_map_map _ _
    (pairComparison_negativeChange hφp hφp' hφq hφq' hf₀ hy)

/-- **The signed count does not depend on the Morse charts**: it is unchanged when the Morse
charts are changed and the orientations of their coordinates of negative weight are transported
along the changes of negative coordinates. -/
theorem signedPairCount_map_negativeChange (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₀ p)))
    (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₁ q)))
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q) :
    hX₀.signedPairCount hX₁ φp' φq' (Orientation.map _ (φp.negativeChange φp') op)
        (Orientation.map _ (φq.negativeChange φq') oq) hpq =
      hX₀.signedPairCount hX₁ φp φq op oq hpq := by
  rw [signedPairCount_def, signedPairCount_def]
  exact finsum_mem_congr rfl fun y hy ↦
    pairSign_map_negativeChange hφp hφp' hφq hφq' hf₀ op oq hpq hy

end ChartChange

/-! ### The signed pair map between Morse chains -/

section Map

variable (hX₀ : IsAdaptedPseudoGradient f₀ X₀) (hX₁ : IsAdaptedPseudoGradient f₁ X₁)
  (𝔬₀ : MorseOrientation f₀ X₀) (𝔬₁ : MorseOrientation f₁ X₁) {hX : IsAdaptedPseudoGradient f X}

/-- The coefficient of the critical point `q` of `f₁` in the image of the critical point `p` of
`f₀` under the signed pair map: `TauCeti.IsAdaptedPseudoGradient.signedPairCount` when
`ind p = ind q`, and `0` otherwise. For a Morse–Smale pair of Morse–Smale pseudo-gradients
adapted to Morse functions, this is the number of points of `W^u_{X₀}(p) ∩ W^s_{X₁}(q)` counted
with their signs. -/
noncomputable def signedPairCoeff (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁) : ℤ :=
  if hpq : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q then
    hX₀.signedPairCount hX₁ (𝔬₀.chart p) (𝔬₁.chart q) (𝔬₀.orientation p) (𝔬₁.orientation q) hpq
  else 0

variable {hX₀ hX₁ 𝔬₀ 𝔬₁}

/-- For critical points of the same index, the coefficient is the signed count. -/
theorem signedPairCoeff_of_morseIndex_eq {p : criticalPoints 𝓘(ℝ, E) f₀}
    {q : criticalPoints 𝓘(ℝ, E) f₁}
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q) :
    hX₀.signedPairCoeff hX₁ 𝔬₀ 𝔬₁ p q =
      hX₀.signedPairCount hX₁ (𝔬₀.chart p) (𝔬₁.chart q) (𝔬₀.orientation p) (𝔬₁.orientation q)
        hpq :=
  dite_eq_left hpq

/-- The coefficient vanishes between critical points of different indices. -/
@[simp]
theorem signedPairCoeff_eq_zero_of_morseIndex_ne {p : criticalPoints 𝓘(ℝ, E) f₀}
    {q : criticalPoints 𝓘(ℝ, E) f₁}
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f₀ p ≠ manifoldMorseIndex 𝓘(ℝ, E) f₁ q) :
    hX₀.signedPairCoeff hX₁ 𝔬₀ 𝔬₁ p q = 0 :=
  dite_eq_right hpq

/-- **The signed pair map preserves the index**: a nonzero coefficient joins critical points of the
same index. -/
theorem morseIndex_eq_of_signedPairCoeff_ne_zero {p : criticalPoints 𝓘(ℝ, E) f₀}
    {q : criticalPoints 𝓘(ℝ, E) f₁} (hpq : hX₀.signedPairCoeff hX₁ 𝔬₀ 𝔬₁ p q ≠ 0) :
    manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q := by
  by_contra h
  exact hpq (signedPairCoeff_eq_zero_of_morseIndex_ne h)

/-- **Reversing orientations changes the signs of the coefficients.** Reversing the orientations of
`𝔬₀` at the critical points of `S₀` and those of `𝔬₁` at the critical points of `S₁` multiplies the
coefficient of `q` in the image of `p` by `-1` for `p ∈ S₀` and by `-1` for `q ∈ S₁`. -/
theorem signedPairCoeff_reverse (S₀ : Set (criticalPoints 𝓘(ℝ, E) f₀)) [DecidablePred (· ∈ S₀)]
    (S₁ : Set (criticalPoints 𝓘(ℝ, E) f₁)) [DecidablePred (· ∈ S₁)]
    (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁) :
    hX₀.signedPairCoeff hX₁ (𝔬₀.reverse S₀) (𝔬₁.reverse S₁) p q =
      (if p ∈ S₀ then -1 else 1) * (if q ∈ S₁ then -1 else 1) *
        hX₀.signedPairCoeff hX₁ 𝔬₀ 𝔬₁ p q := by
  by_cases hpq : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q
  · rw [signedPairCoeff_of_morseIndex_eq hpq, signedPairCoeff_of_morseIndex_eq hpq,
      MorseOrientation.reverse_orientation, MorseOrientation.reverse_orientation]
    by_cases hp : p ∈ S₀ <;> by_cases hq : q ∈ S₁ <;>
      simp [hp, hq, MorseOrientation.reverse_chart]
  · simp [hpq]

/-- **The mod-two reduction of the coefficients.** For a Morse–Smale pair of Morse–Smale
pseudo-gradients adapted to Morse functions, the coefficient of `q` in the image of `p`, for
`ind p = ind q`, is the number of points of `W^u_{X₀}(p) ∩ W^s_{X₁}(q)` modulo two, whatever the
orientations. -/
theorem IsMorseSmalePair.intCast_signedPairCoeff (h : IsMorseSmalePair hX₀ hX₁)
    (h₀ : hX₀.IsMorseSmale) (h₁ : hX₁.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hf₁ : IsMorse 𝓘(ℝ, E) f₁) {p : criticalPoints 𝓘(ℝ, E) f₀} {q : criticalPoints 𝓘(ℝ, E) f₁}
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q) :
    (hX₀.signedPairCoeff hX₁ 𝔬₀ 𝔬₁ p q : ZMod 2) =
      ((hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet q).ncard : ZMod 2) := by
  rw [signedPairCoeff_of_morseIndex_eq hpq]
  exact intCast_signedPairCount (𝔬₀.coord_mfderiv_chart p) (𝔬₁.coord_mfderiv_chart q) h h₀ h₁ hf₀
    hf₁

open scoped Classical in
/-- **For a single Morse–Smale pseudo-gradient, the coefficients form the identity matrix**, with
the same orientation data at both ends: a critical point counts once in its own image, and the
unstable manifold of a critical point misses the stable manifolds of the other critical points of
the same index. -/
theorem IsMorseSmale.signedPairCoeff_self {𝔬 : MorseOrientation f X} (h : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f) (p q : criticalPoints 𝓘(ℝ, E) f) :
    hX.signedPairCoeff hX 𝔬 𝔬 p q = if p = q then 1 else 0 := by
  by_cases hpq : p = q
  · subst hpq
    rw [signedPairCoeff_of_morseIndex_eq rfl, signedPairCount_self (𝔬.coord_mfderiv_chart p)
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 p.property)]
    simp
  simp only [hpq, ↓reduceIte]
  by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q
  · -- A point of `W^u(p) ∩ W^s(q)` would make the index drop strictly from `p` to `q`.
    have hempty : hX.flow.unstableSet p ∩ hX.flow.stableSet q = ∅ :=
      eq_empty_iff_forall_notMem.2 fun y hy ↦
        (hX.manifoldMorseIndex_lt_of_mem_unstableSet_inter_stableSet hf
          (Subtype.coe_injective.ne hpq) hy (h.span_mtangentConeAt_sup_eq_top hy)).ne' hind
    rw [signedPairCoeff_of_morseIndex_eq hind, signedPairCount_def, hempty, finsum_mem_empty]
  · exact signedPairCoeff_eq_zero_of_morseIndex_ne hind

variable (hX₀ hX₁ 𝔬₀ 𝔬₁) in
/-- **The signed pair map with coefficients in a ring `R`.** The `R`-linear map from the free module
on the critical points of `f₀` to that on the critical points of `f₁` sending a critical point `p`
to the sum of the critical points `q` with `ind q = ind p`, each weighted by `signedPairCoeff`. For
a Morse–Smale pair of Morse–Smale pseudo-gradients adapted to Morse functions, that weight is the
number of points of `W^u_{X₀}(p) ∩ W^s_{X₁}(q)` counted with their signs. -/
noncomputable def signedPairMap (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (R : Type*) [Ring R] :
    (criticalPoints 𝓘(ℝ, E) f₀ →₀ R) →ₗ[R] (criticalPoints 𝓘(ℝ, E) f₁ →₀ R) :=
  haveI := hf₁.finite_criticalPoints.to_subtype
  Finsupp.linearCombination R fun p ↦
    Finsupp.ofSupportFinite (fun q ↦ (hX₀.signedPairCoeff hX₁ 𝔬₀ 𝔬₁ p q : R)) (toFinite _)

variable (hf₁ : IsMorse 𝓘(ℝ, E) f₁) {R : Type*} [Ring R]

/-- The coefficient of `q` in the image of a chain `c` is the sum over the critical points `p` of
`c p` times the coefficient `signedPairCoeff` of `q` in the image of `p`. -/
theorem signedPairMap_apply (c : criticalPoints 𝓘(ℝ, E) f₀ →₀ R)
    (q : criticalPoints 𝓘(ℝ, E) f₁) :
    hX₀.signedPairMap hX₁ 𝔬₀ 𝔬₁ hf₁ R c q =
      c.sum fun p a ↦ a * (hX₀.signedPairCoeff hX₁ 𝔬₀ 𝔬₁ p q : R) := by
  simp [signedPairMap, Finsupp.linearCombination_apply, Finsupp.ofSupportFinite_coe]

/-- The coefficient of `q` in the image of `a • p` is `a` times the coefficient `signedPairCoeff`
of `q` in the image of `p`. -/
@[simp]
theorem signedPairMap_single_apply (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁) (a : R) :
    hX₀.signedPairMap hX₁ 𝔬₀ 𝔬₁ hf₁ R (Finsupp.single p a) q =
      a * (hX₀.signedPairCoeff hX₁ 𝔬₀ 𝔬₁ p q : R) := by
  rw [signedPairMap_apply, Finsupp.sum_single_index (zero_mul _)]

/-- **Change of coefficients.** An additive map `g : R → R'`, for instance a ring homomorphism,
applied to the coefficients of the chains, intertwines the signed pair maps with coefficients in
`R` and in `R'`: the coefficients are integers, and `g` commutes with integer multiples. -/
theorem mapRange_signedPairMap {R' F : Type*} [Ring R'] [FunLike F R R']
    [AddMonoidHomClass F R R'] (g : F) (c : criticalPoints 𝓘(ℝ, E) f₀ →₀ R) :
    Finsupp.mapRange g (map_zero g) (hX₀.signedPairMap hX₁ 𝔬₀ 𝔬₁ hf₁ R c) =
      hX₀.signedPairMap hX₁ 𝔬₀ 𝔬₁ hf₁ R' (Finsupp.mapRange g (map_zero g) c) := by
  ext q
  rw [Finsupp.mapRange_apply, signedPairMap_apply, signedPairMap_apply,
    Finsupp.sum_mapRange_index (fun _ ↦ zero_mul _), map_finsuppSum]
  simp only [← zsmul_eq_mul', map_zsmul]

/-- **Reversing orientations conjugates the signed pair map.** The signed pair map for the
orientations reversed at the critical points of `S₀` and `S₁` is the original map composed on both
sides with the involutions `Finsupp.signReversal` negating the coefficients on `S₀` and on `S₁`. -/
theorem signedPairMap_reverse (S₀ : Set (criticalPoints 𝓘(ℝ, E) f₀)) [DecidablePred (· ∈ S₀)]
    (S₁ : Set (criticalPoints 𝓘(ℝ, E) f₁)) [DecidablePred (· ∈ S₁)] :
    hX₀.signedPairMap hX₁ (𝔬₀.reverse S₀) (𝔬₁.reverse S₁) hf₁ R =
      (Finsupp.signReversal R S₁).toLinearMap ∘ₗ hX₀.signedPairMap hX₁ 𝔬₀ 𝔬₁ hf₁ R ∘ₗ
        (Finsupp.signReversal R S₀).toLinearMap := by
  refine Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun q ↦ ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [signedPairMap_single_apply, Finsupp.signReversal_single, Finsupp.signReversal_apply,
    signedPairCoeff_reverse]
  by_cases hp : p ∈ S₀ <;> by_cases hq : q ∈ S₁ <;> simp [hp, hq]

/-- **For a single Morse–Smale pseudo-gradient, the signed pair map is the identity**, with the
same orientation data at both ends. -/
theorem IsMorseSmale.signedPairMap_self {𝔬 : MorseOrientation f X} (h : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f) : hX.signedPairMap hX 𝔬 𝔬 hf R = LinearMap.id := by
  classical
  refine Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun q ↦ ?_
  rw [signedPairMap_single_apply, h.signedPairCoeff_self hf, LinearMap.id_apply,
    Finsupp.single_apply]
  split_ifs <;> simp

end Map

end IsAdaptedPseudoGradient

end TauCeti
