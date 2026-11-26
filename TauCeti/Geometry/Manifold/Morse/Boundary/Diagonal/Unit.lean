/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Diagonal.Signed
public import TauCeti.Geometry.Manifold.Morse.Boundary.SignedAugmentation
import TauCeti.LinearAlgebra.DirectSum.Finsupp

/-!
# The augmentation is a unit for the integral Morse diagonal

Let `f₀`, `f₁` and `f₂` be Morse functions on a compact boundaryless manifold `M`, with
pseudo-gradients `X₀`, `X₁` and `X₂` adapted to them and orientation data `𝔬₀`, `𝔬₁` and `𝔬₂`
(`TauCeti.MorseOrientation`). The integral Morse diagonal
`Δ = TauCeti.IsAdaptedPseudoGradient.signedMorseDiagonalMap` counts, with signs, the points of the
Y-slices `W^u_{X₀}(p) ∩ W^s_{X₁}(q) ∩ W^s_{X₂}(r)`, the vertices of the Y-shaped flow lines. The
augmentation `ε = TauCeti.MorseOrientation.signedMorseAugmentation` adds up the coefficients of the
critical points of index `0`, each weighted by the sign `±1` of the orientation chosen there; for
the orientations of the empty basis it is the sum of the dual cochains of the minima. This file
shows that `ε` is a unit for `Δ` on each side, up to the signed pair map
`TauCeti.IsAdaptedPseudoGradient.signedPairMap`, which counts with signs the points of the
intersections `W^u_{X₀}(p) ∩ W^s_{X₂}(r)` between critical points of the same index.

**Signs.** At a critical point `q` of index `0`, the stable manifold of `q` is open and has no
normal directions. So at a point `y` of the Y-slice, the comparison map of the Y-flow line, which
sends the unstable directions at `p` to the normal directions of `W^s_{X₁}(q)` and of `W^s_{X₂}(r)`,
is the comparison map of the pair `(X₀, X₂)` followed by `w ↦ (0, w)`. The product orientation of
the two leaves is then the orientation at `r`, multiplied by the sign of the orientation at `q`
(`Orientation.reindex_prod_of_left_eq_zero`). Hence the sign of `y` as a Y-flow line is the
augmentation sign of `q` times its sign for the pair `(X₀, X₂)`
(`TauCeti.IsAdaptedPseudoGradient.morseYSign_of_morseIndex_eq_zero_left`), and symmetrically for a
second leaf of index `0` (`TauCeti.IsAdaptedPseudoGradient.morseYSign_of_morseIndex_eq_zero_right`).

**Counts.** Every point of `M` flows along `X₁` to a critical point of `f₁`, and the stable
manifolds of distinct critical points are disjoint. So if no point of the intersection
`W^u_{X₀}(p) ∩ W^s_{X₂}(r)`, for `ind p = ind r`, flows to a critical point of `f₁` of positive
index, that intersection is the disjoint union of the Y-slices `W^u_{X₀}(p) ∩ W^s_{X₁}(m) ∩
W^s_{X₂}(r)` over the critical points `m` of `f₁` of index `0`. For Morse–Smale data this is what
the dimension count `ind p - ind c - ind r < 0` gives at a critical point `c` of positive index.
Counting with signs,

`∑ₘ ε(m) Δ(p)_{m, r} = #_± (W^u_{X₀}(p) ∩ W^s_{X₂}(r))`

(`finsum_augmentationSign_mul_signedMorseDiagonalCoeff`), that is, `(ε ⊗ 1) ∘ Δ` is the signed pair
map of `(X₀, X₂)` (`lid_comp_rTensor_signedMorseAugmentation_comp_signedMorseDiagonalMap`), and
symmetrically `(1 ⊗ ε) ∘ Δ` is the signed pair map of `(X₀, X₁)`
(`rid_comp_lTensor_signedMorseAugmentation_comp_signedMorseDiagonalMap`), both in the namespace
`TauCeti.IsAdaptedPseudoGradient`.
When the root and the other leaf follow the same Morse–Smale pseudo-gradient with the same
orientation data, the signed pair map is the identity, so `ε` is a unit on the nose
(`IsMorseSmale.lid_comp_rTensor_signedMorseAugmentation_comp_signedMorseDiagonalMap_self` and
`IsMorseSmale.rid_comp_lTensor_signedMorseAugmentation_comp_signedMorseDiagonalMap_self`, in the
namespace `TauCeti.IsAdaptedPseudoGradient`).

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `morseYSign_of_morseIndex_eq_zero_left`, `morseYSign_of_morseIndex_eq_zero_right`: the sign of a
  Y-flow line with a leaf at a critical point of index `0`.
* `finsum_augmentationSign_mul_signedMorseDiagonalCoeff`,
  `finsum_augmentationSign_mul_signedMorseDiagonalCoeff_right`: the augmentation of the diagonal
  coefficients is the signed pair count.
* `lid_comp_rTensor_signedMorseAugmentation_comp_signedMorseDiagonalMap`,
  `rid_comp_lTensor_signedMorseAugmentation_comp_signedMorseDiagonalMap`: the unit laws up to the
  signed pair maps.
* `IsMorseSmale.lid_comp_rTensor_signedMorseAugmentation_comp_signedMorseDiagonalMap_self`,
  `IsMorseSmale.rid_comp_lTensor_signedMorseAugmentation_comp_signedMorseDiagonalMap_self`: the
  unit laws on the nose.

## References

* S. Mescher, *Perturbed gradient flow trees and A∞-algebra structures in Morse cohomology*,
  arXiv:1611.07916, §§1–5 (Y-flow lines and the Morse cup product, whose unit is the sum of the
  dual cochains of the minima).
* K. Fukaya, *Morse homotopy, A∞-category, and Floer homologies*, Proceedings of GARC Workshop on
  Geometry and Topology '93, Seoul National University, 1993 (products by counting flow trees for
  three Morse functions).
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

/-! ### The sign of a Y-flow line with a leaf of index `0` -/

section Sign

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  {hX₂ : IsAdaptedPseudoGradient f₂ X₂} {p q r : M}
  {φp : MorseChart E f₀ p} {φq : MorseChart E f₁ q} {φr : MorseChart E f₂ r}
  {o₀ : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₀ p))}
  {o₁ : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₁ q))}
  {o₂ : Orientation ℝ ({i // φr.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₂ r))}
  {hpqr : manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
    manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r}

/-- **The sign of a Y-flow line whose first leaf ends at a critical point of index `0`.** If
`ind q = 0`, the sign of a point `y` of the Y-slice from `p` to `q` and `r` is the sign of the
orientation `o₁` at `q`, relative to the empty basis, times the sign of `y` as a point of
`W^u_{X₀}(p) ∩ W^s_{X₂}(r)`. -/
theorem morseYSign_of_morseIndex_eq_zero_left (hq : manifoldMorseIndex 𝓘(ℝ, E) f₁ q = 0)
    (y : M) :
    hX₀.morseYSign hX₁ hX₂ φp φq φr o₀ o₁ o₂ hpqr y =
      (o₁.signBasis (Module.finBasisOfFinrankEq ℝ _ φq.finrank_negativeWeight_fun) : ℤ) *
        hX₀.pairSign hX₂ φp φr o₀ o₂ (by rw [hpqr, hq, zero_add]) y := by
  have hpr : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₂ r := by
    rw [hpqr, hq, zero_add]
  have := Module.finrank_zero_iff.1 (φq.finrank_negativeWeight_fun.trans hq)
  have : Unique ({i // φq.weight i < 0} → ℝ) := uniqueOfSubsingleton 0
  -- With no normal directions at `q`, the leaf at `r` alone receives the unstable directions.
  let e : ({i // φr.weight i < 0} → ℝ) ≃ₗ[ℝ]
      ({i // φq.weight i < 0} → ℝ) × ({i // φr.weight i < 0} → ℝ) :=
    LinearEquiv.uniqueProd.symm
  have h := Orientation.linearMapSign_map_map (o := o₀)
    (o' := Orientation.reindex ℝ _ (finCongr hpr.symm) o₂)
    (L := (hX₀.pairComparison hX₂ φp φr y).toLinearMap)
    (L' := (hX₀.morseYComparison hX₁ hX₂ φp φq φr y).toLinearMap) (LinearEquiv.refl ℝ _) e
    fun v ↦ Prod.ext (Subsingleton.elim _ _) (by simp [e])
  rw [Orientation.map_refl, Equiv.refl_apply] at h
  rw [morseYSign_def, Orientation.reindex_prod_of_left_eq_zero o₁ o₂
      φq.finrank_negativeWeight_fun φr.finrank_negativeWeight_fun hpqr.symm hpr.symm e
      fun _ ↦ Prod.ext (Subsingleton.elim _ _) (by simp [e]),
    Orientation.linearMapSign_units_smul_right (by
      rw [Fintype.card_fin, Module.finrank_prod, φq.finrank_negativeWeight_fun,
        φr.finrank_negativeWeight_fun, hpqr]), h, pairSign_def]

/-- **The sign of a Y-flow line whose second leaf ends at a critical point of index `0`.** If
`ind r = 0`, the sign of a point `y` of the Y-slice from `p` to `q` and `r` is the sign of the
orientation `o₂` at `r`, relative to the empty basis, times the sign of `y` as a point of
`W^u_{X₀}(p) ∩ W^s_{X₁}(q)`. -/
theorem morseYSign_of_morseIndex_eq_zero_right (hr : manifoldMorseIndex 𝓘(ℝ, E) f₂ r = 0)
    (y : M) :
    hX₀.morseYSign hX₁ hX₂ φp φq φr o₀ o₁ o₂ hpqr y =
      (o₂.signBasis (Module.finBasisOfFinrankEq ℝ _ φr.finrank_negativeWeight_fun) : ℤ) *
        hX₀.pairSign hX₁ φp φq o₀ o₁ (by rw [hpqr, hr, add_zero]) y := by
  have hpq : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q := by
    rw [hpqr, hr, add_zero]
  have := Module.finrank_zero_iff.1 (φr.finrank_negativeWeight_fun.trans hr)
  have : Unique ({i // φr.weight i < 0} → ℝ) := uniqueOfSubsingleton 0
  -- With no normal directions at `r`, the leaf at `q` alone receives the unstable directions.
  let e : ({i // φq.weight i < 0} → ℝ) ≃ₗ[ℝ]
      ({i // φq.weight i < 0} → ℝ) × ({i // φr.weight i < 0} → ℝ) :=
    LinearEquiv.prodUnique.symm
  have h := Orientation.linearMapSign_map_map (o := o₀)
    (o' := Orientation.reindex ℝ _ (finCongr hpq.symm) o₁)
    (L := (hX₀.pairComparison hX₁ φp φq y).toLinearMap)
    (L' := (hX₀.morseYComparison hX₁ hX₂ φp φq φr y).toLinearMap) (LinearEquiv.refl ℝ _) e
    fun v ↦ Prod.ext (by simp [e]) (Subsingleton.elim _ _)
  rw [Orientation.map_refl, Equiv.refl_apply] at h
  rw [morseYSign_def, Orientation.reindex_prod_of_right_eq_zero o₁ o₂
      φq.finrank_negativeWeight_fun φr.finrank_negativeWeight_fun hpqr.symm hpq.symm e
      fun _ ↦ Prod.ext (by simp [e]) (Subsingleton.elim _ _),
    Orientation.linearMapSign_units_smul_right (by
      rw [Fintype.card_fin, Module.finrank_prod, φq.finrank_negativeWeight_fun,
        φr.finrank_negativeWeight_fun, hpqr]), h, pairSign_def]

end Sign

/-! ### Splitting along the stable manifolds of the minima -/

/-- A finite set meeting no stable manifold of a critical point of positive index is the disjoint
union of its intersections with the stable manifolds of the critical points of index `0`, so a sum
over it splits along them. -/
private theorem finsum_mem_eq_finsum_mem_inter_stableSet {f : M → ℝ}
    {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hX : IsAdaptedPseudoGradient f X)
    (hf : IsMorse 𝓘(ℝ, E) f) {P : Set M} (hP : P.Finite)
    (hempty : ∀ c : criticalPoints 𝓘(ℝ, E) f, manifoldMorseIndex 𝓘(ℝ, E) f c ≠ 0 →
      P ∩ hX.flow.stableSet c = ∅) (F : M → ℤ) :
    ∑ᶠ y ∈ P, F y = ∑ᶠ m ∈ {m : criticalPoints 𝓘(ℝ, E) f | manifoldMorseIndex 𝓘(ℝ, E) f m = 0},
      ∑ᶠ y ∈ P ∩ hX.flow.stableSet m, F y := by
  have := hf.finite_criticalPoints.to_subtype
  have hP' : P = ⋃ m ∈ {m : criticalPoints 𝓘(ℝ, E) f | manifoldMorseIndex 𝓘(ℝ, E) f m = 0},
      P ∩ hX.flow.stableSet m := by
    refine Subset.antisymm (fun y hy ↦ ?_) (iUnion₂_subset fun _ _ ↦ inter_subset_left)
    -- The point `y` flows to a critical point, which must have index `0`.
    obtain ⟨c, hc, hyc⟩ := hX.exists_mem_stableSet y
    let c' : criticalPoints 𝓘(ℝ, E) f := ⟨c, mem_criticalPoints_iff_mfderiv_eq_zero.2 hc⟩
    by_cases h0 : manifoldMorseIndex 𝓘(ℝ, E) f c' = 0
    · exact mem_biUnion h0 ⟨hy, hyc⟩
    · exact absurd (hempty c' h0) (nonempty_of_mem (show y ∈ P ∩ hX.flow.stableSet c' from
        ⟨hy, hyc⟩)).ne_empty
  conv_lhs => rw [hP']
  exact finsum_mem_biUnion
    (fun m _ m' _ hmm' ↦ (Flow.disjoint_stableSet (Subtype.coe_injective.ne hmm')).mono
      inter_subset_right inter_subset_right)
    (toFinite _) fun _ _ ↦ hP.subset inter_subset_left

/-! ### The unit laws -/

section Unit

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  {hX₂ : IsAdaptedPseudoGradient f₂ X₂} {𝔬₀ : MorseOrientation f₀ X₀}
  {𝔬₁ : MorseOrientation f₁ X₁} {𝔬₂ : MorseOrientation f₂ X₂}

/-- **The augmentation of the diagonal coefficients at the first leaf is the signed pair count.**
Let `p` and `r` be critical points of `f₀` and `f₂`. Suppose that, when `ind p = ind r`, the
intersection `W^u_{X₀}(p) ∩ W^s_{X₂}(r)` is finite and the Y-slices from `p` to `c` and `r` are
empty at the critical points `c` of `f₁` of positive index. Then the coefficients of `m ⊗ r` in the
integral Morse diagonal of `p`, weighted by the augmentation signs of the critical points `m` of
`f₁`, add up to the signed count of `W^u_{X₀}(p) ∩ W^s_{X₂}(r)`. -/
theorem finsum_augmentationSign_mul_signedMorseDiagonalCoeff (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
    (p : criticalPoints 𝓘(ℝ, E) f₀) (r : criticalPoints 𝓘(ℝ, E) f₂)
    (hfin : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₂ r →
      (hX₀.flow.unstableSet p ∩ hX₂.flow.stableSet r).Finite)
    (hempty : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₂ r →
      ∀ c : criticalPoints 𝓘(ℝ, E) f₁, manifoldMorseIndex 𝓘(ℝ, E) f₁ c ≠ 0 →
        hX₀.morseYSlice hX₁ hX₂ p c r = ∅) :
    ∑ᶠ m, 𝔬₁.augmentationSign m * hX₀.signedMorseDiagonalCoeff hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ p m r =
      hX₀.signedPairCoeff hX₂ 𝔬₀ 𝔬₂ p r := by
  -- Only the critical points of index `0` have a nonzero augmentation sign.
  have hsupp : support (fun m ↦ 𝔬₁.augmentationSign m *
      hX₀.signedMorseDiagonalCoeff hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ p m r) ⊆
      {m | manifoldMorseIndex 𝓘(ℝ, E) f₁ m = 0} := fun m hm ↦ by_contra fun h ↦
    hm (by simp only [𝔬₁.augmentationSign_of_morseIndex_ne_zero h, zero_mul])
  rw [← finsum_mem_univ, finsum_mem_inter_support_eq' _ _ _ fun m hm ↦
    iff_of_true (mem_univ m) (hsupp hm)]
  -- The Y-slice at `c` is the part of `W^u_{X₀}(p) ∩ W^s_{X₂}(r)` flowing along `X₁` to `c`.
  have hslice : ∀ c : M, hX₀.morseYSlice hX₁ hX₂ p c r =
      hX₀.flow.unstableSet p ∩ hX₂.flow.stableSet r ∩ hX₁.flow.stableSet c := fun c ↦
    Set.ext fun y ↦ by simp only [mem_morseYSlice, mem_inter_iff]; tauto
  by_cases hpr : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₂ r
  · rw [signedPairCoeff_of_morseIndex_eq hpr, signedPairCount_def,
      finsum_mem_eq_finsum_mem_inter_stableSet hX₁ hf₁ (hfin hpr)
        (fun c hc ↦ by rw [← hempty hpr c hc, hslice])]
    refine finsum_mem_congr rfl fun m (hm : manifoldMorseIndex 𝓘(ℝ, E) f₁ m = 0) ↦ ?_
    have hpmr : manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
        manifoldMorseIndex 𝓘(ℝ, E) f₁ m + manifoldMorseIndex 𝓘(ℝ, E) f₂ r := by
      rw [hm, zero_add, hpr]
    -- Each Y-flow line with first leaf at `m` counts with the augmentation sign of `m` times its
    -- sign for the pair `(X₀, X₂)`, and the two augmentation signs cancel.
    rw [signedMorseDiagonalCoeff_eq_signedMorseYCount hpmr, signedMorseYCount_def,
      finsum_mem_congr rfl fun y _ ↦ morseYSign_of_morseIndex_eq_zero_left hm y,
      ← mul_finsum_mem, 𝔬₁.augmentationSign_of_morseIndex_eq_zero hm, ← mul_assoc,
      ← Units.val_mul, Int.units_mul_self, Units.val_one, one_mul, hslice]
  · rw [signedPairCoeff_eq_zero_of_morseIndex_ne hpr]
    refine finsum_mem_eq_zero_of_forall_eq_zero fun m (hm : _ = 0) ↦ ?_
    rw [signedMorseDiagonalCoeff_eq_zero_of_manifoldMorseIndex_ne (by omega), mul_zero]

/-- **The augmentation of the diagonal coefficients at the second leaf is the signed pair count.**
Let `p` and `q` be critical points of `f₀` and `f₁`. Suppose that, when `ind p = ind q`, the
intersection `W^u_{X₀}(p) ∩ W^s_{X₁}(q)` is finite and the Y-slices from `p` to `q` and `c` are
empty at the critical points `c` of `f₂` of positive index. Then the coefficients of `q ⊗ m` in the
integral Morse diagonal of `p`, weighted by the augmentation signs of the critical points `m` of
`f₂`, add up to the signed count of `W^u_{X₀}(p) ∩ W^s_{X₁}(q)`. -/
theorem finsum_augmentationSign_mul_signedMorseDiagonalCoeff_right (hf₂ : IsMorse 𝓘(ℝ, E) f₂)
    (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁)
    (hfin : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q →
      (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet q).Finite)
    (hempty : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q →
      ∀ c : criticalPoints 𝓘(ℝ, E) f₂, manifoldMorseIndex 𝓘(ℝ, E) f₂ c ≠ 0 →
        hX₀.morseYSlice hX₁ hX₂ p q c = ∅) :
    ∑ᶠ m, 𝔬₂.augmentationSign m * hX₀.signedMorseDiagonalCoeff hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ p q m =
      hX₀.signedPairCoeff hX₁ 𝔬₀ 𝔬₁ p q := by
  -- Only the critical points of index `0` have a nonzero augmentation sign.
  have hsupp : support (fun m ↦ 𝔬₂.augmentationSign m *
      hX₀.signedMorseDiagonalCoeff hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ p q m) ⊆
      {m | manifoldMorseIndex 𝓘(ℝ, E) f₂ m = 0} := fun m hm ↦ by_contra fun h ↦
    hm (by simp only [𝔬₂.augmentationSign_of_morseIndex_ne_zero h, zero_mul])
  rw [← finsum_mem_univ, finsum_mem_inter_support_eq' _ _ _ fun m hm ↦
    iff_of_true (mem_univ m) (hsupp hm)]
  -- The Y-slice at `c` is the part of `W^u_{X₀}(p) ∩ W^s_{X₁}(q)` flowing along `X₂` to `c`.
  have hslice : ∀ c : M, hX₀.morseYSlice hX₁ hX₂ p q c =
      hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet q ∩ hX₂.flow.stableSet c := fun c ↦
    Set.ext fun y ↦ by simp only [mem_morseYSlice, mem_inter_iff]; tauto
  by_cases hpq : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q
  · rw [signedPairCoeff_of_morseIndex_eq hpq, signedPairCount_def,
      finsum_mem_eq_finsum_mem_inter_stableSet hX₂ hf₂ (hfin hpq)
        (fun c hc ↦ by rw [← hempty hpq c hc, hslice])]
    refine finsum_mem_congr rfl fun m (hm : manifoldMorseIndex 𝓘(ℝ, E) f₂ m = 0) ↦ ?_
    have hpqm : manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
        manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ m := by
      rw [hm, add_zero, hpq]
    -- Each Y-flow line with second leaf at `m` counts with the augmentation sign of `m` times its
    -- sign for the pair `(X₀, X₁)`, and the two augmentation signs cancel.
    rw [signedMorseDiagonalCoeff_eq_signedMorseYCount hpqm, signedMorseYCount_def,
      finsum_mem_congr rfl fun y _ ↦ morseYSign_of_morseIndex_eq_zero_right hm y,
      ← mul_finsum_mem, 𝔬₂.augmentationSign_of_morseIndex_eq_zero hm, ← mul_assoc,
      ← Units.val_mul, Int.units_mul_self, Units.val_one, one_mul, hslice]
  · rw [signedPairCoeff_eq_zero_of_morseIndex_ne hpq]
    refine finsum_mem_eq_zero_of_forall_eq_zero fun m (hm : _ = 0) ↦ ?_
    rw [signedMorseDiagonalCoeff_eq_zero_of_manifoldMorseIndex_ne (by omega), mul_zero]

variable {R : Type*} [CommRing R]

/-- **The augmentation is a left unit for the integral Morse diagonal, up to the signed pair map.**
Suppose that, between critical points `p` of `f₀` and `r` of `f₂` with `ind p = ind r`, the
intersections `W^u_{X₀}(p) ∩ W^s_{X₂}(r)` are finite and the Y-slices from `p` to `c` and `r` are
empty at the critical points `c` of `f₁` of positive index. Then `(ε₁ ⊗ 1) ∘ Δ`, read in the
chains of `f₂`, is the signed pair map of `(X₀, X₂)`, with coefficients in any commutative ring. -/
theorem lid_comp_rTensor_signedMorseAugmentation_comp_signedMorseDiagonalMap
    (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (hf₂ : IsMorse 𝓘(ℝ, E) f₂)
    (hfin : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (r : criticalPoints 𝓘(ℝ, E) f₂),
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₂ r →
        (hX₀.flow.unstableSet p ∩ hX₂.flow.stableSet r).Finite)
    (hempty : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (r : criticalPoints 𝓘(ℝ, E) f₂),
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₂ r →
        ∀ c : criticalPoints 𝓘(ℝ, E) f₁, manifoldMorseIndex 𝓘(ℝ, E) f₁ c ≠ 0 →
          hX₀.morseYSlice hX₁ hX₂ p c r = ∅) :
    (TensorProduct.lid R (criticalPoints 𝓘(ℝ, E) f₂ →₀ R)).toLinearMap ∘ₗ
        (𝔬₁.signedMorseAugmentation R).rTensor _ ∘ₗ
          hX₀.signedMorseDiagonalMap hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R =
      hX₀.signedPairMap hX₂ 𝔬₀ 𝔬₂ hf₂ R := by
  have := hf₁.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f₁)
  refine Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun r ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, lid_rTensor_apply,
    signedPairMap_single_apply,
    ← finsum_augmentationSign_mul_signedMorseDiagonalCoeff (𝔬₁ := 𝔬₁) hf₁ p r (hfin p r)
      (hempty p r),
    finsum_eq_sum_of_fintype, Int.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [finsuppTensorFinsupp'_signedMorseDiagonalMap_single_apply,
    MorseOrientation.signedMorseAugmentation_single, one_mul, Int.cast_mul]
  ring

/-- **The augmentation is a right unit for the integral Morse diagonal, up to the signed pair
map.** Suppose that, between critical points `p` of `f₀` and `q` of `f₁` with `ind p = ind q`, the
intersections `W^u_{X₀}(p) ∩ W^s_{X₁}(q)` are finite and the Y-slices from `p` to `q` and `c` are
empty at the critical points `c` of `f₂` of positive index. Then `(1 ⊗ ε₂) ∘ Δ`, read in the
chains of `f₁`, is the signed pair map of `(X₀, X₁)`, with coefficients in any commutative ring. -/
theorem rid_comp_lTensor_signedMorseAugmentation_comp_signedMorseDiagonalMap
    (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (hf₂ : IsMorse 𝓘(ℝ, E) f₂)
    (hfin : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁),
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q →
        (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet q).Finite)
    (hempty : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁),
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q →
        ∀ c : criticalPoints 𝓘(ℝ, E) f₂, manifoldMorseIndex 𝓘(ℝ, E) f₂ c ≠ 0 →
          hX₀.morseYSlice hX₁ hX₂ p q c = ∅) :
    (TensorProduct.rid R (criticalPoints 𝓘(ℝ, E) f₁ →₀ R)).toLinearMap ∘ₗ
        (𝔬₂.signedMorseAugmentation R).lTensor _ ∘ₗ
          hX₀.signedMorseDiagonalMap hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R =
      hX₀.signedPairMap hX₁ 𝔬₀ 𝔬₁ hf₁ R := by
  have := hf₂.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f₂)
  refine Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun q ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, rid_lTensor_apply,
    signedPairMap_single_apply,
    ← finsum_augmentationSign_mul_signedMorseDiagonalCoeff_right (𝔬₂ := 𝔬₂) hf₂ p q
      (hfin p q) (hempty p q),
    finsum_eq_sum_of_fintype, Int.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [finsuppTensorFinsupp'_signedMorseDiagonalMap_single_apply,
    MorseOrientation.signedMorseAugmentation_single, one_mul, Int.cast_mul]
  ring

/-- **The augmentation is a left unit on the nose** when the root and the second leaf follow the
same Morse–Smale pseudo-gradient `X₀` with the same orientation data: if the Y-slices from `p` to
`c` and `r`, for `ind p = ind r`, are empty at the critical points `c` of `f₁` of positive index,
then `(ε₁ ⊗ 1) ∘ Δ` is the identity of the chains of `f₀`. -/
theorem IsMorseSmale.lid_comp_rTensor_signedMorseAugmentation_comp_signedMorseDiagonalMap_self
    (h₀ : hX₀.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
    (hempty : ∀ p r : criticalPoints 𝓘(ℝ, E) f₀,
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ r →
        ∀ c : criticalPoints 𝓘(ℝ, E) f₁, manifoldMorseIndex 𝓘(ℝ, E) f₁ c ≠ 0 →
          hX₀.morseYSlice hX₁ hX₀ p c r = ∅) :
    (TensorProduct.lid R (criticalPoints 𝓘(ℝ, E) f₀ →₀ R)).toLinearMap ∘ₗ
        (𝔬₁.signedMorseAugmentation R).rTensor _ ∘ₗ
          hX₀.signedMorseDiagonalMap hX₁ hX₀ 𝔬₀ 𝔬₁ 𝔬₀ hf₁ hf₀ R =
      LinearMap.id := by
  rw [lid_comp_rTensor_signedMorseAugmentation_comp_signedMorseDiagonalMap hf₁ hf₀
      (fun _ _ hpr ↦ ((isMorseSmalePair_self_iff hX₀).2 h₀).finite_unstableSet_inter_stableSet
        h₀ h₀ hf₀ hf₀ hpr.le) hempty,
    h₀.signedPairMap_self hf₀]

/-- **The augmentation is a right unit on the nose** when the root and the first leaf follow the
same Morse–Smale pseudo-gradient `X₀` with the same orientation data: if the Y-slices from `p` to
`q` and `c`, for `ind p = ind q`, are empty at the critical points `c` of `f₂` of positive index,
then `(1 ⊗ ε₂) ∘ Δ` is the identity of the chains of `f₀`. -/
theorem IsMorseSmale.rid_comp_lTensor_signedMorseAugmentation_comp_signedMorseDiagonalMap_self
    (h₀ : hX₀.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hf₂ : IsMorse 𝓘(ℝ, E) f₂)
    (hempty : ∀ p q : criticalPoints 𝓘(ℝ, E) f₀,
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ q →
        ∀ c : criticalPoints 𝓘(ℝ, E) f₂, manifoldMorseIndex 𝓘(ℝ, E) f₂ c ≠ 0 →
          hX₀.morseYSlice hX₀ hX₂ p q c = ∅) :
    (TensorProduct.rid R (criticalPoints 𝓘(ℝ, E) f₀ →₀ R)).toLinearMap ∘ₗ
        (𝔬₂.signedMorseAugmentation R).lTensor _ ∘ₗ
          hX₀.signedMorseDiagonalMap hX₀ hX₂ 𝔬₀ 𝔬₀ 𝔬₂ hf₀ hf₂ R =
      LinearMap.id := by
  rw [rid_comp_lTensor_signedMorseAugmentation_comp_signedMorseDiagonalMap hf₀ hf₂
      (fun _ _ hpq ↦ ((isMorseSmalePair_self_iff hX₀).2 h₀).finite_unstableSet_inter_stableSet
        h₀ h₀ hf₀ hf₀ hpq.le) hempty,
    h₀.signedPairMap_self hf₀]

end Unit

end IsAdaptedPseudoGradient

end TauCeti
