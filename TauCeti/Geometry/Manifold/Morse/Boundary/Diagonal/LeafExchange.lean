/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Diagonal.CupProduct
import TauCeti.LinearAlgebra.DirectSum.Finsupp

/-!
# Exchanging the leaves of Y-flow lines

Let `f₀`, `f₁` and `f₂` be Morse functions on a compact boundaryless manifold `M`, with
pseudo-gradients `X₀`, `X₁` and `X₂` adapted to them. A Y-flow line from a critical point `p` of
`f₀` to critical points `q` of `f₁` and `r` of `f₂` is recorded by its vertex, a point of the
Y-slice `W^u_{X₀}(p) ∩ W^s_{X₁}(q) ∩ W^s_{X₂}(r)`. Exchanging the two leaves, that is, the data
`(X₁, q)` and `(X₂, r)`, does not change the Y-slice
(`TauCeti.IsAdaptedPseudoGradient.morseYSlice_comm`). This file computes what the exchange does to
the Morse diagonal and the Morse cup product built from these slices.

**Modulo two** nothing changes: for any slice family `S`, the diagonal of the exchanged family
`(p, r, q) ↦ S p q r` is the diagonal of `S` followed by the exchange of the tensor factors
(`TauCeti.morseDiagonalMap_swap`), so the mod-two cup products satisfy `b ∪' a = a ∪ b`
(`TauCeti.morseCupProduct_swap`).

**Over the integers** the exchange introduces the Koszul sign. The sign of a vertex compares the
orientation of `W^u_{X₀}(p)` with the ordered product of the coorientations of `W^s_{X₁}(q)` and of
`W^s_{X₂}(r)`. Exchanging the leaves exchanges the factors of the comparison map
(`TauCeti.IsAdaptedPseudoGradient.morseYComparison_swap`), and exchanging the factors of a product
orientation of dimensions `ind q` and `ind r` multiplies it by `(-1) ^ (ind q * ind r)`
(`Orientation.map_prodComm_prod`). Hence the sign of each vertex, the signed count of each Y-slice
and each coefficient of the integral Morse diagonal are multiplied by `(-1) ^ (ind q * ind r)`
(`TauCeti.IsAdaptedPseudoGradient.morseYSign_swap`,
`TauCeti.IsAdaptedPseudoGradient.signedMorseYCount_swap`,
`TauCeti.IsAdaptedPseudoGradient.signedMorseDiagonalCoeff_swap`). For the integral cup products
`∪` of `(X₀; X₁, X₂)` and `∪'` of `(X₀; X₂, X₁)`, a linear form `a` of degree `k` on the Morse
chains of `f₁` and a linear form `b` of degree `l` on those of `f₂` satisfy

`b ∪' a = (-1) ^ (k * l) • a ∪ b`

(`TauCeti.IsAdaptedPseudoGradient.signedMorseCupProduct_swap_of_degree`). This is the chain-level
form of the graded commutativity of the cup product: the two products differ only in the order of
their leaf data, and comparing `∪'` with `∪` for the same Morse data needs continuation maps.

The exchange is compatible with the Koszul differentials of the two tensor products: the integral
diagonal of `(X₀; X₂, X₁)` is a chain map for `∂₂ ⊗ 1 + σ₂ ⊗ ∂₁` exactly when that of
`(X₀; X₁, X₂)` is a chain map for `∂₁ ⊗ 1 + σ₁ ⊗ ∂₂`, where `σᵢ` multiplies a critical point by
`(-1)` to the power of its index
(`TauCeti.IsAdaptedPseudoGradient.signedMorseDiagonalMap_swap_comp_signedMorseBoundary_eq_iff`).
So the graded Leibniz rule of either cup product implies that of the other. The proof uses that the
Morse boundaries lower the index by one.

## Main results

* `TauCeti.morseDiagonalMap_swap`, `TauCeti.morseCupProduct_swap`: the mod-two exchange.

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `morseYComparison_swap`: exchanging the leaves exchanges the factors of the comparison map.
* `morseYSign_swap`, `signedMorseYCount_swap`, `signedMorseDiagonalCoeff_swap`: the Koszul sign of
  the exchange.
* `finsuppTensorFinsupp'_signedMorseDiagonalMap_swap_apply`: the integral diagonal of the exchanged
  data, in coordinates.
* `signedMorseCupProduct_swap_of_degree`: the Koszul sign of the integral cup product.
* `signedMorseDiagonalMap_swap_comp_signedMorseBoundary_eq_iff`: the exchange preserves the chain
  map property of the integral diagonal.

## References

* S. Mescher, *Perturbed gradient flow trees and A∞-algebra structures in Morse cohomology*,
  arXiv:1611.07916, §§1–5 and Appendix A (Y-flow lines and their orientations).
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (signed counts).
-/

public section

open Function
open scoped ContDiff Manifold TensorProduct

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f₀ f₁ f₂ : M → ℝ} {X₀ X₁ X₂ : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-! ### The mod-two exchange -/

section ModTwo

variable {α : Type*} (S : M → M → M → Set α)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- **Exchanging the leaves of a mod-two diagonal coefficient.** The coefficient of `r ⊗ q` in the
image of `p` for the exchanged slice family `(p, r, q) ↦ S p q r` is the coefficient of `q ⊗ r` for
`S`. -/
theorem morseDiagonalCoeff_swap (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁)
    (r : criticalPoints 𝓘(ℝ, E) f₂) :
    morseDiagonalCoeff f₀ f₂ f₁ (fun p r q ↦ S p q r) p r q =
      morseDiagonalCoeff f₀ f₁ f₂ S p q r := by
  by_cases hpqr : manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r
  · rw [morseDiagonalCoeff_eq_ncard hpqr, morseDiagonalCoeff_eq_ncard (hpqr.trans (add_comm _ _))]
  · rw [morseDiagonalCoeff_eq_zero_of_manifoldMorseIndex_ne hpqr,
      morseDiagonalCoeff_eq_zero_of_manifoldMorseIndex_ne fun h ↦ hpqr (h.trans (add_comm _ _))]

variable (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (hf₂ : IsMorse 𝓘(ℝ, E) f₂)

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- **Exchanging the leaves of the mod-two Morse diagonal.** The mod-two Morse diagonal of the
exchanged slice family `(p, r, q) ↦ S p q r` is the diagonal of `S` followed by the exchange of
the tensor factors. -/
theorem morseDiagonalMap_swap :
    morseDiagonalMap f₀ hf₂ hf₁ (fun p r q ↦ S p q r) =
      (TensorProduct.comm (ZMod 2) _ _).toLinearMap ∘ₗ morseDiagonalMap f₀ hf₁ hf₂ S := by
  refine Finsupp.lhom_ext fun p a ↦
    (finsuppTensorFinsupp' (ZMod 2) _ _).injective <| Finsupp.ext fun ⟨r, q⟩ ↦ ?_
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, finsuppTensorFinsupp'_comm_apply,
    finsuppTensorFinsupp'_morseDiagonalMap_single_apply,
    finsuppTensorFinsupp'_morseDiagonalMap_single_apply, morseDiagonalCoeff_swap]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- **Exchanging the leaves of the mod-two cup product.** The mod-two cup product of `b` and `a`
for the exchanged slice family `(p, r, q) ↦ S p q r` is the cup product of `a` and `b` for `S`. For
the Y-slices of `(X₀; X₂, X₁)` and of `(X₀; X₁, X₂)`, which correspond under this exchange
(`TauCeti.IsAdaptedPseudoGradient.morseYSlice_comm`), the two mod-two cup products therefore
satisfy `b ∪' a = a ∪ b`. -/
theorem morseCupProduct_swap (a : (criticalPoints 𝓘(ℝ, E) f₁ →₀ ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (b : (criticalPoints 𝓘(ℝ, E) f₂ →₀ ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    morseCupProduct f₀ hf₂ hf₁ (fun p r q ↦ S p q r) b a = morseCupProduct f₀ hf₁ hf₂ S a b := by
  rw [morseCupProduct_apply, morseCupProduct_apply, morseDiagonalMap_swap]
  refine LinearMap.ext fun c ↦ ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.map_comm]
  exact LinearMap.congr_fun LinearMap.mul'_comp_comm _

end ModTwo

namespace IsAdaptedPseudoGradient

/-! ### The sign of an exchanged vertex -/

section Sign

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  {hX₂ : IsAdaptedPseudoGradient f₂ X₂} {p q r : M}
  {φp : MorseChart E f₀ p} {φq : MorseChart E f₁ q} {φr : MorseChart E f₂ r}

/-- **Exchanging the leaves exchanges the factors of the comparison map.** -/
theorem morseYComparison_swap (y : M) (v : {i // φp.weight i < 0} → ℝ) :
    hX₀.morseYComparison hX₂ hX₁ φp φr φq y v =
      (hX₀.morseYComparison hX₁ hX₂ φp φq φr y v).swap := by
  simp only [morseYComparison_apply, Prod.swap_prod_mk]

/-- **The Koszul sign of an exchanged vertex.** Exchanging the two leaves of a Y-flow line
multiplies the sign of its vertex by `(-1) ^ (ind q * ind r)`: exchanging the factors of the
comparison map moves each of the `ind q` coordinates of the first leaf past the `ind r` coordinates
of the second. -/
theorem morseYSign_swap
    (o₀ : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₀ p)))
    (o₁ : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₁ q)))
    (o₂ : Orientation ℝ ({i // φr.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₂ r)))
    (hpqr : manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r) (y : M) :
    hX₀.morseYSign hX₂ hX₁ φp φr φq o₀ o₂ o₁ (hpqr.trans (add_comm _ _)) y =
      (-1) ^ (manifoldMorseIndex 𝓘(ℝ, E) f₁ q * manifoldMorseIndex 𝓘(ℝ, E) f₂ r) *
        hX₀.morseYSign hX₁ hX₂ φp φq φr o₀ o₁ o₂ hpqr y := by
  set k := manifoldMorseIndex 𝓘(ℝ, E) f₁ q * manifoldMorseIndex 𝓘(ℝ, E) f₂ r
  -- Transporting the target orientation along the exchange of factors gives the exchanged product
  -- orientation scaled by `(-1) ^ k`.
  have hmap : Orientation.map _ (LinearEquiv.prodComm ℝ _ _)
      (Orientation.reindex ℝ _ (finCongr hpqr.symm)
        (o₁.prod o₂ φq.finrank_negativeWeight_fun φr.finrank_negativeWeight_fun)) =
      Units.map (Int.castRingHom ℝ).toMonoidHom ((-1) ^ k) •
        Orientation.reindex ℝ _ (finCongr (hpqr.trans (add_comm _ _)).symm)
          (o₂.prod o₁ φr.finrank_negativeWeight_fun φq.finrank_negativeWeight_fun) := by
    rw [Orientation.map_reindex, Orientation.map_prodComm_prod, Orientation.reindex_units_smul,
      Orientation.reindex_finCongr_reindex_finCongr]
    congr 1
    ext
    simp [k]
  have h := Orientation.linearMapSign_map_map (o := o₀)
    (o' := Orientation.reindex ℝ _ (finCongr hpqr.symm)
      (o₁.prod o₂ φq.finrank_negativeWeight_fun φr.finrank_negativeWeight_fun))
    (LinearEquiv.refl ℝ _)
    (LinearEquiv.prodComm ℝ _ _) (L' := (hX₀.morseYComparison hX₂ hX₁ φp φr φq y).toLinearMap)
    fun v ↦ morseYComparison_swap y v
  rw [Orientation.map_refl, Equiv.refl_apply, hmap,
    Orientation.linearMapSign_units_smul_right (by
      rw [Fintype.card_fin, Module.finrank_prod, φr.finrank_negativeWeight_fun,
        φq.finrank_negativeWeight_fun, hpqr, add_comm])] at h
  rw [morseYSign_def, morseYSign_def, ← h, ← mul_assoc, Units.val_pow_eq_pow_val, Units.val_neg,
    Units.val_one, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

/-- **The Koszul sign of an exchanged Y-slice.** Exchanging the two leaves multiplies the signed
count of the Y-slice by `(-1) ^ (ind q * ind r)`. -/
theorem signedMorseYCount_swap
    (o₀ : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₀ p)))
    (o₁ : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₁ q)))
    (o₂ : Orientation ℝ ({i // φr.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₂ r)))
    (hpqr : manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r) :
    hX₀.signedMorseYCount hX₂ hX₁ φp φr φq o₀ o₂ o₁ (hpqr.trans (add_comm _ _)) =
      (-1) ^ (manifoldMorseIndex 𝓘(ℝ, E) f₁ q * manifoldMorseIndex 𝓘(ℝ, E) f₂ r) *
        hX₀.signedMorseYCount hX₁ hX₂ φp φq φr o₀ o₁ o₂ hpqr := by
  rw [signedMorseYCount_def, signedMorseYCount_def, morseYSlice_comm,
    finsum_mem_congr rfl fun y _ ↦ morseYSign_swap o₀ o₁ o₂ hpqr y]
  rcases neg_one_pow_eq_or ℤ (manifoldMorseIndex 𝓘(ℝ, E) f₁ q *
    manifoldMorseIndex 𝓘(ℝ, E) f₂ r) with h | h <;>
    simp only [h, one_mul, neg_one_mul, finsum_neg_distrib]

end Sign

/-! ### The integral Morse diagonal and cup product -/

section Map

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  {hX₂ : IsAdaptedPseudoGradient f₂ X₂} {𝔬₀ : MorseOrientation f₀ X₀}
  {𝔬₁ : MorseOrientation f₁ X₁} {𝔬₂ : MorseOrientation f₂ X₂}

/-- **The Koszul sign of an exchanged diagonal coefficient.** The coefficient of `r ⊗ q` in the
image of `p` under the integral Morse diagonal of `(X₀; X₂, X₁)` is `(-1) ^ (ind q * ind r)` times
the coefficient of `q ⊗ r` under that of `(X₀; X₁, X₂)`. -/
theorem signedMorseDiagonalCoeff_swap (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁) (r : criticalPoints 𝓘(ℝ, E) f₂) :
    hX₀.signedMorseDiagonalCoeff hX₂ hX₁ 𝔬₀ 𝔬₂ 𝔬₁ p r q =
      (-1) ^ (manifoldMorseIndex 𝓘(ℝ, E) f₁ q * manifoldMorseIndex 𝓘(ℝ, E) f₂ r) *
        hX₀.signedMorseDiagonalCoeff hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ p q r := by
  by_cases hpqr : manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r
  · rw [signedMorseDiagonalCoeff_eq_signedMorseYCount hpqr,
      signedMorseDiagonalCoeff_eq_signedMorseYCount (hpqr.trans (add_comm _ _)),
      signedMorseYCount_swap]
  · rw [signedMorseDiagonalCoeff_eq_zero_of_manifoldMorseIndex_ne hpqr,
      signedMorseDiagonalCoeff_eq_zero_of_manifoldMorseIndex_ne
        fun h ↦ hpqr (h.trans (add_comm _ _)), mul_zero]

variable (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (hf₂ : IsMorse 𝓘(ℝ, E) f₂) {R : Type*} [CommRing R]

/-- **The integral Morse diagonal of the exchanged data in coordinates.** The coefficient of
`r ⊗ q` in the image of a chain `c` under the integral Morse diagonal of `(X₀; X₂, X₁)` is
`(-1) ^ (ind q * ind r)` times the coefficient of `q ⊗ r` in its image under that of
`(X₀; X₁, X₂)`: the exchanged diagonal is the original one followed by the Koszul braiding
`q ⊗ r ↦ (-1) ^ (ind q * ind r) r ⊗ q`. -/
theorem finsuppTensorFinsupp'_signedMorseDiagonalMap_swap_apply
    (c : criticalPoints 𝓘(ℝ, E) f₀ →₀ R) (q : criticalPoints 𝓘(ℝ, E) f₁)
    (r : criticalPoints 𝓘(ℝ, E) f₂) :
    finsuppTensorFinsupp' R _ _ (hX₀.signedMorseDiagonalMap hX₂ hX₁ 𝔬₀ 𝔬₂ 𝔬₁ hf₂ hf₁ R c) (r, q) =
      (-1) ^ (manifoldMorseIndex 𝓘(ℝ, E) f₁ q * manifoldMorseIndex 𝓘(ℝ, E) f₂ r) *
        finsuppTensorFinsupp' R _ _ (hX₀.signedMorseDiagonalMap hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R c)
          (q, r) := by
  rw [finsuppTensorFinsupp'_signedMorseDiagonalMap_apply,
    finsuppTensorFinsupp'_signedMorseDiagonalMap_apply, Finsupp.mul_sum]
  refine Finsupp.sum_congr fun p _ ↦ ?_
  rw [signedMorseDiagonalCoeff_swap]
  push_cast
  ring

/-- **The Koszul sign of the integral cup product.** Let `∪` be the integral Morse cup product of
`(X₀; X₁, X₂)` and `∪'` that of `(X₀; X₂, X₁)`. For a linear form `a` of degree `k` on the Morse
chains of `f₁`, vanishing on the critical points of index other than `k`, and a linear form `b` of
degree `l` on those of `f₂`, `b ∪' a = (-1) ^ (k * l) • a ∪ b`. -/
theorem signedMorseCupProduct_swap_of_degree {k l : ℕ}
    {a : (criticalPoints 𝓘(ℝ, E) f₁ →₀ R) →ₗ[R] R} {b : (criticalPoints 𝓘(ℝ, E) f₂ →₀ R) →ₗ[R] R}
    (ha : ∀ q : criticalPoints 𝓘(ℝ, E) f₁, manifoldMorseIndex 𝓘(ℝ, E) f₁ q ≠ k →
      a (Finsupp.single q 1) = 0)
    (hb : ∀ r : criticalPoints 𝓘(ℝ, E) f₂, manifoldMorseIndex 𝓘(ℝ, E) f₂ r ≠ l →
      b (Finsupp.single r 1) = 0) :
    hX₀.signedMorseCupProduct hX₂ hX₁ 𝔬₀ 𝔬₂ 𝔬₁ hf₂ hf₁ R b a =
      (-1 : ℤ) ^ (k * l) • hX₀.signedMorseCupProduct hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R a b := by
  have := hf₁.finite_criticalPoints.to_subtype
  have := hf₂.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f₁)
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f₂)
  refine Finsupp.lhom_ext' fun p ↦ LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, Finsupp.lsingle_apply]
  rw [signedMorseCupProduct_apply_single, signedMorseCupProduct_apply_single, Finset.smul_sum,
    ← (Equiv.prodComm _ _).sum_comp]
  refine Finset.sum_congr rfl fun ⟨q, r⟩ _ ↦ ?_
  rw [Equiv.prodComm_apply, Prod.swap_prod_mk, signedMorseDiagonalCoeff_swap, zsmul_eq_mul]
  -- A term survives only if `ind q = k` and `ind r = l`, where the two signs agree.
  by_cases hq : manifoldMorseIndex 𝓘(ℝ, E) f₁ q = k
  · by_cases hr : manifoldMorseIndex 𝓘(ℝ, E) f₂ r = l
    · rw [hq, hr]
      push_cast
      ring
    · simp [hb r hr]
  · simp [ha q hq]

end Map

/-! ### Compatibility with the Koszul differentials -/

section Differential

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  {hX₂ : IsAdaptedPseudoGradient f₂ X₂} {𝔬₀ : MorseOrientation f₀ X₀}
  {𝔬₁ : MorseOrientation f₁ X₁} {𝔬₂ : MorseOrientation f₂ X₂}
  {hf₀ : IsMorse 𝓘(ℝ, E) f₀} {hf₁ : IsMorse 𝓘(ℝ, E) f₁} {hf₂ : IsMorse 𝓘(ℝ, E) f₂}
  {R : Type*} [CommRing R]

/-- The Koszul signs of the two orders of the leaves agree across a boundary coefficient: when the
coefficient of `q` in the Morse boundary of `q'` is nonzero, `ind q' = ind q + 1`, so that
`(-1) ^ (ind q * n)` is `(-1) ^ n * (-1) ^ (ind q' * n)`. -/
private theorem neg_one_pow_mul_boundary_eq (q q' : criticalPoints 𝓘(ℝ, E) f₁) (n : ℕ) (t : R) :
    (-1) ^ (manifoldMorseIndex 𝓘(ℝ, E) f₁ q * n) *
        (t * hX₁.signedMorseBoundary 𝔬₁ hf₁ R (Finsupp.single q' 1) q) =
      (-1) ^ n * ((-1) ^ (manifoldMorseIndex 𝓘(ℝ, E) f₁ q' * n) *
        (t * hX₁.signedMorseBoundary 𝔬₁ hf₁ R (Finsupp.single q' 1) q)) := by
  rw [signedMorseBoundary_single_apply, one_mul]
  by_cases h : manifoldMorseIndex 𝓘(ℝ, E) f₁ q' = manifoldMorseIndex 𝓘(ℝ, E) f₁ q + 1
  · have hsq : (-1 : R) ^ n * (-1) ^ n = 1 := by rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
    rw [h, add_mul, one_mul, pow_add]
    linear_combination (-((-1 : R) ^ (manifoldMorseIndex 𝓘(ℝ, E) f₁ q * n) *
      (t * hX₁.signedMorseBoundaryCoeff 𝔬₁ q' q))) * hsq
  · rw [signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one h]
    simp

/-- One direction of `signedMorseDiagonalMap_swap_comp_signedMorseBoundary_eq_iff`. -/
private theorem signedMorseDiagonalMap_swap_comp_signedMorseBoundary_eq
    (h : hX₀.signedMorseDiagonalMap hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R ∘ₗ
        hX₀.signedMorseBoundary 𝔬₀ hf₀ R =
      ((hX₁.signedMorseBoundary 𝔬₁ hf₁ R).rTensor _ +
          TensorProduct.map
            (Finsupp.signEquiv (A := R) R fun q : criticalPoints 𝓘(ℝ, E) f₁ ↦
              (-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f₁ q).toLinearMap
            (hX₂.signedMorseBoundary 𝔬₂ hf₂ R)) ∘ₗ
        hX₀.signedMorseDiagonalMap hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R) :
    hX₀.signedMorseDiagonalMap hX₂ hX₁ 𝔬₀ 𝔬₂ 𝔬₁ hf₂ hf₁ R ∘ₗ
        hX₀.signedMorseBoundary 𝔬₀ hf₀ R =
      ((hX₂.signedMorseBoundary 𝔬₂ hf₂ R).rTensor _ +
          TensorProduct.map
            (Finsupp.signEquiv (A := R) R fun r : criticalPoints 𝓘(ℝ, E) f₂ ↦
              (-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f₂ r).toLinearMap
            (hX₁.signedMorseBoundary 𝔬₁ hf₁ R)) ∘ₗ
        hX₀.signedMorseDiagonalMap hX₂ hX₁ 𝔬₀ 𝔬₂ 𝔬₁ hf₂ hf₁ R := by
  have := hf₁.finite_criticalPoints.to_subtype
  have := hf₂.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f₁)
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f₂)
  refine Finsupp.lhom_ext fun p a ↦
    (finsuppTensorFinsupp' R _ _).injective <| Finsupp.ext fun ⟨r, q⟩ ↦ ?_
  have hqr := congr(finsuppTensorFinsupp' R _ _ ($h (Finsupp.single p a)) (q, r))
  simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add, Finsupp.add_apply,
    finsuppTensorFinsupp'_rTensor_apply, finsuppTensorFinsupp'_map_signEquiv_apply,
    finsuppTensorFinsupp'_lTensor_apply] at hqr ⊢
  -- Read every coefficient of the exchanged diagonal off the original one, then match the terms
  -- of the two Koszul differentials one boundary coefficient at a time.
  simp only [finsuppTensorFinsupp'_signedMorseDiagonalMap_swap_apply (hX₁ := hX₁) (hX₂ := hX₂),
    hqr, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, Int.cast_pow, Int.cast_neg,
    Int.cast_one, mul_add, Finset.mul_sum]
  have hsq : (-1 : R) ^ manifoldMorseIndex 𝓘(ℝ, E) f₁ q * (-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f₁ q =
      1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  rw [add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun r' _ ↦ ?_
    linear_combination (-1 : R) ^ manifoldMorseIndex 𝓘(ℝ, E) f₁ q *
        neg_one_pow_mul_boundary_eq r r' (manifoldMorseIndex 𝓘(ℝ, E) f₁ q)
          (finsuppTensorFinsupp' R _ _
            (hX₀.signedMorseDiagonalMap hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R (Finsupp.single p a)) (q, r')) +
      (-1) ^ (manifoldMorseIndex 𝓘(ℝ, E) f₂ r' * manifoldMorseIndex 𝓘(ℝ, E) f₁ q) *
        (finsuppTensorFinsupp' R _ _
            (hX₀.signedMorseDiagonalMap hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R (Finsupp.single p a)) (q, r') *
          hX₂.signedMorseBoundary 𝔬₂ hf₂ R (Finsupp.single r' 1) r) * hsq
  · refine Finset.sum_congr rfl fun q' _ ↦ ?_
    rw [neg_one_pow_mul_boundary_eq q q']
    ring

/-- **Exchanging the leaves preserves the chain map property of the integral diagonal.** For the
parity signs `σ₁` and `σ₂`, which multiply a critical point by `(-1)` to the power of its index,
the integral Morse diagonal of `(X₀; X₂, X₁)` is a chain map for the Koszul differential
`∂₂ ⊗ 1 + σ₂ ⊗ ∂₁` exactly when that of `(X₀; X₁, X₂)` is a chain map for `∂₁ ⊗ 1 + σ₁ ⊗ ∂₂`. By
`signedMorseCupProduct_comp_signedMorseBoundary_eq_iff_signedMorseDiagonalMap_comp_eq`, the
graded Leibniz rule of either integral cup product therefore implies that of the other. -/
theorem signedMorseDiagonalMap_swap_comp_signedMorseBoundary_eq_iff :
    hX₀.signedMorseDiagonalMap hX₂ hX₁ 𝔬₀ 𝔬₂ 𝔬₁ hf₂ hf₁ R ∘ₗ
        hX₀.signedMorseBoundary 𝔬₀ hf₀ R =
      ((hX₂.signedMorseBoundary 𝔬₂ hf₂ R).rTensor _ +
          TensorProduct.map
            (Finsupp.signEquiv (A := R) R fun r : criticalPoints 𝓘(ℝ, E) f₂ ↦
              (-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f₂ r).toLinearMap
            (hX₁.signedMorseBoundary 𝔬₁ hf₁ R)) ∘ₗ
        hX₀.signedMorseDiagonalMap hX₂ hX₁ 𝔬₀ 𝔬₂ 𝔬₁ hf₂ hf₁ R ↔
    hX₀.signedMorseDiagonalMap hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R ∘ₗ
        hX₀.signedMorseBoundary 𝔬₀ hf₀ R =
      ((hX₁.signedMorseBoundary 𝔬₁ hf₁ R).rTensor _ +
          TensorProduct.map
            (Finsupp.signEquiv (A := R) R fun q : criticalPoints 𝓘(ℝ, E) f₁ ↦
              (-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f₁ q).toLinearMap
            (hX₂.signedMorseBoundary 𝔬₂ hf₂ R)) ∘ₗ
        hX₀.signedMorseDiagonalMap hX₁ hX₂ 𝔬₀ 𝔬₁ 𝔬₂ hf₁ hf₂ R :=
  ⟨signedMorseDiagonalMap_swap_comp_signedMorseBoundary_eq,
    signedMorseDiagonalMap_swap_comp_signedMorseBoundary_eq⟩

end Differential

end IsAdaptedPseudoGradient

end TauCeti
