/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Sphere
public import TauCeti.Geometry.Manifold.Morse.Cell.Map

/-!
# Attaching maps of Morse cells in homology under a change of chart

Let `ψ₀` and `ψ₁` be two normal-form charts of index `m + 1` at a critical point of a function
`f`, with characteristic maps `χ₀, χ₁ : (D^{m+1}, ∂D^{m+1}) → (M_{c+ε}, M_{c-ε})` and attaching
maps `α₀, α₁ : ∂D^{m+1} → M_{c-ε}`, where `M_a = {f ≤ a}`. In Milnor's comparison of the two
charts, the characteristic maps are related by a homotopy of maps of pairs from `χ₁` to `χ₀ ∘ g`
for an orthogonal map `g` of `ℝ^{m+1}`, the polar factor of the negative block of the derivative
of the transition. On the boundary sphere such a homotopy is a homotopy from `α₁` to `α₀ ∘ g`
(`TauCeti.homotopic_morseAttachingMap_diskBoundaryMap_comp`).

The boundary map of `g` has degree `sign (det g) = ±1`: it acts on the reduced homology
`H_redₘ(∂D^{m+1})` by that sign (`TauCeti.reducedSingularHomologyFunctor_map_diskBoundaryMap`). So
the maps induced by the two attaching maps on reduced homology, with coefficients in any abelian
category with coproducts, differ by the sign of `det g`
(`TauCeti.reducedSingularHomologyFunctor_map_morseAttachingMap_eq_sign_det_smul`). In particular,
an orientation-reversing change of chart, `det g = -1`, changes the sign of the attaching map in
homology (`TauCeti.reducedSingularHomologyFunctor_map_morseAttachingMap_of_det_eq_neg_one`), and an
orientation-preserving one does not. This holds in every index `m + 1 ≥ 1`. For index `1` the
sphere `∂D¹` consists of two points, `g = -1`, and the attaching maps are related by the swap of
the two points (`TauCeti.homotopic_morseAttachingMap_diskBoundaryNeg_comp_of_det_eq_neg_one`); on
`H_red₀(∂D¹)` the swap acts by `-1`.

## Main results

* `TauCeti.reducedSingularHomologyFunctor_map_morseAttachingMap_eq_sign_det_smul`: the attaching
  maps of two charts related by `g` agree on reduced homology up to the sign of `det g`.
* `TauCeti.reducedSingularHomologyFunctor_map_morseAttachingMap_of_det_eq_neg_one`: if
  `det g = -1`, the attaching maps induce opposite maps on reduced homology.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.2 and Remark 3.3.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.2, properties of
  the degree.
-/

public section

open CategoryTheory Limits Metric

universe u v w

namespace TauCeti

variable {C : Type w} [Category.{v} C] [HasCoproducts.{u} C] [Abelian C] (R : C)
  {M : Type u} [TopologicalSpace M] {n m : ℕ} {f : M → ℝ} {c ε : ℝ}
  {ψ₀ ψ₁ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} (hk : m + 1 ≤ n)
  (hε : 0 ≤ ε) (hball₀ : closedBall 0 √ε ⊆ ψ₀.target) (hball₁ : closedBall 0 √ε ⊆ ψ₁.target)
  (hf₀ : ∀ y ∈ ψ₀.source, f y = c + ∑ j, (if j.val < m + 1 then -1 else 1) * ψ₀ y j ^ 2)
  (hf₁ : ∀ y ∈ ψ₁.source, f y = c + ∑ j, (if j.val < m + 1 then -1 else 1) * ψ₁ y j ^ 2)
  {g : EuclideanSpace ℝ (Fin (m + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m + 1))}

/-- **A change of chart multiplies the attaching map in homology by the sign of its orientation.**
Let `χ₀` and `χ₁` be the characteristic maps of the cells of two normal-form charts of index
`m + 1`, and suppose `χ₁` is homotopic, as a map of pairs into `(M_{c+ε}, M_{c-ε})`, to `χ₀ ∘ g`
for a linear isometry `g` of `ℝ^{m+1}`. Then the attaching maps `α₀, α₁ : ∂D^{m+1} → M_{c-ε}`
satisfy `α₁_* = sign (det g) • α₀_*` on the reduced homology `H_redₘ`. -/
theorem reducedSingularHomologyFunctor_map_morseAttachingMap_eq_sign_det_smul
    (K : (ψ₁.morseCharacteristicMap hk hε hball₁ hf₁).hom.Homotopy
      (g.diskMap ≫ ψ₀.morseCharacteristicMap hk hε hball₀ hf₀).hom)
    (hK : ∀ t (s : TopCat.diskBoundary.{u} (m + 1)),
      f (K (t, TopCat.diskBoundaryInclusion (m + 1) s)) ≤ c - ε) :
    (reducedSingularHomologyFunctor R m).map (ψ₁.morseAttachingMap hk hε hball₁ hf₁) =
      (SignType.sign (LinearMap.det g.toLinearMap) : ℤ) •
        (reducedSingularHomologyFunctor R m).map (ψ₀.morseAttachingMap hk hε hball₀ hf₀) := by
  rw [reducedSingularHomologyFunctor_map_eq_of_homotopy R
      (homotopic_morseAttachingMap_diskBoundaryMap_comp hk hε hball₀ hball₁ hf₀ hf₁ K hK).some m,
    Functor.map_comp, reducedSingularHomologyFunctor_map_diskBoundaryMap, Preadditive.zsmul_comp,
    Category.id_comp]

/-- **An orientation-reversing change of chart negates the attaching map in homology.** Let `χ₀`
and `χ₁` be the characteristic maps of the cells of two normal-form charts of index `m + 1`, and
suppose `χ₁` is homotopic, as a map of pairs into `(M_{c+ε}, M_{c-ε})`, to `χ₀ ∘ g` for a linear
isometry `g` of `ℝ^{m+1}` with `det g = -1`. Then the attaching maps
`α₀, α₁ : ∂D^{m+1} → M_{c-ε}` induce opposite maps `α₁_* = -α₀_*` on the reduced homology `H_redₘ`:
the boundary map of `g` has degree `-1`. -/
theorem reducedSingularHomologyFunctor_map_morseAttachingMap_of_det_eq_neg_one
    (hg : LinearMap.det g.toLinearMap = -1)
    (K : (ψ₁.morseCharacteristicMap hk hε hball₁ hf₁).hom.Homotopy
      (g.diskMap ≫ ψ₀.morseCharacteristicMap hk hε hball₀ hf₀).hom)
    (hK : ∀ t (s : TopCat.diskBoundary.{u} (m + 1)),
      f (K (t, TopCat.diskBoundaryInclusion (m + 1) s)) ≤ c - ε) :
    (reducedSingularHomologyFunctor R m).map (ψ₁.morseAttachingMap hk hε hball₁ hf₁) =
      -(reducedSingularHomologyFunctor R m).map (ψ₀.morseAttachingMap hk hε hball₀ hf₀) := by
  rw [reducedSingularHomologyFunctor_map_morseAttachingMap_eq_sign_det_smul R hk hε hball₀ hball₁
    hf₀ hf₁ K hK, hg]
  simp

end TauCeti
