/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Circle
public import TauCeti.Geometry.Manifold.Morse.Boundary.Continuation.ExtremeIndex

/-!
# The integral continuation maps of the circle examples along a near-rotation

On the circle `S¹ = ℝ ⧸ 2πℤ`, let `X₀` and `X₁` be pseudo-gradients adapted to the functions
`f₀ = δ₀ cos (2 (θ - r₀))` and `f₁ = δ₁ cos (2 (θ - r₁))` (`TauCeti.circleCosTwo`), with orientation
data `𝔬₀` and `𝔬₁`, and let `Φ` be a diffeomorphism of the circle. This file computes every
coefficient of the integral continuation map along `Φ`
(`TauCeti.IsAdaptedPseudoGradient.signedContinuationMap`) when `Φ` is close to a rotation at the
critical points. For a continuation field, the integral continuation map is taken along its
transition diffeomorphisms (`TauCeti.continuationTransition`).

Every critical point has index `0` or `1 = dim S¹`, so the coefficients are given by
`TauCeti.IsAdaptedPseudoGradient.signedContinuationCoeff_of_morseIndex_eq_zero` and
`TauCeti.IsAdaptedPseudoGradient.signedContinuationCoeff_of_morseIndex_eq_finrank`: between minima,
the coefficient of `q` in the image of `p` is the product of the augmentation signs when `Φ p` lies
on the stable manifold of `q` for `X₁`, and between maxima it is the product of the fundamental
signs when `Φ⁻¹ q` lies on the unstable manifold of `p` for `X₀`. For every adapted
pseudo-gradient these manifolds are open arcs of length `π`
(`TauCeti.IsAdaptedPseudoGradient.coe_mem_stableSet_circleCosTwo_of_mem_Ioo`,
`TauCeti.IsAdaptedPseudoGradient.coe_mem_unstableSet_circleCosTwo_of_mem_Ioo`).

Let `n` be an integer and `c = r₁ - r₀ - n π`, so that rotation by `c` carries the critical points
of `f₀` to those of `f₁`, preserving their indices. Suppose that `Φ` moves each minimum `p` of `f₀`
to within `π / 2` of `p + c`, and `Φ⁻¹` moves each maximum `q` of `f₁` to within `π / 2` of `q - c`.
Then the coefficient of `q` in the image of `p` is the product of the signs of `p` and `q` when
`q = p + c`, and `0` otherwise
(`TauCeti.IsAdaptedPseudoGradient.signedContinuationCoeff_circleCosTwo`).
This has the shape of the mod-two count `TauCeti.morseContinuationCoeff_circleCylinderField` of
the circle continuation examples. For the half-turn `r₁ = r₀ + π`, where `f₁ = f₀`
(`TauCeti.circleCosTwo_add_pi`), a diffeomorphism satisfying the hypotheses with `n = 1`, so
`c = 0`, sends each critical point to itself with the weight of the signs: in the fixed spatial
basis the matrix is diagonal, while in the labels `p_j(r₀) ↦ p_j(r₀ + π)` tracked along the path it
is the exchange `S` (`TauCeti.circleCosTwoMax_add_pi`, `TauCeti.circleCosTwoMin_add_pi`).

## Main results

* `TauCeti.IsAdaptedPseudoGradient.signedContinuationCoeff_circleCosTwoMaxCrit`,
  `TauCeti.IsAdaptedPseudoGradient.signedContinuationCoeff_circleCosTwoMinCrit`: the coefficients
  between maxima and between minima.
* `TauCeti.IsAdaptedPseudoGradient.signedContinuationCoeff_circleCosTwo`: all the integral
  continuation coefficients along a diffeomorphism close to the rotation by `c` at the critical
  points.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.1–4.2 (continuation maps over `ℤ`).
-/

public section

open Module Set
open scoped Manifold ContDiff Real

namespace TauCeti

local instance signedContinuationCircleTwoPiPos : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

namespace IsAdaptedPseudoGradient

variable {δ₀ δ₁ r₀ r₁ : ℝ} {X₀ X₁ : (x : AddCircle (2 * π)) → TangentSpace 𝓘(ℝ) x}
  (hX₀ : IsAdaptedPseudoGradient (circleCosTwo δ₀ r₀) X₀)
  (hX₁ : IsAdaptedPseudoGradient (circleCosTwo δ₁ r₁) X₁)
  (𝔬₀ : MorseOrientation (circleCosTwo δ₀ r₀) X₀) (𝔬₁ : MorseOrientation (circleCosTwo δ₁ r₁) X₁)
  (Φ : AddCircle (2 * π) ≃ₘ^∞⟮𝓘(ℝ), 𝓘(ℝ)⟯ AddCircle (2 * π))

/-- The rotation of the maximum `p_i(r₀)` by `r₁ - r₀ - n π` is a maximum of `f₁`. -/
private theorem exists_circleCosTwoMax_eq_add (n : ℤ) (i : Fin 2) :
    ∃ k, circleCosTwoMax r₁ k =
      circleCosTwoMax r₀ i + ((r₁ - r₀ - n * π : ℝ) : AddCircle (2 * π)) := by
  obtain ⟨k, hk⟩ := exists_circleCosTwoMax_eq r₁ ((i : ℕ) - n)
  refine ⟨k, ?_⟩
  rw [hk, circleCosTwoMax_def, ← AddCircle.coe_add]
  congr 1
  push_cast
  ring

/-- The rotation of the minimum `q_i(r₀)` by `r₁ - r₀ - n π` is a minimum of `f₁`. -/
private theorem exists_circleCosTwoMin_eq_add (n : ℤ) (i : Fin 2) :
    ∃ k, circleCosTwoMin r₁ k =
      circleCosTwoMin r₀ i + ((r₁ - r₀ - n * π : ℝ) : AddCircle (2 * π)) := by
  obtain ⟨k, hk⟩ := exists_circleCosTwoMin_eq r₁ ((i : ℕ) - n)
  refine ⟨k, ?_⟩
  rw [hk, circleCosTwoMin_def, ← AddCircle.coe_add]
  congr 1
  push_cast
  ring

open scoped Classical in
/-- **The integral continuation coefficients between maxima.** Let `n` be an integer, and let the
inverse of `Φ` move the maximum `p_j(r₁)` of `f₁` to `p_j(r₁) - c - e`, where
`c = r₁ - r₀ - n π` and `|e| < π / 2`, and preserve an orientation `oM` of the circle there. Then
the coefficient of `p_j(r₁)` in the image of the maximum `p_i(r₀)` of `f₀` under the integral
continuation map along `Φ` is the product of their fundamental signs for `oM` when
`p_j(r₁) = p_i(r₀) + c`, and `0` otherwise. -/
theorem signedContinuationCoeff_circleCosTwoMaxCrit (hδ₀ : 0 < δ₀) (hδ₁ : 0 < δ₁) (n : ℤ)
    (oM : Manifold.Orientation 𝓘(ℝ) (AddCircle (2 * π)) (Fin (finrank ℝ ℝ))) {i j : Fin 2}
    (hmax : ∃ e, |e| < π / 2 ∧
      Φ.symm (circleCosTwoMax r₁ j) =
        circleCosTwoMax r₁ j - ((r₁ - r₀ - n * π + e : ℝ) : AddCircle (2 * π)))
    (hΦ : oM.IsOrientationPreservingAt oM Φ (Φ.symm (circleCosTwoMax r₁ j))) :
    hX₀.signedContinuationCoeff hX₁ 𝔬₀ 𝔬₁ Φ (circleCosTwoMaxCrit δ₀ r₀ i)
        (circleCosTwoMaxCrit δ₁ r₁ j) =
      if circleCosTwoMax r₁ j = circleCosTwoMax r₀ i + ((r₁ - r₀ - n * π : ℝ) : AddCircle (2 * π))
      then hX₀.fundamentalSign 𝔬₀ oM (circleCosTwoMaxCrit δ₀ r₀ i) *
        hX₁.fundamentalSign 𝔬₁ oM (circleCosTwoMaxCrit δ₁ r₁ j)
      else 0 := by
  set c : ℝ := r₁ - r₀ - n * π
  rw [hX₀.signedContinuationCoeff_of_morseIndex_eq_finrank hX₁ 𝔬₀ 𝔬₁ Φ
    (isMorse_circleCosTwo hδ₀.ne' r₀) (isMorse_circleCosTwo hδ₁.ne' r₁) oM
    (by rwa [coe_circleCosTwoMaxCrit])
    ((manifoldMorseIndex_circleCosTwoMaxCrit hδ₀ r₀ i).trans (finrank_self ℝ).symm)
    ((manifoldMorseIndex_circleCosTwoMaxCrit hδ₁ r₁ j).trans (finrank_self ℝ).symm)]
  simp only [coe_circleCosTwoMaxCrit]
  -- `Φ⁻¹ p_j(r₁)` lies on the unstable manifold of the maximum `p_j(r₁) - c` of `f₀`.
  obtain ⟨e, he, hΦj⟩ := hmax
  have hmem : Φ.symm (circleCosTwoMax r₁ j) ∈
      hX₀.flow.unstableSet (circleCosTwoMax r₁ j - ((c : ℝ) : AddCircle (2 * π))) := by
    have h := hX₀.coe_mem_unstableSet_circleCosTwo_of_mem_Ioo hδ₀ (n := (j : ℕ) + n)
      (y := r₁ + j * π - (c + e))
      ⟨by simp only [c]; push_cast; linarith [(abs_lt.1 he).2],
        by simp only [c]; push_cast; linarith [(abs_lt.1 he).1]⟩
    rw [hΦj, circleCosTwoMax_def, ← AddCircle.coe_sub, ← AddCircle.coe_sub]
    convert h using 2
    congr 1
    simp only [c]
    push_cast
    ring
  refine if_congr ⟨fun h ↦ ?_, fun h ↦ ?_⟩ rfl rfl
  · rw [tendsto_nhds_unique (Flow.mem_unstableSet.1 h) (Flow.mem_unstableSet.1 hmem),
      sub_add_cancel]
  · rwa [← sub_eq_iff_eq_add.2 h]

open scoped Classical in
/-- **The integral continuation coefficients between minima.** Let `n` be an integer, and let `Φ`
move the minimum `q_i(r₀)` of `f₀` to `q_i(r₀) + c + e`, where `c = r₁ - r₀ - n π` and
`|e| < π / 2`. Then the coefficient of the minimum `q_j(r₁)` of `f₁` in the image of `q_i(r₀)`
under the integral continuation map along `Φ` is the product of their augmentation signs when
`q_j(r₁) = q_i(r₀) + c`, and `0` otherwise. -/
theorem signedContinuationCoeff_circleCosTwoMinCrit (hδ₀ : 0 < δ₀) (hδ₁ : 0 < δ₁) (n : ℤ)
    {i j : Fin 2}
    (hmin : ∃ e, |e| < π / 2 ∧
      Φ (circleCosTwoMin r₀ i) =
        circleCosTwoMin r₀ i + ((r₁ - r₀ - n * π + e : ℝ) : AddCircle (2 * π))) :
    hX₀.signedContinuationCoeff hX₁ 𝔬₀ 𝔬₁ Φ (circleCosTwoMinCrit δ₀ r₀ i)
        (circleCosTwoMinCrit δ₁ r₁ j) =
      if circleCosTwoMin r₁ j = circleCosTwoMin r₀ i + ((r₁ - r₀ - n * π : ℝ) : AddCircle (2 * π))
      then 𝔬₀.augmentationSign (circleCosTwoMinCrit δ₀ r₀ i) *
        𝔬₁.augmentationSign (circleCosTwoMinCrit δ₁ r₁ j)
      else 0 := by
  set c : ℝ := r₁ - r₀ - n * π
  rw [hX₀.signedContinuationCoeff_of_morseIndex_eq_zero hX₁ 𝔬₀ 𝔬₁ Φ
    (isMorse_circleCosTwo hδ₀.ne' r₀) (manifoldMorseIndex_circleCosTwoMinCrit hδ₀ r₀ i)
    (manifoldMorseIndex_circleCosTwoMinCrit hδ₁ r₁ j)]
  simp only [coe_circleCosTwoMinCrit]
  -- `Φ q_i(r₀)` lies on the stable manifold of the minimum `q_i(r₀) + c` of `f₁`.
  obtain ⟨e, he, hΦi⟩ := hmin
  have hmem : Φ (circleCosTwoMin r₀ i) ∈
      hX₁.flow.stableSet (circleCosTwoMin r₀ i + ((c : ℝ) : AddCircle (2 * π))) := by
    have h := hX₁.coe_mem_stableSet_circleCosTwo_of_mem_Ioo hδ₁ (n := (i : ℕ) - n)
      (y := r₀ + π / 2 + i * π + (c + e))
      ⟨by simp only [c]; push_cast; linarith [(abs_lt.1 he).1],
        by simp only [c]; push_cast; linarith [(abs_lt.1 he).2]⟩
    rw [hΦi, circleCosTwoMin_def, ← AddCircle.coe_add, ← AddCircle.coe_add]
    convert h using 2
    congr 1
    simp only [c]
    push_cast
    ring
  exact if_congr ⟨fun h ↦ tendsto_nhds_unique (Flow.mem_stableSet.1 h)
    (Flow.mem_stableSet.1 hmem), fun h ↦ h ▸ hmem⟩ rfl rfl

open scoped Classical in
/-- **The integral continuation coefficients of the circle examples.** Let `n` be an integer and
`c = r₁ - r₀ - n π`, so that the rotation by `c` carries the critical points of
`f₀ = δ₀ cos (2 (θ - r₀))` to those of `f₁ = δ₁ cos (2 (θ - r₁))`. Let `Φ` be a diffeomorphism of
the circle which moves each minimum `p` of `f₀` to `p + c + e` and whose inverse moves each
maximum `q` of `f₁` to `q - c - e`, with `|e| < π / 2`, and which preserves an orientation `oM` of
the circle at the preimages of the maxima. Then the coefficient of `q` in the image of `p` under
the integral continuation map along `Φ` is the product of the signs of `p` and `q` when
`q = p + c`, and `0` otherwise. The sign of a critical point is its augmentation sign at a minimum
and its fundamental sign for `oM` at a maximum, the other summand being `0`. -/
theorem signedContinuationCoeff_circleCosTwo (hδ₀ : 0 < δ₀) (hδ₁ : 0 < δ₁) (n : ℤ)
    (oM : Manifold.Orientation 𝓘(ℝ) (AddCircle (2 * π)) (Fin (finrank ℝ ℝ)))
    (hmin : ∀ i, ∃ e, |e| < π / 2 ∧
      Φ (circleCosTwoMin r₀ i) =
        circleCosTwoMin r₀ i + ((r₁ - r₀ - n * π + e : ℝ) : AddCircle (2 * π)))
    (hmax : ∀ j, ∃ e, |e| < π / 2 ∧
      Φ.symm (circleCosTwoMax r₁ j) =
        circleCosTwoMax r₁ j - ((r₁ - r₀ - n * π + e : ℝ) : AddCircle (2 * π)))
    (hΦ : ∀ j, oM.IsOrientationPreservingAt oM Φ (Φ.symm (circleCosTwoMax r₁ j)))
    (p : criticalPoints 𝓘(ℝ) (circleCosTwo δ₀ r₀)) (q : criticalPoints 𝓘(ℝ) (circleCosTwo δ₁ r₁)) :
    hX₀.signedContinuationCoeff hX₁ 𝔬₀ 𝔬₁ Φ p q =
      if (q : AddCircle (2 * π)) = p + ((r₁ - r₀ - n * π : ℝ) : AddCircle (2 * π)) then
        (𝔬₀.augmentationSign p + hX₀.fundamentalSign 𝔬₀ oM p) *
          (𝔬₁.augmentationSign q + hX₁.fundamentalSign 𝔬₁ oM q)
      else 0 := by
  have hrank : finrank ℝ ℝ = 1 := finrank_self ℝ
  obtain ⟨i, hi | hi⟩ := (mem_criticalPoints_circleCosTwo_iff_exists hδ₀.ne' r₀).1 p.property <;>
    obtain ⟨j, hj | hj⟩ := (mem_criticalPoints_circleCosTwo_iff_exists hδ₁.ne' r₁).1 q.property
  · -- Two maxima, whose augmentation signs vanish.
    obtain rfl : p = circleCosTwoMaxCrit δ₀ r₀ i :=
      Subtype.ext (hi.trans (coe_circleCosTwoMaxCrit δ₀ r₀ i).symm)
    obtain rfl : q = circleCosTwoMaxCrit δ₁ r₁ j :=
      Subtype.ext (hj.trans (coe_circleCosTwoMaxCrit δ₁ r₁ j).symm)
    rw [signedContinuationCoeff_circleCosTwoMaxCrit hX₀ hX₁ 𝔬₀ 𝔬₁ Φ hδ₀ hδ₁ n oM (hmax j) (hΦ j),
      MorseOrientation.augmentationSign_of_morseIndex_ne_zero _ (by
        rw [manifoldMorseIndex_circleCosTwoMaxCrit hδ₀]; exact one_ne_zero),
      MorseOrientation.augmentationSign_of_morseIndex_ne_zero _ (by
        rw [manifoldMorseIndex_circleCosTwoMaxCrit hδ₁]; exact one_ne_zero),
      zero_add, zero_add, coe_circleCosTwoMaxCrit, coe_circleCosTwoMaxCrit]
  · -- A maximum and a minimum: the rotation by `c` carries the maximum to a maximum.
    obtain rfl : p = circleCosTwoMaxCrit δ₀ r₀ i :=
      Subtype.ext (hi.trans (coe_circleCosTwoMaxCrit δ₀ r₀ i).symm)
    obtain rfl : q = circleCosTwoMinCrit δ₁ r₁ j :=
      Subtype.ext (hj.trans (coe_circleCosTwoMinCrit δ₁ r₁ j).symm)
    rw [signedContinuationCoeff_eq_zero_of_morseIndex_ne 𝔬₀ 𝔬₁ (by
      rw [manifoldMorseIndex_circleCosTwoMaxCrit hδ₀, manifoldMorseIndex_circleCosTwoMinCrit hδ₁]
      exact one_ne_zero), eq_comm, ite_eq_right_iff]
    obtain ⟨k, hk⟩ := exists_circleCosTwoMax_eq_add (r₀ := r₀) (r₁ := r₁) n i
    rw [coe_circleCosTwoMinCrit, coe_circleCosTwoMaxCrit, ← hk]
    exact fun h ↦ absurd h (circleCosTwoMin_ne_circleCosTwoMax r₁ j k)
  · -- A minimum and a maximum: the rotation by `c` carries the minimum to a minimum.
    obtain rfl : p = circleCosTwoMinCrit δ₀ r₀ i :=
      Subtype.ext (hi.trans (coe_circleCosTwoMinCrit δ₀ r₀ i).symm)
    obtain rfl : q = circleCosTwoMaxCrit δ₁ r₁ j :=
      Subtype.ext (hj.trans (coe_circleCosTwoMaxCrit δ₁ r₁ j).symm)
    rw [signedContinuationCoeff_eq_zero_of_morseIndex_ne 𝔬₀ 𝔬₁ (by
      rw [manifoldMorseIndex_circleCosTwoMinCrit hδ₀, manifoldMorseIndex_circleCosTwoMaxCrit hδ₁]
      exact zero_ne_one), eq_comm, ite_eq_right_iff]
    obtain ⟨k, hk⟩ := exists_circleCosTwoMin_eq_add (r₀ := r₀) (r₁ := r₁) n i
    rw [coe_circleCosTwoMinCrit, coe_circleCosTwoMaxCrit, ← hk]
    exact fun h ↦ absurd h (circleCosTwoMax_ne_circleCosTwoMin r₁ j k)
  · -- Two minima, whose fundamental signs vanish.
    obtain rfl : p = circleCosTwoMinCrit δ₀ r₀ i :=
      Subtype.ext (hi.trans (coe_circleCosTwoMinCrit δ₀ r₀ i).symm)
    obtain rfl : q = circleCosTwoMinCrit δ₁ r₁ j :=
      Subtype.ext (hj.trans (coe_circleCosTwoMinCrit δ₁ r₁ j).symm)
    rw [signedContinuationCoeff_circleCosTwoMinCrit hX₀ hX₁ 𝔬₀ 𝔬₁ Φ hδ₀ hδ₁ n (hmin i),
      fundamentalSign_of_morseIndex_ne (by
        rw [manifoldMorseIndex_circleCosTwoMinCrit hδ₀, hrank]; exact zero_ne_one),
      fundamentalSign_of_morseIndex_ne (by
        rw [manifoldMorseIndex_circleCosTwoMinCrit hδ₁, hrank]; exact zero_ne_one),
      add_zero, add_zero, coe_circleCosTwoMinCrit, coe_circleCosTwoMinCrit]

end IsAdaptedPseudoGradient

end TauCeti
