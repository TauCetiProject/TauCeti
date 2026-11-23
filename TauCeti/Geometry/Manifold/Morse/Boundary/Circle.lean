/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.OneDimensional
public import TauCeti.Geometry.Manifold.Morse.Circle

/-!
# The Morse complex of `δ cos (2 (θ - r))` on the circle

On the circle `ℝ ⧸ 2πℤ`, the function `f_r(θ) = δ cos (2 (θ - r))` with `δ > 0`
(`TauCeti.circleCosTwo δ r`) has the two maxima `p_j = r + j π` (`TauCeti.circleCosTwoMax r j`),
of index `1`, and the two minima `q_j = r + π / 2 + j π` (`TauCeti.circleCosTwoMin r j`), of index
`0`. This file computes its Morse boundary for every adapted pseudo-gradient `X`, which is
automatically Morse–Smale in dimension one.

Since `f` has a second maximum, the two trajectories leaving a maximum end at two different
minima, which are therefore `q_0` and `q_1`
(`TauCeti.IsAdaptedPseudoGradient.exists_ne_signedMorseBoundaryCoeff_of_finrank_eq_one`). So:

* the mod-two Morse boundary of each maximum is `q_0 + q_1`, the sum of all the minima
  (`IsMorseSmale.morseBoundary_single_apply_circleCosTwo`), and the mod-two differential is the
  matrix with all entries `1`;
* with integer coefficients and any orientations of the unstable manifolds, the coefficients of
  `p_j` at `q_0` and `q_1`, weighted by the augmentation signs, are `ε_j` and `-ε_j` for a sign
  `ε_j = ±1` (`exists_augmentationSign_mul_signedMorseBoundaryCoeff_circleCosTwo_eq` in the
  namespace `TauCeti.IsAdaptedPseudoGradient`).

Reversing the orientations at some of the critical points therefore produces orientation data in
which the integral Morse differential, in the ordered bases `(p_0, p_1)` and `(q_0, q_1)`, has the
sign pattern of `D = I - S = [[1, -1], [-1, 1]]`, where `S` exchanges the two generators
(`TauCeti.IsAdaptedPseudoGradient.exists_signedMorseBoundaryCoeff_circleCosTwo_eq`). This only
realizes a sign pattern: since the orientation at each critical point can be reversed on its own,
the same argument gives every matrix `(a_j b_i)` with all `a_j, b_i = ±1`, for instance the matrix
with all entries `1`. This file does not identify these orientations with the orientations `+∂_θ`
of the unstable manifolds of the maxima used in the circle continuation examples, so it does not
show that the Morse differential for those orientations is `I - S` for the matrix `S` of the
continuation map.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `isMorseSmale_circleCosTwo`: every pseudo-gradient adapted to `f_r` is Morse–Smale.
* `IsMorseSmale.morseBoundary_single_apply_circleCosTwo`: the mod-two Morse boundary of a maximum
  is the sum of the two minima.
* `exists_augmentationSign_mul_signedMorseBoundaryCoeff_circleCosTwo_eq`: the weighted integral
  boundary coefficients of `p_j` at `q_0` and `q_1` are `ε_j` and `-ε_j`.
* `exists_signedMorseBoundaryCoeff_circleCosTwo_eq`: for suitable orientations the integral Morse
  differential has the sign pattern `[[1, -1], [-1, 1]]` of `I - S`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.1–4.2 (continuation maps).
-/

public section

open Function Module Set
open scoped Manifold ContDiff Real

namespace TauCeti

local instance morseBoundaryCircleTwoPiPos : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

variable {δ r : ℝ} {X : (x : AddCircle (2 * π)) → TangentSpace 𝓘(ℝ) x}

/-- The other maximum `p_{j + 1}` is not `p_j`. -/
private theorem circleCosTwoMaxCrit_add_one_ne (δ r : ℝ) (j : Fin 2) :
    circleCosTwoMaxCrit δ r (j + 1) ≠ circleCosTwoMaxCrit δ r j := by
  fin_cases j <;> simp

/-- Two distinct critical points of index `0` are the two minima, so every critical point of
index `0` is one of them. -/
private theorem eq_or_eq_of_manifoldMorseIndex_eq_zero (hδ : 0 < δ)
    {q q₀ q₁ : criticalPoints 𝓘(ℝ) (circleCosTwo δ r)} (hne : q₀ ≠ q₁)
    (hq₀ : manifoldMorseIndex 𝓘(ℝ) (circleCosTwo δ r) q₀ = 0)
    (hq₁ : manifoldMorseIndex 𝓘(ℝ) (circleCosTwo δ r) q₁ = 0)
    (hq : manifoldMorseIndex 𝓘(ℝ) (circleCosTwo δ r) q = 0) : q = q₀ ∨ q = q₁ := by
  obtain ⟨i, hi⟩ := exists_eq_circleCosTwoMin_of_manifoldMorseIndex_eq_zero hδ r q.property hq
  obtain ⟨i₀, hi₀⟩ := exists_eq_circleCosTwoMin_of_manifoldMorseIndex_eq_zero hδ r q₀.property hq₀
  obtain ⟨i₁, hi₁⟩ := exists_eq_circleCosTwoMin_of_manifoldMorseIndex_eq_zero hδ r q₁.property hq₁
  have hi01 : i₀ ≠ i₁ := fun he ↦ hne (Subtype.ext (by rw [hi₀, hi₁, he]))
  fin_cases i <;> fin_cases i₀ <;> fin_cases i₁ <;>
    first
    | exact absurd rfl hi01
    | exact Or.inl (Subtype.ext (hi.trans hi₀.symm))
    | exact Or.inr (Subtype.ext (hi.trans hi₁.symm))

namespace IsAdaptedPseudoGradient

/-- **Every pseudo-gradient adapted to `θ ↦ δ cos (2 (θ - r))` is Morse–Smale**, as on every
one-dimensional manifold. -/
theorem isMorseSmale_circleCosTwo (hδ : δ ≠ 0)
    (hX : IsAdaptedPseudoGradient (circleCosTwo δ r) X) : hX.IsMorseSmale :=
  hX.isMorseSmale_of_finrank_eq_one (isMorse_circleCosTwo hδ r) (finrank_self ℝ)

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient (circleCosTwo δ r) X} (h : hX.IsMorseSmale)
  (hf : IsMorse 𝓘(ℝ) (circleCosTwo δ r))

/-- **The mod-two Morse boundary of a maximum is the sum of the two minima.** For `δ > 0` and every
adapted pseudo-gradient, the coefficient of a critical point `q` in the mod-two Morse boundary of a
maximum of `θ ↦ δ cos (2 (θ - r))` is `1` when `q` is a minimum and `0` otherwise. -/
theorem morseBoundary_single_apply_circleCosTwo (hδ : 0 < δ)
    {p : criticalPoints 𝓘(ℝ) (circleCosTwo δ r)}
    (hp : manifoldMorseIndex 𝓘(ℝ) (circleCosTwo δ r) p = 1)
    (q : criticalPoints 𝓘(ℝ) (circleCosTwo δ r)) :
    h.morseBoundary hf (Finsupp.single p 1) q =
      if manifoldMorseIndex 𝓘(ℝ) (circleCosTwo δ r) q = 0 then 1 else 0 := by
  -- `p` is a maximum `p_j`; the other maximum is `p_{j + 1}`.
  obtain ⟨j, hj⟩ := exists_eq_circleCosTwoMax_of_manifoldMorseIndex_eq_one hδ r p.property hp
  obtain rfl : p = circleCosTwoMaxCrit δ r j := Subtype.ext (by rw [hj, coe_circleCosTwoMaxCrit])
  obtain ⟨q₀, q₁, hne, hq₀, hq₁, hd⟩ := h.exists_ne_morseBoundary_single_of_finrank_eq_one hf
    (finrank_self ℝ) hp (circleCosTwoMaxCrit_add_one_ne δ r j)
    (by rw [manifoldMorseIndex_circleCosTwoMaxCrit hδ]; exact one_ne_zero)
  rw [hd, Finsupp.add_apply]
  by_cases hq : manifoldMorseIndex 𝓘(ℝ) (circleCosTwo δ r) q = 0
  · rw [ite_eq_left_iff.2 fun h ↦ (h hq).elim]
    rcases eq_or_eq_of_manifoldMorseIndex_eq_zero hδ hne hq₀ hq₁ hq with rfl | rfl
    · simp [hne]
    · simp [hne.symm]
  · have h₀ : q ≠ q₀ := by rintro rfl; exact hq hq₀
    have h₁ : q ≠ q₁ := by rintro rfl; exact hq hq₁
    simp [hq, h₀, h₁]

end IsMorseSmale

/-- **The integral Morse boundary of the circle, up to orientations.** For `δ > 0`, every adapted
pseudo-gradient and every choice of orientations of the unstable manifolds, the coefficients of the
integral Morse boundary of the maximum `p_j = r + j π` at the minima `q_0 = r + π / 2` and
`q_1 = r + 3π / 2`, weighted by the augmentation signs, are `ε_j` and `-ε_j` for a sign
`ε_j = ±1`. -/
theorem exists_augmentationSign_mul_signedMorseBoundaryCoeff_circleCosTwo_eq (hδ : 0 < δ)
    (hX : IsAdaptedPseudoGradient (circleCosTwo δ r) X)
    (𝔬 : MorseOrientation (circleCosTwo δ r) X) :
    ∃ ε : Fin 2 → ℤ, (∀ j, ε j = 1 ∨ ε j = -1) ∧ ∀ i j : Fin 2,
      𝔬.augmentationSign (circleCosTwoMinCrit δ r i) *
          hX.signedMorseBoundaryCoeff 𝔬 (circleCosTwoMaxCrit δ r j) (circleCosTwoMinCrit δ r i) =
        if i = 0 then ε j else -ε j := by
  have hf := isMorse_circleCosTwo hδ.ne' r
  -- For each maximum, the two minima carry opposite weighted coefficients `±1`.
  have key (j : Fin 2) : ∃ e : ℤ, (e = 1 ∨ e = -1) ∧
      𝔬.augmentationSign (circleCosTwoMinCrit δ r 0) * hX.signedMorseBoundaryCoeff 𝔬
          (circleCosTwoMaxCrit δ r j) (circleCosTwoMinCrit δ r 0) = e ∧
      𝔬.augmentationSign (circleCosTwoMinCrit δ r 1) * hX.signedMorseBoundaryCoeff 𝔬
          (circleCosTwoMaxCrit δ r j) (circleCosTwoMinCrit δ r 1) = -e := by
    obtain ⟨Q₀, Q₁, hne, hQ₀, hQ₁, hsign, hrel, -⟩ :=
      hX.exists_ne_signedMorseBoundaryCoeff_of_finrank_eq_one hf (finrank_self ℝ) 𝔬
        (manifoldMorseIndex_circleCosTwoMaxCrit hδ r j) (circleCosTwoMaxCrit_add_one_ne δ r j)
        (by rw [manifoldMorseIndex_circleCosTwoMaxCrit hδ]; exact one_ne_zero)
    have haug := 𝔬.augmentationSign_eq_one_or_eq_neg_one hQ₀
    set e := 𝔬.augmentationSign Q₀ * hX.signedMorseBoundaryCoeff 𝔬 (circleCosTwoMaxCrit δ r j) Q₀
    have he : e = 1 ∨ e = -1 := by
      rcases haug with ha | ha <;> rcases hsign with hs | hs <;> simp [e, ha, hs]
    have hmin := manifoldMorseIndex_circleCosTwoMinCrit hδ r
    have hm01 : circleCosTwoMinCrit δ r 0 ≠ circleCosTwoMinCrit δ r 1 := by simp
    -- The labels of `Q₀` and `Q₁` are `0` and `1` in some order.
    rcases eq_or_eq_of_manifoldMorseIndex_eq_zero hδ hne hQ₀ hQ₁ (hmin 0) with h0 | h0
    · rcases eq_or_eq_of_manifoldMorseIndex_eq_zero hδ hne hQ₀ hQ₁ (hmin 1) with h1 | h1
      · exact absurd (h0.trans h1.symm) hm01
      · exact ⟨e, he, by rw [h0], by rw [h1, hrel]⟩
    · rcases eq_or_eq_of_manifoldMorseIndex_eq_zero hδ hne hQ₀ hQ₁ (hmin 1) with h1 | h1
      · exact ⟨-e, by rcases he with he | he <;> simp [he], by rw [h0, hrel], by rw [h1, neg_neg]⟩
      · exact absurd (h0.trans h1.symm) hm01
  choose ε hε h0 h1 using key
  refine ⟨ε, hε, fun i j ↦ ?_⟩
  fin_cases i
  · exact h0 j
  · exact h1 j

/-- **Orientations realizing the sign pattern of `I - S` on the circle.** For `δ > 0` and every
pseudo-gradient adapted to `θ ↦ δ cos (2 (θ - r))`, there are orientations of the unstable
manifolds for which the integral Morse differential, in the ordered bases `(p_0, p_1)` of the
maxima `p_j = r + j π` and `(q_0, q_1)` of the minima `q_i = r + π / 2 + i π`, is the matrix
`[[1, -1], [-1, 1]]`: the coefficient of `q_i` in the boundary of `p_j` is `1` when `i = j` and
`-1` otherwise. The orientations are obtained by reversing some of those of an arbitrary choice, so
this does not tie them to the orientations `+∂_θ` of the circle continuation examples; reversing
differently realizes every matrix `(a_j b_i)` with all `a_j, b_i = ±1`. -/
theorem exists_signedMorseBoundaryCoeff_circleCosTwo_eq (hδ : 0 < δ)
    (hX : IsAdaptedPseudoGradient (circleCosTwo δ r) X) :
    ∃ 𝔬 : MorseOrientation (circleCosTwo δ r) X, ∀ i j : Fin 2,
      hX.signedMorseBoundaryCoeff 𝔬 (circleCosTwoMaxCrit δ r j) (circleCosTwoMinCrit δ r i) =
        if i = j then 1 else -1 := by
  classical
  obtain ⟨𝔬₀⟩ := hX.nonempty_morseOrientation
  -- First reverse the minima of negative augmentation sign.
  set 𝔬₁ := 𝔬₀.reverse {q | 𝔬₀.augmentationSign q = -1}
  have haug (q : criticalPoints 𝓘(ℝ) (circleCosTwo δ r))
      (hq : manifoldMorseIndex 𝓘(ℝ) (circleCosTwo δ r) q = 0) : 𝔬₁.augmentationSign q = 1 := by
    rw [MorseOrientation.augmentationSign_reverse]
    rcases 𝔬₀.augmentationSign_eq_one_or_eq_neg_one hq with ha | ha <;> simp [ha]
  obtain ⟨ε, hε, hcoeff⟩ :=
    hX.exists_augmentationSign_mul_signedMorseBoundaryCoeff_circleCosTwo_eq hδ 𝔬₁
  -- Then reverse the maxima `p_j` whose sign `ε_j` is not `1` for `j = 0` and `-1` for `j = 1`.
  set S := {p : criticalPoints 𝓘(ℝ) (circleCosTwo δ r) |
    ∃ j, p = circleCosTwoMaxCrit δ r j ∧ ε j ≠ if j = 0 then 1 else -1}
  refine ⟨𝔬₁.reverse S, fun i j ↦ ?_⟩
  have hqS : circleCosTwoMinCrit δ r i ∉ S := by
    rintro ⟨j', hj', -⟩
    exact circleCosTwoMinCrit_ne_circleCosTwoMaxCrit δ r i j' hj'
  have hpS : circleCosTwoMaxCrit δ r j ∈ S ↔ ε j ≠ if j = 0 then 1 else -1 := by
    refine ⟨fun ⟨j', hj', hne⟩ ↦ ?_, fun hne ↦ ⟨j, rfl, hne⟩⟩
    rwa [(circleCosTwoMaxCrit_inj δ r).1 hj']
  have hc := hcoeff i j
  rw [haug _ (manifoldMorseIndex_circleCosTwoMinCrit hδ r i), one_mul] at hc
  rw [signedMorseBoundaryCoeff_reverse]
  simp only [hqS, ↓reduceIte, mul_one, hc]
  by_cases hin : circleCosTwoMaxCrit δ r j ∈ S
  · have hne := hpS.1 hin
    simp only [hin, ↓reduceIte]
    rcases hε j with he | he <;> rw [he] at hne ⊢ <;> fin_cases i <;> fin_cases j <;>
      simp at hne ⊢
  · have heq := not_not.1 (mt hpS.2 hin)
    simp only [hin, ↓reduceIte, one_mul]
    rw [heq]
    fin_cases i <;> fin_cases j <;> simp

end IsAdaptedPseudoGradient

end TauCeti
