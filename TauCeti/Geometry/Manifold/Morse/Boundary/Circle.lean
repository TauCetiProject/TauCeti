/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.FundamentalChain
public import TauCeti.Geometry.Manifold.Morse.Boundary.OneDimensional
public import TauCeti.Geometry.Manifold.Morse.Circle
public import TauCeti.Geometry.Manifold.Orientation.AddCircle
import TauCeti.Topology.Circle.AddCircle

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

Since the orientation at each critical point can be reversed on its own, this alone realizes every
matrix `(a_j b_i)` with all `a_j, b_i = ±1` as the integral Morse differential in the ordered bases
`(p_0, p_1)` and `(q_0, q_1)`.

The file then computes the differential for the orientations of the circle continuation examples,
which orient the unstable line of each maximum by `+∂_θ`, the positive orientation of the circle
(`AddCircle.orientation`): the fundamental signs of the maxima for this orientation are `1`
(`TauCeti.IsAdaptedPseudoGradient.fundamentalSign`). A trajectory from `p_j` to a minimum stays on
the arc between `p_j` and the neighbouring minimum on its side, since its orbit is connected and
`f` takes on it values strictly between `-δ` and `δ`. The trajectory to
`q_j = p_j + π / 2` therefore leaves `p_j` in the direction `+∂_θ` and the one to
`q_{j + 1} = p_j - π / 2` in the direction `-∂_θ`. Weighted by the fundamental sign of its source,
the sign of a trajectory compares the orientation of the circle with the standard orientation of
`ℝ` followed by the orientation of its end, through `v ↦ (df v, N_q v)`
(`TauCeti.IsAdaptedPseudoGradient.fundamentalSign_mul_trajectorySign`), so a trajectory into a
positively oriented minimum counts positively when `f` increases along `+∂_θ`. Hence the
coefficient of `q_i` in the boundary of `p_j` is `-ε_i` for `i = j` and `ε_i` otherwise, where
`ε_i = ±1` is the sign of the orientation of the point `q_i`
(`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundaryCoeff_circleCosTwo_eq_augmentationSign_mul`):
the differential is `S - I` for the positive orientations of the minima and `I - S` for the negative
ones, where `S` exchanges the two generators
(`exists_fundamentalSign_augmentationSign_signedMorseBoundaryCoeff_circleCosTwo_eq` in the
namespace `TauCeti.IsAdaptedPseudoGradient`).

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `isMorseSmale_circleCosTwo`: every pseudo-gradient adapted to `f_r` is Morse–Smale.
* `IsMorseSmale.morseBoundary_single_apply_circleCosTwo`: the mod-two Morse boundary of a maximum
  is the sum of the two minima.
* `exists_augmentationSign_mul_signedMorseBoundaryCoeff_circleCosTwo_eq`: the weighted integral
  boundary coefficients of `p_j` at `q_0` and `q_1` are `ε_j` and `-ε_j`.
* `signedMorseBoundaryCoeff_circleCosTwo_eq_augmentationSign_mul`: for the orientations `+∂_θ` of
  the maxima, the coefficient of `q_i` in the boundary of `p_j` is `-ε_i` for `i = j` and `ε_i`
  otherwise.
* `exists_fundamentalSign_augmentationSign_signedMorseBoundaryCoeff_circleCosTwo_eq`: there are
  orientation data with the orientations `+∂_θ` at the maxima and the negative orientations at
  the minima, and for them the differential is `I - S = [[1, -1], [-1, 1]]`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.1–4.2 (continuation maps).
-/

public section

open Filter Function Module Set
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

/-- **Trajectories on the circle stay in an arc.** If a point `y` on a trajectory from `p` to
`q ≠ p` lies in the image of an open interval `(a, b)`, and `f` takes neither of the values at the
ends of the interval strictly between `f q` and `f p`, then `p` and `q` lie in the image of the
closed interval `[a, b]`: the orbit of `y`, which is connected and on which `f` takes values
strictly between `f q` and `f p`, cannot leave the arc. -/
private theorem mem_image_Icc_of_mem_unstableSet_inter_stableSet
    {f : AddCircle (2 * π) → ℝ} {X : (x : AddCircle (2 * π)) → TangentSpace 𝓘(ℝ) x}
    (hX : IsAdaptedPseudoGradient f X) {p q y : AddCircle (2 * π)} (hpq : p ≠ q)
    (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) {a b : ℝ}
    (hya : y ∈ ((↑) : ℝ → AddCircle (2 * π)) '' Ioo a b)
    (ha : f (a : AddCircle (2 * π)) ∉ Ioo (f q) (f p))
    (hb : f (b : AddCircle (2 * π)) ∉ Ioo (f q) (f p)) :
    p ∈ ((↑) : ℝ → AddCircle (2 * π)) '' Icc a b ∧
      q ∈ ((↑) : ℝ → AddCircle (2 * π)) '' Icc a b := by
  set K : Set (AddCircle (2 * π)) := ((↑) : ℝ → AddCircle (2 * π)) '' Icc a b
  have hK : IsClosed K :=
    IsCompact.isClosed (X := AddCircle (2 * π)) (isCompact_Icc.image continuous_quotient_mk')
  have hU : IsOpen (((↑) : ℝ → AddCircle (2 * π)) '' Ioo a b) :=
    QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  -- The orbit of `y` is connected and avoids the two ends of the arc, so it stays in the arc.
  have hO : range (fun s ↦ hX.flow s y) ⊆ ((↑) : ℝ → AddCircle (2 * π)) '' Ioo a b := by
    refine IsPreconnected.subset_left_of_subset_union hU hK.isOpen_compl
      (disjoint_compl_right.mono_left (image_mono Ioo_subset_Icc_self)) ?_
      ⟨y, ⟨0, hX.flow.map_zero_apply y⟩, hya⟩
      (isPreconnected_range (hX.flow.continuous continuous_id continuous_const))
    rintro _ ⟨s, rfl⟩
    by_cases hs : hX.flow s y ∈ K
    · left
      obtain ⟨u, hu, hu'⟩ := hs
      have hval := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hpq
        (hX.flow.isInvariant_unstableSet_inter_stableSet p q s hy)
      rw [← hu'] at hval
      refine ⟨u, ⟨hu.1.lt_of_ne ?_, hu.2.lt_of_ne ?_⟩, hu'⟩
      · rintro rfl
        exact ha hval
      · rintro rfl
        exact hb hval
    · exact Or.inr hs
  have hOK (s : ℝ) : hX.flow s y ∈ K := image_mono Ioo_subset_Icc_self (hO ⟨s, rfl⟩)
  exact ⟨hK.mem_of_tendsto (Flow.mem_unstableSet.1 hy.1) (Eventually.of_forall hOK),
    hK.mem_of_tendsto (Flow.mem_stableSet.1 hy.2) (Eventually.of_forall hOK)⟩

/-- A point `s` of `[a, a + π / 2]` at which `cos (2 (s - a))` is `cos c`, for `c ∈ [0, π]`, is
`a + c / 2`: the cosine is injective on `[0, π]`. -/
private theorem eq_add_div_two_of_cos_eq {a s c : ℝ} (hs : s ∈ Icc a (a + π / 2))
    (hc : c ∈ Icc 0 π) (h : Real.cos (2 * (s - a)) = Real.cos c) : s = a + c / 2 := by
  have := Real.injOn_cos ⟨by linarith [hs.1], by linarith [hs.2]⟩ hc h
  linarith

/-- If the maximum `p_j` is the class of `r + m π`, then the minimum `q_i` is the class of
`r + π / 2 + m π` exactly for `i = j`. -/
private theorem circleCosTwoMin_eq_coe_iff {r : ℝ} {j : Fin 2} {m : ℤ}
    (hj : circleCosTwoMax r j = ((r + m * π : ℝ) : AddCircle (2 * π))) (i : Fin 2) :
    circleCosTwoMin r i = ((r + π / 2 + m * π : ℝ) : AddCircle (2 * π)) ↔ i = j := by
  have hmin : circleCosTwoMin r j = ((r + π / 2 + m * π : ℝ) : AddCircle (2 * π)) := by
    have h : circleCosTwoMin r j = circleCosTwoMax r j + ((π / 2 : ℝ) : AddCircle (2 * π)) := by
      rw [circleCosTwoMin_def, circleCosTwoMax_def, ← AddCircle.coe_add]
      congr 1
      ring
    rw [h, hj, ← AddCircle.coe_add]
    congr 1
    ring
  rw [← hmin, circleCosTwoMin_inj]


/-- At a lift `s` of a maximum, `cos (2 (s - r)) = 1`. -/
private theorem cos_eq_one_of_coe_eq_circleCosTwoMax {r s : ℝ} {j : Fin 2}
    (h : (s : AddCircle (2 * π)) = circleCosTwoMax r j) : Real.cos (2 * (s - r)) = 1 := by
  simpa using (circleCosTwo_coe 1 r s).symm.trans (h ▸ circleCosTwo_circleCosTwoMax 1 r j)

/-- At a lift `s` of a minimum, `cos (2 (s - r)) = -1`. -/
private theorem cos_eq_neg_one_of_coe_eq_circleCosTwoMin {r s : ℝ} {i : Fin 2}
    (h : (s : AddCircle (2 * π)) = circleCosTwoMin r i) : Real.cos (2 * (s - r)) = -1 := by
  simpa using (circleCosTwo_coe 1 r s).symm.trans (h ▸ circleCosTwo_circleCosTwoMin 1 r i)

/-- At `r + m π`, a lift of a maximum, `cos (2 (u - r)) = 1`. -/
private theorem cos_two_mul_add_int_mul_pi_sub (r : ℝ) (m : ℤ) :
    Real.cos (2 * (r + m * π - r)) = 1 := by
  rw [show 2 * (r + m * π - r) = m * (2 * π) by ring, Real.cos_int_mul_two_pi]

/-- At `r + m π + π / 2`, a lift of a minimum, `cos (2 (u - r)) = -1`. -/
private theorem cos_two_mul_add_int_mul_pi_add_pi_div_two_sub (r : ℝ) (m : ℤ) :
    Real.cos (2 * (r + m * π + π / 2 - r)) = -1 := by
  rw [show 2 * (r + m * π + π / 2 - r) = π + m * (2 * π) by ring, Real.cos_add_int_mul_two_pi,
    Real.cos_pi]

/-- Where `cos (2 (u - r)) = ±1`, the function takes the value `±δ`, which is not strictly between
its values at a minimum and at a maximum. -/
private theorem circleCosTwo_coe_notMem_Ioo {u : ℝ}
    (hu : Real.cos (2 * (u - r)) = 1 ∨ Real.cos (2 * (u - r)) = -1) (i j : Fin 2) :
    circleCosTwo δ r (u : AddCircle (2 * π)) ∉ Ioo (circleCosTwo δ r (circleCosTwoMin r i))
      (circleCosTwo δ r (circleCosTwoMax r j)) := by
  rw [circleCosTwo_coe, circleCosTwo_circleCosTwoMin, circleCosTwo_circleCosTwoMax]
  rcases hu with h | h <;> simp [h]

/-- A trajectory from the maximum `p_j` to the minimum `q_i` crossing the level `0` at
`r + m π + π / 4`, between the critical points `r + m π` and `r + m π + π / 2`, runs from the first
to the second, so `i = j`. -/
private theorem eq_of_coe_mem_morseTrajectorySlice_of_eq
    (hX : IsAdaptedPseudoGradient (circleCosTwo δ r) X) {i j : Fin 2} {m : ℤ}
    (ht : ((r + m * π + π / 4 : ℝ) : AddCircle (2 * π)) ∈
      hX.morseTrajectorySlice (circleCosTwoMax r j) (circleCosTwoMin r i)) : i = j := by
  rw [hX.mem_morseTrajectorySlice] at ht
  obtain ⟨⟨s, hsI, hps⟩, ⟨s', hs'I, hqs⟩⟩ := mem_image_Icc_of_mem_unstableSet_inter_stableSet hX
    (circleCosTwoMax_ne_circleCosTwoMin r j i) ⟨ht.1, ht.2.1⟩ (a := r + m * π)
    (b := r + m * π + π / 2) ⟨_, ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, rfl⟩
    (circleCosTwo_coe_notMem_Ioo (.inl (cos_two_mul_add_int_mul_pi_sub r m)) i j)
    (circleCosTwo_coe_notMem_Ioo (.inr (cos_two_mul_add_int_mul_pi_add_pi_div_two_sub r m)) i j)
  -- The maximum is the left end of the arc and the minimum the right end.
  have hcs (u : ℝ) : Real.cos (2 * (u - r)) = Real.cos (2 * (u - (r + m * π))) := by
    rw [show 2 * (u - r) = 2 * (u - (r + m * π)) + m * (2 * π) by ring,
      Real.cos_add_int_mul_two_pi]
  have hs : s = r + m * π := by
    have := eq_add_div_two_of_cos_eq hsI ⟨le_rfl, Real.pi_pos.le⟩
      (by rw [← hcs, cos_eq_one_of_coe_eq_circleCosTwoMax hps, Real.cos_zero])
    linarith
  have hs' : s' = r + m * π + π / 2 := eq_add_div_two_of_cos_eq hs'I ⟨Real.pi_pos.le, le_rfl⟩
    (by rw [← hcs, cos_eq_neg_one_of_coe_eq_circleCosTwoMin hqs, Real.cos_pi])
  exact (circleCosTwoMin_eq_coe_iff (by rw [← hps, hs]) i).1 (by rw [← hqs, hs']; congr 1; ring)

/-- A trajectory from the maximum `p_j` to the minimum `q_i` crossing the level `0` at
`r + m π + 3 π / 4`, between the critical points `r + m π + π / 2` and `r + (m + 1) π`, runs from
the second to the first, so `i ≠ j`. -/
private theorem ne_of_coe_mem_morseTrajectorySlice_of_eq
    (hX : IsAdaptedPseudoGradient (circleCosTwo δ r) X) {i j : Fin 2} {m : ℤ}
    (ht : ((r + m * π + 3 * π / 4 : ℝ) : AddCircle (2 * π)) ∈
      hX.morseTrajectorySlice (circleCosTwoMax r j) (circleCosTwoMin r i)) : i ≠ j := by
  rw [hX.mem_morseTrajectorySlice] at ht
  obtain ⟨⟨s, hsI, hps⟩, ⟨s', hs'I, hqs⟩⟩ := mem_image_Icc_of_mem_unstableSet_inter_stableSet hX
    (circleCosTwoMax_ne_circleCosTwoMin r j i) ⟨ht.1, ht.2.1⟩
    (a := r + m * π + π / 2) (b := r + m * π + π / 2 + π / 2)
    ⟨_, ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, rfl⟩
    (circleCosTwo_coe_notMem_Ioo (.inr (cos_two_mul_add_int_mul_pi_add_pi_div_two_sub r m)) i j)
    (circleCosTwo_coe_notMem_Ioo (.inl (by
      rw [show r + m * π + π / 2 + π / 2 = r + ((m + 1 : ℤ) : ℝ) * π by push_cast; ring]
      exact cos_two_mul_add_int_mul_pi_sub r (m + 1))) i j)
  -- The minimum is the left end of the arc and the maximum the right end.
  have hcs (u : ℝ) : Real.cos (2 * (u - r)) = -Real.cos (2 * (u - (r + m * π + π / 2))) := by
    rw [show 2 * (u - r) = 2 * (u - (r + m * π + π / 2)) + π + m * (2 * π) by ring,
      Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  have hs : s = r + m * π + π / 2 + π / 2 := eq_add_div_two_of_cos_eq hsI
    ⟨Real.pi_pos.le, le_rfl⟩
    (by rw [Real.cos_pi]; linarith [hcs s, cos_eq_one_of_coe_eq_circleCosTwoMax hps])
  have hs' : s' = r + m * π + π / 2 := by
    have := eq_add_div_two_of_cos_eq hs'I ⟨le_rfl, Real.pi_pos.le⟩
      (by rw [Real.cos_zero]; linarith [hcs s', cos_eq_neg_one_of_coe_eq_circleCosTwoMin hqs])
    linarith
  have hpj : circleCosTwoMax r j = ((r + ((m + 1 : ℤ) : ℝ) * π : ℝ) : AddCircle (2 * π)) := by
    rw [← hps, hs]
    congr 1
    push_cast
    ring
  -- If `i = j`, the minimum would be both `r + π / 2 + m π` and `r + π / 2 + (m + 1) π`.
  intro hij
  have h := (circleCosTwoMin_eq_coe_iff hpj i).2 hij
  rw [← hqs, hs'] at h
  refine AddCircle.coe_add_half_period_ne Real.two_pi_pos.ne' (r + π / 2 + m * π) ?_
  rw [show r + π / 2 + m * π + 2 * π / 2 = r + π / 2 + ((m + 1 : ℤ) : ℝ) * π by
    push_cast; ring, ← h]
  congr 1
  ring

/-- **Where a trajectory of the circle crosses the middle level.** Let `t` be a lift of the point
where a trajectory from the maximum `p_j` to the minimum `q_i` crosses the level `0`. If `i = j`,
the trajectory runs along the arc `(p_j, q_j)`, in the direction `+∂_θ`, and
`sin (2 (t - r)) = 1`; otherwise it runs along the arc `(q_{j + 1}, p_j)`, in the direction
`-∂_θ`, and `sin (2 (t - r)) = -1`. -/
private theorem sin_eq_of_coe_mem_morseTrajectorySlice (hδ : 0 < δ)
    (hX : IsAdaptedPseudoGradient (circleCosTwo δ r) X) {i j : Fin 2} {t : ℝ}
    (ht : (t : AddCircle (2 * π)) ∈
      hX.morseTrajectorySlice (circleCosTwoMax r j) (circleCosTwoMin r i)) :
    Real.sin (2 * (t - r)) = if i = j then 1 else -1 := by
  have hlev := ((hX.mem_morseTrajectorySlice).1 ht).2.2
  rw [circleCosTwo_circleCosTwoMax, circleCosTwo_circleCosTwoMin, circleCosTwo_coe] at hlev
  -- On the middle level `cos (2 (t - r))` vanishes, so `t = r + π / 4 + k π / 2`.
  obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.1
    ((mul_eq_zero.1 (by rw [hlev]; ring)).resolve_left hδ.ne')
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k <;> push_cast at hk
  · rw [show t = r + m * π + π / 4 by linear_combination hk / 2] at ht
    simp only [eq_of_coe_mem_morseTrajectorySlice_of_eq hX ht, ↓reduceIte]
    rw [show 2 * (t - r) = π / 2 + m * (2 * π) by linear_combination hk,
      Real.sin_add_int_mul_two_pi, Real.sin_pi_div_two]
  · rw [show t = r + m * π + 3 * π / 4 by linear_combination hk / 2] at ht
    simp only [ne_of_coe_mem_morseTrajectorySlice_of_eq hX ht, ↓reduceIte]
    rw [show 2 * (t - r) = π / 2 + π + m * (2 * π) by linear_combination hk,
      Real.sin_add_int_mul_two_pi, Real.sin_add_pi, Real.sin_pi_div_two]

/-- The differential of `θ ↦ δ cos (2 (θ - r))` at the class of `t`, along the positive tangent
vector `1` of the circle, indexed by `Fin (finrank ℝ ℝ)`, is `-2 δ sin (2 (t - r))`. -/
private theorem mvfderiv_circleCosTwo_coe_reindex_singleton (δ r t : ℝ) (k : Fin (finrank ℝ ℝ)) :
    mvfderiv 𝓘(ℝ) (circleCosTwo δ r) (t : AddCircle (2 * π))
        (((Module.Basis.singleton (Fin 1) ℝ).reindex (finCongr (finrank_self ℝ).symm) :
          Module.Basis (Fin (finrank ℝ ℝ)) ℝ (TangentSpace 𝓘(ℝ) (t : AddCircle (2 * π)))) k) =
      -(2 * δ) * Real.sin (2 * (t - r)) := by
  rw [Module.Basis.reindex_apply, Module.Basis.singleton_apply, mvfderiv_circleCosTwo_coe]
  -- Read the tangent line at `t` as `ℝ`, where `smulRight_apply` applies.
  change ((1 : ℝ →L[ℝ] ℝ).smulRight _ : ℝ →L[ℝ] ℝ) (1 : ℝ) = _
  simp [ContinuousLinearMap.smulRight_apply]

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

/-- There is a single trajectory from each maximum `p_j` to each minimum `q_i`. -/
private theorem exists_morseTrajectorySlice_circleCosTwo_eq_singleton (hδ : 0 < δ)
    (hX : IsAdaptedPseudoGradient (circleCosTwo δ r) X) (i j : Fin 2) :
    ∃ y, hX.morseTrajectorySlice (circleCosTwoMaxCrit δ r j) (circleCosTwoMinCrit δ r i) = {y} := by
  obtain ⟨Q₀, Q₁, hne, hQ₀, hQ₁, h0, h1, -⟩ :=
    hX.exists_ne_morseTrajectorySlice_eq_singleton_of_finrank_eq_one
      (isMorse_circleCosTwo hδ.ne' r) (finrank_self ℝ)
      (manifoldMorseIndex_circleCosTwoMaxCrit hδ r j) (circleCosTwoMaxCrit_add_one_ne δ r j)
      (by rw [manifoldMorseIndex_circleCosTwoMaxCrit hδ]; exact one_ne_zero)
  rcases eq_or_eq_of_manifoldMorseIndex_eq_zero hδ hne hQ₀ hQ₁
    (manifoldMorseIndex_circleCosTwoMinCrit hδ r i) with h | h <;> rw [h] <;> assumption

open scoped Classical in
/-- **The comparison map along a trajectory of the circle.** At a point `y` of the trajectory from
`p_j` to `q_i`, the map `v ↦ (df_y v, N_{q_i} v)` carries `+∂_θ` to the standard orientation of `ℝ`
followed by the orientation of `q_i` up to the sign `-ε_i` if `i = j` and `ε_i` otherwise, where
`ε_i` is the augmentation sign of `q_i`: along `+∂_θ`, `f` decreases towards `q_j` and increases
towards `q_{j + 1}`. -/
private theorem ite_map_stableComparison_circleCosTwo (hδ : 0 < δ)
    (hX : IsAdaptedPseudoGradient (circleCosTwo δ r) X) (𝔬 : MorseOrientation (circleCosTwo δ r) X)
    {i j : Fin 2} {y : AddCircle (2 * π)}
    (hslice : y ∈ hX.morseTrajectorySlice (circleCosTwoMaxCrit δ r j) (circleCosTwoMinCrit δ r i))
    (hA : Bijective ((mvfderiv 𝓘(ℝ) (circleCosTwo δ r) y).prod
      (hX.stableNormal (𝔬.chart (circleCosTwoMinCrit δ r i)) y))) :
    (if Orientation.map _ (LinearEquiv.ofBijective ((mvfderiv 𝓘(ℝ) (circleCosTwo δ r) y).prod
          (hX.stableNormal (𝔬.chart (circleCosTwoMinCrit δ r i)) y)).toLinearMap hA)
          (((AddCircle.orientation (2 * π)).reindex
            (finCongr (finrank_self ℝ).symm)).orientationAt y) =
        ((Module.Basis.singleton (Fin 1) ℝ).orientation.prod
          (𝔬.orientation (circleCosTwoMinCrit δ r i)) (finrank_self ℝ)
          (𝔬.chart (circleCosTwoMinCrit δ r i)).finrank_negativeWeight_fun).reindex ℝ _
          (finCongr (by rw [manifoldMorseIndex_circleCosTwoMinCrit hδ, finrank_self]))
      then (1 : ℤ) else -1) =
      𝔬.augmentationSign (circleCosTwoMinCrit δ r i) * if i = j then -1 else 1 := by
  have hqi := manifoldMorseIndex_circleCosTwoMinCrit hδ r i
  rw [MorseOrientation.augmentationSign_of_morseIndex_eq_zero _ hqi]
  -- Measure everything against the basis `B = ((1, 0))` of `ℝ × V_q`, `V_q` being zero.
  set c :=
    Module.finBasisOfFinrankEq ℝ _ (𝔬.chart (circleCosTwoMinCrit δ r i)).finrank_negativeWeight_fun
  have hcard : Fintype.card (Fin (finrank ℝ ℝ)) =
      finrank ℝ (ℝ × ({k // (𝔬.chart (circleCosTwoMinCrit δ r i)).weight k < 0} → ℝ)) := by
    rw [Fintype.card_fin, (𝔬.chart _).finrank_prod_negativeWeight_fun, hqi, finrank_self]
  set B : Module.Basis (Fin (finrank ℝ ℝ)) ℝ
      (ℝ × ({k // (𝔬.chart (circleCosTwoMinCrit δ r i)).weight k < 0} → ℝ)) :=
    (((Module.Basis.singleton (Fin 1) ℝ).prod c).reindex finSumFinEquiv).reindex
      (finCongr (by rw [hqi, finrank_self]))
  set bC : Module.Basis (Fin (finrank ℝ ℝ)) ℝ (TangentSpace 𝓘(ℝ) y) :=
    (Module.Basis.singleton (Fin 1) ℝ).reindex (finCongr (finrank_self ℝ).symm)
  have hbC : ((AddCircle.orientation (2 * π)).reindex
      (finCongr (finrank_self ℝ).symm)).orientationAt y = bC.orientation := by
    rw [Manifold.Orientation.orientationAt_reindex, AddCircle.orientationAt_orientation]
    exact (Module.Basis.orientation_reindex _ _).symm
  set 𝒜 := LinearEquiv.ofBijective ((mvfderiv 𝓘(ℝ) (circleCosTwo δ r) y).prod
    (hX.stableNormal (𝔬.chart (circleCosTwoMinCrit δ r i)) y)).toLinearMap hA
  have : Unique (Fin (finrank ℝ ℝ)) := by rw [finrank_self]; infer_instance
  -- The comparison map carries `bC` to `B` scaled by `df_y (bC k)`.
  have hdet : B.det (bC.map 𝒜) = mvfderiv 𝓘(ℝ) (circleCosTwo δ r) y (bC default) := by
    rw [Module.Basis.det_apply, Matrix.det_unique, Module.Basis.toMatrix_apply,
      Module.Basis.map_apply, Module.Basis.repr_reindex_apply, Module.Basis.repr_reindex_apply]
    rcases finSumFinEquiv.symm ((finCongr _).symm default) with k | k
    · rw [Module.Basis.prod_repr_inl, Module.Basis.singleton_repr]
      rfl
    · exact (k.cast hqi).elim0
  -- `df_y` along `+∂_θ` is `-2 δ` towards `q_j` and `2 δ` towards `q_{j + 1}`.
  have hdf : B.det (bC.map 𝒜) = -(2 * δ) * if i = j then 1 else -1 := by
    obtain ⟨t, rfl⟩ : ∃ t : ℝ, (t : AddCircle (2 * π)) = y := QuotientAddGroup.mk_surjective y
    rw [coe_circleCosTwoMaxCrit, coe_circleCosTwoMinCrit] at hslice
    exact hdet.trans ((mvfderiv_circleCosTwo_coe_reindex_singleton δ r t default).trans
      (congrArg (-(2 * δ) * ·) (sin_eq_of_coe_mem_morseTrajectorySlice hδ hX hslice)))
  have hτ : Orientation.reindex ℝ _ (finCongr (by rw [hqi, finrank_self]))
      ((Module.Basis.singleton (Fin 1) ℝ).orientation.prod c.orientation (finrank_self ℝ)
        (𝔬.chart (circleCosTwoMinCrit δ r i)).finrank_negativeWeight_fun) = B.orientation := by
    rw [Orientation.prod_basis_orientation]; exact (Module.Basis.orientation_reindex _ _).symm
  have hkey : (if Orientation.map _ 𝒜 bC.orientation = B.orientation then (1 : ℤ) else -1) =
      if i = j then -1 else 1 := by
    simp only [← Module.Basis.orientation_map, @eq_comm _ (bC.map 𝒜).orientation,
      Module.Basis.orientation_eq_iff_det_pos, hdf]
    split_ifs <;> first | rfl | (exfalso; nlinarith)
  rcases c.orientation_eq_or_eq_neg (𝔬.orientation (circleCosTwoMinCrit δ r i)) with ho | ho
  · rw [hbC, ho, hτ, hkey, Orientation.signBasis_orientation, Units.val_one, one_mul]
  · rw [hbC, ho, Orientation.prod_neg_right, Orientation.reindex_neg, hτ,
      Orientation.ite_eq_neg_eq_neg_ite hcard, hkey, Orientation.signBasis_neg,
      Orientation.signBasis_orientation, Units.val_neg, Units.val_one, neg_one_mul]

/-- **The integral Morse differential of the circle for the orientations `+∂_θ`.** Let `δ > 0`, let
`X` be a pseudo-gradient adapted to `θ ↦ δ cos (2 (θ - r))`, and let `𝔬` orient the unstable line
of each maximum `p_j = r + j π` by `+∂_θ`, the positive orientation of the circle: the fundamental
sign of `p_j` for this orientation is `1`, that is, the unstable orientation of `p_j` is the
orientation of the circle (`fundamentalSign`). Then the coefficient of the minimum
`q_i = r + π / 2 + i π` in the integral Morse boundary of `p_j` is `-ε_i` if `i = j` and `ε_i`
otherwise, where `ε_i` is the augmentation sign of the orientation at `q_i`. The trajectory from
`p_j` to `q_j` leaves `p_j` in the direction `+∂_θ` and counts negatively, since `+∂_θ` points along
`X` there, while a trajectory counts positively only when the orientation points along `-X`; the
one from `p_j` to `q_{j + 1}` leaves in the direction `-∂_θ` and counts positively. So for the
positive orientations at the minima the differential is `S - I`, and for the negative ones it is
`I - S`, in the ordered bases `(p_0, p_1)` and `(q_0, q_1)`, where `S` exchanges the two
generators. -/
theorem signedMorseBoundaryCoeff_circleCosTwo_eq_augmentationSign_mul (hδ : 0 < δ)
    (hX : IsAdaptedPseudoGradient (circleCosTwo δ r) X)
    (𝔬 : MorseOrientation (circleCosTwo δ r) X)
    (h𝔬 : ∀ j, hX.fundamentalSign 𝔬
      ((AddCircle.orientation (2 * π)).reindex (finCongr (finrank_self ℝ).symm))
      (circleCosTwoMaxCrit δ r j) = 1)
    (i j : Fin 2) :
    hX.signedMorseBoundaryCoeff 𝔬 (circleCosTwoMaxCrit δ r j) (circleCosTwoMinCrit δ r i) =
      𝔬.augmentationSign (circleCosTwoMinCrit δ r i) * if i = j then -1 else 1 := by
  classical
  have hf := isMorse_circleCosTwo hδ.ne' r
  have hMS := isMorseSmale_circleCosTwo hδ.ne' hX
  have hpE := (manifoldMorseIndex_circleCosTwoMaxCrit hδ r j).trans (finrank_self ℝ).symm
  have hpq : manifoldMorseIndex 𝓘(ℝ) (circleCosTwo δ r) (circleCosTwoMaxCrit δ r j) =
      manifoldMorseIndex 𝓘(ℝ) (circleCosTwo δ r) (circleCosTwoMinCrit δ r i) + 1 := by
    rw [hpE, manifoldMorseIndex_circleCosTwoMinCrit hδ, finrank_self]
  obtain ⟨y, hy⟩ := exists_morseTrajectorySlice_circleCosTwo_eq_singleton hδ hX i j
  have hslice : y ∈ hX.morseTrajectorySlice (circleCosTwoMaxCrit δ r j)
      (circleCosTwoMinCrit δ r i) := hy ▸ mem_singleton y
  have hz := hX.mem_morseTrajectorySlice.1 hslice
  have hA := bijective_stableComparison hMS hf (𝔬.coord_mfderiv_chart _) (𝔬.coord_mfderiv_chart _)
    hpE hpq ⟨hz.1, hz.2.1⟩
  -- With the fundamental sign `1` at `p_j`, the sign of the trajectory compares the orientation of
  -- the circle with that of `ℝ × V_q` through `v ↦ (df_y v, N_q v)`.
  have hs := fundamentalSign_mul_trajectorySign hMS hf 𝔬
    ((AddCircle.orientation (2 * π)).reindex (finCongr (finrank_self ℝ).symm)) hpE hpq
    ⟨hz.1, hz.2.1⟩ hA
  rw [h𝔬 j, one_mul] at hs
  rw [signedMorseBoundaryCoeff_of_morseIndex_eq_add_one hpq, signedTrajectoryCount_def, hy,
    finsum_mem_singleton, hs]
  exact ite_map_stableComparison_circleCosTwo hδ hX 𝔬 hslice hA

/-- **Orientations `+∂_θ` realizing the integral Morse differential `I - S` of the circle.** For
`δ > 0` and every pseudo-gradient adapted to `θ ↦ δ cos (2 (θ - r))`, there are orientation data
orienting the unstable line of each maximum `p_j` by `+∂_θ`, its fundamental sign for the positive
orientation of the circle being `1`, and each minimum `q_i` negatively. For these, the integral
Morse differential in the ordered bases `(p_0, p_1)` and `(q_0, q_1)` is
`I - S = [[1, -1], [-1, 1]]`, where `S` exchanges the two generators: the coefficient of `q_i` in
the boundary of `p_j` is `1` when `i = j` and `-1` otherwise. -/
theorem exists_fundamentalSign_augmentationSign_signedMorseBoundaryCoeff_circleCosTwo_eq
    (hδ : 0 < δ) (hX : IsAdaptedPseudoGradient (circleCosTwo δ r) X) :
    ∃ 𝔬 : MorseOrientation (circleCosTwo δ r) X,
      (∀ j, hX.fundamentalSign 𝔬
        ((AddCircle.orientation (2 * π)).reindex (finCongr (finrank_self ℝ).symm))
        (circleCosTwoMaxCrit δ r j) = 1) ∧
      (∀ i, 𝔬.augmentationSign (circleCosTwoMinCrit δ r i) = -1) ∧
      ∀ i j, hX.signedMorseBoundaryCoeff 𝔬 (circleCosTwoMaxCrit δ r j)
        (circleCosTwoMinCrit δ r i) = if i = j then 1 else -1 := by
  classical
  obtain ⟨𝔬₀⟩ := hX.nonempty_morseOrientation
  set oC := (AddCircle.orientation (2 * π)).reindex (finCongr (finrank_self ℝ).symm)
  -- Reverse the maxima not oriented by `+∂_θ` and the positively oriented minima.
  let S : Set (criticalPoints 𝓘(ℝ) (circleCosTwo δ r)) :=
    (circleCosTwoMaxCrit δ r '' {j | hX.fundamentalSign 𝔬₀ oC (circleCosTwoMaxCrit δ r j) = -1}) ∪
      (circleCosTwoMinCrit δ r '' {i | 𝔬₀.augmentationSign (circleCosTwoMinCrit δ r i) = 1})
  have hcond (j : Fin 2) :
      hX.fundamentalSign (𝔬₀.reverse S) oC (circleCosTwoMaxCrit δ r j) = 1 := by
    have hmaxS : circleCosTwoMaxCrit δ r j ∈ S ↔
        hX.fundamentalSign 𝔬₀ oC (circleCosTwoMaxCrit δ r j) = -1 := by
      simp [S]
    rw [fundamentalSign_reverse]
    rcases fundamentalSign_eq_one_or_eq_neg_one (hX := hX) (𝔬 := 𝔬₀) (oM := oC)
      ((manifoldMorseIndex_circleCosTwoMaxCrit hδ r j).trans (finrank_self ℝ).symm) with h | h <;>
      simp [hmaxS, h]
  have haug (i : Fin 2) : (𝔬₀.reverse S).augmentationSign (circleCosTwoMinCrit δ r i) = -1 := by
    have hminS : circleCosTwoMinCrit δ r i ∈ S ↔
        𝔬₀.augmentationSign (circleCosTwoMinCrit δ r i) = 1 := by
      simp [S]
    rw [MorseOrientation.augmentationSign_reverse]
    rcases 𝔬₀.augmentationSign_eq_one_or_eq_neg_one
      (manifoldMorseIndex_circleCosTwoMinCrit hδ r i) with h | h <;> simp [hminS, h]
  refine ⟨𝔬₀.reverse S, hcond, haug, fun i j ↦ ?_⟩
  rw [signedMorseBoundaryCoeff_circleCosTwo_eq_augmentationSign_mul hδ hX _ hcond, haug]
  split_ifs <;> norm_num

end IsAdaptedPseudoGradient

end TauCeti
