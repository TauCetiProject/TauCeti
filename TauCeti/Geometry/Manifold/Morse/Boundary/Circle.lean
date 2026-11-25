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
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import TauCeti.Algebra.AddCircle
import TauCeti.Topology.Order.IntermediateValue

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

These signs are determined by the orientations. The point `r + j π + π / 4`, where `f = 0`, lies
on the trajectory from `p_j` to `q_j` (`coe_mem_unstableSet_circleCosTwoMax`,
`coe_mem_stableSet_circleCosTwoMin`): its orbit cannot cross the maxima `r + j π` and
`r + (j + 1) π` forward in time, nor the minima `r + j π ∓ π / 2` backward, since `f` is monotone
along it. That trajectory leaves `p_j` in the direction `+∂_θ`, along which `f` decreases, and its
sign is read off the orientation of the circle
(`fundamentalSign_mul_trajectorySign_of_finrank_eq_one`). With `ε_j` the fundamental sign of `p_j`
for the positive orientation `AddCircle.orientation` of the circle, `1` exactly when `W^u(p_j)` is
oriented by `+∂_θ`, and `η_i` the augmentation sign of `q_i`, the coefficient of `q_i` in the
integral Morse boundary of `p_j` is `-ε_j η_i` for `i = j` and `ε_j η_i` otherwise
(`signedMorseBoundaryCoeff_circleCosTwo`).

So when the unstable manifolds of both maxima are oriented by `+∂_θ` and both minima negatively,
the integral Morse differential, in the ordered bases `(p_0, p_1)` and `(q_0, q_1)`, is
`D = I - S = [[1, -1], [-1, 1]]`, where `S` exchanges the two generators
(`signedMorseBoundaryCoeff_circleCosTwo_eq_ite`); such orientations exist
(`exists_morseOrientation_fundamentalSign_circleCosTwo_eq_one`). With the positive orientations
at the minima the differential is `S - I`: the trajectory signs measure `T W^u(p)` against the
direction `-X` of the flow followed by `T W^u(q)`.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `isMorseSmale_circleCosTwo`: every pseudo-gradient adapted to `f_r` is Morse–Smale.
* `IsMorseSmale.morseBoundary_single_apply_circleCosTwo`: the mod-two Morse boundary of a maximum
  is the sum of the two minima.
* `exists_augmentationSign_mul_signedMorseBoundaryCoeff_circleCosTwo_eq`: the weighted integral
  boundary coefficients of `p_j` at `q_0` and `q_1` are `ε_j` and `-ε_j`.
* `coe_mem_stableSet_circleCosTwoMin`, `coe_mem_unstableSet_circleCosTwoMax`: the point
  `r + j π + π / 4` lies on a trajectory from `p_j` to `q_j`.
* `morseTrajectorySlice_circleCosTwo_eq`: it is the only trajectory from `p_j` to `q_j`.
* `signedMorseBoundaryCoeff_circleCosTwo`: the integral Morse differential for any orientations,
  in terms of the fundamental signs of the maxima and the augmentation signs of the minima.
* `signedMorseBoundaryCoeff_circleCosTwo_eq_ite`: for the orientations `+∂_θ` of the maxima and
  the negative orientations of the minima, the integral Morse differential is `I - S`.
* `exists_morseOrientation_fundamentalSign_circleCosTwo_eq_one`: these orientations exist.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations and the Morse complex over `ℤ`) and
  §4.1–4.2 (continuation maps).
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

/-! ### The trajectories from a maximum to the next minimum -/

/-- The orbit of `a` under the flow of `X`, lifted to a continuous real function starting at `a`
through the covering map `ℝ → S¹`. -/
private theorem exists_continuous_lift_flow (hX : IsAdaptedPseudoGradient (circleCosTwo δ r) X)
    (a : ℝ) : ∃ Γ : ℝ → ℝ, Continuous Γ ∧ Γ 0 = a ∧
      ∀ t, (Γ t : AddCircle (2 * π)) = hX.flow t a := by
  obtain ⟨Γ, ⟨hΓ0, hΓ⟩, -⟩ := (AddCircle.isCoveringMap_coe (2 * π)).existsUnique_continuousMap_lifts
    ⟨fun t ↦ hX.flow t (a : AddCircle (2 * π)), hX.flow.continuous continuous_id continuous_const⟩
    0 a (by simp)
  exact ⟨Γ, Γ.continuous, hΓ0, fun t ↦ congrFun hΓ t⟩

/-- Let the orbit of `a` under the flow of `X` meet neither the class of `u` nor that of `v` at the
times of `T`, a set of times which contains, with every `t`, all times between `0` and `t`, and let
`a ∈ [u, v]`. Then the lift of the orbit through `a` stays in `[u, v]` at these times, so a limit
of the orbit along a filter containing `T` has a lift in `[u, v]`. -/
private theorem exists_mem_Icc_coe_eq_of_tendsto
    (hX : IsAdaptedPseudoGradient (circleCosTwo δ r) X) {a u v : ℝ} (ha : a ∈ Icc u v)
    {T : Set ℝ} (hT : ∀ t ∈ T, uIcc 0 t ⊆ T)
    (hne : ∀ t ∈ T, hX.flow t a ≠ (u : AddCircle (2 * π)) ∧ hX.flow t a ≠ (v : AddCircle (2 * π)))
    {l : Filter ℝ} [l.NeBot] (hl : T ∈ l) {c : AddCircle (2 * π)}
    (hc : Tendsto (fun t ↦ hX.flow t a) l (nhds c)) :
    ∃ x ∈ Icc u v, (x : AddCircle (2 * π)) = c := by
  obtain ⟨Γ, hΓ, hΓ0, hΓt⟩ := exists_continuous_lift_flow hX a
  -- At the times of `T` the lift never meets `u` or `v`, so it stays in `[u, v]`.
  have hlift (t : ℝ) (ht : t ∈ T) : Γ t ∈ Icc u v :=
    Ioo_subset_Icc_self (isPreconnected_uIcc.forall_mem_Ioo_of_mem_Icc hΓ.continuousOn
      (fun s hs ↦ ⟨fun he ↦ (hne s (hT t ht hs)).1 (by rw [← hΓt s, he]),
        fun he ↦ (hne s (hT t ht hs)).2 (by rw [← hΓt s, he])⟩)
      left_mem_uIcc (hΓ0 ▸ ha) t right_mem_uIcc)
  have hK : IsClosed (((↑) : ℝ → AddCircle (2 * π)) '' Icc u v) :=
    (isCompact_Icc.image (AddCircle.continuous_mk' (2 * π))).isClosed
  exact hK.mem_of_tendsto hc (mem_of_superset hl fun t ht ↦ ⟨Γ t, hlift t ht, hΓt t⟩)

/-- The point `r + j π + π / 4`, halfway between `p_j` and `q_j`, lies on the level `f = 0`. -/
private theorem circleCosTwo_coe_add_pi_div_four (δ r : ℝ) (j : ℕ) :
    circleCosTwo δ r ((r + j * π + π / 4 : ℝ) : AddCircle (2 * π)) = 0 := by
  rw [circleCosTwo_coe, show 2 * (r + j * π + π / 4 - r) = π / 2 + (j : ℝ) * (2 * π) by ring,
    Real.cos_add_nat_mul_two_pi, Real.cos_pi_div_two, mul_zero]

/-- At the maxima `r + n π`, `f = δ`. -/
private theorem circleCosTwo_coe_add_nat_mul_pi (δ r : ℝ) (n : ℕ) :
    circleCosTwo δ r ((r + n * π : ℝ) : AddCircle (2 * π)) = δ := by
  rw [circleCosTwo_coe, show 2 * (r + n * π - r) = (n : ℝ) * (2 * π) by ring,
    Real.cos_nat_mul_two_pi, mul_one]

/-- At the minimum `r + j π - π / 2`, `f = -δ`. -/
private theorem circleCosTwo_coe_add_nat_mul_pi_sub_pi_div_two (δ r : ℝ) (j : ℕ) :
    circleCosTwo δ r ((r + j * π - π / 2 : ℝ) : AddCircle (2 * π)) = -δ := by
  rw [circleCosTwo_coe, show 2 * (r + j * π - π / 2 - r) = -π + (j : ℝ) * (2 * π) by ring,
    Real.cos_add_nat_mul_two_pi, Real.cos_neg, Real.cos_pi, mul_neg_one]

/-- At the minimum `r + j π + π / 2`, `f = -δ`. -/
private theorem circleCosTwo_coe_add_nat_mul_pi_add_pi_div_two (δ r : ℝ) (j : ℕ) :
    circleCosTwo δ r ((r + j * π + π / 2 : ℝ) : AddCircle (2 * π)) = -δ := by
  rw [circleCosTwo_coe, show 2 * (r + j * π + π / 2 - r) = π + (j : ℝ) * (2 * π) by ring,
    Real.cos_add_nat_mul_two_pi, Real.cos_pi, mul_neg_one]

/-- At the point `r + j π + π / 4`, the sine `sin (2 (θ - r))` is `1`. -/
private theorem sin_two_mul_add_pi_div_four_sub (r : ℝ) (j : ℕ) :
    Real.sin (2 * (r + j * π + π / 4 - r)) = 1 := by
  rw [show 2 * (r + j * π + π / 4 - r) = π / 2 + (j : ℝ) * (2 * π) by ring,
    Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two]

/-- The angle `c + i π` of the circle has a lift in `[c + j π - π / 2, c + j π + π / 2]` only for
`i = j`. -/
private theorem eq_of_coe_eq_coe_add_mul_pi {c x : ℝ} {i j : Fin 2}
    (h : (x : AddCircle (2 * π)) = ((c + i * π : ℝ) : AddCircle (2 * π)))
    (hx : x ∈ Icc (c + j * π - π / 2) (c + j * π + π / 2)) : i = j := by
  have hπ := Real.pi_pos
  obtain ⟨hx₁, hx₂⟩ := hx
  -- Both lifts lie within `3π / 2 < 2π` of each other, so they are equal.
  have hxc : x = c + i * π := AddCircle.eq_of_coe_eq_of_abs_sub_lt h (by
    rw [abs_lt]
    fin_cases i <;> fin_cases j <;> simp at hx₁ hx₂ ⊢ <;> constructor <;> linarith)
  fin_cases i <;> fin_cases j <;> simp at hxc hx₁ hx₂ ⊢ <;> linarith

/-- **The point `r + j π + π / 4` flows to the minimum `q_j`.** For `δ > 0` and every adapted
pseudo-gradient, the point halfway between the maximum `p_j = r + j π` and the minimum
`q_j = r + π / 2 + j π` lies on the stable manifold of `q_j`. -/
theorem coe_mem_stableSet_circleCosTwoMin (hδ : 0 < δ)
    (hX : IsAdaptedPseudoGradient (circleCosTwo δ r) X) (j : Fin 2) :
    ((r + j * π + π / 4 : ℝ) : AddCircle (2 * π)) ∈ hX.flow.stableSet (circleCosTwoMin r j) := by
  have hπ := Real.pi_pos
  obtain ⟨c, hc, hac⟩ := hX.exists_mem_stableSet (isMorse_circleCosTwo hδ.ne' r)
    ((r + j * π + π / 4 : ℝ) : AddCircle (2 * π))
  -- Along the forward orbit of `r + j π + π / 4`, where `f` starts at `0`, `f ≤ 0`.
  have hle (t : ℝ) (ht : 0 ≤ t) :
      circleCosTwo δ r (hX.flow t ((r + j * π + π / 4 : ℝ) : AddCircle (2 * π))) ≤ 0 := by
    simpa only [Flow.map_zero_apply, circleCosTwo_coe_add_pi_div_four] using
      hX.antitone_flow ((r + j * π + π / 4 : ℝ) : AddCircle (2 * π)) ht
  -- So it never meets the maxima `r + j π` and `r + j π + π`, where `f = δ`, and the limit `c`
  -- has a lift between them.
  obtain ⟨x, hx, hxc⟩ := exists_mem_Icc_coe_eq_of_tendsto hX (u := r + j * π)
    (v := r + j * π + π) (by constructor <;> linarith)
    (fun t ht ↦ by rw [uIcc_of_le ht]; exact fun s hs ↦ hs.1)
    (fun t ht ↦ ⟨fun he ↦ by
      have h := hle t ht
      rw [he, circleCosTwo_coe_add_nat_mul_pi] at h
      linarith, fun he ↦ by
      have h := hle t ht
      rw [he, show r + j * π + π = r + ((j + 1 : ℕ) : ℝ) * π by push_cast; ring,
        circleCosTwo_coe_add_nat_mul_pi] at h
      linarith⟩)
    (Ici_mem_atTop 0) (Flow.mem_stableSet.1 hac)
  -- As `f c ≤ 0`, `c` is the minimum `q_j`.
  have hfc : circleCosTwo δ r c ≤ 0 :=
    le_of_tendsto (((contMDiff_circleCosTwo δ r).continuous.tendsto c).comp
      (Flow.mem_stableSet.1 hac))
      (eventually_atTop.2 ⟨0, hle⟩)
  obtain ⟨i, hi | hi⟩ := (mem_criticalPoints_circleCosTwo_iff_exists hδ.ne' r).1
    (mem_criticalPoints_iff_mfderiv_eq_zero.2 hc)
  · rw [hi, circleCosTwo_circleCosTwoMax] at hfc
    linarith
  · rw [hi, circleCosTwoMin_def] at hxc
    obtain rfl := eq_of_coe_eq_coe_add_mul_pi (j := j) hxc
      (by constructor <;> linarith [hx.1, hx.2])
    exact hi ▸ hac

/-- **The point `r + j π + π / 4` comes from the maximum `p_j`.** For `δ > 0` and every adapted
pseudo-gradient, the point halfway between the maximum `p_j = r + j π` and the minimum
`q_j = r + π / 2 + j π` lies on the unstable manifold of `p_j`. -/
theorem coe_mem_unstableSet_circleCosTwoMax (hδ : 0 < δ)
    (hX : IsAdaptedPseudoGradient (circleCosTwo δ r) X) (j : Fin 2) :
    ((r + j * π + π / 4 : ℝ) : AddCircle (2 * π)) ∈
      hX.flow.unstableSet (circleCosTwoMax r j) := by
  have hπ := Real.pi_pos
  obtain ⟨c, hc, hac⟩ := hX.exists_mem_unstableSet (isMorse_circleCosTwo hδ.ne' r)
    ((r + j * π + π / 4 : ℝ) : AddCircle (2 * π))
  -- Along the backward orbit of `r + j π + π / 4`, where `f` starts at `0`, `f ≥ 0`.
  have hge (t : ℝ) (ht : t ≤ 0) :
      0 ≤ circleCosTwo δ r (hX.flow t ((r + j * π + π / 4 : ℝ) : AddCircle (2 * π))) := by
    simpa only [Flow.map_zero_apply, circleCosTwo_coe_add_pi_div_four] using
      hX.antitone_flow ((r + j * π + π / 4 : ℝ) : AddCircle (2 * π)) ht
  -- So it never meets the minima `r + j π ∓ π / 2`, where `f = -δ`, and the limit `c` has a lift
  -- between them.
  obtain ⟨x, hx, hxc⟩ := exists_mem_Icc_coe_eq_of_tendsto hX (u := r + j * π - π / 2)
    (v := r + j * π + π / 2) (by constructor <;> linarith)
    (fun t ht ↦ by rw [uIcc_of_ge ht]; exact fun s hs ↦ hs.2)
    (fun t ht ↦ ⟨fun he ↦ by
      have h := hge t ht
      rw [he, circleCosTwo_coe_add_nat_mul_pi_sub_pi_div_two] at h
      linarith, fun he ↦ by
      have h := hge t ht
      rw [he, circleCosTwo_coe_add_nat_mul_pi_add_pi_div_two] at h
      linarith⟩)
    (Iic_mem_atBot 0) (Flow.mem_unstableSet.1 hac)
  -- As `f c ≥ 0`, `c` is the maximum `p_j`.
  have hfc : 0 ≤ circleCosTwo δ r c :=
    ge_of_tendsto (((contMDiff_circleCosTwo δ r).continuous.tendsto c).comp
      (Flow.mem_unstableSet.1 hac))
      (eventually_atBot.2 ⟨0, hge⟩)
  obtain ⟨i, hi | hi⟩ := (mem_criticalPoints_circleCosTwo_iff_exists hδ.ne' r).1
    (mem_criticalPoints_iff_mfderiv_eq_zero.2 hc)
  · rw [hi, circleCosTwoMax_def] at hxc
    obtain rfl := eq_of_coe_eq_coe_add_mul_pi hxc hx
    exact hi ▸ hac
  · rw [hi, circleCosTwo_circleCosTwoMin] at hfc
    linarith

/-! ### The integral Morse differential for the orientation of the circle -/

/-- **The trajectory from `p_j` to `q_j`.** For `δ > 0` and every adapted pseudo-gradient, there is
exactly one trajectory from the maximum `p_j = r + j π` to the minimum `q_j = r + π / 2 + j π`, and
it crosses the middle level `f = 0` at `r + j π + π / 4`. -/
theorem morseTrajectorySlice_circleCosTwo_eq (hδ : 0 < δ)
    (hX : IsAdaptedPseudoGradient (circleCosTwo δ r) X) (j : Fin 2) :
    hX.morseTrajectorySlice (circleCosTwoMax r j) (circleCosTwoMin r j) =
      {((r + j * π + π / 4 : ℝ) : AddCircle (2 * π))} := by
  have hf := isMorse_circleCosTwo hδ.ne' r
  set z := ((r + j * π + π / 4 : ℝ) : AddCircle (2 * π))
  have hz : z ∈ hX.morseTrajectorySlice (circleCosTwoMax r j) (circleCosTwoMin r j) := by
    refine (hX.mem_morseTrajectorySlice).2 ⟨coe_mem_unstableSet_circleCosTwoMax hδ hX j,
      coe_mem_stableSet_circleCosTwoMin hδ hX j, ?_⟩
    rw [circleCosTwo_circleCosTwoMax, circleCosTwo_circleCosTwoMin,
      circleCosTwo_coe_add_pi_div_four]
    ring
  -- The slice from `p_j` to a critical point of index `0` is empty or a single point.
  obtain ⟨q₀, q₁, -, -, -, ⟨y₀, hy₀⟩, ⟨y₁, hy₁⟩, hempty⟩ :=
    hX.exists_ne_morseTrajectorySlice_eq_singleton_of_finrank_eq_one hf (finrank_self ℝ)
      (p := circleCosTwoMaxCrit δ r j) (c := circleCosTwoMaxCrit δ r (j + 1))
      (manifoldMorseIndex_circleCosTwoMaxCrit hδ r j) (circleCosTwoMaxCrit_add_one_ne δ r j)
      (by rw [manifoldMorseIndex_circleCosTwoMaxCrit hδ]; exact one_ne_zero)
  rw [coe_circleCosTwoMaxCrit] at hy₀ hy₁ hempty
  by_cases h₀ : circleCosTwoMin r j = q₀
  · rw [h₀, hy₀] at hz ⊢
    rw [mem_singleton_iff.1 hz]
  by_cases h₁ : circleCosTwoMin r j = q₁
  · rw [h₁, hy₁] at hz ⊢
    rw [mem_singleton_iff.1 hz]
  rw [hempty _ (circleCosTwoMin_ne_circleCosTwoMax r j j) h₀ h₁] at hz
  exact hz.elim

/-- The coefficient of `q_j` in the integral Morse boundary of `p_j` is the sign of the
trajectory through `z = r + j π + π / 4`, where `f` decreases in the direction `+∂_θ`. -/
private theorem signedMorseBoundaryCoeff_circleCosTwo_self (hδ : 0 < δ)
    (hX : IsAdaptedPseudoGradient (circleCosTwo δ r) X)
    (𝔬 : MorseOrientation (circleCosTwo δ r) X) (j : Fin 2) :
    hX.signedMorseBoundaryCoeff 𝔬 (circleCosTwoMaxCrit δ r j) (circleCosTwoMinCrit δ r j) =
      -hX.fundamentalSign 𝔬
          ((AddCircle.orientation (2 * π)).reindex (finCongr (finrank_self ℝ).symm))
          (circleCosTwoMaxCrit δ r j) *
        𝔬.augmentationSign (circleCosTwoMinCrit δ r j) := by
  set oM := (AddCircle.orientation (2 * π)).reindex (finCongr (finrank_self ℝ).symm)
  have hpq : manifoldMorseIndex 𝓘(ℝ) (circleCosTwo δ r) (circleCosTwoMaxCrit δ r j) =
      manifoldMorseIndex 𝓘(ℝ) (circleCosTwo δ r) (circleCosTwoMinCrit δ r j) + 1 := by
    rw [manifoldMorseIndex_circleCosTwoMaxCrit hδ, manifoldMorseIndex_circleCosTwoMinCrit hδ]
  set z := ((r + j * π + π / 4 : ℝ) : AddCircle (2 * π))
  have hz : z ∈ hX.flow.unstableSet (circleCosTwoMaxCrit δ r j) ∩
      hX.flow.stableSet (circleCosTwoMinCrit δ r j) := by
    rw [coe_circleCosTwoMaxCrit, coe_circleCosTwoMinCrit]
    exact ⟨coe_mem_unstableSet_circleCosTwoMax hδ hX j, coe_mem_stableSet_circleCosTwoMin hδ hX j⟩
  set b := (Module.Basis.singleton (Fin 1) ℝ).reindex (finCongr (finrank_self ℝ).symm)
  -- The tangent spaces of the circle are `ℝ`, read through the local real lifts.
  have hb : b.orientation = oM.orientationAt z := by
    rw [Manifold.Orientation.orientationAt_reindex, AddCircle.orientationAt_orientation,
      Module.Basis.orientation_reindex]
    rfl
  have hsign := fundamentalSign_mul_trajectorySign_of_finrank_eq_one
    (isMorse_circleCosTwo hδ.ne' r) (finrank_self ℝ) 𝔬 oM hpq hz b hb ⟨0, by simp⟩
  -- At `z`, `df` is `-2 δ` on the positive tangent vector `b 0 = 1`.
  have hd : mvfderiv 𝓘(ℝ) (circleCosTwo δ r) z (b ⟨0, by simp⟩) = -(2 * δ) := by
    have hb0 : b ⟨0, by simp⟩ = 1 := by simp [b]
    rw [mvfderiv_circleCosTwo_coe, sin_two_mul_add_pi_div_four_sub, mul_one, hb0]
    -- The map `u ↦ u • c` is applied to `1`, a tangent vector of the circle read in `ℝ`.
    exact (ContinuousLinearMap.smulRight_apply (c := (1 : ℝ →L[ℝ] ℝ)) (x := (1 : ℝ))).trans
      (by rw [one_apply_eq_self, one_smul])
  have hs : 𝔬.augmentationSign (circleCosTwoMinCrit δ r j) *
        (SignType.sign (mvfderiv 𝓘(ℝ) (circleCosTwo δ r) z (b ⟨0, by simp⟩)) : ℤ) =
      -𝔬.augmentationSign (circleCosTwoMinCrit δ r j) := by
    rw [hd, sign_neg (by linarith)]
    simp
  have hsign' := hsign.trans hs
  have hslice : hX.morseTrajectorySlice (circleCosTwoMaxCrit δ r j)
      (circleCosTwoMinCrit δ r j) = {z} := by
    rw [coe_circleCosTwoMaxCrit, coe_circleCosTwoMinCrit]
    exact morseTrajectorySlice_circleCosTwo_eq hδ hX j
  rw [signedMorseBoundaryCoeff_of_morseIndex_eq_add_one hpq, signedTrajectoryCount_def, hslice,
    finsum_mem_singleton]
  rcases fundamentalSign_eq_one_or_eq_neg_one (hX := hX) (𝔬 := 𝔬) (oM := oM)
    ((manifoldMorseIndex_circleCosTwoMaxCrit hδ r j).trans (finrank_self ℝ).symm) with h | h <;>
    rw [h] at hsign' ⊢ <;> linarith

/-- **The integral Morse differential of the circle.** For `δ > 0`, every adapted pseudo-gradient
and every choice of orientations of the unstable manifolds, the coefficient of the minimum
`q_i = r + π / 2 + i π` in the integral Morse boundary of the maximum `p_j = r + j π` is
`-ε_j η_i` for `i = j` and `ε_j η_i` otherwise. Here `ε_j` is the fundamental sign of `p_j` for the
positive orientation of the circle, `1` when the unstable manifold of `p_j` is oriented by `+∂_θ`,
and `η_i` is the augmentation sign of `q_i`. The trajectory from `p_j` to `q_j` runs in the
direction `+∂_θ`, along which `f` decreases. -/
theorem signedMorseBoundaryCoeff_circleCosTwo (hδ : 0 < δ)
    (hX : IsAdaptedPseudoGradient (circleCosTwo δ r) X)
    (𝔬 : MorseOrientation (circleCosTwo δ r) X) (i j : Fin 2) :
    hX.signedMorseBoundaryCoeff 𝔬 (circleCosTwoMaxCrit δ r j) (circleCosTwoMinCrit δ r i) =
      (if i = j then -1 else 1) *
        hX.fundamentalSign 𝔬
          ((AddCircle.orientation (2 * π)).reindex (finCongr (finrank_self ℝ).symm))
          (circleCosTwoMaxCrit δ r j) *
        𝔬.augmentationSign (circleCosTwoMinCrit δ r i) := by
  set oM := (AddCircle.orientation (2 * π)).reindex (finCongr (finrank_self ℝ).symm)
  have hη (k : Fin 2) := 𝔬.augmentationSign_eq_one_or_eq_neg_one
    (manifoldMorseIndex_circleCosTwoMinCrit hδ r k)
  have hdiag := signedMorseBoundaryCoeff_circleCosTwo_self hδ hX 𝔬 j
  by_cases hij : i = j
  · subst hij
    rw [hdiag, ite_eq_left rfl]
    ring
  -- The two coefficients of `p_j`, weighted by the augmentation signs, are opposite.
  obtain ⟨e, -, he⟩ := hX.exists_augmentationSign_mul_signedMorseBoundaryCoeff_circleCosTwo_eq hδ 𝔬
  have hηi := hη i
  have hηj := hη j
  set ε := hX.fundamentalSign 𝔬 oM (circleCosTwoMaxCrit δ r j)
  set A := 𝔬.augmentationSign (circleCosTwoMinCrit δ r i)
  set B := 𝔬.augmentationSign (circleCosTwoMinCrit δ r j)
  set C := hX.signedMorseBoundaryCoeff 𝔬 (circleCosTwoMaxCrit δ r j) (circleCosTwoMinCrit δ r i)
  have hopp : A * C = -(B * (-ε * B)) := by
    rw [← hdiag, he, he]
    -- As `i ≠ j` in `Fin 2`, exactly one of them is `0`.
    by_cases hi : i = 0
    · rw [ite_eq_left hi, ite_eq_right (by omega : j ≠ 0), neg_neg]
    · rw [ite_eq_right hi, ite_eq_left (by omega : j = 0)]
  have hA : A * A = 1 := by rcases hηi with h | h <;> rw [h] <;> norm_num
  have hB : B * B = 1 := by rcases hηj with h | h <;> rw [h] <;> norm_num
  rw [ite_eq_right hij]
  linear_combination (-C) * hA + A * hopp + ε * A * hB

/-- **The circle differential `I - S`.** Orient the unstable manifolds of both maxima by `+∂_θ`,
that is with fundamental sign `1` for the positive orientation of the circle, and both minima
negatively, with augmentation sign `-1`. Then the integral Morse differential of
`θ ↦ δ cos (2 (θ - r))`, in the ordered bases `(p_0, p_1)` and `(q_0, q_1)`, is
`I - S = [[1, -1], [-1, 1]]`, where `S` exchanges the two generators: the coefficient of `q_i` in
the boundary of `p_j` is `1` when `i = j` and `-1` otherwise. With the positive orientations at the
minima it is `S - I` (`signedMorseBoundaryCoeff_circleCosTwo`). -/
theorem signedMorseBoundaryCoeff_circleCosTwo_eq_ite (hδ : 0 < δ)
    (hX : IsAdaptedPseudoGradient (circleCosTwo δ r) X)
    {𝔬 : MorseOrientation (circleCosTwo δ r) X}
    (hmax : ∀ j, hX.fundamentalSign 𝔬
      ((AddCircle.orientation (2 * π)).reindex (finCongr (finrank_self ℝ).symm))
      (circleCosTwoMaxCrit δ r j) = 1)
    (hmin : ∀ i, 𝔬.augmentationSign (circleCosTwoMinCrit δ r i) = -1) (i j : Fin 2) :
    hX.signedMorseBoundaryCoeff 𝔬 (circleCosTwoMaxCrit δ r j) (circleCosTwoMinCrit δ r i) =
      if i = j then 1 else -1 := by
  rw [signedMorseBoundaryCoeff_circleCosTwo hδ hX 𝔬 i j, hmax, hmin]
  split_ifs <;> norm_num

/-- **Orientations `+∂_θ` exist.** For `δ > 0` and every pseudo-gradient adapted to
`θ ↦ δ cos (2 (θ - r))`, there are orientations of the unstable manifolds orienting both maxima by
`+∂_θ` (fundamental sign `1` for the positive orientation of the circle) and both minima
negatively (augmentation sign `-1`); for these the integral Morse differential is `I - S`
(`signedMorseBoundaryCoeff_circleCosTwo_eq_ite`). -/
theorem exists_morseOrientation_fundamentalSign_circleCosTwo_eq_one (hδ : 0 < δ)
    (hX : IsAdaptedPseudoGradient (circleCosTwo δ r) X) :
    ∃ 𝔬 : MorseOrientation (circleCosTwo δ r) X,
      (∀ j, hX.fundamentalSign 𝔬
        ((AddCircle.orientation (2 * π)).reindex (finCongr (finrank_self ℝ).symm))
        (circleCosTwoMaxCrit δ r j) = 1) ∧
      ∀ i, 𝔬.augmentationSign (circleCosTwoMinCrit δ r i) = -1 := by
  classical
  set oM := (AddCircle.orientation (2 * π)).reindex (finCongr (finrank_self ℝ).symm)
  obtain ⟨𝔬₀⟩ := hX.nonempty_morseOrientation
  -- Reverse the orientations at the maxima of sign `-1` and at the minima of sign `1`.
  refine ⟨𝔬₀.reverse {p | hX.fundamentalSign 𝔬₀ oM p = -1 ∨ 𝔬₀.augmentationSign p = 1},
    fun j ↦ ?_, fun i ↦ ?_⟩
  · have hj := (manifoldMorseIndex_circleCosTwoMaxCrit hδ r j).trans (finrank_self ℝ).symm
    have haug : 𝔬₀.augmentationSign (circleCosTwoMaxCrit δ r j) = 0 :=
      𝔬₀.augmentationSign_of_morseIndex_ne_zero (by rw [hj, finrank_self]; exact one_ne_zero)
    rw [fundamentalSign_reverse]
    rcases fundamentalSign_eq_one_or_eq_neg_one (hX := hX) (𝔬 := 𝔬₀) (oM := oM) hj with h | h <;>
      simp [h, haug]
  · have hfund : hX.fundamentalSign 𝔬₀ oM (circleCosTwoMinCrit δ r i) = 0 :=
      fundamentalSign_of_morseIndex_ne (by
        rw [manifoldMorseIndex_circleCosTwoMinCrit hδ, finrank_self]; exact zero_ne_one)
    rw [MorseOrientation.augmentationSign_reverse]
    rcases 𝔬₀.augmentationSign_eq_one_or_eq_neg_one
      (manifoldMorseIndex_circleCosTwoMinCrit hδ r i) with h | h <;> simp [h, hfund]

end IsAdaptedPseudoGradient

end TauCeti
