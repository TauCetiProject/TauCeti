/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.DiscCharge.SliceMeasure
public import TauCeti.Analysis.PDE.SeibergWitten.ZeroSet.Localization

/-!
# Roots of the Newton polynomial of a slice and the zeros of the field

In Taubes's analysis of Seiberg–Witten solutions near a pseudoholomorphic curve, the cutoff
current `Θ = i F_a + d(χ(|α|²) τ)` (`TauCeti.SeibergWitten.cutoffCurrent`) is sliced by the
dilated normal discs `σ` of the curve. The normalized slice `f dλ / 2π` on the closed disc of
radius `R`, with `f` the slice density (`TauCeti.SeibergWitten.sliceDensity`), is a signed
measure of mass `m`; the roots of the Newton polynomial `P` of degree `m` of its moments are the
candidate positions of the local branches of the limiting curve in the normal fibre. By the
compact moment lemma (`TauCeti.SeibergWitten.exists_forall_abs_setIntegral_mul_sub_sum_roots_le`),
once the negative mass and the Newton variance `∫ |P|² dμ⁺` are small, the slice is close, in the
bounded-Lipschitz distance, to the counting measure of the roots of `P`. This file compares the
roots of `P` with the places where the slice lives, in both directions.

* **No root is missed.** Near every root of `P` the slice density does not vanish
  (`TauCeti.SeibergWitten.exists_forall_mem_roots_exists_dist_lt_ne_zero`). For the cutoff
  current, a point where the slice density does not vanish lies on the support of `Θ`, where
  `|α|² ≤ 1 / 2`, and so, by Taubes's off-zero bound relative to a set `Z` (playing the role of
  the zero set of `α`), within distance `K h` of a point of `Z`
  (`TauCeti.SeibergWitten.exists_forall_exists_dist_le_of_mem_tsupport_cutoffCurrent`). Hence
  every root `V` of `P` has a disc point `w` with `|w - V| < ε` and a point of `Z` within
  distance `K h` of `σ w` (`TauCeti.SeibergWitten.exists_forall_mem_roots_exists_dist_le`), and
  so, for an `L`-Lipschitz disc, a point of `Z` within distance `L ε + K h` of `σ(V)`
  (`TauCeti.SeibergWitten.exists_forall_mem_roots_exists_dist_le_add_mul`). The point of `Z` may
  lie on a neighbouring slice: the distance is the one of the ambient space.
* **No charged core is a ghost.** A subdisc carrying normalized charge at least `1` lies within
  `ε` of a root of `P` (`TauCeti.SeibergWitten.exists_forall_exists_mem_roots_dist_lt`). For the
  cutoff current, the charge of a subdisc whose boundary circle lies in the vacuum `χ(|α|²) = 1`
  is the winding number of `α ∘ σ` around that circle
  (`TauCeti.SeibergWitten.exists_int_integral_cutoffCurrent_comp_closedBall`), so the centre of
  a vacuum circle of radius `ρ₁` around which `α ∘ σ` has positive winding number lies within
  `ρ₁ + ε` of a root
  (`TauCeti.SeibergWitten.exists_forall_exists_mem_roots_dist_lt_of_windingNumber`).

In each statement the tolerance `δ`, and the constants `K` and `r₀`, are chosen before the field,
the disc and the slice, so the comparison is uniform over all fields and discs. The
two hypotheses that the coupled equations have to supply are not proved here: the smallness of
the Newton variance, and the positivity of the winding number of the field around its zeros.

Both comparisons rest on two elementary facts about a density whose normalized slice is within
`ε` of the counting measure of a multiset `S` against `1`-Lipschitz functions bounded by `1`:
within every `ρ > ε` of a point of `S` the density does not vanish
(`TauCeti.SeibergWitten.exists_mem_closedBall_dist_lt_ne_zero`), and a subdisc of radius `ρ₁`
carrying charge `κ` has a point of `S` within `ρ` once `ε < (ρ - ρ₁) (κ - ν)`, where `ν` bounds
the negative mass (`TauCeti.SeibergWitten.exists_mem_dist_lt_of_le_setIntegral`). Both are
tested against a tent function.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

open Complex Metric MeasureTheory Polynomial Set
open scoped Real

namespace TauCeti.SeibergWitten

universe u

/-! ### Atoms of a bounded-Lipschitz approximation -/

/-- **No point of the approximating multiset is missed.** Let `f` be a density whose normalized
slice `f dλ / 2π` on the closed disc of radius `R` is within `ε < 1` of the counting measure of a
multiset `S`, against every `1`-Lipschitz function bounded by `1`. Then for every `ρ > ε`, within
distance `ρ` of every point of `S` there is a point of the disc where `f` does not vanish. -/
theorem exists_mem_closedBall_dist_lt_ne_zero {f : ℂ → ℝ} {R ε ρ : ℝ} {S : Multiset ℂ}
    (hS : ∀ g : ℂ → ℝ, LipschitzWith 1 g → (∀ w, |g w| ≤ 1) →
      |(2 * π)⁻¹ * (∫ w in closedBall 0 R, f w * g w) - (S.map g).sum| ≤ ε)
    (hε : ε < 1) (hερ : ε < ρ) {V : ℂ} (hV : V ∈ S) :
    ∃ w ∈ closedBall (0 : ℂ) R, dist w V < ρ ∧ f w ≠ 0 := by
  by_contra! hf
  -- The tent `g w = max (t - |w - V|) 0`, of height `t = min ρ 1` at `V`, lives where `f = 0`.
  set t := min ρ 1
  have hεt : ε < t := lt_min hερ hε
  set g : ℂ → ℝ := fun w ↦ max (t - dist w V) 0 with hg
  have hgL : LipschitzWith 1 g := by
    simpa using ((LipschitzWith.const t).sub (LipschitzWith.dist_left V)).max_const 0
  have hg₀ (w : ℂ) : 0 ≤ g w := le_max_right _ _
  have hg₁ (w : ℂ) : |g w| ≤ 1 := by
    rw [abs_of_nonneg (hg₀ w)]
    exact max_le (by linarith [dist_nonneg (x := w) (y := V), min_le_right ρ 1]) zero_le_one
  have hint : ∫ w in closedBall 0 R, f w * g w = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun w hw ↦ ?_
    rcases lt_or_ge (dist w V) t with hlt | hge
    · rw [hf w hw (hlt.trans_le (min_le_left _ _)), zero_mul]
    · rw [show g w = 0 from max_eq_right (by linarith), mul_zero]
  have := hS g hgL hg₁
  have ht₀ : 0 ≤ t := by linarith [(abs_nonneg _).trans this]
  have hgV : g V = t := by
    simp only [hg, dist_self, sub_zero]
    exact max_eq_left ht₀
  have hsum : t ≤ (S.map g).sum := hgV ▸ Multiset.single_le_sum (fun x hx ↦ by
    obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 hx
    exact hg₀ y) (g V) (Multiset.mem_map_of_mem g hV)
  rw [hint, mul_zero, zero_sub, abs_neg, abs_of_nonneg (by linarith)] at this
  linarith

/-- **A charged subdisc is near a point of the approximating multiset.** Let `f` be a density,
integrable on the closed disc of radius `R`, whose normalized slice `f dλ / 2π` on that disc is
within `ε` of the counting measure of a multiset `S`, against every `1`-Lipschitz function bounded
by `1`, and whose negative slice measure has mass at most `ν`. If a closed subdisc of radius `ρ₁`
about `w₀` carries normalized charge `(2π)⁻¹ ∫ f ≥ κ`, then for `ρ₁ < ρ ≤ ρ₁ + 1` with
`ε < (ρ - ρ₁) (κ - ν)` some point of `S` lies within distance `ρ` of `w₀`. -/
theorem exists_mem_dist_lt_of_le_setIntegral {f : ℂ → ℝ} {R ε ρ₁ ρ κ ν : ℝ} {S : Multiset ℂ}
    (hS : ∀ g : ℂ → ℝ, LipschitzWith 1 g → (∀ w, |g w| ≤ 1) →
      |(2 * π)⁻¹ * (∫ w in closedBall 0 R, f w * g w) - (S.map g).sum| ≤ ε)
    (hf : IntegrableOn f (closedBall 0 R)) (hν : (negSliceMeasure f R).real univ ≤ ν)
    {w₀ : ℂ} (hsub : closedBall w₀ ρ₁ ⊆ closedBall 0 R)
    (hκ : κ ≤ (2 * π)⁻¹ * ∫ w in closedBall w₀ ρ₁, f w)
    (hρ₁ : ρ₁ < ρ) (hρ : ρ ≤ ρ₁ + 1) (hε : ε < (ρ - ρ₁) * (κ - ν)) :
    ∃ V ∈ S, dist V w₀ < ρ := by
  by_contra! hS'
  set t := ρ - ρ₁ with ht
  have ht₀ : 0 < t := by linarith
  -- The tent `g`, equal to `t` on the subdisc and to `0` off the open disc of radius `ρ`,
  -- vanishes at every point of `S`.
  set g : ℂ → ℝ := fun w ↦ max (min t (ρ - dist w w₀)) 0 with hg
  have hgL : LipschitzWith 1 g := by
    simpa using (((LipschitzWith.const ρ).sub (LipschitzWith.dist_left w₀)).const_min t).max_const 0
  have hg₀ (w : ℂ) : 0 ≤ g w := le_max_right _ _
  have hgt (w : ℂ) : g w ≤ t := max_le (min_le_left _ _) ht₀.le
  have hg₁ (w : ℂ) : |g w| ≤ 1 := by
    rw [abs_of_nonneg (hg₀ w)]
    linarith [hgt w]
  have hgS : (S.map g).sum = 0 := Multiset.sum_eq_zero fun x hx ↦ by
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
    exact max_eq_right <| (min_le_right _ _).trans (by linarith [hS' y hy])
  have hupper := hS g hgL hg₁
  rw [hgS, sub_zero] at hupper
  -- Pointwise on the disc, `f g ≥ t f 1_{B₁} - t f⁻`, where `B₁` is the subdisc.
  have hpt : ∀ w ∈ closedBall (0 : ℂ) R,
      t * (closedBall w₀ ρ₁).indicator f w - t * (f w)⁻ ≤ f w * g w := by
    intro w _
    have hpn := posPart_sub_negPart (f w)
    by_cases hw : w ∈ closedBall w₀ ρ₁
    · have : g w = t := by
        simp only [hg]
        rw [min_eq_left (by linarith [mem_closedBall.1 hw]), max_eq_left ht₀.le]
      rw [indicator_of_mem hw, this]
      nlinarith [negPart_nonneg (f w)]
    · rw [indicator_of_notMem hw]
      nlinarith [hg₀ w, hgt w, posPart_nonneg (f w), negPart_nonneg (f w)]
  have hind : IntegrableOn (fun w ↦ t * (closedBall w₀ ρ₁).indicator f w) (closedBall 0 R) :=
    (hf.indicator measurableSet_closedBall).const_mul t
  have hneg : IntegrableOn (fun w ↦ t * (f w)⁻) (closedBall 0 R) := hf.neg_part.const_mul t
  have hlower : ∫ w in closedBall 0 R, (t * (closedBall w₀ ρ₁).indicator f w - t * (f w)⁻) ≤
      ∫ w in closedBall 0 R, f w * g w :=
    setIntegral_mono_on (hind.sub hneg)
      (hf.mul_continuousOn hgL.continuous.continuousOn (isCompact_closedBall 0 R))
      measurableSet_closedBall hpt
  rw [integral_sub hind hneg, integral_const_mul, integral_const_mul,
    setIntegral_indicator measurableSet_closedBall, inter_eq_right.2 hsub] at hlower
  rw [measureReal_negSliceMeasure hf.aemeasurable] at hν
  have := mul_le_mul_of_nonneg_left hlower (by positivity : (0 : ℝ) ≤ (2 * π)⁻¹)
  nlinarith [abs_le.1 hupper]

/-! ### Roots of the Newton polynomial of a slice -/

/-- **No root of the Newton polynomial is missed.** For every accuracy `ε > 0` there is a
tolerance `δ > 0`, depending only on `m`, `R` and `ε`, with the following property. Let `f` be a
density integrable on the closed disc of radius `R` whose normalized slice has mass `m`, negative
mass at most `δ` and Newton variance `∫ |P|² dμ⁺` at most `δ`, where `P` is the Newton polynomial
of degree `m` of its moments. Then within distance `ε` of every root of `P` there is a point of
the disc where `f` does not vanish. -/
theorem exists_forall_mem_roots_exists_dist_lt_ne_zero (m : ℕ) (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ f : ℂ → ℝ, IntegrableOn f (closedBall 0 R) →
      (posSliceMeasure f R).real univ - (negSliceMeasure f R).real univ = m →
      (negSliceMeasure f R).real univ ≤ δ →
      ∫ w, ‖(newtonPolynomial (fun k ↦ ∫ w, w ^ k ∂posSliceMeasure f R -
        ∫ w, w ^ k ∂negSliceMeasure f R) m).eval w‖ ^ 2 ∂posSliceMeasure f R ≤ δ →
      ∀ V ∈ (newtonPolynomial (fun k ↦ ∫ w, w ^ k ∂posSliceMeasure f R -
        ∫ w, w ^ k ∂negSliceMeasure f R) m).roots,
        ∃ w ∈ closedBall (0 : ℂ) R, dist w V < ε ∧ f w ≠ 0 := by
  have hε₁ : 0 < min ε 1 := lt_min hε one_pos
  obtain ⟨δ, hδ, h⟩ := exists_forall_abs_setIntegral_mul_sub_sum_roots_le m R (half_pos hε₁)
  refine ⟨δ, hδ, fun f hf hmass hneg hvar V hV ↦ ?_⟩
  exact exists_mem_closedBall_dist_lt_ne_zero (h f hf hmass hneg hvar)
    ((half_lt_self hε₁).trans_le (min_le_right _ _))
    ((half_lt_self hε₁).trans_le (min_le_left _ _)) hV

/-- **No charged core is a ghost.** For every accuracy `ε > 0` there is a tolerance `δ > 0`,
depending only on `m`, `R` and `ε`, with the following property. Let `f` be a density integrable
on the closed disc of radius `R` whose normalized slice has mass `m`, negative mass at most `δ`
and Newton variance `∫ |P|² dμ⁺` at most `δ`, where `P` is the Newton polynomial of degree `m` of
its moments. Then every closed subdisc, of radius `ρ₁` about `w₀`, carrying normalized charge
`(2π)⁻¹ ∫ f` at least `1` lies within distance `ρ₁ + ε` of a root of `P`: some root `V` has
`|V - w₀| < ρ₁ + ε`. -/
theorem exists_forall_exists_mem_roots_dist_lt (m : ℕ) (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ f : ℂ → ℝ, IntegrableOn f (closedBall 0 R) →
      (posSliceMeasure f R).real univ - (negSliceMeasure f R).real univ = m →
      (negSliceMeasure f R).real univ ≤ δ →
      ∫ w, ‖(newtonPolynomial (fun k ↦ ∫ w, w ^ k ∂posSliceMeasure f R -
        ∫ w, w ^ k ∂negSliceMeasure f R) m).eval w‖ ^ 2 ∂posSliceMeasure f R ≤ δ →
      ∀ (w₀ : ℂ) (ρ₁ : ℝ), closedBall w₀ ρ₁ ⊆ closedBall 0 R →
        1 ≤ (2 * π)⁻¹ * ∫ w in closedBall w₀ ρ₁, f w →
        ∃ V ∈ (newtonPolynomial (fun k ↦ ∫ w, w ^ k ∂posSliceMeasure f R -
          ∫ w, w ^ k ∂negSliceMeasure f R) m).roots, dist V w₀ < ρ₁ + ε := by
  set t := min ε 1
  have ht₀ : 0 < t := lt_min hε one_pos
  obtain ⟨δ, hδ, h⟩ := exists_forall_abs_setIntegral_mul_sub_sum_roots_le m R
    (div_pos ht₀ four_pos)
  refine ⟨min δ (1 / 2), lt_min hδ one_half_pos,
    fun f hf hmass hneg hvar w₀ ρ₁ hsub hcharge ↦ ?_⟩
  have hneg' := hneg.trans (min_le_right _ _)
  obtain ⟨V, hV, hVw⟩ := exists_mem_dist_lt_of_le_setIntegral
    (h f hf hmass (hneg.trans (min_le_left _ _)) (hvar.trans (min_le_left _ _))) hf hneg' hsub
    hcharge (lt_add_of_pos_right ρ₁ ht₀) (by linarith [min_le_right ε 1])
    (by rw [add_sub_cancel_left]; nlinarith)
  exact ⟨V, hV, hVw.trans_le (by linarith [min_le_left ε 1])⟩

/-! ### The slices of the cutoff current -/

/-- **No root is missed by the zeros of the field.** Fix the constants `C`, `c > 0` and `c₀` of
Taubes's off-zero bound. For every accuracy `ε > 0` there are a tolerance `δ > 0` and constants
`K` and `r₀ > 0` with the following property. Let `Θ` be the cutoff current of a pair `(b, α)`
with `α` of class `C²`, for a cutoff `χ` equal to `1` above `1 / 2`, and let `f` be its slice
density along a disc `σ`, integrable on the closed disc of radius `R`. Suppose the normalized
slice has mass `m`, negative mass at most `δ` and Newton variance at most `δ`, that `r ≥ r₀` and
`h > 0`, and that at the points `σ w` of the disc the off-zero bound holds relative to a set `Z`.
Then for every root `V` of the Newton polynomial of the slice there is a point `w` of the disc
with `|w - V| < ε` and a point of `Z` within distance `K h` of `σ w`. -/
theorem exists_forall_mem_roots_exists_dist_le (m : ℕ) (R : ℝ) {ε : ℝ} (hε : 0 < ε)
    (C c c₀ : ℝ) (hc : 0 < c) :
    ∃ δ > 0, ∃ K r₀ : ℝ, 0 < r₀ ∧ ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {χ : ℝ → ℝ} {b : E → E [⋀^Fin 1]→L[ℝ] ℝ} {α : E → ℂ} {σ : ℂ → E} (Z : Set E) (r h : ℝ),
      ContDiff ℝ 2 α → EqOn χ 1 (Ioi (1 / 2)) → r₀ ≤ r → 0 < h →
      IntegrableOn (sliceDensity χ b α σ) (closedBall 0 R) →
      (posSliceMeasure (sliceDensity χ b α σ) R).real univ -
        (negSliceMeasure (sliceDensity χ b α σ) R).real univ = m →
      (negSliceMeasure (sliceDensity χ b α σ) R).real univ ≤ δ →
      ∫ w, ‖(newtonPolynomial (fun k ↦ ∫ w, w ^ k ∂posSliceMeasure (sliceDensity χ b α σ) R -
        ∫ w, w ^ k ∂negSliceMeasure (sliceDensity χ b α σ) R) m).eval w‖ ^ 2
          ∂posSliceMeasure (sliceDensity χ b α σ) R ≤ δ →
      (∀ w ∈ closedBall (0 : ℂ) R, ∀ R', c₀ * h ≤ R' → (∀ z ∈ Z, R' ≤ dist (σ w) z) →
        max (1 - normSq (α (σ w))) 0 ≤
          C / r * max (1 - normSq (α (σ w))) 0 + C / r + C * Real.exp (-(c * R' / h))) →
      ∀ V ∈ (newtonPolynomial (fun k ↦ ∫ w, w ^ k ∂posSliceMeasure (sliceDensity χ b α σ) R -
        ∫ w, w ^ k ∂negSliceMeasure (sliceDensity χ b α σ) R) m).roots,
        ∃ w ∈ closedBall (0 : ℂ) R, dist w V < ε ∧ ∃ z ∈ Z, dist (σ w) z ≤ K * h := by
  obtain ⟨δ, hδ, hroot⟩ := exists_forall_mem_roots_exists_dist_lt_ne_zero m R hε
  obtain ⟨K, r₀, hr₀, hK⟩ := exists_forall_exists_dist_le_of_mem_tsupport_cutoffCurrent.{u}
    C c c₀ hc
  refine ⟨δ, hδ, K, r₀, hr₀, ?_⟩
  intro E _ _ χ b α σ Z r h hα hχ hr hh hf hmass hneg hvar hbound V hV
  obtain ⟨w, hw, hwV, hfw⟩ := hroot _ hf hmass hneg hvar V hV
  exact ⟨w, hw, hwV, hK Z r h hα hχ hr hh (σ w)
    (subset_tsupport _ (support_sliceDensity_subset χ b α σ hfw)) (hbound w hw)⟩

/-- **No root is missed by the zeros of the field, in the ambient distance.** Under the
hypotheses of `TauCeti.SeibergWitten.exists_forall_mem_roots_exists_dist_le`, if moreover the
disc `σ` is `L`-Lipschitz on the closed disc of radius `R + ε`, then every root `V` of the
Newton polynomial of the slice has a point of `Z` within distance `L ε + K h` of `σ V`. -/
theorem exists_forall_mem_roots_exists_dist_le_add_mul (m : ℕ) (R : ℝ) {ε : ℝ} (hε : 0 < ε)
    (C c c₀ : ℝ) (hc : 0 < c) :
    ∃ δ > 0, ∃ K r₀ : ℝ, 0 < r₀ ∧ ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {χ : ℝ → ℝ} {b : E → E [⋀^Fin 1]→L[ℝ] ℝ} {α : E → ℂ} {σ : ℂ → E} {L : NNReal}
      (Z : Set E) (r h : ℝ),
      ContDiff ℝ 2 α → EqOn χ 1 (Ioi (1 / 2)) → r₀ ≤ r → 0 < h →
      LipschitzOnWith L σ (closedBall 0 (R + ε)) →
      IntegrableOn (sliceDensity χ b α σ) (closedBall 0 R) →
      (posSliceMeasure (sliceDensity χ b α σ) R).real univ -
        (negSliceMeasure (sliceDensity χ b α σ) R).real univ = m →
      (negSliceMeasure (sliceDensity χ b α σ) R).real univ ≤ δ →
      ∫ w, ‖(newtonPolynomial (fun k ↦ ∫ w, w ^ k ∂posSliceMeasure (sliceDensity χ b α σ) R -
        ∫ w, w ^ k ∂negSliceMeasure (sliceDensity χ b α σ) R) m).eval w‖ ^ 2
          ∂posSliceMeasure (sliceDensity χ b α σ) R ≤ δ →
      (∀ w ∈ closedBall (0 : ℂ) R, ∀ R', c₀ * h ≤ R' → (∀ z ∈ Z, R' ≤ dist (σ w) z) →
        max (1 - normSq (α (σ w))) 0 ≤
          C / r * max (1 - normSq (α (σ w))) 0 + C / r + C * Real.exp (-(c * R' / h))) →
      ∀ V ∈ (newtonPolynomial (fun k ↦ ∫ w, w ^ k ∂posSliceMeasure (sliceDensity χ b α σ) R -
        ∫ w, w ^ k ∂negSliceMeasure (sliceDensity χ b α σ) R) m).roots,
        ∃ z ∈ Z, dist (σ V) z ≤ L * ε + K * h := by
  obtain ⟨δ, hδ, K, r₀, hr₀, hK⟩ := exists_forall_mem_roots_exists_dist_le.{u} m R hε C c c₀ hc
  refine ⟨δ, hδ, K, r₀, hr₀, ?_⟩
  intro E _ _ χ b α σ L Z r h hα hχ hr hh hσ hf hmass hneg hvar hbound V hV
  obtain ⟨w, hw, hwV, z, hz, hwz⟩ := hK Z r h hα hχ hr hh hf hmass hneg hvar hbound V hV
  have hR : closedBall (0 : ℂ) R ⊆ closedBall 0 (R + ε) :=
    closedBall_subset_closedBall (by linarith)
  have hV' : V ∈ closedBall (0 : ℂ) (R + ε) := by
    rw [mem_closedBall, dist_zero_right]
    have := mem_closedBall.1 hw
    rw [dist_zero_right] at this
    linarith [norm_le_norm_add_norm_sub' V w, dist_eq_norm V w, dist_comm w V]
  refine ⟨z, hz, ?_⟩
  calc dist (σ V) z ≤ dist (σ V) (σ w) + dist (σ w) z := dist_triangle _ _ _
    _ ≤ L * dist V w + K * h := add_le_add (hσ.dist_le_mul V hV' w (hR hw)) hwz
    _ ≤ L * ε + K * h := by
        gcongr
        rw [dist_comm]
        exact hwV.le

/-- **A zero enclosed by a charged vacuum circle is not a ghost core.** For every accuracy
`ε > 0` there is a tolerance `δ > 0`, depending only on `m`, `R` and `ε`, with the following
property. Let `Θ` be the cutoff current of a `C²` pair `(b, α)`, for a `C¹` cutoff `χ` vanishing
near `0`, and let `f` be its slice density along a `C²` disc `σ`. Suppose the normalized slice on
the closed disc of radius `R` has mass `m`, negative mass at most `δ` and Newton variance at most
`δ`. If a closed subdisc of radius `ρ₁ ≥ 0` about `w₀` lies in that disc, its boundary circle lies
in the vacuum `χ(|α ∘ σ|²) = 1`, and the winding number of `α ∘ σ` around that circle is
positive, then some root `V` of the Newton polynomial of the slice has `|V - w₀| < ρ₁ + ε`. -/
theorem exists_forall_exists_mem_roots_dist_lt_of_windingNumber (m : ℕ) (R : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {χ : ℝ → ℝ}
      {b : E → E [⋀^Fin 1]→L[ℝ] ℝ} {α : E → ℂ} {σ : ℂ → E},
      ContDiff ℝ 2 α → ContDiff ℝ 1 b → ContDiff ℝ 1 χ → χ =ᶠ[nhds 0] 0 → ContDiff ℝ 2 σ →
      (posSliceMeasure (sliceDensity χ b α σ) R).real univ -
        (negSliceMeasure (sliceDensity χ b α σ) R).real univ = m →
      (negSliceMeasure (sliceDensity χ b α σ) R).real univ ≤ δ →
      ∫ w, ‖(newtonPolynomial (fun k ↦ ∫ w, w ^ k ∂posSliceMeasure (sliceDensity χ b α σ) R -
        ∫ w, w ^ k ∂negSliceMeasure (sliceDensity χ b α σ) R) m).eval w‖ ^ 2
          ∂posSliceMeasure (sliceDensity χ b α σ) R ≤ δ →
      ∀ (w₀ : ℂ) (ρ₁ : ℝ), 0 ≤ ρ₁ → closedBall w₀ ρ₁ ⊆ closedBall 0 R →
        (∀ θ, χ (normSq (α (σ (circleMap w₀ ρ₁ θ)))) = 1) →
        0 < (Contour.windingNumber (α ∘ σ ∘ circleMap w₀ ρ₁) (-π) π 0).re →
        ∃ V ∈ (newtonPolynomial (fun k ↦ ∫ w, w ^ k ∂posSliceMeasure (sliceDensity χ b α σ) R -
          ∫ w, w ^ k ∂negSliceMeasure (sliceDensity χ b α σ) R) m).roots,
          dist V w₀ < ρ₁ + ε := by
  obtain ⟨δ, hδ, h⟩ := exists_forall_exists_mem_roots_dist_lt m R hε
  refine ⟨δ, hδ, ?_⟩
  intro E _ _ χ b α σ hα hb hχ hχ₀ hσ hmass hneg hvar w₀ ρ₁ hρ₁ hsub hbd hwind
  have hf : IntegrableOn (sliceDensity χ b α σ) (closedBall 0 R) :=
    (continuous_sliceDensity hα hb hχ hχ₀ hσ).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 R)
  refine h _ hf hmass hneg hvar w₀ ρ₁ hsub ?_
  -- The charge of the subdisc is the winding number `n ≥ 1` of `α ∘ σ` around its boundary.
  obtain ⟨n, hn, hint⟩ := exists_int_integral_cutoffCurrent_comp_closedBall (b := b) hρ₁ hα hb
    hχ hχ₀ hσ hbd
  rw [hn, intCast_re, Int.cast_pos] at hwind
  simp only [sliceDensity_def, hint]
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  exact_mod_cast hwind

end TauCeti.SeibergWitten
