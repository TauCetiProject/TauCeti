/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.DiscCharge.RootSupport

/-!
# The charge of a vacuum circle counts the roots of the Newton polynomial

In Taubes's analysis of Seiberg–Witten solutions near a pseudoholomorphic curve, the cutoff
current `Θ = i F_a + d(χ(|α|²) τ)` (`TauCeti.SeibergWitten.cutoffCurrent`) is sliced by the
dilated normal discs `σ` of the curve, and the roots of the Newton polynomial `P` of degree `m` of
the moments of a slice (`TauCeti.newtonPolynomial`) are the candidate positions, with
multiplicity, of the local branches of the limiting curve in the normal fibre. On the other hand,
the field itself carries a local integer charge around every circle in the vacuum
`χ(|α|²) = 1`: the winding number of `α ∘ σ` around it, which is the integral of the slice over
the enclosed disc (`TauCeti.SeibergWitten.exists_int_integral_cutoffCurrent_comp_closedBall`).
`TauCeti.Analysis.PDE.SeibergWitten.DiscCharge.RootSupport` compares the roots of `P` with the
places where the slice lives, as sets. This file compares them with multiplicity: once the
negative mass and the Newton variance of the slice are small, the charge of a circle bounding a
vacuum annulus is the number of roots of `P` it encloses, counted with multiplicity.

**The vacuum annulus has no roots.** Let `f` be a density whose normalized slice `f dλ / 2π` on
the closed disc of radius `R` is within `ε` of the counting measure of a multiset `S` against
`1`-Lipschitz functions bounded by `1`, and suppose that `f` vanishes on the annulus
`ρ₁ < |w - w₀| < ρ₁ + κ`. If `ε < min (κ / 4) 1`, no point of `S` lies at a distance from `w₀`
between `ρ₁ + κ / 4` and `ρ₁ + 3 κ / 4`
(`TauCeti.SeibergWitten.dist_notMem_Icc_of_forall_eq_zero`): near a point of `S` the density does
not vanish (`TauCeti.SeibergWitten.exists_mem_closedBall_dist_lt_ne_zero`).

**The charge counts the enclosed points.** Test the slice against the plateau function equal to
`t = min (κ / 2) 1` within `ρ₁ + κ / 4` of `w₀` and to `0` beyond `ρ₁ + 3 κ / 4`. On the closed
disc of radius `ρ₁` it equals `t`, on the annulus the density vanishes, and beyond it the plateau
vanishes, so the slice integrates it to `t` times the charge `(2π)⁻¹ ∫_{|w - w₀| ≤ ρ₁} f`. Since no
point of `S` lies in the middle of the annulus, the counting measure integrates it to `t` times
the number `k` of points of `S` within `ρ₁ + κ / 2` of `w₀`. Hence the charge is within `ε / t`
of `k` (`TauCeti.SeibergWitten.abs_inv_mul_setIntegral_sub_countP_le`).

**Newton roots.** By the compact moment lemma
(`TauCeti.SeibergWitten.exists_forall_abs_setIntegral_mul_sub_sum_roots_le`), for every
tolerance `η > 0` there is `δ > 0`, depending only on `m`, `R`, `κ` and `η`, such that a slice of
mass `m` with negative mass and Newton variance at most `δ`, vanishing on the annulus, has charge
within `η` of the number of roots of `P` within `ρ₁ + κ / 2` of `w₀`
(`TauCeti.SeibergWitten.exists_forall_abs_setIntegral_sub_countP_roots_le`). For the slice of
the cutoff current, the annulus lies in the vacuum when `|α ∘ σ|² > c` there, for a cutoff equal to
`1` on `(c, ∞)`; then the slice vanishes on the annulus, and the charge is an integer, so it equals
the count. That is, the winding number of `α ∘ σ` around the circle of radius `ρ₁` about `w₀` is
the number of roots of the Newton polynomial of the slice within `ρ₁ + κ / 2` of `w₀`
(`TauCeti.SeibergWitten.exists_forall_windingNumber_eq_countP_roots`). In particular it is
nonnegative, and it is positive exactly when some root lies within that distance.

As in `TauCeti.Analysis.PDE.SeibergWitten.DiscCharge.RootSupport`, the tolerance `δ` is chosen
before the field, the disc, the circle and the slice, and the smallness of the Newton variance,
which the coupled equations have to supply, is a hypothesis.

## Main results

* `TauCeti.SeibergWitten.abs_inv_mul_setIntegral_sub_countP_le`: the charge of a disc bounding an
  annulus where the density vanishes is within `ε / min (κ / 2) 1` of the number of enclosed
  points of a multiset approximating the slice within `ε`.
* `TauCeti.SeibergWitten.exists_forall_abs_setIntegral_sub_countP_roots_le`: the same for the
  roots of the Newton polynomial of a slice with small negative mass and Newton variance.
* `TauCeti.SeibergWitten.exists_forall_windingNumber_eq_countP_roots`: the winding number of the
  field around a circle bounding a vacuum annulus is the number of enclosed roots of the Newton
  polynomial of its slice, counted with multiplicity.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

open Complex Filter Metric MeasureTheory Set
open scoped Topology Real

namespace TauCeti.SeibergWitten

universe u

/-! ### Charges and enclosed points of a bounded-Lipschitz approximation -/

section Approximation

variable {f : ℂ → ℝ} {R ε ρ₁ κ : ℝ} {S : Multiset ℂ} {w₀ : ℂ}

/-- **No point of the approximating multiset lies deep in an empty annulus.** Let `f` be a density
whose normalized slice `f dλ / 2π` on the closed disc of radius `R` is within `ε` of the counting
measure of a multiset `S`, against every `1`-Lipschitz function bounded by `1`. If `f` vanishes on
the open annulus `ρ₁ < |w - w₀| < ρ₁ + κ` and `ε < min (κ / 4) 1`, then no point of `S` lies at a
distance from `w₀` between `ρ₁ + κ / 4` and `ρ₁ + 3 κ / 4`. -/
theorem dist_notMem_Icc_of_forall_eq_zero
    (hS : ∀ g : ℂ → ℝ, LipschitzWith 1 g → (∀ w, |g w| ≤ 1) →
      |(2 * π)⁻¹ * (∫ w in closedBall 0 R, f w * g w) - (S.map g).sum| ≤ ε)
    (hzero : ∀ w ∈ closedBall (0 : ℂ) R, ρ₁ < dist w w₀ → dist w w₀ < ρ₁ + κ → f w = 0)
    (hε : ε < min (κ / 4) 1) {V : ℂ} (hV : V ∈ S) :
    dist V w₀ ∉ Icc (ρ₁ + κ / 4) (ρ₁ + 3 * κ / 4) := by
  rintro ⟨h₁, h₂⟩
  obtain ⟨w, hw, hwV, hfw⟩ := exists_mem_closedBall_dist_lt_ne_zero hS
    (hε.trans_le (min_le_right _ _)) (hε.trans_le (min_le_left _ _)) hV
  refine hfw (hzero w hw ?_ ?_)
  · linarith [dist_triangle V w w₀, dist_comm w V]
  · linarith [dist_triangle w V w₀]

/-- A weight equal to `t` on the closed disc of radius `ρ₁` about `w₀` and to `0` outside the
disc of radius `ρ₁ + κ` integrates a density vanishing on the annulus between them to `t` times
its integral over the inner disc. -/
private theorem setIntegral_mul_eq_mul_setIntegral {g : ℂ → ℝ} {t : ℝ}
    (hsub : closedBall w₀ ρ₁ ⊆ closedBall 0 R)
    (hzero : ∀ w ∈ closedBall (0 : ℂ) R, ρ₁ < dist w w₀ → dist w w₀ < ρ₁ + κ → f w = 0)
    (hin : ∀ {w}, dist w w₀ ≤ ρ₁ → g w = t) (hout : ∀ {w}, ρ₁ + κ ≤ dist w w₀ → g w = 0) :
    ∫ w in closedBall 0 R, f w * g w = t * ∫ w in closedBall w₀ ρ₁, f w := by
  have hind : ∫ w in closedBall w₀ ρ₁, t * f w =
      ∫ w in closedBall 0 R, (closedBall w₀ ρ₁).indicator (fun w ↦ t * f w) w := by
    rw [setIntegral_indicator measurableSet_closedBall, inter_eq_right.2 hsub]
  rw [← integral_const_mul, hind]
  refine setIntegral_congr_fun measurableSet_closedBall fun w hw ↦ ?_
  by_cases h₁ : dist w w₀ ≤ ρ₁
  · rw [indicator_of_mem (mem_closedBall.2 h₁), hin h₁, mul_comm]
  · rw [indicator_of_notMem (fun h ↦ h₁ (mem_closedBall.1 h))]
    by_cases h₂ : dist w w₀ < ρ₁ + κ
    · rw [hzero w hw (not_le.1 h₁) h₂, zero_mul]
    · rw [hout (not_lt.1 h₂), mul_zero]

/-- **The charge of a disc bounding an empty annulus counts the enclosed points.** Let `f` be a
density whose normalized slice `f dλ / 2π` on the closed disc of radius `R` is within `ε` of the
counting measure of a multiset `S`, against every `1`-Lipschitz function bounded by `1`. Suppose
that the closed disc of radius `ρ₁` about `w₀` lies in that disc, that `f` vanishes on the open
annulus `ρ₁ < |w - w₀| < ρ₁ + κ`, and that `ε < min (κ / 4) 1`. Then the normalized charge
`(2π)⁻¹ ∫ f` of the closed disc of radius `ρ₁` about `w₀` is within `ε / min (κ / 2) 1` of the
number of points of `S`, counted with multiplicity, within `ρ₁ + κ / 2` of `w₀`. -/
theorem abs_inv_mul_setIntegral_sub_countP_le
    (hS : ∀ g : ℂ → ℝ, LipschitzWith 1 g → (∀ w, |g w| ≤ 1) →
      |(2 * π)⁻¹ * (∫ w in closedBall 0 R, f w * g w) - (S.map g).sum| ≤ ε)
    (hsub : closedBall w₀ ρ₁ ⊆ closedBall 0 R)
    (hzero : ∀ w ∈ closedBall (0 : ℂ) R, ρ₁ < dist w w₀ → dist w w₀ < ρ₁ + κ → f w = 0)
    (hε : ε < min (κ / 4) 1) :
    |(2 * π)⁻¹ * (∫ w in closedBall w₀ ρ₁, f w) -
        S.countP (fun V ↦ dist V w₀ < ρ₁ + κ / 2)| ≤ ε / min (κ / 2) 1 := by
  -- Testing against `0` shows `ε ≥ 0`, so `κ > 0`.
  have hε₀ : 0 ≤ ε := (abs_nonneg _).trans
    (hS (fun _ ↦ 0) ((LipschitzWith.const (0 : ℝ)).weaken zero_le_one) (by simp))
  have hκ : 0 < κ := by linarith [min_le_left (κ / 4) 1]
  set t := min (κ / 2) 1
  have ht₀ : 0 < t := lt_min (by linarith) one_pos
  -- The plateau `g`, equal to `t` within `ρ₁ + κ / 4` of `w₀` and to `0` beyond
  -- `ρ₁ + 3 κ / 4`.
  set g : ℂ → ℝ := fun w ↦ max (min t (ρ₁ + 3 * κ / 4 - dist w w₀)) 0 with hg
  have hgL : LipschitzWith 1 g := by
    simpa using (((LipschitzWith.const (ρ₁ + 3 * κ / 4)).sub
      (LipschitzWith.dist_left w₀)).const_min t).max_const 0
  have hg₀ (w : ℂ) : 0 ≤ g w := le_max_right _ _
  have hg₁ (w : ℂ) : |g w| ≤ 1 := by
    rw [abs_of_nonneg (hg₀ w)]
    exact max_le ((min_le_left _ _).trans (min_le_right _ _)) zero_le_one
  have hg_in {w : ℂ} (hw : dist w w₀ ≤ ρ₁ + κ / 4) : g w = t := by
    simp only [hg]
    rw [min_eq_left (by linarith [min_le_left (κ / 2) 1]), max_eq_left ht₀.le]
  have hg_out {w : ℂ} (hw : ρ₁ + 3 * κ / 4 ≤ dist w w₀) : g w = 0 :=
    max_eq_right ((min_le_right _ _).trans (by linarith))
  -- The slice integrates `g` to `t` times the charge of the disc of radius `ρ₁`.
  have hint := setIntegral_mul_eq_mul_setIntegral hsub hzero (fun {w} h ↦ hg_in (w := w)
    (by linarith)) (fun {w} h ↦ hg_out (w := w) (by linarith))
  -- The counting measure integrates `g` to `t` times the number of enclosed points.
  have hsum : (S.map g).sum = t * S.countP (fun V ↦ dist V w₀ < ρ₁ + κ / 2) := by
    have hgS : ∀ V ∈ S, g V = if dist V w₀ < ρ₁ + κ / 2 then t else 0 := by
      intro V hV
      have hgap := dist_notMem_Icc_of_forall_eq_zero hS hzero hε hV
      rw [mem_Icc, not_and_or, not_le, not_le] at hgap
      split_ifs with h
      · exact hg_in (by rcases hgap with h' | h' <;> linarith)
      · exact hg_out (by rcases hgap with h' | h' <;> linarith)
    have hite (T : Multiset ℂ) : (T.map fun V ↦ if dist V w₀ < ρ₁ + κ / 2 then t else 0).sum =
        t * T.countP (fun V ↦ dist V w₀ < ρ₁ + κ / 2) := by
      induction T using Multiset.induction_on with
      | empty => simp
      | cons a T ih =>
        simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.countP_cons, ih]
        split_ifs <;> push_cast <;> ring
    rw [Multiset.map_congr rfl hgS, hite]
  have hS' := hS g hgL hg₁
  rw [hint, hsum, ← mul_assoc, mul_comm (2 * π)⁻¹ t, mul_assoc, ← mul_sub, abs_mul,
    abs_of_pos ht₀] at hS'
  rw [le_div_iff₀ ht₀, mul_comm]
  exact hS'

end Approximation

/-! ### Roots of the Newton polynomial of a slice -/

/-- **The charge of a disc bounding an empty annulus counts the enclosed Newton roots.** For
every width `κ > 0` and tolerance `η > 0` there is `δ > 0`, depending only on `m`, `R`, `κ` and
`η`, with the following property. Let `f` be a density integrable on the closed disc of radius
`R` whose normalized slice has mass `m`, negative mass at most `δ` and Newton variance `∫ |P|² dμ⁺`
at most `δ`, where `P` is the Newton polynomial of degree `m` of its moments. If the closed disc of
radius `ρ₁` about `w₀` lies in that disc and `f` vanishes on the open annulus
`ρ₁ < |w - w₀| < ρ₁ + κ`, then the normalized charge `(2π)⁻¹ ∫ f` of the closed disc of radius
`ρ₁` about `w₀` is within `η` of the number of roots of `P`, counted with multiplicity, within
`ρ₁ + κ / 2` of `w₀`. -/
theorem exists_forall_abs_setIntegral_sub_countP_roots_le (m : ℕ) (R : ℝ) {κ η : ℝ}
    (hκ : 0 < κ) (hη : 0 < η) :
    ∃ δ > 0, ∀ f : ℂ → ℝ, IntegrableOn f (closedBall 0 R) →
      (posSliceMeasure f R).real univ - (negSliceMeasure f R).real univ = m →
      (negSliceMeasure f R).real univ ≤ δ →
      ∫ w, ‖(newtonPolynomial (fun k ↦ ∫ w, w ^ k ∂posSliceMeasure f R -
        ∫ w, w ^ k ∂negSliceMeasure f R) m).eval w‖ ^ 2 ∂posSliceMeasure f R ≤ δ →
      ∀ (w₀ : ℂ) (ρ₁ : ℝ), closedBall w₀ ρ₁ ⊆ closedBall 0 R →
        (∀ w ∈ closedBall (0 : ℂ) R, ρ₁ < dist w w₀ → dist w w₀ < ρ₁ + κ → f w = 0) →
        |(2 * π)⁻¹ * (∫ w in closedBall w₀ ρ₁, f w) -
          (newtonPolynomial (fun k ↦ ∫ w, w ^ k ∂posSliceMeasure f R -
            ∫ w, w ^ k ∂negSliceMeasure f R) m).roots.countP
              (fun V ↦ dist V w₀ < ρ₁ + κ / 2)| ≤ η := by
  set t := min (κ / 2) 1
  have ht₀ : 0 < t := lt_min (by linarith) one_pos
  set ε := min (min (κ / 4) 1) (η * t) / 2 with hε
  have hε₀ : 0 < ε := by positivity
  have hεκ : ε < min (κ / 4) 1 := by
    have := min_le_left (min (κ / 4) 1) (η * t)
    have : 0 < min (κ / 4) 1 := lt_min (by linarith) one_pos
    linarith [hε]
  have hεη : ε / t ≤ η := by
    rw [div_le_iff₀ ht₀]
    have := min_le_right (min (κ / 4) 1) (η * t)
    linarith [mul_pos hη ht₀, hε]
  obtain ⟨δ, hδ, h⟩ := exists_forall_abs_setIntegral_mul_sub_sum_roots_le m R hε₀
  exact ⟨δ, hδ, fun f hf hmass hneg hvar w₀ ρ₁ hsub hzero ↦
    (abs_inv_mul_setIntegral_sub_countP_le (h f hf hmass hneg hvar) hsub hzero hεκ).trans
      hεη⟩

/-! ### The slices of the cutoff current -/

/-- **The winding number of the field around a vacuum circle counts the enclosed Newton roots.**
For every width `κ > 0` there is a tolerance `δ > 0`, depending only on `m`, `R` and `κ`, with
the following property. Let `Θ` be the cutoff current of a `C²` pair `(b, α)`, for a `C¹` cutoff
`χ` vanishing near `0` and equal to `1` on `(c, ∞)`, and let `f` be its slice density along a `C²`
disc `σ`. Suppose the normalized slice on the closed disc of radius `R` has mass `m`, negative mass
at most `δ` and Newton variance at most `δ`. If a closed subdisc of radius `ρ₁ ≥ 0` about `w₀`
lies in that disc and `|α ∘ σ|² > c` on the annulus `ρ₁ ≤ |w - w₀| < ρ₁ + κ`, then the winding
number of `α ∘ σ` around the circle of radius `ρ₁` about `w₀` is the number of roots of the Newton
polynomial of the slice, counted with multiplicity, within `ρ₁ + κ / 2` of `w₀`. -/
theorem exists_forall_windingNumber_eq_countP_roots (m : ℕ) (R : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ δ > 0, ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {χ : ℝ → ℝ}
      {b : E → E [⋀^Fin 1]→L[ℝ] ℝ} {α : E → ℂ} {σ : ℂ → E} {c : ℝ},
      ContDiff ℝ 2 α → ContDiff ℝ 1 b → ContDiff ℝ 1 χ → χ =ᶠ[𝓝 0] 0 → EqOn χ 1 (Ioi c) →
      ContDiff ℝ 2 σ →
      (posSliceMeasure (sliceDensity χ b α σ) R).real univ -
        (negSliceMeasure (sliceDensity χ b α σ) R).real univ = m →
      (negSliceMeasure (sliceDensity χ b α σ) R).real univ ≤ δ →
      ∫ w, ‖(newtonPolynomial (fun k ↦ ∫ w, w ^ k ∂posSliceMeasure (sliceDensity χ b α σ) R -
        ∫ w, w ^ k ∂negSliceMeasure (sliceDensity χ b α σ) R) m).eval w‖ ^ 2
          ∂posSliceMeasure (sliceDensity χ b α σ) R ≤ δ →
      ∀ (w₀ : ℂ) (ρ₁ : ℝ), 0 ≤ ρ₁ → closedBall w₀ ρ₁ ⊆ closedBall 0 R →
        (∀ w, ρ₁ ≤ dist w w₀ → dist w w₀ < ρ₁ + κ → c < normSq (α (σ w))) →
        Contour.windingNumber (α ∘ σ ∘ circleMap w₀ ρ₁) (-π) π 0 =
          (newtonPolynomial (fun k ↦ ∫ w, w ^ k ∂posSliceMeasure (sliceDensity χ b α σ) R -
            ∫ w, w ^ k ∂negSliceMeasure (sliceDensity χ b α σ) R) m).roots.countP
              (fun V ↦ dist V w₀ < ρ₁ + κ / 2) := by
  obtain ⟨δ, hδ, h⟩ := exists_forall_abs_setIntegral_sub_countP_roots_le m R hκ one_half_pos
  refine ⟨δ, hδ, ?_⟩
  intro E _ _ χ b α σ c hα hb hχ hχ₀ hχc hσ hmass hneg hvar w₀ ρ₁ hρ₁ hsub hvac
  have hf : IntegrableOn (sliceDensity χ b α σ) (closedBall 0 R) :=
    (continuous_sliceDensity hα hb hχ hχ₀ hσ).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 R)
  -- The circle lies in the vacuum, so the charge of the disc is the winding number `n`.
  have hbd (θ : ℝ) : χ (normSq (α (σ (circleMap w₀ ρ₁ θ)))) = 1 := by
    have hd : dist (circleMap w₀ ρ₁ θ) w₀ = ρ₁ := by
      rw [dist_eq_norm, circleMap_sub_center, norm_circleMap_zero, abs_of_nonneg hρ₁]
    exact hχc (hvac _ hd.ge (by linarith))
  obtain ⟨n, hn, hint⟩ := exists_int_integral_cutoffCurrent_comp_closedBall (b := b) hρ₁ hα hb
    hχ hχ₀ hσ hbd
  -- The slice density vanishes on the open annulus, where `χ = 1` near `|α ∘ σ|²`.
  have hzero : ∀ w ∈ closedBall (0 : ℂ) R, ρ₁ < dist w w₀ → dist w w₀ < ρ₁ + κ →
      sliceDensity χ b α σ w = 0 := by
    intro w _ h₁ h₂
    have hw := hvac w h₁.le h₂
    rw [sliceDensity_def, cutoffCurrent_eq_zero hα.contDiffAt
      (ne_zero_of_cutoff_eq_one hχ₀ (hχc hw)) (hχc.eventuallyEq_of_mem (Ioi_mem_nhds hw))]
    simp
  have hcount := h _ hf hmass hneg hvar w₀ ρ₁ hsub hzero
  simp only [sliceDensity_def, hint] at hcount
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul] at hcount
  -- An integer within `1 / 2` of a natural number equals it.
  set k := (newtonPolynomial (fun k ↦ ∫ w, w ^ k ∂posSliceMeasure (sliceDensity χ b α σ) R -
    ∫ w, w ^ k ∂negSliceMeasure (sliceDensity χ b α σ) R) m).roots.countP
      (fun V ↦ dist V w₀ < ρ₁ + κ / 2)
  have hnk : |((n - k : ℤ) : ℝ)| < 1 := by push_cast; linarith [hcount]
  rw [← Int.cast_abs, ← Int.cast_one, Int.cast_lt, abs_lt] at hnk
  rw [hn]
  exact_mod_cast (by omega : n = k)

end TauCeti.SeibergWitten
