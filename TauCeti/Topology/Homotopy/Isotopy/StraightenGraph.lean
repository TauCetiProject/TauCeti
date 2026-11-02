/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Isotopy.Push
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Straightening a graph onto the zero section

Let `X` be a topological space, `W` a real normed space and `g : X → W` a continuous map. The
graph `{(x, g x)}` of `g` is a copy of `X` in the product `X × W`, and so is the zero section
`{(x, 0)}`. This file moves the first onto the second by an ambient isotopy of `X × W`
(`TauCeti.AmbientIsotopy.straightenGraph g κ hκ`, for a constant `κ > 2`) with three properties:

* it preserves every fibre `{x} × W` (`TauCeti.AmbientIsotopy.straightenGraph_apply_fst`);
* it moves only the points `(x, w)` with `‖w‖ < κ * ‖g x‖`, so it fixes the fibres over the zeros
  of `g` and everything far from the graph
  (`TauCeti.AmbientIsotopy.straightenGraph_apply_of_mul_norm_le`);
* at time `t` it carries the graph of `g` onto the graph of `(1 - t) • g`, along straight lines
  (`TauCeti.AmbientIsotopy.straightenGraph_apply_graph`), so at time `1` it carries the graph of
  `g` onto the zero section (`TauCeti.AmbientIsotopy.straightenGraph_final_image_range`).

The support condition is what makes the motion local: if `g` is small, the isotopy only moves
points close to the graph. This is the local step in straightening the arcs of a knot of class
`C¹` onto the chords of a fine inscribed polygon, as in the proof that such knots are tame
(Crowell and Fox, Appendix I). In coordinates `ℝ × W` along a chord, an arc running close to the
chord and nearly parallel to it is the graph of a continuous `g : ℝ → W` vanishing outside the
chord, with `‖g x‖` small compared to the distance from `x` to the ends of the chord. The
straightening moves the arc onto the chord, inside a thin region around the arc which pinches to
the two ends of the chord.

## Implementation notes

In the fibre over `x` the isotopy is the push `TauCeti.AmbientIsotopy.push` of `W` from the point
`g x` towards `0`, weighted by the radial function equal to `0` on the closed ball of radius
`‖g x‖` and to `1` outside the ball of radius `κ * ‖g x‖`, interpolating linearly in between. Its
slope `1 / ((κ - 1) * ‖g x‖)` is small enough for the push as soon as `κ > 2`. These pushes vary
continuously with `x`: near a zero of `g` the displacement is at most `‖g x‖`, so it tends to `0`.
The level-preserving total map is a continuous bijection, and it is a closed map: every point is
recovered from its image by moving it back by `s • g x` for some `s ∈ [0, 1]`, and projecting
along the compact parameter `s` is closed. So it is a homeomorphism, without any compactness or
separation assumption on `X`.

## Main definitions

* `TauCeti.AmbientIsotopy.straightenGraph g κ hκ`: the ambient isotopy of `X × W` straightening
  the graph of `g` onto the zero section, supported in `{(x, w) | ‖w‖ < κ * ‖g x‖}`.

## Main results

* `TauCeti.AmbientIsotopy.exists_straightenGraph_apply_eq`: at time `t` the isotopy moves `(x, w)`
  to `(x, w - s • g x)` for some `s ∈ [0, t]`.
* `TauCeti.AmbientIsotopy.straightenGraph_apply_of_mul_norm_le`: it fixes `(x, w)` whenever
  `κ * ‖g x‖ ≤ ‖w‖`.
* `TauCeti.AmbientIsotopy.straightenGraph_apply_of_norm_le`: at time `t` it moves `(x, w)` to
  `(x, w - t • g x)` whenever `‖w‖ ≤ ‖g x‖`.
* `TauCeti.AmbientIsotopy.straightenGraph_apply_graph`: at time `t` it moves `(x, g x)` to
  `(x, (1 - t) • g x)`.
* `TauCeti.AmbientIsotopy.straightenGraph_final_image_range`: its final homeomorphism carries the
  graph of `g` onto the zero section.

## References

* R. H. Crowell, R. H. Fox, *Introduction to Knot Theory*, Springer GTM 57 (1977), Appendix I,
  for straightening the arcs of a knot of class `C¹` onto the chords of an inscribed polygon.
* G. Burde, H. Zieschang, *Knots*, 2nd ed., De Gruyter Studies in Mathematics 5 (2003),
  Chapter 1 §B, for pushes realizing moves of polygonal knots by ambient isotopies.
-/

public section

noncomputable section

open Set unitInterval Topology Filter

namespace TauCeti

namespace AmbientIsotopy

variable {X W : Type*} [TopologicalSpace X] [NormedAddCommGroup W] [NormedSpace ℝ W]
  (g : C(X, W)) {κ : ℝ}

/-- The weight of the push at a point at distance `r` from the origin of a fibre in which the graph
has norm `a`: `1` for `r ≤ a`, `0` for `r ≥ κ * a`, and linear in between. For `a = 0` it is `1`,
since Lean's division by zero gives `0`. -/
private def weight (κ a r : ℝ) : ℝ :=
  max (1 - max ((r - a) / ((κ - 1) * a)) 0) 0

private theorem weight_nonneg (κ a r : ℝ) : 0 ≤ weight κ a r :=
  le_max_right _ _

private theorem weight_le_one (κ a r : ℝ) : weight κ a r ≤ 1 :=
  max_le (by linarith [le_max_right ((r - a) / ((κ - 1) * a)) 0]) zero_le_one

private theorem weight_of_le (hκ : 1 < κ) {a r : ℝ} (ha : 0 ≤ a) (hr : r ≤ a) :
    weight κ a r = 1 := by
  have h : (r - a) / ((κ - 1) * a) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (mul_nonneg (by linarith) ha)
  simp [weight, max_eq_right h]

private theorem weight_of_mul_le (hκ : 1 < κ) {a r : ℝ} (ha : 0 < a) (hr : κ * a ≤ r) :
    weight κ a r = 0 := by
  have hc : 0 < (κ - 1) * a := mul_pos (by linarith) ha
  have h : 1 ≤ (r - a) / ((κ - 1) * a) := by
    rw [le_div_iff₀ hc]
    linarith
  rw [weight, max_eq_left (by linarith : (0 : ℝ) ≤ (r - a) / ((κ - 1) * a)),
    max_eq_right (by linarith)]

/-- The displacement of the straightening at time `t` and point `(x, w)`: the multiple
`t * weight κ ‖g x‖ ‖w‖` of `g x`. -/
private def disp (κ : ℝ) (q : I × (X × W)) : W :=
  ((q.1 : ℝ) * weight κ ‖g q.2.1‖ ‖q.2.2‖) • g q.2.1

omit [NormedSpace ℝ W] in
private theorem coeff_mem_Icc (κ : ℝ) (q : I × (X × W)) :
    (q.1 : ℝ) * weight κ ‖g q.2.1‖ ‖q.2.2‖ ∈ Icc (0 : ℝ) q.1 :=
  ⟨mul_nonneg q.1.2.1 (weight_nonneg _ _ _),
    mul_le_of_le_one_right q.1.2.1 (weight_le_one _ _ _)⟩

private theorem norm_disp_le (κ : ℝ) (q : I × (X × W)) : ‖disp g κ q‖ ≤ ‖g q.2.1‖ := by
  obtain ⟨h₀, h₁⟩ := coeff_mem_Icc g κ q
  rw [disp, norm_smul, Real.norm_of_nonneg h₀]
  exact mul_le_of_le_one_left (norm_nonneg _) (h₁.trans q.1.2.2)

/-- The displacement is continuous. Where `g x ≠ 0` this is continuity of the weight; where
`g x = 0` the displacement vanishes and is bounded by `‖g x‖` nearby. -/
private theorem continuous_disp (hκ : 1 < κ) : Continuous (disp g κ) := by
  refine continuous_iff_continuousAt.2 fun q => ?_
  by_cases h : g q.2.1 = 0
  · have h0 : disp g κ q = 0 := by simp [disp, h]
    rw [ContinuousAt, h0, tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (norm_disp_le g κ) ?_
    have hc : Continuous fun q : I × (X × W) => ‖g q.2.1‖ := by fun_prop
    simpa [h] using hc.tendsto q
  · have hden : (κ - 1) * ‖g q.2.1‖ ≠ 0 :=
      mul_ne_zero (by linarith) (norm_ne_zero_iff.2 h)
    have hw : ContinuousAt (fun q : I × (X × W) => weight κ ‖g q.2.1‖ ‖q.2.2‖) q := by
      refine ContinuousAt.sup (continuousAt_const.sub (ContinuousAt.sup ?_ continuousAt_const))
        continuousAt_const
      exact ContinuousAt.div (by fun_prop) (by fun_prop) hden
    exact ((continuous_subtype_val.comp continuous_fst).continuousAt.mul hw).smul
      (by fun_prop)

/-- In each fibre, at each time, the straightening is a bijection of `W`: it is the identity over
a zero of `g`, and otherwise it is a time slice of a push from `g x` towards `0`. -/
private theorem bijective_sub_disp (hκ : 2 < κ) (t : I) (x : X) :
    Function.Bijective fun w : W => w - disp g κ (t, (x, w)) := by
  by_cases h : g x = 0
  · simp only [disp, h, smul_zero, sub_zero]
    exact ⟨fun _ _ hw => hw, fun z => ⟨z, rfl⟩⟩
  set a := ‖g x‖ with ha_def
  have ha : 0 < a := norm_pos_iff.2 h
  have hc : 0 < (κ - 1) * a := mul_pos (by linarith) ha
  let μ : W → ℝ := fun w => max ((‖w‖ - a) / ((κ - 1) * a)) 0
  have hμ : Continuous μ := by fun_prop
  have hμ₀ : ∀ w, 0 ≤ μ w := fun _ => le_max_right _ _
  -- The weight has slope `1 / (κ - 1) < 1` along `g x`, slower than unit speed.
  have hv : ∀ (w : W) (r : ℝ), 0 < r → μ (w + r • -g x) < μ w + r := by
    intro w r hr
    have hnorm : ‖w + r • -g x‖ ≤ ‖w‖ + r * a := by
      calc ‖w + r • -g x‖ ≤ ‖w‖ + ‖r • -g x‖ := norm_add_le _ _
        _ = ‖w‖ + r * a := by rw [norm_smul, norm_neg, Real.norm_of_nonneg hr.le]
    have hstep : (‖w + r • -g x‖ - a) / ((κ - 1) * a) ≤
        (‖w‖ - a) / ((κ - 1) * a) + r / (κ - 1) := by
      have hr' : r / (κ - 1) = r * a / ((κ - 1) * a) := by
        field_simp
      rw [hr', ← add_div]
      exact div_le_div_of_nonneg_right (by linarith) hc.le
    have hlt : r / (κ - 1) < r := by
      rw [div_lt_iff₀ (by linarith)]
      nlinarith
    have hpos : 0 ≤ r / (κ - 1) := div_nonneg hr.le (by linarith)
    calc μ (w + r • -g x) ≤ μ w + r / (κ - 1) := by
          refine max_le ?_ ?_
          · linarith [le_max_left ((‖w‖ - a) / ((κ - 1) * a)) 0]
          · linarith [hμ₀ w]
      _ < μ w + r := by linarith
  convert ((push μ (0 : W) (-g x) hμ hμ₀ hv).isHomeomorph_apply t).bijective using 1
  funext w
  simp only [disp, weight, push_apply, vsub_eq_sub, sub_zero, vadd_eq_add, smul_neg, μ, ← ha_def]
  abel

/-- The level-preserving total map of the straightening is a homeomorphism of `I × (X × W)`. It
is a continuous bijection, and a closed map: a point `q` is `G (F q, s)` for the map `G` moving
back by `s • g x` and some `s ∈ [0, 1]`, so the image of a closed set is the projection, along the
compact factor `[0, 1]`, of a closed set. -/
private theorem isHomeomorph_straightenGraph_total (hκ : 2 < κ) :
    IsHomeomorph fun q : I × (X × W) => (q.1, (q.2.1, q.2.2 - disp g κ q)) := by
  set F := fun q : I × (X × W) => (q.1, (q.2.1, q.2.2 - disp g κ q))
  have hF : Continuous F := by
    have := continuous_disp g (κ := κ) (by linarith)
    fun_prop
  have hbij : Function.Bijective F := by
    refine ⟨fun q q' hqq' => ?_, fun y => ?_⟩
    · obtain ⟨t, x, w⟩ := q
      obtain ⟨t', x', w'⟩ := q'
      simp only [F, Prod.mk.injEq] at hqq'
      obtain ⟨rfl, rfl, hw⟩ := hqq'
      rw [(bijective_sub_disp g hκ t x).injective hw]
    · obtain ⟨t, x, z⟩ := y
      obtain ⟨w, hw⟩ := (bijective_sub_disp g hκ t x).surjective z
      exact ⟨(t, (x, w)), by simpa [F] using hw⟩
  let G : (I × (X × W)) × I → I × (X × W) :=
    fun p => (p.1.1, (p.1.2.1, p.1.2.2 + (p.2 : ℝ) • g p.1.2.1))
  have hG : Continuous G := by fun_prop
  have hFG : ∀ p, (F (G p)).1 = p.1.1 ∧ (F (G p)).2.1 = p.1.2.1 := fun _ => ⟨rfl, rfl⟩
  have hclosed : IsClosedMap F := by
    intro C hC
    have hR : IsClosed {p : (I × (X × W)) × I | (F (G p)).2.2 = p.1.2.2} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    have heq : F '' C = Prod.fst '' ({p | (F (G p)).2.2 = p.1.2.2} ∩ G ⁻¹' C) := by
      ext y
      constructor
      · rintro ⟨q, hq, rfl⟩
        have hs := coeff_mem_Icc g κ q
        let s : I := ⟨_, hs.1, hs.2.trans q.1.2.2⟩
        have hGF : G (F q, s) = q := by
          simp only [G, F, s, disp, sub_add_cancel]
        refine ⟨(F q, s), ⟨?_, ?_⟩, rfl⟩
        · simp only [mem_ofPred_eq, hGF]
        · simpa only [mem_preimage, hGF] using hq
      · rintro ⟨p, ⟨hp, hpC⟩, rfl⟩
        refine ⟨G p, hpC, ?_⟩
        exact Prod.ext (hFG p).1 (Prod.ext (hFG p).2 hp)
    rw [heq]
    exact isClosedMap_fst_of_compactSpace _ (hR.inter (hC.preimage hG))
  exact isHomeomorph_iff_continuous_isClosedMap_bijective.2 ⟨hF, hclosed, hbij⟩

variable (κ) in
/-- The ambient isotopy of `X × W` **straightening the graph** of a continuous map `g : X → W`
onto the zero section, for a constant `κ > 2`. At time `t` it moves `(x, w)` to `(x, w - s • g x)`
for some `s ∈ [0, t]`, with `s = t` when `‖w‖ ≤ ‖g x‖` and `s = 0` when `κ * ‖g x‖ ≤ ‖w‖`. So it
preserves the fibres, moves only points within `κ * ‖g x‖` of the zero section, and carries the
graph of `g` onto the graph of `(1 - t) • g`. The constant `κ > 2` bounds the support. -/
def straightenGraph (hκ : 2 < κ) : AmbientIsotopy (X × W) where
  toFun q := (q.2.1, q.2.2 - disp g κ q)
  continuous_toFun := by
    have := continuous_disp g (κ := κ) (by linarith)
    fun_prop
  isHomeomorph_total' := isHomeomorph_straightenGraph_total g hκ
  map_zero_left' y := by simp [disp]

variable (hκ : 2 < κ)

/-- The formula of the straightening, in terms of its displacement. -/
private theorem straightenGraph_apply (q : I × (X × W)) :
    (straightenGraph g κ hκ).toContinuousMap q = (q.2.1, q.2.2 - disp g κ q) :=
  (rfl)

/-- **The straightening preserves the fibres** `{x} × W`. -/
@[simp]
theorem straightenGraph_apply_fst (q : I × (X × W)) :
    ((straightenGraph g κ hκ).toContinuousMap q).1 = q.2.1 :=
  (rfl)

/-- At time `t` the straightening moves a point `(x, w)` along the direction of `g x`, to
`(x, w - s • g x)` for some `s ∈ [0, t]`. -/
theorem exists_straightenGraph_apply_eq (q : I × (X × W)) :
    ∃ s ∈ Icc (0 : ℝ) q.1,
      (straightenGraph g κ hκ).toContinuousMap q = (q.2.1, q.2.2 - s • g q.2.1) :=
  ⟨_, coeff_mem_Icc g κ q, straightenGraph_apply g hκ q⟩

/-- **The straightening is supported near the graph**: it fixes every point `(x, w)` with
`κ * ‖g x‖ ≤ ‖w‖`, at all times. In particular it fixes the fibres over the zeros of `g`. -/
theorem straightenGraph_apply_of_mul_norm_le {y : X × W} (hy : κ * ‖g y.1‖ ≤ ‖y.2‖) (t : I) :
    (straightenGraph g κ hκ).toContinuousMap (t, y) = y := by
  rw [straightenGraph_apply]
  rcases eq_or_ne (g y.1) 0 with h | h
  · simp [disp, h]
  · simp [disp, weight_of_mul_le (by linarith) (norm_pos_iff.2 h) hy]

/-- Close to the zero section the straightening is a translation: at time `t` it moves every
point `(x, w)` with `‖w‖ ≤ ‖g x‖` to `(x, w - t • g x)`. -/
theorem straightenGraph_apply_of_norm_le {y : X × W} (hy : ‖y.2‖ ≤ ‖g y.1‖) (t : I) :
    (straightenGraph g κ hκ).toContinuousMap (t, y) = (y.1, y.2 - (t : ℝ) • g y.1) := by
  rw [straightenGraph_apply, disp, weight_of_le (by linarith) (norm_nonneg _) hy, mul_one]

/-- **The straightening moves the graph along straight lines**: at time `t` it carries `(x, g x)`
to `(x, (1 - t) • g x)`. -/
@[simp]
theorem straightenGraph_apply_graph (t : I) (x : X) :
    (straightenGraph g κ hκ).toContinuousMap (t, (x, g x)) = (x, (1 - (t : ℝ)) • g x) := by
  rw [straightenGraph_apply_of_norm_le g hκ le_rfl, sub_smul, one_smul]

/-- **The final homeomorphism of the straightening carries the graph of `g` onto the zero
section** of `X × W`. -/
theorem straightenGraph_final_image_range :
    (straightenGraph g κ hκ).final '' range (fun x => (x, g x)) =
      range fun x : X => (x, (0 : W)) := by
  rw [← range_comp]
  congr 1
  funext x
  simp

end AmbientIsotopy

end TauCeti
