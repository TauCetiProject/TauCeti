/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic

/-!
# Half-discs are Lipschitz domains

The open half-disc `TauCeti.halfDisc r` is the set of points of `WithLp 2 (ℝ × ℝ)` of norm less
than `r` with positive first coordinate. The first coordinate is the normal coordinate of the model
space of Lipschitz boundary charts, so in the complex coordinate `z = s + it` it plays the role of
`t = Im z`, and `halfDisc r` is the interior of the half-disc `{z | 0 ≤ Im z ∧ |z| < r}`.

Its frontier consists of the segment `{0} × [-r, r]`, the arc of the circle of radius `r` with
positive first coordinate, and the two corners `(0, ±r)`. Each frontier point has an explicit
Lipschitz boundary chart:

* on the open segment the chart is a translation and the graph is zero;
* on the arc the normal direction points to the centre, and the graph is the lower boundary of the
  disc, truncated so that it is globally Lipschitz;
* at a corner the normal direction `(3/5, ∓4/5)` points strictly between the inner normals of the
  segment and the arc, and the graph is the maximum of the two boundary graphs.

The frontier is compact, so a single Lipschitz bound serves all frontier points
(`Set.IsLipschitzDomain.exists_isLipschitzDomainWith`).

## Main declarations

* `TauCeti.halfDisc`: the open half-disc of radius `r`.
* `TauCeti.isLipschitzDomain_halfDisc`: the half-disc is a Lipschitz domain.
* `TauCeti.exists_isLipschitzDomainWith_halfDisc`: the half-disc is a Lipschitz domain with a
  uniform Lipschitz bound.

## References

* P. Grisvard, *Elliptic Problems in Nonsmooth Domains*, Definition 1.2.1.1.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix B.
-/

public section

noncomputable section

open Metric Set TopologicalSpace TauCeti
open scoped NNReal

namespace TauCeti

namespace HalfDisc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two points of `WithLp 2 (ℝ × ℝ)` with the same coordinates are equal. -/
private theorem ext {x y : WithLp 2 (ℝ × ℝ)} (h₁ : x.fst = y.fst) (h₂ : x.snd = y.snd) :
    x = y :=
  WithLp.ofLp_injective 2 (Prod.ext h₁ h₂)

/-- The rotation of `WithLp 2 (ℝ × ℝ)` with first row `(α, β)`. -/
private def rotation (α β : ℝ) (h : α ^ 2 + β ^ 2 = 1) :
    WithLp 2 (ℝ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℝ × ℝ) where
  toFun x := WithLp.toLp 2 (α * x.fst + β * x.snd, -β * x.fst + α * x.snd)
  invFun z := WithLp.toLp 2 (α * z.fst - β * z.snd, β * z.fst + α * z.snd)
  map_add' x y := ext (by simp; ring) (by simp; ring)
  map_smul' c x := ext (by simp; ring) (by simp; ring)
  left_inv x := ext (by simp; linear_combination x.fst * h)
    (by simp; linear_combination x.snd * h)
  right_inv z := ext (by simp; linear_combination z.fst * h)
    (by simp; linear_combination z.snd * h)
  norm_map' x := by
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, WithLp.prod_norm_eq_of_L2,
      WithLp.toLp_fst, WithLp.toLp_snd, Real.norm_eq_abs, sq_abs]
    congr 1
    linear_combination (x.fst ^ 2 + x.snd ^ 2) * h

/-- The chart centred at `p` whose linear part is `rotation α β h`. -/
private def chart (p : WithLp 2 (ℝ × ℝ)) (α β : ℝ) (h : α ^ 2 + β ^ 2 = 1) :
    WithLp 2 (ℝ × ℝ) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × ℝ) :=
  (AffineIsometryEquiv.constVAdd ℝ _ (-p)).trans (rotation α β h).toAffineIsometryEquiv

private theorem chart_apply_self (p : WithLp 2 (ℝ × ℝ)) (α β : ℝ) (h : α ^ 2 + β ^ 2 = 1) :
    chart p α β h p = 0 := by
  simp [chart]

private theorem chart_symm_apply (p : WithLp 2 (ℝ × ℝ)) (α β : ℝ) (h : α ^ 2 + β ^ 2 = 1)
    (z : WithLp 2 (ℝ × ℝ)) : (chart p α β h).symm z = p + (rotation α β h).symm z := by
  rw [AffineIsometryEquiv.symm_apply_eq]
  simp [chart]

private theorem chart_symm_fst (p : WithLp 2 (ℝ × ℝ)) (α β : ℝ) (h : α ^ 2 + β ^ 2 = 1)
    (z : WithLp 2 (ℝ × ℝ)) : ((chart p α β h).symm z).fst = p.fst + (α * z.fst - β * z.snd) := by
  rw [chart_symm_apply]; rfl

private theorem chart_symm_snd (p : WithLp 2 (ℝ × ℝ)) (α β : ℝ) (h : α ^ 2 + β ^ 2 = 1)
    (z : WithLp 2 (ℝ × ℝ)) : ((chart p α β h).symm z).snd = p.snd + (β * z.fst + α * z.snd) := by
  rw [chart_symm_apply]; rfl

private theorem chart_zero_fst (p : WithLp 2 (ℝ × ℝ)) (α β : ℝ) (h : α ^ 2 + β ^ 2 = 1) :
    (chart p α β h 0).fst = -(α * p.fst + β * p.snd) := by
  simp [chart, rotation]; ring

private theorem chart_zero_snd (p : WithLp 2 (ℝ × ℝ)) (α β : ℝ) (h : α ^ 2 + β ^ 2 = 1) :
    (chart p α β h 0).snd = β * p.fst - α * p.snd := by
  simp [chart, rotation]; ring

/-- A chart whose cylinder meets `Ω` exactly above the graph of `γ` is a Lipschitz chart. -/
private theorem isLipschitzChart_of_forall_mem_iff {Ω : Set (WithLp 2 (ℝ × E))}
    {e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {γ : E → ℝ} {K : ℝ≥0} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hγ : LipschitzWith K γ)
    (hmem : ∀ z ∈ normalCylinder a b, e.symm z ∈ Ω ↔ γ z.snd < z.fst) :
    Ω.IsLipschitzChart e γ K a b where
  height_pos := ha
  radius_pos := hb
  lipschitzWith := hγ
  image_inter_normalCylinder := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq]
    refine and_congr_left fun hz => ?_
    rw [← hmem z hz]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · exact fun h => ⟨_, h, e.apply_symm_apply z⟩

/-- The lower boundary of `ball 0 r`, written in coordinates in which the centre of the ball is
`c`, truncated at tangential distance `ρ` from `c` so that it is globally Lipschitz. -/
private def ballGraph (c : WithLp 2 (ℝ × E)) (r ρ : ℝ) (v : E) : ℝ :=
  c.fst - √(r ^ 2 - min ‖v - c.snd‖ ρ ^ 2)

omit [NormedSpace ℝ E] in
private theorem lipschitzWith_ballGraph (c : WithLp 2 (ℝ × E)) {r ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ρ < r) :
    LipschitzWith (ρ / √(r ^ 2 - ρ ^ 2)).toNNReal (ballGraph c r ρ) := by
  have hs : 0 < √(r ^ 2 - ρ ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  refine LipschitzWith.of_dist_le_mul fun v w => ?_
  set m := min ‖v - c.snd‖ ρ
  set n := min ‖w - c.snd‖ ρ
  have hm0 : 0 ≤ m := le_min (norm_nonneg _) hρ0
  have hn0 : 0 ≤ n := le_min (norm_nonneg _) hρ0
  have hmρ : m ≤ ρ := min_le_right _ _
  have hnρ : n ≤ ρ := min_le_right _ _
  have hmn : |m - n| ≤ dist v w := by
    calc |m - n| ≤ max |‖v - c.snd‖ - ‖w - c.snd‖| |ρ - ρ| := abs_min_sub_min_le_max _ _ _ _
      _ = |‖v - c.snd‖ - ‖w - c.snd‖| := by simp
      _ ≤ ‖(v - c.snd) - (w - c.snd)‖ := abs_norm_sub_norm_le _ _
      _ = dist v w := by rw [sub_sub_sub_cancel_right, dist_eq_norm]
  set x := √(r ^ 2 - m ^ 2)
  set y := √(r ^ 2 - n ^ 2)
  have hx : x ^ 2 = r ^ 2 - m ^ 2 := Real.sq_sqrt (by nlinarith)
  have hy : y ^ 2 = r ^ 2 - n ^ 2 := Real.sq_sqrt (by nlinarith)
  have hxs : √(r ^ 2 - ρ ^ 2) ≤ x := Real.sqrt_le_sqrt (by nlinarith)
  have hys : √(r ^ 2 - ρ ^ 2) ≤ y := Real.sqrt_le_sqrt (by nlinarith)
  have hd : dist (ballGraph c r ρ v) (ballGraph c r ρ w) = |y - x| := by
    simp only [ballGraph, Real.dist_eq]
    rw [show c.fst - x - (c.fst - y) = y - x by ring]
  rw [hd, Real.coe_toNNReal _ (div_nonneg hρ0 hs.le), div_mul_eq_mul_div,
    le_div_iff₀ hs]
  -- `|y - x| (x + y) = |m - n| (m + n) ≤ 2 ρ dist v w`, and `x + y ≥ 2 √(r² - ρ²)`.
  have hprod : |y - x| * (x + y) = |m - n| * (m + n) := by
    rw [← abs_of_nonneg (by positivity : 0 ≤ x + y), ← abs_of_nonneg (by positivity : 0 ≤ m + n),
      ← abs_mul, ← abs_mul]
    rw [abs_eq_abs]
    left
    linear_combination hy - hx
  have h1 : |y - x| * (2 * √(r ^ 2 - ρ ^ 2)) ≤ |y - x| * (x + y) :=
    mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  have h2 : |m - n| * (m + n) ≤ dist v w * (2 * ρ) :=
    mul_le_mul hmn (by linarith) (by positivity) dist_nonneg
  nlinarith [abs_nonneg (y - x)]

/-- Inside a cylinder lying in the lower half of the ball `ball 0 r` seen from the chart `e`, the
ball is the region above `ballGraph`. -/
private theorem symm_mem_ball_iff (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) {r ρ a b : ℝ}
    (hr : 0 ≤ r) (ha : a ≤ (e 0).fst) (hb : ‖(e 0).snd‖ + b ≤ ρ) {z : WithLp 2 (ℝ × E)}
    (hz : z ∈ normalCylinder a b) :
    e.symm z ∈ ball 0 r ↔ ballGraph (e 0) r ρ z.snd < z.fst := by
  set c := e 0
  rw [mem_normalCylinder] at hz
  have hdist : dist (e.symm z) 0 = dist z c := by rw [← e.dist_map, e.apply_symm_apply]
  have hm : min ‖z.snd - c.snd‖ ρ = ‖z.snd - c.snd‖ :=
    min_eq_left (by linarith [norm_sub_le z.snd c.snd])
  have hpos : 0 ≤ c.fst - z.fst := by linarith
  have hsq : dist z c ^ 2 = (z.fst - c.fst) ^ 2 + ‖z.snd - c.snd‖ ^ 2 := by
    rw [dist_eq_norm, WithLp.prod_norm_sq_eq_of_L2, WithLp.sub_fst, WithLp.sub_snd,
      Real.norm_eq_abs, sq_abs]
  rw [mem_ball, hdist, ballGraph, hm, sub_lt_comm, Real.lt_sqrt hpos,
    ← sq_lt_sq₀ dist_nonneg hr, hsq]
  constructor <;> intro h <;> nlinarith

end HalfDisc

open HalfDisc

/-- The open half-disc of radius `r` in `WithLp 2 (ℝ × ℝ)`: the points of norm less than `r` whose
first coordinate, the normal coordinate of Lipschitz boundary charts, is positive. -/
@[expose] def halfDisc (r : ℝ) : Opens (WithLp 2 (ℝ × ℝ)) :=
  ⟨ball 0 r ∩ {x | 0 < x.fst},
    isOpen_ball.inter (isOpen_lt continuous_const (WithLp.prod_continuous_ofLp 2 ℝ ℝ).fst)⟩

@[simp]
theorem coe_halfDisc (r : ℝ) :
    (halfDisc r : Set (WithLp 2 (ℝ × ℝ))) = ball 0 r ∩ {x | 0 < x.fst} :=
  rfl

theorem mem_halfDisc {r : ℝ} {x : WithLp 2 (ℝ × ℝ)} : x ∈ halfDisc r ↔ ‖x‖ < r ∧ 0 < x.fst := by
  rw [← SetLike.mem_coe, coe_halfDisc, mem_inter_iff, mem_ball_zero_iff, mem_ofPred_eq]

theorem isBounded_halfDisc (r : ℝ) : Bornology.IsBounded (halfDisc r : Set (WithLp 2 (ℝ × ℝ))) :=
  isBounded_ball.subset inter_subset_left

/-- The closure of the half-disc lies in the closed half-disc. -/
private theorem closure_halfDisc_subset (r : ℝ) :
    closure (halfDisc r : Set (WithLp 2 (ℝ × ℝ))) ⊆ closedBall 0 r ∩ {x | 0 ≤ x.fst} :=
  closure_minimal (inter_subset_inter ball_subset_closedBall fun _ (hx : 0 < _) => hx.le)
    (isClosed_closedBall.inter (isClosed_le continuous_const
      (WithLp.prod_continuous_ofLp 2 ℝ ℝ).fst))

private theorem norm_sq_eq (x : WithLp 2 (ℝ × ℝ)) : ‖x‖ ^ 2 = x.fst ^ 2 + x.snd ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]

/-- A Lipschitz chart of the half-disc centred at a point `p` of the arc `‖p‖ = r` with
`p.fst > 0`, whose normal direction points to the centre of the disc. -/
private theorem exists_isLipschitzChart_halfDisc_of_arc {r : ℝ} {p : WithLp 2 (ℝ × ℝ)}
    (hp : ‖p‖ = r) (hp₁ : 0 < p.fst) :
    ∃ (e : WithLp 2 (ℝ × ℝ) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × ℝ)) (γ : ℝ → ℝ) (K : ℝ≥0) (a b : ℝ),
      (halfDisc r : Set (WithLp 2 (ℝ × ℝ))).IsLipschitzChart e γ K a b ∧ e p = 0 := by
  have hsq := norm_sq_eq p
  rw [hp] at hsq
  have hr0 : 0 ≤ r := hp ▸ norm_nonneg p
  have hr : 0 < r := lt_of_le_of_ne hr0 fun h => by subst h; nlinarith
  have ht : p.fst ≤ r := by nlinarith
  have hs : |p.snd| ≤ r := abs_le_of_sq_le_sq (by nlinarith) hr0
  have hαβ : (-p.fst / r) ^ 2 + (-p.snd / r) ^ 2 = 1 := by
    field_simp
    linear_combination hsq.symm
  set e := chart p (-p.fst / r) (-p.snd / r) hαβ
  have he₁ : (e 0).fst = r := by
    rw [chart_zero_fst]
    field_simp
    linear_combination -hsq
  have he₂ : (e 0).snd = 0 := by
    rw [chart_zero_snd]
    ring
  refine ⟨e, ballGraph (e 0) r (r / 2), _, p.fst / 4, p.fst / 4,
    isLipschitzChart_of_forall_mem_iff (by positivity) (by positivity)
      (lipschitzWith_ballGraph _ (by positivity) (by linarith)) fun z hz => ?_,
    chart_apply_self _ _ _ _⟩
  have hz' := hz
  rw [mem_normalCylinder, Real.norm_eq_abs] at hz'
  obtain ⟨-, hu, hv⟩ := hz'
  have hfst : 0 < (e.symm z).fst := by
    rw [chart_symm_fst]
    have hsv : -(p.snd * z.snd) ≤ r * (p.fst / 4) :=
      calc -(p.snd * z.snd) ≤ |p.snd * z.snd| := neg_le_abs _
        _ = |p.snd| * |z.snd| := abs_mul _ _
        _ ≤ r * (p.fst / 4) := mul_le_mul hs hv.le (abs_nonneg _) hr0
    have key : 0 < r * p.fst - p.fst * z.fst + p.snd * z.snd := by nlinarith
    have heq : p.fst + (-p.fst / r * z.fst - -p.snd / r * z.snd) =
        (r * p.fst - p.fst * z.fst + p.snd * z.snd) / r := by
      field_simp
      ring
    rw [heq]
    exact div_pos key hr
  have hball := symm_mem_ball_iff e hr0 (ρ := r / 2) (by linarith) (by
    rw [he₂, norm_zero]; linarith) hz
  simp only [coe_halfDisc, mem_inter_iff, mem_ofPred_eq, hball, hfst, and_true]

/-- A Lipschitz chart of the half-disc centred at a point `p` of the flat part of its boundary,
`p.fst = 0` and `|p.snd| < r`. -/
private theorem exists_isLipschitzChart_halfDisc_of_flat {r : ℝ} {p : WithLp 2 (ℝ × ℝ)}
    (hp₁ : p.fst = 0) (hp₂ : |p.snd| < r) :
    ∃ (e : WithLp 2 (ℝ × ℝ) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × ℝ)) (γ : ℝ → ℝ) (K : ℝ≥0) (a b : ℝ),
      (halfDisc r : Set (WithLp 2 (ℝ × ℝ))).IsLipschitzChart e γ K a b ∧ e p = 0 := by
  have hαβ : (1 : ℝ) ^ 2 + 0 ^ 2 = 1 := by norm_num
  have ha : 0 < (r - |p.snd|) / 2 := by linarith
  refine ⟨chart p 1 0 hαβ, fun _ => 0, 0, (r - |p.snd|) / 2, (r - |p.snd|) / 2,
    isLipschitzChart_of_forall_mem_iff ha ha (LipschitzWith.const 0) fun z hz => ?_,
    chart_apply_self _ _ _ _⟩
  rw [mem_normalCylinder, Real.norm_eq_abs, ← and_assoc, ← abs_lt] at hz
  obtain ⟨hu, hv⟩ := hz
  have hfst : ((chart p 1 0 hαβ).symm z).fst = z.fst := by
    rw [chart_symm_fst, hp₁]
    ring
  have hnorm : ‖(chart p 1 0 hαβ).symm z‖ < r := by
    have hsnd : ((chart p 1 0 hαβ).symm z).snd = p.snd + z.snd := by
      rw [chart_symm_snd]
      ring
    have hA := abs_nonneg z.fst
    have hB : |p.snd + z.snd| < (r + |p.snd|) / 2 := by
      linarith [abs_add_le p.snd z.snd]
    have hA2 : |z.fst| ^ 2 < ((r - |p.snd|) / 2) ^ 2 := by nlinarith
    have hB2 : |p.snd + z.snd| ^ 2 < ((r + |p.snd|) / 2) ^ 2 := by
      nlinarith [abs_nonneg (p.snd + z.snd)]
    have hS := abs_nonneg p.snd
    refine (sq_lt_sq₀ (norm_nonneg _) (by linarith)).1 ?_
    rw [norm_sq_eq, hfst, hsnd, ← sq_abs z.fst, ← sq_abs (p.snd + z.snd)]
    nlinarith
  simp only [coe_halfDisc, mem_inter_iff, mem_ball_zero_iff, mem_ofPred_eq, hnorm, hfst, true_and]

/-- A Lipschitz chart of the half-disc centred at a corner `p`, `p.fst = 0` and `|p.snd| = r`. Its
normal direction `(3/5, -4/5 * σ)`, with `σ = p.snd / r`, points strictly into the quarter plane
spanned by the normals of the two boundary pieces, so both pieces are graphs over the tangential
direction. -/
private theorem exists_isLipschitzChart_halfDisc_of_corner {r : ℝ} {p : WithLp 2 (ℝ × ℝ)}
    (hr : 0 < r) (hp₁ : p.fst = 0) (hp₂ : |p.snd| = r) :
    ∃ (e : WithLp 2 (ℝ × ℝ) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × ℝ)) (γ : ℝ → ℝ) (K : ℝ≥0) (a b : ℝ),
      (halfDisc r : Set (WithLp 2 (ℝ × ℝ))).IsLipschitzChart e γ K a b ∧ e p = 0 := by
  set σ := p.snd / r
  have hs2 : p.snd ^ 2 = r ^ 2 := by rw [← sq_abs, hp₂]
  have hσ2 : σ ^ 2 = 1 := by
    rw [div_pow, hs2, div_self (by positivity)]
  have hσ : |σ| = 1 := by
    rw [abs_div, hp₂, abs_of_pos hr, div_self hr.ne']
  have hσs : σ * p.snd = r := by
    rw [div_mul_eq_mul_div, ← sq, hs2, sq, mul_div_assoc, div_self hr.ne', mul_one]
  have hαβ : (3 / 5 : ℝ) ^ 2 + (-(4 / 5) * σ) ^ 2 = 1 := by
    linear_combination (16 / 25 : ℝ) * hσ2
  set e := chart p (3 / 5) (-(4 / 5) * σ) hαβ
  have he₁ : (e 0).fst = 4 * r / 5 := by
    rw [chart_zero_fst, hp₁]
    linear_combination (4 / 5 : ℝ) * hσs
  have he₂ : ‖(e 0).snd‖ = 3 * r / 5 := by
    rw [chart_zero_snd, hp₁, Real.norm_eq_abs, show -(4 / 5) * σ * 0 - 3 / 5 * p.snd =
      -(3 / 5) * p.snd by ring, abs_mul, hp₂]
    norm_num
    ring
  have hg : LipschitzWith 2 fun v : ℝ => -(4 / 3 * σ) * v := by
    refine LipschitzWith.of_dist_le_mul fun v w => ?_
    rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_neg, abs_mul, hσ]
    norm_num
    nlinarith [abs_nonneg (v - w)]
  refine ⟨e, fun v => max (ballGraph (e 0) r (4 * r / 5) v) (-(4 / 3 * σ) * v), _, r / 5, r / 5,
    isLipschitzChart_of_forall_mem_iff (by positivity) (by positivity)
      ((lipschitzWith_ballGraph _ (by positivity) (by linarith)).max hg) fun z hz => ?_,
    chart_apply_self _ _ _ _⟩
  have hfst : 0 < (e.symm z).fst ↔ -(4 / 3 * σ) * z.snd < z.fst := by
    rw [chart_symm_fst, hp₁]
    constructor <;> intro h <;> linarith
  have hball := symm_mem_ball_iff e hr.le (ρ := 4 * r / 5) (by linarith) (by linarith) hz
  simp only [coe_halfDisc, mem_inter_iff, mem_ofPred_eq, hball, hfst, max_lt_iff]

/-- **The half-disc is a Lipschitz domain.** Its frontier consists of the flat part, the arc and
the two corners `(0, ±r)`, and each point has a Lipschitz boundary chart. -/
theorem isLipschitzDomain_halfDisc (r : ℝ) :
    (halfDisc r : Set (WithLp 2 (ℝ × ℝ))).IsLipschitzDomain ℝ := by
  refine Set.isLipschitzDomain_iff_exists_mem_normalCylinder.2 fun p hp => ?_
  suffices H : ∃ (e : WithLp 2 (ℝ × ℝ) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × ℝ)) (γ : ℝ → ℝ) (K : ℝ≥0) (a b : ℝ),
      (halfDisc r : Set (WithLp 2 (ℝ × ℝ))).IsLipschitzChart e γ K a b ∧ e p = 0 by
    obtain ⟨e, γ, K, a, b, hc, hex⟩ := H
    exact ⟨e, γ, K, a, b, hc, hex ▸ zero_mem_normalCylinder hc.height_pos hc.radius_pos⟩
  have hr : 0 < r := by
    by_contra h
    rw [coe_halfDisc, ball_eq_empty.2 (not_lt.1 h), empty_inter, frontier_empty] at hp
    exact hp
  have hcl := closure_halfDisc_subset r (frontier_subset_closure hp)
  have hnot : p ∉ halfDisc r := ((halfDisc r).isOpen.frontier_eq ▸ hp).2
  rw [mem_inter_iff, mem_closedBall_zero_iff, mem_ofPred_eq] at hcl
  obtain ⟨hpr, hp₁⟩ := hcl
  rw [mem_halfDisc, not_and_or, not_lt, not_lt] at hnot
  have hsq := norm_sq_eq p
  rcases hp₁.lt_or_eq with hp₁ | hp₁
  · exact exists_isLipschitzChart_halfDisc_of_arc (le_antisymm hpr (hnot.resolve_right
      hp₁.not_ge)) hp₁
  rcases lt_or_ge |p.snd| r with hs | hs
  · exact exists_isLipschitzChart_halfDisc_of_flat hp₁.symm hs
  · have hs' : |p.snd| ≤ r := by
      refine abs_le_of_sq_le_sq ?_ ((norm_nonneg p).trans hpr)
      nlinarith [norm_nonneg p]
    exact exists_isLipschitzChart_halfDisc_of_corner hr hp₁.symm (le_antisymm hs' hs)

/-- **The half-disc is a Lipschitz domain with a uniform constant**, since its frontier is
compact. -/
theorem exists_isLipschitzDomainWith_halfDisc (r : ℝ) :
    ∃ L, (halfDisc r : Set (WithLp 2 (ℝ × ℝ))).IsLipschitzDomainWith L :=
  (isLipschitzDomain_halfDisc r).exists_isLipschitzDomainWith
    ((isCompact_closedBall 0 r).of_isClosed_subset isClosed_frontier
      (frontier_subset_closure.trans ((closure_halfDisc_subset r).trans inter_subset_left)))

end TauCeti
