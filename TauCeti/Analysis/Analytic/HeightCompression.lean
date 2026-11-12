/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import TauCeti.Analysis.SpecialFunctions.Arsinh
import Mathlib.Topology.MetricSpace.Contracting
import TauCeti.Analysis.Analytic.Approximation

/-!
# Analytic compressions of the height coordinate

On a cylinder `E × ℝ`, with base point `u` and height `t`, Łojasiewicz straightens an ordered
family of graphs by an analytic automorphism `g = g₂ ∘ g₁` which first rescales the base
coordinate by a positive analytic function of the height, and then compresses the height of the
point `(u, t)` according to the size of `t` relative to `√(1 + ‖u‖²)`. This file constructs both
automorphisms and shows that they and their inverses are analytic. The height compression uses
the inverse `β` of the normalized hyperbolic sine `t ↦ sinh t / sinh 1`, which is
`TauCeti.normalizedArsinh` from `TauCeti/Analysis/SpecialFunctions/Arsinh.lean`.

* `TauCeti.baseScaling h hh`: the automorphism `g₁ (u, t) = (h t • u, t)` of `E × 𝕜`, for a
  nowhere-vanishing `h : 𝕜 → 𝕜`. It is analytic, with analytic inverse, wherever `h` is.
* `TauCeti.heightCompression E`: the automorphism `g₂ (u, t) = (u, β (t / √(1 + ‖u‖²)))` of
  `E × ℝ`. It is increasing on every vertical line and sends `(u, t)` into the strip `|s| < 1`
  exactly when `t² < 1 + ‖u‖²` (`TauCeti.abs_heightCompression_snd_lt_one_iff`), and to a height
  at least (at most) `s` exactly when `t` is at least (at most) `√(1 + ‖u‖²) * (sinh s / sinh 1)`
  (`TauCeti.le_heightCompression_snd_iff`, `TauCeti.heightCompression_snd_le_iff`). When `E` is a
  real inner product space, it is analytic with analytic inverse.
* `TauCeti.mapsTo_heightCompression_comp_baseScaling`: if `√(t² - 1) < |h t| * γ t` whenever
  `|t| ≥ 1`, then `g₂ ∘ g₁` maps every point `(u, t)` with `γ t ≤ ‖u‖` into the strip `|s| < 1`.
  This is how the composite pushes the complement of a neighbourhood of the vertical axis, which
  contains the tube `‖u‖ ≤ γ t`, into a bounded strip.

The second group of results controls the slopes of graphs under these automorphisms. Say that a
set has *Lipschitz constant* `A` if any two of its points satisfy
`dist p.2 q.2 ≤ A * dist p.1 q.1`, so that the set is the graph of an `A`-Lipschitz function over
its projection to the base.

* `TauCeti.dist_snd_le_mul_dist_fst_of_mem_image_baseScaling`: let a set have base points of norm
  at most `a`, heights in `D` and Lipschitz constant `k`, and let `h` be `L`-Lipschitz on `D` with
  `c ≤ ‖h‖` there. If `L * a * k < c`, its image under `g₁` has Lipschitz constant
  `k / (c - L * a * k)`. This rests on the distance estimate
  `TauCeti.mul_dist_fst_le_dist_baseScaling_fst`.
* `TauCeti.closedBall_subset_fst_image_baseScaling_image_graphOn`: under the same hypotheses, the
  image under `g₁` of the graph of a `k`-Lipschitz function over `closedBall 0 a` lies over the
  whole ball `closedBall 0 (a * c)`.
* `TauCeti.dist_heightCompression_snd_le`: compressed heights differ by at most
  `2 * dist p.2 q.2 + dist p.1 q.1`, so `g₂` turns Lipschitz constant `A` into `2 * A + 1`
  (`TauCeti.dist_snd_le_mul_dist_fst_of_mem_image_heightCompression`).
* `TauCeti.dist_snd_le_three_mul_dist_fst_of_mem_image_heightCompression_comp_baseScaling`: if
  `2 * k ≤ |h|` on `D` and `L * a ≤ 1`, then `g₁` produces Lipschitz constant at most `1` and
  `g₂ ∘ g₁` produces Lipschitz constant at most `3`, a bound independent of the graph.
* `TauCeti.isBounded_image_heightCompression_comp_baseScaling`: `g₂ ∘ g₁` maps a set of points with
  bounded base points and heights in a compact set, on which `h` is continuous, to a bounded set.

The scaling function `h` itself is chosen analytic and positive, with
`√(t² - 1) < h t * γ t` for every `t` and, on each height interval `D` of a locally finite family
of disjoint compact intervals, a prescribed strict lower bound and a prescribed Lipschitz constant
(`TauCeti.exists_analyticOnNhd_sqrt_sq_sub_one_lt_mul`). Here `γ` is any function locally bounded
below by positive constants. These are the hypotheses on `h` of the results above.

Since `g₂` does not move base points, the projection of the image of a graph under `g₂ ∘ g₁` is
the projection of its image under `g₁`. In Łojasiewicz's lemma the graphs are pieces of a
locally finite family, with constants `k`, `a` and height intervals `D` depending on the piece:
the last result gives the uniform Lipschitz bound for the straightened family, and the ball
covering result shows that the projections of its members contain balls of radius `a * c`. The
lemma itself is assembled from these results in `TauCeti.Analysis.Analytic.GraphStraightening`.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §2, Lemma 10.
-/

public section

open Real Set Metric
open scoped NNReal

namespace TauCeti

/-! ### Rescaling the base by a function of the height -/

section baseScaling

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {h : 𝕜 → 𝕜} (hh : ∀ t, h t ≠ 0)

/-- For a nowhere-vanishing function `h` of the height, the automorphism `(u, t) ↦ (h t • u, t)`
of the cylinder `E × 𝕜`, rescaling each horizontal slice by the factor `h t`. -/
def baseScaling : E × 𝕜 ≃ E × 𝕜 :=
  Equiv.prodCongrLeft fun t ↦ (LinearEquiv.smulOfNeZero 𝕜 E (h t) (hh t)).toEquiv

@[simp]
theorem baseScaling_apply (p : E × 𝕜) : baseScaling hh p = (h p.2 • p.1, p.2) :=
  (rfl)

@[simp]
theorem baseScaling_symm_apply (p : E × 𝕜) :
    (baseScaling hh).symm p = ((h p.2)⁻¹ • p.1, p.2) :=
  (rfl)

variable {hh}

/-- The base scaling `(u, t) ↦ (h t • u, t)` is analytic at every point `(u, t)` at whose
height `t` the scaling function `h` is analytic. -/
@[fun_prop]
theorem analyticAt_baseScaling {p : E × 𝕜} (hp : AnalyticAt 𝕜 h p.2) :
    AnalyticAt 𝕜 (baseScaling hh) p := by
  rw [funext (baseScaling_apply hh)]
  have : AnalyticAt 𝕜 (fun q : E × 𝕜 ↦ h q.2) p := hp.comp analyticAt_snd
  exact (this.smul analyticAt_fst).prod analyticAt_snd

/-- The inverse `(u, t) ↦ ((h t)⁻¹ • u, t)` of the base scaling is analytic at every point
`(u, t)` at whose height `t` the scaling function `h` is analytic. -/
@[fun_prop]
theorem analyticAt_baseScaling_symm {p : E × 𝕜} (hp : AnalyticAt 𝕜 h p.2) :
    AnalyticAt 𝕜 (baseScaling hh).symm p := by
  rw [funext (baseScaling_symm_apply hh)]
  have : AnalyticAt 𝕜 (fun q : E × 𝕜 ↦ (h q.2)⁻¹) p := (hp.comp analyticAt_snd).inv (hh p.2)
  exact (this.smul analyticAt_fst).prod analyticAt_snd

/-- **Base scaling of Lipschitz graphs.** Let `p = (u, t)` and `q = (u', t')` be points with
`‖u'‖ ≤ a` whose heights satisfy `dist t t' ≤ k * dist u u'`, and suppose that `c ≤ ‖h t‖` and
`dist (h t) (h t') ≤ L * dist t t'`. Then rescaling the base by `h` maps `u` and `u'` to points at
distance at least `(c - L * a * k) * dist u u'`. -/
theorem mul_dist_fst_le_dist_baseScaling_fst {p q : E × 𝕜} {a c : ℝ} {k L : ℝ≥0}
    (hq : ‖q.1‖ ≤ a) (hc : c ≤ ‖h p.2‖) (hL : dist (h p.2) (h q.2) ≤ L * dist p.2 q.2)
    (hk : dist p.2 q.2 ≤ k * dist p.1 q.1) :
    (c - L * a * k) * dist p.1 q.1 ≤ dist (baseScaling hh p).1 (baseScaling hh q).1 := by
  rw [baseScaling_apply, baseScaling_apply]
  rw [dist_eq_norm, dist_eq_norm] at hL hk ⊢
  have hΔ : h p.2 • p.1 - h q.2 • q.1 = h p.2 • (p.1 - q.1) + (h p.2 - h q.2) • q.1 := by
    rw [smul_sub, sub_smul]
    abel
  have htri := norm_sub_le (h p.2 • (p.1 - q.1) + (h p.2 - h q.2) • q.1) ((h p.2 - h q.2) • q.1)
  rw [add_sub_cancel_right, norm_smul, norm_smul, ← hΔ] at htri
  have hh' : ‖h p.2 - h q.2‖ * ‖q.1‖ ≤ L * a * k * ‖p.1 - q.1‖ :=
    calc ‖h p.2 - h q.2‖ * ‖q.1‖ ≤ L * (k * ‖p.1 - q.1‖) * a :=
          mul_le_mul (hL.trans (mul_le_mul_of_nonneg_left hk L.2)) hq (norm_nonneg _)
            (by positivity)
      _ = L * a * k * ‖p.1 - q.1‖ := by ring
  nlinarith [mul_le_mul_of_nonneg_right hc (norm_nonneg (p.1 - q.1))]

/-- **Base scaling of Lipschitz graphs.** Let `s ⊆ E × 𝕜` consist of points with base points of norm
at most `a` and heights in `D`, whose heights satisfy `dist p.2 q.2 ≤ k * dist p.1 q.1`. If `h` is
`L`-Lipschitz on `D`, with `c ≤ ‖h t‖` for `t ∈ D`, and `L * a * k < c`, then the points of
`baseScaling hh '' s` satisfy the same inequality with the constant `k / (c - L * a * k)`. -/
theorem dist_snd_le_mul_dist_fst_of_mem_image_baseScaling {s : Set (E × 𝕜)} {D : Set 𝕜}
    {a c : ℝ} {k L : ℝ≥0} (hsa : ∀ p ∈ s, ‖p.1‖ ≤ a) (hsD : ∀ p ∈ s, p.2 ∈ D)
    (hk : ∀ p ∈ s, ∀ q ∈ s, dist p.2 q.2 ≤ k * dist p.1 q.1) (hL : LipschitzOnWith L h D)
    (hc : ∀ t ∈ D, c ≤ ‖h t‖) (hlt : L * a * k < c) :
    ∀ p ∈ baseScaling hh '' s, ∀ q ∈ baseScaling hh '' s,
      dist p.2 q.2 ≤ k / (c - L * a * k) * dist p.1 q.1 := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
  have hpos : 0 < c - L * a * k := sub_pos.2 hlt
  have key := mul_dist_fst_le_dist_baseScaling_fst (hh := hh) (hsa q hq) (hc _ (hsD p hp))
    (hL.dist_le_mul p.2 (hsD p hp) q.2 (hsD q hq)) (hk p hp q hq)
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  calc dist (baseScaling hh p).2 (baseScaling hh q).2 * (c - L * a * k)
      = dist p.2 q.2 * (c - L * a * k) := by simp
    _ ≤ k * dist p.1 q.1 * (c - L * a * k) := mul_le_mul_of_nonneg_right (hk p hp q hq) hpos.le
    _ = k * ((c - L * a * k) * dist p.1 q.1) := by ring
    _ ≤ k * dist (baseScaling hh p).1 (baseScaling hh q).1 := mul_le_mul_of_nonneg_left key k.2

/-- **The rescaled graph lies over a large ball.** Let `φ : E → 𝕜` be `k`-Lipschitz on
`closedBall 0 a`, with values in `D` there. If `h` is `L`-Lipschitz on `D`, with `c ≤ ‖h t‖` for
`t ∈ D` and some `c > 0`, and `L * a * k < c`, then the image of the graph of `φ` over
`closedBall 0 a` under the base scaling lies over every point of `closedBall 0 (a * c)`.

A point `u` lies over `w` exactly when it is a fixed point of `u ↦ (h (φ u))⁻¹ • w`, which maps
`closedBall 0 a` into itself and is a contraction there with constant `L * a * k / c`. -/
theorem closedBall_subset_fst_image_baseScaling_image_graphOn [CompleteSpace E] {φ : E → 𝕜}
    {D : Set 𝕜} {a c : ℝ} {k L : ℝ≥0} (hφ : LipschitzOnWith k φ (closedBall 0 a))
    (hφD : MapsTo φ (closedBall 0 a) D) (hL : LipschitzOnWith L h D) (hc : ∀ t ∈ D, c ≤ ‖h t‖)
    (hc0 : 0 < c) (hlt : L * a * k < c) :
    closedBall 0 (a * c) ⊆ Prod.fst '' (baseScaling hh '' (closedBall 0 a).graphOn φ) := by
  intro w hw
  rw [mem_closedBall_zero_iff] at hw
  have ha : 0 ≤ a := by nlinarith [norm_nonneg w]
  have hhc {u : E} (hu : u ∈ closedBall (0 : E) a) : c ≤ ‖h (φ u)‖ := hc _ (hφD hu)
  have hT : MapsTo (fun u ↦ (h (φ u))⁻¹ • w) (closedBall 0 a) (closedBall 0 a) := by
    intro u hu
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, inv_mul_le_iff₀ (hc0.trans_le (hhc hu))]
    nlinarith [hhc hu]
  let K : ℝ≥0 := ⟨L * a * k / c, div_nonneg (mul_nonneg (mul_nonneg L.2 ha) k.2) hc0.le⟩
  have hK : (K : ℝ) = L * a * k / c := rfl
  have hTL : LipschitzOnWith K (fun u ↦ (h (φ u))⁻¹ • w) (closedBall 0 a) := by
    refine LipschitzOnWith.of_dist_le_mul fun u hu v hv ↦ ?_
    have hu0 : h (φ u) ≠ 0 := hh _
    have hv0 : h (φ v) ≠ 0 := hh _
    have hhuv : ‖h (φ v) - h (φ u)‖ ≤ L * (k * dist u v) := by
      rw [← dist_eq_norm, dist_comm u v]
      exact (hL.dist_le_mul _ (hφD hv) _ (hφD hu)).trans
        (mul_le_mul_of_nonneg_left (hφ.dist_le_mul v hv u hu) L.2)
    have hcc : c * c ≤ ‖h (φ u)‖ * ‖h (φ v)‖ := mul_le_mul (hhc hu) (hhc hv) hc0.le (norm_nonneg _)
    rw [dist_eq_norm, ← sub_smul, norm_smul, inv_sub_inv hu0 hv0, norm_div, norm_mul, hK]
    calc ‖h (φ v) - h (φ u)‖ / (‖h (φ u)‖ * ‖h (φ v)‖) * ‖w‖
        ≤ L * (k * dist u v) / (c * c) * (a * c) := by
          gcongr
      _ = L * a * k / c * dist u v := by field_simp
  have hcontr : ContractingWith K (hT.restrict _ _ _) :=
    ⟨by rw [← NNReal.coe_lt_coe, hK, NNReal.coe_one]; exact (div_lt_one hc0).2 hlt,
      hTL.mapsToRestrict hT⟩
  obtain ⟨u, hu, hfix, -⟩ := hcontr.exists_fixedPoint' isClosed_closedBall.isComplete hT
    (mem_closedBall_self ha) (edist_ne_top _ _)
  have hu' : (h (φ u))⁻¹ • w = u := hfix
  refine ⟨(h (φ u) • u, φ u), ⟨(u, φ u), ⟨u, hu, rfl⟩, by rw [baseScaling_apply]⟩, ?_⟩
  rw [← smul_inv_smul₀ (hh (φ u)) w, hu']

end baseScaling

/-! ### Compressing the height -/

section heightCompression

variable (E : Type*) [NormedAddCommGroup E]

/-- The automorphism `(u, t) ↦ (u, β (t / √(1 + ‖u‖²)))` of the cylinder `E × ℝ`, where `β` is
`TauCeti.normalizedArsinh`. On the vertical line over `u` it is an increasing bijection taking the
heights `± √(1 + ‖u‖²)` to `± 1`. -/
noncomputable def heightCompression : E × ℝ ≃ E × ℝ where
  toFun p := (p.1, normalizedArsinh (p.2 / √(1 + ‖p.1‖ ^ 2)))
  invFun p := (p.1, √(1 + ‖p.1‖ ^ 2) * (sinh p.2 / sinh 1))
  left_inv p := by
    have : √(1 + ‖p.1‖ ^ 2) ≠ 0 := (sqrt_pos.2 (by positivity)).ne'
    simp [mul_div_cancel₀ _ this]
  right_inv p := by
    have : √(1 + ‖p.1‖ ^ 2) ≠ 0 := (sqrt_pos.2 (by positivity)).ne'
    simp [mul_div_cancel_left₀ _ this]

variable {E}

@[simp]
theorem heightCompression_apply (p : E × ℝ) :
    heightCompression E p = (p.1, normalizedArsinh (p.2 / √(1 + ‖p.1‖ ^ 2))) :=
  (rfl)

@[simp]
theorem heightCompression_symm_apply (p : E × ℝ) :
    (heightCompression E).symm p = (p.1, √(1 + ‖p.1‖ ^ 2) * (sinh p.2 / sinh 1)) :=
  (rfl)

/-- The height compression is increasing on every vertical line. -/
theorem strictMono_heightCompression_snd (u : E) :
    StrictMono fun t ↦ (heightCompression E (u, t)).2 := fun t t' htt' ↦ by
  simpa using div_lt_div_of_pos_right htt' (sqrt_pos.2 (by positivity))

/-- The height compression sends `(u, t)` into the strip `|s| < 1` exactly when
`t² < 1 + ‖u‖²`. -/
theorem abs_heightCompression_snd_lt_one_iff {p : E × ℝ} :
    |(heightCompression E p).2| < 1 ↔ p.2 ^ 2 < 1 + ‖p.1‖ ^ 2 := by
  have hpos : 0 < √(1 + ‖p.1‖ ^ 2) := sqrt_pos.2 (by positivity)
  rw [heightCompression_apply, abs_normalizedArsinh_lt_one_iff, abs_div, abs_of_pos hpos,
    div_lt_one hpos, lt_sqrt (abs_nonneg _), sq_abs]

/-- The height compression takes `(u, t)` to a height at least `s` exactly when `t` is at least
`√(1 + ‖u‖²) * (sinh s / sinh 1)`, the height over `u` that it takes to `s`. -/
theorem le_heightCompression_snd_iff {u : E} {s t : ℝ} :
    s ≤ (heightCompression E (u, t)).2 ↔ √(1 + ‖u‖ ^ 2) * (sinh s / sinh 1) ≤ t := by
  have hpos : 0 < √(1 + ‖u‖ ^ 2) := sqrt_pos.2 (by positivity)
  conv_lhs => rw [← normalizedArsinh_sinh_div s]
  rw [heightCompression_apply, normalizedArsinh_le_normalizedArsinh, le_div_iff₀ hpos, mul_comm]

/-- The height compression takes `(u, t)` to a height at most `s` exactly when `t` is at most
`√(1 + ‖u‖²) * (sinh s / sinh 1)`, the height over `u` that it takes to `s`. -/
theorem heightCompression_snd_le_iff {u : E} {s t : ℝ} :
    (heightCompression E (u, t)).2 ≤ s ↔ t ≤ √(1 + ‖u‖ ^ 2) * (sinh s / sinh 1) := by
  have hpos : 0 < √(1 + ‖u‖ ^ 2) := sqrt_pos.2 (by positivity)
  conv_lhs => rw [← normalizedArsinh_sinh_div s]
  rw [heightCompression_apply, normalizedArsinh_le_normalizedArsinh, div_le_iff₀ hpos, mul_comm]

/-- If `√(t² - 1) < |h t| * γ t` whenever `|t| ≥ 1`, then rescaling the base by the
nowhere-vanishing function `h` and compressing the height maps every point `(u, t)` with
`γ t ≤ ‖u‖` into the strip `|s| < 1`. -/
theorem mapsTo_heightCompression_comp_baseScaling [NormedSpace ℝ E] {h γ : ℝ → ℝ}
    (hh : ∀ t, h t ≠ 0) (hhγ : ∀ t, 1 ≤ |t| → √(t ^ 2 - 1) < |h t| * γ t) :
    MapsTo (heightCompression E ∘ baseScaling hh) {p | γ p.2 ≤ ‖p.1‖} {p | |p.2| < 1} := by
  rintro ⟨u, t⟩ (hu : γ t ≤ ‖u‖)
  simp only [mem_ofPred_eq, Function.comp_apply, abs_heightCompression_snd_lt_one_iff,
    baseScaling_apply, norm_smul, norm_eq_abs]
  rcases lt_or_ge |t| 1 with ht | ht
  · have : t ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one t).2 ht
    nlinarith [sq_nonneg (|h t| * ‖u‖)]
  · have h1 : √(t ^ 2 - 1) < |h t| * ‖u‖ :=
      (hhγ t ht).trans_le (mul_le_mul_of_nonneg_left hu (abs_nonneg _))
    have h2 := (sqrt_lt' ((sqrt_nonneg _).trans_lt h1)).1 h1
    rw [mul_pow] at h2
    linarith

/-- **Lipschitz control of the compressed height.** The compressed heights of two points differ by
at most twice the difference of their heights plus the distance of their base points. -/
theorem dist_heightCompression_snd_le (p q : E × ℝ) :
    dist (heightCompression E p).2 (heightCompression E q).2 ≤ 2 * dist p.2 q.2 + dist p.1 q.1 := by
  have hone (x : ℝ) : 1 ≤ √(1 + x ^ 2) := one_le_sqrt.2 (le_add_of_nonneg_right (sq_nonneg _))
  -- `x ↦ √(1 + x²)` is `1`-Lipschitz
  have hsqrt (x y : ℝ) : √(1 + x ^ 2) ≤ √(1 + y ^ 2) + |x - y| := by
    have hy : |y| ≤ √(1 + y ^ 2) := abs_le_sqrt (le_add_of_nonneg_left zero_le_one)
    have hsq : √(1 + y ^ 2) ^ 2 = 1 + y ^ 2 := sq_sqrt (by positivity)
    refine sqrt_le_iff.2 ⟨by positivity, ?_⟩
    nlinarith [le_abs_self (y * (x - y)), abs_mul y (x - y), sq_abs (x - y),
      mul_le_mul_of_nonneg_right hy (abs_nonneg (x - y))]
  -- `log` is `1`-Lipschitz on `[1, ∞)`
  have hlog (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) : log x - log y ≤ |x - y| := by
    rw [← log_div (by positivity) (by positivity)]
    refine (log_le_sub_one_of_pos (by positivity)).trans ?_
    rw [div_sub_one (by positivity)]
    exact (div_le_div_of_nonneg_right (le_abs_self _) (by positivity)).trans
      (div_le_self (abs_nonneg _) hy)
  set ρ := √(1 + ‖p.1‖ ^ 2)
  set ρ' := √(1 + ‖q.1‖ ^ 2)
  have hρ : 1 ≤ ρ := hone _
  have hρ' : 1 ≤ ρ' := hone _
  have hρρ' : |ρ - ρ'| ≤ dist p.1 q.1 := by
    refine (abs_sub_le_iff.2 ⟨?_, ?_⟩).trans ((abs_norm_sub_norm_le p.1 q.1).trans_eq
      (dist_eq_norm _ _).symm)
    · linarith [hsqrt ‖p.1‖ ‖q.1‖]
    · linarith [hsqrt ‖q.1‖ ‖p.1‖, abs_sub_comm ‖p.1‖ ‖q.1‖]
  have h₁ : |normalizedArsinh (p.2 / ρ) - normalizedArsinh (q.2 / ρ)| ≤ 2 * |p.2 - q.2| := by
    have := lipschitzWith_normalizedArsinh.dist_le_mul (p.2 / ρ) (q.2 / ρ)
    rw [Real.dist_eq, Real.dist_eq, ← sub_div, abs_div, abs_of_pos (zero_lt_one.trans_le hρ)]
      at this
    push_cast at this
    exact this.trans (mul_le_mul_of_nonneg_left (div_le_self (abs_nonneg _) hρ) zero_le_two)
  have h₂ : |normalizedArsinh (q.2 / ρ) - normalizedArsinh (q.2 / ρ')| ≤ |ρ - ρ'| := by
    have := abs_normalizedArsinh_mul_sub_normalizedArsinh_mul_le
      (inv_pos.2 (zero_lt_one.trans_le hρ)) (inv_pos.2 (zero_lt_one.trans_le hρ')) q.2
    rw [log_inv, log_inv, neg_sub_neg] at this
    simp only [div_eq_inv_mul]
    refine this.trans (abs_sub_le_iff.2 ⟨?_, ?_⟩)
    · linarith [hlog ρ' ρ hρ' hρ, abs_sub_comm ρ ρ']
    · linarith [hlog ρ ρ' hρ hρ']
  rw [heightCompression_apply, heightCompression_apply, Real.dist_eq, Real.dist_eq]
  calc |normalizedArsinh (p.2 / ρ) - normalizedArsinh (q.2 / ρ')|
      ≤ |normalizedArsinh (p.2 / ρ) - normalizedArsinh (q.2 / ρ)| +
          |normalizedArsinh (q.2 / ρ) - normalizedArsinh (q.2 / ρ')| := abs_sub_le _ _ _
    _ ≤ 2 * |p.2 - q.2| + dist p.1 q.1 := by linarith

/-- **Height compression of Lipschitz graphs.** If the heights of the points of `s` satisfy
`dist p.2 q.2 ≤ A * dist p.1 q.1`, then the points of `heightCompression E '' s` satisfy the same
inequality with the constant `2 * A + 1`. -/
theorem dist_snd_le_mul_dist_fst_of_mem_image_heightCompression {s : Set (E × ℝ)} {A : ℝ≥0}
    (h : ∀ p ∈ s, ∀ q ∈ s, dist p.2 q.2 ≤ A * dist p.1 q.1) :
    ∀ p ∈ heightCompression E '' s, ∀ q ∈ heightCompression E '' s,
      dist p.2 q.2 ≤ (2 * A + 1 : ℝ≥0) * dist p.1 q.1 := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
  have h₁ := dist_heightCompression_snd_le p q
  have h₂ := h p hp q hq
  simp only [heightCompression_apply] at h₁ ⊢
  push_cast
  linarith

/-- **Lipschitz control of the composite automorphism.** Let `s ⊆ E × ℝ` consist of points with
base points of norm at most `a` and heights in `D`, whose heights satisfy
`dist p.2 q.2 ≤ k * dist p.1 q.1`. If `2 * k ≤ |h t|` for `t ∈ D` and `h` is `L`-Lipschitz on `D`
with `L * a ≤ 1`, then the base scaling yields a set satisfying the inequality with the constant
`1`, and so the points of `(heightCompression E ∘ baseScaling hh) '' s` satisfy it with the
constant `3`, independently of `k`, `a` and `h`. -/
theorem dist_snd_le_three_mul_dist_fst_of_mem_image_heightCompression_comp_baseScaling
    [NormedSpace ℝ E] {h : ℝ → ℝ} (hh : ∀ t, h t ≠ 0) {s : Set (E × ℝ)} {D : Set ℝ} {a : ℝ}
    {k L : ℝ≥0} (hsa : ∀ p ∈ s, ‖p.1‖ ≤ a) (hsD : ∀ p ∈ s, p.2 ∈ D)
    (hk : ∀ p ∈ s, ∀ q ∈ s, dist p.2 q.2 ≤ k * dist p.1 q.1) (hL : LipschitzOnWith L h D)
    (hc : ∀ t ∈ D, 2 * k ≤ |h t|) (hLa : L * a ≤ 1) :
    ∀ p ∈ (heightCompression E ∘ baseScaling hh) '' s,
      ∀ q ∈ (heightCompression E ∘ baseScaling hh) '' s, dist p.2 q.2 ≤ 3 * dist p.1 q.1 := by
  have h₁ : ∀ p ∈ baseScaling hh '' s, ∀ q ∈ baseScaling hh '' s,
      dist p.2 q.2 ≤ (1 : ℝ≥0) * dist p.1 q.1 := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    have key := mul_dist_fst_le_dist_baseScaling_fst (hh := hh) (hsa q hq)
      ((hc _ (hsD p hp)).trans_eq (norm_eq_abs _).symm)
      (hL.dist_le_mul p.2 (hsD p hp) q.2 (hsD q hq)) (hk p hp q hq)
    have hLak : (L : ℝ) * a * k ≤ k := by
      simpa using mul_le_mul_of_nonneg_right hLa k.2
    have hkd : (k : ℝ) * dist p.1 q.1 ≤ (2 * k - L * a * k) * dist p.1 q.1 :=
      mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
    have := hk p hp q hq
    rw [baseScaling_apply, baseScaling_apply] at key ⊢
    rw [NNReal.coe_one, one_mul]
    linarith
  rw [image_comp]
  intro p hp q hq
  have := dist_snd_le_mul_dist_fst_of_mem_image_heightCompression h₁ p hp q hq
  norm_num at this
  exact this

/-- **Bounded pieces have bounded images.** Let `s ⊆ E × ℝ` consist of points with base points of
norm at most `a` and heights in a compact set `D`, on which `h` is continuous. Then the image of
`s` under the base scaling followed by the height compression is bounded. -/
theorem isBounded_image_heightCompression_comp_baseScaling [NormedSpace ℝ E] {h : ℝ → ℝ}
    (hh : ∀ t, h t ≠ 0) {s : Set (E × ℝ)} {D : Set ℝ} {a : ℝ} (hsa : ∀ p ∈ s, ‖p.1‖ ≤ a)
    (hsD : ∀ p ∈ s, p.2 ∈ D) (hD : IsCompact D) (hhD : ContinuousOn h D) :
    Bornology.IsBounded ((heightCompression E ∘ baseScaling hh) '' s) := by
  obtain ⟨C, hC⟩ := hD.exists_bound_of_continuousOn hhD
  obtain ⟨T, hT⟩ := hD.isBounded.exists_norm_le
  refine isBounded_iff_forall_norm_le.2 ⟨max (C * a) (2 * T), ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  have hρ : 1 ≤ √(1 + ‖h p.2 • p.1‖ ^ 2) := one_le_sqrt.2 (le_add_of_nonneg_right (sq_nonneg _))
  -- `β` is `2`-Lipschitz and vanishes at `0`, and the height is divided by `√(1 + ‖u‖²) ≥ 1`.
  have hβ := lipschitzWith_normalizedArsinh.dist_le_mul (p.2 / √(1 + ‖h p.2 • p.1‖ ^ 2)) 0
  rw [normalizedArsinh_zero, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero, abs_div,
    abs_of_pos (zero_lt_one.trans_le hρ)] at hβ
  rw [Function.comp_apply, baseScaling_apply, heightCompression_apply, Prod.norm_def]
  refine max_le_max ?_ ?_
  · rw [norm_smul]
    exact mul_le_mul (hC _ (hsD p hp)) (hsa p hp) (norm_nonneg _)
      ((norm_nonneg _).trans (hC _ (hsD p hp)))
  · rw [Real.norm_eq_abs]
    refine hβ.trans ?_
    push_cast
    gcongr
    exact (div_le_self (abs_nonneg _) hρ).trans
      ((Real.norm_eq_abs _).symm.trans_le (hT _ (hsD p hp)))

variable [InnerProductSpace ℝ E]

/-- On a real inner product space, the height compression is `C^n` for every `n`, including
`n = ω`. -/
@[fun_prop]
theorem contDiff_heightCompression {n : WithTop ℕ∞} : ContDiff ℝ n (heightCompression E) := by
  rw [funext heightCompression_apply]
  have hpos (p : E × ℝ) : 0 < √(1 + ‖p.1‖ ^ 2) := sqrt_pos.2 (by positivity)
  have : ContDiff ℝ n fun p : E × ℝ ↦ √(1 + ‖p.1‖ ^ 2) :=
    (contDiff_const.add ((contDiff_norm_sq ℝ).comp contDiff_fst)).sqrt fun p ↦
      (by positivity : (0 : ℝ) < 1 + ‖p.1‖ ^ 2).ne'
  exact contDiff_fst.prodMk (contDiff_normalizedArsinh.comp
    (contDiff_snd.div this fun p ↦ (hpos p).ne'))

/-- On a real inner product space, the inverse of the height compression is `C^n` for every `n`,
including `n = ω`. -/
@[fun_prop]
theorem contDiff_heightCompression_symm {n : WithTop ℕ∞} :
    ContDiff ℝ n (heightCompression E).symm := by
  rw [funext heightCompression_symm_apply]
  have : ContDiff ℝ n fun p : E × ℝ ↦ √(1 + ‖p.1‖ ^ 2) :=
    (contDiff_const.add ((contDiff_norm_sq ℝ).comp contDiff_fst)).sqrt fun p ↦
      (by positivity : (0 : ℝ) < 1 + ‖p.1‖ ^ 2).ne'
  exact contDiff_fst.prodMk (this.mul (by fun_prop))

/-- On a real inner product space, the height compression is analytic at every point. -/
@[fun_prop]
theorem analyticAt_heightCompression (p : E × ℝ) : AnalyticAt ℝ (heightCompression E) p :=
  contDiff_heightCompression.contDiffAt.analyticAt

/-- On a real inner product space, the inverse of the height compression is analytic at every
point. -/
@[fun_prop]
theorem analyticAt_heightCompression_symm (p : E × ℝ) :
    AnalyticAt ℝ (heightCompression E).symm p :=
  contDiff_heightCompression_symm.contDiffAt.analyticAt

end heightCompression

/-! ### Choosing the scaling function -/

section scalingFunction

open Filter Topology Function

/-- **The scaling function of the straightening.** Let `Δ i` be pairwise disjoint compact intervals
forming a locally finite family, and let `γ : ℝ → ℝ` be locally bounded below by positive
constants. For any constants `M i` and positive Lipschitz constants `L i` there is a positive real
analytic `h` with `√(t² - 1) < h t * γ t` for every `t` and, on each `Δ i`, `M i < h` and `h`
`L i`-Lipschitz.

These are the requirements on `h` of `TauCeti.mapsTo_heightCompression_comp_baseScaling` and
of the Lipschitz estimates for `TauCeti.baseScaling`, in Łojasiewicz's choice of `h` with
`h(t) > γ(t)⁻¹ √(t² - 1)`, `h > 2 kν` and `|h'| < aν⁻¹` on `Δν`. -/
theorem exists_analyticOnNhd_sqrt_sq_sub_one_lt_mul {ι : Type*} {Δ : ι → Set ℝ}
    (hΔ : ∀ i, IsCompact (Δ i)) (hΔc : ∀ i, Convex ℝ (Δ i)) (hdisj : Pairwise (Disjoint on Δ))
    (hlf : LocallyFinite Δ) {γ : ℝ → ℝ} (hγ : ∀ x, ∃ c > 0, ∀ᶠ y in 𝓝 x, c ≤ γ y) (M : ι → ℝ)
    {L : ι → ℝ≥0} (hL : ∀ i, 0 < L i) :
    ∃ h : ℝ → ℝ, AnalyticOnNhd ℝ h univ ∧ (∀ t, 0 < h t) ∧ (∀ t, √(t ^ 2 - 1) < h t * γ t) ∧
      ∀ i, (∀ t ∈ Δ i, M i < h t) ∧ LipschitzOnWith (L i) h (Δ i) := by
  have hγ0 (t : ℝ) : 0 < γ t := by
    obtain ⟨c, hc, hcγ⟩ := hγ t
    exact hc.trans_le hcγ.self_of_nhds
  -- The required lower bound `max 0 (√(t² - 1) / γ t)` is locally bounded above.
  have hbd (x : ℝ) : ∃ C, ∀ᶠ y in 𝓝 x, max 0 (√(y ^ 2 - 1) / γ y) ≤ C := by
    obtain ⟨c, hc, hcγ⟩ := hγ x
    refine ⟨(|x| + 1) / c, ?_⟩
    filter_upwards [hcγ, continuous_abs.continuousAt.eventually_lt continuousAt_const
      (lt_add_one |x|)] with y hy hyx
    have hs : √(y ^ 2 - 1) ≤ |x| + 1 :=
      (sqrt_le_sqrt (by linarith)).trans ((sqrt_sq_eq_abs y).trans_le hyx.le)
    refine max_le (by positivity) ?_
    exact div_le_div₀ (by positivity) hs hc hy
  obtain ⟨h, hha, hh, hΔh⟩ := exists_analyticOnNhd_lt_and_abs_deriv_lt hΔ hdisj hlf hbd M
    (ε := fun i ↦ L i) hL
  have hpos (t : ℝ) : 0 < h t := (le_max_left _ _).trans_lt (hh t)
  refine ⟨h, hha, hpos, fun t ↦ ?_, fun i ↦ ⟨fun t ht ↦ (hΔh i t ht).1, ?_⟩⟩
  · exact (div_lt_iff₀ (hγ0 t)).1 ((le_max_right _ _).trans_lt (hh t))
  · refine (hΔc i).lipschitzOnWith_of_nnnorm_deriv_le
      (fun t _ ↦ (hha t (mem_univ t)).differentiableAt) fun t ht ↦ ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs]
    exact (hΔh i t ht).2.le

end scalingFunction

end TauCeti
