/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import TauCeti.Geometry.Manifold.Immersion.Differential
public import TauCeti.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Basic
public import TauCeti.Topology.Circle.Arc
public import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# Straightening a circle embedding near a point

A smooth embedding `K : S¹ → M` of the circle into a boundaryless manifold `M` modelled on a
finite-dimensional real normed space, and a smooth map `L : S¹ → M`, which agree to first order at a
point `z₀` (same value and same derivative there), can be made to agree on a neighbourhood of
`z₀`: `K` is smoothly isotopic to an embedding which coincides with `L` near `z₀`, by an isotopy
which is stationary off any prescribed neighbourhood of `z₀`
(`TauCeti.SmoothEmbedding.exists_smoothIsotopy_eventuallyEq_of_mfderiv_eq`).

For knots this is how a knot is made standard near a point. The connected sum of knots in a sphere
is defined for knots which agree with a fixed great circle near a point; a knot passing through a
point of that great circle with the same derivative there is isotopic, hence concordant, to such a
knot.

The isotopy is a splice in a chart. Reading `K` and `L` along the arc `z₀ exp (t i)`, `|t|` small,
in a chart at `K z₀` gives two curves `k` and `l` in the model space with `k 0 = l 0` and
`k' 0 = l' 0 = v ≠ 0`. With a smooth cutoff `χ` which is `1` on `[-1, 1]` and vanishes off
`(-2, 2)`, the curves `k + s χ (t / δ) (l - k)` for `s ∈ [0, 1]` run from `k` to a curve which is
`l` on `[-δ, δ]`, and all of them are `k` off `(-2δ, 2δ)`. Since `l - k` vanishes to first order at
`0`, the term coming from the derivative of the cutoff has size `δ⁻¹ · o(δ)`, so on a fixed
interval `[-ρ, ρ]` all these curves have velocity close to `v`, uniformly in `δ` and `s`. A linear
functional normalizing `v` is then strictly increasing along each of them, which makes them
injective immersions. A small scale `δ` keeps the modified stretch in a small ball avoiding the
rest of `K`, and read back through the chart the spliced curves form a smooth isotopy through
embeddings.

## Main results

* `TauCeti.SmoothEmbedding.exists_smoothIsotopy_eventuallyEq_of_mfderiv_eq`: a circle embedding
  is smoothly isotopic, by an isotopy supported near `z₀`, to one agreeing near `z₀` with any
  smooth circle tangent to it at `z₀`.
-/

public section

noncomputable section

open Set Filter Topology Function Manifold
open scoped Manifold ContDiff

namespace TauCeti

/-! ### Splicing two curves with a cutoff -/

section Splice

/-- A fixed smooth cutoff on the line: it is `1` on `[-1, 1]`, vanishes off `(-2, 2)`, and takes
values in `[0, 1]`. -/
private def cutoff : ℝ → ℝ :=
  (⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump (0 : ℝ))

private theorem cutoff_eq_one {x : ℝ} (hx : |x| ≤ 1) : cutoff x = 1 :=
  ContDiffBump.one_of_mem_closedBall _ (by simpa [Real.dist_eq] using hx)

private theorem cutoff_eq_zero {x : ℝ} (hx : 2 ≤ |x|) : cutoff x = 0 :=
  ContDiffBump.zero_of_le_dist _ (by simpa [Real.dist_eq] using hx)

private theorem cutoff_nonneg (x : ℝ) : 0 ≤ cutoff x := ContDiffBump.nonneg _

private theorem cutoff_le_one (x : ℝ) : cutoff x ≤ 1 := ContDiffBump.le_one _

private theorem contDiff_cutoff : ContDiff ℝ ∞ cutoff := ContDiffBump.contDiff _

private theorem deriv_cutoff_eq_zero {x : ℝ} (hx : 2 < |x|) : deriv cutoff x = 0 := by
  have h : cutoff =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hx] with y hy
    exact cutoff_eq_zero (le_of_lt hy)
  rw [h.deriv_eq, deriv_const]

private theorem exists_abs_deriv_cutoff_le : ∃ B, ∀ x, |deriv cutoff x| ≤ B :=
  ((contDiff_cutoff.continuous_deriv (by simp)).bounded_above_of_compact_support
    (ContDiffBump.hasCompactSupport _).deriv)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The curve `k` with its stretch over `[-δ, δ]` replaced by the curve `l`: the convex combination
of `k t` and `l t` with weight `s` times the cutoff at scale `δ`. For `s = 1` it is `l` on
`[-δ, δ]`, and for every `s` it is `k` off `(-2δ, 2δ)`. -/
private def splice (k l : ℝ → E) (δ s t : ℝ) : E :=
  k t + (s * cutoff (δ⁻¹ * t)) • (l t - k t)

private theorem weight_le_one {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (x : ℝ) : s * cutoff x ≤ 1 :=
  (mul_le_mul hs.2 (cutoff_le_one x) (cutoff_nonneg x) zero_le_one).trans_eq (one_mul 1)

private theorem splice_zero (k l : ℝ → E) (δ t : ℝ) : splice k l δ 0 t = k t := by
  simp [splice]

private theorem splice_of_le_abs {k l : ℝ → E} {δ : ℝ} (hδ : 0 < δ) (s : ℝ) {t : ℝ}
    (ht : 2 * δ ≤ |t|) : splice k l δ s t = k t := by
  rw [splice, cutoff_eq_zero, mul_zero, zero_smul, add_zero]
  rwa [abs_mul, abs_inv, abs_of_pos hδ, le_inv_mul_iff₀ hδ, mul_comm]

private theorem splice_one_of_abs_le {k l : ℝ → E} {δ : ℝ} (hδ : 0 < δ) {t : ℝ}
    (ht : |t| ≤ δ) : splice k l δ 1 t = l t := by
  rw [splice, cutoff_eq_one, one_mul, one_smul, add_sub_cancel]
  rwa [abs_mul, abs_inv, abs_of_pos hδ, inv_mul_le_iff₀ hδ, mul_one]

/-- For `s ∈ [0, 1]` the spliced curve is a convex combination of the two curves, so it stays in
any convex set containing both. -/
private theorem splice_mem {k l : ℝ → E} {S : Set E} (hS : Convex ℝ S) (δ : ℝ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) {t : ℝ} (hk : k t ∈ S) (hl : l t ∈ S) : splice k l δ s t ∈ S := by
  have h0 : 0 ≤ s * cutoff (δ⁻¹ * t) := mul_nonneg hs.1 (cutoff_nonneg _)
  have h1 : s * cutoff (δ⁻¹ * t) ≤ 1 := weight_le_one hs _
  have := hS.add_smul_sub_mem hk hl ⟨h0, h1⟩
  simpa [splice] using this

private theorem contDiffOn_splice {k l : ℝ → E} {T : Set ℝ}
    (hk : ContDiffOn ℝ ∞ k T) (hl : ContDiffOn ℝ ∞ l T) (δ : ℝ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => splice k l δ p.1 p.2) (univ ×ˢ T) := by
  have hk' := hk.comp contDiffOn_snd fun (p : ℝ × ℝ) (hp : p ∈ univ ×ˢ T) => hp.2
  have hl' := hl.comp contDiffOn_snd fun (p : ℝ × ℝ) (hp : p ∈ univ ×ˢ T) => hp.2
  have hc : ContDiff ℝ ∞ fun p : ℝ × ℝ => p.1 * cutoff (δ⁻¹ * p.2) :=
    contDiff_fst.mul (contDiff_cutoff.comp (contDiff_const.mul contDiff_snd))
  exact hk'.add (hc.contDiffOn.smul (hl'.sub hk'))

private theorem hasDerivAt_splice {k l : ℝ → E} {δ s t : ℝ} {k' l' : E} (hk : HasDerivAt k k' t)
    (hl : HasDerivAt l l' t) :
    HasDerivAt (splice k l δ s)
      (k' + ((s * cutoff (δ⁻¹ * t)) • (l' - k') +
        (s * (δ⁻¹ * deriv cutoff (δ⁻¹ * t))) • (l t - k t))) t := by
  have hc : HasDerivAt (fun t => s * cutoff (δ⁻¹ * t)) (s * (δ⁻¹ * deriv cutoff (δ⁻¹ * t))) t :=
    ((((contDiff_cutoff.differentiable (by simp)) _).hasDerivAt.comp t
      ((hasDerivAt_id t).const_mul δ⁻¹ |>.congr_deriv (mul_one _))).const_mul s).congr_deriv
      (by simp only [id]; ring)
  exact hk.add (hc.smul (hl.sub hk))

/-- **The velocity of a spliced curve.** If the velocities `k'` and `l'` of `k` and `l` at `t` are
within `ε` of `v`, `‖l t - k t‖ ≤ 2 ε |t|`, and `B` bounds the derivative of the cutoff, then at
every scale `δ > 0` and weight `s ∈ [0, 1]` the spliced curve has velocity within `(3 + 4 B) ε` of
`v` at `t`. -/
private theorem norm_deriv_splice_sub_le {k l : ℝ → E} {k' l' v : E} {δ s t ε B : ℝ} (hδ : 0 < δ)
    (hs : s ∈ Icc (0 : ℝ) 1) (hB : ∀ x, |deriv cutoff x| ≤ B) (hk : HasDerivAt k k' t)
    (hl : HasDerivAt l l' t) (hk' : ‖k' - v‖ ≤ ε) (hl' : ‖l' - v‖ ≤ ε)
    (hlk : ‖l t - k t‖ ≤ 2 * ε * |t|) :
    ‖deriv (splice k l δ s) t - v‖ ≤ (3 + 4 * B) * ε := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans hk'
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  -- The term from the derivative of the cutoff vanishes unless `|t| ≤ 2δ`, where `l t - k t` is
  -- at most `4 ε δ`; so it is at most `4 B ε`.
  have hcorr : ‖(s * (δ⁻¹ * deriv cutoff (δ⁻¹ * t))) • (l t - k t)‖ ≤ 4 * B * ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hs.1, abs_inv,
      abs_of_pos hδ]
    by_cases h2 : 2 < |δ⁻¹ * t|
    · rw [deriv_cutoff_eq_zero h2, abs_zero, mul_zero, mul_zero, zero_mul]; positivity
    · rw [not_lt, abs_mul, abs_inv, abs_of_pos hδ, inv_mul_le_iff₀ hδ] at h2
      calc s * (δ⁻¹ * |deriv cutoff (δ⁻¹ * t)|) * ‖l t - k t‖
          ≤ 1 * (δ⁻¹ * B) * (2 * ε * |t|) := by
            gcongr
            · exact hs.2
            · exact hB _
        _ ≤ 1 * (δ⁻¹ * B) * (2 * ε * (δ * 2)) := by gcongr
        _ = 4 * B * ε := by field_simp; ring
  have hmid : ‖(s * cutoff (δ⁻¹ * t)) • (l' - k')‖ ≤ 2 * ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hs.1 (cutoff_nonneg _))]
    calc s * cutoff (δ⁻¹ * t) * ‖l' - k'‖ ≤ 1 * (ε + ε) := by
          gcongr
          · exact weight_le_one hs _
          · exact (norm_sub_le_norm_sub_add_norm_sub l' v k').trans
              (by rw [norm_sub_rev v]; linarith)
      _ = 2 * ε := by ring
  rw [(hasDerivAt_splice hk hl).deriv]
  calc _ = ‖(k' - v) + ((s * cutoff (δ⁻¹ * t)) • (l' - k') +
          (s * (δ⁻¹ * deriv cutoff (δ⁻¹ * t))) • (l t - k t))‖ := by
        congr 1; abel
    _ ≤ ‖k' - v‖ + (‖(s * cutoff (δ⁻¹ * t)) • (l' - k')‖ +
          ‖(s * (δ⁻¹ * deriv cutoff (δ⁻¹ * t))) • (l t - k t)‖) :=
        (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ ε + (2 * ε + 4 * B * ε) := by gcongr
    _ = (3 + 4 * B) * ε := by ring

/-- **The spliced curves are uniformly regular.** If `k` and `l` are `C¹` near `0`, agree at `0`
and have the same nonzero velocity `v` there, then on a fixed interval `[-ρ, ρ]` the velocity of
every spliced curve, at every scale `δ` and weight `s ∈ [0, 1]`, has positive pairing with a fixed
functional `ℓ` normalizing `v`. The key estimate is that `l - k` vanishes to first order at `0`, so
the derivative `δ⁻¹ χ' (δ⁻¹ t)` of the cutoff, which is supported where `|t| ≤ 2δ`, only meets
`l t - k t = o(t)`. -/
private theorem exists_pos_deriv_splice {k l : ℝ → E} {r : ℝ} (hr : 0 < r)
    (hk : ContDiffOn ℝ 1 k (Ioo (-r) r)) (hl : ContDiffOn ℝ 1 l (Ioo (-r) r))
    (h0 : k 0 = l 0) (hd : deriv k 0 = deriv l 0) (hv : deriv k 0 ≠ 0) :
    ∃ ℓ : StrongDual ℝ E, ∃ ρ, 0 < ρ ∧ ρ < r ∧ ∀ δ, 0 < δ → ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ t ∈ Icc (-ρ) ρ, DifferentiableAt ℝ (splice k l δ s) t ∧
        0 < ℓ (deriv (splice k l δ s) t) := by
  set v := deriv k 0
  obtain ⟨ℓ, hℓ, hℓv⟩ := exists_dual_vector ℝ v (norm_ne_zero_iff.2 hv)
  replace hℓv : ℓ v = ‖v‖ := by simpa using hℓv
  obtain ⟨B, hB⟩ := exists_abs_deriv_cutoff_le
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hv0 : 0 < ‖v‖ := norm_pos_iff.2 hv
  set ε := ‖v‖ / (4 * B + 4) with hε
  have hε0 : 0 < ε := div_pos hv0 (by positivity)
  have hεv : (3 + 4 * B) * ε < ‖v‖ := by
    rw [hε, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  have hI : IsOpen (Ioo (-r) r) := isOpen_Ioo
  have h0I : (0 : ℝ) ∈ Ioo (-r) r := ⟨neg_lt_zero.2 hr, hr⟩
  -- The velocities of `k` and `l` stay within `ε` of `v` on a small interval about `0`.
  have hcont (f : ℝ → E) (hf : ContDiffOn ℝ 1 f (Ioo (-r) r)) (hf0 : deriv f 0 = v) :
      ∃ ρ > 0, ∀ t, |t| < ρ → ‖deriv f t - v‖ < ε := by
    have := ((hf.continuousOn_deriv_of_isOpen hI le_rfl).continuousAt (hI.mem_nhds h0I))
    obtain ⟨ρ, hρ, h⟩ := Metric.continuousAt_iff.1 this ε hε0
    exact ⟨ρ, hρ, fun t ht => by
      simpa [dist_eq_norm, hf0] using h (by simpa [Real.dist_eq] using ht)⟩
  obtain ⟨ρ₁, hρ₁, hk₁⟩ := hcont k hk rfl
  obtain ⟨ρ₂, hρ₂, hl₁⟩ := hcont l hl hd.symm
  set ρ := min (min ρ₁ ρ₂) r / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρr : ρ < r := by
    rw [hρ]; linarith [min_le_right (min ρ₁ ρ₂) r]
  have hlt (t : ℝ) (ht : t ∈ Icc (-ρ) ρ) : |t| < ρ₁ ∧ |t| < ρ₂ ∧ t ∈ Ioo (-r) r := by
    have ht' : |t| < min (min ρ₁ ρ₂) r := (abs_le.2 ht).trans_lt (by rw [hρ]; linarith)
    refine ⟨ht'.trans_le ((min_le_left _ _).trans (min_le_left _ _)),
      ht'.trans_le ((min_le_left _ _).trans (min_le_right _ _)), ?_⟩
    exact ⟨neg_lt_of_abs_lt (ht'.trans_le (min_le_right _ _)),
      lt_of_abs_lt (ht'.trans_le (min_le_right _ _))⟩
  have hdk (t : ℝ) (ht : t ∈ Ioo (-r) r) : DifferentiableAt ℝ k t :=
    (hk.contDiffAt (hI.mem_nhds ht)).differentiableAt one_ne_zero
  have hdl (t : ℝ) (ht : t ∈ Ioo (-r) r) : DifferentiableAt ℝ l t :=
    (hl.contDiffAt (hI.mem_nhds ht)).differentiableAt one_ne_zero
  -- Mean value estimate: `l - k` vanishes to first order at `0`.
  have hlk (t : ℝ) (ht : t ∈ Icc (-ρ) ρ) : ‖l t - k t‖ ≤ 2 * ε * |t| := by
    have h := (convex_Icc (-ρ) ρ).norm_image_sub_le_of_norm_deriv_le (f := fun t => l t - k t)
      (C := 2 * ε) (fun x hx => (hdl x (hlt x hx).2.2).sub (hdk x (hlt x hx).2.2))
      (fun x hx => by
        rw [deriv_fun_sub (hdl x (hlt x hx).2.2) (hdk x (hlt x hx).2.2)]
        refine (norm_sub_le_norm_sub_add_norm_sub _ v _).trans ?_
        rw [norm_sub_rev v]
        linarith [hk₁ x (hlt x hx).1, hl₁ x (hlt x hx).2.1])
      ⟨neg_nonpos.2 hρ0.le, hρ0.le⟩ ht
    simpa [h0, Real.norm_eq_abs] using h
  refine ⟨ℓ, ρ, hρ0, hρr, fun δ hδ s hs t ht => ?_⟩
  obtain ⟨htk, htl, htI⟩ := hlt t ht
  have hk' := (hdk t htI).hasDerivAt
  have hl' := (hdl t htI).hasDerivAt
  refine ⟨(hasDerivAt_splice (δ := δ) (s := s) hk' hl').differentiableAt, ?_⟩
  have hDv := norm_deriv_splice_sub_le hδ hs hB hk' hl' (hk₁ t htk).le (hl₁ t htl).le (hlk t ht)
  set D := deriv (splice k l δ s) t
  -- `ℓ D ≥ ‖v‖ - ‖D - v‖ > 0`.
  have hℓD : |ℓ (D - v)| ≤ ‖D - v‖ := by
    simpa [hℓ] using ℓ.le_opNorm (D - v)
  have : ℓ D = ‖v‖ + ℓ (D - v) := by rw [map_sub, hℓv]; ring
  rw [this]
  linarith [neg_abs_le (ℓ (D - v))]

end Splice

/-! ### Splicing a circle embedding in a chart -/

section Motion

open Complex (arg)

attribute [local instance] finrank_real_complex_fact'

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- The circle map which is `K` off the arc `|arg z| < ρ`, and on that arc is a curve `g` read
through the inverse of a chart `φ`. -/
private def spliceMap (K : Circle → M) (φ : OpenPartialHomeomorph M E) (ρ : ℝ) (g : ℝ → E)
    (z : Circle) : M :=
  if |arg z| < ρ then φ.symm (g (arg z)) else K z

variable {K : SmoothEmbedding (𝓡 1) 𝓘(ℝ, E) ∞ Circle M} {φ : OpenPartialHomeomorph M E}
  {a ρ r : ℝ} {g : ℝ → E}

private theorem spliceMap_of_abs_lt {z : Circle} (hz : |arg z| < ρ) :
    spliceMap K φ ρ g z = φ.symm (g (arg z)) := by
  simp [spliceMap, hz]

/-- Where `g` is `K` read in the chart, the spliced map is `K`. -/
private theorem spliceMap_of_le_abs (hgK : ∀ t, a ≤ |t| → |t| < r → g t = φ (K (Circle.exp t)))
    (hKφ : ∀ t, |t| < r → K (Circle.exp t) ∈ φ.source) (hρr : ρ ≤ r) {z : Circle}
    (hz : a ≤ |arg z|) : spliceMap K φ ρ g z = K z := by
  unfold spliceMap
  split_ifs with h
  · rw [hgK _ hz (h.trans_le hρr), φ.left_inv (hKφ _ (h.trans_le hρr)), Circle.exp_arg]
  · rfl

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- **The spliced maps form a smooth motion.** A family of curves `G s`, jointly smooth in `s` and
`t`, landing in the chart target on `(-ρ, ρ)` and equal to `K` read in the chart where `a ≤ |t|`,
splices into a motion of the circle which is smooth in time and space. -/
private theorem contMDiff_spliceMap {G : ℝ → ℝ → E}
    (hG : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => G p.1 p.2) (univ ×ˢ Ioo (-r) r))
    (hGφ : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t, |t| < ρ → G s t ∈ φ.target)
    (hGK : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t, a ≤ |t| → |t| < r → G s t = φ (K (Circle.exp t)))
    (hKφ : ∀ t, |t| < r → K (Circle.exp t) ∈ φ.source) (haρ : a < ρ) (hρr : ρ ≤ r)
    (hrπ : r ≤ Real.pi) (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) :
    ContMDiff ((𝓡∂ 1).prod (𝓡 1)) 𝓘(ℝ, E) ∞
      (fun q : unitInterval × Circle => spliceMap K φ ρ (G q.1) q.2) := by
  intro q
  by_cases hq : |arg q.2| < ρ
  · -- Near `q` the motion is `φ.symm (G s (arg z))`.
    have hev : (fun q : unitInterval × Circle => spliceMap K φ ρ (G q.1) q.2) =ᶠ[𝓝 q]
        fun q => φ.symm (G q.1 (arg q.2)) := by
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
        ((Circle.isOpen_centeredArc ρ).mem_nhds ((Circle.mem_centeredArc (hρr.trans hrπ)).2 hq))]
        with q' hq'
      exact spliceMap_of_abs_lt ((Circle.mem_centeredArc (hρr.trans hrπ)).1 hq')
    refine ContMDiffAt.congr_of_eventuallyEq ?_ hev
    have hin : ContMDiffAt ((𝓡∂ 1).prod (𝓡 1)) 𝓘(ℝ, ℝ × ℝ) ∞
        (fun q : unitInterval × Circle => ((q.1 : ℝ), arg q.2)) q :=
      (contMDiff_subtypeVal_Icc.comp contMDiff_fst).contMDiffAt.prodMk_space
        ((contMDiffAt_circle_arg ((hq.trans_le hρr).trans_le hrπ)).comp q contMDiffAt_snd)
    have hlt := hq.trans_le hρr
    have hGq : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => G p.1 p.2) ((q.1 : ℝ), arg q.2) :=
      hG.contDiffAt (prod_mem_nhds univ_mem
        (isOpen_Ioo.mem_nhds ⟨neg_lt_of_abs_lt hlt, lt_of_abs_lt hlt⟩))
    exact (contMDiffAt_symm_of_mem_maximalAtlas hφ (hGφ _ q.1.2 _ hq)).comp q
      (hGq.contMDiffAt.comp q hin)
  · -- Near `q` the motion is `K`.
    have hqO : q.2 ∈ (Circle.exp '' Icc (-a) a)ᶜ := fun h =>
      hq ((mem_circleExp_image_Icc_neg_iff.1 h).trans_lt haρ)
    have hev : (fun q : unitInterval × Circle => spliceMap K φ ρ (G q.1) q.2) =ᶠ[𝓝 q]
        fun q => K q.2 := by
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
        ((isClosed_circleExp_image_Icc (-a) a).isOpen_compl.mem_nhds hqO)] with q' hq'
      exact spliceMap_of_le_abs (hGK _ q'.1.2) hKφ hρr
        (not_le.1 (mt mem_circleExp_image_Icc_neg_iff.2 hq')).le
    exact (K.contMDiff.comp contMDiff_snd).contMDiffAt.congr_of_eventuallyEq hev

/-- **The spliced map is a smooth embedding**, provided the curve `g` is regular and injective on
`(-ρ, ρ)`, and its stretch over `(-a, a)` avoids the image of the rest of the circle under `K`. -/
private theorem isSmoothEmbedding_spliceMap [T2Space M]
    (hsmooth : ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ (spliceMap K φ ρ g))
    (hgC : ContDiffOn ℝ ∞ g (Ioo (-r) r)) (hgφ : ∀ t, |t| < ρ → g t ∈ φ.target)
    (hgK : ∀ t, a ≤ |t| → |t| < r → g t = φ (K (Circle.exp t)))
    (hKφ : ∀ t, |t| < r → K (Circle.exp t) ∈ φ.source) (hinj : InjOn g (Ioo (-ρ) ρ))
    (hderiv : ∀ t, |t| < ρ → deriv g t ≠ 0)
    (hfar : ∀ t, |t| < a → φ.symm (g t) ∉ K '' (Circle.centeredArc ρ)ᶜ)
    (haρ : a < ρ) (hρr : ρ ≤ r) (hrπ : r ≤ Real.pi)
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) :
    IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, E) ∞ (spliceMap K φ ρ g) := by
  have hρπ := hρr.trans hrπ
  -- Two points of the arc `|arg z| < ρ` with the same image are equal.
  have hinner {z w : Circle} (hz : |arg z| < ρ) (hw : |arg w| < ρ)
      (hzw : spliceMap K φ ρ g z = spliceMap K φ ρ g w) : z = w := by
    rw [spliceMap_of_abs_lt hz, spliceMap_of_abs_lt hw] at hzw
    have := hinj ⟨neg_lt_of_abs_lt hz, lt_of_abs_lt hz⟩ ⟨neg_lt_of_abs_lt hw, lt_of_abs_lt hw⟩
      (φ.symm.injOn (hgφ _ hz) (hgφ _ hw) hzw)
    exact Circle.injective_arg this
  -- A point of the arc and a point off it have different images.
  have hmixed {z w : Circle} (hz : |arg z| < ρ) (hw : ρ ≤ |arg w|)
      (hzw : spliceMap K φ ρ g z = spliceMap K φ ρ g w) : z = w := by
    rw [spliceMap_of_le_abs hgK hKφ hρr (haρ.le.trans hw)] at hzw
    by_cases hza : |arg z| < a
    · refine absurd ⟨w, fun h => ?_, hzw.symm⟩ (spliceMap_of_abs_lt (g := g) (K := K) (φ := φ) hz
        ▸ hfar _ hza)
      exact not_lt.2 hw ((Circle.mem_centeredArc hρπ).1 h)
    · rw [spliceMap_of_le_abs hgK hKφ hρr (not_lt.1 hza)] at hzw
      exact K.isEmbedding.injective hzw
  have hinj' : Injective (spliceMap K φ ρ g) := by
    intro z w hzw
    by_cases hz : |arg z| < ρ <;> by_cases hw : |arg w| < ρ
    · exact hinner hz hw hzw
    · exact hmixed hz (not_lt.1 hw) hzw
    · exact (hmixed hw (not_lt.1 hz) hzw.symm).symm
    · rw [spliceMap_of_le_abs hgK hKφ hρr (haρ.le.trans (not_lt.1 hz)),
        spliceMap_of_le_abs hgK hKφ hρr (haρ.le.trans (not_lt.1 hw))] at hzw
      exact K.isEmbedding.injective hzw
  refine ⟨isImmersion_iff_forall_isImmersionAt.2 fun z => ?_,
    (hsmooth.continuous.isClosedEmbedding hinj').isEmbedding⟩
  by_cases hz : |arg z| < ρ
  · -- On the arc the map is `φ.symm ∘ g ∘ arg`, and `g` has nonzero velocity.
    set h : Circle → E := fun w => g (arg w)
    have hev : spliceMap K φ ρ g =ᶠ[𝓝 z] φ.symm ∘ h := by
      filter_upwards [(Circle.isOpen_centeredArc ρ).mem_nhds ((Circle.mem_centeredArc hρπ).2 hz)]
        with w hw
      exact spliceMap_of_abs_lt ((Circle.mem_centeredArc hρπ).1 hw)
    have hlt := hz.trans_le hρr
    have hgz : ContDiffAt ℝ ∞ g (arg z) :=
      hgC.contDiffAt (isOpen_Ioo.mem_nhds ⟨neg_lt_of_abs_lt hlt, lt_of_abs_lt hlt⟩)
    have hh : MDifferentiableAt (𝓡 1) 𝓘(ℝ, E) h (Circle.exp (arg z)) := by
      rw [Circle.exp_arg]
      exact (hgz.contMDiffAt.comp z (contMDiffAt_circle_arg (hlt.trans_le hrπ))).mdifferentiableAt
        (by simp)
    have hlift : h ∘ Circle.exp =ᶠ[𝓝 (arg z)] g := by
      have hπ : |arg z| < Real.pi := hlt.trans_le hrπ
      filter_upwards [isOpen_Ioo.mem_nhds ⟨neg_lt_of_abs_lt hπ, lt_of_abs_lt hπ⟩] with t ht
      simp only [h, Function.comp_apply, Circle.arg_exp ht.1 ht.2.le]
    have hdh : Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) h z) := by
      have := injective_mfderiv_of_deriv_comp_circleExp_ne_zero hh
        (by rw [hlift.deriv_eq]; exact hderiv _ hz)
      rwa [Circle.exp_arg] at this
    have hsymm : IsDiffImmersionAt 𝓘(ℝ, E) 𝓘(ℝ, E) φ.symm (h z) :=
      (φ.isLocalDiffeomorphAt_symm_of_mem_maximalAtlas hφ (hgφ _ hz)).isDiffImmersionAt (by simp)
    have himm : IsDiffImmersionAt (𝓡 1) 𝓘(ℝ, E) (spliceMap K φ ρ g) z :=
      (hsymm.comp (IsDiffImmersionAt.of_injective_of_finiteDimensional hdh)).congr hev
    exact ((hsmooth.contMDiffOn (s := univ)).isImmersionAt_iff_hasLeftInverse_mfderiv isOpen_univ
      (mem_univ z) (by simp)).2 (isDiffImmersionAt_iff.1 himm)
  · -- Off the arc the map is `K`.
    have hzO : z ∈ (Circle.exp '' Icc (-a) a)ᶜ := fun h =>
      hz ((mem_circleExp_image_Icc_neg_iff.1 h).trans_lt haρ)
    have hev : spliceMap K φ ρ g =ᶠ[𝓝 z] K := by
      filter_upwards [(isClosed_circleExp_image_Icc (-a) a).isOpen_compl.mem_nhds hzO] with w hw
      exact spliceMap_of_le_abs hgK hKφ hρr (not_le.1 (mt mem_circleExp_image_Icc_neg_iff.2 hw)).le
    exact (K.isImmersion.isImmersionAt z).congr_of_eventuallyEq hev.symm

end Motion

/-! ### Straightening -/

section Straighten

open Complex (arg)

attribute [local instance] finrank_real_complex_fact'

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

variable [T2Space M]

/-- Straightening at the base point `1` of the circle; the general statement is
`TauCeti.SmoothEmbedding.exists_smoothIsotopy_eventuallyEq_of_mfderiv_eq`. -/
private theorem exists_smoothIsotopy_eventuallyEq_of_mfderiv_eq_one
    (K : SmoothEmbedding (𝓡 1) 𝓘(ℝ, E) ∞ Circle M) {L : Circle → M}
    (hL : ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ L) (h₀ : K 1 = L 1)
    (h₁ : mfderiv (𝓡 1) 𝓘(ℝ, E) K 1 = mfderiv (𝓡 1) 𝓘(ℝ, E) L 1) {U : Set Circle}
    (hU : U ∈ 𝓝 1) :
    ∃ (K' : SmoothEmbedding (𝓡 1) 𝓘(ℝ, E) ∞ Circle M)
      (F : SmoothIsotopy K.toContMDiffMap K'.toContMDiffMap),
      ⇑K' =ᶠ[𝓝 1] L ∧ ∀ t z, z ∉ U → F (t, z) = K z := by
  set p := K 1 with hp
  set φ := chartAt E p
  have hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas p
  have hpφ : p ∈ φ.source := mem_chart_source E p
  -- Step 1: an arc `|arg z| < r` inside `U`, along which `K` and `L` stay in the chart `φ`.
  obtain ⟨r, hr, hrπ, hrU, hKφ, hLφ⟩ : ∃ r, 0 < r ∧ r ≤ Real.pi ∧ Circle.centeredArc r ⊆ U ∧
      (∀ t, |t| < r → K (Circle.exp t) ∈ φ.source) ∧
      (∀ t, |t| < r → L (Circle.exp t) ∈ φ.source) := by
    have hpre {f : Circle → M} (hf : Continuous f) (hf1 : f 1 ∈ φ.source) :
        (fun t => f (Circle.exp t)) ⁻¹' φ.source ∈ 𝓝 0 :=
      (hf.comp Circle.exp.continuous).continuousAt.preimage_mem_nhds
        (φ.open_source.mem_nhds (by rwa [comp_apply, Circle.exp_zero]))
    have hU' : Circle.exp ⁻¹' U ∈ 𝓝 0 :=
      Circle.exp.continuous.continuousAt.preimage_mem_nhds (by rwa [Circle.exp_zero])
    obtain ⟨r', hr', hball⟩ := Metric.mem_nhds_iff.1
      (inter_mem hU' (inter_mem (hpre K.contMDiff.continuous hpφ) (hpre hL.continuous (h₀ ▸ hpφ))))
    have hmem {t : ℝ} (ht : |t| < min r' Real.pi) : t ∈ Metric.ball 0 r' := by
      simpa [Real.dist_eq] using ht.trans_le (min_le_left _ _)
    refine ⟨min r' Real.pi, lt_min hr' Real.pi_pos, min_le_right _ _, ?_,
      fun t ht => (hball (hmem ht)).2.1, fun t ht => (hball (hmem ht)).2.2⟩
    rintro _ ⟨t, ht, rfl⟩
    exact (hball (hmem ht)).1
  -- Step 2: `K` and `L` read in the chart along the circle have the same nonzero velocity at `0`.
  set k : ℝ → E := fun t => φ (K (Circle.exp t))
  set l : ℝ → E := fun t => φ (L (Circle.exp t))
  have hC {f : Circle → M} (hf : ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ f)
      (hfφ : ∀ t, |t| < r → f (Circle.exp t) ∈ φ.source) :
      ContDiffOn ℝ ∞ (fun t => φ (f (Circle.exp t))) (Ioo (-r) r) :=
    contMDiffOn_iff_contDiffOn.1 ((contMDiffOn_chart (x := p)).comp
      (hf.comp contMDiff_circleExp).contMDiffOn fun t ht => hfφ t (abs_lt.2 ht))
  have hkC := hC K.contMDiff hKφ
  have hlC := hC hL hLφ
  have hk0 : k 0 = φ p := by simp only [k, Circle.exp_zero, hp]
  have hl0 : l 0 = φ p := by simp only [l, Circle.exp_zero, ← h₀]
  have hvK := toSpanSingleton_deriv_chart_comp_circleExp (by simp)
    (K.contMDiff.mdifferentiableAt (by simp)) hφ (by rwa [Circle.exp_zero])
  have hvL := toSpanSingleton_deriv_chart_comp_circleExp (by simp)
    (hL.mdifferentiableAt (by simp)) hφ (by rwa [Circle.exp_zero, ← h₀])
  rw [Circle.exp_zero] at hvK hvL
  rw [← h₁, ← h₀] at hvL
  have hd : deriv k 0 = deriv l 0 := by
    simpa using congrArg (fun T => T 1) (hvK.trans hvL.symm)
  have hv : deriv k 0 ≠ 0 := by
    intro h0
    have h1 : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ p
        (mfderiv (𝓡 1) 𝓘(ℝ, E) K 1 (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp 0 1)) = 0 := by
      have h := (congrArg (fun T => T 1) hvK).symm
      simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at h
      exact h.trans h0
    have hφi := ((φ.isLocalDiffeomorphAt_of_mem_maximalAtlas hφ hpφ).isDiffImmersionAt
      (by simp)).mfderiv_injective
    have hKi := (K.isImmersion.isImmersionAt 1).mfderiv_injective (by simp)
    exact one_ne_zero (α := ℝ) (injective_mfderiv_circleExp 0
      ((hKi ((hφi (h1.trans (map_zero _).symm)).trans (map_zero _).symm)).trans
        (map_zero _).symm))
  -- Step 3: the spliced curves are regular on a fixed interval `[-ρ, ρ]`.
  obtain ⟨ℓ, ρ, hρ0, hρr, hpos⟩ := exists_pos_deriv_splice hr (hkC.of_le (by simp))
    (hlC.of_le (by simp)) (hk0.trans hl0.symm) hd hv
  -- Step 4: a ball in the chart about `φ p` whose points avoid `K` off the arc `|arg z| < ρ`, and
  -- a scale `δ` below which both curves stay in that ball.
  have hpC : p ∉ K '' (Circle.centeredArc ρ)ᶜ := by
    rintro ⟨z, hz, hKz⟩
    obtain rfl : z = 1 := K.isEmbedding.injective hKz
    exact hz ((Circle.mem_centeredArc (hρr.le.trans hrπ)).2 (by simpa using hρ0))
  have hV : IsOpen (K '' (Circle.centeredArc ρ)ᶜ)ᶜ :=
    (((Circle.isOpen_centeredArc ρ).isClosed_compl.isCompact).image
      K.contMDiff.continuous).isClosed.isOpen_compl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (φ.isOpen_inter_preimage_symm hV) (φ p)
    ⟨φ.map_source hpφ, by simpa [φ.left_inv hpφ] using hpC⟩
  have hI0 : Ioo (-r) r ∈ 𝓝 (0 : ℝ) := isOpen_Ioo.mem_nhds ⟨neg_lt_zero.2 hr, hr⟩
  obtain ⟨δk, hδk, hk⟩ := Metric.continuousAt_iff.1 (hkC.continuousOn.continuousAt hI0) ε hε
  obtain ⟨δl, hδl, hl⟩ := Metric.continuousAt_iff.1 (hlC.continuousOn.continuousAt hI0) ε hε
  set δ := min (ρ / 4) (min δk δl / 2)
  have hδ : 0 < δ := by positivity
  have hδρ : 2 * δ < ρ := by linarith [min_le_left (ρ / 4) (min δk δl / 2)]
  have hinball (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (t : ℝ) (ht : |t| < 2 * δ) :
      splice k l δ s t ∈ Metric.ball (φ p) ε := by
    have ht' : |t| < min δk δl := by
      linarith [min_le_right (ρ / 4) (min δk δl / 2)]
    have htk : dist t 0 < δk := by
      rw [Real.dist_eq, sub_zero]; exact ht'.trans_le (min_le_left _ _)
    have htl : dist t 0 < δl := by
      rw [Real.dist_eq, sub_zero]; exact ht'.trans_le (min_le_right _ _)
    exact splice_mem (convex_ball _ _) δ hs (Metric.mem_ball.2 (by rw [← hk0]; exact hk htk))
      (Metric.mem_ball.2 (by rw [← hl0]; exact hl htl))
  -- Step 5: the spliced curves satisfy the hypotheses of the splicing lemmas.
  have hGK (s : ℝ) (t : ℝ) (ht : 2 * δ ≤ |t|) : splice k l δ s t = φ (K (Circle.exp t)) :=
    splice_of_le_abs hδ s ht
  have hGφ (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (t : ℝ) (ht : |t| < ρ) :
      splice k l δ s t ∈ φ.target := by
    by_cases h2 : |t| < 2 * δ
    · exact (hball (hinball s hs t h2)).1
    · rw [hGK s t (not_lt.1 h2)]
      exact φ.map_source (hKφ t (ht.trans hρr))
  have hjoint := contMDiff_spliceMap (K := K) (G := splice k l δ) (contDiffOn_splice hkC hlC δ)
    hGφ (fun s _ t ht _ => hGK s t ht) hKφ hδρ hρr.le hrπ hφ
  have hemb (s : unitInterval) : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, E) ∞
      (spliceMap K φ ρ (splice k l δ s)) := by
    have hgC : ContDiffOn ℝ ∞ (splice k l δ s) (Ioo (-r) r) :=
      (contDiffOn_splice hkC hlC δ).comp (contDiffOn_const.prodMk contDiffOn_id)
        fun t ht => ⟨mem_univ _, ht⟩
    have hmono : StrictMonoOn (ℓ ∘ splice k l δ s) (Icc (-ρ) ρ) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc _ _) (fun t ht => ?_) fun t ht => ?_
      · exact (ℓ.continuous.continuousAt.comp
          (hpos δ hδ s s.2 t ht).1.continuousAt).continuousWithinAt
      · have ht' := interior_subset ht
        rw [(ℓ.hasFDerivAt.comp_hasDerivAt t (hpos δ hδ s s.2 t ht').1.hasDerivAt).deriv]
        exact (hpos δ hδ s s.2 t ht').2
    refine isSmoothEmbedding_spliceMap (r := r) (a := 2 * δ)
      (hjoint.comp (contMDiff_const.prodMk contMDiff_id)) hgC (hGφ s s.2) (fun t ht _ => hGK s t ht)
      hKφ (fun t ht t' ht' htt' => ?_) (fun t ht h0 => ?_)
      (fun t ht => (hball (hinball s s.2 t ht)).2) hδρ hρr.le hrπ hφ
    · exact hmono.injOn (Ioo_subset_Icc_self ht) (Ioo_subset_Icc_self ht')
        (congrArg ℓ htt')
    · have := (hpos δ hδ s s.2 t (abs_le.1 ht.le)).2
      rw [h0, map_zero] at this
      exact lt_irrefl _ this
  let K' := SmoothEmbedding.ofIsSmoothEmbedding _ (hemb 1)
  refine ⟨K', ⟨⟨_, hjoint⟩, fun z => ?_, fun z => ?_, hemb⟩, ?_, fun t z hz => ?_⟩
  · -- At time `0` the motion is `K`.
    simp only [ContMDiffMap.coeFn_mk, Icc.coe_zero]
    exact spliceMap_of_le_abs (a := 0) (fun t _ _ => splice_zero k l δ t) hKφ hρr.le
      (abs_nonneg _)
  · simp [K']
  · -- Near `1` the final embedding is `L`.
    filter_upwards [(Circle.isOpen_centeredArc δ).mem_nhds
      ((Circle.mem_centeredArc (by linarith)).2 (by simpa using hδ))] with z hz
    have hz' := (Circle.mem_centeredArc (by linarith)).1 hz
    have hzr : |arg z| < r := by linarith
    simp only [K', SmoothEmbedding.ofIsSmoothEmbedding_apply, Icc.coe_one]
    rw [spliceMap_of_abs_lt (by linarith), splice_one_of_abs_le hδ hz'.le,
      φ.left_inv (hLφ _ hzr), Circle.exp_arg]
  · -- Off `U` the motion is stationary.
    have hzr : r ≤ |arg z| := not_lt.1 fun h => hz (hrU ((Circle.mem_centeredArc hrπ).2 h))
    exact spliceMap_of_le_abs (fun t' ht' _ => hGK t t' ht') hKφ hρr.le (by linarith)

/-- **Straightening a circle embedding near a point.** Let `K` be a smooth embedding of the circle
into a boundaryless manifold `M`, and `L` a smooth map of the circle into `M`, which agree to first
order at `z₀`: `K z₀ = L z₀` and `K` and `L` have the same derivative there. Then `K` is smoothly
isotopic to an embedding `K'` which agrees with `L` on a neighbourhood of `z₀`, by an isotopy which
is stationary off any given
neighbourhood `U` of `z₀`. -/
theorem SmoothEmbedding.exists_smoothIsotopy_eventuallyEq_of_mfderiv_eq
    (K : SmoothEmbedding (𝓡 1) 𝓘(ℝ, E) ∞ Circle M) {L : Circle → M}
    (hL : ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ L) {z₀ : Circle} (h₀ : K z₀ = L z₀)
    (h₁ : mfderiv (𝓡 1) 𝓘(ℝ, E) K z₀ = mfderiv (𝓡 1) 𝓘(ℝ, E) L z₀) {U : Set Circle}
    (hU : U ∈ 𝓝 z₀) :
    ∃ (K' : SmoothEmbedding (𝓡 1) 𝓘(ℝ, E) ∞ Circle M)
      (F : SmoothIsotopy K.toContMDiffMap K'.toContMDiffMap),
      ⇑K' =ᶠ[𝓝 z₀] L ∧ ∀ t z, z ∉ U → F (t, z) = K z := by
  -- Rotate the base point `z₀` to `1` and straighten there.
  set R : Circle ≃ₘ^∞⟮𝓡 1, 𝓡 1⟯ Circle := _root_.Diffeomorph.smul (𝓡 1) (𝓡 1) ∞ z₀
  have hR1 : R 1 = z₀ := mul_one z₀
  have hmf {f : Circle → M} (hf : ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ f) :
      mfderiv (𝓡 1) 𝓘(ℝ, E) (f ∘ R) 1 =
        (mfderiv (𝓡 1) 𝓘(ℝ, E) f z₀).comp (mfderiv (𝓡 1) (𝓡 1) R 1) := by
    rw [mfderiv_comp 1 (hf.mdifferentiableAt (by simp))
      (R.contMDiff.mdifferentiableAt (by simp)), hR1]
  obtain ⟨K₁, F₁, hK₁, hF₁⟩ := exists_smoothIsotopy_eventuallyEq_of_mfderiv_eq_one
    (K.compDiffeomorph R) (hL.comp R.contMDiff)
    (by rw [compDiffeomorph_apply, comp_apply, hR1, h₀])
    -- After rewriting, the two sides differ only in the base points `K z₀` and `L z₀` of the
    -- tangent spaces in their types, both of which are `E`.
    (by rw [coe_compDiffeomorph, hmf K.contMDiff, hmf hL, h₁]; rfl)
    (U := R ⁻¹' U) (R.continuous.continuousAt.preimage_mem_nhds (by rwa [hR1]))
  -- Rotate back.
  refine ⟨K₁.compDiffeomorph R.symm,
    { toContMDiffMap := ⟨fun q => F₁ (q.1, R.symm q.2),
        F₁.contMDiff.comp (contMDiff_fst.prodMk (R.symm.contMDiff.comp contMDiff_snd))⟩
      map_zero_left := fun z => by
        simp [F₁.apply_zero, compDiffeomorph_apply]
      map_one_left := fun z => by
        simp [F₁.apply_one, compDiffeomorph_apply]
      isSmoothEmbedding := fun t =>
        isSmoothEmbedding_comp_diffeomorph R.symm (F₁.isSmoothEmbedding t) }, ?_,
    fun t z hz => ?_⟩
  · have hR : Tendsto R.symm (𝓝 z₀) (𝓝 1) := by
      simpa [← hR1] using R.symm.continuous.tendsto z₀
    filter_upwards [hR.eventually hK₁] with z hz
    rw [compDiffeomorph_apply, hz, comp_apply, Diffeomorph.apply_symm_apply]
  · have hz' : R.symm z ∉ R ⁻¹' U := by
      rwa [mem_preimage, Diffeomorph.apply_symm_apply]
    exact (hF₁ t _ hz').trans (by rw [compDiffeomorph_apply, Diffeomorph.apply_symm_apply])

end Straighten

end TauCeti
