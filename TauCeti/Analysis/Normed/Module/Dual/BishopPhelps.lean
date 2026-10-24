/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.RCLike.Extend
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Order.Filter.Extr
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.Analysis.Normed.Module.Dual.Basic
import TauCeti.Topology.MetricSpace.Ekeland

/-!
# The Bishop–Phelps theorem

Let `C` be a complete convex subset of a real or complex normed space `E`. A *support functional*
of `C` is a nonzero continuous linear functional `g` whose real part attains its supremum on `C`;
a point of `C` at which this happens is a *support point*. The **Bishop–Phelps theorem** says
that there are many of both:

* if `C` is moreover bounded and nonempty and `E` is nonzero, the support functionals of `C` are
  norm dense in the dual (`Convex.dense_setOf_ne_zero_isMaxOn_re`);
* the support points of `C` are dense in its boundary
  (`Convex.frontier_subset_closure_setOf_isMaxOn_re`); conversely every support point lies on the
  boundary (`StrongDual.mem_frontier_of_isMaxOn_re`);
* taking for `C` the closed unit ball, the norm-attaining functionals are norm dense in the dual
  (`TauCeti.dense_setOf_exists_norm_apply_eq_norm`).

The support theorems assume only that `C` is complete; the norm-attainment theorem assumes
that `E` is complete. Convexity is real convexity, also over `ℂ`. Cone convexity also holds on
seminormed spaces, without a normed scalar action over `𝕜`.

The proof follows Phelps. Ekeland's variational principle
(`LowerSemicontinuous.exists_add_mul_dist_le_and_lt_add_mul_dist`), applied to minus the real
part of a functional `f` on `C`, produces a point `x ∈ C` such that `C` meets the cone
`x + {w | k * ‖f‖ * ‖w‖ ≤ re (f w)}` only at `x`. Separating `C` from the interior of this cone
gives a support functional `h` at `x` whose real part is positive on the open cone
(`Convex.exists_isMaxOn_re_of_bddAbove`), and the *Bishop–Phelps lemma*
(`StrongDual.exists_pos_norm_sub_ofReal_smul_le`) shows that a positive multiple of `h` lies
within `k * ‖f‖` of `f`.

## Main results

* `StrongDual.exists_pos_norm_sub_ofReal_smul_le`: the Bishop–Phelps lemma.
* `StrongDual.convex_setOf_mul_norm_sub_lt_re`: the open Bishop–Phelps cones are convex.
* `Convex.exists_isMaxOn_re_of_bddAbove`: support functionals at points reached through a cone.
* `Convex.dense_setOf_ne_zero_isMaxOn_re`: support functionals of a bounded complete convex set are
  dense.
* `Convex.frontier_subset_closure_setOf_isMaxOn_re`: support points are dense in the boundary.
* `TauCeti.dense_setOf_exists_norm_apply_eq_norm`: norm-attaining functionals are dense.

## References

* E. Bishop and R. R. Phelps, *A proof that every Banach space is subreflexive*, Bull. Amer.
  Math. Soc. 67 (1961), 97–98.
* R. R. Phelps, *Convex Functions, Monotone Operators and Differentiability*, 2nd ed.,
  Lecture Notes in Mathematics 1364, Springer, 1993, Chapter 3.
* R. E. Megginson, *An Introduction to Banach Space Theory*, §2.11 and Theorem 2.11.14.
-/

public section

open Filter Metric RCLike Set Topology

variable {𝕜 E : Type*} [RCLike 𝕜]

section Seminormed

variable [SeminormedAddCommGroup E] [Module 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- For `0 ≤ r`, the open cone `{y | r * ‖y - x‖ < re (f (y - x))}` with vertex `x` is convex. -/
theorem StrongDual.convex_setOf_mul_norm_sub_lt_re (f : StrongDual 𝕜 E) {r : ℝ} (hr : 0 ≤ r)
    (x : E) : Convex ℝ {y | r * ‖y - x‖ < re (f (y - x))} := by
  let F : E →ₗ[ℝ] ℝ := (reCLM.comp (f.restrictScalars ℝ)).toLinearMap
  have h := ((convexOn_univ_norm (E := E)).smul hr |>.sub (F.concaveOn convex_univ)).convex_lt 0
  simpa [F, sub_eq_add_neg] using h.translate_preimage_left (-x)

end Seminormed

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace StrongDual

/-- **The Bishop–Phelps lemma.** Let `0 ≤ k < 1` and `f ≠ 0`. If the real part of `h` is positive
on the open cone `{x | k * ‖f‖ * ‖x‖ < re (f x)}`, then some positive real multiple of `h` lies
within `k * ‖f‖` of `f`. -/
theorem exists_pos_norm_sub_ofReal_smul_le (f h : StrongDual 𝕜 E) {k : ℝ} (hk₀ : 0 ≤ k)
    (hk₁ : k < 1) (hf : f ≠ 0) (hpos : ∀ x, k * ‖f‖ * ‖x‖ < re (f x) → 0 < re (h x)) :
    ∃ c : ℝ, 0 < c ∧ ‖f - (c : 𝕜) • h‖ ≤ k * ‖f‖ := by
  let : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  let : IsScalarTower ℝ 𝕜 E := .of_algebraMap_smul fun _ _ ↦ rfl
  have hkf : 0 ≤ k * ‖f‖ := by positivity
  -- The argument runs with the real parts `F` and `H` of `f` and `h`.
  let F : StrongDual ℝ E := reCLM.comp (f.restrictScalars ℝ)
  let H : StrongDual ℝ E := reCLM.comp (h.restrictScalars ℝ)
  have hF (x : E) : F x = re (f x) := rfl
  have hH (x : E) : H x = re (h x) := rfl
  -- On the kernel of `H`, the cone condition bounds `|F|` by `k * ‖f‖` times the norm.
  have hker (y : E) (hy : H y = 0) : |F y| ≤ k * ‖f‖ * ‖y‖ := by
    rw [hH] at hy
    rw [abs_le, hF]
    constructor
    · by_contra! hlt
      have := hpos (-y) (by rw [norm_neg, map_neg, map_neg]; linarith)
      rw [map_neg, map_neg, hy, neg_zero] at this
      exact this.false
    · by_contra! hlt
      have := hpos y hlt
      rw [hy] at this
      exact this.false
  -- Hahn–Banach extends `F` from `ker H` without increasing its norm.
  let N : Submodule ℝ E := LinearMap.ker (H : E →ₗ[ℝ] ℝ)
  obtain ⟨F₁, hF₁, hF₁norm⟩ := exists_extension_norm_eq N (F.comp N.subtypeL)
  have hF₁le : ‖F₁‖ ≤ k * ‖f‖ := hF₁norm ▸ (F.comp N.subtypeL).opNorm_le_bound hkf fun y ↦ by
    simpa [Real.norm_eq_abs] using hker y y.2
  -- `F - F₁` vanishes on `ker H`, so it is a real multiple of `H`.
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ∀ x, F x - F₁ x = c * H x := by
    have hle : ⨅ _ : Unit, LinearMap.ker (H : E →ₗ[ℝ] ℝ) ≤
        LinearMap.ker ((F - F₁ : StrongDual ℝ E) : E →ₗ[ℝ] ℝ) := by
      rw [iInf_const]
      intro y hy
      simpa [sub_eq_zero] using (hF₁ ⟨y, hy⟩).symm
    have hmem := mem_span_of_iInf_ker_le_ker hle
    rw [range_const, Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, fun x ↦ by simpa using (LinearMap.congr_fun hc x).symm⟩
  -- Testing at a point of the open cone shows `c > 0`.
  obtain ⟨x₀, hx₀⟩ := f.exists_mul_norm_lt_re_apply hkf (by nlinarith [norm_pos_iff.2 hf])
  have hc₀ : 0 < c := by
    have h₁ : F₁ x₀ ≤ k * ‖f‖ * ‖x₀‖ := (le_abs_self _).trans <|
      (F₁.le_opNorm x₀).trans (mul_le_mul_of_nonneg_right hF₁le (norm_nonneg _))
    have h₂ : 0 < c * H x₀ := by rw [← hc, hF]; linarith
    exact (pos_iff_pos_of_mul_pos h₂).2 (hpos x₀ hx₀)
  refine ⟨c, hc₀, ?_⟩
  -- The real part of `f - c • h` is `F₁`; real-part restriction preserves the dual norm.
  have heq : (extendRCLikeₗᵢ (𝕜 := 𝕜) (F := E)).symm (f - (c : 𝕜) • h) = F₁ := by
    ext x
    simp only [extendRCLikeₗᵢ_symm_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_restrictScalars', reCLM_apply, sub_apply, smul_apply, smul_eq_mul,
      map_sub, re_ofReal_mul]
    have hcx := hc x
    rw [hF, hH] at hcx
    linarith only [hcx]
  rwa [← (extendRCLikeₗᵢ (𝕜 := 𝕜) (F := E)).symm.norm_map, heq]

/-- A point at which the real part of a nonzero functional attains its maximum on `C` lies on the
boundary of `C`. -/
theorem mem_frontier_of_isMaxOn_re (g : StrongDual 𝕜 E) (hg : g ≠ 0) {C : Set E} {x : E}
    (hx : x ∈ C) (hmax : IsMaxOn (fun y ↦ re (g y)) C x) : x ∈ frontier C := by
  refine ⟨subset_closure hx, fun hint ↦ ?_⟩
  obtain ⟨w, hw⟩ := g.exists_mul_norm_lt_re_apply le_rfl (norm_pos_iff.2 hg)
  rw [zero_mul] at hw
  -- Moving from `x` in the direction `w` stays in `C` for a while and increases `re ∘ g`.
  have hcont : Tendsto (fun t : ℝ ↦ x + (t : 𝕜) • w) (𝓝 0) (𝓝 x) := by
    have : Continuous fun t : ℝ ↦ x + (t : 𝕜) • w :=
      continuous_const.add (continuous_ofReal.smul continuous_const)
    simpa using this.tendsto 0
  obtain ⟨t, htC, ht⟩ := ((hcont.eventually (mem_interior_iff_mem_nhds.1 hint)).filter_mono
    nhdsWithin_le_nhds |>.and self_mem_nhdsWithin).exists (f := 𝓝[>] (0 : ℝ))
  have := hmax htC
  simp only [mem_ofPred_eq, map_add, map_smul, smul_eq_mul, re_ofReal_mul] at this
  nlinarith [mem_Ioi.1 ht]

end StrongDual

section RealModule

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] {C : Set E}

/-- **Bishop–Phelps support lemma.** Let `C` be a complete convex subset of a normed space, let `f`
be a nonzero functional whose real part is bounded above on `C`, and let `0 < k < 1`. From every
`z ∈ C` one reaches a point `x ∈ C` with `k * ‖f‖ * ‖x - z‖ ≤ re (f (x - z))` at which `C` has a
support functional `h`, nonzero and with real part positive on the open cone
`{w | k * ‖f‖ * ‖w‖ < re (f w)}`. -/
theorem Convex.exists_isMaxOn_re_of_bddAbove (hconv : Convex ℝ C) (hC : IsComplete C)
    {f : StrongDual 𝕜 E} (hf : f ≠ 0) (hbdd : BddAbove ((fun y ↦ re (f y)) '' C)) {k : ℝ}
    (hk₀ : 0 < k) (hk₁ : k < 1) {z : E} (hz : z ∈ C) :
    ∃ x ∈ C, k * ‖f‖ * ‖x - z‖ ≤ re (f (x - z)) ∧ ∃ h : StrongDual 𝕜 E, h ≠ 0 ∧
      IsMaxOn (fun y ↦ re (h y)) C x ∧ ∀ w, k * ‖f‖ * ‖w‖ < re (f w) → 0 < re (h w) := by
  have hkf : 0 < k * ‖f‖ := mul_pos hk₀ (norm_pos_iff.2 hf)
  -- Ekeland's principle for `-re ∘ f` on the complete metric space `C`.
  have : CompleteSpace C := hC.completeSpace_coe
  obtain ⟨M, hM⟩ := hbdd
  have hcont : Continuous fun y : C ↦ -re (f y) :=
    (continuous_re.comp (f.continuous.comp continuous_subtype_val)).neg
  obtain ⟨⟨x, hx⟩, hxz, hmin⟩ :=
    hcont.lowerSemicontinuous.exists_add_mul_dist_le_and_lt_add_mul_dist
      ⟨-M, by rintro _ ⟨y, rfl⟩; exact neg_le_neg (hM (mem_image_of_mem _ y.2))⟩ hkf ⟨z, hz⟩
  simp only [Subtype.dist_eq, dist_eq_norm] at hxz hmin
  refine ⟨x, hx, by simp only [map_sub]; linarith, ?_⟩
  -- The open cone `s` with vertex `x` is convex, open and disjoint from `C`.
  set s : Set E := {y | k * ‖f‖ * ‖y - x‖ < re (f (y - x))} with hs
  have hs_open : IsOpen s := isOpen_lt (by fun_prop)
    (continuous_re.comp (f.continuous.comp (continuous_id.sub continuous_const)))
  have hs_conv : Convex ℝ s := f.convex_setOf_mul_norm_sub_lt_re hkf.le x
  have hdisj : Disjoint s C := by
    refine disjoint_left.2 fun y hys hyC ↦ ?_
    simp only [hs, mem_ofPred_eq] at hys
    by_cases hyx : y = x
    · subst hyx
      simp at hys
    · have := hmin ⟨y, hyC⟩ (by simpa [Subtype.ext_iff] using hyx)
      simp only [map_sub] at hys
      linarith
  obtain ⟨g, u, hgs, hgC⟩ := RCLike.geometric_hahn_banach_open (𝕜 := 𝕜) hs_conv hs_open hconv hdisj
  -- `x + w` lies in `s` for every `w` in the open cone.
  have hcone (w : E) (hw : k * ‖f‖ * ‖w‖ < re (f w)) : x + w ∈ s := by
    simpa [hs] using hw
  have hneg (w : E) (hw : k * ‖f‖ * ‖w‖ < re (f w)) : re (g w) < 0 := by
    have := hgs _ (hcone w hw)
    rw [map_add, map_add] at this
    linarith [hgC x hx]
  -- Approaching `x` along a cone direction shows that `re ∘ g` is at most `u` at `x`.
  obtain ⟨w₀, hw₀⟩ := f.exists_mul_norm_lt_re_apply hkf.le (by nlinarith [norm_pos_iff.2 hf])
  have hgx : re (g x) ≤ u := by
    have hlim : Tendsto (fun t : ℝ ↦ re (g (x + (t : 𝕜) • w₀))) (𝓝[>] 0) (𝓝 (re (g x))) := by
      have : Continuous fun t : ℝ ↦ re (g (x + (t : 𝕜) • w₀)) :=
        continuous_re.comp (g.continuous.comp
          (continuous_const.add (continuous_ofReal.smul continuous_const)))
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hlim (eventually_nhdsWithin_of_forall fun t (ht : 0 < t) ↦ ?_)
    refine (hgs _ (hcone _ ?_)).le
    rw [norm_smul, norm_ofReal, abs_of_pos ht, map_smul, smul_eq_mul, re_ofReal_mul]
    nlinarith
  refine ⟨-g, fun h0 ↦ ?_, fun y hy ↦ ?_, fun w hw ↦ ?_⟩
  · have := hneg w₀ hw₀
    rw [neg_eq_zero.1 h0] at this
    simp at this
  · simp only [mem_ofPred_eq, FunLike.coe_neg, Pi.neg_apply, map_neg,
      neg_le_neg_iff]
    exact hgx.trans (hgC y hy)
  · simpa using hneg w hw

/-- **The Bishop–Phelps theorem for support functionals.** The support functionals of a nonempty
bounded complete convex subset `C` of a nonzero normed space, namely the nonzero functionals whose
real part attains its supremum on `C`, are norm dense in the dual. -/
theorem Convex.dense_setOf_ne_zero_isMaxOn_re [Nontrivial E] (hconv : Convex ℝ C)
    (hC : IsComplete C) (hb : Bornology.IsBounded C) (hne : C.Nonempty) :
    Dense {g : StrongDual 𝕜 E | g ≠ 0 ∧ ∃ x ∈ C, IsMaxOn (fun y ↦ re (g y)) C x} := by
  set S := {g : StrongDual 𝕜 E | g ≠ 0 ∧ ∃ x ∈ C, IsMaxOn (fun y ↦ re (g y)) C x}
  obtain ⟨z, hz⟩ := hne
  obtain ⟨R, hR⟩ := hb.exists_norm_le
  -- Every nonzero functional is a limit of support functionals.
  have hsub : ({0}ᶜ : Set (StrongDual 𝕜 E)) ⊆ closure S := by
    intro f hf
    rw [mem_compl_singleton_iff] at hf
    have hfpos : 0 < ‖f‖ := norm_pos_iff.2 hf
    refine Metric.mem_closure_iff.2 fun ε hε ↦ ?_
    set k := min (1 / 2) (ε / (2 * ‖f‖))
    have hk₀ : 0 < k := lt_min (by norm_num) (by positivity)
    have hk₁ : k < 1 := (min_le_left _ _).trans_lt (by norm_num)
    have hkε : k * ‖f‖ < ε := by
      calc k * ‖f‖ ≤ ε / (2 * ‖f‖) * ‖f‖ := by gcongr; exact min_le_right _ _
        _ = ε / 2 := by field_simp
        _ < ε := half_lt_self hε
    have hbdd : BddAbove ((fun y ↦ re (f y)) '' C) := by
      refine ⟨‖f‖ * R, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      exact (re_le_norm _).trans ((f.le_opNorm y).trans (by gcongr; exact hR y hy))
    obtain ⟨x, hx, -, h, hh, hmax, hpos⟩ :=
      hconv.exists_isMaxOn_re_of_bddAbove hC hf hbdd hk₀ hk₁ hz
    obtain ⟨c, hc, hfc⟩ := f.exists_pos_norm_sub_ofReal_smul_le h hk₀.le hk₁ hf hpos
    refine ⟨(c : 𝕜) • h, ⟨smul_ne_zero (ofReal_ne_zero.2 hc.ne') hh, x, hx, fun y hy ↦ ?_⟩, ?_⟩
    · simp only [mem_ofPred_eq, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
        re_ofReal_mul]
      exact mul_le_mul_of_nonneg_left (hmax hy) hc.le
    · rw [dist_eq_norm]
      exact hfc.trans_lt hkε
  have := Module.punctured_nhds_neBot 𝕜 (StrongDual 𝕜 E)
  exact dense_closure.1 ((dense_compl_singleton 0).mono hsub)

/-- **The Bishop–Phelps theorem for support points.** The support points of a complete convex
subset `C` of a normed space, namely the points of `C` at which the real part of some nonzero
functional attains its supremum on `C`, are dense in the boundary of `C`. They all lie on the
boundary by `StrongDual.mem_frontier_of_isMaxOn_re`. -/
theorem Convex.frontier_subset_closure_setOf_isMaxOn_re (hconv : Convex ℝ C) (hC : IsComplete C) :
    frontier C ⊆
      closure {x ∈ C | ∃ g : StrongDual 𝕜 E, g ≠ 0 ∧ IsMaxOn (fun y ↦ re (g y)) C x} := by
  intro x hx
  have hxC : x ∈ C := hC.isClosed.frontier_subset hx
  refine Metric.mem_closure_iff.2 fun ε hε ↦ ?_
  -- A point `y ∉ C` close to `x` is strictly separated from `C` by some functional `f`.
  rw [frontier_eq_closure_inter_closure] at hx
  obtain ⟨y, hyC, hxy⟩ := Metric.mem_closure_iff.1 hx.2 (ε / 2) (half_pos hε)
  obtain ⟨f, u, hfC, hfy⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜) hconv hC.isClosed hyC
  have hf : f ≠ 0 := by
    rintro rfl
    have := hfC x hxC
    simp only [zero_apply, map_zero] at this hfy
    linarith
  have hbdd : BddAbove ((fun y ↦ re (f y)) '' C) :=
    ⟨u, by rintro _ ⟨b, hb, rfl⟩; exact (hfC b hb).le⟩
  -- The support point reached from `x` through the cone of slope `1 / 2` is within `ε` of `x`.
  obtain ⟨x₀, hx₀, hx₀x, h, hh, hmax, -⟩ :=
    hconv.exists_isMaxOn_re_of_bddAbove hC hf hbdd (k := 1 / 2) (by norm_num) (by norm_num) hxC
  refine ⟨x₀, ⟨hx₀, h, hh, hmax⟩, ?_⟩
  have hfpos : 0 < ‖f‖ := norm_pos_iff.2 hf
  have h₁ : re (f (x₀ - x)) < re (f (y - x)) := by
    simp only [map_sub]
    linarith [hfC x₀ hx₀]
  have h₂ : re (f (y - x)) ≤ ‖f‖ * ‖y - x‖ := (re_le_norm _).trans (f.le_opNorm _)
  rw [dist_comm, dist_eq_norm]
  rw [dist_eq_norm, norm_sub_rev] at hxy
  nlinarith

end RealModule

namespace TauCeti

/-- **The Bishop–Phelps theorem.** The continuous linear functionals on a Banach space which
attain their norm on the closed unit ball are norm dense in the dual. -/
theorem dense_setOf_exists_norm_apply_eq_norm [CompleteSpace E] :
    Dense {g : StrongDual 𝕜 E | ∃ x, ‖x‖ ≤ 1 ∧ ‖g x‖ = ‖g‖} := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · convert dense_univ using 1
    refine eq_univ_of_forall fun g ↦ ?_
    exact ⟨0, by simp, by simp [Subsingleton.elim g 0]⟩
  let : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  let : IsScalarTower ℝ 𝕜 E := .of_algebraMap_smul fun _ _ ↦ rfl
  refine (Convex.dense_setOf_ne_zero_isMaxOn_re (𝕜 := 𝕜) (convex_closedBall (0 : E) 1)
    isClosed_closedBall.isComplete isBounded_closedBall
    ⟨0, mem_closedBall_self zero_le_one⟩).mono ?_
  rintro g ⟨-, x, hx, hmax⟩
  rw [mem_closedBall_zero_iff] at hx
  refine ⟨x, hx, le_antisymm ((g.le_opNorm x).trans (mul_le_of_le_one_right (norm_nonneg _) hx))
    ?_⟩
  have := StrongDual.re_apply_add_mul_norm_le (f := g) (x := 0) zero_le_one fun y hy ↦ hmax hy
  rw [map_zero, zero_re, zero_add, one_mul] at this
  exact this.trans (re_le_norm _)

end TauCeti
