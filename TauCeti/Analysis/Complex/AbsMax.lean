/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Relative maximum-modulus bounds

A bound by the real part of a holomorphic function propagates from the frontier of a bounded set
to its closure: if `‖f w‖ ≤ re (g w)` on the frontier, for `f` and `g` complex differentiable
inside and continuous on the closure, then the same holds on the closure
(`Complex.norm_le_re_of_forall_mem_frontier_norm_le_re`). Since `re ∘ g` is harmonic, this is a
comparison of the subharmonic function `‖f‖` with a harmonic majorant, and it reduces to the
maximum modulus principle for `exp (ℓ ∘ f - g)` with `ℓ` a norming functional at the point.

The rest of the file gives three consequences of the maximum modulus principle for a function
`f` that is differentiable on `ball z₀ R` and continuous on its closure, under a bound on
`sphere z₀ R` relative to the value at the centre:

* if a nonzero value occurs in the closed disc under the relative sphere bound, then the
  central value is nonzero, for any real radius and any complex normed-space target;
* if `‖f w‖ ≤ M ‖f z₀‖` on the sphere and `f z₀ ≠ 0`, then `1 ≤ M`;
* if `‖P w * G w‖ ≤ M ‖P z₀ * G z₀‖` on the sphere, where `P` is nonzero there and at least as
  large as at the centre, then `‖G w‖ ≤ M ‖G z₀‖` on the closed disc.

The cofactor bound removes a factor `P` that is no smaller on the boundary than at the centre,
such as a product of linear factors over zeros near `z₀`.

The file then gives the maximum modulus principle on a closed disc with the bound read as the
supremum of `‖f‖` over the boundary circle, and the boundedness of `‖f‖` on a sphere that makes
this supremum usable with `le_ciSup`.

Finally, the maximum principle for the real part of a holomorphic function `f` on a bounded set
`U` allows finitely many exceptional frontier points `F`, where `f` need not extend continuously,
provided `re ∘ f` is bounded above on `U`: if `re ∘ f ≤ 0` on `frontier U \ F`, then
`re ∘ f ≤ 0` on `closure U \ F`. Consequently two holomorphic functions on a bounded domain whose
imaginary parts differ by a bounded amount and agree on the frontier away from `F` differ by a real
constant. This determines, up to a real translation, a holomorphic map into a strip from the
boundary line to which it sends each frontier point, although such a map jumps at the corners.

## Main results

* `Complex.norm_le_re_of_forall_mem_frontier_norm_le_re`
* `DiffContOnCl.ne_zero_of_forall_mem_sphere_norm_le_mul`
* `DiffContOnCl.one_le_of_forall_mem_sphere_norm_le_mul`
* `Complex.norm_le_of_forall_mem_sphere_norm_mul_le`
* `ContinuousOn.bddAbove_range_norm_sphere`
* `DiffContOnCl.norm_le_iSup_norm_sphere_of_mem_closedBall`
* `Complex.re_nonpos_of_forall_mem_frontier_diff_re_nonpos`
* `Complex.exists_eqOn_add_ofReal_of_forall_mem_frontier_im_eq`
-/

public section

open Metric Set

/-- **Comparison with the real part of a holomorphic function.** Let `f` and `g` be complex
differentiable on a bounded set `U` and continuous on its closure, with `f` valued in a complex
normed space and `g` complex valued. If `‖f w‖ ≤ re (g w)` on the frontier of `U`, then
`‖f z‖ ≤ re (g z)` on the closure of `U`. -/
theorem Complex.norm_le_re_of_forall_mem_frontier_norm_le_re {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [Nontrivial E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] {f : E → F} {g : E → ℂ} {U : Set E} (hU : Bornology.IsBounded U)
    (hf : DiffContOnCl ℂ f U) (hg : DiffContOnCl ℂ g U)
    (hfg : ∀ w ∈ frontier U, ‖f w‖ ≤ (g w).re) {z : E} (hz : z ∈ closure U) : ‖f z‖ ≤ (g z).re := by
  obtain ⟨ℓ, hℓ, hℓz⟩ := exists_dual_vector'' ℂ (f z)
  have hexp : DiffContOnCl ℂ (fun w ↦ Complex.exp (ℓ (f w) - g w)) U :=
    Complex.differentiable_exp.comp_diffContOnCl ((ℓ.differentiable.comp_diffContOnCl hf).sub hg)
  have key := Complex.norm_le_of_forall_mem_frontier_norm_le hU hexp (C := 1) (fun w hw ↦ by
    rw [Complex.norm_exp, Real.exp_le_one_iff, Complex.sub_re, sub_nonpos]
    calc (ℓ (f w)).re ≤ ‖ℓ (f w)‖ := Complex.re_le_norm _
      _ ≤ ‖ℓ‖ * ‖f w‖ := ℓ.le_opNorm _
      _ ≤ ‖f w‖ := mul_le_of_le_one_left (norm_nonneg _) hℓ
      _ ≤ (g w).re := hfg w hw) hz
  rw [Complex.norm_exp, Real.exp_le_one_iff, Complex.sub_re, sub_nonpos, hℓz] at key
  simpa using key

variable {z₀ : ℂ} {R M : ℝ}

/-- If `f` is differentiable on `ball z₀ R` and continuous on its closure, with `0 < R`,
`f z₀ ≠ 0` and `‖f w‖ ≤ M ‖f z₀‖` on `sphere z₀ R`, then `1 ≤ M`. -/
theorem DiffContOnCl.one_le_of_forall_mem_sphere_norm_le_mul {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (ball z₀ R)) (hR : 0 < R) (hz₀ : f z₀ ≠ 0)
    (hM : ∀ w ∈ sphere z₀ R, ‖f w‖ ≤ M * ‖f z₀‖) : 1 ≤ M := by
  have := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hf
    (by rwa [frontier_ball z₀ hR.ne'])
    (by rw [closure_ball z₀ hR.ne']; exact mem_closedBall_self hR.le)
  rwa [le_mul_iff_one_le_left (norm_pos_iff.2 hz₀)] at this

/-- **Maximum modulus for a cofactor.** Let `G` be differentiable on `ball z₀ R` and continuous on
its closure, with `0 < R`, and let `P` be nonzero on `sphere z₀ R` with `‖P z₀‖ ≤ ‖P w‖` there.
If `‖P w * G w‖ ≤ M ‖P z₀ * G z₀‖` on the sphere, then `‖G w‖ ≤ M ‖G z₀‖` on `closedBall z₀ R`. -/
theorem Complex.norm_le_of_forall_mem_sphere_norm_mul_le {P G : ℂ → ℂ} (hR : 0 < R)
    (hG : DiffContOnCl ℂ G (ball z₀ R)) (hP₀ : ∀ w ∈ sphere z₀ R, P w ≠ 0)
    (hP : ∀ w ∈ sphere z₀ R, ‖P z₀‖ ≤ ‖P w‖)
    (hPG : ∀ w ∈ sphere z₀ R, ‖P w * G w‖ ≤ M * ‖P z₀ * G z₀‖) {w : ℂ}
    (hw : w ∈ closedBall z₀ R) : ‖G w‖ ≤ M * ‖G z₀‖ := by
  have hmax {C : ℝ} (hC : ∀ u ∈ sphere z₀ R, ‖G u‖ ≤ C) {v : ℂ} (hv : v ∈ closedBall z₀ R) :
      ‖G v‖ ≤ C :=
    Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hG
      (by rwa [frontier_ball z₀ hR.ne']) (by rwa [closure_ball z₀ hR.ne'])
  rcases le_or_gt 0 M with hM | hM
  · -- Divide the sphere bound by `‖P u‖ ≥ ‖P z₀‖`.
    refine hmax (fun u hu ↦ ?_) hw
    have h1 := hPG u hu
    rw [norm_mul, norm_mul] at h1
    have h2 : M * (‖P z₀‖ * ‖G z₀‖) ≤ M * (‖P u‖ * ‖G z₀‖) := by gcongr; exact hP u hu
    exact le_of_mul_le_mul_left (h1.trans (h2.trans_eq (by ring))) (norm_pos_iff.2 (hP₀ u hu))
  · -- For `M < 0` the sphere bound forces `G = 0` on the sphere, hence on the whole disc.
    have h0 (u : ℂ) (hu : u ∈ sphere z₀ R) : ‖G u‖ ≤ 0 := by
      have h1 := hPG u hu
      rw [norm_mul, norm_mul] at h1
      have hPu : 0 < ‖P u‖ := norm_pos_iff.2 (hP₀ u hu)
      have hrhs : M * (‖P z₀‖ * ‖G z₀‖) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hM.le (by positivity)
      by_contra! h
      linarith [mul_pos hPu h]
    have hz₀ : ‖G z₀‖ ≤ 0 := hmax h0 (mem_closedBall_self hR.le)
    have : ‖G z₀‖ = 0 := le_antisymm hz₀ (norm_nonneg _)
    rw [this, mul_zero]
    exact hmax h0 hw

/-- Under a relative sphere bound, a nonzero value on the closed disc forces the central
value to be nonzero. The radius and bound are arbitrary real numbers; no completeness of
the complex normed target is required. -/
theorem DiffContOnCl.ne_zero_of_forall_mem_sphere_norm_le_mul {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] {f : ℂ → F} (hf : DiffContOnCl ℂ f (ball z₀ R))
    (hM : ∀ w ∈ sphere z₀ R, ‖f w‖ ≤ M * ‖f z₀‖) {z : ℂ}
    (hz : z ∈ closedBall z₀ R) (hfz : f z ≠ 0) : f z₀ ≠ 0 := by
  by_cases hR : 0 < R
  · intro hzero
    have hbound := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hf
      (by rwa [frontier_ball z₀ hR.ne']) (by rwa [closure_ball z₀ hR.ne'])
    rw [hzero, norm_zero, mul_zero] at hbound
    exact hfz (norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _)))
  · have hzz : z = z₀ := dist_le_zero.mp ((mem_closedBall.mp hz).trans (le_of_not_gt hR))
    simpa only [hzz] using hfz

/-- The norm of a function that is continuous on a sphere of a proper space is bounded there:
the family `w ↦ ‖f w‖` indexed by the sphere is bounded above. This is the hypothesis of
`le_ciSup` for the supremum `⨆ w : sphere x r, ‖f w‖`. -/
theorem ContinuousOn.bddAbove_range_norm_sphere {α F : Type*} [PseudoMetricSpace α]
    [ProperSpace α] [SeminormedAddGroup F] {f : α → F} {x : α} {r : ℝ}
    (hf : ContinuousOn f (sphere x r)) : BddAbove (range fun w : sphere x r => ‖f w‖) := by
  rw [← image_eq_range (fun w => ‖f w‖) (sphere x r)]
  exact (isCompact_sphere x r).bddAbove_image hf.norm

/-- The maximum modulus principle on a closed disc, in terms of the supremum over the boundary
circle: if `f` is differentiable on `ball z₀ R` and continuous on its closure, then `‖f z‖` is at
most the supremum of `‖f‖` over `sphere z₀ R` for every `z` in `closedBall z₀ R`. For `R ≠ 0` this
is Mathlib's `Complex.norm_le_of_forall_mem_frontier_norm_le` on the ball, whose frontier is the
sphere; for `R = 0` the closed disc and the sphere are both `{z₀}`. -/
theorem DiffContOnCl.norm_le_iSup_norm_sphere_of_mem_closedBall {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] {f : ℂ → F} (hf : DiffContOnCl ℂ f (ball z₀ R))
    {z : ℂ} (hz : z ∈ closedBall z₀ R) : ‖f z‖ ≤ ⨆ w : sphere z₀ R, ‖f w‖ := by
  have hbdd := (hf.continuousOn_ball.mono sphere_subset_closedBall).bddAbove_range_norm_sphere
  rcases eq_or_ne R 0 with rfl | hR
  · rw [closedBall_zero, mem_singleton_iff] at hz
    exact le_ciSup hbdd ⟨z, by rw [hz, sphere_zero]; exact mem_singleton z₀⟩
  · refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hf (fun w hw => ?_)
      (by rwa [closure_ball z₀ hR])
    rw [frontier_ball z₀ hR] at hw
    exact le_ciSup hbdd ⟨w, hw⟩

/-! ### Finitely many exceptional boundary points -/

open Complex Filter Topology

private theorem natCast_mul_re (n : ℕ) (z : ℂ) : ((n : ℂ) * z).re = n * z.re := by simp

/-- The auxiliary function `P w * exp (n * f w)` of the maximum principle with finitely many
exceptional points, where `P` is entire and vanishes on the finite set `F`, is differentiable on
`U` and continuous on `closure U`, when `f` is continuous on `closure U \ F` and `re ∘ f` is
bounded above there: at a point of `F` the factor `P` vanishes and the exponential stays bounded. -/
private theorem diffContOnCl_mul_exp {f P : ℂ → ℂ} {U F : Set ℂ} (hF : F.Finite)
    (hd : DifferentiableOn ℂ f U) (hc : ContinuousOn f (closure U \ F)) {M : ℝ}
    (hre : ∀ w ∈ closure U \ F, (f w).re ≤ M) (hPd : Differentiable ℂ P)
    (hP0 : ∀ w ∈ F, P w = 0) (n : ℕ) :
    DiffContOnCl ℂ (fun w => P w * cexp (n * f w)) U := by
  refine ⟨hPd.differentiableOn.mul (hd.const_mul _).cexp, fun w hw => ?_⟩
  by_cases hwF : w ∈ F
  · -- `‖P‖ * exp (n M)` dominates the function on the closure and tends to `0` at `w`
    have hdom (v : ℂ) (hv : v ∈ closure U) :
        ‖P v * cexp (n * f v)‖ ≤ ‖P v‖ * Real.exp (n * M) := by
      simp only [norm_mul, norm_exp, natCast_mul_re]
      by_cases hvF : v ∈ F
      · simp [hP0 v hvF]
      · gcongr
        exact hre v ⟨hv, hvF⟩
    have hlim : Tendsto (fun v => ‖P v‖ * Real.exp (n * M)) (𝓝[closure U] w) (𝓝 0) := by
      simpa [hP0 w hwF] using
        ((hPd.continuous.norm.tendsto w).mul_const _).mono_left nhdsWithin_le_nhds
    have : Tendsto (fun v => P v * cexp (n * f v)) (𝓝[closure U] w) (𝓝 0) :=
      squeeze_zero_norm' (eventually_nhdsWithin_of_forall hdom) hlim
    rwa [ContinuousWithinAt, hP0 w hwF, zero_mul]
  · exact ((hPd.continuous.continuousWithinAt.mul
      ((hc w ⟨hw, hwF⟩).const_mul _).cexp)).mono_of_mem_nhdsWithin
      (inter_mem_nhdsWithin _ (hF.isClosed.isOpen_compl.mem_nhds hwF))

/-- **Maximum principle for the real part with finitely many exceptional boundary points.** Let
`f` be complex differentiable on a bounded set `U` and continuous on its closure away from a finite
set `F`. If `re ∘ f` is bounded above on `U` and nonpositive on `frontier U \ F`, then it is
nonpositive on `closure U \ F`.

The bound on `U` cannot be dropped: on the unit disc the real part of `(1 + z) / (1 - z)` is
positive, although it vanishes on the unit circle away from `1`. The proof applies the maximum
modulus principle to `(∏ c ∈ F, (w - c)) * exp (n * f w)` and lets `n` tend to infinity. -/
theorem Complex.re_nonpos_of_forall_mem_frontier_diff_re_nonpos {f : ℂ → ℂ} {U F : Set ℂ}
    (hU : Bornology.IsBounded U) (hF : F.Finite) (hd : DifferentiableOn ℂ f U)
    (hc : ContinuousOn f (closure U \ F)) (hb : BddAbove ((fun z => (f z).re) '' U))
    (hfr : ∀ z ∈ frontier U \ F, (f z).re ≤ 0) {z : ℂ} (hz : z ∈ closure U \ F) :
    (f z).re ≤ 0 := by
  rcases (closure_eq_self_union_frontier U ▸ hz.1 : z ∈ U ∪ frontier U) with hzU | hzfr
  swap
  · exact hfr z ⟨hzfr, hz.2⟩
  obtain ⟨M, hM⟩ := hb
  -- `re ∘ f` is at most `max M 0` on the closure, away from `F`
  have hre (w : ℂ) (hw : w ∈ closure U \ F) : (f w).re ≤ max M 0 := by
    rcases (closure_eq_self_union_frontier U ▸ hw.1 : w ∈ U ∪ frontier U) with hwU | hwfr
    · exact (hM ⟨w, hwU, rfl⟩).trans (le_max_left _ _)
    · exact (hfr w ⟨hwfr, hw.2⟩).trans (le_max_right _ _)
  set P : ℂ → ℂ := fun w => ∏ c ∈ hF.toFinset, (w - c)
  have hPd : Differentiable ℂ P := by fun_prop
  have hP0 (w : ℂ) (hw : w ∈ F) : P w = 0 :=
    Finset.prod_eq_zero (hF.mem_toFinset.mpr hw) (sub_self w)
  have hPz : P z ≠ 0 := Finset.prod_ne_zero_iff.mpr fun c hc =>
    sub_ne_zero.mpr fun h => hz.2 (h ▸ hF.mem_toFinset.mp hc)
  obtain ⟨B, hB⟩ := hU.isCompact_closure.exists_bound_of_continuousOn hPd.continuous.continuousOn
  -- the maximum modulus principle bounds `‖P z‖ * exp (n * re (f z))` by `B` for every `n`
  have hbound (n : ℕ) : ‖P z‖ * Real.exp (n * (f z).re) ≤ B := by
    have := Complex.norm_le_of_forall_mem_frontier_norm_le hU
      (diffContOnCl_mul_exp hF hd hc hre hPd hP0 n) (C := B) (fun w hw => ?_) (subset_closure hzU)
    · simpa only [norm_mul, norm_exp, natCast_mul_re] using this
    simp only [norm_mul, norm_exp, natCast_mul_re]
    by_cases hwF : w ∈ F
    · simpa [hP0 w hwF] using (norm_nonneg _).trans (hB z hz.1)
    · calc ‖P w‖ * Real.exp (n * (f w).re) ≤ ‖P w‖ * 1 := by
            gcongr
            exact Real.exp_le_one_iff.mpr
              (mul_nonpos_of_nonneg_of_nonpos n.cast_nonneg (hfr w ⟨hw, hwF⟩))
        _ ≤ B := by simpa using hB w (frontier_subset_closure hw)
  by_contra! hpos
  have hPpos : 0 < ‖P z‖ := norm_pos_iff.mpr hPz
  obtain ⟨n, hn⟩ := exists_nat_gt (B / (‖P z‖ * (f z).re))
  rw [div_lt_iff₀ (mul_pos hPpos hpos)] at hn
  have hexp := Real.add_one_le_exp (n * (f z).re)
  nlinarith [hbound n, mul_le_mul_of_nonneg_left hexp hPpos.le]

/-- **Holomorphic functions whose imaginary parts agree on the frontier differ by a real
constant.** Let `u` and `v` be complex differentiable on a bounded, preconnected open set `U` and
continuous on its closure away from a finite set `F`. If the difference of their imaginary parts is
bounded on `U` and vanishes on `frontier U \ F`, then `u` and `v` differ by a real constant on
`closure U \ F`. -/
theorem Complex.exists_eqOn_add_ofReal_of_forall_mem_frontier_im_eq {u v : ℂ → ℂ} {U F : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUb : Bornology.IsBounded U) (hF : F.Finite)
    (hu : DifferentiableOn ℂ u U) (hv : DifferentiableOn ℂ v U)
    (huc : ContinuousOn u (closure U \ F)) (hvc : ContinuousOn v (closure U \ F))
    (hb : Bornology.IsBounded ((fun z => (u z).im - (v z).im) '' U))
    (him : ∀ z ∈ frontier U \ F, (u z).im = (v z).im) :
    ∃ c : ℝ, EqOn u (fun z => v z + c) (closure U \ F) := by
  rcases U.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, by simp⟩
  -- `re (± I (u - v)) = ∓ (im u - im v)` satisfies the maximum principle on both sides
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
  have hside (ε : ℂ) (hε : ε = I ∨ ε = -I) (z : ℂ) (hz : z ∈ closure U \ F) :
      (ε * (u z - v z)).re ≤ 0 := by
    have hre (w : ℂ) : (ε * (u w - v w)).re = ε.im * -((u w).im - (v w).im) := by
      rcases hε with rfl | rfl <;> simp
    have hε1 : |ε.im| = 1 := by rcases hε with rfl | rfl <;> simp
    refine Complex.re_nonpos_of_forall_mem_frontier_diff_re_nonpos hUb hF
      ((hu.sub hv).const_mul ε) ((huc.sub hvc).const_mul ε) ⟨C, ?_⟩ (fun w hw => ?_) hz
    · rintro _ ⟨w, hw, rfl⟩
      simp only [Pi.sub_apply]
      rw [hre]
      have := hC _ ⟨w, hw, rfl⟩
      rw [Real.norm_eq_abs] at this
      calc ε.im * -((u w).im - (v w).im) ≤ |ε.im * -((u w).im - (v w).im)| := le_abs_self _
        _ = |(u w).im - (v w).im| := by rw [abs_mul, hε1, abs_neg, one_mul]
        _ ≤ C := this
    · simp only [Pi.sub_apply]
      rw [hre, him w hw, sub_self, neg_zero, mul_zero]
  have hdiff (z : ℂ) (hz : z ∈ closure U \ F) : (u z).im = (v z).im := by
    have h1 := hside I (.inl rfl) z hz
    have h2 := hside (-I) (.inr rfl) z hz
    simp at h1 h2
    linarith
  -- the imaginary parts agree on `U`, since `U \ F` is dense in `U`
  have hcont : ContinuousOn (fun z => (u z).im - (v z).im) U :=
    (continuous_im.comp_continuousOn hu.continuousOn).sub
      (continuous_im.comp_continuousOn hv.continuousOn)
  have hdense : U ⊆ closure (U ∩ Fᶜ) :=
    (hF.countable.dense_compl ℂ).open_subset_closure_inter hUo
  have hU0 : EqOn (fun z => (u z).im - (v z).im) 0 U :=
    EqOn.of_subset_closure (s := U ∩ Fᶜ)
      (fun z hz => sub_eq_zero.mpr (hdiff z ⟨subset_closure hz.1, hz.2⟩)) hcont continuousOn_const
      inter_subset_left hdense
  obtain ⟨c, hc⟩ := ((hu.sub hv).analyticOnNhd hUo).eq_const_add_im_mul_I_of_re_eq_const
    (c₀ := 0) (fun z hz => by simpa using hU0 hz) hUo ⟨hne, hUc⟩
  refine ⟨c, EqOn.of_subset_closure (s := U ∩ Fᶜ) (fun z hz => ?_) huc
    (hvc.add continuousOn_const) (fun z hz => ⟨subset_closure hz.1, hz.2⟩) fun z hz => ?_⟩
  · have := hc z hz.1
    simp only [Pi.sub_apply, ofReal_zero, zero_mul, add_zero] at this
    simp [← this]
  · rw [inter_comm]
    exact hF.isClosed.isOpen_compl.inter_closure ⟨hz.2, hz.1⟩
