/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Meromorphic.TrailingCoefficient
public import TauCeti.Analysis.Complex.Laurent.Basic

/-!
# The residue at an isolated singularity

For `f : ℂ → E` valued in a complex Banach space and `z₀ : ℂ`, the **residue**
`TauCeti.Contour.residue f z₀` is the order-`(−1)` Laurent coefficient of `f` at `z₀` — the
quantity summed in Cauchy's residue theorem. It is defined at every isolated singularity of `f`,
that is wherever `f` is complex differentiable on a punctured neighbourhood of `z₀`, whether the
singularity is removable, a pole or essential: it is the circle Laurent coefficient
`TauCeti.circleLaurentCoeff f z₀ r (-1) = (2πi)⁻¹ ∮_{|z − z₀| = r} f z dz` of any circle in that
neighbourhood, a value that does not depend on `r` by Cauchy's theorem on annuli.

At a pole it is computed from any presentation `f z = (z − z₀) ^ n • g z` near `z₀` with `g`
analytic and `n ≤ −1`: it is the Taylor coefficient `((−1 − n)!)⁻¹ • iteratedDeriv (−1 − n) g z₀`
of `g`. It is `0` where `f` is analytic, and at a **simple pole** it is the leading Laurent
coefficient `meromorphicTrailingCoeffAt f z₀ = lim_{z→z₀} (z − z₀) • f z`.

As an unconditional value it is junk (`0`) when `f` is not differentiable on any punctured
neighbourhood of `z₀`, and also when `E` is not complete, where every circle integral is `0`. This
follows `MeasureTheory.integral`, which is likewise `0` for an incomplete codomain.

## Main definitions

* `TauCeti.Contour.residue` — the residue of `f` at `z₀`.

## Main results

* `TauCeti.Contour.residue_eq_circleLaurentCoeff`, `TauCeti.Contour.residue_eq_circleIntegral` —
  the residue is `(2πi)⁻¹ ∮_{|z − z₀| = r} f z dz` for every `r > 0` such that `f` is
  differentiable on the punctured closed disc of radius `r` about `z₀`.
* `TauCeti.Contour.residue_eq_of_eventuallyEq_zpow_smul` — the value at a pole, from any
  presentation `f =ᶠ[𝓝[≠] z₀] (· − z₀) ^ n • g` with `g` analytic and `n ≤ −1`; the exponent `n`
  need not be the meromorphic order of `f`.
* `TauCeti.Contour.residue_add`, `TauCeti.Contour.residue_sub`, `TauCeti.Contour.residue_sum` —
  additivity of the residue over functions differentiable on a punctured neighbourhood of `z₀`,
  including finite sums. The hypotheses are essential: two functions without an isolated
  singularity at `z₀` can sum to one with a pole there.
* `TauCeti.Contour.residue_const_smul` and `TauCeti.Contour.residue_const_mul` — homogeneity, in
  the unapplied and (scalar) applied forms. These are unconditional, the junk value scaling
  correctly.
* `TauCeti.Contour.residue_congr_nhdsNE` — the residue depends only on the germ of `f` on a
  punctured neighborhood of `z₀`.
* `TauCeti.Contour.residue_eq_zero_of_analyticAt` and
  `TauCeti.Contour.residue_eq_zero_of_meromorphicOrderAt_nonneg` — the residue vanishes where `f`
  is analytic, or meromorphic of nonnegative order.
* `TauCeti.Contour.residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one` — at a simple pole the
  residue is the leading Laurent (trailing) coefficient.
* `TauCeti.Contour.residue_div_sub_pow_of_analyticAt` — the Cauchy-kernel computation
  `Res_{z₀} (g / (· − z₀) ^ (k + 1)) = g^{(k)}(z₀) / k !` for `g : ℂ → ℂ` analytic at `z₀`.
* `TauCeti.Contour.residue_zero_cpow_smul_of_eventually_ne_zero`,
  `TauCeti.Contour.residue_zero_cpow_smul`, `TauCeti.Contour.residue_zero_cpow_neg_smul`,
  `TauCeti.Contour.residue_zero_cpow_mul`, `TauCeti.Contour.residue_zero_cpow_neg_mul` —
  vanishing of the residue when multiplying by `(0 : ℂ) ^ g z` for an exponent nonzero on a
  punctured neighborhood (in particular `(0 : ℂ) ^ z` and `(0 : ℂ) ^ (-z)`).

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (the residue material of
`ForMathlib/GeneralizedResidueTheory/Residue.lean` and
`ForMathlib/GeneralizedResidueTheory/Residue/GeneralizedTheoremBase.lean`), reformulated for raw
functions `ℂ → E`, and defined through the circle Laurent coefficients of
`TauCeti.Analysis.Complex.Laurent.Basic` so that it covers every isolated singularity.

## References

* J. B. Conway, *Functions of One Complex Variable I*, Chapter V, §1 and §2.
* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997.
-/

public section

noncomputable section

open Filter Topology Set Metric Complex

open scoped Real

namespace TauCeti.Contour

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The **residue** of `f` at `z₀`. If `f` is complex differentiable on a punctured neighbourhood
of `z₀`, it is the value, for small `r > 0`, of the order-`(−1)` circle Laurent coefficient
`circleLaurentCoeff f z₀ r (-1) = (2πi)⁻¹ ∮_{|z − z₀| = r} f z dz`, which does not depend on such
`r` (`residue_eq_circleLaurentCoeff`); otherwise it is `0`. -/
noncomputable def residue (f : ℂ → E) (z₀ : ℂ) : E :=
  haveI := Classical.propDecidable (∀ᶠ z in 𝓝[≠] z₀, DifferentiableAt ℂ f z)
  if ∀ᶠ z in 𝓝[≠] z₀, DifferentiableAt ℂ f z then
    limUnder (𝓝[>] (0 : ℝ)) fun r ↦ circleLaurentCoeff f z₀ r (-1)
  else 0

/-- **The residue is the order-`(−1)` Laurent coefficient of any small circle.** If `f` is
differentiable on the punctured closed disc of radius `r > 0` about `z₀`, its residue at `z₀` is
`circleLaurentCoeff f z₀ r (-1)`. -/
theorem residue_eq_circleLaurentCoeff {f : ℂ → E} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (closedBall z₀ r \ {z₀})) :
    residue f z₀ = circleLaurentCoeff f z₀ r (-1) := by
  have hev : ∀ᶠ z in 𝓝[≠] z₀, DifferentiableAt ℂ f z := by
    filter_upwards [sdiff_mem_nhdsWithin_compl (ball_mem_nhds z₀ hr) {z₀}] with z hz
    exact (hf.mono (sdiff_subset_sdiff_left ball_subset_closedBall)).differentiableAt
      ((isOpen_ball.sdiff isClosed_singleton).mem_nhds hz)
  rw [residue, ite_eq_left hev]
  refine Tendsto.limUnder_eq (tendsto_const_nhds.congr' ?_)
  filter_upwards [Ioc_mem_nhdsGT hr] with ρ hρ
  have hz₀ : z₀ ∈ ball z₀ ρ := mem_ball_self hρ.1
  refine circleLaurentCoeff_eq_of_differentiable_on_annulus_off_countable hρ.1 hρ.2
    countable_empty (hf.continuousOn.mono fun z hz ↦ ⟨hz.1, fun h ↦ hz.2 ?_⟩) (fun z hz ↦ ?_) (-1)
  · rwa [mem_singleton_iff.1 h]
  · refine (hf.mono (sdiff_subset_sdiff_left ball_subset_closedBall)).differentiableAt
      ((isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hz.1.1, fun h ↦ hz.1.2 ?_⟩)
    rw [mem_singleton_iff.1 h]
    exact mem_closedBall_self hρ.1.le

/-- **The residue as a circle integral.** If `f` is differentiable on the punctured closed disc of
radius `r > 0` about `z₀`, its residue at `z₀` is `(2πi)⁻¹ ∮_{|z − z₀| = r} f z dz`. -/
theorem residue_eq_circleIntegral {f : ℂ → E} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (closedBall z₀ r \ {z₀})) :
    residue f z₀ = (2 * π * I : ℂ)⁻¹ • ∮ z in C(z₀, r), f z := by
  rw [residue_eq_circleLaurentCoeff hr hf, circleLaurentCoeff_def]
  simp

/-- Where `f` is not differentiable on any punctured neighbourhood of `z₀`, its residue is `0` by
definition. -/
@[simp]
theorem residue_of_not_eventually_differentiableAt {f : ℂ → E} {z₀ : ℂ}
    (h : ¬ ∀ᶠ z in 𝓝[≠] z₀, DifferentiableAt ℂ f z) : residue f z₀ = 0 := by
  rw [residue, ite_eq_right h]

/-- If `E` is not complete, the residue of any `f : ℂ → E` is `0`: every circle integral vanishes.
-/
@[simp]
theorem residue_of_not_completeSpace (hE : ¬ CompleteSpace E) (f : ℂ → E) (z₀ : ℂ) :
    residue f z₀ = 0 := by
  have h0 : (fun r : ℝ ↦ circleLaurentCoeff f z₀ r (-1)) = fun _ ↦ 0 := by
    funext r
    simp [circleLaurentCoeff_def, circleIntegral, intervalIntegral,
      MeasureTheory.integral_of_not_completeSpace hE]
  rw [residue]
  split_ifs
  · rw [h0]
    exact tendsto_const_nhds.limUnder_eq
  · rfl

/-- **Characteristic value of the residue at a pole.** If `f z = (z − z₀) ^ n • g z` on a punctured
neighbourhood of `z₀` with `g` analytic at `z₀` and `n ≤ −1`, then the residue is the Taylor
coefficient `((−1 − n)!)⁻¹ • iteratedDeriv (−1 − n) g z₀`. The exponent need not be the
meromorphic order of `f`: `g` may vanish at `z₀`, and only when its vanishing order is at least
`-n` is `f` analytic (residue `0`). -/
theorem residue_eq_of_eventuallyEq_zpow_smul [CompleteSpace E] {f g : ℂ → E} {z₀ : ℂ} {n : ℤ}
    (hn : n ≤ -1) (hg : AnalyticAt ℂ g z₀) (hfg : f =ᶠ[𝓝[≠] z₀] fun z ↦ (z - z₀) ^ n • g z) :
    residue f z₀ = ((-1 - n).toNat.factorial : ℂ)⁻¹ • iteratedDeriv (-1 - n).toNat g z₀ := by
  -- A punctured closed disc on which `f` is the presentation and `g` is differentiable.
  obtain ⟨R, hR, hgR⟩ := hg.exists_ball_analyticOnNhd
  obtain ⟨r, hr, hfr⟩ := (nhdsWithin_hasBasis nhds_basis_closedBall _).eventually_iff.1 hfg
  have hρ : 0 < min r (R / 2) := lt_min hr (half_pos hR)
  have hgρ : DifferentiableOn ℂ g (closedBall z₀ (min r (R / 2))) := fun z hz ↦
    (hgR z (mem_ball.2 ((mem_closedBall.1 hz).trans_lt
      ((min_le_right _ _).trans_lt (half_lt_self hR))))).differentiableAt.differentiableWithinAt
  have heq : EqOn f (fun z ↦ (z - z₀) ^ n • g z) (closedBall z₀ (min r (R / 2)) \ {z₀}) :=
    fun z hz ↦ hfr ⟨closedBall_subset_closedBall (min_le_left _ _) hz.1, hz.2⟩
  have hf : DifferentiableOn ℂ f (closedBall z₀ (min r (R / 2)) \ {z₀}) :=
    DifferentiableOn.congr (fun z hz ↦ ((((differentiableAt_id.sub_const z₀).zpow
      (Or.inl (sub_ne_zero.2 hz.2))).differentiableWithinAt).smul
        ((hgρ z hz.1).mono sdiff_subset))) heq
  obtain ⟨m, hm⟩ : ∃ m : ℕ, -1 - n = m := ⟨(-1 - n).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  rw [residue_eq_circleLaurentCoeff hρ hf, circleLaurentCoeff_congr hρ.le
    (fun z hz ↦ heq ⟨sphere_subset_closedBall hz, ne_of_mem_sphere hz hρ.ne'⟩),
    circleLaurentCoeff_sub_zpow_smul_apply, hm, Int.toNat_natCast,
    hgρ.circleLaurentCoeff_natCast_eq_iteratedDeriv hρ]

/-- The residue vanishes where `f` is analytic. -/
@[simp]
theorem residue_eq_zero_of_analyticAt {f : ℂ → E} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) :
    residue f z₀ = 0 := by
  by_cases hE : CompleteSpace E
  swap
  · exact residue_of_not_completeSpace hE f z₀
  have hfg : f =ᶠ[𝓝[≠] z₀] fun z ↦ (z - z₀) ^ (-1 : ℤ) • ((z - z₀) • f z) :=
    eventually_mem_nhdsWithin.mono fun z hz ↦ by
      dsimp only
      rw [smul_smul, zpow_neg_one, inv_mul_cancel₀ (sub_ne_zero.2 hz), one_smul]
  rw [residue_eq_of_eventuallyEq_zpow_smul le_rfl (by fun_prop) hfg]
  simp

/-- The residue depends only on the germ of `f` on a punctured neighborhood of `z₀`: functions
agreeing near (but not necessarily at) `z₀` have the same residue. -/
theorem residue_congr_nhdsNE {f g : ℂ → E} {z₀ : ℂ} (h : f =ᶠ[𝓝[≠] z₀] g) :
    residue f z₀ = residue g z₀ := by
  -- Near each point of a punctured neighbourhood the two functions agree on a whole neighbourhood.
  have hloc : ∀ᶠ z in 𝓝[≠] z₀, f =ᶠ[𝓝 z] g := eventually_nhdsNE_eventually_nhds_iff.mpr h
  have hdiff : (∀ᶠ z in 𝓝[≠] z₀, DifferentiableAt ℂ f z) ↔
      ∀ᶠ z in 𝓝[≠] z₀, DifferentiableAt ℂ g z :=
    ⟨fun hf ↦ (hf.and hloc).mono fun _ hz ↦ hz.1.congr_of_eventuallyEq hz.2.symm,
      fun hg ↦ (hg.and hloc).mono fun _ hz ↦ hz.1.congr_of_eventuallyEq hz.2⟩
  by_cases hf : ∀ᶠ z in 𝓝[≠] z₀, DifferentiableAt ℂ f z
  · obtain ⟨r, hr, hr'⟩ :=
      (nhdsWithin_hasBasis nhds_basis_closedBall _).eventually_iff.1 ((hf.and (hdiff.1 hf)).and h)
    rw [residue_eq_circleLaurentCoeff hr fun z hz ↦ (hr' hz).1.1.differentiableWithinAt,
      residue_eq_circleLaurentCoeff hr fun z hz ↦ (hr' hz).1.2.differentiableWithinAt]
    exact circleLaurentCoeff_congr hr.le
      (fun z hz ↦ (hr' ⟨sphere_subset_closedBall hz, ne_of_mem_sphere hz hr.ne'⟩).2) _
  · rw [residue_of_not_eventually_differentiableAt hf,
      residue_of_not_eventually_differentiableAt (hdiff.not.1 hf)]

/-- Any meromorphic `f` admits an analytic presentation `f z = (z − z₀) ^ m • φ z` near `z₀` at any
exponent `m` at or below its meromorphic order (padding the reduced presentation with a nonnegative
power of `z − z₀`). The factor `φ` is analytic but may vanish at `z₀` when `m` is strictly below the
order. This is the factorisation entry point for the canonical Laurent data
(`MeromorphicLaurent.lean`). -/
lemma exists_analyticAt_eventuallyEq_zpow_smul {f : ℂ → E} {z₀ : ℂ} {m : ℤ}
    (hf : MeromorphicAt f z₀) (hm : (m : WithTop ℤ) ≤ meromorphicOrderAt f z₀) :
    ∃ φ : ℂ → E, AnalyticAt ℂ φ z₀ ∧ f =ᶠ[𝓝[≠] z₀] fun z ↦ (z - z₀) ^ m • φ z := by
  rcases eq_or_ne (meromorphicOrderAt f z₀) ⊤ with htop | htop
  · refine ⟨fun _ ↦ 0, analyticAt_const, ?_⟩
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 htop] with z hz
    simp [hz]
  · obtain ⟨g₀, hg₀_an, -, hf_eq⟩ := (meromorphicOrderAt_ne_top_iff hf).1 htop
    set a := (meromorphicOrderAt f z₀).untop₀
    have hma : m ≤ a := by rwa [← WithTop.coe_le_coe, WithTop.coe_untop₀_of_ne_top htop]
    refine ⟨fun z ↦ (z - z₀) ^ (a - m).toNat • g₀ z, by fun_prop, ?_⟩
    filter_upwards [hf_eq, self_mem_nhdsWithin] with z hz1 hz2
    rw [hz1, smul_smul, ← zpow_natCast, ← zpow_add₀ (sub_ne_zero.mpr hz2),
      Int.toNat_of_nonneg (by omega), add_sub_cancel]

/-- The residue vanishes where `f` is meromorphic of nonnegative order (in particular where `f` is
analytic): there is no order-`(−1)` Laurent coefficient. -/
@[simp]
theorem residue_eq_zero_of_meromorphicOrderAt_nonneg {f : ℂ → E} {z₀ : ℂ}
    (hf : MeromorphicAt f z₀) (h : 0 ≤ meromorphicOrderAt f z₀) : residue f z₀ = 0 := by
  obtain ⟨φ, hφ, hfφ⟩ := exists_analyticAt_eventuallyEq_zpow_smul (m := 0) hf (by simpa using h)
  have hfφ' : f =ᶠ[𝓝[≠] z₀] φ := hfφ.mono fun z hz ↦ by simpa using hz
  rw [residue_congr_nhdsNE hfφ', residue_eq_zero_of_analyticAt hφ]

/-- At a **simple pole** (`meromorphicOrderAt f z₀ = −1`), the residue is the leading Laurent
coefficient `meromorphicTrailingCoeffAt f z₀`, i.e. `lim_{z→z₀} (z − z₀) • f z`: the Taylor
coefficient at index `−1 − (−1) = 0` of the analytic part `g` is just `g z₀`, which is the trailing
coefficient. -/
@[simp]
theorem residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one [CompleteSpace E] {f : ℂ → E}
    {z₀ : ℂ} (hord : meromorphicOrderAt f z₀ = -1) :
    residue f z₀ = meromorphicTrailingCoeffAt f z₀ := by
  have hf : MeromorphicAt f z₀ :=
    meromorphicAt_of_meromorphicOrderAt_ne_zero (by rw [hord]; decide)
  obtain ⟨g, hg, -, hfg⟩ := (meromorphicOrderAt_ne_top_iff hf).1 (by rw [hord]; decide)
  rw [hg.meromorphicTrailingCoeffAt_of_eq_nhdsNE hfg]
  have huntop : (meromorphicOrderAt f z₀).untop₀ = -1 := by rw [hord]; rfl
  rw [huntop] at hfg
  rw [residue_eq_of_eventuallyEq_zpow_smul le_rfl hg hfg]
  simp

/-- **Additivity of the residue.** The residue is additive on functions differentiable on a
punctured neighbourhood of `z₀`, such as functions meromorphic at `z₀`.

No completeness hypothesis is needed: for an incomplete `E` every residue is the junk value `0`. -/
@[simp]
theorem residue_add {f g : ℂ → E} {z₀ : ℂ} (hf : ∀ᶠ z in 𝓝[≠] z₀, DifferentiableAt ℂ f z)
    (hg : ∀ᶠ z in 𝓝[≠] z₀, DifferentiableAt ℂ g z) :
    residue (f + g) z₀ = residue f z₀ + residue g z₀ := by
  obtain ⟨r, hr, hfg⟩ := (nhdsWithin_hasBasis nhds_basis_closedBall _).eventually_iff.1 (hf.and hg)
  have hfr : DifferentiableOn ℂ f (closedBall z₀ r \ {z₀}) :=
    fun z hz ↦ (hfg hz).1.differentiableWithinAt
  have hgr : DifferentiableOn ℂ g (closedBall z₀ r \ {z₀}) :=
    fun z hz ↦ (hfg hz).2.differentiableWithinAt
  have hsph : sphere z₀ r ⊆ closedBall z₀ r \ {z₀} :=
    fun z hz ↦ ⟨sphere_subset_closedBall hz, ne_of_mem_sphere hz hr.ne'⟩
  rw [residue_eq_circleLaurentCoeff hr (hfr.add hgr), residue_eq_circleLaurentCoeff hr hfr,
    residue_eq_circleLaurentCoeff hr hgr]
  exact circleLaurentCoeff_add ((hfr.continuousOn.mono hsph).circleIntegrable hr.le)
    ((hgr.continuousOn.mono hsph).circleIntegrable hr.le) (-1)

/-- **Scaling of the residue.** The residue commutes with scalar multiplication.

No hypothesis is needed: the identity holds for every `f`, through the junk value where `f` is not
differentiable on a punctured neighbourhood of `z₀` or `E` is not complete. Contrast
`residue_add`, whose hypotheses are essential. -/
@[simp]
theorem residue_const_smul {f : ℂ → E} {z₀ : ℂ} (c : ℂ) :
    residue (c • f) z₀ = c • residue f z₀ := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [zero_smul, zero_smul]
    exact residue_eq_zero_of_analyticAt analyticAt_const
  by_cases hf : ∀ᶠ z in 𝓝[≠] z₀, DifferentiableAt ℂ f z
  · obtain ⟨r, hr, hfr⟩ := (nhdsWithin_hasBasis nhds_basis_closedBall _).eventually_iff.1 hf
    have hfr : DifferentiableOn ℂ f (closedBall z₀ r \ {z₀}) :=
      fun z hz ↦ (hfr hz).differentiableWithinAt
    rw [residue_eq_circleLaurentCoeff hr (hfr.const_smul c), residue_eq_circleLaurentCoeff hr hfr]
    exact circleLaurentCoeff_smul c f z₀ r (-1)
  · have hcf : ¬ ∀ᶠ z in 𝓝[≠] z₀, DifferentiableAt ℂ (c • f) z := fun h ↦ hf (h.mono fun z hz ↦ by
      simpa [smul_smul, inv_mul_cancel₀ hc] using hz.const_smul c⁻¹)
    rw [residue_of_not_eventually_differentiableAt hcf,
      residue_of_not_eventually_differentiableAt hf, smul_zero]

/-- **Scaling of the residue (applied `*`).** Scaling a scalar function `f` by a constant scales its
residue by that constant; the applied companion to `residue_const_smul`. -/
@[simp]
theorem residue_const_mul {f : ℂ → ℂ} {z₀ : ℂ} (c : ℂ) :
    residue (fun z ↦ c * f z) z₀ = c * residue f z₀ :=
  -- `fun z ↦ c * f z` is `c • f` by `Pi.smul_apply` and `smul_eq_mul`, both definitional.
  residue_const_smul c

/-- **Subtractivity of the residue.** The residue distributes over subtraction of functions
differentiable on a punctured neighbourhood of `z₀`; the `−1` scaling case of `residue_add` and
`residue_const_smul`. -/
@[simp]
theorem residue_sub {f g : ℂ → E} {z₀ : ℂ} (hf : ∀ᶠ z in 𝓝[≠] z₀, DifferentiableAt ℂ f z)
    (hg : ∀ᶠ z in 𝓝[≠] z₀, DifferentiableAt ℂ g z) :
    residue (f - g) z₀ = residue f z₀ - residue g z₀ := by
  rw [sub_eq_add_neg, residue_add hf (hg.mono fun _ h ↦ h.neg), ← neg_one_smul ℂ g,
    residue_const_smul, neg_one_smul, sub_eq_add_neg]

/-- **The residue of a finite sum.** For a finite family of functions differentiable on a
punctured neighbourhood of `z₀`, the residue of the sum is the sum of the residues — the form
consumed by the residue theorem. -/
@[simp]
theorem residue_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → E} {z₀ : ℂ}
    (hf : ∀ i ∈ s, ∀ᶠ z in 𝓝[≠] z₀, DifferentiableAt ℂ (f i) z) :
    residue (∑ i ∈ s, f i) z₀ = ∑ i ∈ s, residue (f i) z₀ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact residue_eq_zero_of_analyticAt analyticAt_const
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, ∀ᶠ z in 𝓝[≠] z₀, DifferentiableAt ℂ (f i) z :=
      fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      residue_add (hf a (Finset.mem_insert_self a s))
        ((s.eventually_all.2 hs).mono fun _ hz ↦ DifferentiableAt.sum hz), ih hs]

/-- **The residue of the Cauchy kernel.** If `g` is analytic at `z₀`, then the function
`g z / (z - z₀) ^ (k + 1)` has residue the Taylor coefficient `iteratedDeriv k g z₀ / k !` at `z₀`:
the whole Laurent principal part comes from the first `k + 1` Taylor terms of `g`, and only the one
of index `k` sits at order `−1`. This is the residue behind Cauchy's integral formula for the
`k`-th derivative; the constant case is `TauCeti.Contour.residue_const_div_sub_pow`. -/
@[simp]
theorem residue_div_sub_pow_of_analyticAt {g : ℂ → ℂ} {z₀ : ℂ} (hg : AnalyticAt ℂ g z₀) (k : ℕ) :
    residue (fun z ↦ g z / (z - z₀) ^ (k + 1)) z₀
      = iteratedDeriv k g z₀ / (k.factorial : ℂ) := by
  have hfg : (fun z ↦ g z / (z - z₀) ^ (k + 1)) =ᶠ[𝓝[≠] z₀]
      fun z ↦ (z - z₀) ^ (-(k + 1 : ℕ) : ℤ) • g z :=
    Filter.Eventually.of_forall fun z ↦ by
      simp only [smul_eq_mul, zpow_neg, zpow_natCast, div_eq_inv_mul]
  have hidx : (-1 - (-(k + 1 : ℕ) : ℤ)).toNat = k := by omega
  rw [residue_eq_of_eventuallyEq_zpow_smul (by omega) hg hfg, hidx, smul_eq_mul, inv_mul_eq_div]

/-- **The residue of a Laurent monomial**: `residue (a / (z - z₀)^(k+1)) z₀` is `a` for `k = 0`
and `0` for higher-order terms. -/
@[simp]
theorem residue_const_div_sub_pow (a z₀ : ℂ) (k : ℕ) :
    residue (fun z ↦ a / (z - z₀) ^ (k + 1)) z₀ = if k = 0 then a else 0 := by
  rw [residue_div_sub_pow_of_analyticAt analyticAt_const, iteratedDeriv_const]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · simp [hk.ne']

/-- **The residue from a Laurent expansion.** If `f z = g z + ∑ k, a k / (z - z₀)^(k+1)` near
`z₀` with `g` analytic at `z₀`, then `residue f z₀` is the first Laurent coefficient `a 0` (or
`0` for an empty expansion): the analytic part and the higher-order terms contribute nothing. -/
theorem residue_of_laurent_expansion {f g : ℂ → ℂ} {z₀ : ℂ} {N : ℕ} {a : Fin N → ℂ}
    (hg : AnalyticAt ℂ g z₀)
    (hf_eq : ∀ᶠ z in 𝓝[≠] z₀, f z = g z + ∑ k : Fin N, a k / (z - z₀) ^ (k.val + 1)) :
    residue f z₀ = if h : 0 < N then a ⟨0, h⟩ else 0 := by
  have hmono : ∀ k : Fin N,
      ∀ᶠ z in 𝓝[≠] z₀, DifferentiableAt ℂ (fun z ↦ a k / (z - z₀) ^ (k.val + 1)) z :=
    fun k ↦ eventually_mem_nhdsWithin.mono fun z hz ↦ (differentiableAt_const _).div
      ((differentiableAt_id.sub_const z₀).pow _) (pow_ne_zero _ (sub_ne_zero.2 hz))
  have hf_eq' : f =ᶠ[𝓝[≠] z₀]
      g + ∑ k : Fin N, fun z ↦ a k / (z - z₀) ^ (k.val + 1) := by
    filter_upwards [hf_eq] with z hz
    simpa [Finset.sum_apply] using hz
  rw [residue_congr_nhdsNE hf_eq',
    residue_add ((hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds).mono
        fun _ h ↦ h.differentiableAt)
      ((Finset.univ.eventually_all.2 fun k _ ↦ hmono k).mono fun _ hz ↦ DifferentiableAt.sum hz),
    residue_eq_zero_of_analyticAt hg, zero_add, residue_sum _ fun k _ ↦ hmono k]
  simp only [residue_const_div_sub_pow]
  rcases Nat.eq_zero_or_pos N with rfl | hpos
  · simp
  · rw [dite_eq_left hpos, Finset.sum_eq_single ⟨0, hpos⟩ (fun k _ hk ↦ ite_eq_right fun h0 ↦
      hk (Fin.ext h0)) (by simp), ite_eq_left rfl]

/-- If `g : ℂ → ℂ` does not vanish on a punctured neighborhood of `z₀`, then
`z ↦ (0 : ℂ) ^ g z • f z` vanishes on a punctured neighborhood of `z₀` and has residue `0`,
without requiring meromorphy of `f` or completeness of `E`. -/
theorem residue_zero_cpow_smul_of_eventually_ne_zero {g : ℂ → ℂ} (f : ℂ → E) {z₀ : ℂ}
    (hg : ∀ᶠ z in 𝓝[≠] z₀, g z ≠ 0) :
    residue (fun z ↦ (0 : ℂ) ^ g z • f z) z₀ = 0 :=
  (residue_congr_nhdsNE (hg.mono fun z hz ↦ by rw [Complex.zero_cpow hz, zero_smul])).trans
    (residue_eq_zero_of_analyticAt analyticAt_const)

/-- Since `z ↦ (0 : ℂ) ^ z` vanishes on a punctured neighborhood of every point `z₀`, multiplying
any function by `(0 : ℂ) ^ z` has residue `0` at `z₀`. -/
@[simp]
theorem residue_zero_cpow_smul (f : ℂ → E) (z₀ : ℂ) :
    residue (fun z ↦ (0 : ℂ) ^ z • f z) z₀ = 0 :=
  residue_zero_cpow_smul_of_eventually_ne_zero f
    ((eventually_cofinite_ne (0 : ℂ)).filter_mono (nhdsNE_le_cofinite z₀))

/-- Since `z ↦ (0 : ℂ) ^ (-z)` vanishes on a punctured neighborhood of every point `z₀`,
multiplying any function by `(0 : ℂ) ^ (-z)` has residue `0` at `z₀`. -/
@[simp]
theorem residue_zero_cpow_neg_smul (f : ℂ → E) (z₀ : ℂ) :
    residue (fun z ↦ (0 : ℂ) ^ (-z) • f z) z₀ = 0 :=
  residue_zero_cpow_smul_of_eventually_ne_zero f
    (((eventually_cofinite_ne (0 : ℂ)).filter_mono (nhdsNE_le_cofinite z₀)).mono fun _ hz ↦
      neg_ne_zero.mpr hz)

/-- The applied `*` companion to `residue_zero_cpow_smul`: `z ↦ (0 : ℂ) ^ z * f z` has residue `0`
at every point `z₀`. -/
@[simp]
theorem residue_zero_cpow_mul (f : ℂ → ℂ) (z₀ : ℂ) :
    residue (fun z ↦ (0 : ℂ) ^ z * f z) z₀ = 0 := by
  simpa only [smul_eq_mul] using residue_zero_cpow_smul f z₀

/-- The applied `*` companion to `residue_zero_cpow_neg_smul`: `z ↦ (0 : ℂ) ^ (-z) * f z` has
residue `0` at every point `z₀`. -/
@[simp]
theorem residue_zero_cpow_neg_mul (f : ℂ → ℂ) (z₀ : ℂ) :
    residue (fun z ↦ (0 : ℂ) ^ (-z) * f z) z₀ = 0 := by
  simpa only [smul_eq_mul] using residue_zero_cpow_neg_smul f z₀

end TauCeti.Contour

end
