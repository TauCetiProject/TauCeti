/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Harnack
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# The strong maximum principle for weak subsolutions

Let `a` be measurable and uniformly elliptic on a connected open set `Ω ⊆ ℝⁿ`, `n ≥ 1`, with
constants `0 < λ ≤ Λ`, and let `u ∈ H¹(Ω)` be a weak subsolution of the divergence-form equation

`-∂ⱼ(aⁱʲ ∂ᵢu) ≤ 0` in `Ω`,

meaning `a(u, v) ≤ 0` for every nonnegative `v ∈ H¹₀(Ω)`. This file proves the **strong maximum
principle**: if `u ≤ M` almost everywhere on `Ω` and `u` comes essentially arbitrarily close to
`M` near some point of `Ω`, then `u = M` almost everywhere on `Ω`. No regularity of the
coefficients beyond measurability is assumed, so `u` has no pointwise values and the maximum is
an essential one. Two forms of the hypothesis are provided:

* near a point `y ∈ Ω`: for every ball `B(y, ρ) ⊆ Ω` and every `ε > 0`, the set `{u > M - ε}`
  meets `B(y, ρ)` in positive measure, that is, the essential supremum of `u` on every ball about
  `y` is `M`;
* on a compact `K ⊆ Ω`: the essential supremum of `u` on `K` is `M`. This is the form of
  Gilbarg–Trudinger, Theorem 8.19, where `K` is the closure of a ball compactly contained in `Ω`.

Supersolutions satisfy the corresponding strong minimum principle.

The input is Moser's weak Harnack inequality at a small exponent `p₀`
(`TauCeti.PDE.exists_pos_ae_setAverage_rpow_rpow_inv_le_mul_value`), applied to the nonnegative
weak supersolution `M - u` on a ball `B(y, 12√n r) ⊆ Ω`:

`(⨍_{B(y, 2r)} (M - u)^{p₀})^{1/p₀} ≤ C (M - u)(x)` for almost every `x ∈ B(y, r)`.

If `M - u` takes values below every `ε > 0` on subsets of `B(y, r)` of positive measure, the left
side vanishes, so `u = M` almost everywhere on `B(y, r)`. The set of points near which `u = M`
almost everywhere is therefore open, and relatively closed in `Ω`: a point of `Ω` in its closure
has a ball `B(y, r)` meeting a ball on which `u = M`, in an open set of positive measure.
Connectedness of `Ω` does the rest.

Connectedness is needed: on the union of two disjoint balls, a function equal to `0` on one and
to `-1` on the other is a weak solution which attains its maximum without being constant.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.ae_value_eq_of_frequently_sub_lt`: the strong maximum
  principle for weak subsolutions, with the essential maximum attained near a point.
* `TauCeti.PDE.UniformlyEllipticOn.ae_value_eq_of_frequently_sub_lt_of_isCompact`: the same,
  with the essential maximum attained on a compact subset of `Ω`.
* `TauCeti.PDE.UniformlyEllipticOn.ae_value_eq_of_frequently_lt_add` and
  `TauCeti.PDE.UniformlyEllipticOn.ae_value_eq_of_frequently_lt_add_of_isCompact`: the strong
  minimum principle for weak supersolutions.

## References

* J. Moser, *On Harnack's theorem for elliptic differential equations*, Comm. Pure Appl. Math.
  **14** (1961), 577–591.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.19.
-/

public section

noncomputable section

open Filter MeasureTheory Metric Set TopologicalSpace

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ} {u : W1p mu Omega 2} {M : ℝ}

/-- The local step of the strong maximum principle. If `u ≤ M` is a weak subsolution on `Ω`,
`B(y, 12√n r) ⊆ Ω`, and `u` exceeds `M - ε` on a subset of `B(y, r)` of positive measure for every
`ε > 0`, then `u = M` almost everywhere on `B(y, r)`. -/
private theorem UniformlyEllipticOn.ae_ball_value_eq_of_frequently_sub_lt [Nonempty ι]
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤ 0)
    (hM : ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ M) {y : EuclideanSpace ℝ ι} {r : ℝ}
    (hball : ball y (12 * √(Fintype.card ι) * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)))
    (hfreq : ∀ ε > 0, ∃ᵐ x ∂mu.restrict (ball y r), M - ε < W1p.value u x) :
    ∀ᵐ x ∂mu.restrict (ball y r), W1p.value u x = M := by
  obtain ⟨p₀, hp₀, hp₀2, C, hC, hH⟩ :=
    exists_pos_ae_setAverage_rpow_rpow_inv_le_mul_value (ι := ι) (mu := mu) (lam := lam)
      (Lam := Lam)
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  have hsqrt : 1 ≤ √(Fintype.card ι : ℝ) := Real.one_le_sqrt.2 (Nat.one_le_cast.2 Fintype.card_pos)
  -- Work on the bounded open ball `U = B(y, 12√n r)`, where constants lie in `H¹(U)`.
  set U : Opens (EuclideanSpace ℝ ι) := ⟨ball y (12 * √(Fintype.card ι) * r), isOpen_ball⟩
  have hU : U ≤ Omega := hball
  have h2U : ball y (2 * r) ⊆ (U : Set (EuclideanSpace ℝ ι)) := ball_subset_ball (by nlinarith)
  have hr2 : ball y r ⊆ ball y (2 * r) := ball_subset_ball (by linarith)
  have : IsFiniteMeasure (mu.restrict U) := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have : IsFiniteMeasure (mu.restrict (ball y (2 * r))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  -- `w = M - u` is a nonnegative weak supersolution on `U`.
  have hneg := W1p.value_neg_ae u
  set w := W1p.restrictL hU (-u) + W1p.const M
  have hwv : ∀ᵐ x ∂mu.restrict U, W1p.value w x = M - W1p.value u x := by
    filter_upwards [W1p.value_add_const_ae (W1p.restrictL hU (-u)) M,
      W1p.value_restrictL_ae hU (-u), ae_restrict_of_ae_restrict_of_subset hball hneg]
      with x h1 h2 h3
    rw [h1, h2, h3, Pi.neg_apply]
    ring
  have hw0 : ∀ᵐ x ∂mu.restrict U, 0 ≤ W1p.value w x := by
    filter_upwards [hwv, ae_restrict_of_ae_restrict_of_subset hball hM] with x h1 h2
    rw [h1]
    linarith
  have hsuper := energyFormH1_restrictL_add_const_nonneg hU (u := -u) (fun v hv => by
    rw [energyFormH1_neg_left]
    linarith [hu v hv]) M
  -- The weak Harnack inequality for `w`: its `L^{p₀}` average is at most `C w(x)` on `B(y, r)`.
  have hHw := hH (h.mono_set hball) (ha.mono_measure (Measure.restrict_mono hball le_rfl))
    hsuper hw0 (x₀ := y) (r := r) subset_rfl
  have hw02 := ae_restrict_of_ae_restrict_of_subset h2U hw0
  have hA0 : 0 ≤ ⨍ x in ball y (2 * r), W1p.value w x ^ p₀ ∂mu :=
    average_nonneg_of_ae (hw02.mono fun x hx => Real.rpow_nonneg hx _)
  -- Since `w` is essentially as small as we like on `B(y, r)`, that average vanishes.
  have hA : (⨍ x in ball y (2 * r), W1p.value w x ^ p₀ ∂mu) ^ p₀⁻¹ ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨x, hx1, hx2, hx3⟩ := ((hfreq (ε / C) (div_pos hε hC)).and_eventually
      (hHw.and (ae_restrict_of_ae_restrict_of_subset (hr2.trans h2U) hwv))).exists
    rw [hx3] at hx2
    calc _ ≤ C * (M - W1p.value u x) := hx2
      _ ≤ C * (ε / C) := by gcongr; linarith
      _ = 0 + ε := by field_simp; ring
  have havg : ⨍ x in ball y (2 * r), W1p.value w x ^ p₀ ∂mu = 0 :=
    (Real.rpow_eq_zero hA0 (inv_ne_zero hp₀.ne')).1 (hA.antisymm (Real.rpow_nonneg hA0 _))
  -- `w^{p₀}` is integrable on `B(y, 2r)`, as `w ∈ L²` there and `p₀ ≤ 2`.
  have hint : IntegrableOn (fun x => W1p.value w x ^ p₀) (ball y (2 * r)) mu := by
    have hmem : MemLp (W1p.value w) (ENNReal.ofReal p₀) (mu.restrict (ball y (2 * r))) :=
      ((Lp.memLp _).mono_measure (Measure.restrict_mono h2U le_rfl)).mono_exponent
        ((ENNReal.ofReal_le_ofReal hp₀2).trans_eq (ENNReal.ofReal_ofNat 2))
    refine (hmem.integrable_norm_rpow (ENNReal.ofReal_pos.2 hp₀).ne'
      ENNReal.ofReal_ne_top).congr ?_
    filter_upwards [hw02] with x hx
    rw [ENNReal.toReal_ofReal hp₀.le, Real.norm_of_nonneg hx]
  rw [setAverage_eq, smul_eq_mul, mul_eq_zero, inv_eq_zero] at havg
  have hzero := (integral_eq_zero_iff_of_nonneg_ae
    (hw02.mono fun x hx => Real.rpow_nonneg hx _) hint).1
    (havg.resolve_left (measureReal_ball_pos mu y (by linarith)).ne')
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hr2 hzero,
    ae_restrict_of_ae_restrict_of_subset hr2 hw02,
    ae_restrict_of_ae_restrict_of_subset (hr2.trans h2U) hwv] with x h1 h2 h3
  have := (Real.rpow_eq_zero h2 hp₀.ne').1 h1
  linarith

/-- **The strong maximum principle for weak subsolutions.** Let `a` be measurable and uniformly
elliptic on a connected open set `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak
subsolution of `-∂ⱼ(aⁱʲ ∂ᵢu) ≤ 0`, that is `a(u, v) ≤ 0` for every nonnegative `v ∈ H¹₀(Ω)`.
Suppose that `u ≤ M` almost everywhere on `Ω`, and that `M` is the essential supremum of `u` on
every ball about a point `y ∈ Ω`: for every ball `B(y, ρ) ⊆ Ω` and every `ε > 0`, `u > M - ε` on
a subset of `B(y, ρ)` of positive measure. Then `u = M` almost everywhere on `Ω`. -/
theorem UniformlyEllipticOn.ae_value_eq_of_frequently_sub_lt [Nonempty ι]
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hΩ : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤ 0)
    (hM : ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ M) {y : EuclideanSpace ℝ ι} (hy : y ∈ Omega)
    (hfreq : ∀ ρ > 0, ball y ρ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ ε > 0, ∃ᵐ x ∂mu.restrict (ball y ρ), M - ε < W1p.value u x) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x = M := by
  -- Every point of `Ω` is the centre of a ball `B(z, r)` with `B(z, 12√n r) ⊆ Ω`.
  have hrad : ∀ z ∈ Omega, ∃ r > 0,
      ball z (12 * √(Fintype.card ι) * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) := by
    intro z hz
    obtain ⟨R, hR, hRΩ⟩ := Metric.isOpen_iff.1 Omega.isOpen z hz
    have hc : 0 < 12 * √(Fintype.card ι : ℝ) :=
      mul_pos (by norm_num) (Real.sqrt_pos.2 (Nat.cast_pos.2 Fintype.card_pos))
    exact ⟨R / (12 * √(Fintype.card ι)), div_pos hR hc, by rwa [mul_div_cancel₀ R hc.ne']⟩
  -- `S` is the set of points near which `u = M` almost everywhere.
  set S := {z | ∃ ρ > 0, ∀ᵐ x ∂mu.restrict (ball z ρ), W1p.value u x = M}
  have hSo : IsOpen S := by
    refine isOpen_iff_mem_nhds.2 fun z ⟨ρ, hρ, hz⟩ => ?_
    filter_upwards [ball_mem_nhds z hρ] with z' hz'
    have hsub : ball z' (ρ - dist z' z) ⊆ ball z ρ := ball_subset_ball' (by linarith)
    exact ⟨ρ - dist z' z, sub_pos.2 hz', ae_restrict_of_ae_restrict_of_subset hsub hz⟩
  -- `S` contains `y`, by the local step.
  have hyS : y ∈ S := by
    obtain ⟨r, hr, hball⟩ := hrad y hy
    have hsqrt : 1 ≤ √(Fintype.card ι : ℝ) :=
      Real.one_le_sqrt.2 (Nat.one_le_cast.2 Fintype.card_pos)
    exact ⟨r, hr, h.ae_ball_value_eq_of_frequently_sub_lt ha hu hM hball
      (hfreq r hr ((ball_subset_ball (by nlinarith)).trans hball))⟩
  -- A point of `Ω` in the closure of `S` lies in `S`: a ball about it meets a ball on which
  -- `u = M` in an open set of positive measure, and the local step applies.
  have hcl : closure S ∩ Omega ⊆ S := by
    rintro z ⟨hzS, hzΩ⟩
    obtain ⟨r, hr, hball⟩ := hrad z hzΩ
    obtain ⟨z', ⟨ρ, hρ, hz'⟩, hzz'⟩ := Metric.mem_closure_iff.1 hzS r hr
    have hV : mu (ball z r ∩ ball z' ρ) ≠ 0 := ((isOpen_ball.inter isOpen_ball).measure_pos mu
      ⟨z', by rwa [mem_ball, dist_comm], mem_ball_self hρ⟩).ne'
    refine ⟨r, hr, h.ae_ball_value_eq_of_frequently_sub_lt ha hu hM hball fun ε hε => ?_⟩
    have := ae_restrict_neBot.2 hV
    exact ((ae_restrict_of_ae_restrict_of_subset inter_subset_right hz').mono fun x hx => by
      rw [hx]; linarith).frequently.filter_mono
        (ae_mono (Measure.restrict_mono inter_subset_left le_rfl))
  have hΩS : (Omega : Set (EuclideanSpace ℝ ι)) ⊆ S :=
    hΩ.subset_of_closure_inter_subset hSo ⟨y, hy, hyS⟩ hcl
  -- `Ω` is covered by balls on which `u = M` almost everywhere.
  rw [ae_restrict_iff' Omega.isOpen.measurableSet, ae_iff]
  refine measure_null_of_locally_null _ fun z hz => ?_
  obtain ⟨ρ, hρ, hzρ⟩ := hΩS (not_imp.1 hz).1
  rw [ae_restrict_iff' measurableSet_ball, ae_iff] at hzρ
  refine ⟨_, inter_mem_nhdsWithin _ (ball_mem_nhds z hρ), measure_mono_null (fun x hx => ?_) hzρ⟩
  exact not_imp.2 ⟨hx.2, (not_imp.1 hx.1).2⟩

/-- **The strong maximum principle for weak subsolutions, compact form.** Let `a` be measurable
and uniformly elliptic on a connected open set `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a
weak subsolution of `-∂ⱼ(aⁱʲ ∂ᵢu) ≤ 0`. If `u ≤ M` almost everywhere on `Ω` and the essential
supremum of `u` on a compact `K ⊆ Ω` is `M`, that is, `u > M - ε` on a subset of `K` of positive
measure for every `ε > 0`, then `u = M` almost everywhere on `Ω`. -/
theorem UniformlyEllipticOn.ae_value_eq_of_frequently_sub_lt_of_isCompact [Nonempty ι]
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hΩ : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤ 0)
    (hM : ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ M) {K : Set (EuclideanSpace ℝ ι)}
    (hK : IsCompact K) (hKΩ : K ⊆ (Omega : Set (EuclideanSpace ℝ ι)))
    (hfreq : ∀ ε > 0, ∃ᵐ x ∂mu.restrict K, M - ε < W1p.value u x) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x = M := by
  -- Some point of `K` has `M` as the essential supremum of `u` on every ball about it.
  by_contra hne
  have hloc : ∀ y ∈ K, ∃ ρ > 0, ∃ ε > 0, ∀ᵐ x ∂mu.restrict (ball y ρ), W1p.value u x ≤ M - ε := by
    intro y hy
    by_contra hy'
    simp only [not_exists, not_and, Filter.not_eventually, not_le] at hy'
    exact hne (h.ae_value_eq_of_frequently_sub_lt ha hΩ hu hM (hKΩ hy) fun ρ hρ _ ε hε =>
      (hy' ρ hρ ε hε).mono fun x hx => by linarith)
  -- Otherwise compactness gives a single `ε` with `u ≤ M - ε` almost everywhere on `K`.
  obtain ⟨ε, hε, hK'⟩ : ∃ ε > 0, ∀ᵐ x ∂mu.restrict K, W1p.value u x ≤ M - ε := by
    refine hK.induction_on (p := fun s => ∃ ε > 0, ∀ᵐ x ∂mu.restrict s, W1p.value u x ≤ M - ε)
      ⟨1, one_pos, by simp⟩ (fun s t hst ⟨ε, hε, ht⟩ =>
        ⟨ε, hε, ae_restrict_of_ae_restrict_of_subset hst ht⟩)
      (fun s t ⟨ε, hε, hs⟩ ⟨δ, hδ, ht⟩ => ⟨min ε δ, lt_min hε hδ, ?_⟩) fun y hy => ?_
    · rw [ae_restrict_union_iff]
      exact ⟨hs.mono fun x hx => hx.trans (by gcongr; exact min_le_left _ _),
        ht.mono fun x hx => hx.trans (by gcongr; exact min_le_right _ _)⟩
    · obtain ⟨ρ, hρ, ε, hε, hyρ⟩ := hloc y hy
      exact ⟨ball y ρ, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds y hρ), ε, hε, hyρ⟩
  obtain ⟨x, hx1, hx2⟩ := ((hfreq ε hε).and_eventually hK').exists
  linarith

/-- **The strong minimum principle for weak supersolutions.** Let `a` be measurable and uniformly
elliptic on a connected open set `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak
supersolution of `-∂ⱼ(aⁱʲ ∂ᵢu) ≥ 0`, that is `a(u, v) ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)`.
Suppose that `m ≤ u` almost everywhere on `Ω`, and that `m` is the essential infimum of `u` on
every ball about a point `y ∈ Ω`: for every ball `B(y, ρ) ⊆ Ω` and every `ε > 0`, `u < m + ε` on
a subset of `B(y, ρ)` of positive measure. Then `u = m` almost everywhere on `Ω`. -/
theorem UniformlyEllipticOn.ae_value_eq_of_frequently_lt_add [Nonempty ι]
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hΩ : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2))
    {m : ℝ} (hm : ∀ᵐ x ∂mu.restrict Omega, m ≤ W1p.value u x) {y : EuclideanSpace ℝ ι}
    (hy : y ∈ Omega)
    (hfreq : ∀ ρ > 0, ball y ρ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ ε > 0, ∃ᵐ x ∂mu.restrict (ball y ρ), W1p.value u x < m + ε) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x = m := by
  -- Apply the strong maximum principle to the subsolution `-u ≤ -m`.
  have hneg := W1p.value_neg_ae u
  have hmax := h.ae_value_eq_of_frequently_sub_lt ha hΩ (u := -u) (M := -m) (fun v hv => by
      rw [energyFormH1_neg_left]
      linarith [hu v hv])
    (by filter_upwards [hm, hneg] with x hx hxn; rw [hxn, Pi.neg_apply]; linarith) hy
    fun ρ hρ hρΩ ε hε => ((hfreq ρ hρ hρΩ ε hε).and_eventually
      (ae_restrict_of_ae_restrict_of_subset hρΩ hneg)).mono fun x ⟨hx, hxn⟩ => by
        rw [hxn, Pi.neg_apply]; linarith
  filter_upwards [hmax, hneg] with x hx hxn
  rw [hxn, Pi.neg_apply] at hx
  linarith

/-- **The strong minimum principle for weak supersolutions, compact form.** Let `a` be measurable
and uniformly elliptic on a connected open set `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a
weak supersolution of `-∂ⱼ(aⁱʲ ∂ᵢu) ≥ 0`. If `m ≤ u` almost everywhere on `Ω` and the essential
infimum of `u` on a compact `K ⊆ Ω` is `m`, that is, `u < m + ε` on a subset of `K` of positive
measure for every `ε > 0`, then `u = m` almost everywhere on `Ω`. -/
theorem UniformlyEllipticOn.ae_value_eq_of_frequently_lt_add_of_isCompact [Nonempty ι]
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hΩ : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2))
    {m : ℝ} (hm : ∀ᵐ x ∂mu.restrict Omega, m ≤ W1p.value u x) {K : Set (EuclideanSpace ℝ ι)}
    (hK : IsCompact K) (hKΩ : K ⊆ (Omega : Set (EuclideanSpace ℝ ι)))
    (hfreq : ∀ ε > 0, ∃ᵐ x ∂mu.restrict K, W1p.value u x < m + ε) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x = m := by
  -- Apply the compact strong maximum principle to the subsolution `-u ≤ -m`.
  have hneg := W1p.value_neg_ae u
  have hmax := h.ae_value_eq_of_frequently_sub_lt_of_isCompact ha hΩ (u := -u) (M := -m)
    (fun v hv => by
      rw [energyFormH1_neg_left]
      linarith [hu v hv])
    (by filter_upwards [hm, hneg] with x hx hxn; rw [hxn, Pi.neg_apply]; linarith) hK hKΩ
    fun ε hε => ((hfreq ε hε).and_eventually (ae_restrict_of_ae_restrict_of_subset hKΩ hneg)).mono
      fun x ⟨hx, hxn⟩ => by rw [hxn, Pi.neg_apply]; linarith
  filter_upwards [hmax, hneg] with x hx hxn
  rw [hxn, Pi.neg_apply] at hx
  linarith

end PDE

end TauCeti
