/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The TauCeti contributors
-/
module

public import TauCeti.Analysis.GradientFlow.EVI.MinimizingMovement
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.GeneralizedGeodesic.Convex
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Complete

/-!
# Wasserstein `EVI_λ` gradient flows and convergence of JKO schemes

Let `E` be a separable Hilbert space and `φ : WassersteinSpace 2 E → EReal` be lower
semicontinuous and `λ`-convex along generalized geodesics based at every law of `P₂(E)`. No
compactness of sublevels is assumed.

First, `TauCeti.GeneralizedGeodesicallyConvex.moreauYosida_ne_bot` shows that local lower
boundedness extends along generalized geodesics to coercivity `φ_τ(μ) > -∞` if `1 + m τ > 0`,
using `TauCeti.IsGeneralizedGeodesicPlan.dist_sq_add_le` and
`TauCeti.WassersteinSpace.dist_sq_le_integral`. Combined with
`TauCeti.penalizedConvex_of_generalizedGeodesicallyConvex`, this gives existence and uniqueness of
each JKO step (`TauCeti.moreauYosidaResolvent_nonempty_of_generalizedGeodesicallyConvex`,
`TauCeti.existsUnique_mem_moreauYosidaResolvent_of_generalizedGeodesicallyConvex`), uniform
convergence on compact time intervals of JKO schemes to the unique `EVI_λ` gradient flow
(`TauCeti.exists_isEVISolution_tendstoUniformlyOn_of_generalizedGeodesicallyConvex`), and
extension of existence to `closure {μ | φ μ ≠ ⊤}`
(`TauCeti.exists_isEVISolution_of_mem_closure_of_generalizedGeodesicallyConvex`,
`TauCeti.eviDomain_eq_closure_of_generalizedGeodesicallyConvex`).

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Chapters 4 and 11 (Theorems 4.0.4, 4.1.2,
  11.2.1).
* R. Jordan, D. Kinderlehrer, F. Otto, *The variational formulation of the Fokker–Planck
  equation*, SIAM J. Math. Anal. 29 (1998), 1--17.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
  {m lam : ℝ} {φ : WassersteinSpace 2 E → EReal} {μ : WassersteinSpace 2 E} {τ : ℝ≥0}

/-- **Coercivity of energies convex along generalized geodesics.** A lower semicontinuous
energy `φ` on `P₂(E)` that is `m`-convex along generalized geodesics at `μ` and finite at `μ`
satisfies `φ_τ(μ) > -∞` for every time step `τ > 0` with `1 + m τ > 0`. -/
theorem GeneralizedGeodesicallyConvex.moreauYosida_ne_bot (hφ : LowerSemicontinuous φ)
    (h : GeneralizedGeodesicallyConvex m φ μ) (hμtop : φ μ ≠ ⊤) (hμbot : φ μ ≠ ⊥)
    (hτ : 0 < τ) (hmτ : 0 < 1 + m * τ) : moreauYosida φ τ μ ≠ ⊥ := by
  set a : ℝ := (φ μ).toReal
  have ha : φ μ = a := (EReal.coe_toReal hμtop hμbot).symm
  have hnhds : ∀ᶠ ν in 𝓝 μ, ((a - 1 : ℝ) : EReal) < φ ν :=
    hφ μ _ (by simpa [ha] using EReal.coe_lt_coe_iff.2 (sub_one_lt a))
  obtain ⟨δ, hδ, hball⟩ := Metric.nhds_basis_ball.eventually_iff.1 hnhds
  set c : ℝ := min 1 (1 + m * τ)
  have : 0 < c := lt_min one_pos hmτ
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcm : c ≤ 1 + m * τ := min_le_right _ _
  set k : ℝ := c / (2 * τ)
  have hkpos : 0 < k := by positivity
  set L : ℝ := min (a - 1) (a - 1 / (k * δ ^ 2))
  refine ne_bot_of_le_ne_bot (EReal.coe_ne_bot L) (le_moreauYosida_iff.2 fun ν _ ↦ ?_)
  rw [coe_edist_sq_div_eq_coe_dist_sq_div hτ]
  rcases lt_or_ge (dist μ ν) δ with hμν | hμν
  · refine (EReal.coe_le_coe_iff.2 (min_le_left _ _)).trans ?_
    exact (hball (Metric.mem_ball'.2 hμν)).le.trans (le_add_of_nonneg_right (by positivity))
  rcases eq_or_ne (φ ν) ⊤ with hνtop | hνtop
  · rw [hνtop, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
    exact le_top
  set r : ℝ := dist μ ν
  have hrpos : 0 < r := hδ.trans_le hμν
  set t : ℝ := δ / (2 * r)
  have htpos : 0 < t := by positivity
  have ht1 : t ≤ 1 / 2 := by rw [div_le_div_iff₀ (by positivity) two_pos]; linarith
  have htIcc : t ∈ Icc (0 : ℝ) 1 := ⟨htpos.le, ht1.trans (by norm_num)⟩
  have ht' : 0 ≤ 1 - t := sub_nonneg.2 htIcc.2
  obtain ⟨γ, hγ, hconv⟩ := generalizedGeodesicallyConvex_def.1 h hμtop hνtop
  obtain ⟨νt, hνt⟩ := exists_coe_eq_generalizedGeodesic hγ.isCoupling_snd t
  set I : ℝ := ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ.snd
  have hd := hγ.dist_sq_add_le htIcc hνt
  rw [dist_self, zero_pow two_ne_zero, mul_zero, zero_add] at hd
  have hW2 : r ^ 2 ≤ I := WassersteinSpace.dist_sq_le_integral hγ.isCoupling_snd
  have hmul_I : t * (1 - t) * r ^ 2 ≤ t * (1 - t) * I :=
    mul_le_mul_of_nonneg_left hW2 (mul_nonneg htpos.le ht')
  have hνt_ball : νt ∈ Metric.ball μ δ := by
    rw [Metric.mem_ball']
    have htr : t * r = δ / 2 := by dsimp [t]; field_simp
    have hsq_eq : t * r ^ 2 - t * (1 - t) * r ^ 2 = (δ / 2) ^ 2 := by
      calc t * r ^ 2 - t * (1 - t) * r ^ 2 = (t * r) ^ 2 := by ring
        _ = (δ / 2) ^ 2 := by rw [htr]
    have hsq_νt : dist μ νt ^ 2 ≤ (δ / 2) ^ 2 := by linarith
    have hle : dist μ νt ≤ δ / 2 :=
      (pow_le_pow_iff_left₀ dist_nonneg (by positivity) two_ne_zero).1 hsq_νt
    linarith
  have hI_le : (1 - t) * I ≤ r ^ 2 :=
    le_of_mul_le_mul_left (by nlinarith [sq_nonneg (dist μ νt)]) htpos
  have hlow : ((a - 1 : ℝ) : EReal) < φ νt := hball hνt_ball
  have hconv_t := convexAlongGeneralizedGeodesicPlan_def.1 hconv t htIcc νt hνt
  have hνbot : φ ν ≠ ⊥ := fun hνbot ↦ by
    rw [hνbot, EReal.coe_mul_bot_of_pos htpos, EReal.add_bot, EReal.bot_sub, le_bot_iff]
      at hconv_t
    rw [hconv_t] at hlow
    exact not_lt_bot hlow
  set b : ℝ := (φ ν).toReal
  have hb : φ ν = b := (EReal.coe_toReal hνtop hνbot).symm
  rw [ha, hb] at hconv_t
  norm_cast at hconv_t
  have hmid : a - 1 ≤ (1 - t) * a + t * b - m / 2 * t * (1 - t) * I := by
    exact_mod_cast (hlow.le.trans hconv_t)
  have hslope : a - 2 * r / δ ≤ b - m / 2 * (1 - t) * I := by
    have hmul : t * (a - 2 * r / δ) ≤ t * (b - m / 2 * (1 - t) * I) := by
      have : t * (2 * r / δ) = 1 := by dsimp [t]; field_simp
      linarith
    exact le_of_mul_le_mul_left hmul htpos
  have hquad : k * r ^ 2 ≤ m / 2 * (1 - t) * I + r ^ 2 / (2 * τ) := by
    have hkr : k * r ^ 2 = (c - 1) / (2 * τ) * r ^ 2 + r ^ 2 / (2 * τ) := by
      dsimp [k]; field_simp; ring
    rw [hkr]
    rcases le_or_gt 0 m with hm | hm
    · have hcτ : (c - 1) / (2 * τ) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      have h1 : (c - 1) / (2 * τ) * r ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hcτ (sq_nonneg r)
      have h2 : 0 ≤ m / 2 * (1 - t) * I := mul_nonneg
        (mul_nonneg (div_nonneg hm zero_le_two) ht') (integral_nonneg fun _ ↦ by positivity)
      linarith
    · have hcτ : (c - 1) / (2 * τ) ≤ m / 2 := (div_le_iff₀ (by positivity)).2 (by linarith)
      have h1 : (c - 1) / (2 * τ) * r ^ 2 ≤ m / 2 * r ^ 2 :=
        mul_le_mul_of_nonneg_right hcτ (sq_nonneg r)
      have h2 : m / 2 * r ^ 2 ≤ m / 2 * ((1 - t) * I) :=
        mul_le_mul_of_nonpos_left hI_le (div_nonpos_of_nonpos_of_nonneg hm.le zero_le_two)
      linarith
  have hsq : -(1 / (k * δ ^ 2)) ≤ k * r ^ 2 - 2 * r / δ := by
    rw [← sub_nonneg]
    calc k * r ^ 2 - 2 * r / δ - -(1 / (k * δ ^ 2))
        = (k * δ * r - 1) ^ 2 / (k * δ ^ 2) := by field_simp; ring
      _ ≥ 0 := div_nonneg (sq_nonneg _) (by positivity)
  rw [hb, ← EReal.coe_add]
  exact EReal.coe_le_coe_iff.2 ((min_le_right _ _).trans (by linarith))

private lemma exists_moreauYosida_ne_bot_gt (hφ : LowerSemicontinuous φ)
    (hconv : ∀ ν, GeneralizedGeodesicallyConvex m φ ν) (hτ : 0 < τ) (hmτ : 0 < 1 + m * τ)
    {ν₀ : WassersteinSpace 2 E} (hν₀top : φ ν₀ ≠ ⊤) (hν₀bot : φ ν₀ ≠ ⊥) :
    ∃ τ₀ : ℝ≥0, τ < τ₀ ∧ moreauYosida φ τ₀ ν₀ ≠ ⊥ := by
  rcases le_or_gt 0 m with hm | hm
  · refine ⟨τ + 1, lt_add_one τ, (hconv ν₀).moreauYosida_ne_bot hφ hν₀top hν₀bot
      (by positivity) ?_⟩
    push_cast; nlinarith
  · have hm_pos : 0 < -m := neg_pos.2 hm
    have hτ_lt : (τ : ℝ) < 1 / (-m) := (lt_div_iff₀ hm_pos).2 (by linarith)
    let τ₀ : ℝ≥0 := ⟨((τ : ℝ) + 1 / (-m)) / 2, by positivity⟩
    have hτ₀_val : (τ₀ : ℝ) = ((τ : ℝ) + 1 / (-m)) / 2 := rfl
    have hτ₀_lt : τ < τ₀ := NNReal.coe_lt_coe.1 (by rw [hτ₀_val]; linarith)
    have hτ₀_bound : (τ₀ : ℝ) < 1 / (-m) := by rw [hτ₀_val]; linarith
    refine ⟨τ₀, hτ₀_lt,
      (hconv ν₀).moreauYosida_ne_bot hφ hν₀top hν₀bot (hτ.trans hτ₀_lt) ?_⟩
    have : (τ₀ : ℝ) * (-m) < 1 := (lt_div_iff₀ hm_pos).1 hτ₀_bound
    linarith

/-- **Existence of the JKO step without compactness.** Let `φ` be lower semicontinuous on
`P₂(E)`, never `⊥`, finite somewhere, and `m`-convex along generalized geodesics based at every
law. Then for every `τ > 0` with `1 + m τ > 0`, the JKO resolvent `J_τ μ` is nonempty. -/
theorem moreauYosidaResolvent_nonempty_of_generalizedGeodesicallyConvex
    (hφ : LowerSemicontinuous φ) (hconv : ∀ ν, GeneralizedGeodesicallyConvex m φ ν)
    (hτ : 0 < τ) (hmτ : 0 < 1 + m * τ) (hbot : ∀ ν, φ ν ≠ ⊥)
    (hdom : ∃ ν, φ ν ≠ ⊤) (μ : WassersteinSpace 2 E) :
    (moreauYosidaResolvent φ τ μ).Nonempty := by
  obtain ⟨ν₀, hν₀⟩ := hdom
  obtain ⟨τ₀, hττ₀, h₀⟩ :=
    exists_moreauYosida_ne_bot_gt hφ hconv hτ hmτ hν₀ (hbot ν₀)
  exact PenalizedConvex.moreauYosidaResolvent_nonempty hφ
    (penalizedConvex_of_generalizedGeodesicallyConvex hconv hτ hmτ.le) hτ hmτ
    (moreauYosida_ne_bot_of_lt hττ₀ (edist_ne_top μ ν₀) h₀)

/-- **Existence and uniqueness of the JKO step.** Under the hypotheses of
`TauCeti.moreauYosidaResolvent_nonempty_of_generalizedGeodesicallyConvex`, `J_τ μ` contains a
unique point. -/
theorem existsUnique_mem_moreauYosidaResolvent_of_generalizedGeodesicallyConvex
    (hφ : LowerSemicontinuous φ) (hconv : ∀ ν, GeneralizedGeodesicallyConvex m φ ν)
    (hτ : 0 < τ) (hmτ : 0 < 1 + m * τ) (hbot : ∀ ν, φ ν ≠ ⊥)
    (hdom : ∃ ν, φ ν ≠ ⊤) (μ : WassersteinSpace 2 E) :
    ∃! ν, ν ∈ moreauYosidaResolvent φ τ μ := by
  obtain ⟨ν, hν⟩ :=
    moreauYosidaResolvent_nonempty_of_generalizedGeodesicallyConvex hφ hconv hτ hmτ hbot hdom μ
  exact ⟨ν, hν, fun ν' hν' ↦
    (hconv μ).subsingleton_moreauYosidaResolvent hτ hmτ hbot hdom hν' hν⟩

private lemma exists_moreauYosida_and_penalizedConvex
    (hφ : LowerSemicontinuous φ) (hconv : ∀ ν, GeneralizedGeodesicallyConvex lam φ ν)
    {ν₀ : WassersteinSpace 2 E} (hν₀top : φ ν₀ ≠ ⊤) (hν₀bot : φ ν₀ ≠ ⊥) :
    ∃ τ₀ : ℝ≥0, 0 < τ₀ ∧ moreauYosida φ τ₀ ν₀ ≠ ⊥ ∧
      ∀ τ : ℝ≥0, 0 < τ → τ < τ₀ → PenalizedConvex lam τ φ := by
  let τ₀ : ℝ≥0 := ⟨(2 * (|lam| + 1))⁻¹, by positivity⟩
  have hτ₀ : 0 < τ₀ := Subtype.mk_lt_mk.2 (by positivity)
  have hpos : ∀ {δ : ℝ≥0}, δ ≤ τ₀ → 0 < 1 + lam * (δ : ℝ) := fun {δ} hδ ↦ by
    have hδr : (δ : ℝ) ≤ (2 * (|lam| + 1))⁻¹ := hδ
    have habs : |lam| * (δ : ℝ) ≤ 1 / 2 := calc
      |lam| * (δ : ℝ) ≤ (|lam| + 1) * (2 * (|lam| + 1))⁻¹ := by
        gcongr; linarith
      _ = 1 / 2 := by field_simp [show |lam| + 1 ≠ 0 by positivity]
    have heq : |lam * (δ : ℝ)| = |lam| * δ := by
      rw [abs_mul, abs_of_nonneg (NNReal.coe_nonneg δ)]
    linarith [neg_abs_le (lam * (δ : ℝ))]
  refine ⟨τ₀, hτ₀,
    (hconv ν₀).moreauYosida_ne_bot hφ hν₀top hν₀bot hτ₀ (hpos le_rfl), ?_⟩
  exact fun τ hτ hττ₀ ↦
    penalizedConvex_of_generalizedGeodesicallyConvex hconv hτ (hpos hττ₀.le).le

/-- **Existence of Wasserstein `EVI_λ` flows and uniform convergence of JKO schemes**
(Ambrosio–Gigli–Savaré, Theorems 4.1.2 and 11.2.1). Let `φ : WassersteinSpace 2 E → EReal`
be lower semicontinuous, `lam`-convex along generalized geodesics at every law of `P₂(E)`, and
never `-∞`. Then from every `μ₀` of finite energy starts an `EVI_λ` flow `u` (`u 0 = μ₀`),
and each JKO interpolant `t ↦ J j ⌈t / τ j⌉₊` with `τ j → 0⁺` converges uniformly
to `u` on compact time intervals `[0, T]`. -/
theorem exists_isEVISolution_tendstoUniformlyOn_of_generalizedGeodesicallyConvex
    (hφ : LowerSemicontinuous φ) (hconv : ∀ ν, GeneralizedGeodesicallyConvex lam φ ν)
    (hbot : ∀ ν, φ ν ≠ ⊥) {μ₀ : WassersteinSpace 2 E} (hμ₀ : φ μ₀ ≠ ⊤) :
    ∃ u : ℝ → WassersteinSpace 2 E, u 0 = μ₀ ∧ IsEVISolution lam φ u ∧
      ∀ (τ : ℕ → ℝ≥0) (J : ℕ → ℕ → WassersteinSpace 2 E), (∀ j, 0 < τ j) →
        Tendsto τ atTop (𝓝 0) → (∀ j, J j 0 = μ₀) →
        (∀ j k, J j (k + 1) ∈ moreauYosidaResolvent φ (τ j) (J j k)) →
        ∀ T : ℝ, TendstoUniformlyOn
          (fun j (t : ℝ) ↦ J j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T) := by
  obtain ⟨τ₀, hτ₀, h₀, hPen⟩ :=
    exists_moreauYosida_and_penalizedConvex hφ hconv hμ₀ (hbot μ₀)
  exact exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex
    hφ hτ₀ hτ₀ hPen h₀ hμ₀

/-- **Existence of Wasserstein `EVI_λ` flows on `closure {μ | φ μ ≠ ⊤}`.** Under the
hypotheses of `TauCeti.exists_isEVISolution_tendstoUniformlyOn_of_generalizedGeodesicallyConvex`,
an `EVI_λ` gradient flow starts from every `μ₀ ∈ closure {μ | φ μ ≠ ⊤}`. -/
theorem exists_isEVISolution_of_mem_closure_of_generalizedGeodesicallyConvex
    (hφ : LowerSemicontinuous φ) (hconv : ∀ ν, GeneralizedGeodesicallyConvex lam φ ν)
    (hbot : ∀ ν, φ ν ≠ ⊥) {μ₀ : WassersteinSpace 2 E}
    (hμ₀ : μ₀ ∈ closure {μ | φ μ ≠ ⊤}) :
    ∃ u : ℝ → WassersteinSpace 2 E, IsEVISolution lam φ u ∧ u 0 = μ₀ := by
  obtain ⟨seq, hseq, -⟩ := mem_closure_iff_seq_limit.1 hμ₀
  obtain ⟨τ₀, hτ₀, h₀, hPen⟩ :=
    exists_moreauYosida_and_penalizedConvex hφ hconv (hseq 0) (hbot (seq 0))
  exact exists_isEVISolution_of_mem_closure_of_penalizedConvex hφ hτ₀ hτ₀ hPen h₀ hμ₀

/-- **Characterization of the Wasserstein `EVI_λ` domain.** For an energy on `P₂(E)` that is
lower semicontinuous, `lam`-convex along generalized geodesics based at every law, and never `-∞`,
`TauCeti.eviDomain lam φ = closure {μ | φ μ ≠ ⊤}`. -/
theorem eviDomain_eq_closure_of_generalizedGeodesicallyConvex
    (hφ : LowerSemicontinuous φ) (hconv : ∀ ν, GeneralizedGeodesicallyConvex lam φ ν)
    (hbot : ∀ ν, φ ν ≠ ⊥) : eviDomain lam φ = closure {μ | φ μ ≠ ⊤} :=
  Set.Subset.antisymm eviDomain_subset_closure fun _ hμ ↦
    mem_eviDomain.2
      (exists_isEVISolution_of_mem_closure_of_generalizedGeodesicallyConvex hφ hconv hbot hμ)

end TauCeti
