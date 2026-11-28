/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.NormalForm
public import TauCeti.Analysis.Contour.Residue.Basic
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Entire
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Laplace
import Mathlib.Analysis.Calculus.DSlope
import TauCeti.Analysis.Contour.Residue.Germ
import TauCeti.Analysis.LaplaceTransform.Meromorphic
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.FiniteSum

/-!
# Poles of the one-sided prime remainder transform

This file studies the meromorphic normal form of `(G_q(z) / z - G_q(1)) / (z - 1)`, where
`G_q` is the signed mean of logarithmic derivatives. For an odd prime `d` coprime to `q`,
`TauCeti.OneSidedBound.hasLaplace_primeRemainderTransform` identifies the normal form on
`Re z > 1` with the Laplace transform of the normalized first Riesz remainder at `z - 1`.
The point `1` is removable. Away from `0` and `1`, the only possible poles are simple.
The residue is the difference of the total untwisted and twisted zero multiplicities divided by
`φ(q) z (1 - z)`. Where the twists do not vanish, the untwisted zeros cannot cancel, and
the residue at a positive real pole is strictly positive. These are the pole and sign
conditions used in the one-sided Landau argument below: a one-sided bound and nonvanishing
of the twists on the relevant real interval give absolute convergence past `Re s = 1`.

The normalization and signed multiplicities follow `New.isPolar_primeRemainder` in
`New/Reduction/Zeros/PrimeError` of lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open Complex DirichletCharacter Filter Set
open scoped Topology

namespace TauCeti.OneSidedBound

variable (d q : ℕ) [Fact d.Prime] [NeZero q]

local instance : NeZero (q * d) :=
  ⟨Nat.mul_ne_zero (NeZero.ne q) (Fact.out : d.Prime).ne_zero⟩

/-- The meromorphic normal form of `(G_q(z) / z - G_q(1)) / (z - 1)`. -/
noncomputable def primeRemainderTransform : ℂ → ℂ :=
  toMeromorphicNFOn (fun z ↦ (logDerivMean d q z / z - logDerivMean d q 1) / (z - 1)) univ

/-- The transform expression is meromorphic in normal form. -/
theorem meromorphicNFOn_primeRemainderTransform :
    MeromorphicNFOn (primeRemainderTransform d q) univ :=
  meromorphicNFOn_toMeromorphicNFOn _ _

/-- The defining quotient represents the punctured germ of the transform expression. -/
theorem primeRemainderTransform_eventuallyEq (s : ℂ) :
    primeRemainderTransform d q =ᶠ[𝓝[≠] s]
      fun z ↦ (logDerivMean d q z / z - logDerivMean d q 1) / (z - 1) := by
  have h := meromorphic_logDerivMean (d := d) (q := q)
  have hq : Meromorphic (fun z ↦ (logDerivMean d q z / z - logDerivMean d q 1) / (z - 1)) := by
    fun_prop
  exact (meromorphicOn_univ.mpr hq).toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ s)

private theorem primeRemainderTransform_analyticGerm {s : ℂ} (hs : 1 ≤ s.re) :
    AnalyticAt ℂ (primeRemainderTransform d q) s ∧
      primeRemainderTransform d q =ᶠ[𝓝 s] dslope (fun z ↦ logDerivMean d q z / z) 1 := by
  have ha : AnalyticAt ℂ (fun z ↦ logDerivMean d q z / z) s :=
    (analyticAt_logDerivMean_of_one_le_re (d := d) (q := q) hs).fun_div
      analyticAt_id (ne_zero_of_re_pos (zero_lt_one.trans_le hs))
  have hd := ha.dslope 1
  have hnf := meromorphicNFOn_primeRemainderTransform d q (mem_univ s)
  have he := (hnf.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hd.meromorphicNFAt).mp <|
    (primeRemainderTransform_eventuallyEq d q s).trans <| by
      have hne : ∀ᶠ z in 𝓝[≠] s, z ≠ (1 : ℂ) := by
        rcases eq_or_ne s 1 with rfl | h
        · exact self_mem_nhdsWithin
        · exact (eventually_ne_nhds h).filter_mono nhdsWithin_le_nhds
      filter_upwards [hne] with z hz
      rw [dslope_of_ne _ hz, slope_def_field, div_one]
  exact ⟨hd.congr he.symm, he⟩

/-- The transform expression is analytic on `Re s ≥ 1`; in particular `1` is removable. -/
theorem analyticAt_primeRemainderTransform_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    AnalyticAt ℂ (primeRemainderTransform d q) s :=
  (primeRemainderTransform_analyticGerm d q hs).1

/-- On `Re s ≥ 1`, the transform is the divided difference of `G_q(z) / z` at `1`.
At `s = 1` this gives the derivative, not the junk value of the defining quotient. -/
theorem primeRemainderTransform_eq_dslope {s : ℂ} (hs : 1 ≤ s.re) :
    primeRemainderTransform d q s = dslope (fun z ↦ logDerivMean d q z / z) 1 s :=
  (primeRemainderTransform_analyticGerm d q hs).2.eq_of_nhds

/-- On `Re s > 1`, the Laplace transform of `v ↦ R_q(exp v)` at `s - 1` agrees with
its meromorphic normal form. -/
theorem hasLaplace_primeRemainderTransform (hd : d ≠ 2) (hc : q.Coprime d) {s : ℂ}
    (hs : 1 < s.re) :
    HasLaplace (fun v : ℝ ↦ (primeRemainder d q (Real.exp v) : ℂ)) (s - 1)
      (primeRemainderTransform d q s) := by
  rw [primeRemainderTransform_eq_dslope d q hs.le, dslope_of_ne _ (ne_of_apply_ne re hs.ne'),
    slope_def_field, div_one]
  exact hasLaplace_primeRemainder hd hc hs

/-- The constant `-1` in the numerator of `G_q` contributes the reciprocal term. -/
private theorem primeRemainderTransform_eventuallyEq_rieszRemainderMellin (s : ℂ) :
    primeRemainderTransform d q =ᶠ[𝓝[≠] s]
      (q.totient : ℂ)⁻¹ • (((∑ ψ : DirichletCharacter ℂ q,
        rieszRemainderMellin ψ.entireLFunction) - (∑ ψ : DirichletCharacter ℂ q,
        rieszRemainderMellin (quadraticTwist d ψ).entireLFunction)) + fun z : ℂ ↦ z⁻¹) := by
  have hterm {L : ℂ → ℂ} (hL : Meromorphic L) (ha : AnalyticAt ℂ L 1) (h₁ : L 1 ≠ 0) :
      rieszRemainderMellin L =ᶠ[𝓝[≠] s]
        fun z ↦ (z * logDeriv L 1 - logDeriv L z) / (z * (z - 1)) := by
    have hord := ha.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr h₁
    simpa [hord, ha.logDerivFinitePart_eq_logDeriv h₁] using hL.rieszRemainderMellin_eventuallyEq s
  have hu := (Finset.univ : Finset (DirichletCharacter ℂ q)).eventually_all.mpr
    fun ψ _ ↦ hterm (fun z ↦ (ψ.analyticAt_entireLFunction z).meromorphicAt)
      (ψ.analyticAt_entireLFunction 1) (ψ.entireLFunction_ne_zero_of_one_le_re (by simp))
  have ht := (Finset.univ : Finset (DirichletCharacter ℂ q)).eventually_all.mpr
    fun ψ _ ↦ hterm (fun z ↦ ((quadraticTwist d ψ).analyticAt_entireLFunction z).meromorphicAt)
      ((quadraticTwist d ψ).analyticAt_entireLFunction 1)
      ((quadraticTwist d ψ).entireLFunction_ne_zero_of_one_le_re (by simp))
  have hne (a : ℂ) : ∀ᶠ z in 𝓝[≠] s, z ≠ a := by
    rcases eq_or_ne s a with rfl | h
    · exact self_mem_nhdsWithin
    · exact eventually_ne_nhdsWithin h
  filter_upwards [primeRemainderTransform_eventuallyEq d q s, hu, ht, hne 0, hne 1]
    with z hz hu ht hz₀ hz₁
  rw [hz, logDerivMean_def, logDerivMean_def]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply, Finset.sum_apply]
  rw [Finset.sum_congr rfl hu, Finset.sum_congr rfl ht]
  simp only [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum]
  field_simp [sub_ne_zero.mpr hz₁]
  ring

/-- Away from `0` the transform has at most a simple pole. -/
theorem neg_one_le_meromorphicOrderAt_primeRemainderTransform {s : ℂ} (h₀ : s ≠ 0) :
    -1 ≤ meromorphicOrderAt (primeRemainderTransform d q) s := by
  have hφ : (q.totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  have hu (ψ : DirichletCharacter ℂ q) : Meromorphic ψ.entireLFunction :=
    fun z ↦ (ψ.analyticAt_entireLFunction z).meromorphicAt
  have ht (ψ : DirichletCharacter ℂ q) : Meromorphic (quadraticTwist d ψ).entireLFunction :=
    fun z ↦ ((quadraticTwist d ψ).analyticAt_entireLFunction z).meromorphicAt
  rw [meromorphicOrderAt_congr (primeRemainderTransform_eventuallyEq_rieszRemainderMellin d q s),
    meromorphicOrderAt_const_smul_eq_meromorphicOrderAt (inv_ne_zero hφ)]
  have hinv : AnalyticAt ℂ (fun z : ℂ ↦ z⁻¹) s := analyticAt_id.inv h₀
  have hsum := neg_one_le_meromorphicOrderAt_sum_sub_rieszRemainderMellin
    (t := Finset.univ) (u := Finset.univ) (fun ψ _ ↦ hu ψ) (fun ψ _ ↦ ht ψ) h₀
  have hinv' : -1 ≤ meromorphicOrderAt (fun z : ℂ ↦ z⁻¹) s :=
    (by decide : (-1 : WithTop ℤ) ≤ 0).trans hinv.meromorphicOrderAt_nonneg
  exact (le_min hsum hinv').trans
    (meromorphicOrderAt_add
      ((MeromorphicAt.sum fun ψ _ ↦ meromorphicAt_rieszRemainderMellin ψ.entireLFunction s).sub
        (MeromorphicAt.sum fun ψ _ ↦ meromorphicAt_rieszRemainderMellin
          (quadraticTwist d ψ).entireLFunction s)) hinv.meromorphicAt)

/-- The residue is the total untwisted vanishing order minus the total twisted vanishing
    order, scaled by `1 / (φ(q) s (1 - s))`. -/
theorem residue_primeRemainderTransform {s : ℂ} (h₀ : s ≠ 0) :
    Contour.residue (primeRemainderTransform d q) s =
      (∑ ψ : DirichletCharacter ℂ q, ((analyticOrderNatAt ψ.entireLFunction s : ℂ) -
        (analyticOrderNatAt (quadraticTwist d ψ).entireLFunction s : ℂ))) /
        ((Nat.totient q : ℂ) * s * (1 - s)) := by
  let U := fun ψ : DirichletCharacter ℂ q ↦ ψ.entireLFunction
  let T := fun ψ : DirichletCharacter ℂ q ↦ (quadraticTwist d ψ).entireLFunction
  have hu (ψ : DirichletCharacter ℂ q) (z : ℂ) : AnalyticAt ℂ (U ψ) z :=
    ψ.analyticAt_entireLFunction z
  have ht (ψ : DirichletCharacter ℂ q) (z : ℂ) : AnalyticAt ℂ (T ψ) z :=
    (quadraticTwist d ψ).analyticAt_entireLFunction z
  have hm (L : DirichletCharacter ℂ q → ℂ → ℂ) :
      MeromorphicAt (∑ ψ, rieszRemainderMellin (L ψ)) s :=
    MeromorphicAt.sum fun ψ _ ↦ meromorphicAt_rieszRemainderMellin (L ψ) s
  have hsum (L : DirichletCharacter ℂ q → ℂ → ℂ) (hL : ∀ ψ z, AnalyticAt ℂ (L ψ) z) :
      Contour.residue (∑ ψ, rieszRemainderMellin (L ψ)) s =
        (∑ ψ, (analyticOrderNatAt (L ψ) s : ℂ)) / (s * (1 - s)) := by
    have hr := residue_sum_rieszRemainderMellin (t := Finset.univ) (L := L)
      (fun _ ↦ 1) (fun ψ _ z ↦ (hL ψ z).meromorphicAt) h₀
    have hord (ψ : DirichletCharacter ℂ q) :
        ((meromorphicOrderAt (L ψ) s).untop₀ : ℂ) = analyticOrderNatAt (L ψ) s := by
      rw [(hL ψ s).meromorphicOrderAt_eq, analyticOrderNatAt]
      cases analyticOrderAt (L ψ) s <;> simp
    simpa [hord] using hr
  have hinv : AnalyticAt ℂ (fun z : ℂ ↦ z⁻¹) s := analyticAt_id.inv h₀
  rw [Contour.residue_congr_nhdsNE
      (primeRemainderTransform_eventuallyEq_rieszRemainderMellin d q s),
    Contour.residue_const_smul, Contour.residue_add ((hm U).sub (hm T)) hinv.meromorphicAt,
    Contour.residue_sub (hm U) (hm T), Contour.residue_eq_zero_of_analyticAt hinv,
    add_zero, hsum U hu, hsum T ht, ← sub_div, ← Finset.sum_sub_distrib, smul_eq_mul]
  simp only [U, T, div_eq_mul_inv, mul_inv]
  ring

private theorem residue_eq_sum_order_of_twists_ne_zero {s : ℂ} (h₀ : s ≠ 0)
    (ht : ∀ ψ : DirichletCharacter ℂ q, (quadraticTwist d ψ).entireLFunction s ≠ 0) :
    Contour.residue (primeRemainderTransform d q) s =
      ((∑ ψ : DirichletCharacter ℂ q, analyticOrderNatAt ψ.entireLFunction s : ℕ) : ℂ) /
        ((Nat.totient q : ℂ) * s * (1 - s)) := by
  rw [residue_primeRemainderTransform d q h₀, Nat.cast_sum]
  refine congrArg (· / _) (Finset.sum_congr rfl fun ψ _ ↦ ?_)
  have hψ := not_not.mp (mt apply_eq_zero_of_analyticOrderNatAt_ne_zero (ht ψ))
  simp only [hψ, Nat.cast_zero, sub_zero]

/-- At a nonzero point where none of the twisted entire functions vanish, a pole of the
    transform detects a zero of an untwisted entire function, and conversely. -/
theorem meromorphicOrderAt_primeRemainderTransform_neg_iff {s : ℂ} (h₀ : s ≠ 0)
    (ht : ∀ ψ : DirichletCharacter ℂ q, (quadraticTwist d ψ).entireLFunction s ≠ 0) :
    meromorphicOrderAt (primeRemainderTransform d q) s < 0 ↔
      ∃ ψ : DirichletCharacter ℂ q, ψ.entireLFunction s = 0 := by
  rcases eq_or_ne s 1 with rfl | h₁
  · have h := analyticAt_primeRemainderTransform_of_one_le_re d q (s := 1) (by simp)
    exact iff_of_false (not_lt.mpr h.meromorphicOrderAt_nonneg) fun ⟨ψ, hψ⟩ ↦
      ψ.entireLFunction_ne_zero_of_one_le_re (by simp) hψ
  have hφ : (q.totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  rw [Contour.meromorphicOrderAt_lt_zero_iff_residue_ne_zero
    (meromorphicNFOn_primeRemainderTransform d q (mem_univ s)).meromorphicAt
    (neg_one_le_meromorphicOrderAt_primeRemainderTransform d q h₀),
    residue_eq_sum_order_of_twists_ne_zero d q h₀ ht,
    div_ne_zero_iff, and_iff_left (mul_ne_zero (mul_ne_zero hφ h₀) (sub_ne_zero.mpr h₁.symm)),
    Nat.cast_ne_zero]
  simp only [ne_eq, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ Nat.zero_le _), Finset.mem_univ,
    true_implies, not_forall]
  refine exists_congr fun ψ ↦ ?_
  rw [analyticOrderNatAt, ENat.toNat_eq_zero,
    or_iff_left (ψ.analyticOrderAt_entireLFunction_ne_top s),
    (ψ.analyticAt_entireLFunction s).analyticOrderAt_eq_zero, not_ne_iff]

/-- At a positive real pole where the twists are nonvanishing, the residue has strictly
    positive real part. -/
theorem re_residue_primeRemainderTransform_pos {σ : ℝ} (hσ : 0 < σ)
    (ht : ∀ ψ : DirichletCharacter ℂ q, (quadraticTwist d ψ).entireLFunction σ ≠ 0)
    (hp : meromorphicOrderAt (primeRemainderTransform d q) (σ : ℂ) < 0) :
    0 < (Contour.residue (primeRemainderTransform d q) σ).re := by
  have h₀ := Complex.ofReal_ne_zero.mpr hσ.ne'
  have h₁ : σ < 1 := by
    by_contra! h
    exact (analyticAt_primeRemainderTransform_of_one_le_re d q (s := σ)
      (by simpa using h)).meromorphicOrderAt_nonneg.not_gt hp
  have hr := (Contour.meromorphicOrderAt_lt_zero_iff_residue_ne_zero
    (meromorphicNFOn_primeRemainderTransform d q (mem_univ (σ : ℂ))).meromorphicAt
    (neg_one_le_meromorphicOrderAt_primeRemainderTransform d q h₀)).mp hp
  rw [residue_eq_sum_order_of_twists_ne_zero d q h₀ ht] at hr ⊢
  have hsum : 0 < ∑ ψ : DirichletCharacter ℂ q, analyticOrderNatAt ψ.entireLFunction σ :=
    Nat.pos_of_ne_zero (Nat.cast_ne_zero.mp (div_ne_zero_iff.mp hr).1)
  calc
    0 < ((∑ ψ : DirichletCharacter ℂ q, analyticOrderNatAt ψ.entireLFunction σ : ℕ) : ℝ) /
        ((q.totient : ℝ) * σ * (1 - σ)) :=
      div_pos (Nat.cast_pos.mpr hsum)
        (mul_pos (mul_pos (Nat.cast_pos.mpr (NeZero.pos q.totient)) hσ) (sub_pos.mpr h₁))
    _ = _ := by
      refine (Complex.ofReal_re _).symm.trans ?_
      push_cast
      rfl

/-- An eventual bound `R_q(x) ≤ C * x ^ (β - 1)` and nonvanishing of the twisted
L-functions on the real interval `(β, 1)` ensure that the continued transform is analytic
on `Re s > β` and represented there by the absolutely convergent Laplace integral. -/
theorem analyticAt_and_hasLaplace_primeRemainderTransform_of_eventually_le
    (hd : d ≠ 2) (hc : q.Coprime d) {β C : ℝ} (hβ : 0 ≤ β)
    (hR : ∀ᶠ x : ℝ in atTop, primeRemainder d q x ≤ C * x ^ (β - 1))
    (htwist : ∀ b ∈ Ioo β 1, ∀ ψ : DirichletCharacter ℂ q,
      (ψ.legendreTwist d).LFunction (b : ℂ) ≠ 0) {s : ℂ} (hs : β < s.re) :
    AnalyticAt ℂ (primeRemainderTransform d q) s ∧
      HasLaplace (fun u : ℝ ↦ (primeRemainder d q (Real.exp u) : ℂ)) (s - 1)
        (primeRemainderTransform d q s) := by
  let F := primeRemainderTransform d q
  let g := fun u : ℝ ↦ Real.exp u * primeRemainder d q (Real.exp u)
  obtain ⟨u₀, hbound⟩ := exists_ae_le_exp_of_eventually_le_rpow hR
  have hg : ∀ᵐ u ∂MeasureTheory.volume.restrict (Ioi u₀), g u ≤ C * Real.exp (β * u) := by
    filter_upwards [hbound] with u hu
    calc
      g u ≤ Real.exp u * (C * Real.exp ((β - 1) * u)) :=
        mul_le_mul_of_nonneg_left hu (Real.exp_nonneg u)
      _ = C * Real.exp (β * u) := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring
  have hF : MeromorphicNFOn F {z | β < z.re} :=
    fun z _ ↦ meromorphicNFOn_primeRemainderTransform d q (mem_univ z)
  have hshift (z : ℂ) : HasLaplace (fun u ↦ (g u : ℂ)) z (F z) ↔
      HasLaplace (fun u ↦ (primeRemainder d q (Real.exp u) : ℂ)) (z - 1) (F z) := by
    simpa only [g, one_mul, ofReal_mul, ofReal_exp, smul_eq_mul] using
      (hasLaplace_cexp_mul_smul_iff (s := z) (w := 1) (z := F z)
        (f := fun u ↦ (primeRemainder d q (Real.exp u) : ℂ)))
  have hL (z : ℂ) (hz : 1 < z.re) :=
    (hshift z).mpr (hasLaplace_primeRemainderTransform d q hd hc hz)
  have hsign (b : ℝ) (hb : b ∈ Ioc β 1) (hp : meromorphicOrderAt F (b : ℂ) < 0) :
      0 ≤ (meromorphicTrailingCoeffAt F (b : ℂ)).re := by
    have hb₁ : b < 1 := by
      by_contra! hb'
      exact hp.not_ge (analyticAt_primeRemainderTransform_of_one_le_re d q
        (by simpa using hb')).meromorphicOrderAt_nonneg
    have hb₀ := hβ.trans_lt hb.1
    have hlo := neg_one_le_meromorphicOrderAt_primeRemainderTransform d q
      (ofReal_ne_zero.mpr hb₀.ne')
    have hord : meromorphicOrderAt F (b : ℂ) = -1 := by
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hp.ne_top
      have hneg : n < 0 := WithTop.coe_lt_coe.mp (hn ▸ hp)
      have hle : -1 ≤ n := WithTop.coe_le_coe.mp (hn ▸ hlo)
      have he : n = -1 := by omega
      simpa [he] using hn.symm
    rw [← Contour.residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one hord]
    exact (re_residue_primeRemainderTransform_pos d q hb₀ (fun ψ ↦ by
      simpa only [quadraticTwist_eq_legendreTwist, entireLFunction_legendreTwist _ d hd hc]
        using htwist b ⟨hb.1, hb₁⟩ ψ) hp).le
  obtain ⟨hord, hLap⟩ := hasLaplace_toMeromorphicNFOn_of_ae_le_exp hg hF.meromorphicOn hL hsign
  rw [toMeromorphicNFOn_eq_self.mpr hF] at hLap
  exact ⟨(hF hs).meromorphicOrderAt_nonneg_iff_analyticAt.mp (hord s hs), (hshift s).mp (hLap s hs)⟩

end TauCeti.OneSidedBound
