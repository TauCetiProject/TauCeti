/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Laurent.Expansion
public import TauCeti.Analysis.Contour.Residue.Basic
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.RegularEval
import TauCeti.Analysis.Contour.Residue.PrincipalPart

/-!
# Circle Laurent coefficients and principal parts of meromorphic germs

This file bridges analytic Laurent series expansions on concentric annuli and punctured disks
(`TauCeti.HasLaurentSeriesOnAnnulus`, `TauCeti.circleLaurentCoeff`, `TauCeti.laurentPosPart`,
`TauCeti.laurentNegPart`) with the algebraic principal-part / regular-part decomposition of
meromorphic germs over `ℂ` (`TauCeti.meromorphicGerms.principalPart`,
`TauCeti.holomorphicStructureSheaf.regularPart`, `TauCeti.holomorphicStructureSheaf.regularEval`)
and contour residues (`TauCeti.Contour.residue`).

For any meromorphic germ `φ : meromorphicGerms ℂ c` represented by `f : ℂ → ℂ`, both on
sufficiently small circles around `c` and on every interior circle of radius `ρ ∈ (0, R)` when `f`
is complex-differentiable on `Metric.eball c R \ {c}`:

* the negative circle Laurent coefficients `circleLaurentCoeff f c ρ (-(k + 1))` agree with
  `(principalPart φ).coeff (k + 1)`;
* the `(-1)`-st circle Laurent coefficient equals `Contour.residue f c`;
* the `0`-th circle Laurent coefficient equals the stalk evaluation at `c` of `regularPart c φ`
  (and `regularEval c φ` when `φ` is regular);
* the negative Laurent sum `laurentNegPart (circleLaurentCoeff f c ρ) c w` equals
  `(principalPart φ).eval (w - c)⁻¹`;
* on `Metric.eball c R \ {c}`, the nonnegative Laurent sum
  `laurentPosPart (circleLaurentCoeff f c ρ) c` recovers `f - (principalPart φ).eval (· - c)⁻¹`.

## Main results

* `Polynomial.hasLaurentSeriesOnAnnulus_eval_inv_sub` and
  `Polynomial.circleLaurentCoeff_eval_inv_sub`: Laurent expansion and circle Laurent coefficients of
  `w ↦ P.eval (w - c)⁻¹` for `P : ℂ[X]`.
* `TauCeti.meromorphicGerms.eventually_circleLaurentCoeff_neg_add_one_eq_coeff_principalPart` and
  `TauCeti.meromorphicGerms.circleLaurentCoeff_neg_add_one_eq_coeff_principalPart`: negative circle
  Laurent coefficients compute the coefficients of `meromorphicGerms.principalPart`.
* `TauCeti.eventually_circleLaurentCoeff_neg_one_eq_residue` and
  `TauCeti.circleLaurentCoeff_neg_one_eq_residue`: the `(-1)`-st circle Laurent coefficient computes
  `Contour.residue`.
* `TauCeti.meromorphicGerms.eventually_circleLaurentCoeff_zero_eq_eval_regularPart`,
  `TauCeti.meromorphicGerms.circleLaurentCoeff_zero_eq_eval_regularPart`, and
  `TauCeti.holomorphicStructureSheaf.circleLaurentCoeff_zero_eq_regularEval`: the `0`-th circle
  Laurent coefficient computes the value at `c` of `regularPart` / `regularEval`.
* `TauCeti.meromorphicGerms.laurentNegPart_circleLaurentCoeff_eq_eval_principalPart` and
  `TauCeti.meromorphicGerms.laurentPosPart_circleLaurentCoeff_eq_sub_principalPart`: the analytic
  Laurent splitting `laurentPosPart + laurentNegPart` on a punctured disk agrees with the algebraic
  principal-part splitting of `φ`.

## References

* Lars V. Ahlfors, *Complex Analysis*, 3rd edition, McGraw-Hill, 1979, Chapter 5, §1.2–§1.3.
* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §1.
-/

public section

open Complex Filter Metric Polynomial Set Topology
open scoped ContDiff ENNReal Manifold NNReal

namespace TauCeti

/-- The negative-degree Laurent terms `(w - c) ^ (-(k + 1)) • P.coeff (k + 1)` of a polynomial
`P : ℂ[X]` have finite support and sum to `P.eval (w - c)⁻¹ - P.coeff 0`. -/
private theorem hasSum_zpow_neg_add_one_smul_coeff_succ (P : ℂ[X]) (c w : ℂ) :
    HasSum (fun k : ℕ => (w - c) ^ (-((k : ℤ) + 1)) • P.coeff (k + 1))
      (P.eval (w - c)⁻¹ - P.coeff 0) := by
  have hterm : ∀ k : ℕ,
      (w - c) ^ (-((k : ℤ) + 1)) • P.coeff (k + 1) =
        P.coeff (k + 1) * ((w - c)⁻¹) ^ (k + 1) := fun k => by
    rw [← Nat.cast_add_one, zpow_neg, zpow_natCast, ← inv_pow, smul_eq_mul, mul_comm]
  simp_rw [hterm]
  have hsum : HasSum (fun k : ℕ => P.coeff (k + 1) * ((w - c)⁻¹) ^ (k + 1))
      (∑ k ∈ Finset.range P.natDegree, P.coeff (k + 1) * ((w - c)⁻¹) ^ (k + 1)) := by
    refine hasSum_sum_of_ne_finset_zero fun k hk => ?_
    rw [Finset.mem_range, not_lt] at hk
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
  have heval : ∑ k ∈ Finset.range P.natDegree, P.coeff (k + 1) * ((w - c)⁻¹) ^ (k + 1) =
      P.eval (w - c)⁻¹ - P.coeff 0 := by
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ', pow_zero, mul_one,
      add_sub_cancel_right]
  rwa [heval] at hsum

/-- A polynomial `P : ℂ[X]` evaluated at the inverted coordinate `(w - c)⁻¹` has the finite Laurent
series supported in nonpositive degrees `n ≤ 0` with coefficients `P.coeff (-n).toNat`. -/
theorem _root_.Polynomial.hasLaurentSeriesOnAnnulus_eval_inv_sub (P : ℂ[X]) (c : ℂ)
    {r : ℝ} {R : ℝ≥0∞} (hr : 0 ≤ r) (hrR : ENNReal.ofReal r < R) :
    HasLaurentSeriesOnAnnulus (fun w => P.eval (w - c)⁻¹)
      (fun n : ℤ => if n ≤ 0 then P.coeff (-n).toNat else 0) c r R where
  r_nonneg := hr
  r_lt := hrR
  hasSum {w} _ := by
    have hp : HasSum (fun n : ℕ =>
        (w - c) ^ (n : ℤ) • (if (n : ℤ) ≤ 0 then P.coeff (-(n : ℤ)).toNat else 0))
        (P.coeff 0) := by
      refine (hasSum_ite_eq (0 : ℕ) (P.coeff 0)).congr_fun fun n => ?_
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · simp [hn]
    have hn : HasSum (fun k : ℕ =>
        (w - c) ^ (-((k : ℤ) + 1)) •
          (if -((k : ℤ) + 1) ≤ 0 then P.coeff (-(-((k : ℤ) + 1))).toNat else 0))
        (P.eval (w - c)⁻¹ - P.coeff 0) := by
      refine (hasSum_zpow_neg_add_one_smul_coeff_succ P c w).congr_fun fun k => ?_
      split_ifs with hle
      · have hnat : (-(-((k : ℤ) + 1))).toNat = k + 1 := by omega
        rw [hnat]
      · omega
    simpa only [add_sub_cancel] using HasSum.of_nat_of_neg_add_one
      (f := fun n : ℤ => (w - c) ^ n • (if n ≤ 0 then P.coeff (-n).toNat else 0)) hp hn

/-- On every circle of positive radius `ρ > 0` around `c`, the circle Laurent coefficients of
`z ↦ P.eval (z - c)⁻¹` extract the coefficients of `P` in nonpositive degrees and vanish in positive
degrees. -/
theorem _root_.Polynomial.circleLaurentCoeff_eval_inv_sub (P : ℂ[X]) (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (n : ℤ) :
    circleLaurentCoeff (fun z => P.eval (z - c)⁻¹) c ρ n =
      if n ≤ 0 then P.coeff (-n).toNat else 0 :=
  (P.hasLaurentSeriesOnAnnulus_eval_inv_sub c le_rfl
    (r := 0) (R := ⊤) (by simp)).circleLaurentCoeff_eq hρ ENNReal.ofReal_lt_top n

/-- When the negative-degree coefficients `a (-(k + 1))` match those of a polynomial `P : ℂ[X]` with
`P.coeff 0 = 0`, the negative Laurent sum `laurentNegPart a c w` evaluates to `P.eval (w - c)⁻¹`. -/
theorem laurentNegPart_eq_eval_inv_sub_of_coeff_eq {a : ℤ → ℂ} {P : ℂ[X]}
    (hP : P.coeff 0 = 0) (ha : ∀ k : ℕ, a (-((k : ℤ) + 1)) = P.coeff (k + 1)) (c w : ℂ) :
    laurentNegPart a c w = P.eval (w - c)⁻¹ := by
  have hsum : HasSum (fun k : ℕ => (w - c) ^ (-((k : ℤ) + 1)) • a (-((k : ℤ) + 1)))
      (P.eval (w - c)⁻¹ - P.coeff 0) :=
    (hasSum_zpow_neg_add_one_smul_coeff_succ P c w).congr_fun fun k => by rw [ha k]
  rw [laurentNegPart_def, hsum.tsum_eq, hP, sub_zero]

namespace meromorphicGerms

/-- Local Laurent expansion of any representative `f` of a meromorphic germ `φ` at `c`, combining
`principalPart φ` in negative degrees with a Taylor series of `regularPart c φ` in nonnegative
degrees. -/
private theorem exists_hasLaurentSeriesOnAnnulus_of_coe_eq {c : ℂ} {φ : meromorphicGerms ℂ c}
    {f : ℂ → ℂ} (hφ : (φ : Germ (𝓝[≠] c) ℂ) = f) :
    ∃ (p : FormalMultilinearSeries ℂ ℂ ℂ) (R₁ : ℝ≥0∞),
      p.coeff 0 = holomorphicStructureSheaf.eval 𝓘(ℂ) ℂ c
        (holomorphicStructureSheaf.regularPart c φ) ∧
      HasLaurentSeriesOnAnnulus f
        (fun n : ℤ => if n < 0 then (principalPart φ).coeff (-n).toNat else p.coeff n.toNat)
        c 0 R₁ := by
  let s := holomorphicStructureSheaf.regularPart c φ
  obtain ⟨g, hg_mdiff, hgs⟩ := holomorphicStructureSheaf.exists_toFilterGerm_eq c s
  have hg : AnalyticAt ℂ g c := (contMDiffAt_iff_contDiffAt.1 hg_mdiff.self_of_nhds).analyticAt
  have hg_eval : holomorphicStructureSheaf.eval 𝓘(ℂ) ℂ c s = g c :=
    holomorphicStructureSheaf.eval_eq_of_toFilterGerm_eq (hgs (𝓝 c) le_rfl)
  have hsplit := congrArg Subtype.val
    (holomorphicStructureSheaf.evalInvSub_principalPart_add_toMeromorphicGerms_regularPart φ)
  rw [AddMemClass.coe_add, Polynomial.coe_evalInvSub,
    holomorphicStructureSheaf.coe_toMeromorphicGerms,
    hgs (𝓝[≠] c) nhdsWithin_le_nhds, hφ, ← Germ.coe_add, Germ.coe_eq] at hsplit
  obtain ⟨p, R₀, hp⟩ := hg
  obtain ⟨ε, hε, hεfg⟩ := EMetric.mem_nhdsWithin_iff.1 hsplit
  let R₁ : ℝ≥0∞ := min R₀ ε
  have hR₁_pos : ENNReal.ofReal 0 < R₁ := by
    rw [ENNReal.ofReal_zero]
    exact lt_min hp.r_pos hε
  have hP := (principalPart φ).hasLaurentSeriesOnAnnulus_eval_inv_sub c le_rfl hR₁_pos
  have hg_ser := hp.hasLaurentSeriesOnAnnulus.mono le_rfl (min_le_left _ _) hR₁_pos
  have hsum_ser := (hP.add hg_ser).congr fun z hz =>
    hεfg ⟨eball_subset_eball (min_le_right _ _) hz.1, by simpa using hz.2⟩
  have hcoeff : (fun n : ℤ =>
      (if n ≤ 0 then (principalPart φ).coeff (-n).toNat else 0) +
        (if 0 ≤ n then p.coeff n.toNat else 0)) =
      fun n : ℤ => if n < 0 then (principalPart φ).coeff (-n).toNat else p.coeff n.toNat := by
    funext n
    rcases lt_trichotomy n 0 with hn | rfl | hn
    · split_ifs <;> first | omega | simp
    · simp [coeff_zero_principalPart]
    · split_ifs <;> first | omega | simp
  rw [hcoeff] at hsum_ser
  refine ⟨p, R₁, ?_, hsum_ser⟩
  rw [FormalMultilinearSeries.coeff, hp.coeff_zero 1, hg_eval]

/-- For every sufficiently small circle radius `ρ > 0` (chosen uniformly across all degrees `k`),
the negative circle Laurent coefficients `circleLaurentCoeff f c ρ (-(k + 1))` of any representative
`f` of `φ : meromorphicGerms ℂ c` equal `(principalPart φ).coeff (k + 1)`. -/
theorem eventually_circleLaurentCoeff_neg_add_one_eq_coeff_principalPart
    {c : ℂ} {φ : meromorphicGerms ℂ c} {f : ℂ → ℂ} (hφ : (φ : Germ (𝓝[≠] c) ℂ) = f) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ k : ℕ,
      circleLaurentCoeff f c ρ (-((k : ℤ) + 1)) = (principalPart φ).coeff (k + 1) := by
  obtain ⟨p, R₁, _, hser⟩ := exists_hasLaurentSeriesOnAnnulus_of_coe_eq hφ
  obtain ⟨q, h0q, hqR₁⟩ := exists_between hser.r_lt
  lift q to ℝ≥0 using hqR₁.ne_top
  have hq_pos : 0 < (q : ℝ) := (ENNReal.ofReal_lt_coe_iff le_rfl).mp h0q
  filter_upwards [Ioo_mem_nhdsGT hq_pos] with ρ ⟨hρ0, hρq⟩ k
  have hρR₁ : ENNReal.ofReal ρ < R₁ :=
    (ENNReal.ofReal_lt_coe_iff hρ0.le).mpr hρq |>.trans hqR₁
  have heq := hser.circleLaurentCoeff_eq hρ0 hρR₁ (-((k : ℤ) + 1))
  split_ifs at heq with hlt
  · have hnat : (-(-((k : ℤ) + 1))).toNat = k + 1 := by omega
    rwa [hnat] at heq
  · omega

/-- For every sufficiently small circle radius `ρ > 0`, the `0`-th circle Laurent coefficient of any
representative `f` of `φ : meromorphicGerms ℂ c` equals the stalk evaluation at `c` of
`holomorphicStructureSheaf.regularPart c φ`. -/
theorem eventually_circleLaurentCoeff_zero_eq_eval_regularPart
    {c : ℂ} {φ : meromorphicGerms ℂ c} {f : ℂ → ℂ} (hφ : (φ : Germ (𝓝[≠] c) ℂ) = f) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), circleLaurentCoeff f c ρ 0 =
      holomorphicStructureSheaf.eval 𝓘(ℂ) ℂ c (holomorphicStructureSheaf.regularPart c φ) := by
  obtain ⟨p, R₁, hp0, hser⟩ := exists_hasLaurentSeriesOnAnnulus_of_coe_eq hφ
  obtain ⟨q, h0q, hqR₁⟩ := exists_between hser.r_lt
  lift q to ℝ≥0 using hqR₁.ne_top
  have hq_pos : 0 < (q : ℝ) := (ENNReal.ofReal_lt_coe_iff le_rfl).mp h0q
  filter_upwards [Ioo_mem_nhdsGT hq_pos] with ρ ⟨hρ0, hρq⟩
  have hρR₁ : ENNReal.ofReal ρ < R₁ :=
    (ENNReal.ofReal_lt_coe_iff hρ0.le).mpr hρq |>.trans hqR₁
  have heq := hser.circleLaurentCoeff_eq hρ0 hρR₁ 0
  rw [ite_eq_right (lt_irrefl (0 : ℤ)), Int.toNat_zero] at heq
  exact heq.trans hp0

private theorem circleLaurentCoeff_eq_of_differentiableOn_punctured_eball
    {c : ℂ} {φ : meromorphicGerms ℂ c} {f : ℂ → ℂ} {ρ : ℝ} {R : ℝ≥0∞}
    (hf : DifferentiableOn ℂ f (eball c R \ {c})) (hφ : (φ : Germ (𝓝[≠] c) ℂ) = f)
    (hρ : 0 < ρ) (hρR : ENNReal.ofReal ρ < R) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ,
      p.coeff 0 = holomorphicStructureSheaf.eval 𝓘(ℂ) ℂ c
        (holomorphicStructureSheaf.regularPart c φ) ∧
      circleLaurentCoeff f c ρ =
        fun n : ℤ => if n < 0 then (principalPart φ).coeff (-n).toNat else p.coeff n.toNat := by
  obtain ⟨p, R₁, hp0, hlocal⟩ := exists_hasLaurentSeriesOnAnnulus_of_coe_eq hφ
  have hf' : DifferentiableOn ℂ f (eball c R \ closedBall c 0) := by
    simpa only [closedBall_zero] using hf
  have hdisk : HasLaurentSeriesOnAnnulus f (circleLaurentCoeff f c ρ) c 0 R :=
    hf'.hasLaurentSeriesOnAnnulus le_rfl hρ hρR
  have hmin_pos : ENNReal.ofReal 0 < min R R₁ := by
    simpa only [ENNReal.ofReal_zero] using lt_min hdisk.r_pos hlocal.r_pos
  refine ⟨p, hp0, ?_⟩
  exact (hdisk.mono le_rfl (min_le_left _ _) hmin_pos).coeff_unique
    (hlocal.mono le_rfl (min_le_right _ _) hmin_pos)

/-- If `f` is complex-differentiable on the punctured disk `Metric.eball c R \ {c}` and represents
`φ : meromorphicGerms ℂ c` at `c`, then on every interior circle of radius `ρ ∈ (0, R)` the negative
circle Laurent coefficients equal the coefficients of `principalPart φ`. -/
theorem circleLaurentCoeff_neg_add_one_eq_coeff_principalPart
    {c : ℂ} {φ : meromorphicGerms ℂ c} {f : ℂ → ℂ} {ρ : ℝ} {R : ℝ≥0∞}
    (hf : DifferentiableOn ℂ f (eball c R \ {c})) (hφ : (φ : Germ (𝓝[≠] c) ℂ) = f)
    (hρ : 0 < ρ) (hρR : ENNReal.ofReal ρ < R) (k : ℕ) :
    circleLaurentCoeff f c ρ (-((k : ℤ) + 1)) = (principalPart φ).coeff (k + 1) := by
  obtain ⟨p, _, heq⟩ := circleLaurentCoeff_eq_of_differentiableOn_punctured_eball hf hφ hρ hρR
  have hk := congrFun heq (-((k : ℤ) + 1))
  split_ifs at hk with hlt
  · have hnat : (-(-((k : ℤ) + 1))).toNat = k + 1 := by omega
    rwa [hnat] at hk
  · omega

/-- If `f` is complex-differentiable on `Metric.eball c R \ {c}` and represents
`φ : meromorphicGerms ℂ c` at `c`, then on every interior circle of radius `ρ ∈ (0, R)` the `0`-th
circle Laurent coefficient equals the stalk evaluation at `c` of `regularPart c φ`. -/
theorem circleLaurentCoeff_zero_eq_eval_regularPart
    {c : ℂ} {φ : meromorphicGerms ℂ c} {f : ℂ → ℂ} {ρ : ℝ} {R : ℝ≥0∞}
    (hf : DifferentiableOn ℂ f (eball c R \ {c})) (hφ : (φ : Germ (𝓝[≠] c) ℂ) = f)
    (hρ : 0 < ρ) (hρR : ENNReal.ofReal ρ < R) :
    circleLaurentCoeff f c ρ 0 =
      holomorphicStructureSheaf.eval 𝓘(ℂ) ℂ c (holomorphicStructureSheaf.regularPart c φ) := by
  obtain ⟨p, hp0, heq⟩ := circleLaurentCoeff_eq_of_differentiableOn_punctured_eball hf hφ hρ hρR
  have h0 := congrFun heq 0
  rw [ite_eq_right (lt_irrefl (0 : ℤ)), Int.toNat_zero] at h0
  exact h0.trans hp0

/-- **Analytic negative Laurent part equals algebraic principal part.** If `f` is
complex-differentiable on `Metric.eball c R \ {c}` and represents `φ : meromorphicGerms ℂ c`, then
for every interior radius `ρ ∈ (0, R)`, `laurentNegPart (circleLaurentCoeff f c ρ) c w` agrees with
`(principalPart φ).eval (w - c)⁻¹` for every `w : ℂ`. -/
theorem laurentNegPart_circleLaurentCoeff_eq_eval_principalPart
    {c : ℂ} {φ : meromorphicGerms ℂ c} {f : ℂ → ℂ} {ρ : ℝ} {R : ℝ≥0∞}
    (hf : DifferentiableOn ℂ f (eball c R \ {c})) (hφ : (φ : Germ (𝓝[≠] c) ℂ) = f)
    (hρ : 0 < ρ) (hρR : ENNReal.ofReal ρ < R) (w : ℂ) :
    laurentNegPart (circleLaurentCoeff f c ρ) c w = (principalPart φ).eval (w - c)⁻¹ :=
  laurentNegPart_eq_eval_inv_sub_of_coeff_eq (coeff_zero_principalPart φ)
    (circleLaurentCoeff_neg_add_one_eq_coeff_principalPart hf hφ hρ hρR) c w

/-- **Analytic nonnegative Laurent part equals regular remainder.** If `f` is complex-differentiable
on `Metric.eball c R \ {c}` and represents `φ : meromorphicGerms ℂ c`, then on
`Metric.eball c R \ {c}` the nonnegative Laurent sum `laurentPosPart (circleLaurentCoeff f c ρ) c`
equals `f w - (principalPart φ).eval (w - c)⁻¹` (and takes value `eval c (regularPart c φ)` at `c`
by `laurentPosPart_at_center` and `circleLaurentCoeff_zero_eq_eval_regularPart`). -/
theorem laurentPosPart_circleLaurentCoeff_eq_sub_principalPart
    {c w : ℂ} {φ : meromorphicGerms ℂ c} {f : ℂ → ℂ} {ρ : ℝ} {R : ℝ≥0∞}
    (hf : DifferentiableOn ℂ f (eball c R \ {c})) (hφ : (φ : Germ (𝓝[≠] c) ℂ) = f)
    (hρ : 0 < ρ) (hρR : ENNReal.ofReal ρ < R) (hw : w ∈ eball c R \ {c}) :
    laurentPosPart (circleLaurentCoeff f c ρ) c w = f w - (principalPart φ).eval (w - c)⁻¹ := by
  have hf' : DifferentiableOn ℂ f (eball c R \ closedBall c 0) := by
    simpa only [closedBall_zero] using hf
  have hdisk : HasLaurentSeriesOnAnnulus f (circleLaurentCoeff f c ρ) c 0 R :=
    hf'.hasLaurentSeriesOnAnnulus le_rfl hρ hρR
  have hw' : w ∈ eball c R \ closedBall c 0 := by simpa only [closedBall_zero] using hw
  have hsplit := hdisk.eq_laurentPosPart_add_laurentNegPart hw'
  rw [laurentNegPart_circleLaurentCoeff_eq_eval_principalPart hf hφ hρ hρR w] at hsplit
  exact eq_sub_of_add_eq hsplit.symm

end meromorphicGerms

/-- For every sufficiently small circle radius `ρ > 0`, the `(-1)`-st circle Laurent coefficient of
a function meromorphic at `c` equals `Contour.residue f c`. -/
theorem eventually_circleLaurentCoeff_neg_one_eq_residue {f : ℂ → ℂ} {c : ℂ}
    (hf : MeromorphicAt f c) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), circleLaurentCoeff f c ρ (-1) = Contour.residue f c := by
  let φ : meromorphicGerms ℂ c := ⟨(f : Germ (𝓝[≠] c) ℂ), coe_mem_meromorphicGerms.2 hf⟩
  have hφ : (φ : Germ (𝓝[≠] c) ℂ) = f := (rfl)
  filter_upwards [meromorphicGerms.eventually_circleLaurentCoeff_neg_add_one_eq_coeff_principalPart
    hφ] with ρ hρ
  have h0 := hρ 0
  rw [Nat.cast_zero, zero_add, meromorphicGerms.coeff_principalPart_one_eq_residue hφ] at h0
  exact h0

/-- If `f` is complex-differentiable on `Metric.eball c R \ {c}` and meromorphic at `c`, then on
every interior circle of radius `ρ ∈ (0, R)` the `(-1)`-st circle Laurent coefficient equals
`Contour.residue f c`. -/
theorem circleLaurentCoeff_neg_one_eq_residue {f : ℂ → ℂ} {c : ℂ} {ρ : ℝ} {R : ℝ≥0∞}
    (hf : DifferentiableOn ℂ f (eball c R \ {c})) (hm : MeromorphicAt f c)
    (hρ : 0 < ρ) (hρR : ENNReal.ofReal ρ < R) :
    circleLaurentCoeff f c ρ (-1) = Contour.residue f c := by
  let φ : meromorphicGerms ℂ c := ⟨(f : Germ (𝓝[≠] c) ℂ), coe_mem_meromorphicGerms.2 hm⟩
  have hφ : (φ : Germ (𝓝[≠] c) ℂ) = f := (rfl)
  have h0 := meromorphicGerms.circleLaurentCoeff_neg_add_one_eq_coeff_principalPart hf hφ hρ hρR 0
  rw [Nat.cast_zero, zero_add, meromorphicGerms.coeff_principalPart_one_eq_residue hφ] at h0
  exact h0

namespace holomorphicStructureSheaf

/-- For every sufficiently small circle radius `ρ > 0`, the `0`-th circle Laurent coefficient of any
representative `f` of a regular meromorphic germ `φ : (toMeromorphicGerms c).range` equals
`regularEval c φ`. -/
theorem eventually_circleLaurentCoeff_zero_eq_regularEval {c : ℂ}
    (φ : (toMeromorphicGerms c).range) {f : ℂ → ℂ}
    (hφ : ((φ : meromorphicGerms ℂ c) : Germ (𝓝[≠] c) ℂ) = f) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), circleLaurentCoeff f c ρ 0 = regularEval c φ := by
  rw [regularEval_eq_eval_regularPart]
  exact meromorphicGerms.eventually_circleLaurentCoeff_zero_eq_eval_regularPart hφ

/-- If `f` is complex-differentiable on `Metric.eball c R \ {c}` and represents a regular
meromorphic germ `φ : (toMeromorphicGerms c).range` at `c`, then on every interior circle of radius
`ρ ∈ (0, R)` the `0`-th circle Laurent coefficient equals `regularEval c φ`. -/
theorem circleLaurentCoeff_zero_eq_regularEval {c : ℂ}
    (φ : (toMeromorphicGerms c).range) {f : ℂ → ℂ} {ρ : ℝ} {R : ℝ≥0∞}
    (hf : DifferentiableOn ℂ f (eball c R \ {c}))
    (hφ : ((φ : meromorphicGerms ℂ c) : Germ (𝓝[≠] c) ℂ) = f)
    (hρ : 0 < ρ) (hρR : ENNReal.ofReal ρ < R) :
    circleLaurentCoeff f c ρ 0 = regularEval c φ := by
  rw [regularEval_eq_eval_regularPart]
  exact meromorphicGerms.circleLaurentCoeff_zero_eq_eval_regularPart hf hφ hρ hρR

end holomorphicStructureSheaf

end TauCeti
