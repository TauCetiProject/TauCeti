/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.Amice.Isometry
public import TauCeti.NumberTheory.Padics.Distribution.Amice.Norm
public import TauCeti.NumberTheory.Padics.Distribution.Amice.Transition
public import TauCeti.NumberTheory.Padics.Distribution.Dual
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.LinearCombination

/-!
# The Amice transform of locally analytic distributions

The Mahler term `x ↦ (x choose n) • e` is locally analytic on `ℤ_p`. As an element of the
algebraic direct limit `LA(ℤ_p, E)` of the analytic stages it is
`TauCeti.LocallyAnalytic.mahlerTerm p S e n`, the class of Amice's vector `e_{n,n} • e`: at level
`n` the factor `⌊n / pⁿ⌋!` of Amice's polynomial `e_{n,n}(x) = ⌊n / pⁿ⌋! (x choose n)` is `1`.
It evaluates to Mathlib's `PadicInt.mahlerTerm e n`. At every level `h`, Amice's vector
`e_{h,n} • e` is the class of the Mahler term `(x choose n) • ⌊n / pʰ⌋! e`
(`TauCeti.LocallyAnalytic.ofStage_amiceTerm`). This identity uses only the integral diagonal
transitions between the levels, so it holds for every coefficient module, including torsion ones.

Let `K` be a complete nontrivially normed field with contractive `ℤ_p`-action. The *Amice
transform* of a locally analytic distribution `μ` on `ℤ_p` with values in `K` is the power series
`∑ₙ μ(x ↦ (x choose n)) Tⁿ` of its moments,
`TauCeti.LocallyAnalyticDistribution.amiceTransform`. On a measure it is Mathlib's
`AbstractMeasure.amiceTransform` (`amiceTransform_ofMeasure`).

Since Amice's vectors form an orthonormal basis of the stage `LA_h(K)`, the restriction of `μ` to
`LA_h(K)` is the linear combination map of its values `⌊n / pʰ⌋! bₙ` on that basis, where `bₙ` is
the `n`-th moment. Hence its operator norm is

`‖μ‖_h = supₙ ‖bₙ‖ ‖⌊n / pʰ⌋!‖`

(`stageSeminorm_eq_iSup`). When `K` is a normed `ℚ_p`-algebra, this is the dual stage norm
`TauCeti.amiceDualNorm p h` of the Amice transform (`stageSeminorm_eq_amiceDualNorm`). Comparing
with the Gauss norms `S_h` at the radii `r_h = p ^ (-1 / ((p - 1) pʰ))` gives
`S_h(Aμ) ≤ ‖μ‖_h ≤ p S_{h+1}(Aμ)`.

Only the norms of natural numbers in `K` enter here, so no compatibility between the given
`ℤ_p`-action and the `ℚ_p`-algebra structure is needed.

Every moment family is thus bounded against the factorial weights at every level, so the Amice
transform of a distribution converges on the open unit disc. Conversely, a power series on the
open unit disc has coefficients defining a compatible family of bounded functionals on the
stages, hence a distribution. This proves **Amice's theorem** for distributions: the Amice
transform is injective (`amiceTransform_injective`) and its range consists exactly of the power
series converging on the open unit disc (`mem_range_amiceTransform_iff`). Its inverse is
`ofOnOpenDisc` (`amiceTransform_ofOnOpenDisc`, `ofOnOpenDisc_amiceTransform`).

## Main definitions

* `TauCeti.LocallyAnalytic.mahlerTerm p S e n`: the locally analytic Mahler term
  `x ↦ (x choose n) • e`.
* `TauCeti.LocallyAnalyticDistribution.amiceTransform`: the power series of the moments
  `μ(x ↦ (x choose n))`.
* `TauCeti.LocallyAnalyticDistribution.ofOnOpenDisc`: the distribution whose moments are the
  coefficients of a power series on the open unit disc, inverse to the Amice transform.

## Main results

* `TauCeti.LocallyAnalytic.ofStage_amiceTerm`: Amice's vector `e_{h,n} • e` is the Mahler term
  `(x choose n) • ⌊n / pʰ⌋! e`.
* `TauCeti.LocallyAnalyticDistribution.stageSeminorm_eq_amiceDualNorm`: the stage seminorm of
  level `h` is the dual stage norm `supₙ ‖bₙ‖ ‖⌊n / pʰ⌋!‖` of the Amice transform.
* `TauCeti.LocallyAnalyticDistribution.amiceTransform_injective`: a distribution is determined
  by its moments.
* `TauCeti.LocallyAnalyticDistribution.mem_range_amiceTransform_iff`: the Amice transforms of
  distributions are exactly the power series on the open unit disc.

The bijection is bundled additively as `amiceTransformEquiv` into the native open-disc
series algebra. The logarithm example `ofOnOpenDisc_log_notMem_range_ofMeasure` shows that
distributions strictly extend continuous measures.

## References

* Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4 and §II.2.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §3,
  Theorem 3.43.
-/

public section

open Nat ZeroAtInftyContinuousMap
open scoped ENNReal ZeroAtInfty

namespace TauCeti

variable {p : ℕ} [hp : Fact p.Prime]

namespace LocallyAnalytic

open AnalyticStage

variable {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

/-- Raising the level from `h` to `k` multiplies the coefficient of Amice's vector `e_{h,n} • e`
by an integer `r` with `⌊n / pᵏ⌋! r = ⌊n / pʰ⌋!`. -/
private theorem exists_ofStage_amiceTerm_eq {h k : ℕ} (hhk : h ≤ k) (n : ℕ) (e : E) :
    ∃ r : ℤ_[p], ((n / p ^ k)! : ℤ_[p]) * r = (n / p ^ h)! ∧
      ofStage S h (amiceTerm p h n e) = ofStage S k (amiceTerm p k n (r • e)) := by
  induction k, hhk using Nat.le_induction with
  | base => exact ⟨1, mul_one _, by rw [one_smul]⟩
  | succ k _ ih =>
    obtain ⟨r, hr, he⟩ := ih
    refine ⟨amiceTransitionCoeff p k n * r, ?_, ?_⟩
    · rw [← mul_assoc, factorial_mul_amiceTransitionCoeff, hr]
    · rw [he, ← ofStage_transition S (amiceTerm p k n (r • e)), transition_amiceTerm, smul_smul]

variable (p) in
/-- The locally analytic Mahler term `x ↦ (x choose n) • e`: the class of Amice's vector
`e_{n,n} • e` of level `n`, whose factor `⌊n / pⁿ⌋!` is `1`. At another level `h`,
`ofStage_amiceTerm` identifies Amice's vector `e_{h,n} • e` with the factorial-weighted term
`mahlerTerm p S ((n / p ^ h)! • e) n`. -/
noncomputable def mahlerTerm (e : E) (n : ℕ) : LocallyAnalytic p S E :=
  ofStage S n (amiceTerm p n n e)

/-- The Mahler term is the class of Amice's vector of level `n`. -/
theorem mahlerTerm_def (e : E) (n : ℕ) : mahlerTerm p S e n = ofStage S n (amiceTerm p n n e) :=
  (rfl)

/-- The locally analytic Mahler term evaluates to Mathlib's Mahler term `x ↦ (x choose n) • e`. -/
@[simp]
theorem eval_mahlerTerm (e : E) (n : ℕ) :
    eval S (mahlerTerm p S e n) = PadicInt.mahlerTerm e n := by
  rw [mahlerTerm_def, eval_ofStage, eval_amiceTerm,
    Nat.div_eq_of_lt (Nat.lt_pow_self hp.out.one_lt), factorial_zero, one_smul]

/-- The Mahler term is additive in its coefficient. -/
theorem mahlerTerm_add (e f : E) (n : ℕ) :
    mahlerTerm p S (e + f) n = mahlerTerm p S e n + mahlerTerm p S f n := by
  rw [mahlerTerm_def, amiceTerm_add, map_add, ← mahlerTerm_def, ← mahlerTerm_def]

/-- The Mahler term commutes with scalars acting on `E` compatibly with `ℤ_p`. -/
theorem mahlerTerm_smul (s : S) (e : E) (n : ℕ) :
    mahlerTerm p S (s • e) n = s • mahlerTerm p S e n := by
  rw [mahlerTerm_def, amiceTerm_smul, map_smul, ← mahlerTerm_def]

/-- **Amice's vectors are Mahler terms.** At every level `h`, Amice's vector `e_{h,n} • e` is the
class of the Mahler term `x ↦ (x choose n) • ⌊n / pʰ⌋! e`. No torsion-freeness of `E` is needed.
-/
@[simp]
theorem ofStage_amiceTerm (h n : ℕ) (e : E) :
    ofStage S h (amiceTerm p h n e) = mahlerTerm p S ((n / p ^ h)! • e) n := by
  have hk : n / p ^ max h n = 0 :=
    Nat.div_eq_of_lt ((Nat.lt_pow_self hp.out.one_lt).trans_le
      (Nat.pow_le_pow_right hp.out.pos (le_max_right h n)))
  obtain ⟨r, hr, he⟩ := exists_ofStage_amiceTerm_eq (p := p) S (le_max_left h n) n e
  obtain ⟨r', hr', he'⟩ :=
    exists_ofStage_amiceTerm_eq (p := p) S (le_max_right h n) n ((n / p ^ h)! • e)
  rw [hk, factorial_zero, Nat.cast_one, one_mul] at hr hr'
  rw [Nat.div_eq_of_lt (Nat.lt_pow_self hp.out.one_lt), factorial_zero, Nat.cast_one] at hr'
  rw [he, mahlerTerm_def, he', hr, hr', one_smul, Nat.cast_smul_eq_nsmul]

end LocallyAnalytic

namespace LocallyAnalyticDistribution

open AnalyticStage LocallyAnalytic

variable {K : Type*} [NontriviallyNormedField K] [Algebra ℤ_[p] K]
  [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K] [CompleteSpace K]

/-- The **Amice transform** of a locally analytic distribution `μ` on `ℤ_p`: the power series
`∑ₙ μ(x ↦ (x choose n)) Tⁿ` of its moments. -/
noncomputable def amiceTransform : LocallyAnalyticDistribution p K →ₗ[K] PowerSeries K where
  toFun μ :=
    PowerSeries.mk fun n ↦ (μ : Module.Dual K (LocallyAnalytic p K K)) (mahlerTerm p K 1 n)
  map_add' μ ν := by ext; simp
  map_smul' a μ := by ext; simp

/-- The `n`-th coefficient of the Amice transform is the moment `μ(x ↦ (x choose n))`. -/
@[simp]
theorem coeff_amiceTransform (μ : LocallyAnalyticDistribution p K) (n : ℕ) :
    (amiceTransform μ).coeff n =
      (μ : Module.Dual K (LocallyAnalytic p K K)) (mahlerTerm p K 1 n) := by
  simp [amiceTransform]

/-- The value of a distribution on Amice's vector `e_{h,n} • e` is `⌊n / pʰ⌋! e bₙ`, where `bₙ`
is the `n`-th moment. -/
theorem stage_amiceTerm (μ : LocallyAnalyticDistribution p K) (h n : ℕ) (e : K) :
    stage h μ (amiceTerm p h n e) = ((n / p ^ h)! : K) * e * (amiceTransform μ).coeff n := by
  have he : (n / p ^ h)! • e = (((n / p ^ h)! : K) * e) • (1 : K) := by
    rw [smul_eq_mul, mul_one, nsmul_eq_mul]
  rw [stage_apply, ofStage_amiceTerm, he, mahlerTerm_smul, map_smul, coeff_amiceTransform,
    smul_eq_mul]

/-- A distribution evaluates an analytic-stage vector by pairing its Amice coordinates with
the factorial-weighted moments. The sum is unconditional. -/
theorem hasSum_amiceEquiv_symm_mul_coeff_amiceTransform
    (μ : LocallyAnalyticDistribution p K) {h : ℕ} (c : AnalyticStage p h K) :
    HasSum (fun n ↦ (amiceEquiv p h K).symm c n *
      (((n / p ^ h).factorial : K) * (amiceTransform μ).coeff n)) (stage h μ c) := by
  convert ((hasSum_amiceMap K ((amiceEquiv p h K).symm c)).mapL (stage h μ)) using 1
  · ext n
    rw [← smul_eq_mul, ← map_smul, ← amiceTerm_smul, stage_amiceTerm]
    simp
  · simp only [← amiceEquiv_apply, LinearIsometryEquiv.apply_symm_apply]

/-- The weighted moments at every level are bounded by the stage operator norm. -/
theorem norm_factorial_mul_coeff_amiceTransform_le (μ : LocallyAnalyticDistribution p K)
    (h n : ℕ) :
    ‖((n / p ^ h).factorial : K) * (amiceTransform μ).coeff n‖ ≤ ‖stage h μ‖ := by
  have hterm := stage_amiceTerm μ h n 1
  rw [mul_one] at hterm
  rw [← hterm]
  exact ((stage h μ).le_opNorm _).trans <| by
    simpa using mul_le_mul_of_nonneg_left
      (norm_amiceTerm_le n (1 : K)) (norm_nonneg (stage h μ))

/-- The restriction of a distribution to the stage `LA_h(K)`, read in Amice's coordinates
`C₀(ℕ, K)`, sends the coordinate vector `single n e` to `⌊n / pʰ⌋! e bₙ`. -/
private theorem stage_comp_amiceEquiv_single (μ : LocallyAnalyticDistribution p K) (h n : ℕ)
    (e : K) :
    (stage h μ ∘L (amiceEquiv p h K (E := K) : C₀(ℕ, K) →L[K] AnalyticStage p h K)) (single n e) =
      ((n / p ^ h)! : K) * e * (amiceTransform μ).coeff n := by
  rw [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_coe'', amiceEquiv_apply,
    amiceMap_single, stage_amiceTerm]

/-- The values `⌊n / pʰ⌋! bₙ` of a distribution on Amice's basis of `LA_h(K)` are bounded. -/
theorem bddAbove_norm_coeff_amiceTransform_mul_norm_factorial
    (μ : LocallyAnalyticDistribution p K) (h : ℕ) :
    BddAbove (Set.range fun n ↦ ‖(amiceTransform μ).coeff n‖ * ‖((n / p ^ h)! : K)‖) := by
  have hmem := memℓp_infty_iff.mp
    (memℓp_infty_apply_single (stage h μ ∘L (amiceEquiv p h K (E := K) : C₀(ℕ, K) →L[K] _)))
  simpa only [stage_comp_amiceEquiv_single, mul_one, norm_mul, mul_comm] using hmem

/-- **The stage seminorms in Amice's coordinates.** The norm of a distribution on the stage
`LA_h(K)` is `supₙ ‖bₙ‖ ‖⌊n / pʰ⌋!‖`, where `bₙ` is the `n`-th moment, the factorials being taken
in `K`. -/
theorem stageSeminorm_eq_iSup (μ : LocallyAnalyticDistribution p K) (h : ℕ) :
    stageSeminorm h μ = ⨆ n, ‖(amiceTransform μ).coeff n‖ * ‖((n / p ^ h)! : K)‖ := by
  have hnorm := opNorm_linearCombination (K := K) ⟨_, memℓp_infty_apply_single
    (stage h μ ∘L (amiceEquiv p h K (E := K) : C₀(ℕ, K) →L[K] AnalyticStage p h K))⟩
  rw [linearCombination_self, ContinuousLinearMap.opNorm_comp_linearIsometryEquiv,
    lp.norm_eq_ciSup] at hnorm
  rw [stageSeminorm_apply, hnorm]
  simp only [stage_comp_amiceEquiv_single, mul_one, norm_mul, mul_comm]

/-- **A distribution is determined by its moments.** -/
theorem amiceTransform_injective :
    Function.Injective (amiceTransform (p := p) (K := K)) := by
  intro μ ν hμν
  apply ext
  intro h
  apply continuousLinearMap_ext_amiceTerm
  intro n
  simp only [stage_amiceTerm, hμν]

/-- On a measure, the Amice transform of distributions is Mathlib's Amice transform of measures:
the locally analytic Mahler terms evaluate to Mathlib's Mahler terms. -/
@[simp]
theorem amiceTransform_ofMeasure (μ : AbstractMeasure ℤ_[p] K K) :
    amiceTransform (ofMeasure μ) = AbstractMeasure.amiceTransform μ := by
  ext n
  rw [coeff_amiceTransform, coe_ofMeasure_apply, eval_mahlerTerm,
    AbstractMeasure.coeff_amiceTransform, PadicInt.mahlerTerm, ContinuousMap.const_one]

section NormedAlgebra

variable [NormedAlgebra ℚ_[p] K]

/-- **The stage seminorm is the dual stage norm of the Amice transform.** For a normed
`ℚ_p`-algebra `K`, the norm of a distribution on the stage `LA_h(K)` is
`D_h(Aμ) = supₙ ‖bₙ‖ ‖⌊n / pʰ⌋!‖`, the factorials being taken in `ℚ_p`. -/
theorem stageSeminorm_eq_amiceDualNorm (μ : LocallyAnalyticDistribution p K) (h : ℕ) :
    stageSeminorm h μ = amiceDualNorm p h (amiceTransform μ) := by
  simp only [stageSeminorm_eq_iSup, amiceDualNorm_def, norm_natCast_eq_norm_padic (p := p)]

/-- The Gauss norm of the Amice transform at the radius `r_h` is at most the stage seminorm of
level `h`. -/
theorem gaussNorm_amiceRadius_le_stageSeminorm (μ : LocallyAnalyticDistribution p K) (h : ℕ) :
    (amiceTransform μ).gaussNorm norm (amiceRadius p h) ≤ stageSeminorm h μ := by
  rw [stageSeminorm_eq_amiceDualNorm]
  refine gaussNorm_amiceRadius_le_amiceDualNorm ?_
  simpa only [norm_natCast_eq_norm_padic (p := p)] using
    bddAbove_norm_coeff_amiceTransform_mul_norm_factorial μ h

/-- The stage seminorm of level `h` is at most `p` times the Gauss norm of the Amice transform at
the radius `r_{h+1}`. -/
theorem stageSeminorm_le_mul_gaussNorm_amiceRadius_succ (μ : LocallyAnalyticDistribution p K)
    (h : ℕ) :
    stageSeminorm h μ ≤ p * (amiceTransform μ).gaussNorm norm (amiceRadius p (h + 1)) := by
  rw [stageSeminorm_eq_amiceDualNorm]
  refine amiceDualNorm_le_mul_gaussNorm_amiceRadius_succ ?_
  refine hasGaussNorm_amiceRadius_of_bddAbove ?_
  simpa only [norm_natCast_eq_norm_padic (p := p)] using
    bddAbove_norm_coeff_amiceTransform_mul_norm_factorial μ (h + 1)

/-- The Amice transform of a distribution converges on the open unit disc. -/
theorem onOpenDisc_amiceTransform (μ : LocallyAnalyticDistribution p K) :
    (amiceTransform μ).OnOpenDisc 1 :=
  (onOpenDisc_iff_forall_bddAbove_norm_coeff_mul_norm_factorial (p := p)).mpr fun h ↦ by
    simpa only [norm_natCast_eq_norm_padic (p := p)] using
      bddAbove_norm_coeff_amiceTransform_mul_norm_factorial μ h

section OfOnOpenDisc

variable (p) {F : PowerSeries K} (hF : F.OnOpenDisc 1)
include hF

/-- The functional on `LA_h(K)` taking the value `⌊n / pʰ⌋! cₙ` on Amice's vector `e_{h,n}`. -/
private noncomputable def stageOfOnOpenDisc (h : ℕ) : AnalyticStage p h K →L[K] K :=
  linearCombination K ⟨_, memℓp_factorial_mul_coeff_of_onOpenDisc p hF h⟩ ∘L
    ((amiceEquiv p h K (E := K)).symm : AnalyticStage p h K →L[K] C₀(ℕ, K))

private theorem stageOfOnOpenDisc_amiceTerm (h n : ℕ) (e : K) :
    stageOfOnOpenDisc p hF h (amiceTerm p h n e) = e * (((n / p ^ h)! : K) * F.coeff n) := by
  rw [stageOfOnOpenDisc, ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_coe'',
    amiceEquiv_symm_amiceTerm, linearCombination_single, smul_eq_mul]

/-- The functionals `stageOfOnOpenDisc` are compatible with re-expansion: the diagonal transition
multiplies the `n`-th Amice coordinate by `⌊n / pʰ⌋! / ⌊n / p^(h+1)⌋!`. -/
private theorem stageOfOnOpenDisc_comp_transition (h : ℕ) :
    stageOfOnOpenDisc p hF (h + 1) ∘L transition K = stageOfOnOpenDisc p hF h := by
  apply continuousLinearMap_ext_amiceTerm
  intro n
  simp only [ContinuousLinearMap.comp_apply, transition_amiceTerm,
    stageOfOnOpenDisc_amiceTerm, one_mul, Algebra.smul_def, mul_one]
  rw [← mul_assoc, ← map_natCast (algebraMap ℤ_[p] K) (n / p ^ (h + 1))!, ← map_mul,
    mul_comm (amiceTransitionCoeff p h n), factorial_mul_amiceTransitionCoeff, map_natCast]

/-- The distribution whose moments are the coefficients of a power series on the open unit disc:
the inverse of the Amice transform (`amiceTransform_ofOnOpenDisc`, `ofOnOpenDisc_amiceTransform`).
-/
noncomputable def ofOnOpenDisc : LocallyAnalyticDistribution p K :=
  stagesEquiv.symm ⟨fun h ↦ stageOfOnOpenDisc p hF h,
    mem_compatibleStageFunctionals_iff.mpr (stageOfOnOpenDisc_comp_transition p hF)⟩

/-- The moments of `ofOnOpenDisc p hF` are the coefficients of `F`. -/
@[simp]
theorem amiceTransform_ofOnOpenDisc : amiceTransform (ofOnOpenDisc p hF) = F := by
  ext n
  rw [coeff_amiceTransform, mahlerTerm_def, ← stage_apply, ofOnOpenDisc, stage_stagesEquiv_symm,
    stageOfOnOpenDisc_amiceTerm, Nat.div_eq_of_lt (Nat.lt_pow_self hp.out.one_lt),
    factorial_zero, Nat.cast_one, one_mul, one_mul]

end OfOnOpenDisc

/-- A distribution is recovered from its Amice transform by `ofOnOpenDisc`. -/
@[simp]
theorem ofOnOpenDisc_amiceTransform (μ : LocallyAnalyticDistribution p K) :
    ofOnOpenDisc p (onOpenDisc_amiceTransform μ) = μ :=
  amiceTransform_injective (amiceTransform_ofOnOpenDisc p _)

/-- **Amice's theorem for distributions.** When the complete field `K` is a normed
`ℚ_p`-algebra, a power series over `K` is the Amice transform of a locally analytic distribution
exactly when it converges on the open unit disc. Together with `amiceTransform_injective`, the
Amice transform identifies distributions with the power series on the open unit disc. -/
theorem mem_range_amiceTransform_iff {F : PowerSeries K} :
    F ∈ LinearMap.range (amiceTransform (p := p) (K := K)) ↔ F.OnOpenDisc 1 := by
  refine ⟨?_, fun hF ↦ ⟨ofOnOpenDisc p hF, amiceTransform_ofOnOpenDisc p hF⟩⟩
  rintro ⟨μ, rfl⟩
  exact onOpenDisc_amiceTransform μ

/-- The Amice bijection between locally analytic distributions and the native open-unit-disc
series algebra, bundled additively. The forward transform is also `K`-linear. -/
noncomputable def amiceTransformEquiv :
    LocallyAnalyticDistribution p K ≃+ _root_.PowerSeries.OnOpenDisc.subring K 1 where
  toFun μ := ⟨amiceTransform μ, _root_.PowerSeries.OnOpenDisc.mem_subring.mpr
    (onOpenDisc_amiceTransform μ)⟩
  invFun F := ofOnOpenDisc p (_root_.PowerSeries.OnOpenDisc.mem_subring.mp F.2)
  left_inv := ofOnOpenDisc_amiceTransform
  right_inv F := Subtype.ext (amiceTransform_ofOnOpenDisc p
    (_root_.PowerSeries.OnOpenDisc.mem_subring.mp F.2))
  map_add' μ ν := Subtype.ext (map_add amiceTransform μ ν)

/-- The bijection has the usual Amice transform as its underlying formal series. -/
@[simp]
theorem coe_amiceTransformEquiv (μ : LocallyAnalyticDistribution p K) :
    (amiceTransformEquiv μ : PowerSeries K) = amiceTransform μ := (rfl)

/-- The inverse bijection constructs the distribution from the given open-disc series. -/
@[simp]
theorem amiceTransformEquiv_symm_apply (F : _root_.PowerSeries.OnOpenDisc.subring K 1) :
    amiceTransformEquiv.symm F = ofOnOpenDisc p
      (_root_.PowerSeries.OnOpenDisc.mem_subring.mp F.2) := (rfl)

/-- The logarithm is the transform of a distribution which is not induced by a continuous
measure. Thus passing from measures to distributions strictly enlarges the transform range. -/
theorem ofOnOpenDisc_log_notMem_range_ofMeasure :
    ofOnOpenDisc p (_root_.PowerSeries.onOpenDisc_log (K := ℚ_[p])) ∉
      LinearMap.range (ofMeasure (p := p) (K := ℚ_[p])) := by
  rintro ⟨μ, hμ⟩
  apply log_notMem_range_amiceTransform (p := p)
  refine ⟨μ, ?_⟩
  rw [← amiceTransform_ofMeasure, hμ, amiceTransform_ofOnOpenDisc]

end NormedAlgebra

end LocallyAnalyticDistribution

end TauCeti
