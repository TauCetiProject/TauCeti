/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive
public import TauCeti.Analysis.CStarAlgebra.Ideal
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
import Mathlib.Analysis.LocallyConvex.Separation
import TauCeti.Analysis.CStarAlgebra.State.JordanDecomposition

/-!
# Quasicentral approximate units for closed two-sided ideals in C⋆-algebras

Every closed two-sided ideal `I` of a C⋆-algebra `A` admits a positive contractive approximate unit
that is **quasicentral** in `A`, meaning `‖e_λ * a - a * e_λ‖ → 0` for every `a : A`
(Arveson 1977; Akemann–Pedersen 1977). When `A` is separable, the quasicentral approximate unit can
be chosen as a monotone sequence `(e_n)` in `I` with `0 ≤ e_n` and `‖e_n‖ < 1`.

## Proof strategy

1. **Weak quasicentrality of the canonical approximate unit**
   (`PositiveContinuousLinearMap.tendsto_commutator_approximateUnit_zero`):
   For any positive continuous linear functional `φ : A →P[ℂ] ℂ`, its restriction `φ_I : I →P[ℂ] ℂ`
   satisfies `φ_I e → ‖(φ_I : I →L[ℂ] ℂ)‖` along `CStarAlgebra.approximateUnit I`. For fixed
   `0 ≤ e₀ ≤ 1` in `I` and any `e` in the upper section `e₀ ≤ e`, `‖e‖ ≤ 1`, the difference
   `d = e - e₀` satisfies `0 ≤ d * d ≤ d`, so `‖φ (d * d)‖ ≤ ‖φ_I‖ - (φ_I e₀).re`. Applying the
   Cauchy–Schwarz inequality for positive functionals to `d * (a * e) - (e * a) * d =
   e * a * e₀ - e₀ * a * e` and passing to the limit in `e` along `CStarAlgebra.approximateUnit I`
   (using `(e₀ : A) * a ∈ I` and `a * (e₀ : A) ∈ I`) bounds `‖φ ((e₀ : A) * a - a * (e₀ : A))‖` by
   `2 * √(‖φ_I‖ - (φ_I e₀).re) * √‖φ‖ * ‖a‖ → 0`. By the Grothendieck–Jordan decomposition
   (`ContinuousLinearMap.tendsto_real_zero_of_forall_positiveContinuousLinearMap`), every continuous
   complex- or real-linear functional on `A` also annihilates `(e : A) * a - a * (e : A)` in the
   limit along `CStarAlgebra.approximateUnit I`.
2. **Norm quasicentrality on finite sets via Hahn–Banach**
   (`TwoSidedIdeal.exists_ge_and_norm_lt_one_and_forall_norm_commutator_lt`):
   Each canonical strict upper section `V = {e : I | e₀ ≤ e} ∩ Metric.ball 0 1` is already
   `ℝ`-convex (`CStarAlgebra.convex_Ici_inter_ball`). For any finite set `F : Finset A`, the
   `ℝ`-linear commutator map `Θ : I → (F → A)`, `Θ e b = (e : A) * b - b * (e : A)`, maps `V` onto
   a convex set in `F → A`. If `0 ∉ closure (Θ '' V)`, geometric Hahn–Banach separation produces a
   continuous `ℝ`-linear functional on `F → A` strictly separating `0` from `closure (Θ '' V)`,
   contradicting weak convergence of `Θ` to `0` along `CStarAlgebra.strictApproximateUnit I`.
3. **Filter and sequential quasicentral approximate units**:
   Intersecting `CStarAlgebra.strictApproximateUnit I` with the directed family of commutator
   neighborhoods yields a proper subfilter `l_I ≤ CStarAlgebra.strictApproximateUnit I`
   (`TwoSidedIdeal.exists_isIncreasingApproximateUnit_tendsto_commutator_zero`), whose pushforward
   to `A` gives `TauCeti.CStarAlgebra.exists_quasicentral_approximateUnit`. When `A` is separable,
   diagonalizing against dense sequences in `I` and `A` produces a monotone sequence
   (`TwoSidedIdeal.exists_monotone_seq_quasicentral_approximateUnit`).

## References

* William Arveson, *Notes on extensions of C*-algebras*, Duke Math. J. **44** (1977), 329–355,
  Theorem 1.
* Charles A. Akemann and Gert K. Pedersen, *Ideal perturbations of elements in C*-algebras*,
  Math. Scand. **41** (1977), 117–139, Theorem 2.2.
* Gert K. Pedersen, *C*-Algebras and their Automorphism Groups*, Proposition 3.12.14.
* Bruce Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*, II.4.2.5.
-/

public section

open Filter Set Topology
open scoped CStarAlgebra ComplexOrder

namespace PositiveContinuousLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Weak quasicentrality under positive functionals.** For any closed two-sided ideal `I` of a
C⋆-algebra `A`, any `φ : A →P[ℂ] ℂ`, and any `a : A`, `φ ((e : A) * a - a * (e : A)) → 0` along the
canonical approximate unit `CStarAlgebra.approximateUnit I`. -/
theorem tendsto_commutator_approximateUnit_zero (φ : A →P[ℂ] ℂ) (I : TwoSidedIdeal A)
    [IsClosed (I : Set A)] (a : A) :
    Tendsto (fun e : I => φ ((e : A) * a - a * (e : A))) (CStarAlgebra.approximateUnit I)
      (𝓝 0) := by
  let φI : I →P[ℂ] ℂ := φ.comp (.ofClass I.starAlgHom)
  let M : ℝ := ‖(φI : I →L[ℂ] ℂ)‖
  let l₀ : Filter I := CStarAlgebra.approximateUnit I
  have hl₀ : l₀.IsIncreasingApproximateUnit := CStarAlgebra.increasingApproximateUnit I
  have := hl₀.neBot
  -- First establish the commutator estimate on strict contractions `0 ≤ e₀`, `‖e₀‖ < 1`.
  have hbound_strict (e₀ : I) (he₀_nonneg : 0 ≤ e₀) (he₀_lt : ‖e₀‖ < 1) :
      ‖φ ((e₀ : A) * a - a * (e₀ : A))‖ ≤
        2 * (Real.sqrt (M - (φI e₀).re) * (Real.sqrt ‖(φ : A →L[ℂ] ℂ)‖ * ‖a‖)) := by
    let η : ℝ := M - (φI e₀).re
    have hη_step (e : I) (hee₀ : e₀ ≤ e) (he_norm : ‖e‖ ≤ 1) :
        ‖φ ((e : A) * a * (e₀ : A) - (e₀ : A) * a * (e : A))‖ ≤
          2 * (Real.sqrt η * (Real.sqrt ‖(φ : A →L[ℂ] ℂ)‖ * ‖a‖)) := by
      have he_nonneg : 0 ≤ e := he₀_nonneg.trans hee₀
      let d : I := e - e₀
      have hd_nonneg : 0 ≤ d := sub_nonneg.2 hee₀
      have hd_le_e : d ≤ e := sub_le_self e he₀_nonneg
      have hd_norm : ‖d‖ ≤ 1 :=
        (CStarAlgebra.norm_le_norm_of_le_of_nonneg hd_le_e).trans he_norm
      have hdd_le : d * d ≤ d := CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one hd_nonneg hd_norm
      have hdA_nonneg : 0 ≤ (d : A) := hd_nonneg
      have hdA_star : star (d : A) = (d : A) := hdA_nonneg.isSelfAdjoint.star_eq
      have hddA_le : star (d : A) * (d : A) ≤ (d : A) := by
        rw [hdA_star]
        exact hdd_le
      have hφ_dd : ‖φ (star (d : A) * (d : A))‖ ≤ η := by
        have h1 : ‖φ (star (d : A) * (d : A))‖ ≤ ‖φ (d : A)‖ :=
          CStarAlgebra.norm_le_norm_of_le_of_nonneg (φ.mono hddA_le)
        have h2 : 0 ≤ φ (d : A) := φ.map_nonneg hdA_nonneg
        have h3 : ‖φ (d : A)‖ = (φ (d : A)).re := by
          simpa using congrArg Complex.re (Complex.norm_of_nonneg' h2)
        have h4 : (φ (d : A)).re = (φI e).re - (φI e₀).re := by
          simp [d, φI]
        have h5 : (φI e).re ≤ M :=
          (Complex.re_le_norm _).trans ((φI : I →L[ℂ] ℂ).unit_le_opNorm e he_norm)
        linarith
      have h_ae : ‖φ (star (a * (e : A)) * (a * (e : A)))‖ ≤ ‖(φ : A →L[ℂ] ℂ)‖ * ‖a‖ ^ 2 := by
        calc
          ‖φ (star (a * (e : A)) * (a * (e : A)))‖ ≤
              ‖(φ : A →L[ℂ] ℂ)‖ * ‖star (a * (e : A)) * (a * (e : A))‖ :=
            (φ : A →L[ℂ] ℂ).le_opNorm _
          _ = ‖(φ : A →L[ℂ] ℂ)‖ * ‖a * (e : A)‖ ^ 2 := by
            rw [CStarRing.norm_star_mul_self, ← sq]
          _ ≤ ‖(φ : A →L[ℂ] ℂ)‖ * ‖a‖ ^ 2 := by
            gcongr
            exact (norm_mul_le a (e : A)).trans (mul_le_of_le_one_right (norm_nonneg a) he_norm)
      have h_ea : ‖φ (((e : A) * a) * star ((e : A) * a))‖ ≤ ‖(φ : A →L[ℂ] ℂ)‖ * ‖a‖ ^ 2 := by
        calc
          ‖φ (((e : A) * a) * star ((e : A) * a))‖ ≤
              ‖(φ : A →L[ℂ] ℂ)‖ * ‖((e : A) * a) * star ((e : A) * a)‖ :=
            (φ : A →L[ℂ] ℂ).le_opNorm _
          _ = ‖(φ : A →L[ℂ] ℂ)‖ * ‖(e : A) * a‖ ^ 2 := by
            rw [CStarRing.norm_self_mul_star, ← sq]
          _ ≤ ‖(φ : A →L[ℂ] ℂ)‖ * ‖a‖ ^ 2 := by
            gcongr
            exact (norm_mul_le (e : A) a).trans (mul_le_of_le_one_left (norm_nonneg a) he_norm)
      have hsqrt_rhs : Real.sqrt (‖(φ : A →L[ℂ] ℂ)‖ * ‖a‖ ^ 2) =
          Real.sqrt ‖(φ : A →L[ℂ] ℂ)‖ * ‖a‖ := by
        rw [Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq (norm_nonneg a)]
      have hterm1 : ‖φ ((d : A) * (a * (e : A)))‖ ≤
          Real.sqrt η * (Real.sqrt ‖(φ : A →L[ℂ] ℂ)‖ * ‖a‖) := by
        rw [← hdA_star, ← hsqrt_rhs]
        exact (PositiveLinearMap.cauchy_schwarz_star_mul φ.toPositiveLinearMap (d : A)
          (a * (e : A))).trans (mul_le_mul (Real.sqrt_le_sqrt hφ_dd) (Real.sqrt_le_sqrt h_ae)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      have hterm2 : ‖φ (((e : A) * a) * (d : A))‖ ≤
          Real.sqrt η * (Real.sqrt ‖(φ : A →L[ℂ] ℂ)‖ * ‖a‖) := by
        have hdd_flip : (d : A) * star (d : A) = star (d : A) * (d : A) := by rw [hdA_star]
        rw [← hdA_star, ← hsqrt_rhs, mul_comm (Real.sqrt η)]
        refine (PositiveLinearMap.cauchy_schwarz_mul_star φ.toPositiveLinearMap ((e : A) * a)
          (d : A)).trans ?_
        rw [hdd_flip]
        exact mul_le_mul (Real.sqrt_le_sqrt h_ea) (Real.sqrt_le_sqrt hφ_dd)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have hid : (e : A) * a * (e₀ : A) - (e₀ : A) * a * (e : A) =
          (d : A) * (a * (e : A)) - ((e : A) * a) * (d : A) := by
        change (e : A) * a * (e₀ : A) - (e₀ : A) * a * (e : A) =
          ((e : A) - (e₀ : A)) * (a * (e : A)) - ((e : A) * a) * ((e : A) - (e₀ : A))
        noncomm_ring
      rw [hid, map_sub]
      exact (norm_sub_le _ _).trans (by linarith)
    -- Pass to the limit in `e` along `l₀` using ideal membership of `a * e₀` and `e₀ * a`.
    let b₁ : I := ⟨a * (e₀ : A), I.mul_mem_left a (e₀ : A) e₀.2⟩
    let b₂ : I := ⟨(e₀ : A) * a, I.mul_mem_right (e₀ : A) a e₀.2⟩
    have hb₁ : Tendsto (fun e : I => (e : A) * (a * (e₀ : A))) l₀ (𝓝 (a * (e₀ : A))) := by
      simpa [Function.comp_def] using
        (continuous_subtype_val.tendsto b₁).comp (hl₀.tendsto_mul_right b₁)
    have hb₂ : Tendsto (fun e : I => ((e₀ : A) * a) * (e : A)) l₀ (𝓝 ((e₀ : A) * a)) := by
      simpa [Function.comp_def] using
        (continuous_subtype_val.tendsto b₂).comp (hl₀.tendsto_mul_left b₂)
    have hlim_sub : Tendsto (fun e : I => (e : A) * a * (e₀ : A) - (e₀ : A) * a * (e : A)) l₀
        (𝓝 (a * (e₀ : A) - (e₀ : A) * a)) := by
      simpa only [mul_assoc] using hb₁.sub hb₂
    have hlim_norm : Tendsto (fun e : I => ‖φ ((e : A) * a * (e₀ : A) - (e₀ : A) * a * (e : A))‖)
        l₀ (𝓝 ‖φ (a * (e₀ : A) - (e₀ : A) * a)‖) :=
      ((φ.cont.tendsto _).comp hlim_sub).norm
    have hev : ∀ᶠ e : I in l₀, ‖φ ((e : A) * a * (e₀ : A) - (e₀ : A) * a * (e : A))‖ ≤
        2 * (Real.sqrt η * (Real.sqrt ‖(φ : A →L[ℂ] ℂ)‖ * ‖a‖)) := by
      have hsec : {e : I | e₀ ≤ e} ∩ Metric.closedBall 0 1 ∈ l₀ :=
        (CStarAlgebra.hasBasis_approximateUnit I).mem_of_mem ⟨he₀_nonneg, he₀_lt⟩
      filter_upwards [hsec] with e ⟨hee₀, he_ball⟩
      exact hη_step e hee₀ (by simpa using he_ball)
    have hle := le_of_tendsto hlim_norm hev
    have hneg : φ ((e₀ : A) * a - a * (e₀ : A)) = -φ (a * (e₀ : A) - (e₀ : A) * a) := by
      rw [← map_neg, neg_sub]
    rwa [hneg, norm_neg]
  -- Extend `hbound_strict` to `0 ≤ e₀`, `‖e₀‖ ≤ 1` via `(1 - 1 / (n + 1)) • e₀`.
  have hbound (e₀ : I) (he₀_nonneg : 0 ≤ e₀) (he₀_norm : ‖e₀‖ ≤ 1) :
      ‖φ ((e₀ : A) * a - a * (e₀ : A))‖ ≤
        2 * (Real.sqrt (M - (φI e₀).re) * (Real.sqrt ‖(φ : A →L[ℂ] ℂ)‖ * ‖a‖)) := by
    let r : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 1)
    have hr_nonneg (n : ℕ) : 0 ≤ r n := by
      dsimp [r]
      have hle : 1 / ((n : ℝ) + 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
      linarith
    have hr_lt_one (n : ℕ) : r n < 1 := by
      dsimp [r]
      have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    have hr_tendsto : Tendsto r atTop (𝓝 1) := by
      simpa [r] using (tendsto_const_nhds (x := (1 : ℝ))).sub
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have he_tendsto : Tendsto (fun n => r n • e₀) atTop (𝓝 e₀) := by
      simpa using hr_tendsto.smul (tendsto_const_nhds (x := e₀))
    have hf₁ : Continuous (fun x : I => ‖φ ((x : A) * a - a * (x : A))‖) :=
      continuous_norm.comp <| φ.cont.comp <|
        (continuous_subtype_val.mul continuous_const).sub
          (continuous_const.mul continuous_subtype_val)
    have hf₂ : Continuous (fun x : I =>
        2 * (Real.sqrt (M - (φI x).re) * (Real.sqrt ‖(φ : A →L[ℂ] ℂ)‖ * ‖a‖))) :=
      continuous_const.mul <|
        (Real.continuous_sqrt.comp
          (continuous_const.sub (Complex.continuous_re.comp φI.cont))).mul continuous_const
    refine le_of_tendsto_of_tendsto ((hf₁.tendsto e₀).comp he_tendsto)
      ((hf₂.tendsto e₀).comp he_tendsto) (Eventually.of_forall fun n => ?_)
    refine hbound_strict (r n • e₀) (smul_nonneg (hr_nonneg n) he₀_nonneg) ?_
    rw [norm_smul, Real.norm_of_nonneg (hr_nonneg n)]
    exact (mul_le_of_le_one_right (hr_nonneg n) he₀_norm).trans_lt (hr_lt_one n)
  -- Now let `e₀` run along `l₀`: `(φI e₀).re → M`, so the upper bound tends to `0`.
  have hφI_re : Tendsto (fun e₀ : I => (φI e₀).re) l₀ (𝓝 M) := by
    simpa [Function.comp_def] using
      (Complex.continuous_re.tendsto (M : ℂ)).comp (φI.tendsto_nhds_opNorm hl₀)
  have hsub_zero : Tendsto (fun e₀ : I => M - (φI e₀).re) l₀ (𝓝 0) := by
    simpa [sub_self] using (tendsto_const_nhds (x := M)).sub hφI_re
  have hsqrt_zero : Tendsto (fun e₀ : I => Real.sqrt (M - (φI e₀).re)) l₀ (𝓝 0) := by
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hsub_zero
  have hrhs_zero : Tendsto
      (fun e₀ : I => 2 * (Real.sqrt (M - (φI e₀).re) * (Real.sqrt ‖(φ : A →L[ℂ] ℂ)‖ * ‖a‖)))
      l₀ (𝓝 0) := by
    simpa using (hsqrt_zero.mul_const (Real.sqrt ‖(φ : A →L[ℂ] ℂ)‖ * ‖a‖)).const_mul 2
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hrhs_zero
  filter_upwards [hl₀.eventually_nonneg, hl₀.eventually_norm] with e₀ he₀_nonneg he₀_norm
  exact hbound e₀ he₀_nonneg he₀_norm

end PositiveContinuousLinearMap

namespace ContinuousLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Weak quasicentrality under continuous complex-linear functionals.** Along the canonical
approximate unit of a closed two-sided ideal `I`, `(e : A) * a - a * (e : A)` tends weakly to `0`
under every `ψ : A →L[ℂ] ℂ`. -/
theorem tendsto_commutator_approximateUnit_zero (ψ : A →L[ℂ] ℂ) (I : TwoSidedIdeal A)
    [IsClosed (I : Set A)] (a : A) :
    Tendsto (fun e : I => ψ ((e : A) * a - a * (e : A))) (CStarAlgebra.approximateUnit I)
      (𝓝 0) :=
  tendsto_zero_of_forall_positiveContinuousLinearMap
    (fun φ => φ.tendsto_commutator_approximateUnit_zero I a) ψ

/-- **Weak quasicentrality under continuous real-linear functionals.** Along the canonical
approximate unit of a closed two-sided ideal `I`, `(e : A) * a - a * (e : A)` tends weakly to `0`
under every `g : A →L[ℝ] ℝ`. -/
theorem tendsto_real_commutator_approximateUnit_zero (g : A →L[ℝ] ℝ) (I : TwoSidedIdeal A)
    [IsClosed (I : Set A)] (a : A) :
    Tendsto (fun e : I => g ((e : A) * a - a * (e : A))) (CStarAlgebra.approximateUnit I)
      (𝓝 0) :=
  tendsto_real_zero_of_forall_positiveContinuousLinearMap
    (fun φ => φ.tendsto_commutator_approximateUnit_zero I a) g

end ContinuousLinearMap

namespace TwoSidedIdeal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Finite-set norm quasicentrality in strict canonical upper sections.** For any closed two-sided
ideal `I` of `A`, any `e₀ : I` with `0 ≤ e₀` and `‖e₀‖ < 1`, any finite subset `F : Finset A`, and
any `ε > 0`, there exists `e : I` with `e₀ ≤ e`, `‖e‖ < 1`, and `‖(e : A) * a - a * (e : A)‖ < ε`
for all `a ∈ F`. -/
theorem exists_ge_and_norm_lt_one_and_forall_norm_commutator_lt (I : TwoSidedIdeal A)
    [IsClosed (I : Set A)] {e₀ : I} (he₀ : 0 ≤ e₀) (hnorm : ‖e₀‖ < 1) (F : Finset A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ e : I, e₀ ≤ e ∧ ‖e‖ < 1 ∧ ∀ a ∈ F, ‖(e : A) * a - a * (e : A)‖ < ε := by
  classical
  let V : Set I := {e : I | e₀ ≤ e} ∩ Metric.ball 0 1
  have hV_conv : Convex ℝ V := CStarAlgebra.convex_Ici_inter_ball e₀
  let Θ : I →ₗ[ℝ] (F → A) :=
    { toFun := fun e b => (e : A) * (b : A) - (b : A) * (e : A)
      map_add' := fun x y => by
        ext b
        simp only [Pi.add_apply, AddMemClass.coe_add, add_mul, mul_add]
        abel
      map_smul' := fun r x => by
        ext b
        have hcoe : ((r • x : I) : A) = r • (x : A) := by
          rw [← Complex.coe_smul, I.coe_smul_complex, Complex.coe_smul]
        simp only [RingHom.id_apply, Pi.smul_apply, hcoe, smul_mul_assoc, mul_smul_comm, smul_sub] }
  have h0_mem : (0 : F → A) ∈ closure (Θ '' V) := by
    by_contra hnot
    obtain ⟨Λ, u, hΛ0, hΛ_gt⟩ :=
      geometric_hahn_banach_point_closed (hV_conv.linear_image Θ).closure isClosed_closure hnot
    have hu_pos : 0 < u := by simpa using hΛ0
    have hΛ_tendsto : Tendsto (fun e : I => Λ (Θ e)) (CStarAlgebra.strictApproximateUnit I)
        (𝓝 0) := by
      have hsum_eq (e : I) :
          Λ (Θ e) = ∑ b : F, (Λ.comp (.single ℝ (fun _ : F => A) b))
            ((e : A) * (b : A) - (b : A) * (e : A)) := by
        have hy : Θ e = ∑ b : F, ContinuousLinearMap.single ℝ (fun _ : F => A) b (Θ e b) := by
          ext b'
          simp [Finset.sum_apply, Pi.single_apply]
        conv_lhs => rw [hy, map_sum]
        rfl
      simp_rw [hsum_eq]
      simpa using tendsto_finsetSum Finset.univ fun (b : F) _ =>
        ((Λ.comp (.single ℝ (fun _ : F => A) b)).tendsto_real_commutator_approximateUnit_zero
          I (b : A)).mono_left (CStarAlgebra.strictApproximateUnit_le_approximateUnit I)
    have hV_mem : V ∈ CStarAlgebra.strictApproximateUnit I :=
      (CStarAlgebra.hasBasis_strictApproximateUnit I).mem_of_mem ⟨he₀, hnorm⟩
    have hlt_mem : ∀ᶠ e : I in CStarAlgebra.strictApproximateUnit I, Λ (Θ e) < u :=
      hΛ_tendsto.eventually (gt_mem_nhds hu_pos)
    obtain ⟨e, heV, he_lt⟩ :=
      (CStarAlgebra.increasingStrictApproximateUnit I).neBot.nonempty_of_mem
        (inter_mem hV_mem hlt_mem)
    exact (he_lt.trans (hΛ_gt (Θ e) (subset_closure ⟨e, heV, rfl⟩))).false
  obtain ⟨_, ⟨e, ⟨hee₀, he_ball⟩, rfl⟩, hdist⟩ := Metric.mem_closure_iff.1 h0_mem ε hε
  refine ⟨e, hee₀, by simpa using he_ball, fun a ha => ?_⟩
  have hnorm_Θ : ‖Θ e‖ < ε := by simpa [dist_zero_left] using hdist
  exact (norm_le_pi_norm (Θ e) ⟨a, ha⟩).trans_lt hnorm_Θ

/-- **Arveson's quasicentral approximate unit theorem (ideal-filter form).** Every closed two-sided
ideal `I` of a C⋆-algebra `A` admits an increasing approximate unit `l : Filter I` with `‖e‖ < 1`
eventually and `(e : A) * a - a * (e : A) → 0` in norm for every `a : A`. -/
theorem exists_isIncreasingApproximateUnit_tendsto_commutator_zero (I : TwoSidedIdeal A)
    [IsClosed (I : Set A)] :
    ∃ l : Filter I, l.IsIncreasingApproximateUnit ∧ (∀ᶠ e in l, ‖e‖ < 1) ∧
      ∀ a : A, Tendsto (fun e : I => (e : A) * a - a * (e : A)) l (𝓝 0) := by
  classical
  let Idx := {x : I // 0 ≤ x ∧ ‖x‖ < 1} × Finset A × ℕ
  let W : Idx → Set I := fun p =>
    {e : I | p.1.1 ≤ e ∧ ‖e‖ < 1 ∧
      ∀ a ∈ p.2.1, ‖(e : A) * a - a * (e : A)‖ < 1 / ((p.2.2 : ℝ) + 1)}
  have hIdx_nonempty : Nonempty Idx := ⟨⟨⟨0, le_rfl, by simp⟩, ∅, 0⟩⟩
  have hW_nonempty (p : Idx) : (W p).Nonempty := by
    obtain ⟨e, he₁, he₂, he₃⟩ := exists_ge_and_norm_lt_one_and_forall_norm_commutator_lt I
      p.1.2.1 p.1.2.2 p.2.1 (ε := 1 / ((p.2.2 : ℝ) + 1)) (by positivity)
    exact ⟨e, he₁, he₂, he₃⟩
  have hW_dir : Directed (· ≥ ·) W := by
    rintro ⟨⟨x₁, hx₁₀, hx₁₁⟩, F₁, n₁⟩ ⟨⟨x₂, hx₂₀, hx₂₁⟩, F₂, n₂⟩
    obtain ⟨x₃, ⟨hx₃₀, hx₃_ball⟩, hx₁₃, hx₂₃⟩ := CStarAlgebra.directedOn_nonneg_ball
      x₁ ⟨hx₁₀, by simpa using hx₁₁⟩ x₂ ⟨hx₂₀, by simpa using hx₂₁⟩
    refine ⟨⟨⟨x₃, hx₃₀, by simpa using hx₃_ball⟩, F₁ ∪ F₂, max n₁ n₂⟩, ?_, ?_⟩
    · rintro e ⟨he_ge, he_norm, he_comm⟩
      refine ⟨hx₁₃.trans he_ge, he_norm,
        fun a ha => (he_comm a (Finset.mem_union_left _ ha)).trans_le ?_⟩
      gcongr
      exact le_max_left n₁ n₂
    · rintro e ⟨he_ge, he_norm, he_comm⟩
      refine ⟨hx₂₃.trans he_ge, he_norm,
        fun a ha => (he_comm a (Finset.mem_union_right _ ha)).trans_le ?_⟩
      gcongr
      exact le_max_right n₁ n₂
  let l : Filter I := ⨅ p : Idx, 𝓟 (W p)
  have hl_basis : l.HasBasis (fun _ : Idx => True) W := hasBasis_iInf_principal hW_dir
  have : l.NeBot := hl_basis.neBot_iff.2 fun _ => hW_nonempty _
  have hl_le : l ≤ CStarAlgebra.strictApproximateUnit I := by
    rw [(CStarAlgebra.hasBasis_strictApproximateUnit I).ge_iff]
    rintro x ⟨hx₀, hx₁⟩
    refine hl_basis.mem_iff.2 ⟨⟨⟨x, hx₀, hx₁⟩, ∅, 0⟩, trivial, ?_⟩
    rintro e ⟨he₁, he₂, -⟩
    exact ⟨he₁, by simpa using he₂⟩
  refine ⟨l, (CStarAlgebra.increasingStrictApproximateUnit I).mono hl_le,
    (CStarAlgebra.eventually_norm_lt_one_strictApproximateUnit I).filter_mono hl_le, fun a => ?_⟩
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine hl_basis.mem_iff.2 ⟨⟨⟨0, le_rfl, by simp⟩, {a}, n⟩, trivial, ?_⟩
  rintro e ⟨-, -, he_comm⟩
  simpa [dist_eq_norm] using (he_comm a (Finset.mem_singleton_self a)).trans hn

/-- **Sequential quasicentral approximate unit in the separable case.** If `A` is a separable
C⋆-algebra and `I` is a closed two-sided ideal of `A`, then `I` admits a monotone sequence
`e : ℕ → I` with `0 ≤ e n` and `‖e n‖ < 1` that forms an increasing approximate unit of `I` and
satisfies `‖(e n : A) * a - a * (e n : A)‖ → 0` for every `a : A`. -/
theorem exists_monotone_seq_quasicentral_approximateUnit [TopologicalSpace.SeparableSpace A]
    (I : TwoSidedIdeal A) [IsClosed (I : Set A)] :
    ∃ e : ℕ → I, Monotone e ∧ (∀ n, 0 ≤ e n ∧ ‖e n‖ < 1) ∧
      (Filter.map e atTop).IsIncreasingApproximateUnit ∧
      ∀ a : A, Tendsto (fun n => (e n : A) * a - a * (e n : A)) atTop (𝓝 0) := by
  classical
  have : Nonempty A := ⟨0⟩
  have : Nonempty I := ⟨0⟩
  let u : ℕ → I := TopologicalSpace.denseSeq I
  have hu : DenseRange u := TopologicalSpace.denseRange_denseSeq I
  let v : ℕ → A := TopologicalSpace.denseSeq A
  have hv : DenseRange v := TopologicalSpace.denseRange_denseSeq A
  let PosBall := {x : I // 0 ≤ x ∧ ‖x‖ < 1}
  -- Given `n` and `x₀ ∈ PosBall`, choose `x' ≥ x₀` in `PosBall` whose upper strict-ball section
  -- approximates `u 0, …, u n` within `1 / (n + 1)` and whose commutators with `v 0, …, v n` are
  -- `< 1 / (n + 1)`.
  have hstep (n : ℕ) (x₀ : PosBall) :
      ∃ x' : PosBall, x₀.1 ≤ x'.1 ∧
        (∀ y : I, x'.1 ≤ y → ‖y‖ < 1 → ∀ k ≤ n,
          ‖y * u k - u k‖ < 1 / ((n : ℝ) + 1) ∧ ‖u k * y - u k‖ < 1 / ((n : ℝ) + 1)) ∧
        (∀ k ≤ n, ‖(x'.1 : A) * v k - v k * (x'.1 : A)‖ < 1 / ((n : ℝ) + 1)) := by
    have hl_strict := CStarAlgebra.increasingStrictApproximateUnit I
    have hev_u : ∀ᶠ y : I in CStarAlgebra.strictApproximateUnit I,
        ∀ k ∈ Finset.range (n + 1),
          ‖y * u k - u k‖ < 1 / ((n : ℝ) + 1) ∧ ‖u k * y - u k‖ < 1 / ((n : ℝ) + 1) :=
      (eventually_all_finset (Finset.range (n + 1))).2 fun k _ =>
        ((tendsto_iff_norm_sub_tendsto_zero.1 (hl_strict.tendsto_mul_right (u k))).eventually
          (gt_mem_nhds (by positivity))).and
          ((tendsto_iff_norm_sub_tendsto_zero.1 (hl_strict.tendsto_mul_left (u k))).eventually
            (gt_mem_nhds (by positivity)))
    obtain ⟨x₁, ⟨hx₁₀, hx₁₁⟩, hx₁_sub⟩ :=
      (CStarAlgebra.hasBasis_strictApproximateUnit I).mem_iff.1 hev_u
    obtain ⟨x₂, ⟨hx₂₀, hx₂_ball⟩, hx₀₂, hx₁₂⟩ := CStarAlgebra.directedOn_nonneg_ball
      x₀.1 ⟨x₀.2.1, by simpa using x₀.2.2⟩ x₁ ⟨hx₁₀, by simpa using hx₁₁⟩
    obtain ⟨x₃, hx₂₃, hx₃_norm, hx₃_comm⟩ :=
      exists_ge_and_norm_lt_one_and_forall_norm_commutator_lt I hx₂₀ (by simpa using hx₂_ball)
        ((Finset.range (n + 1)).image v) (ε := 1 / ((n : ℝ) + 1)) (by positivity)
    refine ⟨⟨x₃, hx₂₀.trans hx₂₃, hx₃_norm⟩, hx₀₂.trans hx₂₃, fun y hy hy_norm k hk => ?_,
      fun k hk => hx₃_comm (v k) (Finset.mem_image.2 ⟨k, Finset.mem_range.2 (Nat.lt_succ_of_le hk),
        rfl⟩)⟩
    exact hx₁_sub ⟨(hx₁₂.trans hx₂₃).trans hy, by simpa using hy_norm⟩ k
      (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
  choose next hnext_le hnext_u hnext_v using hstep
  let seq : ℕ → PosBall := fun n => Nat.rec ⟨0, le_rfl, by simp⟩ (fun k ih => next k ih) n
  let e : ℕ → I := fun n => (seq n).1
  have he_mono : Monotone e := monotone_nat_of_le_succ fun n => hnext_le n (seq n)
  have he_bounds (n : ℕ) : 0 ≤ e n ∧ ‖e n‖ < 1 := (seq n).2
  -- Approximate unit property on `I` by density of `u` and uniform norm bound `‖e n‖ ≤ 1`.
  have he_mul_right (b : I) : Tendsto (fun n => e n * b) atTop (𝓝 b) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨_, ⟨k, rfl⟩, hk⟩ := Metric.mem_closure_iff.1 (hu b) (ε / 3) (by positivity)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < ε / 3 by positivity)
    refine ⟨max k m + 1, fun n hn => ?_⟩
    have hkn : k ≤ max k m := le_max_left k m
    have h_le_seq : (next (max k m) (seq (max k m))).1 ≤ e n := he_mono hn
    have hu_close : ‖e n * u k - u k‖ < 1 / (((max k m : ℕ) : ℝ) + 1) :=
      (hnext_u (max k m) (seq (max k m)) (e n) h_le_seq (he_bounds n).2 k hkn).1
    have hu_lt : ‖e n * u k - u k‖ < ε / 3 := by
      refine hu_close.trans (lt_of_le_of_lt ?_ hm)
      gcongr
      exact_mod_cast le_max_right k m
    have hdiff1 : ‖e n * b - e n * u k‖ ≤ dist b (u k) := by
      rw [← mul_sub, dist_eq_norm]
      exact (norm_mul_le (e n) (b - u k)).trans
        (mul_le_of_le_one_left (norm_nonneg _) (he_bounds n).2.le)
    rw [dist_eq_norm]
    have hsplit : e n * b - b = (e n * b - e n * u k) + (e n * u k - u k) + (u k - b) := by abel
    rw [hsplit]
    have htri := (norm_add_le ((e n * b - e n * u k) + (e n * u k - u k)) (u k - b)).trans
      (add_le_add (norm_add_le _ _) le_rfl)
    have hdist_symm : ‖u k - b‖ < ε / 3 := by rwa [← dist_eq_norm, dist_comm]
    linarith
  have he_mul_left (b : I) : Tendsto (fun n => b * e n) atTop (𝓝 b) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨_, ⟨k, rfl⟩, hk⟩ := Metric.mem_closure_iff.1 (hu b) (ε / 3) (by positivity)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < ε / 3 by positivity)
    refine ⟨max k m + 1, fun n hn => ?_⟩
    have hkn : k ≤ max k m := le_max_left k m
    have h_le_seq : (next (max k m) (seq (max k m))).1 ≤ e n := he_mono hn
    have hu_close : ‖u k * e n - u k‖ < 1 / (((max k m : ℕ) : ℝ) + 1) :=
      (hnext_u (max k m) (seq (max k m)) (e n) h_le_seq (he_bounds n).2 k hkn).2
    have hu_lt : ‖u k * e n - u k‖ < ε / 3 := by
      refine hu_close.trans (lt_of_le_of_lt ?_ hm)
      gcongr
      exact_mod_cast le_max_right k m
    have hdiff1 : ‖b * e n - u k * e n‖ ≤ dist b (u k) := by
      rw [← sub_mul, dist_eq_norm]
      exact (norm_mul_le (b - u k) (e n)).trans
        (mul_le_of_le_one_right (norm_nonneg _) (he_bounds n).2.le)
    rw [dist_eq_norm]
    have hsplit : b * e n - b = (b * e n - u k * e n) + (u k * e n - u k) + (u k - b) := by abel
    rw [hsplit]
    have htri := (norm_add_le ((b * e n - u k * e n) + (u k * e n - u k)) (u k - b)).trans
      (add_le_add (norm_add_le _ _) le_rfl)
    have hdist_symm : ‖u k - b‖ < ε / 3 := by rwa [← dist_eq_norm, dist_comm]
    linarith
  have he_approx : (Filter.map e atTop).IsIncreasingApproximateUnit :=
    { tendsto_mul_left := fun b => by simpa [Function.comp_def] using he_mul_left b
      tendsto_mul_right := fun b => by simpa [Function.comp_def] using he_mul_right b
      eventually_nonneg := eventually_map.2 (Eventually.of_forall fun n => (he_bounds n).1)
      eventually_norm := eventually_map.2 (Eventually.of_forall fun n => (he_bounds n).2.le) }
  -- Commutator convergence on `A` by density of `v` and `‖(e n : A)‖ ≤ 1`.
  refine ⟨e, he_mono, he_bounds, he_approx, fun a => ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := Metric.mem_closure_iff.1 (hv a) (ε / 3) (by positivity)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < ε / 3 by positivity)
  refine ⟨max k m + 1, fun n hn => ?_⟩
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  have hkr : k ≤ r := by omega
  have hmr : m ≤ r := by omega
  have hv_comm : ‖(e (r + 1) : A) * v k - v k * (e (r + 1) : A)‖ < ε / 3 := by
    refine (hnext_v r (seq r) k hkr).trans (lt_of_le_of_lt ?_ hm)
    gcongr
  have hnorm_le_one : ‖(e (r + 1) : A)‖ ≤ 1 := (he_bounds (r + 1)).2.le
  have hdiff1 : ‖(e (r + 1) : A) * (a - v k)‖ ≤ dist a (v k) := by
    rw [dist_eq_norm]
    exact (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hnorm_le_one)
  have hdiff2 : ‖(a - v k) * (e (r + 1) : A)‖ ≤ dist a (v k) := by
    rw [dist_eq_norm]
    exact (norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hnorm_le_one)
  rw [dist_zero_right]
  have hsplit : (e (r + 1) : A) * a - a * (e (r + 1) : A) =
      (e (r + 1) : A) * (a - v k) - (a - v k) * (e (r + 1) : A) +
        ((e (r + 1) : A) * v k - v k * (e (r + 1) : A)) := by
    noncomm_ring
  rw [hsplit]
  have htri := (norm_add_le ((e (r + 1) : A) * (a - v k) - (a - v k) * (e (r + 1) : A))
    ((e (r + 1) : A) * v k - v k * (e (r + 1) : A))).trans (add_le_add (norm_sub_le _ _) le_rfl)
  linarith

end TwoSidedIdeal

namespace TauCeti.CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Arveson's quasicentral approximate unit theorem.** Every closed two-sided ideal `I` of a
C⋆-algebra `A` admits a positive contractive approximate unit `l : Filter A` supported in `I` that
is quasicentral in `A`, i.e., `e * a - a * e → 0` along `l` for every `a : A`. -/
theorem exists_quasicentral_approximateUnit (I : TwoSidedIdeal A) (hI : IsClosed (I : Set A)) :
    ∃ l : Filter A, l.NeBot ∧ (∀ᶠ e in l, e ∈ I ∧ 0 ≤ e ∧ ‖e‖ ≤ 1) ∧
      (∀ a ∈ I, Tendsto (fun e ↦ e * a) l (𝓝 a)) ∧
      (∀ a ∈ I, Tendsto (fun e ↦ a * e) l (𝓝 a)) ∧
      (∀ a : A, Tendsto (fun e ↦ e * a - a * e) l (𝓝 0)) := by
  have : IsClosed (I : Set A) := hI
  obtain ⟨l₀, hl₀, -, hcomm⟩ := I.exists_isIncreasingApproximateUnit_tendsto_commutator_zero
  have := hl₀.neBot
  refine ⟨l₀.map ((↑) : I → A), map_neBot, ?_, ?_, ?_, ?_⟩
  · rw [eventually_map]
    filter_upwards [hl₀.eventually_nonneg, hl₀.eventually_norm] with e he₀ he₁
    exact ⟨e.2, he₀, he₁⟩
  · intro a ha
    rw [tendsto_map'_iff]
    let b : I := ⟨a, ha⟩
    simpa [Function.comp_def] using
      (continuous_subtype_val.tendsto b).comp (hl₀.tendsto_mul_right b)
  · intro a ha
    rw [tendsto_map'_iff]
    let b : I := ⟨a, ha⟩
    simpa [Function.comp_def] using
      (continuous_subtype_val.tendsto b).comp (hl₀.tendsto_mul_left b)
  · intro a
    rw [tendsto_map'_iff]
    simpa [Function.comp_def] using hcomm a

end TauCeti.CStarAlgebra
