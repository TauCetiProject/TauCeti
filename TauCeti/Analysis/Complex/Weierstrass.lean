/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.RingTheory.Polynomial.Vieta
import TauCeti.Analysis.Analytic.Multiset
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.Contour.Residue.LogDeriv
import TauCeti.Analysis.Contour.Residue.Theorem
import TauCeti.Analysis.Meromorphic.Divisor
import TauCeti.Analysis.Meromorphic.Order
import TauCeti.Analysis.Polynomial.Order
import TauCeti.Analysis.Polynomial.SimpleRoots.Basic

/-!
# The complex analytic Weierstrass preparation and division theorems

Let `f : E × ℂ → ℂ` be jointly holomorphic at `(x₀, w₀)` on the product of a finite-dimensional
complex normed space `E` with `ℂ`, and assume that the slice `w ↦ f (x₀, w)` has finite order of
vanishing `d` at `w₀`. This file proves the local analytic **Weierstrass preparation theorem** and
**Weierstrass division theorem** by Cauchy's contour-integral method and Newton's identities.

## Main results

* `AnalyticAt.exists_weierstrassPreparation`: **Weierstrass preparation.** If `f` is analytic at
  `(x₀, w₀)` and `analyticOrderAt (fun w ↦ f (x₀, w)) w₀ = d`, there exist analytic coefficient
  functions `c : Fin d → E → ℂ` vanishing at `x₀` and a nonvanishing analytic function `u` at
  `(x₀, w₀)` such that near `(x₀, w₀)`,
  `f (x, w) = (TauCeti.Polynomial.monicOfCoeff (fun i ↦ c i x)).eval (w - w₀) * u (x, w)`.
* `AnalyticAt.exists_weierstrassDivision_monicOfCoeff`: **Weierstrass division by a Weierstrass
  polynomial.** Given analytic functions `c : Fin d → E → ℂ` vanishing at `x₀` and any `g`
  analytic at `(x₀, w₀)`, there exist `q` analytic at `(x₀, w₀)` and `r : Fin d → E → ℂ` analytic
  at `x₀` such that near `(x₀, w₀)`,
  `g (x, w) = (TauCeti.Polynomial.monicOfCoeff (fun i ↦ c i x)).eval (w - w₀) * q (x, w) +
    ∑ i : Fin d, r i x * (w - w₀) ^ (i : ℕ)`.
* `AnalyticAt.exists_weierstrassDivision`: **Weierstrass division.** Combining preparation and
  division by a Weierstrass polynomial divides any analytic `g` by any `f` whose slice has order
  `d` at `w₀`.

## Proof outline

After translating `(x₀, w₀)` to `(0, 0)`, choose `R > 0` so that `w ↦ f (0, w)` has `0` as its
unique zero on `closedBall 0 R`, and then `δ > 0` so that `f (x, ·)` is analytic on
`closedBall 0 R` and nonvanishing on `sphere 0 R` for `x ∈ ball 0 δ`. For each such `x`, the
residue theorem applied to `ζ ↦ ζ ^ k * logDeriv (f (x, ·)) ζ` expresses the `k`-th power sum of
the zero multiset of `f (x, ·)` in `ball 0 R` (counted with multiplicity) as a contour integral
whose integrand is jointly analytic along `ball 0 δ ×ˢ sphere 0 R`. Parametric analyticity of
contour integrals (`TauCeti.analyticOnNhd_circleIntegral`) makes every power sum — and for `k = 0`
the total multiplicity, which is therefore locally constant and equal to `d` — analytic on
`ball 0 δ`. Newton's identities (`TauCeti.analyticAt_esymm_of_forall_analyticAt_sum_map_pow`) and
Vieta's formula (`Multiset.prod_X_sub_C_coeff`) turn this into analyticity of the coefficients of
the monic polynomial `P_x` whose roots are those zeros. For each `x`, dividing `f (x, ·)` by `P_x`
cancels all zeros in `closedBall 0 R`, so its meromorphic normal form `u₀_x` is analytic and
nonvanishing on `closedBall 0 R` and represented on `ball 0 R` by Cauchy's integral formula, which
makes `(x, w) ↦ u₀_x w` jointly analytic at `(0, 0)`.

For division by `P_x(w) = w ^ d + ∑ i, c_i(x) w ^ i`, choose `R > 0` and `δ > 0` so that `P_x` is
nonvanishing on `sphere 0 R` for `x ∈ ball 0 δ`. Expanding `(P_x(ζ) - P_x(w)) / (ζ - w)` as a
polynomial in `w` of degree `< d` via `geom_sum₂_mul` rewrites the Cauchy kernel `(ζ - w)⁻¹` as
`P_x(w) / ((ζ - w) P_x(ζ))` plus a degree-`< d` polynomial in `w`; integrating against
`(2πi)⁻¹ g (x, ζ)` over `C(0, R)` produces the analytic quotient and remainder coefficients.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §6.1.
* H. Grauert, R. Remmert, *Coherent Analytic Sheaves*, Ch. 2, §1.
-/

public section

open Complex Filter Function Metric Polynomial Real Set Topology

namespace TauCeti

section Aux

/-- The finitely supported `ℕ`-valued zero divisor of an analytic function `g` in `ball 0 R`. -/
private noncomputable def zeroDivisor {g : ℂ → ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) : ℂ →₀ ℕ :=
  Finsupp.ofSupportFinite (fun z ↦ (MeromorphicOn.divisor g (ball 0 R) z).toNat) <|
    (MeromorphicOn.divisor_ball_support_finite hg.meromorphicOn).subset fun z hz ↦
      Function.mem_support.2 fun h0 ↦ Function.mem_support.1 hz (by simp [h0])

/-- The multiset of zeros of an analytic function `g` in `ball 0 R`, counted with multiplicity via
`MeromorphicOn.divisor`. -/
private noncomputable def zeroMultiset {g : ℂ → ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) : Multiset ℂ :=
  (zeroDivisor hg).toMultiset

private theorem natCast_zeroDivisor_apply {g : ℂ → ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) (z : ℂ) :
    (zeroDivisor hg z : ℤ) = MeromorphicOn.divisor g (ball 0 R) z :=
  Int.toNat_of_nonneg
    (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hg.mono ball_subset_closedBall) z)

private theorem mem_ball_of_mem_zeroMultiset {g : ℂ → ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) {α : ℂ} (hα : α ∈ zeroMultiset hg) :
    α ∈ ball 0 R := by
  rw [zeroMultiset, Finsupp.mem_toMultiset, Finsupp.mem_support_iff] at hα
  exact (MeromorphicOn.divisor g (ball 0 R)).supportWithinDomain
    (Function.mem_support.2 fun h0 ↦ hα (by simp [zeroDivisor, h0]))

private theorem meromorphicOrderAt_eq_count_zeroMultiset {g : ℂ → ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) (hsphere : ∀ ζ ∈ sphere 0 R, g ζ ≠ 0)
    {z : ℂ} (hz : z ∈ closedBall 0 R) :
    meromorphicOrderAt g z = ((Multiset.count z (zeroMultiset hg) : ℕ) : WithTop ℤ) := by
  classical
  rcases (ball_union_sphere (x := (0 : ℂ)) (ε := R) ▸ hz) with hzb | hzs
  · rw [← WithTop.coe_untop₀_of_ne_top
        (hg.meromorphicOrderAt_ne_top_of_forall_mem_sphere_ne_zero hsphere hz),
      ← (hg.mono ball_subset_closedBall).meromorphicOn.divisor_apply hzb,
      ← natCast_zeroDivisor_apply hg z, zeroMultiset, Finsupp.count_toMultiset]
    rfl
  · have hc0 : Multiset.count z (zeroMultiset hg) = 0 := Multiset.count_eq_zero.2 fun hmem ↦
      (mem_ball.1 (mem_ball_of_mem_zeroMultiset hg hmem)).ne (mem_sphere.1 hzs)
    rw [(hg z hz).meromorphicOrderAt_eq, (hg z hz).analyticOrderAt_eq_zero.2 (hsphere z hzs), hc0]
    simp

private theorem sum_map_zeroMultiset_eq_circleIntegral {g φ : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) (hsphere : ∀ ζ ∈ sphere 0 R, g ζ ≠ 0)
    (hφ : AnalyticOnNhd ℂ φ (closedBall 0 R)) :
    ((zeroMultiset hg).map φ).sum = (2 * π * I)⁻¹ * ∮ ζ in C(0, R), φ ζ * logDeriv g ζ := by
  classical
  set S := (zeroDivisor hg).support
  have hgb : AnalyticOnNhd ℂ g (ball 0 R) := hg.mono ball_subset_closedBall
  have hS_ball : (S : Set ℂ) ⊆ ball 0 R := fun z hz ↦
    mem_ball_of_mem_zeroMultiset hg ((Finsupp.mem_toMultiset _ _).2 hz)
  have hsupp : ∀ z ∈ closedBall 0 R,
      meromorphicOrderAt (fun ζ ↦ φ ζ * logDeriv g ζ) z < 0 → z ∈ S := by
    intro z hz hneg
    by_contra hzS
    have hc0 : Multiset.count z (zeroMultiset hg) = 0 := by
      rw [zeroMultiset, Finsupp.count_toMultiset]
      exact Finsupp.notMem_support_iff.1 hzS
    have hord0 := meromorphicOrderAt_eq_count_zeroMultiset hg hsphere hz
    rw [hc0, (hg z hz).meromorphicOrderAt_eq] at hord0
    have hgz : g z ≠ 0 := (hg z hz).analyticOrderAt_eq_zero.1 (by simpa using hord0)
    exact not_le_of_gt hneg
      ((hφ z hz).fun_mul (Contour.analyticAt_logDeriv_of_analyticAt (hg z hz) hgz)
        |>.meromorphicOrderAt_nonneg)
  have hres := Contour.classicalResidueTheorem_circle_of_meromorphicOrderAt_neg
    (f := fun ζ ↦ φ ζ * logDeriv g ζ) hR S
    (hφ.meromorphicOn.mul hg.meromorphicOn.logDeriv) hS_ball hsupp
  have hsum_multiset : ((zeroMultiset hg).map φ).sum =
      ∑ s ∈ S, (MeromorphicOn.divisor g (ball 0 R) s : ℂ) * φ s := by
    rw [zeroMultiset, Finsupp.toMultiset_map, Finsupp.sum_toMultiset,
      Finsupp.sum_mapDomain_index (h := fun b n ↦ n • b)
        (fun _ ↦ zero_nsmul _) (fun b m n ↦ add_nsmul b m n), Finsupp.sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [nsmul_eq_mul, ← Int.cast_natCast, natCast_zeroDivisor_apply]
  have hsum_res : ∑ s ∈ S, Contour.residue (fun ζ ↦ φ ζ * logDeriv g ζ) s =
      ∑ s ∈ S, (MeromorphicOn.divisor g (ball 0 R) s : ℂ) * φ s := by
    refine Finset.sum_congr rfl fun s hs ↦ ?_
    have hsb := hS_ball hs
    have hsc := ball_subset_closedBall hsb
    have hord : meromorphicOrderAt g s = (MeromorphicOn.divisor g (ball 0 R) s : WithTop ℤ) := by
      rw [hgb.meromorphicOn.divisor_apply hsb, WithTop.coe_untop₀_of_ne_top
        (hg.meromorphicOrderAt_ne_top_of_forall_mem_sphere_ne_zero hsphere hsc)]
    have hgs := (hg s hsc).meromorphicAt
    have hlim := ((hφ s hsc).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
      (Contour.tendsto_sub_mul_nhds_residue hgs.logDeriv
        (by simpa using Contour.neg_one_le_meromorphicOrderAt_logDeriv hgs))
    rw [Contour.residue_logDeriv_eq_meromorphicOrderAt hgs hord, mul_comm (φ s)] at hlim
    exact Contour.residue_eq_of_tendsto_sub_mul ((hφ s hsc).meromorphicAt.mul hgs.logDeriv)
      (hlim.congr fun ζ ↦ by ring)
  rw [hres, hsum_res, inv_mul_cancel_left₀ two_pi_I_ne_zero, hsum_multiset]

private theorem zeroMultiset_eq_replicate_zero {g : ℂ → ℂ} {R : ℝ} {d : ℕ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) (hd : analyticOrderAt g 0 = d)
    (honly : ∀ z ∈ closedBall 0 R, z ≠ 0 → g z ≠ 0) :
    zeroMultiset hg = Multiset.replicate d 0 := by
  classical
  have hgb : AnalyticOnNhd ℂ g (ball 0 R) := hg.mono ball_subset_closedBall
  ext z
  rw [zeroMultiset, Finsupp.count_toMultiset, Multiset.count_replicate]
  have hcount := natCast_zeroDivisor_apply hg z
  split_ifs with hz0
  · subst hz0
    rw [MeromorphicOn.divisor_eq_analyticOrderNatAt hgb.meromorphicOn
      (hg 0 (mem_closedBall_self hR.le)) (mem_ball_self hR), analyticOrderNatAt, hd,
      ENat.toNat_natCast] at hcount
    exact_mod_cast hcount
  · by_cases hzb : z ∈ ball 0 R
    · rw [MeromorphicOn.divisor_eq_analyticOrderNatAt hgb.meromorphicOn
        (hg z (ball_subset_closedBall hzb)) hzb, analyticOrderNatAt,
        (hg z (ball_subset_closedBall hzb)).analyticOrderAt_eq_zero.2
          (honly z (ball_subset_closedBall hzb) (Ne.symm hz0)),
        ENat.toNat_zero, Nat.cast_zero] at hcount
      exact_mod_cast hcount
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hzb] at hcount
      exact_mod_cast hcount

/-- On a closed disc where `g` is analytic and boundary-nonvanishing, dividing `g` by the monic
polynomial of its interior zeros produces a nonvanishing analytic factor represented in the open
disc by Cauchy's integral formula. -/
private theorem exists_slice_weierstrassFactor {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) (hsphere : ∀ ζ ∈ sphere 0 R, g ζ ≠ 0) :
    let P : ℂ[X] := ((zeroMultiset hg).map (fun α ↦ X - C α)).prod
    ∃ u₀ : ℂ → ℂ, AnalyticOnNhd ℂ u₀ (closedBall 0 R) ∧ (∀ z ∈ closedBall 0 R, u₀ z ≠ 0) ∧
      (∀ z ∈ closedBall 0 R, g z = P.eval z * u₀ z) ∧
      (∀ w ∈ ball 0 R, u₀ w = (2 * π * I)⁻¹ * ∮ ζ in C(0, R), (ζ - w)⁻¹ * (g ζ / P.eval ζ)) := by
  intro P
  have hP_an (w : ℂ) : AnalyticAt ℂ (fun z ↦ P.eval z) w :=
    (AnalyticOnNhd.eval_polynomial P) w trivial
  have hp0 : P ≠ 0 := (monic_multiset_prod_of_monic _ _ fun α _ ↦ monic_X_sub_C α).ne_zero
  have hr : P.roots = zeroMultiset hg := roots_multiset_prod_X_sub_C (zeroMultiset hg)
  have hP_ord (z : ℂ) : meromorphicOrderAt (fun w ↦ P.eval w) z =
      ((Multiset.count z (zeroMultiset hg) : ℕ) : WithTop ℤ) := by
    rw [(hP_an z).meromorphicOrderAt_eq, Polynomial.analyticOrderAt_eval hp0 z,
      ← Polynomial.count_roots, hr]
    simp
  have hP_sphere {ζ : ℂ} (hζ : ζ ∈ sphere 0 R) : P.eval ζ ≠ 0 := fun h0 ↦
    (mem_ball.1 (mem_ball_of_mem_zeroMultiset hg (by rwa [← hr, mem_roots hp0]))).ne
      (mem_sphere.1 hζ)
  set q : ℂ → ℂ := g / fun w ↦ P.eval w
  have hq_mero : MeromorphicOn q (closedBall 0 R) :=
    hg.meromorphicOn.div (AnalyticOnNhd.meromorphicOn fun w _ ↦ hP_an w)
  have hq_ord {z : ℂ} (hz : z ∈ closedBall 0 R) : meromorphicOrderAt q z = 0 := by
    rw [meromorphicOrderAt_div (hg z hz).meromorphicAt (hP_an z).meromorphicAt,
      meromorphicOrderAt_eq_count_zeroMultiset hg hsphere hz, hP_ord z]
    simp
  set u₀ := toMeromorphicNFOn q (closedBall 0 R)
  have hu₀_nf : MeromorphicNFOn u₀ (closedBall 0 R) := meromorphicNFOn_toMeromorphicNFOn q _
  have hu₀_ord {z : ℂ} (hz : z ∈ closedBall 0 R) : meromorphicOrderAt u₀ z = 0 :=
    (meromorphicOrderAt_toMeromorphicNFOn hq_mero hz).trans (hq_ord hz)
  have hu₀_an : AnalyticOnNhd ℂ u₀ (closedBall 0 R) := fun z hz ↦
    (hu₀_nf hz).meromorphicOrderAt_nonneg_iff_analyticAt.1 (hu₀_ord hz).symm.le
  refine ⟨u₀, hu₀_an, fun z hz ↦ (hu₀_nf hz).meromorphicOrderAt_eq_zero_iff.1 (hu₀_ord hz),
    fun z hz ↦ ?_, fun w hw ↦ ?_⟩
  · have hP_ne_nhds : ∀ᶠ w in 𝓝[≠] z, P.eval w ≠ 0 :=
      (hP_an z).eventually_eq_zero_or_eventually_ne_zero.resolve_left fun hzero ↦
        ENat.natCast_ne_top _ ((Polynomial.analyticOrderAt_eval hp0 z).symm.trans
          (analyticOrderAt_eq_top.2 hzero))
    have heq_ne : g =ᶠ[𝓝[≠] z] fun w ↦ P.eval w * u₀ w := by
      filter_upwards [hq_mero.toMeromorphicNFOn_eq_self_on_nhdsNE hz, hP_ne_nhds] with w hw hPw
      dsimp only [u₀]
      rw [hw]
      simp only [q, Pi.div_apply, mul_div_cancel₀ _ hPw]
    exact (((hg z hz).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      ((hP_an z).mul (hu₀_an z hz)).continuousAt).1 heq_ne).eq_of_nhds
  · have hcauchy := hu₀_an.differentiableOn.circleIntegral_sub_inv_smul hw
    simp only [smul_eq_mul] at hcauchy
    have hu₀_sphere {ζ : ℂ} (hζ : ζ ∈ sphere 0 R) : u₀ ζ = g ζ / P.eval ζ :=
      (((hu₀_an ζ (sphere_subset_closedBall hζ)).continuousAt
        |>.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
        ((hg ζ (sphere_subset_closedBall hζ)).div (hP_an ζ) (hP_sphere hζ)).continuousAt).1
        (hq_mero.toMeromorphicNFOn_eq_self_on_nhdsNE (sphere_subset_closedBall hζ))).eq_of_nhds
    rw [circleIntegral.integral_congr hR.le fun ζ hζ ↦ by rw [← hu₀_sphere hζ], hcauchy,
      inv_mul_cancel_left₀ two_pi_I_ne_zero]

/-- On an open preconnected base `U` where `F` is jointly analytic on `U ×ˢ closedBall 0 R`,
boundary-nonvanishing on `U ×ˢ sphere 0 R`, and has `0` as its unique zero of multiplicity `d` on
`closedBall 0 R` over `x₀ ∈ U`, the symmetric zero-polynomial coefficients of `F (x, ·)` in
`ball 0 R` depend analytically on `x ∈ U` and vanish at `x₀`. -/
private theorem exists_analyticOnNhd_zeroPolynomial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {U : Set E} (hU : IsOpen U) (hU_conn : IsPreconnected U) {x₀ : E} (hx₀ : x₀ ∈ U)
    {R : ℝ} (hR : 0 < R) {d : ℕ} {F : E × ℂ → ℂ}
    (hF_an : ∀ x ∈ U, ∀ w ∈ closedBall (0 : ℂ) R, AnalyticAt ℂ F (x, w))
    (hF_sphere : ∀ x ∈ U, ∀ ζ ∈ sphere (0 : ℂ) R, F (x, ζ) ≠ 0)
    (hF_ord : analyticOrderAt (fun w ↦ F (x₀, w)) 0 = d)
    (hF_only : ∀ w ∈ closedBall (0 : ℂ) R, w ≠ 0 → F (x₀, w) ≠ 0) :
    ∃ c : Fin d → E → ℂ,
      (∀ i, AnalyticOnNhd ℂ (c i) U) ∧ (∀ i, c i x₀ = 0) ∧
      ∀ x (hx : x ∈ U),
        Polynomial.monicOfCoeff (fun i ↦ c i x) =
          ((zeroMultiset (g := fun w ↦ F (x, w)) fun w hw ↦ (hF_an x hx w hw).curry_right).map
            (fun α ↦ X - C α)).prod := by
  classical
  have hFx_an {x : E} (hx : x ∈ U) : AnalyticOnNhd ℂ (fun w ↦ F (x, w)) (closedBall 0 R) :=
    fun w hw ↦ (hF_an x hx w hw).curry_right
  let Z : E → Multiset ℂ := fun x ↦ if hx : x ∈ U then zeroMultiset (hFx_an hx) else 0
  have hZ_eq {x : E} (hx : x ∈ U) : Z x = zeroMultiset (hFx_an hx) := dite_eq_left hx
  have hpow_int (k : ℕ) {x : E} (hx : x ∈ U) : ((Z x).map (· ^ k)).sum =
      (2 * π * I)⁻¹ * ∮ ζ in C(0, R), ζ ^ k * (fderiv ℂ F (x, ζ) (0, 1) / F (x, ζ)) := by
    rw [hZ_eq hx, sum_map_zeroMultiset_eq_circleIntegral hR (hFx_an hx) (hF_sphere x hx)
      (fun z _ ↦ by simpa using (analyticAt_id (𝕜 := ℂ) (z := z)).fun_pow k)]
    refine congrArg (_ * ·) (circleIntegral.integral_congr hR.le fun ζ hζ ↦ ?_)
    have hderiv : deriv (fun w ↦ F (x, w)) ζ = fderiv ℂ F (x, ζ) (0, 1) :=
      ((hF_an x hx ζ (sphere_subset_closedBall hζ)).differentiableAt.hasFDerivAt.comp_hasDerivAt
        ζ ((hasDerivAt_const ζ x).prodMk (hasDerivAt_id' ζ))).deriv
    rw [logDeriv_apply, hderiv]
  have hpow_an (k : ℕ) : AnalyticOnNhd ℂ (fun x ↦ ((Z x).map (· ^ k)).sum) U := by
    refine AnalyticOnNhd.congr hU (fun x hx ↦ ?_) fun x hx ↦ (hpow_int k hx).symm
    refine analyticAt_const.fun_mul (TauCeti.analyticAt_circleIntegral
      (f := fun q : E × ℂ ↦ q.2 ^ k * (fderiv ℂ F q (0, 1) / F q)) fun ζ hζ ↦ ?_)
    rw [abs_of_pos hR] at hζ
    have hFp := hF_an x hx ζ (sphere_subset_closedBall hζ)
    exact (analyticAt_snd.fun_pow k).fun_mul
      ((((ContinuousLinearMap.apply ℂ ℂ ((0 : E), (1 : ℂ))).analyticAt _).comp_of_eq
        hFp.fderiv rfl).fun_div hFp (hF_sphere x hx ζ hζ))
  have hZ0 : Z x₀ = Multiset.replicate d 0 :=
    (hZ_eq hx₀).trans (zeroMultiset_eq_replicate_zero hR (hFx_an hx₀) hF_ord hF_only)
  have hcard {x : E} (hx : x ∈ U) : (Z x).card = d := by
    have hcont : ContinuousOn (fun x ↦ (Z x).card) U :=
      Nat.isClosedEmbedding_coe_real.isInducing.continuousOn_iff.2
        ((Complex.continuous_re.comp_continuousOn (hpow_an 0).continuousOn).congr fun _ _ ↦ by simp)
    simpa [hZ0] using hU_conn.constant hcont hx hx₀
  refine ⟨fun i x ↦ (-1) ^ (d - (i : ℕ)) * (Z x).esymm (d - (i : ℕ)),
    fun i x hx ↦ analyticAt_const.fun_mul
      (TauCeti.analyticAt_esymm_of_forall_analyticAt_sum_map_pow _ fun j _ _ ↦ hpow_an j x hx),
    fun i ↦ ?_, fun x hx ↦ ?_⟩
  · have h := Multiset.prod_X_sub_C_coeff (Multiset.replicate d (0 : ℂ)) (k := (i : ℕ))
      (by simp [i.2.le])
    simpa [hZ0, coeff_X_pow, i.2.ne] using h.symm
  · rw [← hZ_eq hx, ← Polynomial.monicOfCoeff_coeff
      (monic_multiset_prod_of_monic _ _ fun α _ ↦ monic_X_sub_C α)
      ((natDegree_multiset_prod_X_sub_C_eq_card _).trans (hcard hx))]
    exact congrArg _ (funext fun i ↦ by
      rw [Multiset.prod_X_sub_C_coeff (Z x) (by rw [hcard hx]; exact i.2.le), hcard hx])

/-- Joint analyticity at `(x₀, 0)` of the Cauchy integral against `(monicOfCoeff (c · x))⁻¹` when
all lower coefficients `c i` vanish at `x₀`. -/
private theorem analyticAt_circleIntegral_div_eval_monicOfCoeff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {d : ℕ} {c : Fin d → E → ℂ} {H : E × ℂ → ℂ} {x₀ : E} {R : ℝ} (hR : 0 < R)
    (hc : ∀ i, AnalyticAt ℂ (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hH : ∀ ζ ∈ sphere (0 : ℂ) R, AnalyticAt ℂ H (x₀, ζ)) :
    AnalyticAt ℂ (fun p : E × ℂ ↦ (2 * π * I)⁻¹ * ∮ ζ in C(0, R),
      (ζ - p.2)⁻¹ * (H (p.1, ζ) / (Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval ζ)) (x₀, 0) := by
  refine analyticAt_const.fun_mul (TauCeti.analyticAt_circleIntegral
    (f := fun q : (E × ℂ) × ℂ ↦ (q.2 - q.1.2)⁻¹ *
      (H (q.1.1, q.2) / (Polynomial.monicOfCoeff (fun i ↦ c i q.1.1)).eval q.2))
    fun ζ hζ ↦ ?_)
  rw [abs_of_pos hR] at hζ
  have hζ0 := ne_of_mem_sphere hζ hR.ne'
  refine ((analyticAt_snd.fun_sub (analyticAt_snd.comp_of_eq analyticAt_fst rfl)).inv
    (sub_ne_zero.2 hζ0)).fun_mul (((hH ζ hζ).comp_of_eq
    ((analyticAt_fst.comp_of_eq analyticAt_fst rfl).prod analyticAt_snd) rfl).fun_div
    ((Polynomial.analyticAt_eval_monicOfCoeff _).comp
      ((AnalyticAt.pi fun i ↦ (hc i).comp_of_eq
        (analyticAt_fst.comp_of_eq analyticAt_fst rfl) rfl).prod analyticAt_snd)) ?_)
  simp [Polynomial.eval_monicOfCoeff, hc0, pow_ne_zero d hζ0]

/-- Given the analytic zero-polynomial coefficients `c` of `F` on `U ×ˢ closedBall 0 R`, Cauchy's
integral formula constructs the jointly analytic nonvanishing Weierstrass unit at `(x₀, 0)`. -/
private theorem exists_analyticAt_weierstrassUnit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {U : Set E} {x₀ : E} (hx₀ : x₀ ∈ U) {R : ℝ} (hR : 0 < R) {d : ℕ}
    {F : E × ℂ → ℂ} {c : Fin d → E → ℂ}
    (hF_an : ∀ x ∈ U, ∀ w ∈ closedBall (0 : ℂ) R, AnalyticAt ℂ F (x, w))
    (hF_sphere : ∀ x ∈ U, ∀ ζ ∈ sphere (0 : ℂ) R, F (x, ζ) ≠ 0)
    (hc : ∀ i, AnalyticAt ℂ (c i) x₀) (hc0 : ∀ i, c i x₀ = 0)
    (hmonic : ∀ x (hx : x ∈ U),
      Polynomial.monicOfCoeff (fun i ↦ c i x) =
        ((zeroMultiset (g := fun w ↦ F (x, w)) fun w hw ↦ (hF_an x hx w hw).curry_right).map
          (fun α ↦ X - C α)).prod) :
    ∃ u : E × ℂ → ℂ, AnalyticAt ℂ u (x₀, 0) ∧ u (x₀, 0) ≠ 0 ∧
      ∀ x ∈ U, ∀ w ∈ ball 0 R,
        F (x, w) = (Polynomial.monicOfCoeff (fun i ↦ c i x)).eval w * u (x, w) := by
  let u : E × ℂ → ℂ := fun p ↦ (2 * π * I)⁻¹ * ∮ ζ in C(0, R),
    (ζ - p.2)⁻¹ * (F (p.1, ζ) / (Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval ζ)
  have hslice {x : E} (hx : x ∈ U) :
      (∀ w ∈ ball 0 R, F (x, w) = (Polynomial.monicOfCoeff (fun i ↦ c i x)).eval w * u (x, w)) ∧
      u (x, 0) ≠ 0 := by
    obtain ⟨u₀, _, hu₀_ne, hu₀_fac, hu₀_int⟩ := exists_slice_weierstrassFactor
      (g := fun w ↦ F (x, w)) hR (fun w hw ↦ (hF_an x hx w hw).curry_right) (hF_sphere x hx)
    have hu_eq {w : ℂ} (hw : w ∈ ball 0 R) : u (x, w) = u₀ w := by
      simp only [u, hmonic x hx, ← hu₀_int w hw]
    exact ⟨fun w hw ↦ by rw [hu_eq hw, hmonic x hx]; exact hu₀_fac w (ball_subset_closedBall hw),
      hu_eq (mem_ball_self hR) ▸ hu₀_ne 0 (mem_closedBall_self hR.le)⟩
  exact ⟨u, analyticAt_circleIntegral_div_eval_monicOfCoeff hR hc hc0
    (fun ζ hζ ↦ hF_an x₀ hx₀ ζ (sphere_subset_closedBall hζ)),
    (hslice hx₀).2, fun _ hx ↦ (hslice hx).1⟩

/-- The polynomial difference kernel coefficients for dividing by `monicOfCoeff c` of degree `d`. -/
private def divKernelCoeff {d : ℕ} (c : Fin d → ℂ) (k : Fin d) (ζ : ℂ) : ℂ :=
  ζ ^ (d - 1 - (k : ℕ)) +
    ∑ i : Fin d, if (k : ℕ) < (i : ℕ) then c i * ζ ^ ((i : ℕ) - 1 - (k : ℕ)) else 0

private theorem analyticAt_divKernelCoeff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {d : ℕ} {c : Fin d → E → ℂ} {x₀ : E} (hc : ∀ i, AnalyticAt ℂ (c i) x₀) (k : Fin d) (ζ : ℂ) :
    AnalyticAt ℂ (fun q : E × ℂ ↦ divKernelCoeff (fun i ↦ c i q.1) k q.2) (x₀, ζ) := by
  simp only [divKernelCoeff]
  refine (analyticAt_snd.fun_pow _).fun_add (Finset.analyticAt_fun_sum _ fun i _ ↦ ?_)
  split_ifs
  · exact ((hc i).comp_of_eq analyticAt_fst rfl).fun_mul (analyticAt_snd.fun_pow _)
  · exact analyticAt_const

private theorem sub_mul_sum_divKernelCoeff {d : ℕ} (c : Fin d → ℂ) (ζ w : ℂ) :
    (ζ - w) * ∑ k : Fin d, divKernelCoeff c k ζ * w ^ (k : ℕ) =
      (Polynomial.monicOfCoeff c).eval ζ - (Polynomial.monicOfCoeff c).eval w := by
  have hpow {n : ℕ} (hn : n ≤ d) :
      (ζ - w) * ∑ k : Fin d, (if (k : ℕ) < n then ζ ^ (n - 1 - (k : ℕ)) else 0) * w ^ (k : ℕ) =
        ζ ^ n - w ^ n := by
    rw [Fin.sum_univ_eq_sum_range (fun k ↦ (if k < n then ζ ^ (n - 1 - k) else 0) * w ^ k) d,
      ← Finset.sum_subset (Finset.range_mono hn) fun k _ hkn ↦ by simp [Finset.mem_range.not.1 hkn],
      Finset.sum_congr rfl fun k hk ↦ by rw [ite_eq_left (Finset.mem_range.1 hk), mul_comm]]
    linear_combination -(geom_sum₂_mul w ζ n)
  have hlower : (ζ - w) * ∑ k : Fin d,
      (∑ i : Fin d, if (k : ℕ) < (i : ℕ) then c i * ζ ^ ((i : ℕ) - 1 - (k : ℕ)) else 0) *
        w ^ (k : ℕ) = ∑ i : Fin d, c i * (ζ ^ (i : ℕ) - w ^ (i : ℕ)) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← hpow i.2.le, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by split_ifs <;> ring
  have htop : (ζ - w) * ∑ k : Fin d, ζ ^ (d - 1 - (k : ℕ)) * w ^ (k : ℕ) = ζ ^ d - w ^ d := by
    simpa only [Fin.is_lt, ↓reduceIte] using hpow le_rfl
  simp only [divKernelCoeff, add_mul, Finset.sum_add_distrib, mul_add, hlower, htop,
    Polynomial.eval_monicOfCoeff, mul_sub, Finset.sum_sub_distrib]
  ring

/-- On an open disc `ball 0 R` where `g` is analytic up to the boundary and `monicOfCoeff c` has no
zeros on `sphere 0 R`, Cauchy's integral formula decomposes `g w` into `(monicOfCoeff c).eval w`
times a contour-integral quotient plus a degree-`< d` polynomial remainder. -/
private theorem eq_eval_monicOfCoeff_mul_circleIntegral_add_sum {d : ℕ} (c : Fin d → ℂ)
    {g : ℂ → ℂ} {R : ℝ} (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hP : ∀ ζ ∈ sphere 0 R, (Polynomial.monicOfCoeff c).eval ζ ≠ 0)
    {w : ℂ} (hw : w ∈ ball 0 R) :
    g w = (Polynomial.monicOfCoeff c).eval w *
        ((2 * π * I)⁻¹ * ∮ ζ in C(0, R),
          (ζ - w)⁻¹ * (g ζ / (Polynomial.monicOfCoeff c).eval ζ)) +
      ∑ k : Fin d,
        ((2 * π * I)⁻¹ * ∮ ζ in C(0, R),
          divKernelCoeff c k ζ * (g ζ / (Polynomial.monicOfCoeff c).eval ζ)) * w ^ (k : ℕ) := by
  have hR : 0 ≤ R := dist_nonneg.trans (mem_ball.1 hw).le
  let P_eval : ℂ → ℂ := (Polynomial.monicOfCoeff c).eval
  have hcauchy := hg.differentiableOn.circleIntegral_sub_inv_smul hw
  simp only [smul_eq_mul] at hcauchy
  have hP_cont : ContinuousOn P_eval (sphere 0 R) := by
    simp only [P_eval, Polynomial.eval_monicOfCoeff]; fun_prop
  have hquot_cont : ContinuousOn (fun ζ ↦ g ζ / P_eval ζ) (sphere 0 R) :=
    (hg.continuousOn.mono sphere_subset_closedBall).div hP_cont hP
  have hzw_ne : ∀ ζ ∈ sphere 0 R, ζ - w ≠ 0 := fun ζ hζ ↦
    sub_ne_zero.2 fun h ↦ (mem_ball.1 hw).ne (h ▸ mem_sphere.1 hζ)
  have hint1 : CircleIntegrable (fun ζ ↦ P_eval w * ((ζ - w)⁻¹ * (g ζ / P_eval ζ))) 0 R :=
    (continuousOn_const.mul
      (((continuousOn_id.sub continuousOn_const).inv₀ hzw_ne).mul hquot_cont)).circleIntegrable hR
  have hint_k (k : Fin d) :
      CircleIntegrable (fun ζ ↦ w ^ (k : ℕ) * (divKernelCoeff c k ζ * (g ζ / P_eval ζ))) 0 R := by
    have hker_cont : ContinuousOn (fun ζ ↦ divKernelCoeff c k ζ) (sphere 0 R) := by
      simp only [divKernelCoeff]
      refine (continuousOn_id.pow _).add (continuousOn_finsetSum _ fun i _ ↦ ?_)
      split_ifs
      · exact continuousOn_const.mul (continuousOn_id.pow _)
      · exact continuousOn_const
    exact (continuousOn_const.mul (hker_cont.mul hquot_cont)).circleIntegrable hR
  have hpointwise : ∀ ζ ∈ sphere 0 R, (ζ - w)⁻¹ * g ζ =
      P_eval w * ((ζ - w)⁻¹ * (g ζ / P_eval ζ)) +
        ∑ k : Fin d, w ^ (k : ℕ) * (divKernelCoeff c k ζ * (g ζ / P_eval ζ)) := by
    intro ζ hζ
    have hdiff := sub_mul_sum_divKernelCoeff c ζ w
    have hPζ : P_eval ζ ≠ 0 := hP ζ hζ
    have hζw : ζ - w ≠ 0 := hzw_ne ζ hζ
    have hsum_rw : ∑ k : Fin d, w ^ (k : ℕ) * (divKernelCoeff c k ζ * (g ζ / P_eval ζ)) =
        (g ζ / P_eval ζ) * ∑ k : Fin d, divKernelCoeff c k ζ * w ^ (k : ℕ) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ ↦ by ring
    rw [hsum_rw]
    field_simp
    linear_combination -g ζ * hdiff
  have hint_eq := circleIntegral.integral_congr hR hpointwise
  rw [circleIntegral.integral_add hint1 (CircleIntegrable.fun_sum Finset.univ fun k _ ↦ hint_k k),
    circleIntegral.integral_const_mul,
    circleIntegral.integral_fun_sum fun k _ ↦ hint_k k] at hint_eq
  rw [← inv_mul_cancel_left₀ two_pi_I_ne_zero (g w), ← hcauchy, hint_eq, mul_add,
    ← mul_left_comm (P_eval w), Finset.mul_sum]
  exact congrArg (_ + ·) (Finset.sum_congr rfl fun k _ ↦ by
    simp only [circleIntegral.integral_const_mul]; ring)

end Aux

end TauCeti

namespace AnalyticAt

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- **Complex analytic Weierstrass preparation theorem.** Let `f : E × ℂ → ℂ` be analytic at
`(x₀, w₀)` on the product of a finite-dimensional complex normed space `E` with `ℂ`, and suppose
the vertical slice `w ↦ f (x₀, w)` has finite order of vanishing `d` at `w₀`. Then there exist
analytic coefficient functions `c : Fin d → E → ℂ` vanishing at `x₀` and an analytic function `u`
nonvanishing at `(x₀, w₀)` such that near `(x₀, w₀)`,
`f (x, w) = (TauCeti.Polynomial.monicOfCoeff (fun i ↦ c i x)).eval (w - w₀) * u (x, w)`. -/
theorem exists_weierstrassPreparation {f : E × ℂ → ℂ} {x₀ : E} {w₀ : ℂ} {d : ℕ}
    (hf : AnalyticAt ℂ f (x₀, w₀)) (hd : analyticOrderAt (fun w ↦ f (x₀, w)) w₀ = d) :
    ∃ (c : Fin d → E → ℂ) (u : E × ℂ → ℂ),
      (∀ i, AnalyticAt ℂ (c i) x₀) ∧ (∀ i, c i x₀ = 0) ∧
      AnalyticAt ℂ u (x₀, w₀) ∧ u (x₀, w₀) ≠ 0 ∧
      f =ᶠ[𝓝 (x₀, w₀)] fun p ↦
        (TauCeti.Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval (p.2 - w₀) * u p := by
  set F : E × ℂ → ℂ := fun p ↦ f (p.1, w₀ + p.2)
  have hF : AnalyticAt ℂ F (x₀, 0) :=
    hf.comp_of_eq (analyticAt_fst.prod (analyticAt_const.fun_add analyticAt_snd)) (by simp)
  have hF_ord : analyticOrderAt (fun w ↦ F (x₀, w)) 0 = d := by
    have htr : AnalyticAt ℂ (fun w : ℂ ↦ w₀ + w) 0 := analyticAt_const.fun_add analyticAt_id
    have htr' : deriv (fun w : ℂ ↦ w₀ + w) 0 ≠ 0 := by
      rw [deriv_const_add, deriv_id'']; exact one_ne_zero
    exact (congrArg (analyticOrderAt · 0) (funext fun w ↦ by simp [F])).trans <|
      (analyticOrderAt_comp_of_deriv_ne_zero htr htr').trans <|
        (congrArg (analyticOrderAt (fun w ↦ f (x₀, w))) (add_zero w₀)).trans hd
  have hF_isol : ∀ᶠ w in 𝓝[≠] (0 : ℂ), F (x₀, w) ≠ 0 :=
    hF.curry_right.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun hzero ↦
      ENat.natCast_ne_top d (hF_ord.symm.trans (analyticOrderAt_eq_top.2 hzero))
  obtain ⟨r₁, hr₁, hball₁⟩ := Metric.mem_nhds_iff.1 ((isOpen_analyticAt ℂ F).mem_nhds hF)
  obtain ⟨r₂, hr₂, hball₂⟩ := Metric.mem_nhds_iff.1 (eventually_nhdsWithin_iff.1 hF_isol)
  set R : ℝ := min r₁ r₂ / 2
  have hR : 0 < R := half_pos (lt_min hr₁ hr₂)
  have hF0_an {w : ℂ} (hw : w ∈ closedBall (0 : ℂ) R) : AnalyticAt ℂ F (x₀, w) :=
    hball₁ (by simp [Prod.dist_eq, (mem_closedBall_zero_iff.1 hw).trans_lt
      ((half_lt_self (lt_min hr₁ hr₂)).trans_le (min_le_left _ _))])
  have hF0_only : ∀ w ∈ closedBall (0 : ℂ) R, w ≠ 0 → F (x₀, w) ≠ 0 := fun w hw ↦
    hball₂ (mem_ball.2 ((mem_closedBall.1 hw).trans_lt
      ((half_lt_self (lt_min hr₁ hr₂)).trans_le (min_le_right _ _))))
  have hev_an : ∀ᶠ x in 𝓝 x₀, ∀ w ∈ closedBall (0 : ℂ) R, AnalyticAt ℂ F (x, w) :=
    (isCompact_closedBall (0 : ℂ) R).eventually_forall_of_forall_eventually fun _ hw ↦
      (hF0_an hw).eventually_analyticAt
  have hev_ne : ∀ᶠ x in 𝓝 x₀, ∀ ζ ∈ sphere (0 : ℂ) R, F (x, ζ) ≠ 0 :=
    (isCompact_sphere (0 : ℂ) R).eventually_forall_of_forall_eventually fun ζ hζ ↦
      (hF0_an (sphere_subset_closedBall hζ)).continuousAt.eventually_ne
        (hF0_only ζ (sphere_subset_closedBall hζ) (ne_of_mem_sphere hζ hR.ne'))
  obtain ⟨δ, hδ, hδ_prop⟩ := Metric.mem_nhds_iff.1 (hev_an.and hev_ne)
  obtain ⟨c, hc_an, hc0, hmonic⟩ := exists_analyticOnNhd_zeroPolynomial isOpen_ball
    (convex_ball x₀ δ).isPreconnected (mem_ball_self hδ) hR
    (fun _ hx ↦ (hδ_prop hx).1) (fun _ hx ↦ (hδ_prop hx).2) hF_ord hF0_only
  obtain ⟨U, hU_an, hU0, hFU⟩ := exists_analyticAt_weierstrassUnit (mem_ball_self hδ) hR
    (fun _ hx ↦ (hδ_prop hx).1) (fun _ hx ↦ (hδ_prop hx).2)
    (fun i ↦ hc_an i x₀ (mem_ball_self hδ)) hc0 hmonic
  refine ⟨c, fun p ↦ U (p.1, p.2 - w₀), fun i ↦ hc_an i x₀ (mem_ball_self hδ), hc0,
    hU_an.comp_of_eq (analyticAt_fst.prod (analyticAt_snd.fun_sub analyticAt_const)) (by simp),
    by simpa using hU0, ?_⟩
  filter_upwards [prod_mem_nhds (ball_mem_nhds x₀ hδ) (ball_mem_nhds w₀ hR)] with ⟨x, w⟩ ⟨hx, hw⟩
  have hw_ball : w - w₀ ∈ ball (0 : ℂ) R := by simpa [dist_eq_norm] using mem_ball.1 hw
  simpa [F, add_sub_cancel] using hFU x hx (w - w₀) hw_ball

/-- **Complex analytic Weierstrass division by a Weierstrass polynomial.** Let `c : Fin d → E → ℂ`
be analytic at `x₀` with `c i x₀ = 0`, and let `g : E × ℂ → ℂ` be analytic at `(x₀, w₀)`. Then
there exist `q : E × ℂ → ℂ` analytic at `(x₀, w₀)` and `r : Fin d → E → ℂ` analytic at `x₀` such
that near `(x₀, w₀)`,
`g (x, w) = (TauCeti.Polynomial.monicOfCoeff (fun i ↦ c i x)).eval (w - w₀) * q (x, w) +
  ∑ i : Fin d, r i x * (w - w₀) ^ (i : ℕ)`. -/
theorem exists_weierstrassDivision_monicOfCoeff {d : ℕ} {c : Fin d → E → ℂ} {g : E × ℂ → ℂ}
    {x₀ : E} {w₀ : ℂ} (hg : AnalyticAt ℂ g (x₀, w₀)) (hc : ∀ i, AnalyticAt ℂ (c i) x₀)
    (hc0 : ∀ i, c i x₀ = 0) :
    ∃ (q : E × ℂ → ℂ) (r : Fin d → E → ℂ),
      AnalyticAt ℂ q (x₀, w₀) ∧ (∀ i, AnalyticAt ℂ (r i) x₀) ∧
      g =ᶠ[𝓝 (x₀, w₀)] fun p ↦
        (TauCeti.Polynomial.monicOfCoeff (fun i ↦ c i p.1)).eval (p.2 - w₀) * q p +
          ∑ i : Fin d, r i p.1 * (p.2 - w₀) ^ (i : ℕ) := by
  set G : E × ℂ → ℂ := fun p ↦ g (p.1, w₀ + p.2)
  have hG : AnalyticAt ℂ G (x₀, 0) :=
    hg.comp_of_eq (analyticAt_fst.prod (analyticAt_const.fun_add analyticAt_snd)) (by simp)
  let P_eval : E → ℂ → ℂ := fun x ζ ↦ (TauCeti.Polynomial.monicOfCoeff (fun i ↦ c i x)).eval ζ
  obtain ⟨r₁, hr₁, hball₁⟩ := Metric.mem_nhds_iff.1 ((isOpen_analyticAt ℂ G).mem_nhds hG)
  set R : ℝ := r₁ / 2
  have hR : 0 < R := half_pos hr₁
  have hG0_an {w : ℂ} (hw : w ∈ closedBall (0 : ℂ) R) : AnalyticAt ℂ G (x₀, w) :=
    hball₁ (by simp [Prod.dist_eq, (mem_closedBall_zero_iff.1 hw).trans_lt (half_lt_self hr₁)])
  have hP_an0 (ζ : ℂ) : AnalyticAt ℂ (fun p : E × ℂ ↦ P_eval p.1 p.2) (x₀, ζ) :=
    (TauCeti.Polynomial.analyticAt_eval_monicOfCoeff _).comp
      ((AnalyticAt.pi fun i ↦ (hc i).comp_of_eq analyticAt_fst rfl).prod analyticAt_snd)
  have hP0_sphere {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) R) : P_eval x₀ ζ ≠ 0 := by
    simp [P_eval, TauCeti.Polynomial.eval_monicOfCoeff, hc0,
      pow_ne_zero d (ne_of_mem_sphere hζ hR.ne')]
  have hev_G : ∀ᶠ x in 𝓝 x₀, ∀ w ∈ closedBall (0 : ℂ) R, AnalyticAt ℂ G (x, w) :=
    (isCompact_closedBall (0 : ℂ) R).eventually_forall_of_forall_eventually fun _ hw ↦
      (hG0_an hw).eventually_analyticAt
  have hev_P : ∀ᶠ x in 𝓝 x₀, ∀ ζ ∈ sphere (0 : ℂ) R, P_eval x ζ ≠ 0 :=
    (isCompact_sphere (0 : ℂ) R).eventually_forall_of_forall_eventually fun ζ hζ ↦
      (hP_an0 ζ).continuousAt.eventually_ne (hP0_sphere hζ)
  obtain ⟨δ, hδ, hδ_prop⟩ := Metric.mem_nhds_iff.1 (hev_G.and hev_P)
  let Q : E × ℂ → ℂ := fun p ↦
    (2 * π * I)⁻¹ * ∮ ζ in C(0, R), (ζ - p.2)⁻¹ * (G (p.1, ζ) / P_eval p.1 ζ)
  let r : Fin d → E → ℂ := fun k x ↦
    (2 * π * I)⁻¹ * ∮ ζ in C(0, R),
      divKernelCoeff (fun i ↦ c i x) k ζ * (G (x, ζ) / P_eval x ζ)
  have hr_an (k : Fin d) : AnalyticAt ℂ (r k) x₀ :=
    analyticAt_const.fun_mul <| TauCeti.analyticAt_circleIntegral
      (f := fun q : E × ℂ ↦
        divKernelCoeff (fun i ↦ c i q.1) k q.2 * (G (q.1, q.2) / P_eval q.1 q.2))
      fun ζ hζ ↦ by
        rw [abs_of_pos hR] at hζ
        exact (analyticAt_divKernelCoeff hc k ζ).fun_mul
          ((hG0_an (sphere_subset_closedBall hζ)).fun_div (hP_an0 ζ) (hP0_sphere hζ))
  refine ⟨fun p ↦ Q (p.1, p.2 - w₀), r,
    (analyticAt_circleIntegral_div_eval_monicOfCoeff hR hc hc0
      fun _ hζ ↦ hG0_an (sphere_subset_closedBall hζ)).comp_of_eq
      (analyticAt_fst.prod (analyticAt_snd.fun_sub analyticAt_const)) (by simp),
    hr_an, ?_⟩
  filter_upwards [prod_mem_nhds (ball_mem_nhds x₀ hδ) (ball_mem_nhds w₀ hR)] with ⟨x, w⟩ ⟨hx, hw⟩
  have hw_ball : w - w₀ ∈ ball (0 : ℂ) R := by simpa [dist_eq_norm] using mem_ball.1 hw
  simpa [G, P_eval, Q, r, add_sub_cancel] using
    eq_eval_monicOfCoeff_mul_circleIntegral_add_sum (g := fun ζ ↦ G (x, ζ)) (fun i ↦ c i x)
      (fun ζ hζ ↦ ((hδ_prop hx).1 ζ hζ).curry_right) (hδ_prop hx).2 hw_ball

/-- **Complex analytic Weierstrass division theorem.** Let `f, g : E × ℂ → ℂ` be analytic at
`(x₀, w₀)` on the product of a finite-dimensional complex normed space `E` with `ℂ`, and suppose
the vertical slice `w ↦ f (x₀, w)` has finite order of vanishing `d` at `w₀`. Then there exist `q`
analytic at `(x₀, w₀)` and `r : Fin d → E → ℂ` analytic at `x₀` such that near `(x₀, w₀)`,
`g (x, w) = f (x, w) * q (x, w) + ∑ i : Fin d, r i x * (w - w₀) ^ (i : ℕ)`. -/
theorem exists_weierstrassDivision {f g : E × ℂ → ℂ} {x₀ : E} {w₀ : ℂ} {d : ℕ}
    (hg : AnalyticAt ℂ g (x₀, w₀)) (hf : AnalyticAt ℂ f (x₀, w₀))
    (hd : analyticOrderAt (fun w ↦ f (x₀, w)) w₀ = d) :
    ∃ (q : E × ℂ → ℂ) (r : Fin d → E → ℂ),
      AnalyticAt ℂ q (x₀, w₀) ∧ (∀ i, AnalyticAt ℂ (r i) x₀) ∧
      g =ᶠ[𝓝 (x₀, w₀)] fun p ↦ f p * q p + ∑ i : Fin d, r i p.1 * (p.2 - w₀) ^ (i : ℕ) := by
  obtain ⟨c, u, hc, hc0, hu, hu0, hprep⟩ := hf.exists_weierstrassPreparation hd
  obtain ⟨q₀, r, hq₀, hr, hdiv⟩ := hg.exists_weierstrassDivision_monicOfCoeff hc hc0
  refine ⟨fun p ↦ q₀ p / u p, r, hq₀.fun_div hu hu0, hr, ?_⟩
  filter_upwards [hprep, hdiv, hu.continuousAt.eventually_ne hu0] with p hp hgp hup
  rw [hgp, hp, mul_assoc, mul_div_cancel₀ _ hup]

end AnalyticAt
