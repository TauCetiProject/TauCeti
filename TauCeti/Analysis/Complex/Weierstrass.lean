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
import TauCeti.Analysis.Contour.Argument.Divisor
import TauCeti.Analysis.Contour.Residue.LogDeriv
import TauCeti.Analysis.Contour.Residue.Theorem
import TauCeti.Analysis.Meromorphic.Divisor
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

/-- The multiset of zeros of an analytic function `g` in `ball 0 R`, counted with multiplicity via
`MeromorphicOn.divisor`. -/
private noncomputable def zeroMultiset {g : ℂ → ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) : Multiset ℂ :=
  ∑ s ∈ (MeromorphicOn.divisor_ball_support_finite hg.meromorphicOn).toFinset,
    Multiset.replicate (MeromorphicOn.divisor g (ball 0 R) s).toNat s

private theorem mem_ball_of_mem_zeroMultiset {g : ℂ → ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) {α : ℂ} (hα : α ∈ zeroMultiset hg) :
    α ∈ ball 0 R := by
  classical
  obtain ⟨s, hs, hmem⟩ := Multiset.mem_sum.1 hα
  rw [Multiset.eq_of_mem_replicate hmem]
  exact (MeromorphicOn.divisor g (ball 0 R)).supportWithinDomain (by simpa using hs)

private theorem count_zeroMultiset {g : ℂ → ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) (z : ℂ) :
    (Multiset.count z (zeroMultiset hg) : ℤ) = MeromorphicOn.divisor g (ball 0 R) z := by
  classical
  set S := (MeromorphicOn.divisor_ball_support_finite hg.meromorphicOn).toFinset
  have hnn := MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hg.mono ball_subset_closedBall) z
  rw [show Multiset.count z (zeroMultiset hg) =
      ∑ s ∈ S, Multiset.count z
        (Multiset.replicate (MeromorphicOn.divisor g (ball 0 R) s).toNat s) from
    map_sum (Multiset.countAddMonoidHom z) _ S]
  by_cases hzS : z ∈ S
  · rw [Finset.sum_eq_single_of_mem z hzS fun s _ hne ↦ by simp [Multiset.count_replicate, hne],
      Multiset.count_replicate_self, Int.toNat_of_nonneg hnn]
  · rw [Finset.sum_eq_zero fun s hs ↦ by
      simp [Multiset.count_replicate, show s ≠ z from fun h ↦ hzS (h ▸ hs)]]
    exact_mod_cast (Function.notMem_support.1 (by simpa [S] using hzS)).symm

private theorem meromorphicOrderAt_ne_top_of_sphere {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) (hsphere : ∀ ζ ∈ sphere 0 R, g ζ ≠ 0)
    {z : ℂ} (hz : z ∈ closedBall 0 R) : meromorphicOrderAt g z ≠ ⊤ := by
  have hR_mem : (R : ℂ) ∈ sphere 0 R := by simp [abs_of_pos hR]
  have hRc := sphere_subset_closedBall hR_mem
  refine hg.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    (convex_closedBall 0 R).isPreconnected hRc hz ?_
  rw [(hg _ hRc).meromorphicOrderAt_eq, (hg _ hRc).analyticOrderAt_eq_zero.2 (hsphere _ hR_mem)]
  simp

private theorem meromorphicOrderAt_eq_count_zeroMultiset {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) (hsphere : ∀ ζ ∈ sphere 0 R, g ζ ≠ 0)
    {z : ℂ} (hz : z ∈ closedBall 0 R) :
    meromorphicOrderAt g z = ((Multiset.count z (zeroMultiset hg) : ℕ) : WithTop ℤ) := by
  rcases (ball_union_sphere (x := (0 : ℂ)) (ε := R) ▸ hz) with hzb | hzs
  · rw [← WithTop.coe_untop₀_of_ne_top (meromorphicOrderAt_ne_top_of_sphere hR hg hsphere hz),
      ← (hg.mono ball_subset_closedBall).meromorphicOn.divisor_apply hzb,
      ← count_zeroMultiset hg z]
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
  set S := (MeromorphicOn.divisor_ball_support_finite hg.meromorphicOn).toFinset
  have hgb : AnalyticOnNhd ℂ g (ball 0 R) := hg.mono ball_subset_closedBall
  have hS_ball : (S : Set ℂ) ⊆ ball 0 R := fun z hz ↦
    (MeromorphicOn.divisor g (ball 0 R)).supportWithinDomain (by simpa [S] using hz)
  have hsupp : ∀ z ∈ closedBall 0 R,
      meromorphicOrderAt (fun ζ ↦ φ ζ * logDeriv g ζ) z < 0 → z ∈ S := by
    intro z hz hneg
    by_contra hzS
    have hc0 : Multiset.count z (zeroMultiset hg) = 0 := by
      exact_mod_cast (count_zeroMultiset hg z).trans
        (Function.notMem_support.1 (by simpa [S] using hzS))
    have hord0 := meromorphicOrderAt_eq_count_zeroMultiset hR hg hsphere hz
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
    refine (map_sum (AddMonoidHom.mk' (fun m : Multiset ℂ ↦ (m.map φ).sum) fun _ _ ↦ by simp)
      _ S).trans (Finset.sum_congr rfl fun s _ ↦ ?_)
    simp only [AddMonoidHom.mk'_apply, Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hgb s)]
  have hsum_res : ∑ s ∈ S, Contour.residue (fun ζ ↦ φ ζ * logDeriv g ζ) s =
      ∑ s ∈ S, (MeromorphicOn.divisor g (ball 0 R) s : ℂ) * φ s := by
    refine Finset.sum_congr rfl fun s hs ↦ ?_
    have hsb := hS_ball hs
    have hsc := ball_subset_closedBall hsb
    have hord : meromorphicOrderAt g s = (MeromorphicOn.divisor g (ball 0 R) s : WithTop ℤ) := by
      rw [hgb.meromorphicOn.divisor_apply hsb,
        WithTop.coe_untop₀_of_ne_top (meromorphicOrderAt_ne_top_of_sphere hR hg hsphere hsc)]
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
  have hgb : AnalyticOnNhd ℂ g (ball 0 R) := hg.mono ball_subset_closedBall
  ext z
  rw [Multiset.count_replicate]
  have hcount := count_zeroMultiset hg z
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
      meromorphicOrderAt_eq_count_zeroMultiset hR hg hsphere hz, hP_ord z]
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
      rw [show u₀ w = g w / P.eval w from hw, mul_div_cancel₀ _ hPw]
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

/-- The polynomial difference kernel coefficients for dividing by `monicOfCoeff c` of degree `d`. -/
private def divKernelCoeff {d : ℕ} (c : Fin d → ℂ) (k : Fin d) (ζ : ℂ) : ℂ :=
  ζ ^ (d - 1 - (k : ℕ)) +
    ∑ i : Fin d, if (k : ℕ) < (i : ℕ) then c i * ζ ^ ((i : ℕ) - 1 - (k : ℕ)) else 0

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
  simp only [divKernelCoeff, add_mul, Finset.sum_add_distrib, mul_add, hlower,
    show (ζ - w) * ∑ k : Fin d, ζ ^ (d - 1 - (k : ℕ)) * w ^ (k : ℕ) = ζ ^ d - w ^ d by
      simpa only [Fin.is_lt, ↓reduceIte] using hpow le_rfl,
    Polynomial.eval_monicOfCoeff, mul_sub, Finset.sum_sub_distrib]
  ring

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
  set F : E × ℂ → ℂ := fun p ↦ f (x₀ + p.1, w₀ + p.2)
  have hF : AnalyticAt ℂ F (0, 0) :=
    hf.comp_of_eq ((analyticAt_const.fun_add analyticAt_fst).prod
      (analyticAt_const.fun_add analyticAt_snd)) (by simp)
  have hF_ord : analyticOrderAt (fun w ↦ F (0, w)) 0 = d := by
    have htr : AnalyticAt ℂ (fun w : ℂ ↦ w₀ + w) 0 := analyticAt_const.fun_add analyticAt_id
    have htr' : deriv (fun w : ℂ ↦ w₀ + w) 0 ≠ 0 := by
      rw [deriv_const_add, deriv_id'']; exact one_ne_zero
    exact (congrArg (analyticOrderAt · 0) (funext fun w ↦ by simp [F])).trans <|
      (analyticOrderAt_comp_of_deriv_ne_zero htr htr').trans <|
        (congrArg (analyticOrderAt (fun w ↦ f (x₀, w))) (add_zero w₀)).trans hd
  have hF_isol : ∀ᶠ w in 𝓝[≠] (0 : ℂ), F (0, w) ≠ 0 :=
    hF.curry_right.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun hzero ↦
      ENat.natCast_ne_top d (hF_ord.symm.trans (analyticOrderAt_eq_top.2 hzero))
  obtain ⟨r₁, hr₁, hball₁⟩ := Metric.mem_nhds_iff.1 ((isOpen_analyticAt ℂ F).mem_nhds hF)
  obtain ⟨r₂, hr₂, hball₂⟩ := Metric.mem_nhds_iff.1 (eventually_nhdsWithin_iff.1 hF_isol)
  set R : ℝ := min r₁ r₂ / 2
  have hR : 0 < R := half_pos (lt_min hr₁ hr₂)
  have hF0_an : ∀ w ∈ closedBall (0 : ℂ) R, AnalyticAt ℂ F (0, w) := fun w hw ↦
    hball₁ (by simp [Prod.dist_eq, (mem_closedBall_zero_iff.1 hw).trans_lt
      ((half_lt_self (lt_min hr₁ hr₂)).trans_le (min_le_left _ _))])
  have hF0_only : ∀ w ∈ closedBall (0 : ℂ) R, w ≠ 0 → F (0, w) ≠ 0 := fun w hw ↦
    hball₂ (mem_ball.2 ((mem_closedBall.1 hw).trans_lt
      ((half_lt_self (lt_min hr₁ hr₂)).trans_le (min_le_right _ _))))
  have hev_an : ∀ᶠ x in 𝓝 (0 : E), ∀ w ∈ closedBall (0 : ℂ) R, AnalyticAt ℂ F (x, w) :=
    (isCompact_closedBall (0 : ℂ) R).eventually_forall_of_forall_eventually fun w hw ↦
      (hF0_an w hw).eventually_analyticAt
  have hev_ne : ∀ᶠ x in 𝓝 (0 : E), ∀ ζ ∈ sphere (0 : ℂ) R, F (x, ζ) ≠ 0 :=
    (isCompact_sphere (0 : ℂ) R).eventually_forall_of_forall_eventually fun ζ hζ ↦
      (hF0_an ζ (sphere_subset_closedBall hζ)).continuousAt.eventually_ne
        (hF0_only ζ (sphere_subset_closedBall hζ) (ne_of_mem_sphere hζ hR.ne'))
  obtain ⟨δ, hδ, hδ_prop⟩ := Metric.mem_nhds_iff.1 (hev_an.and hev_ne)
  have hFx_an {x : E} (hx : x ∈ ball 0 δ) : AnalyticOnNhd ℂ (fun w ↦ F (x, w)) (closedBall 0 R) :=
    fun _ hw ↦ ((hδ_prop hx).1 _ hw).curry_right
  have hFx_sphere {x : E} (hx : x ∈ ball 0 δ) : ∀ ζ ∈ sphere 0 R, F (x, ζ) ≠ 0 := (hδ_prop hx).2
  classical
  let Z : E → Multiset ℂ := fun x ↦ if hx : x ∈ ball 0 δ then zeroMultiset (hFx_an hx) else 0
  have hZ_eq {x : E} (hx : x ∈ ball 0 δ) : Z x = zeroMultiset (hFx_an hx) := by
    dsimp only [Z]; split_ifs; rfl
  have hpow_int (k : ℕ) {x : E} (hx : x ∈ ball 0 δ) : ((Z x).map (· ^ k)).sum =
      (2 * π * I)⁻¹ * ∮ ζ in C(0, R), ζ ^ k * (fderiv ℂ F (x, ζ) (0, 1) / F (x, ζ)) := by
    rw [hZ_eq hx, sum_map_zeroMultiset_eq_circleIntegral hR (hFx_an hx) (hFx_sphere hx)
      (fun z _ ↦ by simpa using (analyticAt_id (𝕜 := ℂ) (z := z)).fun_pow k)]
    refine congrArg (_ * ·) (circleIntegral.integral_congr hR.le fun ζ hζ ↦ ?_)
    have hderiv : deriv (fun w ↦ F (x, w)) ζ = fderiv ℂ F (x, ζ) (0, 1) :=
      (((hδ_prop hx).1 ζ (sphere_subset_closedBall hζ)).differentiableAt.hasFDerivAt.comp_hasDerivAt
        ζ ((hasDerivAt_const ζ x).prodMk (hasDerivAt_id' ζ))).deriv
    rw [logDeriv_apply, hderiv]
  have hpow_an (k : ℕ) : AnalyticOnNhd ℂ (fun x ↦ ((Z x).map (· ^ k)).sum) (ball 0 δ) := by
    refine AnalyticOnNhd.congr isOpen_ball (fun x hx ↦ ?_) fun x hx ↦ (hpow_int k hx).symm
    refine analyticAt_const.fun_mul (TauCeti.analyticAt_circleIntegral
      (f := fun q : E × ℂ ↦ q.2 ^ k * (fderiv ℂ F q (0, 1) / F q)) fun ζ hζ ↦ ?_)
    rw [abs_of_pos hR] at hζ
    have hFp := (hδ_prop hx).1 ζ (sphere_subset_closedBall hζ)
    exact (analyticAt_snd.fun_pow k).fun_mul
      ((((ContinuousLinearMap.apply ℂ ℂ ((0 : E), (1 : ℂ))).analyticAt _).comp_of_eq
        hFp.fderiv rfl).fun_div hFp (hFx_sphere hx ζ hζ))
  have hZ0 : Z 0 = Multiset.replicate d 0 :=
    (hZ_eq (mem_ball_self hδ)).trans
      (zeroMultiset_eq_replicate_zero hR (hFx_an (mem_ball_self hδ)) hF_ord hF0_only)
  have hcard {x : E} (hx : x ∈ ball 0 δ) : (Z x).card = d := by
    have hcont : ContinuousOn (fun x ↦ (Z x).card) (ball 0 δ) :=
      Nat.isClosedEmbedding_coe_real.isInducing.continuousOn_iff.2
        ((Complex.continuous_re.comp_continuousOn (hpow_an 0).continuousOn).congr fun _ _ ↦ by simp)
    simpa [hZ0] using (convex_ball (0 : E) δ).isPreconnected.constant hcont hx (mem_ball_self hδ)
  let C_coeff : Fin d → E → ℂ := fun i x ↦ (-1) ^ (d - (i : ℕ)) * (Z x).esymm (d - (i : ℕ))
  have hC_an (i : Fin d) : AnalyticOnNhd ℂ (C_coeff i) (ball 0 δ) := fun x hx ↦
    analyticAt_const.fun_mul (TauCeti.analyticAt_esymm_of_forall_analyticAt_sum_map_pow _
      fun j _ _ ↦ hpow_an j x hx)
  have hC_zero (i : Fin d) : C_coeff i 0 = 0 := by
    have h := Multiset.prod_X_sub_C_coeff (Multiset.replicate d (0 : ℂ)) (k := (i : ℕ))
      (by simp [i.2.le])
    simpa [C_coeff, hZ0, coeff_X_pow, i.2.ne] using h.symm
  have hmonic_eq {x : E} (hx : x ∈ ball 0 δ) :
      TauCeti.Polynomial.monicOfCoeff (fun i ↦ C_coeff i x) =
        ((Z x).map (fun α ↦ X - C α)).prod := by
    rw [← TauCeti.Polynomial.monicOfCoeff_coeff
      (monic_multiset_prod_of_monic _ _ fun α _ ↦ monic_X_sub_C α)
      ((natDegree_multiset_prod_X_sub_C_eq_card _).trans (hcard hx))]
    exact congrArg _ (funext fun i ↦ by
      rw [Multiset.prod_X_sub_C_coeff (Z x) (by rw [hcard hx]; exact i.2.le), hcard hx])
  let U : E × ℂ → ℂ := fun p ↦ (2 * π * I)⁻¹ * ∮ ζ in C(0, R),
    (ζ - p.2)⁻¹ * (F (p.1, ζ) / (TauCeti.Polynomial.monicOfCoeff (fun i ↦ C_coeff i p.1)).eval ζ)
  have hU_an : AnalyticAt ℂ U (0, 0) := by
    refine analyticAt_const.fun_mul (TauCeti.analyticAt_circleIntegral
      (f := fun q : (E × ℂ) × ℂ ↦ (q.2 - q.1.2)⁻¹ *
        (F (q.1.1, q.2) / (TauCeti.Polynomial.monicOfCoeff (fun i ↦ C_coeff i q.1.1)).eval q.2))
      fun ζ hζ ↦ ?_)
    rw [abs_of_pos hR] at hζ
    have hζ0 := ne_of_mem_sphere hζ hR.ne'
    refine ((analyticAt_snd.fun_sub (analyticAt_snd.comp_of_eq analyticAt_fst rfl)).inv
      (sub_ne_zero.2 hζ0)).fun_mul (((hF0_an ζ (sphere_subset_closedBall hζ)).comp_of_eq
      ((analyticAt_fst.comp_of_eq analyticAt_fst rfl).prod analyticAt_snd) rfl).fun_div
      ((TauCeti.Polynomial.analyticAt_eval_monicOfCoeff _).comp
        ((AnalyticAt.pi fun i ↦ (hC_an i 0 (mem_ball_self hδ)).comp_of_eq
          (analyticAt_fst.comp_of_eq analyticAt_fst rfl) rfl).prod analyticAt_snd)) ?_)
    simp [TauCeti.Polynomial.eval_monicOfCoeff, hC_zero, pow_ne_zero d hζ0]
  have hFU_slice {x : E} (hx : x ∈ ball 0 δ) :
      (∀ w ∈ ball 0 R,
        F (x, w) = (TauCeti.Polynomial.monicOfCoeff (fun i ↦ C_coeff i x)).eval w * U (x, w)) ∧
      U (x, 0) ≠ 0 := by
    obtain ⟨u₀, _, hu₀_ne, hu₀_fac, hu₀_int⟩ :=
      exists_slice_weierstrassFactor hR (hFx_an hx) (hFx_sphere hx)
    have hU_eq {w : ℂ} (hw : w ∈ ball 0 R) : U (x, w) = u₀ w := by
      simp only [U, hmonic_eq hx, hZ_eq hx, ← hu₀_int w hw]
    exact ⟨fun w hw ↦ by
      rw [hU_eq hw, hmonic_eq hx, hZ_eq hx]; exact hu₀_fac w (ball_subset_closedBall hw),
      hU_eq (mem_ball_self hR) ▸ hu₀_ne 0 (mem_closedBall_self hR.le)⟩
  refine ⟨fun i x ↦ C_coeff i (x - x₀), fun p ↦ U (p.1 - x₀, p.2 - w₀),
    fun i ↦ (hC_an i 0 (mem_ball_self hδ)).comp_of_eq
      (analyticAt_id.fun_sub analyticAt_const) (sub_self x₀),
    fun i ↦ by simp [hC_zero i],
    hU_an.comp_of_eq ((analyticAt_fst.fun_sub analyticAt_const).prod
      (analyticAt_snd.fun_sub analyticAt_const)) (by simp),
    by simpa using (hFU_slice (mem_ball_self hδ)).2, ?_⟩
  filter_upwards [prod_mem_nhds (ball_mem_nhds x₀ hδ) (ball_mem_nhds w₀ hR)] with ⟨x, w⟩ ⟨hx, hw⟩
  have hx₀ : x₀ + (x - x₀) = x := by rw [add_comm, sub_add_cancel]
  have hw₀ : w₀ + (w - w₀) = w := by rw [add_comm, sub_add_cancel]
  have h := (hFU_slice (by simpa [dist_eq_norm] using mem_ball.1 hx)).1 (w - w₀)
    (by simpa [dist_eq_norm] using mem_ball.1 hw)
  simp_rw [F, hx₀, hw₀] at h
  exact h

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
  set G : E × ℂ → ℂ := fun p ↦ g (x₀ + p.1, w₀ + p.2)
  set C_coeff : Fin d → E → ℂ := fun i x ↦ c i (x₀ + x)
  have hG : AnalyticAt ℂ G (0, 0) :=
    hg.comp_of_eq ((analyticAt_const.fun_add analyticAt_fst).prod
      (analyticAt_const.fun_add analyticAt_snd)) (by simp)
  have hC (i : Fin d) : AnalyticAt ℂ (C_coeff i) 0 :=
    (hc i).comp_of_eq (analyticAt_const.fun_add analyticAt_id) (add_zero x₀)
  have hC0 (i : Fin d) : C_coeff i 0 = 0 := by simp [C_coeff, hc0 i]
  let P_eval : E → ℂ → ℂ := fun x ζ ↦ (TauCeti.Polynomial.monicOfCoeff (fun i ↦ C_coeff i x)).eval ζ
  obtain ⟨r₁, hr₁, hball₁⟩ := Metric.mem_nhds_iff.1 ((isOpen_analyticAt ℂ G).mem_nhds hG)
  set R : ℝ := r₁ / 2
  have hR : 0 < R := half_pos hr₁
  have hG0_an : ∀ w ∈ closedBall (0 : ℂ) R, AnalyticAt ℂ G (0, w) := fun w hw ↦
    hball₁ (by simp [Prod.dist_eq, (mem_closedBall_zero_iff.1 hw).trans_lt (half_lt_self hr₁)])
  have hP_an0 (ζ : ℂ) : AnalyticAt ℂ (fun p : E × ℂ ↦ P_eval p.1 p.2) (0, ζ) :=
    (TauCeti.Polynomial.analyticAt_eval_monicOfCoeff _).comp
      ((AnalyticAt.pi fun i ↦ (hC i).comp_of_eq analyticAt_fst rfl).prod analyticAt_snd)
  have hP0_sphere {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) R) : P_eval 0 ζ ≠ 0 := by
    simp [P_eval, TauCeti.Polynomial.eval_monicOfCoeff, hC0,
      pow_ne_zero d (ne_of_mem_sphere hζ hR.ne')]
  have hev_G : ∀ᶠ x in 𝓝 (0 : E), ∀ w ∈ closedBall (0 : ℂ) R, AnalyticAt ℂ G (x, w) :=
    (isCompact_closedBall (0 : ℂ) R).eventually_forall_of_forall_eventually fun w hw ↦
      (hG0_an w hw).eventually_analyticAt
  have hev_P : ∀ᶠ x in 𝓝 (0 : E), ∀ ζ ∈ sphere (0 : ℂ) R, P_eval x ζ ≠ 0 :=
    (isCompact_sphere (0 : ℂ) R).eventually_forall_of_forall_eventually fun ζ hζ ↦
      (hP_an0 ζ).continuousAt.eventually_ne (hP0_sphere hζ)
  obtain ⟨δ, hδ, hδ_prop⟩ := Metric.mem_nhds_iff.1 (hev_G.and hev_P)
  let Q : E × ℂ → ℂ := fun p ↦
    (2 * π * I)⁻¹ * ∮ ζ in C(0, R), (ζ - p.2)⁻¹ * (G (p.1, ζ) / P_eval p.1 ζ)
  let r_coeff : Fin d → E → ℂ := fun k x ↦
    (2 * π * I)⁻¹ * ∮ ζ in C(0, R),
      divKernelCoeff (fun i ↦ C_coeff i x) k ζ * (G (x, ζ) / P_eval x ζ)
  have hQ_an : AnalyticAt ℂ Q (0, 0) := by
    refine analyticAt_const.fun_mul (TauCeti.analyticAt_circleIntegral
      (f := fun q : (E × ℂ) × ℂ ↦ (q.2 - q.1.2)⁻¹ * (G (q.1.1, q.2) / P_eval q.1.1 q.2))
      fun ζ hζ ↦ ?_)
    rw [abs_of_pos hR] at hζ
    exact ((analyticAt_snd.fun_sub (analyticAt_snd.comp_of_eq analyticAt_fst rfl)).inv
      (sub_ne_zero.2 (ne_of_mem_sphere hζ hR.ne'))).fun_mul
      (((hG0_an ζ (sphere_subset_closedBall hζ)).comp_of_eq
        ((analyticAt_fst.comp_of_eq analyticAt_fst rfl).prod analyticAt_snd) rfl).fun_div
        ((hP_an0 ζ).comp_of_eq
          ((analyticAt_fst.comp_of_eq analyticAt_fst rfl).prod analyticAt_snd) rfl)
        (hP0_sphere hζ))
  have hr_an (k : Fin d) : AnalyticAt ℂ (r_coeff k) 0 := by
    refine analyticAt_const.fun_mul (TauCeti.analyticAt_circleIntegral
      (f := fun q : E × ℂ ↦
        divKernelCoeff (fun i ↦ C_coeff i q.1) k q.2 * (G (q.1, q.2) / P_eval q.1 q.2))
      fun ζ hζ ↦ ?_)
    rw [abs_of_pos hR] at hζ
    have hker : AnalyticAt ℂ (fun q : E × ℂ ↦ divKernelCoeff (fun i ↦ C_coeff i q.1) k q.2)
        (0, ζ) := by
      simp only [divKernelCoeff]
      refine (analyticAt_snd.fun_pow _).fun_add (Finset.analyticAt_fun_sum _ fun i _ ↦ ?_)
      split_ifs
      · exact ((hC i).comp_of_eq analyticAt_fst rfl).fun_mul (analyticAt_snd.fun_pow _)
      · exact analyticAt_const
    exact hker.fun_mul
      ((hG0_an ζ (sphere_subset_closedBall hζ)).fun_div (hP_an0 ζ) (hP0_sphere hζ))
  have hdiv_eq {x : E} (hx : x ∈ ball 0 δ) {w : ℂ} (hw : w ∈ ball 0 R) :
      G (x, w) = P_eval x w * Q (x, w) + ∑ k : Fin d, r_coeff k x * w ^ (k : ℕ) := by
    obtain ⟨hGx_an, hPx_ne⟩ := hδ_prop hx
    have hGx_slice : AnalyticOnNhd ℂ (fun ζ ↦ G (x, ζ)) (closedBall 0 R) :=
      fun _ hζ ↦ (hGx_an _ hζ).curry_right
    have hcauchy := hGx_slice.differentiableOn.circleIntegral_sub_inv_smul hw
    simp only [smul_eq_mul] at hcauchy
    have hP_cont : ContinuousOn (fun ζ ↦ P_eval x ζ) (sphere 0 R) := by
      simp only [P_eval, TauCeti.Polynomial.eval_monicOfCoeff]; fun_prop
    have hquot_cont : ContinuousOn (fun ζ ↦ G (x, ζ) / P_eval x ζ) (sphere 0 R) :=
      (hGx_slice.continuousOn.mono sphere_subset_closedBall).div hP_cont hPx_ne
    have hzw_ne : ∀ ζ ∈ sphere 0 R, ζ - w ≠ 0 := fun ζ hζ ↦
      sub_ne_zero.2 fun h ↦ (mem_ball.1 hw).ne (h ▸ mem_sphere.1 hζ)
    have hint1 : CircleIntegrable
        (fun ζ ↦ P_eval x w * ((ζ - w)⁻¹ * (G (x, ζ) / P_eval x ζ))) 0 R :=
      (continuousOn_const.mul
        (((continuousOn_id.sub continuousOn_const).inv₀ hzw_ne).mul hquot_cont)).circleIntegrable
        hR.le
    have hint_k (k : Fin d) : CircleIntegrable
        (fun ζ ↦ w ^ (k : ℕ) * (divKernelCoeff (fun i ↦ C_coeff i x) k ζ *
          (G (x, ζ) / P_eval x ζ))) 0 R := by
      have hker_cont : ContinuousOn
          (fun ζ ↦ divKernelCoeff (fun i ↦ C_coeff i x) k ζ) (sphere 0 R) := by
        simp only [divKernelCoeff]
        refine (continuousOn_id.pow _).add (continuousOn_finsetSum _ fun i _ ↦ ?_)
        split_ifs
        · exact continuousOn_const.mul (continuousOn_id.pow _)
        · exact continuousOn_const
      exact (continuousOn_const.mul (hker_cont.mul hquot_cont)).circleIntegrable hR.le
    have hpointwise : ∀ ζ ∈ sphere 0 R,
        (ζ - w)⁻¹ * G (x, ζ) =
          P_eval x w * ((ζ - w)⁻¹ * (G (x, ζ) / P_eval x ζ)) +
            ∑ k : Fin d, w ^ (k : ℕ) * (divKernelCoeff (fun i ↦ C_coeff i x) k ζ *
              (G (x, ζ) / P_eval x ζ)) := by
      intro ζ hζ
      have hdiff := sub_mul_sum_divKernelCoeff (fun i ↦ C_coeff i x) ζ w
      have hPζ : P_eval x ζ ≠ 0 := hPx_ne ζ hζ
      have hζw : ζ - w ≠ 0 := hzw_ne ζ hζ
      have hsum_rw : ∑ k : Fin d, w ^ (k : ℕ) * (divKernelCoeff (fun i ↦ C_coeff i x) k ζ *
          (G (x, ζ) / P_eval x ζ)) =
          (G (x, ζ) / P_eval x ζ) *
            ∑ k : Fin d, divKernelCoeff (fun i ↦ C_coeff i x) k ζ * w ^ (k : ℕ) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ ↦ by ring
      rw [hsum_rw]
      field_simp
      dsimp only [P_eval]
      linear_combination -G (x, ζ) * hdiff
    have hint_eq := circleIntegral.integral_congr hR.le hpointwise
    rw [circleIntegral.integral_add hint1 (CircleIntegrable.fun_sum Finset.univ fun k _ ↦ hint_k k),
      circleIntegral.integral_const_mul, circleIntegral.integral_fun_sum fun k _ ↦ hint_k k]
      at hint_eq
    have hsum_int : ∑ k : Fin d, (2 * π * I)⁻¹ *
        (∮ ζ in C(0, R), w ^ (k : ℕ) * (divKernelCoeff (fun i ↦ C_coeff i x) k ζ *
          (G (x, ζ) / P_eval x ζ))) = ∑ k : Fin d, r_coeff k x * w ^ (k : ℕ) :=
      Finset.sum_congr rfl fun k _ ↦ by simp only [r_coeff, circleIntegral.integral_const_mul]; ring
    rw [← inv_mul_cancel_left₀ two_pi_I_ne_zero (G (x, w)), ← hcauchy, hint_eq, mul_add,
      ← mul_left_comm (P_eval x w), Finset.mul_sum, hsum_int]
  refine ⟨fun p ↦ Q (p.1 - x₀, p.2 - w₀), fun k x ↦ r_coeff k (x - x₀),
    hQ_an.comp_of_eq ((analyticAt_fst.fun_sub analyticAt_const).prod
      (analyticAt_snd.fun_sub analyticAt_const)) (by simp),
    fun k ↦ (hr_an k).comp_of_eq (analyticAt_id.fun_sub analyticAt_const) (sub_self x₀), ?_⟩
  filter_upwards [prod_mem_nhds (ball_mem_nhds x₀ hδ) (ball_mem_nhds w₀ hR)] with ⟨x, w⟩ ⟨hx, hw⟩
  have hx₀ : x₀ + (x - x₀) = x := by rw [add_comm, sub_add_cancel]
  have hw₀ : w₀ + (w - w₀) = w := by rw [add_comm, sub_add_cancel]
  have h := hdiv_eq (by simpa [dist_eq_norm] using mem_ball.1 hx)
    (by simpa [dist_eq_norm] using mem_ball.1 hw)
  simp_rw [G, P_eval, C_coeff, hx₀, hw₀] at h
  exact h

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
