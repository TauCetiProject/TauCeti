/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.FactorOrder
public import Mathlib.RingTheory.Polynomial.IntegralNormalization

/-!
# Laurent forms of nonmonic polynomial roots

For a nonmonic polynomial family, multiplying roots by the leading coefficient gives roots
of its integral normalization. Suppose these rescaled roots extend analytically across a
distinguished hyperplane. If both the leading and constant coefficients are powers of the
distinguished variable times analytic units, each original root is a Laurent power times an
analytic unit. The exponent is independent of the other parameters, so the possibility of a
pole does not vary with them.

The constant coefficient hypothesis is essential: for `y * X - x`, the rescaled root is `x`,
which has no such unit form near `(0, 0)`. The theorem below extracts the Laurent forms from
an already supplied analytic splitting of the normalized family; it does not construct that
splitting or the power substitution that produces it. Repeated roots are allowed.
The leading coefficient is the coefficient at the fixed punctured-fiber degree; the degree
may drop on the hyperplane.

## References

* S. McCallum, A. Parusiński, L. Paunescu,
  [Validity proof of Lazard's method for CAD construction](https://arxiv.org/abs/1607.00264),
  J. Symbolic Comput. 92 (2019), §4, proof of Corollary 4.2.
-/

public section

open Filter Polynomial Set Topology

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The product of analytically extended normalized roots is a centered power times a unit.
The identity is initially supplied only off the distinguished hyperplane, where the degree
of the original family is fixed. -/
private theorem eventually_prod_normalized_roots_eq {d a c : ℕ} (hd : 0 < d)
    {P : E × 𝕜 → Polynomial 𝕜} {s : Fin d → E × 𝕜 → 𝕜} {x₀ : E} {y₀ : 𝕜}
    {u v : E × 𝕜 → 𝕜} (hs : ∀ i, AnalyticAt 𝕜 (s i) (x₀, y₀))
    (hu : AnalyticAt 𝕜 u (x₀, y₀)) (hv : AnalyticAt 𝕜 v (x₀, y₀))
    (hnorm : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ →
      (P p).integralNormalization = ∏ i, (X - C (s i p)))
    (hlead : ∀ᶠ p in 𝓝 (x₀, y₀), (P p).coeff d = (p.2 - y₀) ^ c * v p)
    (hconst : ∀ᶠ p in 𝓝 (x₀, y₀), (P p).coeff 0 = (p.2 - y₀) ^ a * u p) :
    ∀ᶠ p in 𝓝 (x₀, y₀),
      ∏ i, s i p = (p.2 - y₀) ^ (a + c * (d - 1)) *
        ((-1 : 𝕜) ^ d * u p * v p ^ (d - 1)) := by
  classical
  let G : E × 𝕜 → 𝕜 := fun p ↦ ∏ i, s i p
  let H : E × 𝕜 → 𝕜 := fun p ↦ (p.2 - y₀) ^ (a + c * (d - 1)) *
    ((-1 : 𝕜) ^ d * u p * v p ^ (d - 1))
  have hG : AnalyticAt 𝕜 G (x₀, y₀) := by
    simpa only [G, Finset.prod_fn] using Finset.analyticAt_prod _ (fun i _ ↦ hs i)
  have hH : AnalyticAt 𝕜 H (x₀, y₀) :=
    ((analyticAt_snd.sub analyticAt_const).fun_pow _).mul
      ((analyticAt_const.mul hu).mul (hv.fun_pow _))
  have heq : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ → G p = H p := by
    filter_upwards [hnorm, hlead, hconst] with p hnp hlp hcp hp
    have hdegree : (P p).natDegree = d := by
      simpa only [natDegree_integralNormalization, natDegree_finsetProd_X_sub_C_eq_card,
        Finset.card_univ, Fintype.card_fin] using congrArg natDegree (hnp hp)
    have hc := congrArg (fun f : Polynomial 𝕜 ↦ f.coeff 0) (hnp hp)
    rw [integralNormalization_coeff_ne_natDegree (by omega : 0 ≠ (P p).natDegree),
      hdegree] at hc
    simp only [Nat.sub_zero, coeff_zero_prod, coeff_sub, coeff_X_zero, coeff_C_zero,
      zero_sub, Finset.prod_neg, Finset.card_univ, Fintype.card_fin] at hc
    have hsign : ((-1 : 𝕜) ^ d) * (-1) ^ d = 1 := by
      rw [← mul_pow]
      simp
    have hprod : G p = (-1 : 𝕜) ^ d * ((P p).coeff 0 * (P p).leadingCoeff ^ (d - 1)) := by
      rw [hc, ← mul_assoc, hsign, one_mul]
    rw [hprod, leadingCoeff, hdegree, hlp, hcp]
    simp only [H, mul_pow, pow_add, pow_mul]
    ring
  -- Continuity extends the coefficient identity across the hyperplane, even
  -- though integral normalization itself need not be continuous there.
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp
    (heq.and (hG.eventually_analyticAt.and hH.eventually_analyticAt))
  have hUeq : EqOn G H (U ∩ (univ ×ˢ ({y₀}ᶜ : Set 𝕜))) :=
    fun p hp ↦ (hUsub hp.1).1 hp.2.2
  have hclosure := (dense_univ.prod (dense_compl_singleton y₀)).open_subset_closure_inter hU
  have heqU := hUeq.of_subset_closure
    (fun p hp ↦ (hUsub hp).2.1.continuousAt.continuousWithinAt)
    (fun p hp ↦ (hUsub hp).2.2.continuousAt.continuousWithinAt)
    inter_subset_left hclosure
  exact Filter.mem_of_superset (hU.mem_nhds hpU) heqU

/-- **Laurent unit forms of nonmonic roots.** Suppose the leading and constant coefficients
of a positive-degree family are centered powers times analytic units. Given an analytic
extension `s` of the leading-coefficient multiples of a complete list `r` of roots, expressed
by a splitting of the integral normalization off the hyperplane, each `r i` is locally
`(y - y₀) ^ (m i - c) * w i`, where `m i` is natural and `w i` is an analytic unit.

The exponent `c` is that of the leading coefficient. The Laurent equality holds off the
hyperplane, on one common neighborhood for every label. The units are nonzero on that
neighborhood, including on the hyperplane. No analyticity of the original roots at a pole
is assumed, and no simplicity assumption is imposed. -/
theorem exists_root_eq_zpow_mul_unit {d a c : ℕ} (hd : 0 < d)
    {P : E × 𝕜 → Polynomial 𝕜} {r s : Fin d → E × 𝕜 → 𝕜} {x₀ : E} {y₀ : 𝕜}
    {u v : E × 𝕜 → 𝕜} (hs : ∀ i, AnalyticAt 𝕜 (s i) (x₀, y₀))
    (hu : AnalyticAt 𝕜 u (x₀, y₀)) (hu0 : u (x₀, y₀) ≠ 0)
    (hv : AnalyticAt 𝕜 v (x₀, y₀)) (hv0 : v (x₀, y₀) ≠ 0)
    (hnorm : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ →
      (P p).integralNormalization = ∏ i, (X - C (s i p)))
    (hlead : ∀ᶠ p in 𝓝 (x₀, y₀), (P p).coeff d = (p.2 - y₀) ^ c * v p)
    (hconst : ∀ᶠ p in 𝓝 (x₀, y₀), (P p).coeff 0 = (p.2 - y₀) ^ a * u p)
    (hscale : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ →
      ∀ i, (P p).coeff d * r i p = s i p) :
    ∃ m : Fin d → ℕ, ∃ w : Fin d → E × 𝕜 → 𝕜,
      (∀ i, AnalyticAt 𝕜 (w i) (x₀, y₀)) ∧
      (∀ i, w i (x₀, y₀) ≠ 0) ∧
      ∀ᶠ p in 𝓝 (x₀, y₀), (∀ i, w i p ≠ 0) ∧
        (p.2 ≠ y₀ → ∀ i, r i p = (p.2 - y₀) ^ ((m i : ℤ) - c) * w i p) := by
  classical
  let U : E × 𝕜 → 𝕜 := fun p ↦ (-1 : 𝕜) ^ d * u p * v p ^ (d - 1)
  have hU : AnalyticAt 𝕜 U (x₀, y₀) := (analyticAt_const.mul hu).mul (hv.fun_pow _)
  have hU0 : U (x₀, y₀) ≠ 0 := mul_ne_zero (mul_ne_zero (by simp) hu0) (pow_ne_zero _ hv0)
  have hprod := eventually_prod_normalized_roots_eq hd hs hu hv hnorm hlead hconst
  have hG : AnalyticAt 𝕜 (fun p ↦ ∏ i, s i p) (x₀, y₀) := by
    simpa only [Finset.prod_fn] using Finset.analyticAt_prod _ (fun i _ ↦ hs i)
  have horder := hG.eventually_analyticOrderAt_eq_natCast_iff.mpr
    ⟨U, hU, hU0, by simpa only [smul_eq_mul] using hprod⟩
  have hfactor := exists_factor_eq_pow_mul_unit (fun i _ ↦ hs i) horder
  have hchoices := fun i : Fin d ↦ hfactor i (Finset.mem_univ i)
  choose m V hV hV0 heq using hchoices
  let w : Fin d → E × 𝕜 → 𝕜 := fun i p ↦ V i p / v p
  have hw : ∀ i, AnalyticAt 𝕜 (w i) (x₀, y₀) := fun i ↦ (hV i).div hv hv0
  have hw0 : ∀ i, w i (x₀, y₀) ≠ 0 := fun i ↦ div_ne_zero (hV0 i) hv0
  have hwne : ∀ᶠ p in 𝓝 (x₀, y₀), ∀ i, w i p ≠ 0 := by
    rw [eventually_all]
    exact fun i ↦ (hw i).continuousAt.eventually_ne (hw0 i)
  have heqall : ∀ᶠ p in 𝓝 (x₀, y₀), ∀ i, s i p = (p.2 - y₀) ^ m i * V i p := by
    rw [eventually_all]
    exact heq
  refine ⟨m, w, hw, hw0, ?_⟩
  filter_upwards [hwne, heqall, hlead, hscale, hv.continuousAt.eventually_ne hv0]
    with p hwp hep hlp hsp hvp
  refine ⟨hwp, fun hp i ↦ ?_⟩
  have ht : p.2 - y₀ ≠ 0 := sub_ne_zero.mpr hp
  have hl : (P p).coeff d ≠ 0 := hlp ▸ mul_ne_zero (pow_ne_zero _ ht) hvp
  have hr : r i p = s i p / (P p).coeff d := (eq_div_iff hl).mpr (by
    simpa only [mul_comm] using hsp hp i)
  rw [hr, hep i, hlp, zpow_natCast_sub_natCast₀ ht]
  simp only [w]
  ring

end TauCeti
