/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Puiseux.RootDifference.Basic
public import TauCeti.RingTheory.Polynomial.Resultant.Normalization

/-!
# Laurent unit forms of nonmonic root differences

Let the leading coefficient and discriminant of a nonmonic polynomial family be centered
powers of a distinguished variable times analytic units. If its leading-coefficient-scaled
roots extend analytically across the distinguished hyperplane, every difference of distinct
root labels is a Laurent power times an analytic unit. The exponent is independent of the
other parameters. Negative exponents permit poles; positive exponents permit collisions.

The normalized roots are supplied by a splitting of the integral normalization off the
hyperplane. No splitting of the original family on the hyperplane is required, where its
degree may drop or it may be nullified. Parameter-independent orders of root differences are
used in analytic preparation of nonmonic polynomial families, including those whose branches
have poles.
The original coefficient and discriminant formulas are required only off the hyperplane:
recomputing a discriminant after a degree drop need not preserve the formal discriminant. No
constant-coefficient hypothesis is needed for differences.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, J. Symbolic Comput. 92 (2019), §4, Corollary 4.2.
-/

public section

open Filter Polynomial Set Topology

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The discriminant of the analytic normalized splitting retains its power-times-unit form
on the hyperplane, even when the original family's degree drops there. -/
private theorem eventually_discr_normalized_splitting_eq {d a c : ℕ}
    {P : E × 𝕜 → Polynomial 𝕜} {s : Fin d → E × 𝕜 → 𝕜} {x₀ : E} {y₀ : 𝕜}
    {u v : E × 𝕜 → 𝕜} (hs : ∀ i, AnalyticAt 𝕜 (s i) (x₀, y₀))
    (hu : AnalyticAt 𝕜 u (x₀, y₀)) (hv : AnalyticAt 𝕜 v (x₀, y₀))
    (hnorm : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ →
      (P p).integralNormalization = ∏ i, (X - C (s i p)))
    (hlead : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ →
      (P p).coeff d = (p.2 - y₀) ^ c * v p)
    (hdiscr : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ →
      (P p).discr = (p.2 - y₀) ^ a * u p) :
    ∀ᶠ p in 𝓝 (x₀, y₀),
      (∏ i, (X - C (s i p))).discr =
        (p.2 - y₀) ^ (c * ((d - 1) * (d - 2)) + a) *
          (v p ^ ((d - 1) * (d - 2)) * u p) := by
  classical
  let G : E × 𝕜 → 𝕜 := fun p ↦ (∏ i, (X - C (s i p))).discr
  let H : E × 𝕜 → 𝕜 := fun p ↦
    (p.2 - y₀) ^ (c * ((d - 1) * (d - 2)) + a) *
      (v p ^ ((d - 1) * (d - 2)) * u p)
  have hG : AnalyticAt 𝕜 G (x₀, y₀) := by
    simp only [G, discr_prod_X_sub_C]
    simpa only [Finset.prod_fn, Pi.sub_apply] using
      Finset.analyticAt_prod Finset.univ (fun i _ ↦
        Finset.analyticAt_prod (Finset.Ioi i) fun j _ ↦ ((hs i).sub (hs j)).fun_pow 2)
  have hH : AnalyticAt 𝕜 H (x₀, y₀) :=
    ((analyticAt_snd.sub analyticAt_const).fun_pow _).mul ((hv.fun_pow _).mul hu)
  have heq : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ → G p = H p := by
    filter_upwards [hnorm, hlead, hdiscr] with p hnp hlp hdp hp
    have hdegree : (P p).natDegree = d := by
      simpa only [natDegree_integralNormalization, natDegree_finsetProd_X_sub_C_eq_card,
        Finset.card_univ, Fintype.card_fin] using congrArg natDegree (hnp hp)
    dsimp only [G, H]
    rw [← hnp hp, discr_integralNormalization, leadingCoeff, hdegree, hlp hp, hdp hp]
    simp only [mul_pow, pow_mul, pow_add]
    ring
  -- Extend the scalar discriminant identity, rather than the discontinuous integral
  -- normalization operation, from the dense complement of the hyperplane.
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp
    (heq.and (hG.eventually_analyticAt.and hH.eventually_analyticAt))
  have hUeq : EqOn G H (U ∩ (univ ×ˢ ({y₀}ᶜ : Set 𝕜))) :=
    fun p hp ↦ (hUsub hp.1).1 hp.2.2
  have heqU := hUeq.of_subset_closure
    (fun p hp ↦ (hUsub hp).2.1.continuousAt.continuousWithinAt)
    (fun p hp ↦ (hUsub hp).2.2.continuousAt.continuousWithinAt)
    inter_subset_left ((dense_univ.prod (dense_compl_singleton y₀)).open_subset_closure_inter hU)
  exact Filter.mem_of_superset (hU.mem_nhds hpU) heqU

/-- Differences of nonmonic root branches are Laurent powers times analytic units when the
leading coefficient and discriminant are centered powers times analytic units. The scaled
roots `s i` must extend analytically and split the integral normalization off the hyperplane.
Only the selected pair of original roots must satisfy the scaling identities, and they may
have poles there. The exponent is constant in the parameters, and the unit is nonzero on a
neighborhood including the hyperplane. -/
theorem exists_root_sub_eq_zpow_mul_unit {d a c : ℕ}
    {P : E × 𝕜 → Polynomial 𝕜} {r s : Fin d → E × 𝕜 → 𝕜} {x₀ : E} {y₀ : 𝕜}
    {u v : E × 𝕜 → 𝕜} (hs : ∀ i, AnalyticAt 𝕜 (s i) (x₀, y₀))
    (hu : AnalyticAt 𝕜 u (x₀, y₀)) (hu0 : u (x₀, y₀) ≠ 0)
    (hv : AnalyticAt 𝕜 v (x₀, y₀)) (hv0 : v (x₀, y₀) ≠ 0)
    (hnorm : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ →
      (P p).integralNormalization = ∏ i, (X - C (s i p)))
    (hlead : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ →
      (P p).coeff d = (p.2 - y₀) ^ c * v p)
    (hdiscr : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ →
      (P p).discr = (p.2 - y₀) ^ a * u p)
    {i j : Fin d} (hscale : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ →
      (P p).coeff d * r i p = s i p ∧ (P p).coeff d * r j p = s j p)
    (hij : i ≠ j) :
    ∃ b : ℤ, ∃ w : E × 𝕜 → 𝕜,
      AnalyticAt 𝕜 w (x₀, y₀) ∧ w (x₀, y₀) ≠ 0 ∧
        ∀ᶠ p in 𝓝 (x₀, y₀), w p ≠ 0 ∧
          (p.2 ≠ y₀ → r i p - r j p = (p.2 - y₀) ^ b * w p) := by
  let U : E × 𝕜 → 𝕜 := fun p ↦ v p ^ ((d - 1) * (d - 2)) * u p
  have hU : AnalyticAt 𝕜 U (x₀, y₀) := (hv.fun_pow _).mul hu
  have hU0 : U (x₀, y₀) ≠ 0 := mul_ne_zero (pow_ne_zero _ hv0) hu0
  have hD := eventually_discr_normalized_splitting_eq hs hu hv hnorm hlead hdiscr
  obtain ⟨m, V, hV, hV0, heq⟩ := exists_root_sub_eq_pow_mul_unit hs
    (Filter.Eventually.of_forall fun _ ↦ rfl) hU hU0 hD hij
  let w : E × 𝕜 → 𝕜 := fun p ↦ V p / v p
  have hw : AnalyticAt 𝕜 w (x₀, y₀) := hV.div hv hv0
  have hw0 : w (x₀, y₀) ≠ 0 := div_ne_zero hV0 hv0
  refine ⟨(m : ℤ) - c, w, hw, hw0, ?_⟩
  filter_upwards [heq, hlead, hscale, hv.continuousAt.eventually_ne hv0,
    hw.continuousAt.eventually_ne hw0] with p hep hlp hsp hvp hwp
  refine ⟨hwp, fun hp ↦ ?_⟩
  have ht : p.2 - y₀ ≠ 0 := sub_ne_zero.mpr hp
  have hl : (P p).coeff d ≠ 0 := hlp hp ▸ mul_ne_zero (pow_ne_zero _ ht) hvp
  have hscaled : (P p).coeff d * (r i p - r j p) = s i p - s j p := by
    rw [mul_sub, (hsp hp).1, (hsp hp).2]
  have hr : r i p - r j p = (s i p - s j p) / (P p).coeff d :=
    (eq_div_iff hl).mpr (by simpa only [mul_comm] using hscaled)
  rw [hr, hep, hlp hp, zpow_natCast_sub_natCast₀ ht]
  simp only [w]
  ring

end TauCeti
