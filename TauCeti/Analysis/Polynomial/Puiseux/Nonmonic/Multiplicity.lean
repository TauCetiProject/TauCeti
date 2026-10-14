/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Roots
public import TauCeti.Analysis.Analytic.ConstantOrder.Laurent
public import TauCeti.Analysis.Analytic.Laurent.Hyperplane
public import TauCeti.Analysis.Polynomial.Puiseux.RootDifference.Nonmonic

/-!
# Collisions and multiplicities of finite nonmonic branches

Suppose a nonmonic polynomial family's leading coefficient and discriminant are powers of
a distinguished coordinate times analytic units, and its normalized roots extend
analytically. Any two original branches that extend analytically have locally constant
contact order, and hence locally persistent collisions, on the exceptional hyperplane.
Collision persistence also holds for independent analytic extensions of selected labels.
Other branches may have poles there.

For Laurent branches, the nonnegative-exponent labels have explicit analytic extensions.
If a polynomial's root multiset consists of their finite limits, its multiplicity at each
labelled limit is locally constant. In particular this applies to the root multisets of
Lazard evaluations identified by `MvPolynomial.roots_lazardEval_eq_map_of_laurent`.
Repeated finite limits and an empty set of finite branches are allowed. No preservation of
the original central fiber's degree, or nonnullification of that fiber, is required.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), §5.2, proof of Theorem 5.1.
-/

public section

open Filter Polynomial Set Topology

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {d a c : ℕ} {P : E × 𝕜 → Polynomial 𝕜} {r s : Fin d → E × 𝕜 → 𝕜}
  {x₀ : E} {y₀ : 𝕜} {u v : E × 𝕜 → 𝕜}

/-- Two finite analytic branches of a nonmonic splitting have locally constant contact
order on the exceptional hyperplane. Only the selected branches need analytic extensions;
the other original branches may have poles. -/
theorem eventually_analyticOrderAt_finite_root_sub_eq
    (hs : ∀ i, AnalyticAt 𝕜 (s i) (x₀, y₀))
    (hu : AnalyticAt 𝕜 u (x₀, y₀)) (hu0 : u (x₀, y₀) ≠ 0)
    (hv : AnalyticAt 𝕜 v (x₀, y₀)) (hv0 : v (x₀, y₀) ≠ 0)
    (hnorm : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ →
      (P p).integralNormalization = ∏ i, (X - C (s i p)))
    (hlead : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ →
      (P p).coeff d = (p.2 - y₀) ^ c * v p)
    (hdiscr : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ →
      (P p).discr = (p.2 - y₀) ^ a * u p)
    (i j : Fin d) (hi : AnalyticAt 𝕜 (r i) (x₀, y₀))
    (hj : AnalyticAt 𝕜 (r j) (x₀, y₀))
    (hscale : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ →
      (P p).coeff d * r i p = s i p ∧ (P p).coeff d * r j p = s j p) :
    ∀ᶠ x in 𝓝 x₀, analyticOrderAt (fun y ↦ r i (x, y) - r j (x, y)) y₀ =
      analyticOrderAt (fun y ↦ r i (x₀, y) - r j (x₀, y)) y₀ := by
  obtain rfl | hij := eq_or_ne i j
  · simp
  obtain ⟨b, w, hw, hw0, heq⟩ :=
    exists_root_sub_eq_zpow_mul_unit hs hu hu0 hv hv0 hnorm hlead hdiscr hscale hij
  exact (hi.sub hj).eventually_analyticOrderAt_eq_of_zpow_smul_unit hw hw0
    (heq.mono fun p hp ↦ by simpa only [smul_eq_mul, Pi.sub_apply] using hp.2)

/-- Coincidence of two finite analytic extensions of nonmonic root labels is locally
constant on the exceptional hyperplane. Only the chosen branches must have finite
extensions; all other labels may have poles and central fibers may be nullified. -/
theorem eventually_finite_root_eq_iff_on_hyperplane
    (hs : ∀ i, AnalyticAt 𝕜 (s i) (x₀, y₀))
    (hu : AnalyticAt 𝕜 u (x₀, y₀)) (hu0 : u (x₀, y₀) ≠ 0)
    (hv : AnalyticAt 𝕜 v (x₀, y₀)) (hv0 : v (x₀, y₀) ≠ 0)
    (hnorm : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ →
      (P p).integralNormalization = ∏ i, (X - C (s i p)))
    (hlead : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ → (P p).coeff d = (p.2 - y₀) ^ c * v p)
    (hdiscr : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ → (P p).discr = (p.2 - y₀) ^ a * u p)
    (i j : Fin d)
    {f g : E × 𝕜 → 𝕜} (hf : AnalyticAt 𝕜 f (x₀, y₀))
    (hg : AnalyticAt 𝕜 g (x₀, y₀))
    (hscale : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ →
      (P p).coeff d * f p = s i p ∧ (P p).coeff d * g p = s j p) :
    ∀ᶠ x in 𝓝 x₀, f (x, y₀) = g (x, y₀) ↔ f (x₀, y₀) = g (x₀, y₀) := by
  have hslice : Tendsto (fun x : E ↦ (x, y₀)) (𝓝 x₀) (𝓝 (x₀, y₀)) :=
    continuousAt_id.prodMk continuousAt_const
  rcases eq_or_ne i j with rfl | hij
  · -- The two finite extensions of the same label agree off the hyperplane.
    have heq : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ → f p = g p := by
      filter_upwards [hscale, hlead, hv.continuousAt.eventually_ne hv0] with p hp hl hvp hp0
      have hl0 : (P p).coeff d ≠ 0 :=
        hl hp0 ▸ mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hp0)) hvp
      exact mul_left_cancel₀ hl0 ((hp hp0).1.trans (hp hp0).2.symm)
    have hfull := (dense_univ.prod (dense_compl_singleton y₀)).eventuallyEq_nhds
      hf.eventually_continuousAt hg.eventually_continuousAt
      (eventually_nhdsWithin_iff.mpr (by simpa using heq))
    filter_upwards [hslice.eventually hfull] with x hx
    exact iff_of_true hx hfull.self_of_nhds
  -- The difference theorem only uses the two selected unscaled branches.
  let r : Fin d → E × 𝕜 → 𝕜 := fun k ↦ if k = i then f else g
  have hr : r i = f ∧ r j = g := by simp [r, hij.symm]
  have hord := eventually_analyticOrderAt_finite_root_sub_eq (r := r) hs hu hu0 hv hv0
    hnorm hlead hdiscr i j
    (by simpa only [hr.1] using hf) (by simpa only [hr.2] using hg)
    (by simpa only [hr.1, hr.2] using hscale)
  simp only [hr.1, hr.2] at hord
  filter_upwards [hord, hf.eventually_analyticAt_curry_right,
    hg.eventually_analyticAt_curry_right] with x hx hfx hgx
  have hA : AnalyticAt 𝕜 (fun y ↦ f (x, y) - g (x, y)) y₀ := hfx.sub hgx
  have hA₀ : AnalyticAt 𝕜 (fun y ↦ f (x₀, y) - g (x₀, y)) y₀ :=
    hf.curry_right.sub hg.curry_right
  simpa only [hA.analyticOrderAt_ne_zero, hA₀.analyticOrderAt_ne_zero,
    sub_eq_zero] using (congrArg (· ≠ 0) hx).to_iff

/-- Multiplicities of finite Laurent limits are locally constant when the nonmonic
leading coefficient and discriminant have power-times-unit forms. The root multiset
identity is an input, so the polynomial `Q` can be a divided central fiber, such as a
Lazard evaluation, rather than the possibly nullified ordinary fiber. -/
theorem eventually_rootMultiplicity_eq_of_finite_laurent_limits
    (hs : ∀ i, AnalyticAt 𝕜 (s i) (x₀, y₀))
    (hu : AnalyticAt 𝕜 u (x₀, y₀)) (hu0 : u (x₀, y₀) ≠ 0)
    (hv : AnalyticAt 𝕜 v (x₀, y₀)) (hv0 : v (x₀, y₀) ≠ 0)
    (hnorm : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ →
      (P p).integralNormalization = ∏ i, (X - C (s i p)))
    (hlead : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ →
      (P p).coeff d = (p.2 - y₀) ^ c * v p)
    (hdiscr : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ →
      (P p).discr = (p.2 - y₀) ^ a * u p)
    {e : Fin d → ℤ} {w : Fin d → E × 𝕜 → 𝕜}
    (hscale : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ →
      ∀ i, 0 ≤ e i → (P p).coeff d * r i p = s i p)
    (hw : ∀ i, 0 ≤ e i → AnalyticAt 𝕜 (w i) (x₀, y₀))
    (hLaurent : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ →
      ∀ i, 0 ≤ e i → r i p = (p.2 - y₀) ^ e i * w i p)
    {Q : E → Polynomial 𝕜}
    (hroots : ∀ᶠ x in 𝓝 x₀, (Q x).roots =
      (Finset.univ.filter (fun i ↦ 0 ≤ e i)).val.map
        (fun i ↦ if e i = 0 then w i (x, y₀) else 0)) :
    ∀ᶠ x in 𝓝 x₀, ∀ i, 0 ≤ e i →
      (Q x).rootMultiplicity (if e i = 0 then w i (x, y₀) else 0) =
        (Q x₀).rootMultiplicity (if e i = 0 then w i (x₀, y₀) else 0) := by
  classical
  let I := Finset.univ.filter (fun i ↦ 0 ≤ e i)
  let f : Fin d → E × 𝕜 → 𝕜 := fun i p ↦ (p.2 - y₀) ^ (e i).toNat * w i p
  have hf (i : Fin d) (hi : i ∈ I) : AnalyticAt 𝕜 (f i) (x₀, y₀) :=
    ((analyticAt_snd.sub analyticAt_const).fun_pow _).mul
      (hw i (Finset.mem_filter.mp hi).2)
  have hvalue (i : Fin d) (hei : 0 ≤ e i) :
      ∀ x, f i (x, y₀) = if e i = 0 then w i (x, y₀) else 0 := by
    intro x
    by_cases he : e i = 0
    · simp [f, he]
    · have hpos : (e i).toNat ≠ 0 := by omega
      simp [f, he, zero_pow hpos]
  have hscaled : ∀ᶠ p in 𝓝 (x₀, y₀), p.2 ≠ y₀ →
      ∀ i ∈ I, (P p).coeff d * f i p = s i p := by
    filter_upwards [hscale, hLaurent] with p hp hl hp0 i hi
    have hei := (Finset.mem_filter.mp hi).2
    rw [← hp hp0 i hei, hl hp0 i hei, ← Int.toNat_of_nonneg hei, zpow_natCast]
  have hrel : ∀ᶠ x in 𝓝 x₀, ∀ i ∈ I, ∀ j ∈ I,
      f i (x, y₀) = f j (x, y₀) ↔ f i (x₀, y₀) = f j (x₀, y₀) := by
    refine (eventually_all_finset I).2 fun i hi ↦ (eventually_all_finset I).2 fun j hj ↦ ?_
    exact eventually_finite_root_eq_iff_on_hyperplane hs hu hu0 hv hv0
      hnorm hlead hdiscr i j (hf i hi) (hf j hj)
      (hscaled.mono fun p hp hp0 ↦ ⟨hp hp0 i hi, hp hp0 j hj⟩)
  have hlimits : ∀ᶠ x in 𝓝 x₀, ∀ i ∈ I, ∀ j ∈ I,
      (if e i = 0 then w i (x, y₀) else 0) =
        (if e j = 0 then w j (x, y₀) else 0) ↔
      (if e i = 0 then w i (x₀, y₀) else 0) =
        (if e j = 0 then w j (x₀, y₀) else 0) := by
    filter_upwards [hrel] with x hx i hi j hj
    simpa only [hvalue i (Finset.mem_filter.mp hi).2,
      hvalue j (Finset.mem_filter.mp hj).2] using hx i hi j hj
  have hmult := eventually_rootMultiplicity_eq_of_roots_eq_map hroots.self_of_nhds
    hroots hlimits
  exact hmult.mono fun x hx i hei ↦ hx i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hei⟩)

end TauCeti
