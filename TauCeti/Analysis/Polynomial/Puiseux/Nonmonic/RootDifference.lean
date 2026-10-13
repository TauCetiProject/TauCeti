/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Puiseux.Nonmonic.Basic
public import TauCeti.Analysis.Polynomial.Puiseux.RootDifference.Nonmonic

/-!
# Constructing nonmonic Puiseux root differences

An analytic polynomial family whose leading coefficient and discriminant are powers of a
distinguished coordinate times nowhere-zero analytic units admits Puiseux branches with
Laurent power-times-unit differences. The branches and their pole-removed extensions are
constructed from coefficient hypotheses, and the difference forms use those same labels.
No splitting, root labelling, or constancy of contact orders is assumed.

The Laurent exponent of each difference is locally independent of the other parameters.
Negative exponents allow poles, and positive exponents allow collisions on the exceptional
hyperplane. Fibers on that hyperplane may drop degree or be nullified. No condition on the
constant coefficient is needed: an individual root may vanish identically even though each
pairwise difference has a nonvanishing unit form.

For Puiseux splittings without root-difference forms, see
`exists_analyticOnNhd_nonmonic_powerSubstitution`. For Laurent unit forms for a supplied
splitting, see `TauCeti.exists_root_sub_eq_zpow_mul_unit`.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), §4, Corollary 4.2.
-/

public section

open Filter Function Metric Polynomial Set Topology

namespace TauCeti.Polynomial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {U : Set E} [SimplyConnectedSpace U] {F : E × ℂ → ℂ[X]} {d n a c : ℕ} {R R' : ℝ}
  {u v : E × ℂ → ℂ}

/-- Construct a complete distinct nonmonic Puiseux splitting, analytic extensions after
pole removal, and Laurent unit forms for every pairwise root difference near each point of
the exceptional hyperplane. The leading coefficient and discriminant need their prescribed
power-times-unit forms only off the hyperplane. Any positive substitution power divisible
by the factorial of the punctured-fiber degree is allowed. The difference exponents are
fixed on a neighborhood of the chosen parameter point; degree zero and one are included. -/
theorem exists_analyticOnNhd_nonmonic_root_sub_eq_zpow_mul_unit
    (hU : IsOpen U) (hR' : 0 < R') (hn : n ≠ 0) (hR : R' ^ n ≤ R)
    (hdvd : d.factorial ∣ n)
    (hF : ∀ i ≤ d, AnalyticOnNhd ℂ (fun b ↦ (F b).coeff i) (U ×ˢ ball 0 R))
    (hdeg : ∀ b ∈ U ×ˢ (ball 0 R \ {0}), (F b).natDegree = d)
    (hu : AnalyticOnNhd ℂ u (U ×ˢ ball 0 R))
    (hu0 : ∀ b ∈ U ×ˢ ball 0 R, u b ≠ 0)
    (hv : AnalyticOnNhd ℂ v (U ×ˢ ball 0 R))
    (hv0 : ∀ b ∈ U ×ˢ ball 0 R, v b ≠ 0)
    (hlead : ∀ b ∈ U ×ˢ (ball 0 R \ {0}), (F b).coeff d = b.2 ^ a * u b)
    (hdiscr : ∀ b ∈ U ×ˢ (ball 0 R \ {0}), (F b).discr = b.2 ^ c * v b) :
    ∃ r g : Fin d → E × ℂ → ℂ,
      (∀ i, AnalyticOnNhd ℂ (r i) (U ×ˢ (ball 0 R' \ {0}))) ∧
      (∀ i, AnalyticOnNhd ℂ (g i) (U ×ˢ ball 0 R') ∧
        EqOn (g i) (fun b ↦ b.2 ^ (n * a) * r i b) (U ×ˢ (ball 0 R' \ {0}))) ∧
      (∀ b ∈ U ×ˢ (ball 0 R' \ {0}),
        Injective (fun i ↦ r i b) ∧
        F (b.1, b.2 ^ n) = C ((F (b.1, b.2 ^ n)).coeff d) * ∏ i, (X - C (r i b))) ∧
      ∀ x ∈ U, ∀ i j : Fin d, i ≠ j → ∃ e : ℤ, ∃ w : E × ℂ → ℂ,
        AnalyticAt ℂ w (x, 0) ∧ w (x, 0) ≠ 0 ∧
          ∀ᶠ b in 𝓝 (x, (0 : ℂ)), w b ≠ 0 ∧
            (b.2 ≠ 0 → r i b - r j b = b.2 ^ e * w b) := by
  have hdiscr0 : ∀ b ∈ U ×ˢ (ball 0 R \ {0}), (F b).discr ≠ 0 := by
    intro b hb
    rw [hdiscr b hb]
    exact mul_ne_zero (pow_ne_zero _ hb.2.2) (hv0 b ⟨hb.1, hb.2.1⟩)
  obtain ⟨r, g, hra, hg, hr⟩ := exists_analyticOnNhd_nonmonic_powerSubstitution
    hU hR' hn hR hdvd hF hdeg hdiscr0 hu hu0 hlead
  obtain ⟨s, hsa, hscale, hnorm⟩ :=
    exists_analyticOnNhd_integralNormalization_eq_prod_X_sub_C_powerSubstitution
      hn hR hdeg hu (fun b hb ↦ hu0 b ⟨hb.1, hb.2.1⟩) hlead hg
      (fun b hb ↦ (hr b hb).2)
  refine ⟨r, g, hra, hg, hr, ?_⟩
  intro x hx i j hij
  let q : E × ℂ → E × ℂ := fun b ↦ (b.1, b.2 ^ n)
  have hq : AnalyticOnNhd ℂ q (U ×ˢ ball 0 R') := fun _ _ ↦
    analyticAt_fst.prod (analyticAt_snd.pow n)
  have hqfull : MapsTo q (U ×ˢ ball 0 R') (U ×ˢ ball 0 R) :=
    (mapsTo_id U).prodMap (mapsTo_pow_ball_zero hn hR)
  have hqmem : MapsTo q (U ×ˢ (ball 0 R' \ {0})) (U ×ˢ (ball 0 R \ {0})) :=
    (mapsTo_id U).prodMap (mapsTo_pow_ball_zero_diff_singleton hn hR)
  have hRpos : 0 < R := lt_of_lt_of_le (pow_pos hR' n) hR
  have hxR : (x, (0 : ℂ)) ∈ U ×ˢ ball 0 R := ⟨hx, mem_ball_self hRpos⟩
  have hx' : (x, (0 : ℂ)) ∈ U ×ˢ ball 0 R' := ⟨hx, mem_ball_self hR'⟩
  have hscale' : ∀ᶠ b in 𝓝 (x, (0 : ℂ)), b.2 ≠ 0 → ∀ k,
      (F (q b)).coeff d * r k b = s k b := by
    filter_upwards [(hU.prod isOpen_ball).mem_nhds hx'] with b hb hb0
    exact hscale b ⟨hb.1, hb.2, hb0⟩
  have hnorm' : ∀ᶠ b in 𝓝 (x, (0 : ℂ)), b.2 ≠ 0 →
      (F (q b)).integralNormalization = ∏ k, (X - C (s k b)) := by
    filter_upwards [(hU.prod isOpen_ball).mem_nhds hx'] with b hb hb0
    exact hnorm b ⟨hb.1, hb.2, hb0⟩
  -- Apply the Laurent difference theorem to this constructed normalized splitting.
  have hl : ∀ᶠ b in 𝓝 (x, (0 : ℂ)), b.2 ≠ 0 →
      (F (q b)).coeff d = b.2 ^ (n * a) * u (q b) := by
    filter_upwards [(hU.prod isOpen_ball).mem_nhds hx'] with b hb hb0
    simpa only [q, ← pow_mul] using hlead _ (hqmem ⟨hb.1, hb.2, hb0⟩)
  have hD : ∀ᶠ b in 𝓝 (x, (0 : ℂ)), b.2 ≠ 0 →
      (F (q b)).discr = b.2 ^ (n * c) * v (q b) := by
    filter_upwards [(hU.prod isOpen_ball).mem_nhds hx'] with b hb hb0
    simpa only [q, ← pow_mul] using hdiscr _ (hqmem ⟨hb.1, hb.2, hb0⟩)
  simpa only [sub_zero] using TauCeti.exists_root_sub_eq_zpow_mul_unit
    (fun k ↦ hsa k _ hx') ((hv.comp hq hqfull) _ hx')
    (by simpa only [comp_apply, q, zero_pow hn] using hv0 _ hxR)
    ((hu.comp hq hqfull) _ hx')
    (by simpa only [comp_apply, q, zero_pow hn] using hu0 _ hxR) hnorm'
    (by simpa only [sub_zero, comp_apply] using hl)
    (by simpa only [sub_zero, comp_apply] using hD)
    (hscale'.mono fun b hb hb0 ↦ ⟨hb hb0 i, hb hb0 j⟩) hij

end TauCeti.Polynomial
