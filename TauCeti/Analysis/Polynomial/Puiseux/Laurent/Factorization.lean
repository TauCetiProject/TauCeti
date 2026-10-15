/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Puiseux.Nonmonic.Basic
public import TauCeti.Analysis.Polynomial.Puiseux.Laurent.Basic
import TauCeti.Analysis.Analytic.Laurent.Exponent

/-!
# Construction of nonmonic Puiseux Laurent factorizations

A polynomial family with analytic coefficients and nonzero discriminant off a distinguished
hyperplane splits after substitution by the factorial of its degree. When its leading and
constant coefficients are powers of the distinguished coordinate times analytic units,
the roots have Laurent power times unit forms near every point of the hyperplane.
The integer exponents are independent of the parameter throughout the simply connected base,
and their pole orders are bounded by the substituted leading-coefficient exponent. Degree drops
and nullified fibers on the hyperplane are allowed.

The construction joins `exists_analyticOnNhd_nonmonic_powerSubstitution`, which constructs
roots and removes their poles, with `TauCeti.exists_root_eq_zpow_mul_unit`, which extracts
unit forms from the analytic roots of integral normalization. Neither a root labelling nor
a splitting is an input. The trailing-coefficient hypothesis prevents roots from vanishing
identically or acquiring a parameter-dependent order.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), §4, Corollary 4.2.
-/

public section

open Filter Function Metric Polynomial Set Topology

namespace TauCeti.Polynomial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {U : Set E} [SimplyConnectedSpace U] {F : E × ℂ → ℂ[X]} {d a c : ℕ} {R : ℝ}
  {u v : E × ℂ → ℂ}

/-- **Nonmonic Puiseux Laurent factorization with parameters.** Analytic coefficients,
constant degree and nonzero discriminant off `y = 0`, and power-times-unit leading and
constant coefficients suffice to construct a complete distinct splitting after `y = t ^ d!`.
All roots simultaneously have the form `t ^ e * w` near every point of `t = 0`, with one
integer exponent vector `e ≥ -(d! * a)` on the entire base and point-dependent analytic
nowhere-zero units.
The same root labels have analytic extensions after multiplication by `t ^ (d! * a)`.
The original fibers on the hyperplane may drop degree or be zero. Degree zero is included. -/
theorem exists_analyticOnNhd_nonmonic_laurent
    (hU : IsOpen U) (hR : 0 < R)
    (hF : ∀ i ≤ d, AnalyticOnNhd ℂ (fun b ↦ (F b).coeff i) (U ×ˢ ball 0 R))
    (hdeg : ∀ b ∈ U ×ˢ (ball 0 R \ {0}), (F b).natDegree = d)
    (hdiscr : ∀ b ∈ U ×ˢ (ball 0 R \ {0}), (F b).discr ≠ 0)
    (hu : AnalyticOnNhd ℂ u (U ×ˢ ball 0 R))
    (hu0 : ∀ b ∈ U ×ˢ ball 0 R, u b ≠ 0)
    (hv : AnalyticOnNhd ℂ v (U ×ˢ ball 0 R))
    (hv0 : ∀ b ∈ U ×ˢ ball 0 R, v b ≠ 0)
    (hlead : ∀ b ∈ U ×ˢ ball 0 R, (F b).coeff d = b.2 ^ a * u b)
    (hconst : ∀ b ∈ U ×ˢ ball 0 R, (F b).coeff 0 = b.2 ^ c * v b) :
    ∃ R' : ℝ, 0 < R' ∧ R' ^ d.factorial ≤ R ∧
      ∃ r g : Fin d → E × ℂ → ℂ,
        (∀ i, AnalyticOnNhd ℂ (r i) (U ×ˢ (ball 0 R' \ {0}))) ∧
        (∀ i, AnalyticOnNhd ℂ (g i) (U ×ˢ ball 0 R') ∧
          EqOn (g i) (fun b ↦ b.2 ^ (d.factorial * a) * r i b)
            (U ×ˢ (ball 0 R' \ {0}))) ∧
        (∀ b ∈ U ×ˢ (ball 0 R' \ {0}),
          Injective (fun i ↦ r i b) ∧
          F (b.1, b.2 ^ d.factorial) =
            C ((F (b.1, b.2 ^ d.factorial)).coeff d) * ∏ i, (X - C (r i b))) ∧
        ∃ e : Fin d → ℤ, ∀ x ∈ U, ∃ w : Fin d → E × ℂ → ℂ,
          (∀ i, -(d.factorial * a : ℤ) ≤ e i) ∧
          (∀ i, AnalyticAt ℂ (w i) (x, 0)) ∧ (∀ i, w i (x, 0) ≠ 0) ∧
          ∀ᶠ b in 𝓝 (x, (0 : ℂ)), (∀ i, w i b ≠ 0) ∧
            (b.2 ≠ 0 → ∀ i, r i b = b.2 ^ e i * w i b) := by
  -- Choose a substituted disc and construct roots with analytically removable poles.
  let R' := min R 1 / 2
  have hR' : 0 < R' := by dsimp only [R']; positivity
  have hR'R : R' ≤ R := by dsimp only [R']; linarith [min_le_left R 1]
  have hR'1 : R' ≤ 1 := by dsimp only [R']; linarith [min_le_right R 1]
  have hfit : R' ^ d.factorial ≤ R :=
    (pow_le_of_le_one hR'.le hR'1 d.factorial_ne_zero).trans hR'R
  obtain ⟨r, g, hra, hg, hr⟩ := exists_analyticOnNhd_nonmonic_powerSubstitution
    hU hR' d.factorial_ne_zero hfit (dvd_refl _) hF hdeg hdiscr hu hu0
    (fun b hb ↦ hlead b ⟨hb.1, hb.2.1⟩)
  obtain ⟨s, hsa, hscale, hnorm⟩ :=
    exists_analyticOnNhd_integralNormalization_eq_prod_X_sub_C_powerSubstitution
      d.factorial_ne_zero hfit hdeg hu (fun b hb ↦ hu0 b ⟨hb.1, hb.2.1⟩)
      (fun b hb ↦ hlead b ⟨hb.1, hb.2.1⟩) hg (fun b hb ↦ (hr b hb).2)
  refine ⟨R', hR', hfit, r, g, hra, hg, hr, ?_⟩
  have hlocal : ∀ i x, x ∈ U →
      ∃ e : ℤ, -(d.factorial * a : ℤ) ≤ e ∧ ∃ w : E × ℂ → ℂ,
        AnalyticAt ℂ w (x, 0) ∧ w (x, 0) ≠ 0 ∧
          ∀ᶠ b in 𝓝 (x, (0 : ℂ)), b.2 ≠ 0 → r i b = b.2 ^ e * w b := by
    intro i x hx
    by_cases hd : d = 0
    · subst d
      exact Fin.elim0 i
    let q : E × ℂ → E × ℂ := fun b ↦ (b.1, b.2 ^ d.factorial)
    have hq : AnalyticOnNhd ℂ q (U ×ˢ ball 0 R') := fun _ _ ↦
      analyticAt_fst.prod (analyticAt_snd.pow d.factorial)
    have hqmem : MapsTo q (U ×ˢ ball 0 R') (U ×ˢ ball 0 R) :=
      (mapsTo_id U).prodMap (mapsTo_pow_ball_zero d.factorial_ne_zero hfit)
    have hx' : (x, (0 : ℂ)) ∈ U ×ˢ ball 0 R' := ⟨hx, mem_ball_self hR'⟩
    have hxR : (x, (0 : ℂ)) ∈ U ×ˢ ball 0 R := ⟨hx, mem_ball_self hR⟩
    have hscale' : ∀ᶠ b in 𝓝 (x, (0 : ℂ)), b.2 ≠ 0 → ∀ i,
        (F (q b)).coeff d * r i b = s i b := by
      filter_upwards [(hU.prod isOpen_ball).mem_nhds hx'] with b hb hb0
      exact hscale b ⟨hb.1, hb.2, hb0⟩
    have hnorm' : ∀ᶠ b in 𝓝 (x, (0 : ℂ)), b.2 ≠ 0 →
        (F (q b)).integralNormalization = ∏ i, (X - C (s i b)) := by
      filter_upwards [(hU.prod isOpen_ball).mem_nhds hx'] with b hb hb0
      exact hnorm b ⟨hb.1, hb.2, hb0⟩
    have hleadq : ∀ᶠ b in 𝓝 (x, (0 : ℂ)),
        (F (q b)).coeff d = b.2 ^ (d.factorial * a) * u (q b) := by
      filter_upwards [(hU.prod isOpen_ball).mem_nhds hx'] with b hb
      simpa only [q, ← pow_mul] using hlead _ (hqmem hb)
    have hconstq : ∀ᶠ b in 𝓝 (x, (0 : ℂ)),
        (F (q b)).coeff 0 = b.2 ^ (d.factorial * c) * v (q b) := by
      filter_upwards [(hU.prod isOpen_ball).mem_nhds hx'] with b hb
      simpa only [q, ← pow_mul] using hconst _ (hqmem hb)
    -- The trailing coefficient forces each normalized root to have constant finite
    -- order. Dividing by the leading coefficient gives the Laurent exponent and bound.
    obtain ⟨m, w, hw, hw0, hform⟩ := TauCeti.exists_root_eq_zpow_mul_unit
      (Nat.pos_of_ne_zero hd) (fun i ↦ hsa i _ hx') ((hv.comp hq hqmem) _ hx')
      (by simpa only [comp_apply, q, zero_pow d.factorial_ne_zero] using hv0 _ hxR)
      ((hu.comp hq hqmem) _ hx')
      (by simpa only [comp_apply, q, zero_pow d.factorial_ne_zero] using hu0 _ hxR) hnorm'
      (by simpa only [sub_zero, comp_apply] using hleadq)
      (by simpa only [sub_zero, comp_apply] using hconstq)
      hscale'
    refine ⟨(m i : ℤ) - (d.factorial * a : ℕ), ?_, w i, hw i, hw0 i, ?_⟩
    · push_cast
      omega
    · simpa only [sub_zero] using (hform.mono fun b hb hb0 ↦ hb.2 hb0 i)
  obtain ⟨x₀, hx₀⟩ := (inferInstance : Nonempty U)
  obtain ⟨e, he, hform⟩ := exists_laurentExponents_of_isPreconnected
    ⟨x₀, hx₀⟩ (isPreconnected_iff_preconnectedSpace.mpr inferInstance) r hlocal
  refine ⟨e, fun x hx ↦ ?_⟩
  choose w hw hw0 hweq using fun i ↦ hform i x hx
  refine ⟨w, he, hw, hw0, ?_⟩
  filter_upwards [eventually_all.2 fun i ↦ (hw i).continuousAt.eventually_ne (hw0 i),
    eventually_all.2 hweq] with b hbne hbeq
  exact ⟨hbne, fun hb i ↦ hbeq i hb⟩

end TauCeti.Polynomial
