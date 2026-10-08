/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Puiseux.Nonmonic
public import TauCeti.Analysis.Polynomial.Puiseux.Laurent.Basic

/-!
# Construction of nonmonic Puiseux Laurent factorizations

A polynomial family with analytic coefficients and nonzero discriminant off a distinguished
hyperplane splits after substitution by the factorial of its degree. When its leading and
constant coefficients are powers of the distinguished coordinate times analytic units,
the roots have Laurent power times unit forms near every point of the hyperplane.
The integer exponents are locally independent of the parameter, and their pole orders are
bounded by the substituted leading-coefficient exponent. Degree drops and nullified fibers
on the hyperplane are allowed.

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
Near every point of `t = 0`, all roots simultaneously have the form `t ^ e * w`, with
analytic nowhere-zero units and fixed integer exponents `e ≥ -(d! * a)`.
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
        ∀ x ∈ U, ∃ e : Fin d → ℤ, ∃ w : Fin d → E × ℂ → ℂ,
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
  refine ⟨R', hR', hfit, r, g, hra, hg, hr, ?_⟩
  intro x hx
  by_cases hd : d = 0
  · subst d
    exact ⟨Fin.elim0, Fin.elim0, by simp, by simp, by simp, by simp⟩
  let q : E × ℂ → E × ℂ := fun b ↦ (b.1, b.2 ^ d.factorial)
  have hq : AnalyticAt ℂ q (x, 0) := analyticAt_fst.prod (analyticAt_snd.pow _)
  have hq0 : q (x, 0) = (x, 0) := by simp [q, d.factorial_ne_zero]
  have hqmem : MapsTo q (U ×ˢ ball 0 R') (U ×ˢ ball 0 R) := by
    intro b hb
    refine ⟨hb.1, ?_⟩
    rw [mem_ball_zero_iff, norm_pow]
    exact (pow_lt_pow_left₀ (mem_ball_zero_iff.mp hb.2) (norm_nonneg _)
      d.factorial_ne_zero).trans_le hfit
  have hx' : (x, (0 : ℂ)) ∈ U ×ˢ ball 0 R' := ⟨hx, mem_ball_self hR'⟩
  have hxR : (x, (0 : ℂ)) ∈ U ×ˢ ball 0 R := ⟨hx, mem_ball_self hR⟩
  -- Multiplying the pole-removed branches by the leading-coefficient unit gives
  -- analytic roots of integral normalization, even at a degree drop.
  let s : Fin d → E × ℂ → ℂ := fun i b ↦ g i b * u (q b)
  have huq : AnalyticAt ℂ (u ∘ q) (x, 0) := (hq0 ▸ hu _ hxR).comp hq
  have hvq : AnalyticAt ℂ (v ∘ q) (x, 0) := (hq0 ▸ hv _ hxR).comp hq
  have hs : ∀ i, AnalyticAt ℂ (s i) (x, 0) := fun i ↦ ((hg i).1 _ hx').mul huq
  have hleadq : ∀ᶠ b in 𝓝 (x, (0 : ℂ)),
      (F (q b)).coeff d = b.2 ^ (d.factorial * a) * u (q b) := by
    filter_upwards [(hU.prod isOpen_ball).mem_nhds hx'] with b hb
    simpa only [q, ← pow_mul] using hlead _ (hqmem hb)
  have hconstq : ∀ᶠ b in 𝓝 (x, (0 : ℂ)),
      (F (q b)).coeff 0 = b.2 ^ (d.factorial * c) * v (q b) := by
    filter_upwards [(hU.prod isOpen_ball).mem_nhds hx'] with b hb
    simpa only [q, ← pow_mul] using hconst _ (hqmem hb)
  have hscale : ∀ᶠ b in 𝓝 (x, (0 : ℂ)), b.2 ≠ 0 →
      ∀ i, (F (q b)).coeff d * r i b = s i b := by
    filter_upwards [(hU.prod isOpen_ball).mem_nhds hx', hleadq] with b hb hl hb0 i
    have hgb : g i b = b.2 ^ (d.factorial * a) * r i b :=
      (hg i).2 ⟨hb.1, hb.2, hb0⟩
    simp only [s, hgb, hl, mul_right_comm]
  have hnorm : ∀ᶠ b in 𝓝 (x, (0 : ℂ)), b.2 ≠ 0 →
      (F (q b)).integralNormalization = ∏ i, (X - C (s i b)) := by
    filter_upwards [(hU.prod isOpen_ball).mem_nhds hx', hscale] with b hb hsb hb0
    have hbq : q b ∈ U ×ˢ (ball 0 R \ {0}) :=
      ⟨(hqmem hb).1, (hqmem hb).2, pow_ne_zero _ hb0⟩
    have hlc : (F (q b)).coeff d = (F (q b)).leadingCoeff := by
      rw [← hdeg _ hbq, coeff_natDegree]
    have hne : F (q b) ≠ 0 :=
      ne_zero_of_natDegree_gt ((hdeg _ hbq).symm ▸ Nat.pos_of_ne_zero hd)
    rw [(F (q b)).integralNormalization_eq_prod_X_sub_C (fun i ↦ r i b) hne
      (by simpa only [q, hlc] using (hr b ⟨hb.1, hb.2, hb0⟩).2)]
    simp only [← hlc, mul_comm _ ((F (q b)).coeff d), hsb hb0]
  -- The trailing coefficient forces each normalized root to have constant finite
  -- order. Dividing by the leading coefficient gives the Laurent exponent and bound.
  obtain ⟨m, w, hw, hw0, hform⟩ := TauCeti.exists_root_eq_zpow_mul_unit
    (Nat.pos_of_ne_zero hd) hs hvq (by simpa only [comp_apply, hq0] using hv0 _ hxR)
    huq (by simpa only [comp_apply, hq0] using hu0 _ hxR) hnorm
    (by simpa only [sub_zero, comp_apply] using hleadq)
    (by simpa only [sub_zero, comp_apply] using hconstq)
    hscale
  refine ⟨fun i ↦ (m i : ℤ) - (d.factorial * a : ℕ), w, ?_, hw, hw0, ?_⟩
  · intro i
    push_cast
    omega
  · simpa only [sub_zero] using hform

end TauCeti.Polynomial
