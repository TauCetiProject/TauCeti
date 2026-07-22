/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.DriftMaximumPrinciple

/-!
# Maximum principles with drift and a nonnegative zeroth-order term

This file combines the two lower-order extensions of the Laplacian maximum principle.  For the
operator `-Δ - b·∇ + c`, a nonnegative zeroth-order coefficient and a bounded drift preserve the
weak maximum principle.  The sign condition on `c` and the nonnegativity of the frontier bound are
explicit, as required for the standard estimate `sup u ≤ sup (u⁺|∂Ω)`.

The proof perturbs a subsolution by the positive exponential barrier already used for the drift
maximum principle.  At a positive interior maximum of the perturbation, its derivative vanishes
and its Laplacian is nonpositive, while the subsolution inequality, `c ≥ 0`, and strict positivity
of the barrier give the opposite strict inequality.

## Main declarations

* `TauCeti.le_of_mul_le_laplacian_add_fderiv_le_frontier`: the weak maximum principle for
  `-Δ - b·∇ + c`.
* `TauCeti.le_of_lowerOrder_le_of_le_frontier`: the corresponding comparison principle.
* `TauCeti.eqOn_of_lowerOrder_eq_of_eqOn_frontier`: Dirichlet uniqueness for equal operator
  values.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace Laplacian Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E]

/-- **Weak maximum principle for `-Δ - b·∇ + c`.**

If `c` is nonnegative, `b` has norm at most `β` on the interior of a compact set, and
`c x * f x ≤ Δ f x + fderiv ℝ f x (b x)`, then every nonnegative frontier bound for `f` is a
bound on the whole set. -/
theorem le_of_mul_le_laplacian_add_fderiv_le_frontier {K : Set E} (hK : IsCompact K)
    {c f : E → ℝ} {b : E → E} {β m : ℝ} (hm : 0 ≤ m) (hcont : ContinuousOn f K)
    (hcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hc : ∀ ⦃x⦄, x ∈ interior K → 0 ≤ c x)
    (hb : ∀ ⦃x⦄, x ∈ interior K → ‖b x‖ ≤ β)
    (hsub : ∀ ⦃x⦄, x ∈ interior K → c x * f x ≤ Δ f x + fderiv ℝ f x (b x))
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → f x ≤ m) :
    ∀ ⦃x⦄, x ∈ K → f x ≤ m := by
  intro x hxK
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  let u : E := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := norm_smul_inv_norm hv
  let α : ℝ := β + 1
  let w : E → ℝ := fun y => Real.exp (α * ⟪u, y⟫)
  have hwpos (y : E) : 0 < w y := Real.exp_pos _
  have hwcd : ContDiff ℝ 2 w := by
    have hi : ContDiff ℝ 2 (fun y : E => (⟪u, y⟫ : ℝ)) := by
      simpa only [coe_innerSL_apply] using (innerSL ℝ u).contDiff
    exact (by simpa only [smul_eq_mul] using hi.const_smul α : ContDiff ℝ 2 _).exp
  obtain ⟨C, hC⟩ := hK.bddAbove_image hwcd.continuous.continuousOn
  have hC0 : 0 ≤ C := (hwpos x).le.trans (hC (Set.mem_image_of_mem w hxK))
  apply le_of_forall_pos_mul_le hC0
  intro ε hε
  let g : E → ℝ := fun y => f y + ε • w y
  have hgcont : ContinuousOn g K := hcont.add (hwcd.continuous.continuousOn.const_smul ε)
  obtain ⟨z, hzK, hzmax⟩ := hK.exists_isMaxOn ⟨x, hxK⟩ hgcont
  have hfz : f z ≤ m := by
    by_cases hzint : z ∈ interior K
    · by_contra hn
      have hfz0 : 0 ≤ f z := hm.trans (not_le.mp hn).le
      have hgcd : ContDiffAt ℝ 2 g z := (hcd hzint).add (hwcd.contDiffAt.const_smul ε)
      have hloc : IsLocalMax g z := hzmax.isLocalMax (mem_interior_iff_mem_nhds.mp hzint)
      have hLgnonpos : Δ g z + fderiv ℝ g z (b z) ≤ 0 := by
        rw [hloc.fderiv_eq_zero]
        simpa using laplacian_nonpos_of_isLocalMax hgcd hloc
      have hαpos : 0 < α := by
        have hβ0 : 0 ≤ β := (norm_nonneg (b z)).trans (hb hzint)
        dsimp [α]
        linarith
      have hinner : -β ≤ ⟪u, b z⟫ := by
        have h := (abs_le.mp (abs_real_inner_le_norm u (b z))).1
        rw [hu, one_mul] at h
        exact (neg_le_neg (hb hzint)).trans h
      have hLwpos : 0 < Δ w z + fderiv ℝ w z (b z) := by
        have hLw : Δ w z + fderiv ℝ w z (b z) =
            α * (α + ⟪u, b z⟫) * Real.exp (α * ⟪u, z⟫) := by
          rw [show Δ w z = α ^ 2 * ‖u‖ ^ 2 * Real.exp (α * ⟪u, z⟫) by
                exact laplacian_exp_inner α u z,
            show fderiv ℝ w z (b z) = Real.exp (α * ⟪u, z⟫) * (α * ⟪u, b z⟫) by
                exact fderiv_exp_inner_apply α u z (b z), hu]
          ring
        rw [hLw]
        have : 0 < α + ⟪u, b z⟫ := by
          dsimp [α]
          linarith
        positivity
      have hLg : Δ g z + fderiv ℝ g z (b z) =
          (Δ f z + fderiv ℝ f z (b z)) +
            ε * (Δ w z + fderiv ℝ w z (b z)) := by
        have hfd : DifferentiableAt ℝ f z := (hcd hzint).differentiableAt (by norm_num)
        have hwd : DifferentiableAt ℝ w z := hwcd.differentiable (by norm_num) z
        have hΔ : Δ g z = Δ f z + ε * Δ w z := by
          have hadd : Δ (fun y => f y + ε • w y) z =
              Δ f z + Δ (fun y => ε • w y) z :=
            (hcd hzint).laplacian_add (hwcd.contDiffAt.const_smul ε)
          have hsmul : Δ (fun y => ε • w y) z = ε • Δ w z :=
            laplacian_smul ε hwcd.contDiffAt
          rw [show g = fun y => f y + ε • w y from rfl, hadd, hsmul, smul_eq_mul]
        have hderiv : fderiv ℝ g z (b z) =
            fderiv ℝ f z (b z) + ε * fderiv ℝ w z (b z) := by
          have hadd : fderiv ℝ (fun y => f y + ε • w y) z =
              fderiv ℝ f z + fderiv ℝ (fun y => ε • w y) z :=
            fderiv_add hfd (hwd.const_smul ε)
          have hsmul : fderiv ℝ (fun y => ε • w y) z = ε • fderiv ℝ w z :=
            fderiv_const_smul hwd ε
          rw [show g = fun y => f y + ε • w y from rfl, hadd, hsmul]
          simp only [add_apply, smul_apply, smul_eq_mul]
        rw [hΔ, hderiv]
        ring
      have hLf0 : 0 ≤ Δ f z + fderiv ℝ f z (b z) :=
        (mul_nonneg (hc hzint) hfz0).trans (hsub hzint)
      rw [hLg] at hLgnonpos
      nlinarith [mul_pos hε hLwpos]
    · exact hbdry ⟨subset_closure hzK, hzint⟩
  have hxle : f x + ε * w x ≤ f z + ε * w z := by
    simpa [g, smul_eq_mul] using hzmax hxK
  have hwzC : ε * w z ≤ ε * C :=
    mul_le_mul_of_nonneg_left (hC (Set.mem_image_of_mem w hzK)) hε.le
  nlinarith [mul_nonneg hε.le (hwpos x).le]

/-- **Comparison principle for `-Δ - b·∇ + c`.** Functions acted on by the same lower-order
coefficients are ordered on a compact set when their operator values and frontier values are
ordered. -/
theorem le_of_lowerOrder_le_of_le_frontier {K : Set E} (hK : IsCompact K) {c f g : E → ℝ}
    {b : E → E} {β : ℝ} (hfcont : ContinuousOn f K) (hgcont : ContinuousOn g K)
    (hfcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hgcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 g x)
    (hc : ∀ ⦃x⦄, x ∈ interior K → 0 ≤ c x)
    (hb : ∀ ⦃x⦄, x ∈ interior K → ‖b x‖ ≤ β)
    (hL : ∀ ⦃x⦄, x ∈ interior K →
      Δ g x + fderiv ℝ g x (b x) - c x * g x ≤
        Δ f x + fderiv ℝ f x (b x) - c x * f x)
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → f x ≤ g x) :
    ∀ ⦃x⦄, x ∈ K → f x ≤ g x := by
  intro x hx
  have h := le_of_mul_le_laplacian_add_fderiv_le_frontier (c := c) (f := f - g) (b := b)
    (β := β) (m := 0) hK le_rfl (hfcont.sub hgcont)
    (fun y hy => (hfcd hy).sub (hgcd hy)) hc hb (fun y hy => by
      rw [(hfcd hy).laplacian_sub (hgcd hy), fderiv_sub
        ((hfcd hy).differentiableAt (by norm_num)) ((hgcd hy).differentiableAt (by norm_num))]
      simp only [Pi.sub_apply, sub_apply]
      linarith [hL hy]) (fun y hy => sub_nonpos.mpr (hbdry hy)) hx
  exact sub_nonpos.mp h

/-- **Dirichlet uniqueness for `-Δ - b·∇ + c`.** Equal operator values and equal frontier data
force two functions to agree throughout the compact set. -/
theorem eqOn_of_lowerOrder_eq_of_eqOn_frontier {K : Set E} (hK : IsCompact K)
    {c f g : E → ℝ} {b : E → E} {β : ℝ} (hfcont : ContinuousOn f K)
    (hgcont : ContinuousOn g K)
    (hfcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hgcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 g x)
    (hc : ∀ ⦃x⦄, x ∈ interior K → 0 ≤ c x)
    (hb : ∀ ⦃x⦄, x ∈ interior K → ‖b x‖ ≤ β)
    (hL : ∀ ⦃x⦄, x ∈ interior K →
      Δ f x + fderiv ℝ f x (b x) - c x * f x =
        Δ g x + fderiv ℝ g x (b x) - c x * g x)
    (hbdry : Set.EqOn f g (frontier K)) : Set.EqOn f g K := by
  intro x hx
  apply le_antisymm
  · exact le_of_lowerOrder_le_of_le_frontier hK hfcont hgcont hfcd hgcd hc hb
      (fun y hy => (hL hy).ge) (fun y hy => (hbdry hy).le) hx
  · exact le_of_lowerOrder_le_of_le_frontier hK hgcont hfcont hgcd hfcd hc hb
      (fun y hy => (hL hy).le) (fun y hy => (hbdry hy).ge) hx

end TauCeti

end
