/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Puiseux.Branches
public import TauCeti.Analysis.Polynomial.Puiseux.Extension
public import TauCeti.Analysis.Polynomial.Monic.Normalization
public import TauCeti.RingTheory.Polynomial.Resultant.Normalization

/-!
# Nonmonic Puiseux branches and pole removal

A polynomial family with analytic coefficients, fixed degree and nonzero discriminant on a
punctured product splits after a power substitution into distinct analytic linear factors.
If its leading coefficient is `y ^ a` times a nowhere-zero analytic function on the full product,
multiplication of every substituted root by `t ^ (n * a)` gives an analytic extension across
`t = 0`. Degree drops and root collisions on that hyperplane are allowed.

The construction uses integral normalization, whose coefficients remain analytic through a
vanishing leading coefficient. Apply the monic punctured splitting theorem to this family,
divide its roots by the original leading coefficient off the hyperplane, and apply
`exists_analyticOnNhd_pow_mul_of_isRoot` to extend the scaled branches. The monic construction
is `exists_analyticOnNhd_eq_prod_X_sub_C_powerSubstitution`, and the analytic coefficient
normalization is `TauCeti.exists_analytic_monic_normalization`.
No root branches or analytic splitting are assumed. The discriminant need only be nonzero off
the hyperplane; in particular it may be a power of the parameter times a unit. No condition on
the constant coefficient is needed for construction or pole removal. A condition on that
coefficient is needed to extract nonvanishing Laurent units from the extended branches.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), §4, Corollary 4.2.
-/

public section

open Function Metric Polynomial Set

namespace TauCeti.Polynomial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {U : Set E} {F : E × ℂ → ℂ[X]} {u : E × ℂ → ℂ} {d n a : ℕ} {R R' : ℝ}

/-- A nonmonic analytic family of fixed degree with separable fibers splits on a punctured
product after a power substitution divisible by the factorial of its degree. The resulting
branches are distinct and give a complete factorization with the original leading coefficient.
No behavior at the puncture is assumed or asserted. -/
theorem exists_analyticOnNhd_eq_C_mul_prod_X_sub_C_powerSubstitution [CompleteSpace E]
    [SimplyConnectedSpace U]
    (hU : IsOpen U) (hR' : 0 < R') (hn : n ≠ 0) (hR : R' ^ n ≤ R)
    (hdvd : d.factorial ∣ n)
    (hF : ∀ i ≤ d, AnalyticOnNhd ℂ (fun b ↦ (F b).coeff i)
      (U ×ˢ (ball 0 R \ {0})))
    (hdeg : ∀ b ∈ U ×ˢ (ball 0 R \ {0}), (F b).natDegree = d)
    (hsep : ∀ b ∈ U ×ˢ (ball 0 R \ {0}), (F b).Separable) :
    ∃ r : Fin d → E × ℂ → ℂ,
      (∀ i, AnalyticOnNhd ℂ (r i) (U ×ˢ (ball 0 R' \ {0}))) ∧
      ∀ b ∈ U ×ˢ (ball 0 R' \ {0}),
        Injective (fun i ↦ r i b) ∧
        F (b.1, b.2 ^ n) = C ((F (b.1, b.2 ^ n)).coeff d) * ∏ i, (X - C (r i b)) := by
  classical
  let q : E × ℂ → E × ℂ := fun b ↦ (b.1, b.2 ^ n)
  have hq : AnalyticOnNhd ℂ q (U ×ˢ (ball 0 R' \ {0})) := fun _ _ ↦
    analyticAt_fst.prod (analyticAt_snd.pow n)
  have hqpunct : MapsTo q (U ×ˢ (ball 0 R' \ {0})) (U ×ˢ (ball 0 R \ {0})) := by
    intro b hb
    refine ⟨hb.1, ?_, pow_ne_zero n hb.2.2⟩
    rw [mem_ball_zero_iff, norm_pow]
    exact (pow_lt_pow_left₀ (mem_ball_zero_iff.1 hb.2.1) (norm_nonneg _) hn).trans_le hR
  -- Integral normalization preserves separability without division by coefficients.
  obtain ⟨Q, hQ, hQa, hQeq⟩ := exists_analytic_monic_normalization hF
  have hQsep : ∀ b ∈ U ×ˢ (ball 0 R \ {0}), (Q b).Separable := by
    intro b hb
    apply (hQ b).1.discr_ne_zero_iff.mp
    rw [hQeq b (hdeg b hb) (hsep b hb).ne_zero, discr_integralNormalization]
    exact mul_ne_zero (pow_ne_zero _ (leadingCoeff_ne_zero.2 (hsep b hb).ne_zero))
      ((discr_ne_zero_iff (hsep b hb).ne_zero).mpr (hsep b hb))
  obtain ⟨s, hsa, hs⟩ := exists_analyticOnNhd_eq_prod_X_sub_C_powerSubstitution
    hU hR' hn hR hdvd (fun i _ ↦ hQa i) (fun b _ ↦ (hQ b).1)
    (fun b _ ↦ (hQ b).2) hQsep
  let l : E × ℂ → ℂ := fun b ↦ (F (q b)).coeff d
  let r : Fin d → E × ℂ → ℂ := fun i b ↦ s i b / l b
  have hl : AnalyticOnNhd ℂ l (U ×ˢ (ball 0 R' \ {0})) :=
    (hF d le_rfl).comp hq hqpunct
  have hlc : ∀ b ∈ U ×ˢ (ball 0 R' \ {0}), l b = (F (q b)).leadingCoeff := by
    intro b hb
    dsimp only [l]
    rw [← hdeg _ (hqpunct hb), coeff_natDegree]
  have hl0 : ∀ b ∈ U ×ˢ (ball 0 R' \ {0}), l b ≠ 0 := fun b hb ↦
    hlc b hb ▸ leadingCoeff_ne_zero.2 (hsep _ (hqpunct hb)).ne_zero
  refine ⟨r, fun i ↦ (hsa i).div hl hl0, fun b hb ↦ ?_⟩
  -- Divide the normalized roots by the leading coefficient and recover the original factors.
  have hinj : Injective (fun i ↦ r i b) := fun i j hij ↦ (hs b hb).1
    ((div_left_inj' (hl0 b hb)).mp hij)
  have hroot : ∀ i, (F (q b)).IsRoot (r i b) := by
    intro i
    rw [← (F (q b)).isRoot_integralNormalization_mul_iff,
      ← hQeq _ (hdeg _ (hqpunct hb)) (hsep _ (hqpunct hb)).ne_zero, (hs b hb).2,
      isRoot_prod]
    refine ⟨i, Finset.mem_univ _, ?_⟩
    simp only [IsRoot.def, eval_sub, eval_X, eval_C, r, ← hlc b hb,
      mul_div_cancel₀ _ (hl0 b hb), sub_self]
  have hm : (C (l b)⁻¹ * F (q b)).Monic :=
    monic_C_mul_of_mul_leadingCoeff_eq_one (hlc b hb ▸ inv_mul_cancel₀ (hl0 b hb))
  have hd : (C (l b)⁻¹ * F (q b)).natDegree = d := by
    rw [natDegree_C_mul (inv_ne_zero (hl0 b hb)), hdeg _ (hqpunct hb)]
  have hfac := (Sym.toMonic_ofFn_eq_of_forall_isRoot hm hd hinj
    (fun i ↦ by simp only [IsRoot.def, eval_mul, eval_C, (hroot i).eq_zero, mul_zero])).symm.trans
      (Sym.toMonic_ofFn _)
  refine ⟨hinj, ?_⟩
  have heq := congrArg (C (l b) * ·) hfac
  simpa only [← mul_assoc, ← C_mul, mul_inv_cancel₀ (hl0 b hb), C_1, one_mul] using heq

/-- **Construct nonmonic Puiseux branches with removable poles.** Suppose the coefficients of
`F` through degree `d` are analytic on the full product, its degree is `d` and its discriminant
is nonzero off `y = 0`, and its degree-`d` coefficient is `y ^ a * u` there, with `u` analytic and
nowhere zero on the full product. For any positive power substitution divisible by `d!`, on a
suitably resized disc there are `d` distinct analytic roots giving a complete factorization.
Each `t ^ (n * a) * r i` extends analytically to the full product. The extended functions may
vanish or coincide at `t = 0`; the original fibers there may have smaller degree or be zero.
Degree zero is included. -/
theorem exists_analyticOnNhd_nonmonic_powerSubstitution [FiniteDimensional ℂ E]
    [SimplyConnectedSpace U]
    (hU : IsOpen U) (hR' : 0 < R') (hn : n ≠ 0) (hR : R' ^ n ≤ R)
    (hdvd : d.factorial ∣ n)
    (hF : ∀ i ≤ d, AnalyticOnNhd ℂ (fun b ↦ (F b).coeff i) (U ×ˢ ball 0 R))
    (hdeg : ∀ b ∈ U ×ˢ (ball 0 R \ {0}), (F b).natDegree = d)
    (hdiscr : ∀ b ∈ U ×ˢ (ball 0 R \ {0}), (F b).discr ≠ 0)
    (hu : AnalyticOnNhd ℂ u (U ×ˢ ball 0 R))
    (hu0 : ∀ b ∈ U ×ˢ ball 0 R, u b ≠ 0)
    (hlc : ∀ b ∈ U ×ˢ (ball 0 R \ {0}), (F b).coeff d = b.2 ^ a * u b) :
    ∃ r g : Fin d → E × ℂ → ℂ,
      (∀ i, AnalyticOnNhd ℂ (r i) (U ×ˢ (ball 0 R' \ {0}))) ∧
      (∀ i, AnalyticOnNhd ℂ (g i) (U ×ˢ ball 0 R') ∧
        EqOn (g i) (fun b ↦ b.2 ^ (n * a) * r i b) (U ×ˢ (ball 0 R' \ {0}))) ∧
      ∀ b ∈ U ×ˢ (ball 0 R' \ {0}),
        Injective (fun i ↦ r i b) ∧
        F (b.1, b.2 ^ n) = C ((F (b.1, b.2 ^ n)).coeff d) * ∏ i, (X - C (r i b)) := by
  have hne : ∀ b ∈ U ×ˢ (ball 0 R \ {0}), F b ≠ 0 := by
    intro b hb hz
    have hc : (F b).coeff d ≠ 0 := by
      rw [hlc b hb]
      exact mul_ne_zero (pow_ne_zero _ hb.2.2)
        (hu0 b (prod_mono subset_rfl sdiff_subset hb))
    exact hc (by simp [hz])
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  obtain ⟨r, hra, hr⟩ := exists_analyticOnNhd_eq_C_mul_prod_X_sub_C_powerSubstitution
    hU hR' hn hR hdvd (fun i hi ↦ (hF i hi).mono (prod_mono subset_rfl sdiff_subset))
    hdeg (fun b hb ↦ (discr_ne_zero_iff (hne b hb)).mp (hdiscr b hb))
  let q : E × ℂ → E × ℂ := fun b ↦ (b.1, b.2 ^ n)
  have hq : AnalyticOnNhd ℂ q (U ×ˢ ball 0 R') := fun _ _ ↦
    analyticAt_fst.prod (analyticAt_snd.pow n)
  have hqfull : MapsTo q (U ×ˢ ball 0 R') (U ×ˢ ball 0 R) := by
    intro b hb
    refine ⟨hb.1, ?_⟩
    rw [mem_ball_zero_iff, norm_pow]
    exact (pow_lt_pow_left₀ (mem_ball_zero_iff.1 hb.2) (norm_nonneg _) hn).trans_le hR
  have hqpunct : MapsTo q (U ×ˢ (ball 0 R' \ {0})) (U ×ˢ (ball 0 R \ {0})) :=
    fun b hb ↦ ⟨hb.1, (hqfull (prod_mono subset_rfl sdiff_subset hb)).2,
      pow_ne_zero n hb.2.2⟩
  have hroot : ∀ i b, b ∈ U ×ˢ (ball 0 R' \ {0}) → (F (q b)).IsRoot (r i b) := by
    intro i b hb
    rw [(hr b hb).2]
    apply root_mul_left_of_isRoot
    rw [isRoot_prod]
    exact ⟨i, Finset.mem_univ _, by simp⟩
  choose g hga hgeq using fun i ↦
    exists_analyticOnNhd_pow_mul_of_isRoot (d := d) (a := n * a) (F ∘ q) hU isOpen_ball
      (fun j hj ↦ ((hF j hj).comp hq hqfull).continuousOn)
      (fun b hb ↦ hdeg _ (hqpunct hb)) (hu.comp hq hqfull)
      (fun b hb ↦ hu0 _ (hqfull hb))
      (fun b hb ↦ by
        simpa only [q, comp_apply, sub_zero, pow_mul] using hlc _ (hqpunct hb))
      (hra i) (hroot i)
  exact ⟨r, g, hra, fun i ↦ ⟨hga i, by simpa only [sub_zero] using hgeq i⟩, hr⟩

end TauCeti.Polynomial
