/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Puiseux.Branches
public import TauCeti.Analysis.Polynomial.Puiseux.Extension
public import TauCeti.Analysis.Polynomial.Puiseux.RootDifference
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Monic Puiseux factorization with parameters

A monic polynomial family with analytic coefficients on `U × ball 0 R`, whose discriminant
is `y ^ a * u` with `u` nowhere zero, splits into analytic linear factors after `y = t ^ d!`.
The factorization holds on the full substituted disc, including `t = 0`, where roots may
collide. The parameter domain `U` can be any open simply connected subset of a finite
dimensional complex normed space, in particular a polydisc.

`exists_analyticOnNhd_prod_X_sub_C_powerSubstitution_ball` gives the full-disc splitting
under the weaker assumption of separability off the hyperplane, for any nonzero multiple
of `d!` and any substituted radius that fits. The discriminant form of the result is
`exists_analyticOnNhd_prod_X_sub_C_of_discr_eq_pow_mul`; it chooses a positive substituted
radius and also gives the local power-times-unit form of every difference of distinct
root labels at each point of the hyperplane. The degree-zero case is included.

The splitting uses the punctured root covering and monodromy theorem
`exists_analyticOnNhd_eq_prod_X_sub_C_powerSubstitution`, followed by the joint analytic
extension `exists_analyticOnNhd_monicOfCoeff_eq_prod_X_sub_C`. The root-difference conclusion
uses `TauCeti.exists_root_sub_eq_pow_mul_unit`.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), Theorem 4.1 and its appendix.
-/

public section

open Filter Function Metric Polynomial Set Topology

namespace TauCeti.Polynomial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {U : Set E} [SimplyConnectedSpace U] {F : E × ℂ → ℂ[X]} {d n : ℕ} {R R' : ℝ}

/-- A monic family with continuous coefficients, analytic and separable off `y = 0`,
splits after a power substitution into analytic linear factors on the full disc.
The factors retain their multiplicities at `t = 0` and are pointwise distinct off that
hyperplane. The exponent can be any
nonzero multiple of `d!`. -/
theorem exists_analyticOnNhd_prod_X_sub_C_powerSubstitution_ball
    (hU : IsOpen U) (hR' : 0 < R')
    (hF : ∀ i < d, AnalyticOnNhd ℂ (fun b ↦ (F b).coeff i) (U ×ˢ (ball 0 R \ {0})))
    (hcoeff : ∀ i < d, ContinuousOn (fun b ↦ (F b).coeff i) (U ×ˢ ball 0 R))
    (hmonic : ∀ b ∈ U ×ˢ ball 0 R, (F b).Monic)
    (hdeg : ∀ b ∈ U ×ˢ ball 0 R, (F b).natDegree = d)
    (hsep : ∀ b ∈ U ×ˢ (ball 0 R \ {0}), (F b).Separable)
    (hn : n ≠ 0) (hR : R' ^ n ≤ R) (hdvd : d.factorial ∣ n) :
    ∃ r : Fin d → E × ℂ → ℂ,
      (∀ i, AnalyticOnNhd ℂ (r i) (U ×ˢ ball 0 R')) ∧
      (∀ b ∈ U ×ˢ ball 0 R', F (b.1, b.2 ^ n) = ∏ i, (X - C (r i b))) ∧
      ∀ b ∈ U ×ˢ (ball 0 R' \ {0}), Injective (fun i ↦ r i b) := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  have hsub : U ×ˢ (ball (0 : ℂ) R \ {0}) ⊆ U ×ˢ ball 0 R :=
    prod_mono subset_rfl sdiff_subset
  obtain ⟨s, hs, hfac⟩ := exists_analyticOnNhd_eq_prod_X_sub_C_powerSubstitution hU
    hR' hn hR hdvd hF (fun b hb ↦ hmonic b (hsub hb))
    (fun b hb ↦ hdeg b (hsub hb)) hsep
  let Q : E × ℂ → E × ℂ := fun b ↦ (b.1, b.2 ^ n)
  have hQ : MapsTo Q (U ×ˢ ball 0 R') (U ×ˢ ball 0 R) := by
    intro b hb
    refine ⟨hb.1, ?_⟩
    rw [mem_ball_zero_iff, norm_pow]
    exact (pow_lt_pow_left₀ (mem_ball_zero_iff.1 hb.2) (norm_nonneg _) hn).trans_le hR
  let c : E × ℂ → Fin d → ℂ := fun b i ↦ (F (Q b)).coeff i
  have hc : ContinuousOn c (U ×ˢ ball 0 R') := continuousOn_pi.2 fun i ↦
    ((hcoeff i i.isLt).comp (by fun_prop) hQ)
  have hcF (b) (hb : b ∈ U ×ˢ ball 0 R') : monicOfCoeff (c b) = F (Q b) :=
    monicOfCoeff_coeff (hmonic _ (hQ hb)) (hdeg _ (hQ hb))
  obtain ⟨r, hr, hrfac⟩ := exists_analyticOnNhd_monicOfCoeff_eq_prod_X_sub_C c s hU
    isOpen_ball hc hs (fun b hb ↦ (hcF b ⟨hb.1, hb.2.1⟩).trans (hfac b hb).2)
  exact ⟨r, fun i ↦ (hr i).1, fun b hb ↦ (hcF b hb).symm.trans (hrfac b hb),
    fun b hb ↦ by simpa only [(hr _).2 hb] using (hfac b hb).1⟩

/-- **Monic Puiseux with parameters.** If the discriminant is `y ^ a * u`, with analytic
nowhere-zero `u`, substitution by `t ^ d!` gives an analytic splitting on a full disc of
positive radius. At every parameter on `t = 0`, every difference of distinct root labels
is locally a power of `t` times an analytic unit. The branches may collide at `t = 0`,
but are pointwise distinct elsewhere. -/
theorem exists_analyticOnNhd_prod_X_sub_C_of_discr_eq_pow_mul
    (hU : IsOpen U) (hR : 0 < R)
    (hF : ∀ i < d, AnalyticOnNhd ℂ (fun b ↦ (F b).coeff i) (U ×ˢ ball 0 R))
    (hmonic : ∀ b ∈ U ×ˢ ball 0 R, (F b).Monic)
    (hdeg : ∀ b ∈ U ×ˢ ball 0 R, (F b).natDegree = d)
    {a : ℕ} {u : E × ℂ → ℂ} (hu : AnalyticOnNhd ℂ u (U ×ˢ ball 0 R))
    (hu0 : ∀ b ∈ U ×ˢ ball 0 R, u b ≠ 0)
    (hdiscr : ∀ b ∈ U ×ˢ ball 0 R, (F b).discr = b.2 ^ a * u b) :
    ∃ R' : ℝ, 0 < R' ∧ R' ^ d.factorial ≤ R ∧
      ∃ r : Fin d → E × ℂ → ℂ,
        (∀ i, AnalyticOnNhd ℂ (r i) (U ×ˢ ball 0 R')) ∧
        (∀ b ∈ U ×ˢ ball 0 R', F (b.1, b.2 ^ d.factorial) = ∏ i, (X - C (r i b))) ∧
        (∀ b ∈ U ×ˢ (ball 0 R' \ {0}), Injective (fun i ↦ r i b)) ∧
        ∀ w ∈ U, ∀ i j : Fin d, i ≠ j → ∃ m : ℕ, ∃ v : E × ℂ → ℂ,
          AnalyticAt ℂ v (w, 0) ∧ v (w, 0) ≠ 0 ∧
            ∀ᶠ b in 𝓝 (w, 0), r i b - r j b = b.2 ^ m * v b := by
  have hsep : ∀ b ∈ U ×ˢ (ball 0 R \ {0}), (F b).Separable := by
    intro b hb
    have hb' : b ∈ U ×ˢ ball (0 : ℂ) R := ⟨hb.1, hb.2.1⟩
    apply (hmonic b hb').discr_ne_zero_iff.1
    rw [hdiscr b hb']
    exact mul_ne_zero (pow_ne_zero a hb.2.2) (hu0 b hb')
  -- A radius below both `R` and `1` fits for every positive substitution exponent.
  let R' := min R 1 / 2
  have hR' : 0 < R' := by dsimp only [R']; positivity
  have hR'R : R' ≤ R := by dsimp only [R']; linarith [min_le_left R 1]
  have hR'1 : R' ≤ 1 := by dsimp only [R']; linarith [min_le_right R 1]
  have hfit : R' ^ d.factorial ≤ R :=
    (pow_le_of_le_one hR'.le hR'1 d.factorial_ne_zero).trans hR'R
  obtain ⟨r, hr, hfac, hinj⟩ := exists_analyticOnNhd_prod_X_sub_C_powerSubstitution_ball
    hU hR' (fun i hi ↦ (hF i hi).mono (prod_mono subset_rfl sdiff_subset))
    (fun i hi ↦ (hF i hi).continuousOn) hmonic hdeg hsep
    d.factorial_ne_zero hfit (dvd_refl _)
  refine ⟨R', hR', hfit, r, hr, hfac, hinj, ?_⟩
  intro w hw i j hij
  let Q : E × ℂ → E × ℂ := fun b ↦ (b.1, b.2 ^ d.factorial)
  have hQ : AnalyticAt ℂ Q (w, 0) := analyticAt_fst.prod (analyticAt_snd.pow _)
  have hw0 : (w, (0 : ℂ)) ∈ U ×ˢ ball 0 R' := ⟨hw, mem_ball_self hR'⟩
  have hwR : Q (w, 0) ∈ U ×ˢ ball 0 R := by simp [Q, d.factorial_ne_zero, hw, hR]
  have hQmem : ∀ b ∈ U ×ˢ ball 0 R', Q b ∈ U ×ˢ ball 0 R := by
    intro b hb
    refine ⟨hb.1, ?_⟩
    rw [mem_ball_zero_iff, norm_pow]
    exact (pow_lt_pow_left₀ (mem_ball_zero_iff.1 hb.2) (norm_nonneg _)
      d.factorial_ne_zero).trans_le hfit
  have hd : ∀ᶠ b in 𝓝 (w, (0 : ℂ)), (F (Q b)).discr = b.2 ^ (d.factorial * a) * u (Q b) := by
    filter_upwards [(hU.prod isOpen_ball).mem_nhds hw0] with b hb
    simpa only [Q, ← pow_mul] using hdiscr _ (hQmem b hb)
  obtain ⟨m, v, hv, hv0, heq⟩ := TauCeti.exists_root_sub_eq_pow_mul_unit
    (fun i ↦ hr i _ hw0)
    (Filter.mem_of_superset ((hU.prod isOpen_ball).mem_nhds hw0) hfac)
    ((hu _ hwR).comp hQ) (hu0 _ hwR)
    (by simpa only [sub_zero, Q, Function.comp_apply] using hd) hij
  exact ⟨m, v, hv, hv0, by simpa only [sub_zero] using heq⟩

end TauCeti.Polynomial
