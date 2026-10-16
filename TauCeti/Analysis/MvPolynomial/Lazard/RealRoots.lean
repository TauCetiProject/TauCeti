/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MvPolynomial.Lazard.PreparedRoots
import TauCeti.Analysis.Polynomial.Puiseux.Nonmonic.RealRoots

/-!
# Constructing ordered analytic roots of Lazard evaluations

Locally constant finite Lazard valuations of the leading coefficient, constant coefficient,
and discriminant along real analytic centers construct strictly ordered real analytic root
sections of the Lazard evaluations. Their multiplicities are positive and locally constant,
and the vector of removed base exponents is constant on the same neighborhood. The ordinary
fibers may be nullified: the sections enumerate the nonzero Lazard evaluations.

The sections include repeated finite Laurent limits with their multiplicities; branches with
poles contribute no finite root. Finite-valuation hypotheses exclude zero formal polynomials,
but neither preservation of the ordinary fiber degree nor nonnullification is required.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), §5.2, proof of Theorem 5.1.
-/

public section

open Filter Finsupp Function Metric Set Topology

namespace Polynomial

variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- Finite locally constant Lazard valuations of the formal leading coefficient, constant
coefficient, and discriminant along analytic centers construct all real roots of nearby
Lazard evaluations as a strictly ordered analytic list, with constant removed base exponent
and constant positive multiplicities. The number of real roots is constructed and may be zero.
Ordinary fibers may be nullified, and no positive-degree assumption is needed. -/
theorem exists_analyticOnNhd_ordered_lazardEval_roots
    (p : Polynomial (MvPolynomial (Fin n) ℝ))
    {φ : (ι → ℝ) → Fin n → ℝ} {a : ι → ℝ}
    (hφ : AnalyticAt ℝ φ a) (vLead vConst vDiscr : Fin n →₀ ℕ)
    (hlead : ∀ᶠ x in 𝓝 a, p.leadingCoeff.lazardValuation (φ x) = toLex vLead)
    (hconst : ∀ᶠ x in 𝓝 a, (p.coeff 0).lazardValuation (φ x) = toLex vConst)
    (hdiscr : ∀ᶠ x in 𝓝 a, p.discr.lazardValuation (φ x) = toLex vDiscr) :
    let q := MvPolynomial.optionEquivRight ℝ (Fin n)
      ((MvPolynomial.optionEquivLeft ℝ (Fin n)).symm p)
    let F := fun x ↦ q.lazardEval (Polynomial.C ∘ φ x)
    ∃ k : ℕ, ∃ t : Fin k → (ι → ℝ) → ℝ, ∃ U : Set (ι → ℝ),
      IsOpen U ∧ a ∈ U ∧
      (∀ x ∈ U, F x ≠ 0) ∧
      (∀ x ∈ U, q.lazardExponent (Polynomial.C ∘ φ x) =
        q.lazardExponent (Polynomial.C ∘ φ a)) ∧
      (∀ i, AnalyticOnNhd ℝ (t i) U) ∧
      (∀ x ∈ U, StrictMono (fun i ↦ t i x)) ∧
      (∀ x ∈ U, ∀ z, (F x).IsRoot z ↔ ∃ i, t i x = z) ∧
      (∀ i, 0 < (F a).rootMultiplicity (t i a)) ∧
      ∀ x ∈ U, ∀ i, (F x).rootMultiplicity (t i x) = (F a).rootMultiplicity (t i a) := by
  classical
  let q := MvPolynomial.optionEquivRight ℝ (Fin n)
    ((MvPolynomial.optionEquivLeft ℝ (Fin n)).symm p)
  obtain ⟨ρ, hρ, Φ, c, hc, hΦ, hreal, hstar, u, v, hu, hunit, hv, hvunit,
      R, hR, hfit, r, g, hr, hg, hfac, e, w, he, hw, hw0, hlocal, hroots⟩ :=
    p.exists_complexification_isLazardEvaluator_lazardEval_roots hφ
      vLead vConst vDiscr hlead hconst hdiscr
  let z₀ : ι → ℂ := fun j ↦ (a j : ℂ)
  let d := p.natDegree.factorial
  let A := ball z₀ ρ
  let P : (ι → ℂ) × ℂ → ℂ[X] := fun b ↦
    p.map (MvPolynomial.eval₂Hom Complex.ofRealHom (fun j ↦ Φ b.1 j + b.2 ^ c j))
  -- Apply the factorial substitution to the prepared monomial deformation.
  let Q : (ι → ℂ) × ℂ → ℂ[X] := fun b ↦ P (b.1, b.2 ^ d)
  let subst : (ι → ℂ) × ℂ → (ι → ℂ) × ℂ := fun b ↦ (b.1, b.2 ^ d)
  have hsubst : AnalyticOnNhd ℂ subst (A ×ˢ ball 0 R) := fun _ _ ↦
    analyticAt_fst.prod (analyticAt_snd.pow d)
  have hsubmem : MapsTo subst (A ×ˢ ball 0 R) (A ×ˢ ball 0 ρ) :=
    (mapsTo_id A).prodMap (TauCeti.mapsTo_pow_ball_zero (Nat.factorial_ne_zero _) hfit)
  have hsubpunct : MapsTo subst (A ×ˢ (ball 0 R \ {0}))
      (A ×ˢ (ball 0 ρ \ {0})) :=
    (mapsTo_id A).prodMap
      (TauCeti.mapsTo_pow_ball_zero_diff_singleton (Nat.factorial_ne_zero _) hfit)
  have hL (b) (hb : b ∈ A ×ˢ ball 0 ρ) :
      (P b).coeff p.natDegree = b.2 ^ weight c vLead * u b := by
    simpa only [P, coeff_map, coeff_natDegree, MvPolynomial.coe_eval₂Hom] using
      (hunit b hb).2
  have hdeg (b) (hb : b ∈ A ×ˢ (ball 0 ρ \ {0})) :
      (P b).natDegree = p.natDegree := by
    apply natDegree_map_of_leadingCoeff_ne_zero
    have hl := hL b ⟨hb.1, hb.2.1⟩
    simp only [P, coeff_map, coeff_natDegree] at hl
    rw [hl]
    exact mul_ne_zero (pow_ne_zero _ hb.2.2) (hunit b ⟨hb.1, hb.2.1⟩).1
  -- Retain the normalized splitting of the same constructed branch labels.
  obtain ⟨s, hs, hscale, hnorm⟩ :=
    TauCeti.Polynomial.exists_analyticOnNhd_integralNormalization_eq_prod_X_sub_C_powerSubstitution
      (Nat.factorial_ne_zero _) hfit hdeg hu
      (fun b hb ↦ (hunit b ⟨hb.1, hb.2.1⟩).1)
      (fun b hb ↦ hL b ⟨hb.1, hb.2.1⟩) hg
      (fun b hb ↦ by simpa only [P, d, ← pow_mul, coeff_map, coeff_natDegree,
        MvPolynomial.coe_eval₂Hom] using (hfac b hb).2)
  have hzR : (z₀, (0 : ℂ)) ∈ A ×ˢ ball 0 R :=
    ⟨mem_ball_self hρ, mem_ball_self hR⟩
  have hzρ : (z₀, (0 : ℂ)) ∈ A ×ˢ ball 0 ρ :=
    ⟨mem_ball_self hρ, mem_ball_self hρ⟩
  have hmem : A ×ˢ ball (0 : ℂ) R ∈ 𝓝 (z₀, (0 : ℂ)) :=
    (isOpen_ball.prod isOpen_ball).mem_nhds hzR
  have hnorm' : ∀ᶠ b in 𝓝 (z₀, (0 : ℂ)), b.2 ≠ 0 →
      (Q b).integralNormalization = ∏ i, (X - C (s i b)) := by
    filter_upwards [hmem] with b hb hb0
    exact hnorm b ⟨hb.1, hb.2, hb0⟩
  have hscale' : ∀ᶠ b in 𝓝 (z₀, (0 : ℂ)), b.2 ≠ 0 →
      ∀ i, 0 ≤ e i → (Q b).coeff p.natDegree * r i b = s i b := by
    filter_upwards [hmem] with b hb hb0 i _
    exact hscale b ⟨hb.1, hb.2, hb0⟩ i
  have hL' : ∀ᶠ b in 𝓝 (z₀, (0 : ℂ)), b.2 ≠ 0 →
      (Q b).coeff p.natDegree = b.2 ^ (d * weight c vLead) * u (subst b) := by
    filter_upwards [hmem] with b hb _
    simpa only [Q, subst, ← pow_mul] using hL _ (hsubmem hb)
  have hD' : ∀ᶠ b in 𝓝 (z₀, (0 : ℂ)), b.2 ≠ 0 →
      (Q b).discr = b.2 ^ (d * weight c vDiscr) * v (subst b) := by
    filter_upwards [hmem] with b hb hb0
    have hb' := hsubpunct ⟨hb.1, hb.2, hb0⟩
    -- Formal and fiber discriminants agree here because the punctured degree is preserved.
    dsimp only [Q]
    rw [discr_map_of_natDegree_eq _ (hdeg _ hb')]
    simpa only [subst, MvPolynomial.coe_eval₂Hom, ← pow_mul] using
      (hvunit _ ⟨hb'.1, hb'.2.1⟩).2
  have hu' : AnalyticAt ℂ (u ∘ subst) (z₀, (0 : ℂ)) :=
    (hu.comp hsubst hsubmem) _ hzR
  have hv' : AnalyticAt ℂ (v ∘ subst) (z₀, (0 : ℂ)) :=
    (hv.comp hsubst hsubmem) _ hzR
  have hu0 : (u ∘ subst) (z₀, (0 : ℂ)) ≠ 0 := by
    simpa only [comp_apply, subst, d, zero_pow (Nat.factorial_ne_zero _)] using
      (hunit _ hzρ).1
  have hv0 : (v ∘ subst) (z₀, (0 : ℂ)) ≠ 0 := by
    simpa only [comp_apply, subst, d, zero_pow (Nat.factorial_ne_zero _)] using
      (hvunit _ hzρ).1
  have hp : p ≠ 0 := by
    intro hp
    obtain ⟨x, hx⟩ := hlead.exists
    simp [hp] at hx
  have hq : q ≠ 0 := by
    simpa only [q, AlgEquiv.trans_apply, map_zero] using
      ((MvPolynomial.optionEquivLeft ℝ (Fin n)).symm.trans
        (MvPolynomial.optionEquivRight ℝ (Fin n))).injective.ne hp
  -- Finite Laurent limits supply the real divided family, including nullified fibers.
  have hroots' := hroots.mono fun _ hx ↦ hx.1
  have hexponent := hroots.mono fun _ hx ↦ hx.2
  obtain ⟨k, t, U, hU, haU, hF, ht, hmono, hroot, hpos, hmult⟩ :=
    TauCeti.exists_analyticOnNhd_ordered_real_roots_of_finite_laurent_limits
      (fun i ↦ hs i _ hzR) hv' hv0 hu' hu0 hnorm'
      (by simpa only [comp_apply] using hL')
      (by simpa only [comp_apply] using hD') hscale' (fun i _ ↦ hw i)
      (hlocal.mono fun b hb hb0 i _ ↦ hb.2 hb0 i) hroots'
      (Eventually.of_forall fun x ↦ MvPolynomial.lazardEval_ne_zero hq _)
      ((ContinuousLinearMap.piMap fun _ ↦ Complex.ofRealCLM).analyticAt a)
  obtain ⟨W, hWU, hW, haW⟩ := _root_.mem_nhds_iff.1 hexponent
  refine ⟨k, t, U ∩ W, hU.inter hW, ⟨haU, haW⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun x hx ↦ hF x hx.1
  · exact fun x hx ↦ hWU hx.2
  · exact fun i ↦ (ht i).mono inter_subset_left
  · exact fun x hx ↦ hmono x hx.1
  · exact fun x hx ↦ hroot x hx.1
  · exact hpos
  · exact fun x hx ↦ hmult x hx.1

end Polynomial
