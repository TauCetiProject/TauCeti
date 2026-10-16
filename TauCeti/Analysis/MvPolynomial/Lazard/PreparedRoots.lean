/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Puiseux.Lazard
public import TauCeti.Analysis.MvPolynomial.Lazard.RootFactorization
public import TauCeti.RingTheory.MvPolynomial.Lazard.Map
import TauCeti.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Polynomial

/-!
# Constructed Lazard root multisets

Real analytic centers with locally constant finite Lazard valuations of the formal leading
coefficient, constant coefficient, and discriminant construct a complete Laurent splitting.
The finite branch limits of this same splitting enumerate the roots, with multiplicity, of
nearby Lazard evaluations. Ordinary fibers may be nullified. A common complexification,
evaluator, analytic leading unit, and pole-removed root functions are retained for subsequent
analysis of the real roots.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), §5.2, proof of Theorem 5.1.
-/

public section

open Filter Finsupp Function Metric Set Topology

namespace Polynomial

variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- Finite locally constant valuations along real analytic centers construct Laurent branches
whose finite limits give the complete complex root multiset of the Lazard evaluation near the
center. The leading unit and all branch data belong to the same monomial deformation. The
local unit family is fixed at the central parameter and works for every nearby real parameter;
poles contribute no finite root and positive branch exponents contribute zero. -/
theorem exists_complexification_isLazardEvaluator_lazardEval_roots
    (p : Polynomial (MvPolynomial (Fin n) ℝ)) {φ : (ι → ℝ) → Fin n → ℝ} {a : ι → ℝ}
    (hφ : AnalyticAt ℝ φ a) (vLead vConst vDiscr : Fin n →₀ ℕ)
    (hlead : ∀ᶠ x in 𝓝 a, p.leadingCoeff.lazardValuation (φ x) = toLex vLead)
    (hconst : ∀ᶠ x in 𝓝 a, (p.coeff 0).lazardValuation (φ x) = toLex vConst)
    (hdiscr : ∀ᶠ x in 𝓝 a, p.discr.lazardValuation (φ x) = toLex vDiscr) :
    let q := MvPolynomial.optionEquivRight ℝ (Fin n)
      ((MvPolynomial.optionEquivLeft ℝ (Fin n)).symm p)
    ∃ ρ > (0 : ℝ), ∃ Φ : (ι → ℂ) → Fin n → ℂ, ∃ c : Fin n → ℕ,
      TauCeti.IsLazardEvaluator ({vLead, vConst, vDiscr} ∪ Set.range q.lazardExponent) c ∧
      AnalyticOnNhd ℂ Φ (ball (fun j ↦ (a j : ℂ)) ρ) ∧
      (∀ x ∈ ball a ρ, Φ (fun j ↦ (x j : ℂ)) = fun i ↦ (φ x i : ℂ)) ∧
      (∀ z, Φ (star z) = star (Φ z)) ∧
      ∃ u : (ι → ℂ) × ℂ → ℂ,
        AnalyticOnNhd ℂ u (ball (fun j ↦ (a j : ℂ)) ρ ×ˢ ball 0 ρ) ∧
        (∀ b ∈ ball (fun j ↦ (a j : ℂ)) ρ ×ˢ ball 0 ρ, u b ≠ 0 ∧
          MvPolynomial.eval₂ Complex.ofRealHom
            (fun j ↦ Φ b.1 j + b.2 ^ c j) p.leadingCoeff =
              b.2 ^ Finsupp.weight c vLead * u b) ∧
      ∃ R > (0 : ℝ), R ^ p.natDegree.factorial ≤ ρ ∧
        ∃ r g : Fin p.natDegree → (ι → ℂ) × ℂ → ℂ,
          (∀ i, AnalyticOnNhd ℂ (r i)
            (ball (fun j ↦ (a j : ℂ)) ρ ×ˢ (ball 0 R \ {0}))) ∧
          (∀ i, AnalyticOnNhd ℂ (g i)
              (ball (fun j ↦ (a j : ℂ)) ρ ×ˢ ball 0 R) ∧
            EqOn (g i) (fun b ↦ b.2 ^ (p.natDegree.factorial *
              Finsupp.weight c vLead) * r i b)
              (ball (fun j ↦ (a j : ℂ)) ρ ×ˢ (ball 0 R \ {0}))) ∧
          (∀ b ∈ ball (fun j ↦ (a j : ℂ)) ρ ×ˢ (ball 0 R \ {0}),
            Injective (fun i ↦ r i b) ∧
            p.map (MvPolynomial.eval₂Hom Complex.ofRealHom
                (fun j ↦ Φ b.1 j + b.2 ^ (p.natDegree.factorial * c j))) =
              C (MvPolynomial.eval₂ Complex.ofRealHom
                (fun j ↦ Φ b.1 j + b.2 ^ (p.natDegree.factorial * c j)) p.leadingCoeff) *
                ∏ i, (X - C (r i b))) ∧
          ∃ e : Fin p.natDegree → ℤ, ∃ w : Fin p.natDegree → (ι → ℂ) × ℂ → ℂ,
            (∀ i, -(p.natDegree.factorial * Finsupp.weight c vLead : ℤ) ≤ e i) ∧
            (∀ i, AnalyticAt ℂ (w i) ((fun j ↦ (a j : ℂ)), 0)) ∧
            (∀ i, w i ((fun j ↦ (a j : ℂ)), 0) ≠ 0) ∧
            (∀ᶠ b in 𝓝 ((fun j ↦ (a j : ℂ)), (0 : ℂ)), (∀ i, w i b ≠ 0) ∧
              (b.2 ≠ 0 → ∀ i, r i b = b.2 ^ e i * w i b)) ∧
            ∀ᶠ x in 𝓝 a,
              ((q.lazardEval (Polynomial.C ∘ φ x)).map Complex.ofRealHom).roots =
                (Finset.univ.filter (fun i ↦ 0 ≤ e i)).val.map
                  (fun i ↦ if e i = 0 then w i ((fun j ↦ (x j : ℂ)), 0) else 0) := by
  classical
  let q := MvPolynomial.optionEquivRight ℝ (Fin n)
    ((MvPolynomial.optionEquivLeft ℝ (Fin n)).symm p)
  obtain ⟨ρ, hρ, Φ, c, hc, hΦ, hreal, hstar, u, hu, hunit,
      R, hR, hfit, r, g, hr, hg, hfac, e, hLaurent⟩ :=
    p.exists_complexification_isLazardEvaluator_nonmonic_laurent hφ
      vLead vConst vDiscr hlead hconst hdiscr (MvPolynomial.finite_range_lazardExponent q)
  obtain ⟨w, he, hw, hw0, hlocal⟩ := hLaurent _ (mem_ball_self hρ)
  refine ⟨ρ, hρ, Φ, c, hc, hΦ, hreal, hstar, u, hu, hunit,
    R, hR, hfit, r, g, hr, hg, hfac, e, w, he, hw, hw0, hlocal, ?_⟩
  have hp : p ≠ 0 := by
    intro hp
    obtain ⟨x, hx⟩ := hlead.exists
    simp [hp] at hx
  let f := Polynomial.mapRingHom Complex.ofRealHom
  let qC := MvPolynomial.map f q
  have hf : Injective f := Polynomial.map_injective Complex.ofRealHom Complex.ofReal_injective
  have hq : q ≠ 0 := by
    simpa only [q, AlgEquiv.trans_apply, map_zero] using
      ((MvPolynomial.optionEquivLeft ℝ (Fin n)).symm.trans
        (MvPolynomial.optionEquivRight ℝ (Fin n))).injective.ne hp
  have hqC : qC ≠ 0 := by
    simpa only [qC, map_zero] using (MvPolynomial.map_injective f hf).ne hq
  -- A unit family chosen once at the central parameter stays analytic and nonzero nearby.
  have hregular : ∀ᶠ b in 𝓝 ((fun j ↦ (a j : ℂ)), (0 : ℂ)),
      ∀ i, AnalyticAt ℂ (w i) b ∧ w i b ≠ 0 := by
    exact eventually_all.2 fun i ↦ (hw i).eventually_analyticAt.and
      ((hw i).continuousAt.eventually_ne (hw0 i))
  have hcenters : Tendsto (fun x : ι → ℝ ↦ (fun j ↦ (x j : ℂ)))
      (𝓝 a) (𝓝 (fun j ↦ (a j : ℂ))) :=
    (continuous_pi fun j ↦ Complex.continuous_ofReal.comp (continuous_apply j)).tendsto a
  have hregular0 := (tendsto_id.prodMk_nhds tendsto_const_nhds).eventually hregular
  have hcurried : ∀ᶠ z in 𝓝 (fun j ↦ (a j : ℂ)), ∀ᶠ y in 𝓝 (0 : ℂ),
      (∀ i, w i (z, y) ≠ 0) ∧
        (y ≠ 0 → ∀ i, r i (z, y) = y ^ e i * w i (z, y)) := by
    rw [nhds_prod_eq] at hlocal
    exact hlocal.curry
  filter_upwards [ball_mem_nhds a hρ, hcenters.eventually hregular0,
    hcenters.eventually hcurried] with x hx hxregular hxlocal
  let z : ι → ℂ := fun j ↦ (x j : ℂ)
  have hz : z ∈ ball (fun j ↦ (a j : ℂ)) ρ := by
    have hdist : dist z (fun j ↦ (a j : ℂ)) = dist x a := by
      simpa only [z, Function.comp_def] using
        (Complex.isometry_ofReal.postcomp_pi).dist_eq x a
    exact hdist.trans_lt hx
  let d := p.natDegree.factorial
  have hd : 0 < d := Nat.factorial_pos _
  let U : ℂ → ℂ := fun y ↦ u (z, y ^ d)
  have hU : AnalyticAt ℂ U 0 := by
    exact (hu (z, 0) ⟨hz, mem_ball_self hρ⟩).comp_of_eq
      (analyticAt_const.prod (analyticAt_id.pow d)) (by simp only [zero_pow hd.ne'])
  have hU0 : U 0 ≠ 0 := by
    simpa only [U, zero_pow hd.ne'] using (hunit (z, 0) ⟨hz, mem_ball_self hρ⟩).1
  -- Injective coefficient transport preserves the actual Lazard exponents and evaluation.
  have hexp : qC.lazardExponent (Polynomial.C ∘ (fun j ↦ (φ x j : ℂ))) =
      q.lazardExponent (Polynomial.C ∘ φ x) := by
    simpa only [qC, Function.comp_def, f, Polynomial.coe_mapRingHom,
      Polynomial.map_C, Complex.ofRealHom_eq_coe] using
      MvPolynomial.lazardExponent_map f hf q (Polynomial.C ∘ φ x)
  have heval : qC.lazardEval (Polynomial.C ∘ (fun j ↦ (φ x j : ℂ))) =
      (q.lazardEval (Polynomial.C ∘ φ x)).map Complex.ofRealHom := by
    simpa only [qC, Function.comp_def, f, Polynomial.coe_mapRingHom,
      Polynomial.map_C, Complex.ofRealHom_eq_coe] using
      MvPolynomial.lazardEval_map f hf q (Polynomial.C ∘ φ x)
  have hcx : TauCeti.IsLazardEvaluator
      {qC.lazardExponent (Polynomial.C ∘ (fun j ↦ (φ x j : ℂ)))} (d • c) := by
    apply (hc.mono ?_).smul hd
    intro v hv
    rcases Set.mem_singleton_iff.1 hv with rfl
    exact Set.mem_union_right _ (hexp ▸ Set.mem_range_self _)
  -- The factorial substitution retains the prepared scalar unit in the same factorization.
  have hsplit : ∀ᶠ y in 𝓝[≠] (0 : ℂ),
      (MvPolynomial.aeval (MvPolynomial.monomialCurve
        (Polynomial.C ∘ (fun j ↦ (φ x j : ℂ))) (d • c)) qC).eval (Polynomial.C y) =
          C (y ^ (d * Finsupp.weight c vLead : ℤ) * U y) *
            ∏ i, (X - C (y ^ e i * w i (z, y))) := by
    have hball : ∀ᶠ y in 𝓝 (0 : ℂ), y ∈ ball 0 R := ball_mem_nhds 0 hR
    have hpower : ∀ᶠ y in 𝓝 (0 : ℂ), (z, y ^ d) ∈
        ball (fun j ↦ (a j : ℂ)) ρ ×ˢ ball 0 ρ := by
      apply (tendsto_const_nhds.prodMk_nhds ?_).eventually
        ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨hz, mem_ball_self hρ⟩)
      simpa only [zero_pow hd.ne'] using (continuous_pow d).tendsto (0 : ℂ)
    filter_upwards [hball.filter_mono nhdsWithin_le_nhds,
      hpower.filter_mono nhdsWithin_le_nhds, hxlocal.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with y hy hyp hyw hy0
    have hy0' : y ≠ 0 := by simpa using hy0
    have hsplit := (hfac (z, y) ⟨hz, hy, hy0'⟩).2
    have hlead' := (hunit (z, y ^ d) hyp).2
    simp only [← pow_mul] at hlead'
    have hcenter : Φ z = fun j ↦ (φ x j : ℂ) := hreal x hx
    rw [hcenter] at hsplit hlead'
    -- The two presentations retain the distinguished variable through coefficient evaluation.
    have hcurve :
        (MvPolynomial.aeval (MvPolynomial.monomialCurve
          (Polynomial.C ∘ (fun j ↦ (φ x j : ℂ))) (d • c)) qC).eval (Polynomial.C y) =
            p.map (MvPolynomial.eval₂Hom Complex.ofRealHom
              (fun j ↦ (φ x j : ℂ) + y ^ (d * c j))) := by
      simp only [MvPolynomial.aeval_def, Polynomial.algebraMap_eq,
        MvPolynomial.polynomial_eval_eval₂, MvPolynomial.monomialCurve_apply,
        Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        Function.comp_apply, Pi.smul_apply, smul_eq_mul, ← Polynomial.C_pow,
        ← Polynomial.C_add]
      rw [← MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂Hom_map_hom]
      have hcoeff : ((evalRingHom (C y)).comp C).comp f = f := by
        apply RingHom.ext
        intro b
        simp only [RingHom.comp_apply, coe_evalRingHom, eval_C]
      rw [hcoeff]
      simpa only [q, f, AlgEquiv.trans_apply, Function.comp_def] using
        MvPolynomial.eval₂Hom_optionEquivRight_optionEquivLeft_symm
          Complex.ofRealHom (fun j ↦ (φ x j : ℂ) + y ^ (d * c j)) p
    rw [hcurve]
    have hrw (i) : r i (z, y) = y ^ e i * w i (z, y) := hyw.2 hy0' i
    simpa only [qC, q, f, Function.comp_def, Pi.smul_apply, smul_eq_mul,
      ← pow_mul, hlead', U, ← Int.natCast_mul, zpow_natCast, hrw, d] using hsplit
  rw [← heval]
  exact MvPolynomial.roots_lazardEval_eq_map_of_laurent qC hqC _ _ hcx hU hU0
    (fun i ↦ (hxregular i).1.comp (analyticAt_const.prod analyticAt_id))
    (fun i _ ↦ (hxregular i).2) hsplit

end Polynomial
