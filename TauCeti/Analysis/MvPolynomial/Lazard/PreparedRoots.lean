/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Puiseux.Lazard
public import TauCeti.Analysis.MvPolynomial.Lazard.RootFactorization
public import TauCeti.RingTheory.MvPolynomial.Lazard.Map

/-!
# Constructed Lazard root multisets

Real analytic centers with locally constant finite Lazard valuations of the formal leading
coefficient, constant coefficient, and discriminant construct a complete Laurent splitting.
The finite branch limits of this same splitting enumerate the roots, with multiplicity, of
nearby Lazard evaluations. Ordinary fibers may be nullified. A common complexification,
evaluator, analytic leading and formal-discriminant units, and pole-removed root functions
are retained for subsequent analysis of the real roots.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), §5.2, proof of Theorem 5.1.
-/

public section

open Filter Finsupp Function Metric Set Topology

namespace Polynomial

variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- The factorial substitution keeps the prepared scalar unit in the factorization: for a fixed
center `z` and all small nonzero `y`, the complexified rotated polynomial along the monomial curve
factors through the pole-removed root functions. -/
private theorem eventually_eval_monomialCurve_eq_prod_of_laurent
    (p : Polynomial (MvPolynomial (Fin n) ℝ)) {a : ι → ℝ} {ρ R : ℝ} (hρ : 0 < ρ) (hR : 0 < R)
    {c : Fin n → ℕ} {vLead : Fin n →₀ ℕ} {Φ : (ι → ℂ) → Fin n → ℂ} {s : Fin n → ℝ}
    {u : (ι → ℂ) × ℂ → ℂ} {r w : Fin p.natDegree → (ι → ℂ) × ℂ → ℂ} {e : Fin p.natDegree → ℤ}
    {z : ι → ℂ} (hz : z ∈ ball (fun j ↦ (a j : ℂ)) ρ) (hΦ : Φ z = fun j ↦ (s j : ℂ))
    (hunit : ∀ b ∈ ball (fun j ↦ (a j : ℂ)) ρ ×ˢ ball 0 ρ,
      MvPolynomial.eval₂ Complex.ofRealHom (fun j ↦ Φ b.1 j + b.2 ^ c j) p.leadingCoeff =
        b.2 ^ Finsupp.weight c vLead * u b)
    (hfac : ∀ b ∈ ball (fun j ↦ (a j : ℂ)) ρ ×ˢ (ball 0 R \ {0}),
      p.map (MvPolynomial.eval₂Hom Complex.ofRealHom
          (fun j ↦ Φ b.1 j + b.2 ^ (p.natDegree.factorial * c j))) =
        C (MvPolynomial.eval₂ Complex.ofRealHom
          (fun j ↦ Φ b.1 j + b.2 ^ (p.natDegree.factorial * c j)) p.leadingCoeff) *
          ∏ i, (X - C (r i b)))
    (hr : ∀ᶠ y in 𝓝 (0 : ℂ), y ≠ 0 → ∀ i, r i (z, y) = y ^ e i * w i (z, y)) :
    ∀ᶠ y in 𝓝[≠] (0 : ℂ),
      (MvPolynomial.aeval (MvPolynomial.monomialCurve (Polynomial.C ∘ (fun j ↦ (s j : ℂ)))
        (p.natDegree.factorial • c)) (MvPolynomial.map (Polynomial.mapRingHom Complex.ofRealHom)
        (MvPolynomial.optionEquivRight ℝ (Fin n)
          ((MvPolynomial.optionEquivLeft ℝ (Fin n)).symm p)))).eval (Polynomial.C y) =
          C (y ^ (p.natDegree.factorial * Finsupp.weight c vLead : ℤ) *
            u (z, y ^ p.natDegree.factorial)) * ∏ i, (X - C (y ^ e i * w i (z, y))) := by
  have hd : 0 < p.natDegree.factorial := Nat.factorial_pos _
  have hball : ∀ᶠ y in 𝓝 (0 : ℂ), y ∈ ball 0 R := ball_mem_nhds 0 hR
  have hpower : ∀ᶠ y in 𝓝 (0 : ℂ), (z, y ^ p.natDegree.factorial) ∈
      ball (fun j ↦ (a j : ℂ)) ρ ×ˢ ball 0 ρ := by
    apply (tendsto_const_nhds.prodMk_nhds ?_).eventually
      ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨hz, mem_ball_self hρ⟩)
    simpa only [zero_pow hd.ne'] using (continuous_pow p.natDegree.factorial).tendsto (0 : ℂ)
  filter_upwards [hball.filter_mono nhdsWithin_le_nhds, hpower.filter_mono nhdsWithin_le_nhds,
    hr.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy hyp hyr hy0
  have hy0' : y ≠ 0 := by simpa using hy0
  have hsplit := hfac (z, y) ⟨hz, hy, hy0'⟩
  have hlead' := hunit (z, y ^ p.natDegree.factorial) hyp
  simp only [← pow_mul] at hlead'
  rw [hΦ] at hsplit hlead'
  rw [MvPolynomial.aeval_monomialCurve_map_optionEquivRight_eval Complex.ofRealHom]
  simpa only [Function.comp_def, ← pow_mul, hlead', ← Int.natCast_mul, zpow_natCast,
    hyr hy0'] using hsplit

/-- The roots of the complexified Lazard evaluation at a nearby center `x` are the finite limits of
the Laurent branches, and the weight of its Lazard exponent, with respect to the factorial-scaled
evaluator, equals the factorial-scaled weight of the leading coefficient plus the sum of the
negative branch exponents. -/
private theorem roots_weight_lazardEval_of_laurent
    (p : Polynomial (MvPolynomial (Fin n) ℝ)) (hp : p ≠ 0) {a x : ι → ℝ} {ρ R : ℝ} (hρ : 0 < ρ)
    (hR : 0 < R) (hx : dist x a < ρ) {c : Fin n → ℕ} {vLead : Fin n →₀ ℕ}
    {T : Set (Fin n →₀ ℕ)} (hc : TauCeti.IsLazardEvaluator T c)
    {Φ : (ι → ℂ) → Fin n → ℂ} {s : Fin n → ℝ} {u : (ι → ℂ) × ℂ → ℂ}
    {r w : Fin p.natDegree → (ι → ℂ) × ℂ → ℂ} {e : Fin p.natDegree → ℤ}
    (hmem : (MvPolynomial.optionEquivRight ℝ (Fin n)
      ((MvPolynomial.optionEquivLeft ℝ (Fin n)).symm p)).lazardExponent (Polynomial.C ∘ s) ∈ T)
    (hΦ : Φ (fun j ↦ (x j : ℂ)) = fun j ↦ (s j : ℂ))
    (hu : AnalyticOnNhd ℂ u (ball (fun j ↦ (a j : ℂ)) ρ ×ˢ ball 0 ρ))
    (hunit : ∀ b ∈ ball (fun j ↦ (a j : ℂ)) ρ ×ˢ ball 0 ρ, u b ≠ 0 ∧
      MvPolynomial.eval₂ Complex.ofRealHom (fun j ↦ Φ b.1 j + b.2 ^ c j) p.leadingCoeff =
        b.2 ^ Finsupp.weight c vLead * u b)
    (hfac : ∀ b ∈ ball (fun j ↦ (a j : ℂ)) ρ ×ˢ (ball 0 R \ {0}),
      p.map (MvPolynomial.eval₂Hom Complex.ofRealHom
          (fun j ↦ Φ b.1 j + b.2 ^ (p.natDegree.factorial * c j))) =
        C (MvPolynomial.eval₂ Complex.ofRealHom
          (fun j ↦ Φ b.1 j + b.2 ^ (p.natDegree.factorial * c j)) p.leadingCoeff) *
          ∏ i, (X - C (r i b)))
    (hxan : ∀ i, AnalyticAt ℂ (w i) ((fun j ↦ (x j : ℂ)), 0))
    (hxne : ∀ i, e i < 0 → w i ((fun j ↦ (x j : ℂ)), 0) ≠ 0)
    (hxlocal : ∀ᶠ y in 𝓝 (0 : ℂ),
      y ≠ 0 → ∀ i, r i ((fun j ↦ (x j : ℂ)), y) = y ^ e i * w i ((fun j ↦ (x j : ℂ)), y)) :
    (((MvPolynomial.optionEquivRight ℝ (Fin n)
        ((MvPolynomial.optionEquivLeft ℝ (Fin n)).symm p)).lazardEval
          (Polynomial.C ∘ s)).map Complex.ofRealHom).roots =
          (Finset.univ.filter (fun i ↦ 0 ≤ e i)).val.map
            (fun i ↦ if e i = 0 then w i ((fun j ↦ (x j : ℂ)), 0) else 0) ∧
      (Finsupp.weight (p.natDegree.factorial • c) ((MvPolynomial.optionEquivRight ℝ (Fin n)
        ((MvPolynomial.optionEquivLeft ℝ (Fin n)).symm p)).lazardExponent
          (Polynomial.C ∘ s)) : ℤ) =
        p.natDegree.factorial * Finsupp.weight c vLead + ∑ i, min (e i) 0 := by
  classical
  let z : ι → ℂ := fun j ↦ (x j : ℂ)
  have hz : z ∈ ball (fun j ↦ (a j : ℂ)) ρ := by
    have hdist : dist z (fun j ↦ (a j : ℂ)) = dist x a := by
      simpa only [z, Function.comp_def] using (Complex.isometry_ofReal.postcomp_pi).dist_eq x a
    exact hdist.trans_lt hx
  let q := MvPolynomial.optionEquivRight ℝ (Fin n)
    ((MvPolynomial.optionEquivLeft ℝ (Fin n)).symm p)
  let f := Polynomial.mapRingHom Complex.ofRealHom
  let qC := MvPolynomial.map f q
  have hf : Injective f := Polynomial.map_injective Complex.ofRealHom Complex.ofReal_injective
  have hq : q ≠ 0 := by
    simpa only [q, AlgEquiv.trans_apply, map_zero] using
      ((MvPolynomial.optionEquivLeft ℝ (Fin n)).symm.trans
        (MvPolynomial.optionEquivRight ℝ (Fin n))).injective.ne hp
  have hqC : qC ≠ 0 := by
    simpa only [qC, map_zero] using (MvPolynomial.map_injective f hf).ne hq
  let d := p.natDegree.factorial
  have hd : 0 < d := Nat.factorial_pos _
  let U : ℂ → ℂ := fun y ↦ u (z, y ^ d)
  have hU : AnalyticAt ℂ U 0 := by
    exact (hu (z, 0) ⟨hz, mem_ball_self hρ⟩).comp_of_eq
      (analyticAt_const.prod (analyticAt_id.pow d)) (by simp only [zero_pow hd.ne'])
  have hU0 : U 0 ≠ 0 := by
    simpa only [U, zero_pow hd.ne'] using (hunit (z, 0) ⟨hz, mem_ball_self hρ⟩).1
  -- Injective coefficient transport preserves the actual Lazard exponents and evaluation.
  have hexp : qC.lazardExponent (Polynomial.C ∘ (fun j ↦ (s j : ℂ))) =
      q.lazardExponent (Polynomial.C ∘ s) := by
    simpa only [qC, Function.comp_def, f, Polynomial.coe_mapRingHom,
      Polynomial.map_C, Complex.ofRealHom_eq_coe] using
      MvPolynomial.lazardExponent_map f hf q (Polynomial.C ∘ s)
  have heval : qC.lazardEval (Polynomial.C ∘ (fun j ↦ (s j : ℂ))) =
      (q.lazardEval (Polynomial.C ∘ s)).map Complex.ofRealHom := by
    simpa only [qC, Function.comp_def, f, Polynomial.coe_mapRingHom,
      Polynomial.map_C, Complex.ofRealHom_eq_coe] using
      MvPolynomial.lazardEval_map f hf q (Polynomial.C ∘ s)
  have hcx : TauCeti.IsLazardEvaluator {qC.lazardExponent (Polynomial.C ∘ (fun j ↦ (s j : ℂ)))}
      (d • c) := (hc.mono (by simpa only [hexp, Set.singleton_subset_iff] using hmem)).smul hd
  have hsplit := eventually_eval_monomialCurve_eq_prod_of_laurent p hρ hR hz hΦ
    (fun b hb ↦ (hunit b hb).2) hfac hxlocal
  have hw' (i) : AnalyticAt ℂ (fun y ↦ w i (z, y)) 0 :=
    (hxan i).comp (analyticAt_const.prod analyticAt_id)
  have hw0' (i) (hi : e i < 0) : w i (z, 0) ≠ 0 := hxne i hi
  rw [← heval, ← hexp]
  exact ⟨MvPolynomial.roots_lazardEval_eq_map_of_laurent qC hqC _ _ hcx hU hU0 hw' hw0' hsplit,
    MvPolynomial.weight_lazardExponent_eq_of_laurent qC hqC _ _ hcx hU hU0 hw' hw0' hsplit⟩

/-- Finite locally constant valuations along real analytic centers construct Laurent branches
whose finite limits give the complete complex root multiset of the Lazard evaluation near the
center. The leading and formal-discriminant units and all branch data belong to the same
monomial deformation. The local branch-unit family is fixed at the central parameter and
works for every nearby real parameter. Poles contribute no finite root and positive branch
exponents contribute zero. The same Laurent exponents force the removed Lazard exponent to be
locally constant. -/
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
      ∃ u v : (ι → ℂ) × ℂ → ℂ,
        AnalyticOnNhd ℂ u (ball (fun j ↦ (a j : ℂ)) ρ ×ˢ ball 0 ρ) ∧
        (∀ b ∈ ball (fun j ↦ (a j : ℂ)) ρ ×ˢ ball 0 ρ, u b ≠ 0 ∧
          MvPolynomial.eval₂ Complex.ofRealHom
            (fun j ↦ Φ b.1 j + b.2 ^ c j) p.leadingCoeff =
              b.2 ^ Finsupp.weight c vLead * u b) ∧
        AnalyticOnNhd ℂ v (ball (fun j ↦ (a j : ℂ)) ρ ×ˢ ball 0 ρ) ∧
        (∀ b ∈ ball (fun j ↦ (a j : ℂ)) ρ ×ˢ ball 0 ρ, v b ≠ 0 ∧
          MvPolynomial.eval₂ Complex.ofRealHom
            (fun j ↦ Φ b.1 j + b.2 ^ c j) p.discr =
              b.2 ^ Finsupp.weight c vDiscr * v b) ∧
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
                    (fun i ↦ if e i = 0 then w i ((fun j ↦ (x j : ℂ)), 0) else 0) ∧
                q.lazardExponent (Polynomial.C ∘ φ x) =
                  q.lazardExponent (Polynomial.C ∘ φ a) := by
  classical
  let q := MvPolynomial.optionEquivRight ℝ (Fin n)
    ((MvPolynomial.optionEquivLeft ℝ (Fin n)).symm p)
  obtain ⟨ρ, hρ, Φ, c, hc, hΦ, hreal, hstar, u, v, hu, hunit, hv, hvunit,
      R, hR, hfit, r, g, hr, hg, hfac, e, w, he, hwa, hwne, hform⟩ :=
    p.exists_complexification_isLazardEvaluator_nonmonic_laurent hφ
      vLead vConst vDiscr hlead hconst hdiscr (MvPolynomial.finite_range_lazardExponent q)
  have ha : ((fun j ↦ (a j : ℂ)), (0 : ℂ)) ∈
      ball (fun j ↦ (a j : ℂ)) ρ ×ˢ ball 0 R := ⟨mem_ball_self hρ, mem_ball_self hR⟩
  have hw (i) := hwa i _ ha
  have hw0 (i) := hwne i _ ha
  have hlocal : ∀ᶠ b in 𝓝 ((fun j ↦ (a j : ℂ)), (0 : ℂ)), (∀ i, w i b ≠ 0) ∧
      (b.2 ≠ 0 → ∀ i, r i b = b.2 ^ e i * w i b) := by
    filter_upwards [(isOpen_ball.prod isOpen_ball).mem_nhds ha] with b hb
    exact ⟨fun i ↦ hwne i b hb, fun hb0 i ↦ hform b ⟨hb.1, hb.2, hb0⟩ i⟩
  refine ⟨ρ, hρ, Φ, c, hc, hΦ, hreal, hstar, u, v, hu, hunit, hv, hvunit,
    R, hR, hfit, r, g, hr, hg, hfac, e, w, he, hw, hw0, hlocal, ?_⟩
  have hp : p ≠ 0 := by
    rintro rfl
    simpa using hlead.exists
  -- A unit family chosen once at the central parameter stays analytic and nonzero nearby.
  have hregular : ∀ᶠ b in 𝓝 ((fun j ↦ (a j : ℂ)), (0 : ℂ)),
      ∀ i, AnalyticAt ℂ (w i) b ∧ w i b ≠ 0 :=
    eventually_all.2 fun i ↦ (hw i).eventually_analyticAt.and
      ((hw i).continuousAt.eventually_ne (hw0 i))
  have hcenters := (continuous_pi fun j ↦
    Complex.continuous_ofReal.comp (continuous_apply j) : Continuous fun x : ι → ℝ ↦
      (fun j ↦ (x j : ℂ))).tendsto a
  have hcurried : ∀ᶠ z in 𝓝 (fun j ↦ (a j : ℂ)), ∀ᶠ y in 𝓝 (0 : ℂ),
      (∀ i, w i (z, y) ≠ 0) ∧
        (y ≠ 0 → ∀ i, r i (z, y) = y ^ e i * w i (z, y)) := by
    rw [nhds_prod_eq] at hlocal
    exact hlocal.curry
  have hdata : ∀ᶠ x in 𝓝 a,
      ((q.lazardEval (Polynomial.C ∘ φ x)).map Complex.ofRealHom).roots =
          (Finset.univ.filter (fun i ↦ 0 ≤ e i)).val.map
            (fun i ↦ if e i = 0 then w i ((fun j ↦ (x j : ℂ)), 0) else 0) ∧
        (Finsupp.weight (p.natDegree.factorial • c)
          (q.lazardExponent (Polynomial.C ∘ φ x)) : ℤ) =
            p.natDegree.factorial * Finsupp.weight c vLead + ∑ i, min (e i) 0 := by
    filter_upwards [ball_mem_nhds a hρ, hcenters.eventually
        ((tendsto_id.prodMk_nhds tendsto_const_nhds).eventually hregular),
      hcenters.eventually hcurried] with x hx hxregular hxlocal
    exact roots_weight_lazardEval_of_laurent p hp hρ hR hx hc
      (Set.mem_union_right _ (Set.mem_range_self _)) (hreal x hx) hu hunit
      (fun b hb ↦ (hfac b hb).2) (fun i ↦ (hxregular i).1) (fun i _ ↦ (hxregular i).2)
      (hxlocal.mono fun y hy ↦ hy.2)
  have haweight := hdata.self_of_nhds.2
  filter_upwards [hdata] with x hx
  exact ⟨hx.1, (hc.smul (Nat.factorial_pos _)).weight_injOn
    (Set.mem_union_right _ (Set.mem_range_self _))
    (Set.mem_union_right _ (Set.mem_range_self _))
    (Int.ofNat_injective (hx.2.trans haweight.symm))⟩

end Polynomial
