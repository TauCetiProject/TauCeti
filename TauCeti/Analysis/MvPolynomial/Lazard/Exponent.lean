/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MvPolynomial.Lazard.RootFactorization
import TauCeti.Topology.LocallyConstant.Preconnected
import Mathlib.Analysis.Analytic.Constructions

/-!
# Constancy of removed Lazard exponents from Laurent factorizations

A complete Laurent factorization along monomial deformations determines the evaluator weight
of the removed base exponent: it is the scalar exponent plus the sum of the pole exponents.
An evaluator separates the possible removed exponents, so this scalar identity determines the
whole vector. Local Laurent forms with fixed integer exponents therefore force the removed
base vector to be locally constant, and constant on a preconnected parameter set.

These results apply before ordering the finite branch limits or proving their multiplicities
constant. Ordinary specialization can be nullified. Only the pole amplitudes must be nonzero;
no distinctness of branches or analyticity of the moving centers is required.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), §5.2, proof of Theorem 5.1.
-/

public section

open Filter Finsupp Polynomial Set Topology

namespace MvPolynomial

variable {𝕜 ι E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}

/-- Local Laurent forms with fixed scalar and branch exponents force the removed Lazard
base exponent to be constant near the parameter within `U`. The evaluator must separate the
removed exponents within `U` near that parameter. Ordinary fibers may be nullified. -/
theorem eventually_lazardExponent_eq_of_laurent
    (p : MvPolynomial (Fin n) (Polynomial 𝕜)) (hp : p ≠ 0)
    (φ : E → Fin n → 𝕜) (c : Fin n → ℕ) {U : Set E} {x : E} (hx : x ∈ U)
    (hc : ∀ᶠ y in 𝓝[U] x, TauCeti.IsLazardEvaluator
      {p.lazardExponent (Polynomial.C ∘ φ y), p.lazardExponent (Polynomial.C ∘ φ x)} c)
    {a : ℤ} {e : ι → ℤ} {u : E × 𝕜 → 𝕜} {w : ι → E × 𝕜 → 𝕜}
    (hu : AnalyticAt 𝕜 u (x, 0)) (hu0 : u (x, 0) ≠ 0)
    (hw : ∀ i, AnalyticAt 𝕜 (w i) (x, 0))
    (hw0 : ∀ i, e i < 0 → w i (x, 0) ≠ 0)
    (hfac : ∀ᶠ b in 𝓝 (x, (0 : 𝕜)), b.2 ≠ 0 →
      (aeval (monomialCurve (Polynomial.C ∘ φ b.1) c) p).eval (Polynomial.C b.2) =
        Polynomial.C (b.2 ^ a * u b) *
          ∏ i, (Polynomial.X - Polynomial.C (b.2 ^ e i * w i b))) :
    ∀ᶠ y in 𝓝[U] x,
      p.lazardExponent (Polynomial.C ∘ φ y) = p.lazardExponent (Polynomial.C ∘ φ x) := by
  classical
  have hdata := hu.eventually_analyticAt.and
    ((eventually_all.2 fun i ↦ (hw i).eventually_analyticAt).and hfac)
  rw [nhds_prod_eq] at hdata
  have hslice := hdata.curry
  have hunit' : ∀ᶠ b in 𝓝 (x, (0 : 𝕜)),
      u b ≠ 0 ∧ ∀ i, e i < 0 → w i b ≠ 0 := by
    refine (hu.continuousAt.eventually_ne hu0).and (eventually_all.2 fun i ↦ ?_)
    by_cases hi : e i < 0
    · exact ((hw i).continuousAt.eventually_ne (hw0 i hi)).mono fun _ h ↦ fun _ ↦ h
    · exact .of_forall fun _ h ↦ (hi h).elim
  have hunit : ∀ᶠ y in 𝓝 x, u (y, 0) ≠ 0 ∧ ∀ i, e i < 0 → w i (y, 0) ≠ 0 :=
    (continuous_id.prodMk continuous_const).continuousAt.eventually hunit'
  have hweight (y : E) (hcy : TauCeti.IsLazardEvaluator
      {p.lazardExponent (Polynomial.C ∘ φ y), p.lazardExponent (Polynomial.C ∘ φ x)} c)
      (hy : ∀ᶠ t in 𝓝 (0 : 𝕜), AnalyticAt 𝕜 u (y, t) ∧
        (∀ i, AnalyticAt 𝕜 (w i) (y, t)) ∧ (t ≠ 0 →
          (aeval (monomialCurve (Polynomial.C ∘ φ y) c) p).eval (Polynomial.C t) =
            Polynomial.C (t ^ a * u (y, t)) *
              ∏ i, (Polynomial.X - Polynomial.C (t ^ e i * w i (y, t)))))
      (huy : u (y, 0) ≠ 0) (hwy : ∀ i, e i < 0 → w i (y, 0) ≠ 0) :
      (weight c (p.lazardExponent (Polynomial.C ∘ φ y)) : ℤ) =
        a + ∑ i, min (e i) 0 := by
    apply (p.lazardEval_eq_C_mul_prod_of_laurent hp (φ y) c
      (hcy.mono (by simp)) hy.self_of_nhds.1.curry_right huy
      (fun i ↦ (hy.self_of_nhds.2.1 i).curry_right) hwy ?_).1
    filter_upwards [hy.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht ht0
    exact ht.2.2 (by simpa using ht0)
  have hxweight := hweight x (hc.self_of_nhdsWithin hx) hslice.self_of_nhds
    hunit.self_of_nhds.1 hunit.self_of_nhds.2
  filter_upwards [hc, hslice.filter_mono nhdsWithin_le_nhds,
    hunit.filter_mono nhdsWithin_le_nhds] with y hcy hy hunit
  have heq : weight c (p.lazardExponent (Polynomial.C ∘ φ y)) =
      weight c (p.lazardExponent (Polynomial.C ∘ φ x)) := by
    exact_mod_cast (hweight y hcy hy hunit.1 hunit.2).trans hxweight.symm
  rcases lt_trichotomy (toLex (p.lazardExponent (Polynomial.C ∘ φ y)))
      (toLex (p.lazardExponent (Polynomial.C ∘ φ x))) with hlt | he | hgt
  · exact (ne_of_lt (hcy.weight_lt_weight (by simp) hlt) heq).elim
  · exact toLex.injective he
  · exact (ne_of_lt (hcy.weight_lt_weight (by simp) hgt) heq.symm).elim

/-- On a preconnected parameter set, local complete Laurent forms with locally fixed scalar
and branch exponents give one removed Lazard base-exponent vector. The local units and integer
exponents may differ from one neighborhood to another. -/
theorem lazardExponent_eq_of_locally_laurent
    (p : MvPolynomial (Fin n) (Polynomial 𝕜)) (hp : p ≠ 0)
    (φ : E → Fin n → 𝕜) (c : Fin n → ℕ) {U : Set E} (hU : IsPreconnected U)
    (hc : TauCeti.IsLazardEvaluator ((fun y ↦
      p.lazardExponent (Polynomial.C ∘ φ y)) '' U) c)
    (hlocal : ∀ x ∈ U, ∃ (a : ℤ) (e : ι → ℤ) (u : E × 𝕜 → 𝕜)
        (w : ι → E × 𝕜 → 𝕜),
      AnalyticAt 𝕜 u (x, 0) ∧ u (x, 0) ≠ 0 ∧
      (∀ i, AnalyticAt 𝕜 (w i) (x, 0)) ∧ (∀ i, e i < 0 → w i (x, 0) ≠ 0) ∧
      ∀ᶠ b in 𝓝 (x, (0 : 𝕜)), b.2 ≠ 0 →
        (aeval (monomialCurve (Polynomial.C ∘ φ b.1) c) p).eval (Polynomial.C b.2) =
          Polynomial.C (b.2 ^ a * u b) *
            ∏ i, (Polynomial.X - Polynomial.C (b.2 ^ e i * w i b)))
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    p.lazardExponent (Polynomial.C ∘ φ x) = p.lazardExponent (Polynomial.C ∘ φ y) := by
  apply hU.apply_eq_of_eventually_eq _ hx hy
  intro z hz
  obtain ⟨a, e, u, w, hu, hu0, hw, hw0, hfac⟩ := hlocal z hz
  have hc' : ∀ᶠ y in 𝓝[U] z, TauCeti.IsLazardEvaluator
      {p.lazardExponent (Polynomial.C ∘ φ y), p.lazardExponent (Polynomial.C ∘ φ z)} c := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    refine hc.mono ?_
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨Set.mem_image_of_mem _ hy, Set.mem_image_of_mem _ hz⟩
  exact p.eventually_lazardExponent_eq_of_laurent hp φ c hz hc' hu hu0 hw hw0 hfac

end MvPolynomial
