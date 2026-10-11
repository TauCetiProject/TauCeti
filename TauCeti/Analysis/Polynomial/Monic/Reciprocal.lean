/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Monic.Normalization
public import TauCeti.RingTheory.Polynomial.Resultant.Normalization
public import TauCeti.RingTheory.Polynomial.Resultant.RootCoordinates
import Mathlib.Analysis.Analytic.Polynomial

/-!
# Monic preparation in reciprocal root coordinates

Translate a polynomial family to a nonroot of its central fiber and reverse at the formal
degree. The leading coefficient of the new family is the original value at the translation
center, so it stays nonzero on a neighborhood. Integral normalization gives a monic analytic
family of fixed degree. Its discriminant is the original formal discriminant multiplied by
a nonvanishing power of that value. The original leading coefficient may vanish, and the
original fiber degree may drop.

This preparation supplies monic families for analytic root splitting without imposing an
order condition on the original leading coefficient. Constants are included. Reversal is
taken before specialization; it must not be recomputed at the smaller fiber degree.

## References

* S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
  Springer (1998), Sections 2–3 (reciprocal coordinates in the discriminant theorem).
-/

public section

open Filter Metric Polynomial Set Topology

namespace Polynomial

variable {𝕜 E σ : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Near a fiber that does not vanish at `τ`, the translated formal reversal has an analytic
monic normalization of the original formal degree. Its discriminant is the original formal
discriminant times a nonvanishing power of the value at `τ`. No preservation of the original
fiber degree is required. The center `τ` can be chosen in the real field before complexifying. -/
theorem exists_analytic_monic_reciprocal_normalization
    (p : Polynomial (MvPolynomial σ 𝕜)) {Φ : E → σ → 𝕜} {S : Set E} {x₀ : E} (τ : 𝕜)
    (hS : IsOpen S) (hx₀ : x₀ ∈ S)
    (hΦ : ∀ i, AnalyticOnNhd 𝕜 (fun x ↦ Φ x i) S)
    (hτ : (p.map (MvPolynomial.eval (Φ x₀))).eval τ ≠ 0) :
    ∃ ε > (0 : ℝ), ball x₀ ε ⊆ S ∧ ∃ Q : E → 𝕜[X],
      (∀ i, AnalyticOnNhd 𝕜 (fun x ↦ (Q x).coeff i) (ball x₀ ε)) ∧
      ∀ x ∈ ball x₀ ε,
        (p.map (MvPolynomial.eval (Φ x))).eval τ ≠ 0 ∧
        (Q x).Monic ∧ (Q x).natDegree = p.natDegree ∧
        Q x = ((p.comp (X + C (MvPolynomial.C τ))).reverse.map
          (MvPolynomial.eval (Φ x))).integralNormalization ∧
        (Q x).discr = (p.map (MvPolynomial.eval (Φ x))).eval τ ^
          ((p.natDegree - 1) * (p.natDegree - 2)) * MvPolynomial.eval (Φ x) p.discr := by
  let g := p.comp (X + C (MvPolynomial.C τ))
  let F := fun x ↦ g.reverse.map (MvPolynomial.eval (Φ x))
  let v := fun x ↦ MvPolynomial.eval (Φ x) (g.coeff 0)
  have hv (x) : v x = (p.map (MvPolynomial.eval (Φ x))).eval τ := by
    simp only [v, g, ← taylor_apply, taylor_coeff_zero]
    rw [← eval₂_at_apply, eval_map]
    simp
  have hvA : AnalyticOnNhd 𝕜 v S := by
    simpa only [v, MvPolynomial.aeval_eq_eval] using
      AnalyticOnNhd.aeval_mvPolynomial hΦ (g.coeff 0)
  -- A nonzero value at the translation center fixes the formal reversed degree.
  have hg0 : g.coeff 0 ≠ 0 := by
    intro h
    exact hτ (by rw [← hv]; simp [v, h])
  have hgdeg : g.natDegree = p.natDegree := by simp [g, ← taylor_apply]
  have hrevdeg : g.reverse.natDegree = p.natDegree := by
    rw [reverse_natDegree, natTrailingDegree_eq_zero.2 (.inr hg0), Nat.sub_zero, hgdeg]
  -- Keep that value nonzero on one neighborhood before specializing the reversal.
  have hmem : ∀ᶠ x in 𝓝 x₀, x ∈ S := hS.mem_nhds hx₀
  obtain ⟨ε, hε, hεS⟩ := Metric.eventually_nhds_iff.1
    (hmem.and ((hvA x₀ hx₀).continuousAt.eventually_ne (by rwa [hv])))
  have hlocal (x) (hx : x ∈ ball x₀ ε) : x ∈ S ∧ v x ≠ 0 :=
    hεS (by simpa only [mem_ball, dist_comm] using hx)
  have htop (x) : (F x).coeff p.natDegree = v x := by
    dsimp only [F]
    rw [coeff_map, coeff_reverse, ← hgdeg, revAt_le le_rfl, Nat.sub_self]
  have hdeg (x) (hx : x ∈ ball x₀ ε) : (F x).natDegree = p.natDegree := by
    apply natDegree_eq_of_le_of_coeff_ne_zero (hrevdeg ▸ natDegree_map_le)
    rw [htop]
    exact (hlocal x hx).2
  have hcoeff (i) : AnalyticOnNhd 𝕜 (fun x ↦ (F x).coeff i) (ball x₀ ε) := by
    simp only [F, coeff_map]
    exact (AnalyticOnNhd.aeval_mvPolynomial hΦ (g.reverse.coeff i)).mono
      (fun x hx ↦ (hlocal x hx).1)
  -- Apply analytic integral normalization at the preserved degree.
  obtain ⟨Q, hQ, hQA, hQeq⟩ := TauCeti.exists_analytic_monic_normalization
    (d := p.natDegree) (fun i _ ↦ hcoeff i)
  refine ⟨ε, hε, fun x hx ↦ (hlocal x hx).1, Q, hQA, fun x hx ↦ ?_⟩
  have hFx : F x ≠ 0 := by
    intro h
    apply (hlocal x hx).2
    rw [← htop, h]
    simp
  have hlc : (F x).leadingCoeff = v x := by
    rw [← coeff_natDegree, hdeg x hx, htop]
  have hd : (F x).discr = MvPolynomial.eval (Φ x) p.discr := by
    dsimp only [F]
    rw [discr_map_reverse g _ (hlocal x hx).2]
    simp [g]
  refine ⟨by rw [← hv]; exact (hlocal x hx).2, (hQ x).1, (hQ x).2, hQeq x (hdeg x hx) hFx, ?_⟩
  rw [hQeq x (hdeg x hx) hFx, TauCeti.discr_integralNormalization,
    hlc, hdeg x hx, hd, hv]

end Polynomial
