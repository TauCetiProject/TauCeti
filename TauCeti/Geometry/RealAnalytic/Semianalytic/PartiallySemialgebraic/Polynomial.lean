/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAnalytic.Semianalytic.PartiallySemialgebraic
public import Mathlib.Algebra.Polynomial.OfFn

/-!
# Substitution of analytic polynomial families

A semialgebraic condition on a polynomial family and a height remains partially semialgebraic
after substituting analytic coefficient functions of locally bounded degree. This allows
coefficient-space descriptions, such as root counts and ordered-root comparisons, to be used
for analytic families without choosing a constant fiber degree or excluding zero fibers.

The construction uses the finite coefficient representation `Polynomial.ofFn` and
`IsSemialgebraic.isAnalyticCoeffBooleanCombination_preimage_sumElim`.
-/

public section

open Filter Polynomial Set Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : E → ℝ[X]} {x₀ : E} {d : ℕ}

/-- A semialgebraic condition on a finite coefficient tuple and a height has partially
semialgebraic descriptions for analytic coefficient families of locally bounded degree.
Only the coefficients through the local degree bound need
be analytic. The description is uniform over the entire height fiber. -/
theorem partiallySemialgebraicAt_polynomial_condition
    (Φ : ℝ[X] → ℝ → Prop)
    (hΦ : IsSemialgebraic {v : (Fin (d + 1) ⊕ Unit) → ℝ |
      Φ (Polynomial.ofFn (d + 1) (fun i ↦ v (.inl i))) (v (.inr ()))})
    (hF : ∀ i ≤ d, AnalyticAt ℝ (fun x ↦ (F x).coeff i) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).natDegree ≤ d) :
    PartiallySemialgebraicAt {p : E × (Unit → ℝ) | Φ (F p.1) (p.2 ())} x₀ := by
  classical
  let c : E → Fin (d + 1) → ℝ := fun x i ↦ (F x).coeff i
  have hc : AnalyticAt ℝ c x₀ := AnalyticAt.pi fun i ↦ hF i (by omega)
  obtain ⟨U, hU, hcU⟩ := hc.exists_mem_nhds_analyticOnNhd
  have hS := hΦ.isAnalyticCoeffBooleanCombination_preimage_sumElim
    (c := c) (fun i x hx ↦
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) ↦ ℝ) i).analyticAt _).comp
        (hcU x hx))
  have hs := partiallySemialgebraicAt_def.2 ⟨U, hU, _, hS, rfl⟩
  apply hs.congr hdeg
  have hP (x : E) (hx : (F x).natDegree ≤ d) :
      Polynomial.ofFn (d + 1) (c x) = F x :=
    Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
  ext p
  simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, and_congr_left_iff]
  intro hp
  simp only [Sum.elim_inr, Sum.elim_inl]
  rw [hP p.1 hp]

end TauCeti
