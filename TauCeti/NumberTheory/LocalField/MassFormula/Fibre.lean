/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Basic
public import TauCeti.NumberTheory.LocalField.RootCount.Volume

/-!
# The local fibre count for counted subextensions

These `IntermediateField` theorems specialize the root-ball criterion to totally ramified
subextensions of a fixed separable closure. They install each finite subextension's canonical
local-field structures, so callers supply only membership in `totallyRamifiedOfDegree`.

For a uniformizer `ξ`, a monic degree-`n` polynomial `g`, and radius order `r > d`, where
`d` is the discriminant exponent, the ball `v_L(z - ξ) ≥ r` contains a root precisely when
`v_L(g(ξ)) ≥ r + d`, and that root is unique. This criterion supplies the local fibres used to
integrate the root count of Eisenstein polynomials. For a left-invariant measure on the
coefficient space normalized on the integer box, the fibre over such a ball has volume
`q ^ (-(r + d))`, where `q` is the residue cardinality of `K`.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, Lemma 1 and §3.
-/

public section

open ValuativeRel Polynomial IsDiscreteValuationRing MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

private theorem fibre_criteria {n : ℕ}
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n) :
    letI := (mem_totallyRamifiedOfDegree_iff.1 hL).2.finite
    letI := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
    letI := finiteIntermediateFieldTopology K (SeparableClosure K) L
    haveI := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
    haveI := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
    ∀ {ξ : 𝒪[L]}, Irreducible ξ → ∀ {g : 𝒪[K][X]}, g.Monic → g.natDegree = n →
      ∀ {r : ℕ}, L.discriminantExponent < r →
        (((∃ z : 𝒪[L], aeval z g = 0 ∧ (r : ℕ∞) ≤ addVal 𝒪[L] (z - ξ)) ↔
            ((r + L.discriminantExponent : ℕ) : ℕ∞) ≤ addVal 𝒪[L] (aeval ξ g)) ∧
          ((∃! z : 𝒪[L], aeval z g = 0 ∧ (r : ℕ∞) ≤ addVal 𝒪[L] (z - ξ)) ↔
            ((r + L.discriminantExponent : ℕ) : ℕ∞) ≤ addVal 𝒪[L] (aeval ξ g))) := by
  have hL' := mem_totallyRamifiedOfDegree_iff.1 hL
  let _ := hL'.2.finite
  let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
  let _ := finiteIntermediateFieldTopology K (SeparableClosure K) L
  have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
  have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
  intro ξ hξ g hg hdeg r hr
  have htr := (IntermediateField.isTotallyRamified_iff L).1 hL'.2
  have he := (isTotallyRamified_iff_ramificationIndex_eq_finrank K L).1 htr
  have hdeg' := hdeg.trans (he.trans hL'.1).symm
  rw [IntermediateField.discriminantExponent_eq] at hr ⊢
  exact ⟨htr.exists_isRoot_le_addVal_iff hξ hg hdeg' hr,
    htr.existsUnique_isRoot_le_addVal_iff hξ hg hdeg' hr⟩

/-- The local fibre criterion for a counted subextension, using its canonical local-field
structures. No topology or valuation on the subextension is supplied by the caller. -/
theorem _root_.IntermediateField.exists_isRoot_le_addVal_iff {n : ℕ}
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n) :
    letI := (mem_totallyRamifiedOfDegree_iff.1 hL).2.finite
    letI := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
    letI := finiteIntermediateFieldTopology K (SeparableClosure K) L
    haveI := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
    haveI := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
    ∀ {ξ : 𝒪[L]}, Irreducible ξ → ∀ {g : 𝒪[K][X]}, g.Monic → g.natDegree = n →
      ∀ {r : ℕ}, L.discriminantExponent < r →
        ((∃ z : 𝒪[L], aeval z g = 0 ∧ (r : ℕ∞) ≤ addVal 𝒪[L] (z - ξ)) ↔
          ((r + L.discriminantExponent : ℕ) : ℕ∞) ≤ addVal 𝒪[L] (aeval ξ g)) := by
  intro ξ hξ g hg hdeg r hr
  exact (fibre_criteria hL hξ hg hdeg hr).1

/-- The unique-root form of the local fibre criterion for a counted subextension, with
its canonical local-field structures. -/
theorem _root_.IntermediateField.existsUnique_isRoot_le_addVal_iff {n : ℕ}
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n) :
    letI := (mem_totallyRamifiedOfDegree_iff.1 hL).2.finite
    letI := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
    letI := finiteIntermediateFieldTopology K (SeparableClosure K) L
    haveI := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
    haveI := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
    ∀ {ξ : 𝒪[L]}, Irreducible ξ → ∀ {g : 𝒪[K][X]}, g.Monic → g.natDegree = n →
      ∀ {r : ℕ}, L.discriminantExponent < r →
        ((∃! z : 𝒪[L], aeval z g = 0 ∧ (r : ℕ∞) ≤ addVal 𝒪[L] (z - ξ)) ↔
          ((r + L.discriminantExponent : ℕ) : ℕ∞) ≤ addVal 𝒪[L] (aeval ξ g)) := by
  intro ξ hξ g hg hdeg r hr
  exact (fibre_criteria hL hξ hg hdeg hr).2

open TauCeti.Polynomial (monicOfCoeff) in
/-- **The volume of a local fibre** for a counted subextension `L ∈ σ_K(n)`, with its canonical
local-field structures. For a uniformizer `ξ` of `L` and `d < r`, where `d` is the discriminant
exponent, and a left-invariant measure on `Fin n → K` normalized on the integer box, the monic
polynomials of degree `n` over `𝒪[K]` having a root in the ball `v_L(z - ξ) ≥ r`, identified with
their lower coefficients, have volume `q ^ (-(r + d))`, where `q = Nat.card 𝓀[K]`. -/
theorem _root_.IntermediateField.measure_image_setOf_exists_aeval_monicOfCoeff_eq_zero_le_addVal
    {n : ℕ} {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n) :
    letI := (mem_totallyRamifiedOfDegree_iff.1 hL).2.finite
    letI := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
    letI := finiteIntermediateFieldTopology K (SeparableClosure K) L
    haveI := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
    haveI := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
    ∀ [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)] (μ : Measure (Fin n → K))
      [μ.IsAddLeftInvariant], μ (integerBox K (Fin n)) = 1 →
      ∀ {ξ : 𝒪[L]}, Irreducible ξ → ∀ {r : ℕ}, L.discriminantExponent < r →
        μ ((fun c : Fin n → 𝒪[K] ↦ fun i ↦ (c i : K)) ''
            {c | ∃ z : 𝒪[L], aeval z (monicOfCoeff c) = 0 ∧ (r : ℕ∞) ≤ addVal 𝒪[L] (z - ξ)}) =
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (r + L.discriminantExponent) := by
  have hL' := mem_totallyRamifiedOfDegree_iff.1 hL
  let _ := hL'.2.finite
  let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
  let _ := finiteIntermediateFieldTopology K (SeparableClosure K) L
  have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
  have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
  intro _ _ μ _ hμ ξ hξ r hr
  have htr := (IntermediateField.isTotallyRamified_iff L).1 hL'.2
  have hn := ((isTotallyRamified_iff_ramificationIndex_eq_finrank K L).1 htr).trans hL'.1
  rw [IntermediateField.discriminantExponent_eq] at hr ⊢
  exact μ.measure_image_setOf_exists_aeval_monicOfCoeff_eq_zero_le_addVal htr hμ hξ hn hr

end TauCeti
