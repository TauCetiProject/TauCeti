/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Basic
public import TauCeti.NumberTheory.LocalField.RootCount.Fibre

/-!
# The local fibre count for counted subextensions

These `IntermediateField` theorems specialize the root-ball criterion to totally ramified
subextensions of a fixed separable closure. They install each finite subextension's canonical
local-field structures, so callers supply only membership in `totallyRamifiedOfDegree`.

For a uniformizer `ξ`, a monic degree-`n` polynomial `g`, and radius order `r > d`, where
`d` is the discriminant exponent, the ball `v_L(z - ξ) ≥ r` contains a root precisely when
`v_L(g(ξ)) ≥ r + d`, and that root is unique. This criterion supplies the local fibres used to
integrate the root count of Eisenstein polynomials.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, Lemma 1.
-/

public section

open ValuativeRel Polynomial IsDiscreteValuationRing

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

end TauCeti
