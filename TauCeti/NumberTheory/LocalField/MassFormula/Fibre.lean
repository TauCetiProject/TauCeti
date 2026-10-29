/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Eisenstein.Fibre
public import TauCeti.NumberTheory.LocalField.MassFormula.Basic

/-!
# The local fibre count for members of `σ_K(n)`

Let `L ∈ σ_K(n)` be a totally ramified subextension of degree `n` of `SeparableClosure K`, with
discriminant exponent `d = L.discriminantExponent`, and let `ξ` be a uniformizer of `L`. For a
monic polynomial `g` of degree `n` over `𝒪[K]` and a radius order `r ≥ d + n`, the ball
`v_L(z - ξ) ≥ r` contains a root of `g` if and only if `v_L(g(ξ)) ≥ r + d`, and then exactly one.
At `r = n ρ`, with `d + n ≤ n ρ`, the ball is the cube `ξ + π ^ ρ 𝒪[L]`.

This transports `TauCeti.IsTotallyRamified.existsUnique_isRoot_le_addVal_iff` to the setting of
Serre's mass formula. The subextension `L` carries no valuation of its own; the statements install
the canonical local-field structure `finiteIntermediateFieldValuativeRel`,
`finiteIntermediateFieldTopology` on it, so a caller supplies only membership in `σ_K(n)`.
The local fibres described here are the pieces over which the root count of the Eisenstein
polynomials of degree `n` is integrated.

## Main results

* `IntermediateField.existsUnique_isRoot_le_addVal_iff`: for `L ∈ σ_K(n)`, the ball
  `v_L(z - ξ) ≥ r` contains exactly one root of `g` if and only if `v_L(g(ξ)) ≥ r + d`.
* `IntermediateField.exists_isRoot_le_addVal_iff`: its existence form.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, Lemma 1.
-/

public section

open ValuativeRel Polynomial IsDiscreteValuationRing

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **The local fibre count for `σ_K(n)`** (Serre's Lemma 1). For `L ∈ σ_K(n)` with its canonical
local-field structure, a uniformizer `ξ` of `L`, a monic `g` of degree `n` over `𝒪[K]` and
`r ≥ d + n`, where `d` is the discriminant exponent of `L`, the ball `v_L(z - ξ) ≥ r` contains
exactly one root of `g` if and only if `v_L(g(ξ)) ≥ r + d`. -/
theorem _root_.IntermediateField.existsUnique_isRoot_le_addVal_iff {n : ℕ}
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n) :
    letI := (mem_totallyRamifiedOfDegree_iff.1 hL).2.finite
    letI := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
    letI := finiteIntermediateFieldTopology K (SeparableClosure K) L
    haveI := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
    haveI := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
    ∀ {ξ : 𝒪[L]}, Irreducible ξ → ∀ {g : 𝒪[K][X]}, g.Monic → g.natDegree = n →
      ∀ {r : ℕ}, L.discriminantExponent + n ≤ r →
        ((∃! z : 𝒪[L], aeval z g = 0 ∧ (r : ℕ∞) ≤ addVal 𝒪[L] (z - ξ)) ↔
          ((r + L.discriminantExponent : ℕ) : ℕ∞) ≤ addVal 𝒪[L] (aeval ξ g)) := by
  obtain ⟨hdeg, htr⟩ := mem_totallyRamifiedOfDegree_iff.1 hL
  let _ := htr.finite
  let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
  let _ := finiteIntermediateFieldTopology K (SeparableClosure K) L
  have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
  have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
  intro ξ hξ g hg hgdeg r hr
  have htr' := (IntermediateField.isTotallyRamified_iff L).1 htr
  have he := (isTotallyRamified_iff_ramificationIndex_eq_finrank K L).1 htr'
  rw [IntermediateField.discriminantExponent_eq] at hr ⊢
  exact htr'.existsUnique_isRoot_le_addVal_iff hξ hg (hgdeg.trans (he.trans hdeg).symm)
    (by rwa [he, hdeg])

/-- **The local fibre count for `σ_K(n)`, existence form.** Under the hypotheses of
`IntermediateField.existsUnique_isRoot_le_addVal_iff`, the ball `v_L(z - ξ) ≥ r` contains a root
of `g` if and only if `v_L(g(ξ)) ≥ r + d`; that root is then unique. -/
theorem _root_.IntermediateField.exists_isRoot_le_addVal_iff {n : ℕ}
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n) :
    letI := (mem_totallyRamifiedOfDegree_iff.1 hL).2.finite
    letI := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
    letI := finiteIntermediateFieldTopology K (SeparableClosure K) L
    haveI := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
    haveI := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
    ∀ {ξ : 𝒪[L]}, Irreducible ξ → ∀ {g : 𝒪[K][X]}, g.Monic → g.natDegree = n →
      ∀ {r : ℕ}, L.discriminantExponent + n ≤ r →
        ((∃ z : 𝒪[L], aeval z g = 0 ∧ (r : ℕ∞) ≤ addVal 𝒪[L] (z - ξ)) ↔
          ((r + L.discriminantExponent : ℕ) : ℕ∞) ≤ addVal 𝒪[L] (aeval ξ g)) := by
  obtain ⟨hdeg, htr⟩ := mem_totallyRamifiedOfDegree_iff.1 hL
  let _ := htr.finite
  let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
  let _ := finiteIntermediateFieldTopology K (SeparableClosure K) L
  have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
  have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
  intro ξ hξ g hg hgdeg r hr
  have htr' := (IntermediateField.isTotallyRamified_iff L).1 htr
  have he := (isTotallyRamified_iff_ramificationIndex_eq_finrank K L).1 htr'
  rw [IntermediateField.discriminantExponent_eq] at hr ⊢
  exact htr'.exists_isRoot_le_addVal_iff hξ hg (hgdeg.trans (he.trans hdeg).symm)
    (by rwa [he, hdeg])

end TauCeti
