/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.Elliptic
import TauCeti.Analysis.Pseudodifferential.Manifold.Composition
import TauCeti.Analysis.Pseudodifferential.Manifold.SymbolQuantization

/-!
# Inverting elliptic operators up to lower order on a compact manifold

Let `P` be an elliptic classical pseudodifferential operator of order `m` on a compact manifold `M`
modelled on `ℝⁿ` (`TauCeti.IsClassicalElliptic`). Its principal symbol `σ_m(P)` vanishes at no
nonzero covector, so `1 / σ_m(P)` is a smooth positively homogeneous function of degree `-m` on the
cotangent bundle (`TauCeti.inv_mem_homogeneousCotangentSymbols`). On a compact manifold it is the
principal symbol of an operator `Q` of order `-m`
(`TauCeti.classicalPrincipalSymbolLinearMap_surjective`). Principal symbols are multiplicative
(`TauCeti.classicalPrincipalSymbol_comp`), so `P ∘ Q` and `Q ∘ P` have principal symbol `1`, the
principal symbol of the identity (`TauCeti.classicalPrincipalSymbol_id`). By the principal symbol
exact sequence (`TauCeti.classicalPrincipalSymbol_eq_zero_iff`), `P ∘ Q - 1` and `Q ∘ P - 1` have
order `-1`
(`TauCeti.IsClassicalElliptic.exists_comp_sub_id_mem_classicalPseudodifferentialOperators`).

This is the first step of the parametrix construction (Taylor, Lecture I, (4.1)–(4.6)): with
`R = 1 - P ∘ Q` of order `-1`, the operators `Q (1 + R + ⋯ + R ^ (N - 1))` invert `P` on the right
up to `R ^ N`, of order `-N`, and an asymptotic sum of the series is a parametrix modulo operators
of order `-∞`.

## Main results

* `TauCeti.IsClassicalElliptic.exists_comp_sub_id_mem_classicalPseudodifferentialOperators`: an
  elliptic classical pseudodifferential operator `P` of order `m` on a compact manifold has an
  inverse `Q` of order `-m`, with principal symbol `1 / σ_m(P)`, up to operators of order `-1` on
  both sides.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §4.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] {m : ℝ}
  {P Q : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}

/-- If the principal symbols of `P` of order `m` and of `Q` of order `-m` are inverse at every
nonzero covector, then `P ∘ Q - 1` has order `-1`. -/
private theorem comp_sub_id_mem_classicalPseudodifferentialOperators_of_mul_eq_one
    {m' : ℝ} (hP : P ∈ classicalPseudodifferentialOperators m)
    (hQ : Q ∈ classicalPseudodifferentialOperators m') (hm : m + m' = 0)
    (h : ∀ x ξ, ξ ≠ 0 → classicalPrincipalSymbol m P x ξ * classicalPrincipalSymbol m' Q x ξ = 1) :
    P ∘ₗ Q - LinearMap.id ∈ classicalPseudodifferentialOperators (-1) := by
  have hPQ := comp_mem_classicalPseudodifferentialOperators hP hQ
  rw [hm] at hPQ
  rw [← zero_sub]
  refine (classicalPrincipalSymbol_eq_zero_iff
    (sub_mem hPQ id_mem_classicalPseudodifferentialOperators)).1 fun x ξ ↦ ?_
  rcases eq_or_ne ξ 0 with rfl | hξ
  · exact classicalPrincipalSymbol_zero_covector x
  have hσ := classicalPrincipalSymbol_comp hP hQ x ξ
  rw [hm] at hσ
  rw [classicalPrincipalSymbol_sub hPQ id_mem_classicalPseudodifferentialOperators, hσ,
    h x ξ hξ, classicalPrincipalSymbol_id x hξ, sub_self]

/-- **An inverse up to order `-1`.** On a compact manifold, an elliptic classical
pseudodifferential operator `P` of order `m` has an inverse up to operators of order `-1`: there is
a classical pseudodifferential operator `Q` of order `-m`, with principal symbol `1 / σ_m(P)`, such
that `P ∘ Q - 1` and `Q ∘ P - 1` are classical pseudodifferential operators of order `-1`. -/
theorem IsClassicalElliptic.exists_comp_sub_id_mem_classicalPseudodifferentialOperators
    [CompactSpace M] (hP : P ∈ classicalPseudodifferentialOperators m)
    (hPe : IsClassicalElliptic m P) :
    ∃ Q ∈ classicalPseudodifferentialOperators (-m),
      (∀ x ξ, classicalPrincipalSymbol (-m) Q x ξ = (classicalPrincipalSymbol m P x ξ)⁻¹) ∧
      P ∘ₗ Q - LinearMap.id ∈ classicalPseudodifferentialOperators (-1) ∧
      Q ∘ₗ P - LinearMap.id ∈ classicalPseudodifferentialOperators (-1) := by
  have hσP (x : M) : ∀ ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ, ξ ≠ 0 →
      classicalPrincipalSymbol m P x ξ ≠ 0 :=
    isClassicalEllipticAt_iff.1 (isClassicalElliptic_iff.1 hPe x)
  obtain ⟨⟨Q, hQ⟩, hQs⟩ := classicalPrincipalSymbolLinearMap_surjective
    ⟨_, inv_mem_homogeneousCotangentSymbols classicalPrincipalSymbol_mem_homogeneousCotangentSymbols
      hσP⟩
  have hσQ (x : M) (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
      classicalPrincipalSymbol (-m) Q x ξ = (classicalPrincipalSymbol m P x ξ)⁻¹ :=
    by simpa only [coe_classicalPrincipalSymbolLinearMap_apply] using
      congrFun (congrFun (congrArg Subtype.val hQs) x) ξ
  refine ⟨Q, hQ, hσQ,
    comp_sub_id_mem_classicalPseudodifferentialOperators_of_mul_eq_one hP hQ (add_neg_cancel m)
      fun x ξ hξ ↦ ?_,
    comp_sub_id_mem_classicalPseudodifferentialOperators_of_mul_eq_one hQ hP (neg_add_cancel m)
      fun x ξ hξ ↦ ?_⟩
  · rw [hσQ, mul_inv_cancel₀ (hσP x ξ hξ)]
  · rw [hσQ, inv_mul_cancel₀ (hσP x ξ hξ)]

end TauCeti
