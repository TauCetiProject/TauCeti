/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.Elliptic
public import TauCeti.Analysis.Pseudodifferential.Manifold.Smoothing
import TauCeti.Analysis.Pseudodifferential.Manifold.SymbolQuantization
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact

/-!
# Toward parametrices of elliptic operators on a manifold

Let `P` be a classical pseudodifferential operator of order `m` on a manifold `M` modelled on
`ℝⁿ` (`TauCeti.classicalPseudodifferentialOperators`). A **parametrix** of `P` is an operator `Q`
inverting `P` modulo the operators of order `-∞` (`TauCeti.smoothingPseudodifferentialOperators`):
`Q ∘ P - 1` and `P ∘ Q - 1` have order `-∞`. This file proves two facts on which the construction
of a parametrix of an elliptic operator rests.

**Left and right parametrices agree.** If `L` is a left parametrix and `R` a right parametrix of
`P`, both classical pseudodifferential operators, then `L - R` has order `-∞`
(`TauCeti.sub_mem_smoothingPseudodifferentialOperators_of_comp_sub_id`), because

`L - R = (L ∘ P - 1) ∘ R - L ∘ (P ∘ R - 1)`

and the operators of order `-∞` form a two-sided ideal
(`TauCeti.comp_mem_smoothingPseudodifferentialOperators_of_left`,
`TauCeti.comp_mem_smoothingPseudodifferentialOperators_of_right`). Consequently each of them is a
two-sided parametrix (`TauCeti.comp_left_sub_id_mem_smoothingPseudodifferentialOperators`,
`TauCeti.right_comp_sub_id_mem_smoothingPseudodifferentialOperators`), and a parametrix is unique
modulo order `-∞`. So a parametrix may be built one side at a time.

**The inverse principal symbol is quantized.** If `P` is elliptic at every point of a compact set
`K` (`TauCeti.IsClassicalEllipticAt`), there is a classical pseudodifferential operator `Q₀` of
order `-m`, elliptic over `K`, whose principal symbol is `σ_m(P)(x, ξ)⁻¹` for `x ∈ K`
(`IsCompact.exists_classicalPrincipalSymbol_eq_inv`). It quantizes the cut-off inverse
`σ(x) σ_m(P)(x, ξ)⁻¹` (`TauCeti.mul_inv_mem_homogeneousCotangentSymbols`) for a smooth cutoff `σ`
equal to `1` near `K` and supported where `P` is elliptic. On a compact manifold an elliptic `P`
thus has an elliptic `Q₀` with `σ_{-m}(Q₀) = σ_m(P)⁻¹` everywhere
(`TauCeti.IsClassicalElliptic.exists_classicalPrincipalSymbol_eq_inv`). This `Q₀` is the first
approximation to a parametrix: the principal symbols of `P ∘ Q₀` and `Q₀ ∘ P` are
`σ_m(P) σ_{-m}(Q₀) = 1` at nonzero covectors, so these compositions differ from the identity by
operators of order `-1`, and a Neumann series in these remainders corrects `Q₀` to a parametrix.

## Main results

* `TauCeti.sub_mem_smoothingPseudodifferentialOperators_of_comp_sub_id`: a left and a right
  parametrix of the same operator differ by an operator of order `-∞`.
* `TauCeti.comp_left_sub_id_mem_smoothingPseudodifferentialOperators`,
  `TauCeti.right_comp_sub_id_mem_smoothingPseudodifferentialOperators`: if an operator has both
  a left parametrix and a right parametrix, each of them is a two-sided parametrix.
* `IsCompact.exists_classicalPrincipalSymbol_eq_inv`: an operator of order `m` elliptic
  over a compact set `K` has an operator of order `-m` elliptic over `K` with the inverse principal
  symbol over `K`.
* `TauCeti.IsClassicalElliptic.exists_classicalPrincipalSymbol_eq_inv`: on a compact manifold, an
  elliptic operator of order `m` has an elliptic operator of order `-m` with the inverse principal
  symbol.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1 (parametrices
  of elliptic operators, and the discussion after Definition 18.1.20).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §4,
  (4.1)–(4.6).
* R. Melrose, *Introduction to Microlocal Analysis*, §5.3.
-/

public section

open Filter Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] {m : ℝ}
  {P L R : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}

/-! ### Left and right parametrices -/

section LeftRight

variable {m' m'' : ℝ} (hL : L ∈ classicalPseudodifferentialOperators m')
  (hR : R ∈ classicalPseudodifferentialOperators m'')
  (hLP : L ∘ₗ P - LinearMap.id ∈ smoothingPseudodifferentialOperators)
  (hPR : P ∘ₗ R - LinearMap.id ∈ smoothingPseudodifferentialOperators)

include hL hR hLP hPR

/-- **Left and right parametrices agree modulo order `-∞`.** If `L` and `R` are classical
pseudodifferential operators such that `L ∘ P - 1` and `P ∘ R - 1` have order `-∞`, then `L - R`
has order `-∞`, since `L - R = (L ∘ P - 1) ∘ R - L ∘ (P ∘ R - 1)`. No hypothesis on `P` is
needed. -/
theorem sub_mem_smoothingPseudodifferentialOperators_of_comp_sub_id :
    L - R ∈ smoothingPseudodifferentialOperators := by
  have h : L - R = (L ∘ₗ P - LinearMap.id) ∘ₗ R - L ∘ₗ (P ∘ₗ R - LinearMap.id) := by
    ext u : 1
    simp
  rw [h]
  exact sub_mem (comp_mem_smoothingPseudodifferentialOperators_of_left hLP hR)
    (comp_mem_smoothingPseudodifferentialOperators_of_right hL hPR)

/-- **A right parametrix is a left parametrix.** If `P` is a classical pseudodifferential operator
with a left parametrix `L` and a right parametrix `R`, then `R ∘ P - 1` has order `-∞`. -/
theorem right_comp_sub_id_mem_smoothingPseudodifferentialOperators
    (hP : P ∈ classicalPseudodifferentialOperators m) :
    R ∘ₗ P - LinearMap.id ∈ smoothingPseudodifferentialOperators := by
  have h : R ∘ₗ P - LinearMap.id = (L ∘ₗ P - LinearMap.id) - (L - R) ∘ₗ P := by
    ext u : 1
    simp
  rw [h]
  exact sub_mem hLP (comp_mem_smoothingPseudodifferentialOperators_of_left
    (sub_mem_smoothingPseudodifferentialOperators_of_comp_sub_id hL hR hLP hPR) hP)

/-- **A left parametrix is a right parametrix.** If `P` is a classical pseudodifferential operator
with a left parametrix `L` and a right parametrix `R`, then `P ∘ L - 1` has order `-∞`. -/
theorem comp_left_sub_id_mem_smoothingPseudodifferentialOperators
    (hP : P ∈ classicalPseudodifferentialOperators m) :
    P ∘ₗ L - LinearMap.id ∈ smoothingPseudodifferentialOperators := by
  have h : P ∘ₗ L - LinearMap.id = (P ∘ₗ R - LinearMap.id) + P ∘ₗ (L - R) := by
    ext u : 1
    simp
  rw [h]
  exact add_mem hPR (comp_mem_smoothingPseudodifferentialOperators_of_right hP
    (sub_mem_smoothingPseudodifferentialOperators_of_comp_sub_id hL hR hLP hPR))

end LeftRight

/-! ### The inverse principal symbol -/

/-- **Quantizing the inverse principal symbol over a compact set.** Let `P` be a classical
pseudodifferential operator of order `m` which is elliptic at every point of a compact set `K`.
Then there is a classical pseudodifferential operator `Q` of order `-m`, elliptic at every point of
`K`, whose principal symbol is the inverse of that of `P` over `K`:
`σ_{-m}(Q)(x, ξ) = σ_m(P)(x, ξ)⁻¹` for `x ∈ K` and every covector `ξ ∈ T*ₓM`.

The operator `Q` quantizes `σ(x) σ_m(P)(x, ξ)⁻¹` for a smooth cutoff `σ` equal to `1` near `K` and
supported in the open set where `P` is elliptic. -/
theorem _root_.IsCompact.exists_classicalPrincipalSymbol_eq_inv {K : Set M} (hK : IsCompact K)
    (hP : ∀ x ∈ K, IsClassicalEllipticAt m P x) :
    ∃ Q ∈ classicalPseudodifferentialOperators (-m), (∀ x ∈ K, IsClassicalEllipticAt (-m) Q x) ∧
      ∀ x ∈ K, ∀ ξ, classicalPrincipalSymbol (-m) Q x ξ = (classicalPrincipalSymbol m P x ξ)⁻¹ := by
  obtain ⟨σ, hσ, hσK, hσc, hσW, -⟩ := hK.exists_contMDiff_one_nhds_tsupport_subset
    𝓘(ℝ, CoordinateSpace n) (isOpen_setOf_isClassicalEllipticAt m P) hP
  obtain ⟨Q, hQ, hQs⟩ := exists_mem_classicalPseudodifferentialOperators_classicalPrincipalSymbol_eq
    (mul_inv_mem_homogeneousCotangentSymbols
      classicalPrincipalSymbol_mem_homogeneousCotangentSymbols hσ
      fun x hx ξ hξ ↦ isClassicalEllipticAt_iff.1 (hσW hx) ξ hξ) hσc
    fun x hx ↦ funext fun ξ ↦ by simp [image_eq_zero_of_notMem_tsupport hx]
  have hQK (x : M) (hx : x ∈ K) (ξ) :
      classicalPrincipalSymbol (-m) Q x ξ = (classicalPrincipalSymbol m P x ξ)⁻¹ := by
    simp [hQs, hσK.self_of_nhdsSet x hx]
  refine ⟨Q, hQ, fun x hx ↦ isClassicalEllipticAt_iff.2 fun ξ hξ ↦ ?_, hQK⟩
  rw [hQK x hx]
  exact inv_ne_zero (isClassicalEllipticAt_iff.1 (hP x hx) ξ hξ)

/-- **Quantizing the inverse principal symbol.** On a compact manifold, an elliptic classical
pseudodifferential operator `P` of order `m` has an elliptic classical pseudodifferential operator
`Q` of order `-m` whose principal symbol is the inverse of that of `P`:
`σ_{-m}(Q)(x, ξ) = σ_m(P)(x, ξ)⁻¹` for every covector `ξ ∈ T*ₓM`. -/
theorem IsClassicalElliptic.exists_classicalPrincipalSymbol_eq_inv [CompactSpace M]
    (hP : IsClassicalElliptic m P) :
    ∃ Q ∈ classicalPseudodifferentialOperators (-m), IsClassicalElliptic (-m) Q ∧
      ∀ x ξ, classicalPrincipalSymbol (-m) Q x ξ = (classicalPrincipalSymbol m P x ξ)⁻¹ := by
  obtain ⟨Q, hQ, hQe, hQs⟩ :=
    isCompact_univ.exists_classicalPrincipalSymbol_eq_inv fun x _ ↦
      isClassicalElliptic_iff.1 hP x
  exact ⟨Q, hQ, isClassicalElliptic_iff.2 fun x ↦ hQe x (mem_univ x), fun x ↦ hQs x (mem_univ x)⟩

end TauCeti
