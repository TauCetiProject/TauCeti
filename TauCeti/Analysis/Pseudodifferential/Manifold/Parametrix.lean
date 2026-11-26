/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.Elliptic
public import TauCeti.Analysis.Pseudodifferential.Manifold.Smoothing
import TauCeti.Analysis.Pseudodifferential.Manifold.AsymptoticSum
import TauCeti.Analysis.Pseudodifferential.Manifold.Composition
import TauCeti.Analysis.Pseudodifferential.Manifold.SymbolQuantization
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact

/-!
# Parametrices of elliptic operators on a manifold

Let `P` be a classical pseudodifferential operator of order `m` on a manifold `M` modelled on
`ℝⁿ` (`TauCeti.classicalPseudodifferentialOperators`). A **parametrix** of `P` is an operator `Q`
inverting `P` modulo the operators of order `-∞` (`TauCeti.smoothingPseudodifferentialOperators`):
`Q ∘ P - 1` and `P ∘ Q - 1` have order `-∞`. This file shows that on a σ-compact manifold, for
instance a compact one, `P` has a parametrix of order `-m` exactly when it is elliptic
(`TauCeti.isClassicalElliptic_iff_exists_comp_sub_id_mem_smoothingPseudodifferentialOperators`),
and that the principal symbol of a parametrix is `σ_m(P)⁻¹`.

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
equal to `1` near `K` and supported where `P` is elliptic. On a σ-compact manifold every smooth
homogeneous function on the cotangent bundle is a principal symbol
(`TauCeti.classicalPrincipalSymbolLinearMap_surjective`), so an elliptic `P` has an elliptic `Q₀`
with `σ_{-m}(Q₀) = σ_m(P)⁻¹` everywhere
(`TauCeti.IsClassicalElliptic.exists_classicalPrincipalSymbol_eq_inv`). This `Q₀` is the first
approximation to a parametrix: the principal symbols of `P ∘ Q₀` and `Q₀ ∘ P` are
`σ_m(P) σ_{-m}(Q₀) = 1` at nonzero covectors, so these compositions differ from the identity by
operators of order `-1` (`TauCeti.classicalPrincipalSymbol_comp`,
`TauCeti.classicalPrincipalSymbol_id`). Conversely, if `Q ∘ P - 1` has order `-1` for some `Q` of
order `-m`, then `σ_{-m}(Q) σ_m(P) = 1` at nonzero covectors, so `P` is elliptic
(`TauCeti.IsClassicalElliptic.of_comp_sub_id_mem`) and `σ_{-m}(Q) = σ_m(P)⁻¹`
(`TauCeti.classicalPrincipalSymbol_eq_inv_of_comp_sub_id_mem`).

**The Neumann series.** With `R = 1 - P Q₀` and `L = 1 - Q₀ P`, both of order `-1`, the operators
`1 - R = P Q₀` and `1 - L = Q₀ P` are invertible modulo order `-∞`
(`TauCeti.exists_one_sub_mul_sub_one_mem_smoothingPseudodifferentialOperators`), by asymptotic sums
`S ∼ ∑ₖ Rᵏ` and `S' ∼ ∑ₖ Lᵏ` of operators on `M`. Then `Q₀ S` is a right parametrix and `S' Q₀` a
left parametrix of `P`, so `Q₀ S` is a parametrix
(`TauCeti.IsClassicalElliptic.exists_comp_sub_id_mem_smoothingPseudodifferentialOperators`). The
remainders also have every finite order `-N`
(`TauCeti.IsClassicalElliptic.exists_comp_sub_id_mem_classicalPseudodifferentialOperators`):
operators of negative order are compact between Sobolev spaces of a compact manifold, so a
parametrix is what makes an elliptic operator Fredholm there.

## Main results

* `TauCeti.sub_mem_smoothingPseudodifferentialOperators_of_comp_sub_id`: a left and a right
  parametrix of the same operator differ by an operator of order `-∞`.
* `TauCeti.comp_left_sub_id_mem_smoothingPseudodifferentialOperators`,
  `TauCeti.right_comp_sub_id_mem_smoothingPseudodifferentialOperators`: if an operator has both
  a left parametrix and a right parametrix, each of them is a two-sided parametrix.
* `IsCompact.exists_classicalPrincipalSymbol_eq_inv`: an operator of order `m` elliptic
  over a compact set `K` has an operator of order `-m` elliptic over `K` with the inverse principal
  symbol over `K`.
* `TauCeti.IsClassicalElliptic.exists_classicalPrincipalSymbol_eq_inv`: on a σ-compact manifold,
  an elliptic operator of order `m` has an elliptic operator of order `-m` with the inverse
  principal symbol.
* `TauCeti.classicalPrincipalSymbol_eq_inv_of_comp_sub_id_mem`,
  `TauCeti.IsClassicalElliptic.of_comp_sub_id_mem`: an operator inverting `P` on the left modulo
  order `-1` has principal symbol `σ_m(P)⁻¹`, and then `P` is elliptic.
* `TauCeti.IsClassicalElliptic.exists_comp_sub_id_mem_smoothingPseudodifferentialOperators`: an
  elliptic classical pseudodifferential operator of order `m` on a σ-compact manifold has a
  two-sided parametrix of order `-m` modulo operators of order `-∞`.
* `TauCeti.isClassicalElliptic_iff_exists_comp_sub_id_mem_smoothingPseudodifferentialOperators`:
  on a σ-compact manifold, an operator is elliptic exactly when it has a parametrix.

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
  {P Q L R : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
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

/-- **Quantizing the inverse principal symbol.** On a σ-compact manifold, for instance a compact
one, an elliptic classical pseudodifferential operator `P` of order `m` has an elliptic classical
pseudodifferential operator `Q` of order `-m` whose principal symbol is the inverse of that of `P`:
`σ_{-m}(Q)(x, ξ) = σ_m(P)(x, ξ)⁻¹` for every covector `ξ ∈ T*ₓM`. -/
theorem IsClassicalElliptic.exists_classicalPrincipalSymbol_eq_inv [SigmaCompactSpace M]
    (hP : IsClassicalElliptic m P) :
    ∃ Q ∈ classicalPseudodifferentialOperators (-m), IsClassicalElliptic (-m) Q ∧
      ∀ x ξ, classicalPrincipalSymbol (-m) Q x ξ = (classicalPrincipalSymbol m P x ξ)⁻¹ := by
  obtain ⟨⟨Q, hQ⟩, hQs⟩ := classicalPrincipalSymbolLinearMap_surjective (n := n) (M := M) (m := -m)
    ⟨_, hP.inv_classicalPrincipalSymbol_mem_homogeneousCotangentSymbols⟩
  have hσ (x : M) (ξ) :
      classicalPrincipalSymbol (-m) Q x ξ = (classicalPrincipalSymbol m P x ξ)⁻¹ :=
    by simpa using congrFun (congrFun (congrArg Subtype.val hQs) x) ξ
  refine ⟨Q, hQ, isClassicalElliptic_iff.2 fun x ↦ isClassicalEllipticAt_iff.2 fun ξ hξ ↦ ?_, hσ⟩
  rw [hσ]
  exact inv_ne_zero (isClassicalEllipticAt_iff.1 (isClassicalElliptic_iff.1 hP x) ξ hξ)

/-! ### Principal symbols of parametrices -/

/-- If `Q ∘ P - 1` has order `-1`, then `σ_{-m}(Q) σ_m(P) = 1` at nonzero covectors, since
`σ_0(Q ∘ P) = σ_0(1) = 1`. -/
private theorem classicalPrincipalSymbol_mul_eq_one_of_comp_sub_id_mem
    (hQ : Q ∈ classicalPseudodifferentialOperators (-m))
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (hQP : Q ∘ₗ P - LinearMap.id ∈ classicalPseudodifferentialOperators (-1)) (x : M)
    {ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ} (hξ : ξ ≠ 0) :
    classicalPrincipalSymbol (-m) Q x ξ * classicalPrincipalSymbol m P x ξ = 1 := by
  have hQP0 : Q ∘ₗ P ∈ classicalPseudodifferentialOperators 0 := by
    simpa using comp_mem_classicalPseudodifferentialOperators hQ hP
  have h := classicalPrincipalSymbol_comp hQ hP x ξ
  rw [neg_add_cancel] at h
  rw [← h, ← sub_add_cancel (classicalPrincipalSymbol 0 (Q ∘ₗ P) x ξ)
    (classicalPrincipalSymbol 0 LinearMap.id x ξ), ← classicalPrincipalSymbol_sub hQP0
    id_mem_classicalPseudodifferentialOperators, classicalPrincipalSymbol_eq_zero_of_mem_sub_one
    (by rwa [zero_sub]), classicalPrincipalSymbol_id x hξ, zero_add]

/-- **The principal symbol of a parametrix.** If `P` has order `m` and `Q` of order `-m` inverts it
on the left modulo operators of order `-1`, then the principal symbol of `Q` is the inverse of
that of `P`: `σ_{-m}(Q)(x, ξ) = σ_m(P)(x, ξ)⁻¹`. This applies to every parametrix, since
operators of order `-∞` have order `-1`. -/
theorem classicalPrincipalSymbol_eq_inv_of_comp_sub_id_mem
    (hQ : Q ∈ classicalPseudodifferentialOperators (-m))
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (hQP : Q ∘ₗ P - LinearMap.id ∈ classicalPseudodifferentialOperators (-1)) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol (-m) Q x ξ = (classicalPrincipalSymbol m P x ξ)⁻¹ := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [classicalPrincipalSymbol_zero_covector]
  · exact eq_inv_of_mul_eq_one_left
      (classicalPrincipalSymbol_mul_eq_one_of_comp_sub_id_mem hQ hP hQP x hξ)

/-- **Operators with a parametrix are elliptic.** If `P` has order `m` and an operator `Q` of order
`-m` inverts it on the left modulo operators of order `-1`, then `P` is elliptic: at a nonzero
covector, `σ_{-m}(Q) σ_m(P) = 1`. -/
theorem IsClassicalElliptic.of_comp_sub_id_mem (hQ : Q ∈ classicalPseudodifferentialOperators (-m))
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (hQP : Q ∘ₗ P - LinearMap.id ∈ classicalPseudodifferentialOperators (-1)) :
    IsClassicalElliptic m P :=
  isClassicalElliptic_iff.2 fun x ↦ isClassicalEllipticAt_iff.2 fun _ hξ ↦
    right_ne_zero_of_mul_eq_one
      (classicalPrincipalSymbol_mul_eq_one_of_comp_sub_id_mem hQ hP hQP x hξ)

/-! ### Parametrices modulo operators of order `-∞` -/

/-- **Inverting the principal symbol.** On a σ-compact manifold, an elliptic classical
pseudodifferential operator `P` of order `m` has an inverse modulo operators of order `-1`: an
operator `Q` of order `-m` with principal symbol `σ_m(P)⁻¹`. -/
private theorem IsClassicalElliptic.exists_comp_sub_id_mem_neg_one [SigmaCompactSpace M]
    (hP : P ∈ classicalPseudodifferentialOperators m) (hPe : IsClassicalElliptic m P) :
    ∃ Q ∈ classicalPseudodifferentialOperators (-m),
      P ∘ₗ Q - LinearMap.id ∈ classicalPseudodifferentialOperators (-1) ∧
      Q ∘ₗ P - LinearMap.id ∈ classicalPseudodifferentialOperators (-1) := by
  have hPe' (x : M) (ξ) (hξ : ξ ≠ 0) : classicalPrincipalSymbol m P x ξ ≠ 0 :=
    isClassicalEllipticAt_iff.1 (isClassicalElliptic_iff.1 hPe x) ξ hξ
  obtain ⟨Q, hQ, -, hσQ⟩ := hPe.exists_classicalPrincipalSymbol_eq_inv
  -- Both products have principal symbol `σ_m(P) σ_m(P)⁻¹ = 1`, that of the identity.
  have key (A : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) (hA : A ∈ classicalPseudodifferentialOperators 0)
      (hσA : ∀ x ξ, classicalPrincipalSymbol 0 A x ξ =
        classicalPrincipalSymbol m P x ξ * (classicalPrincipalSymbol m P x ξ)⁻¹) :
      A - LinearMap.id ∈ classicalPseudodifferentialOperators (-1) := by
    rw [show (-1 : ℝ) = 0 - 1 by norm_num]
    refine sub_mem_classicalPseudodifferentialOperators_of_classicalPrincipalSymbol_eq hA
      id_mem_classicalPseudodifferentialOperators fun x ξ ↦ ?_
    rw [hσA]
    rcases eq_or_ne ξ 0 with rfl | hξ
    · simp
    · rw [mul_inv_cancel₀ (hPe' x ξ hξ), classicalPrincipalSymbol_id x hξ]
  refine ⟨Q, hQ, key _ ?_ fun x ξ ↦ ?_, key _ ?_ fun x ξ ↦ ?_⟩
  · simpa using comp_mem_classicalPseudodifferentialOperators hP hQ
  · have h := classicalPrincipalSymbol_comp hP hQ x ξ
    rwa [add_neg_cancel, hσQ] at h
  · simpa using comp_mem_classicalPseudodifferentialOperators hQ hP
  · have h := classicalPrincipalSymbol_comp hQ hP x ξ
    rwa [neg_add_cancel, hσQ, mul_comm] at h

/-- **Parametrices of elliptic operators.** On a σ-compact manifold `M`, for instance a compact
one, let `P` be a classical pseudodifferential operator of order `m` that is elliptic: its principal
symbol vanishes at no nonzero covector. Then `P` has a **parametrix**: a classical
pseudodifferential operator `Q` of order `-m` that inverts `P` modulo operators of order `-∞` on
both sides, so that `P ∘ Q - 1` and `Q ∘ P - 1` have order `-∞`. Its principal symbol is
`σ_m(P)⁻¹` (`TauCeti.classicalPrincipalSymbol_eq_inv_of_comp_sub_id_mem`), and it is unique modulo
operators of order `-∞` (`TauCeti.sub_mem_smoothingPseudodifferentialOperators_of_comp_sub_id`).

The operator `Q₀` quantizing `σ_m(P)⁻¹` inverts `P` modulo order `-1`; with `R = 1 - P Q₀` and
`L = 1 - Q₀ P`, the Neumann series give `S ∼ ∑ₖ Rᵏ` and `S' ∼ ∑ₖ Lᵏ`, and `Q₀ S` and `S' Q₀` are a
right and a left parametrix. -/
theorem IsClassicalElliptic.exists_comp_sub_id_mem_smoothingPseudodifferentialOperators
    [SigmaCompactSpace M] (hP : P ∈ classicalPseudodifferentialOperators m)
    (hPe : IsClassicalElliptic m P) :
    ∃ Q ∈ classicalPseudodifferentialOperators (-m),
      P ∘ₗ Q - LinearMap.id ∈ smoothingPseudodifferentialOperators ∧
      Q ∘ₗ P - LinearMap.id ∈ smoothingPseudodifferentialOperators := by
  obtain ⟨Q₀, hQ₀, hPQ, hQP⟩ := hPe.exists_comp_sub_id_mem_neg_one hP
  simp only [← Module.End.mul_eq_comp, ← Module.End.one_eq_id] at hPQ hQP ⊢
  -- `R = 1 - P Q₀` and `L = 1 - Q₀ P` have order `-1`; `1 - R = P Q₀` and `1 - L = Q₀ P` are
  -- inverted modulo order `-∞` by `S` on the right and by `S'` on the left.
  obtain ⟨S, hS, hRS, -⟩ := exists_one_sub_mul_sub_one_mem_smoothingPseudodifferentialOperators
    (R := 1 - P * Q₀) (by simpa using neg_mem hPQ)
  obtain ⟨S', hS', -, hS'L⟩ := exists_one_sub_mul_sub_one_mem_smoothingPseudodifferentialOperators
    (R := 1 - Q₀ * P) (by simpa using neg_mem hQP)
  rw [sub_sub_cancel] at hRS hS'L
  have hR : Q₀ * S ∈ classicalPseudodifferentialOperators (-m) := by
    simpa [Module.End.mul_eq_comp] using comp_mem_classicalPseudodifferentialOperators hQ₀ hS
  have hL : S' * Q₀ ∈ classicalPseudodifferentialOperators (-m) := by
    simpa [Module.End.mul_eq_comp] using comp_mem_classicalPseudodifferentialOperators hS' hQ₀
  have hPR : P * (Q₀ * S) - 1 ∈ smoothingPseudodifferentialOperators := by rwa [← mul_assoc]
  have hLP : S' * Q₀ * P - 1 ∈ smoothingPseudodifferentialOperators := by rwa [mul_assoc]
  -- The right parametrix `Q₀ S` is also a left parametrix.
  refine ⟨Q₀ * S, hR, hPR, ?_⟩
  simpa [Module.End.mul_eq_comp, Module.End.one_eq_id] using
    right_comp_sub_id_mem_smoothingPseudodifferentialOperators (L := S' * Q₀) hL hR
      (by simpa [Module.End.mul_eq_comp, Module.End.one_eq_id] using hLP)
      (by simpa [Module.End.mul_eq_comp, Module.End.one_eq_id] using hPR) hP

/-- **Parametrices modulo operators of finite order.** On a σ-compact manifold, an elliptic
classical pseudodifferential operator `P` of order `m` has, for every `N : ℕ`, an operator `Q` of
order `-m` such that `P ∘ Q - 1` and `Q ∘ P - 1` are classical pseudodifferential operators of
order `-N`: the parametrix of
`TauCeti.IsClassicalElliptic.exists_comp_sub_id_mem_smoothingPseudodifferentialOperators`. This is
the form in which a parametrix enters compactness arguments on Sobolev spaces. -/
theorem IsClassicalElliptic.exists_comp_sub_id_mem_classicalPseudodifferentialOperators
    [SigmaCompactSpace M] (hP : P ∈ classicalPseudodifferentialOperators m)
    (hPe : IsClassicalElliptic m P) (N : ℕ) :
    ∃ Q ∈ classicalPseudodifferentialOperators (-m),
      P ∘ₗ Q - LinearMap.id ∈ classicalPseudodifferentialOperators (-N) ∧
      Q ∘ₗ P - LinearMap.id ∈ classicalPseudodifferentialOperators (-N) :=
  let ⟨Q, hQ, hPQ, hQP⟩ := hPe.exists_comp_sub_id_mem_smoothingPseudodifferentialOperators hP
  ⟨Q, hQ, smoothingPseudodifferentialOperators_le_classicalPseudodifferentialOperators _ hPQ,
    smoothingPseudodifferentialOperators_le_classicalPseudodifferentialOperators _ hQP⟩

/-- **Ellipticity is invertibility modulo order `-∞`.** On a σ-compact manifold, a classical
pseudodifferential operator `P` of order `m` is elliptic exactly when it has a parametrix: an
operator `Q` of order `-m` such that `P ∘ Q - 1` and `Q ∘ P - 1` have order `-∞`. -/
theorem isClassicalElliptic_iff_exists_comp_sub_id_mem_smoothingPseudodifferentialOperators
    [SigmaCompactSpace M] (hP : P ∈ classicalPseudodifferentialOperators m) :
    IsClassicalElliptic m P ↔ ∃ Q ∈ classicalPseudodifferentialOperators (-m),
      P ∘ₗ Q - LinearMap.id ∈ smoothingPseudodifferentialOperators ∧
      Q ∘ₗ P - LinearMap.id ∈ smoothingPseudodifferentialOperators :=
  ⟨fun hPe ↦ hPe.exists_comp_sub_id_mem_smoothingPseudodifferentialOperators hP,
    fun ⟨_, hQ, _, hQP⟩ ↦ IsClassicalElliptic.of_comp_sub_id_mem hQ hP
      (smoothingPseudodifferentialOperators_le_classicalPseudodifferentialOperators _ hQP)⟩

end TauCeti
