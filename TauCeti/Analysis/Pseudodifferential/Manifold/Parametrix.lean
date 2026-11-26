/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.Elliptic
public import TauCeti.Analysis.Pseudodifferential.Manifold.Smoothing
import Mathlib.Algebra.Ring.GeomSum
import TauCeti.Analysis.Pseudodifferential.Manifold.Composition
import TauCeti.Analysis.Pseudodifferential.Manifold.SymbolQuantization
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact

/-!
# Parametrices of elliptic operators on a manifold

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
operators of order `-1`.

**The Neumann series.** On a compact manifold, with `R = 1 - P Q₀` and `L = 1 - Q₀ P`, both of
order `-1` since the principal symbol of a composition is the product of the principal symbols
(`TauCeti.classicalPrincipalSymbol_comp`) and that of the identity is `1`
(`TauCeti.classicalPrincipalSymbol_id`), the operator `Q = Q₀ (1 + R + ⋯ + R^{N-1})` satisfies
`P Q = 1 - R^N`. Since `Q₀ R = L Q₀`, also `Q = (1 + L + ⋯ + L^{N-1}) Q₀`, and `Q P = 1 - L^N`.
The powers `R^N` and `L^N` have order `-N` (`TauCeti.pow_mem_classicalPseudodifferentialOperators`).
So for every `N : ℕ` an elliptic `P` of order `m` has an operator `Q` of order `-m` with
`P ∘ Q - 1` and `Q ∘ P - 1` of order `-N`
(`TauCeti.IsClassicalElliptic.exists_comp_sub_id_mem_classicalPseudodifferentialOperators`).
Operators of negative order are compact between Sobolev spaces of a compact manifold, so these
parametrices are what makes an elliptic operator Fredholm. A parametrix modulo operators of order
`-∞` is the asymptotic sum of the full Neumann series `Q₀ ∑ R^k`, whose terms `Q₀ R^k` have order
`-m - k`; this needs asymptotic summation of operators on `M` and is not done here.

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
* `TauCeti.IsClassicalElliptic.exists_comp_sub_id_mem_classicalPseudodifferentialOperators`: an
  elliptic classical pseudodifferential operator of order `m` on a compact manifold has, for every
  `N : ℕ`, a two-sided parametrix of order `-m` modulo operators of order `-N`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1 (parametrices
  of elliptic operators, and the discussion after Definition 18.1.20).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §4,
  (4.1)–(4.6).
* R. Melrose, *Introduction to Microlocal Analysis*, §5.3.-/

public section

open Filter Finset Set
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
/-! ### Parametrices modulo operators of any finite order -/

/-- **The Neumann series.** If `Q` of order `-m` inverts `P` modulo operators of order `-1` on
both sides, then for every `N` the operator `Q (1 + R + ⋯ + R^{N-1})`, with `R = 1 - P Q`, inverts
`P` modulo operators of order `-N` on both sides. -/
private theorem exists_comp_sub_id_mem_of_comp_sub_id_mem_neg_one
    (hQ : Q ∈ classicalPseudodifferentialOperators (-m))
    (hPQ : P ∘ₗ Q - LinearMap.id ∈ classicalPseudodifferentialOperators (-1))
    (hQP : Q ∘ₗ P - LinearMap.id ∈ classicalPseudodifferentialOperators (-1)) (N : ℕ) :
    ∃ Q' ∈ classicalPseudodifferentialOperators (-m),
      P ∘ₗ Q' - LinearMap.id ∈ classicalPseudodifferentialOperators (-N) ∧
      Q' ∘ₗ P - LinearMap.id ∈ classicalPseudodifferentialOperators (-N) := by
  simp only [← Module.End.mul_eq_comp, ← Module.End.one_eq_id] at hPQ hQP ⊢
  -- `R = 1 - P Q` and `L = 1 - Q P` have order `-1`, and `Q R = L Q`.
  set R := 1 - P * Q
  set L := 1 - Q * P
  have hR : R ∈ classicalPseudodifferentialOperators (-1) := by simpa [R] using neg_mem hPQ
  have hL : L ∈ classicalPseudodifferentialOperators (-1) := by simpa [L] using neg_mem hQP
  have hQR : SemiconjBy Q R L := by
    simp only [SemiconjBy, R, L, mul_sub, sub_mul, mul_one, one_mul, mul_assoc]
  -- The powers of an operator of order `-1` have order `-k`.
  have hpow {A} (hA : A ∈ classicalPseudodifferentialOperators (n := n) (M := M) (-1)) (k : ℕ) :
      A ^ k ∈ classicalPseudodifferentialOperators (-k) := by
    simpa using pow_mem_classicalPseudodifferentialOperators hA k
  refine ⟨Q * ∑ k ∈ range N, R ^ k, ?_, ?_, ?_⟩
  · rw [mul_sum]
    refine Submodule.sum_mem _ fun k _ ↦ classicalPseudodifferentialOperators_le
      (m' := -m + -k) k (by ring) ?_
    rw [Module.End.mul_eq_comp]
    exact comp_mem_classicalPseudodifferentialOperators hQ
      (hpow hR k)
  · rw [← mul_assoc, show P * Q = 1 - R by simp [R], mul_neg_geom_sum, sub_sub_cancel_left]
    exact neg_mem (hpow hR N)
  · rw [mul_sum, sum_congr rfl fun k _ ↦ (hQR.pow_right k).eq, ← sum_mul, mul_assoc,
      show Q * P = 1 - L by simp [L], geom_sum_mul_neg, sub_sub_cancel_left]
    exact neg_mem (hpow hL N)

/-- **Inverting the principal symbol.** On a compact manifold, an elliptic classical
pseudodifferential operator `P` of order `m` has an inverse modulo operators of order `-1`: an
operator `Q` of order `-m` with principal symbol `σ_m(P)⁻¹`. -/
private theorem IsClassicalElliptic.exists_comp_sub_id_mem_neg_one [CompactSpace M]
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

/-- **Parametrices of elliptic operators.** On a compact manifold `M`, let `P` be a classical
pseudodifferential operator of order `m` that is elliptic: its principal symbol vanishes at no
nonzero covector. For every `N : ℕ` there is a classical pseudodifferential operator `Q` of order
`-m` that inverts `P` modulo operators of order `-N` on both sides: `P ∘ Q - 1` and `Q ∘ P - 1`
are classical pseudodifferential operators of order `-N`. -/
theorem IsClassicalElliptic.exists_comp_sub_id_mem_classicalPseudodifferentialOperators
    [CompactSpace M] (hP : P ∈ classicalPseudodifferentialOperators m)
    (hPe : IsClassicalElliptic m P) (N : ℕ) :
    ∃ Q ∈ classicalPseudodifferentialOperators (-m),
      P ∘ₗ Q - LinearMap.id ∈ classicalPseudodifferentialOperators (-N) ∧
      Q ∘ₗ P - LinearMap.id ∈ classicalPseudodifferentialOperators (-N) := by
  obtain ⟨Q, hQ, hPQ, hQP⟩ := hPe.exists_comp_sub_id_mem_neg_one hP
  exact exists_comp_sub_id_mem_of_comp_sub_id_mem_neg_one hQ hPQ hQP N

end TauCeti
