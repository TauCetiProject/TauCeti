/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.LinearMap
public import TauCeti.Analysis.Pseudodifferential.Conjugation
public import TauCeti.Analysis.Pseudodifferential.Manifold.PrincipalSymbol

/-!
# Complex conjugation of pseudodifferential operators on a manifold

Let `M` be a manifold modelled on `ℝⁿ`. The complex-valued smooth functions on `M` are a star ring
under pointwise complex conjugation, and the **complex conjugate** of a complex-linear operator `P`
on them is the operator `f ↦ star (P (star f))`. This is Mathlib's intrinsic star of linear maps,
`(star (WithConv.toConv P)).ofConv`, which is again complex-linear.

This file shows that the classical pseudodifferential operators of order `m`
(`TauCeti.classicalPseudodifferentialOperators`) are closed under conjugation
(`TauCeti.intrinsicStar_mem_classicalPseudodifferentialOperators_iff`), and that the principal
symbol of the conjugate is

`σ_m(conj P)(x, ξ) = conj (σ_m(P)(x, -ξ))`

(`TauCeti.classicalPrincipalSymbol_intrinsicStar`). In a chart, the conjugate of the compression of
`P` is the compression of its conjugate, since the cutoffs are real
(`OpenPartialHomeomorph.complexChartCompression_intrinsicStar`); by the Euclidean formula
`star (Op(a) (star u)) = Op(b) u` with `b(x, ξ) = conj (a(x, -ξ))`
(`TauCeti.ClassicalSymbol.quantizeSchwartzValue_intrinsicStar`), it is a quantization again.

**Real operators.** An operator commuting with conjugation, `P (star f) = star (P f)`, is exactly
the complexification of a real-linear operator on the real-valued smooth functions
(`ContMDiffMap.exists_complexifyLinearMap_eq_iff`), such as a differential operator. Its principal
symbol satisfies `σ_m(P)(x, -ξ) = conj (σ_m(P)(x, ξ))`
(`TauCeti.classicalPrincipalSymbol_neg_covector_of_isSelfAdjoint`). For instance, in the
angular-frequency convention `σ(∂ⱼ) = i ξⱼ` the principal symbol of the complexification of a real
differential operator of order `k` is `iᵏ p(x, ξ)` with `p` real and homogeneous of degree `k` in
`ξ`, and indeed `iᵏ p(x, -ξ) = conj (iᵏ p(x, ξ))`.

## Main results

* `TauCeti.IsProperlySupported.intrinsicStar`: the conjugate of a properly supported operator is
  properly supported.
* `TauCeti.intrinsicStar_mem_classicalPseudodifferentialOperators_iff`: the conjugate of `P` is a
  classical pseudodifferential operator of order `m` exactly when `P` is; in a chart its symbol is
  the conjugate of the chart symbol of `P`
  (`TauCeti.quantizeSchwartzValue_intrinsicStar_eq_complexChartCompression`).
* `TauCeti.classicalPrincipalSymbol_intrinsicStar`: `σ_m(conj P)(x, ξ) = conj (σ_m(P)(x, -ξ))`.
* `TauCeti.classicalPrincipalSymbol_neg_covector_of_isSelfAdjoint`: an operator equal to its
  conjugate has `σ_m(P)(x, -ξ) = conj (σ_m(P)(x, ξ))`; this applies to the complexifications of
  real operators (`ContMDiffMap.isSelfAdjoint_toConv_complexifyLinearMap`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
-/

public section

noncomputable section

open Set WithConv
open scoped ContDiff Manifold Distributions SchwartzMap Topology

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}

/-! ### Proper support -/

/-- The conjugate of a properly supported operator is properly supported, with the same compact
sets: conjugation does not change supports. -/
theorem IsProperlySupported.intrinsicStar (hP : IsProperlySupported P) :
    IsProperlySupported (star (toConv P)).ofConv := by
  have hsupp (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
      tsupport ⇑(star f) = tsupport f := by
    simp [tsupport, Function.support]
  refine isProperlySupported_iff.2 fun K hK ↦ ?_
  obtain ⟨K', hK', hP₁, hP₂⟩ := isProperlySupported_iff.1 hP K hK
  refine ⟨K', hK', fun f hf ↦ ?_, fun f hf x hx ↦ ?_⟩
  · rw [LinearMap.intrinsicStar_apply, hsupp]
    exact hP₁ _ (by rwa [hsupp])
  · rw [LinearMap.intrinsicStar_apply, ContMDiffMap.star_apply,
      hP₂ _ (hf.mono fun y hy ↦ by simp [hy]) x hx, star_zero]

/-- An operator is properly supported exactly when its conjugate is. -/
@[simp]
theorem isProperlySupported_intrinsicStar_iff :
    IsProperlySupported (star (toConv P)).ofConv ↔ IsProperlySupported P :=
  ⟨fun h ↦ by simpa using h.intrinsicStar, IsProperlySupported.intrinsicStar⟩

variable [T2Space M] {m : ℝ}

/-! ### Classical pseudodifferential operators -/

/-- If the chart compression of `P` by `φ` and `ψ` is `Op(a)` on Schwartz functions, then that of
the conjugate of `P` is the quantization of the conjugate symbol `a.intrinsicStar`. -/
theorem quantizeSchwartzValue_intrinsicStar_eq_complexChartCompression
    {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    {φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)} {a : ClassicalSymbol n ℂ ℂ m}
    (ha : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n),
      quantizeSchwartzValue a.toSymbol.coefficient u x =
        e.complexChartCompression he φ ψ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) x)
    (u : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n) :
    quantizeSchwartzValue a.intrinsicStar.toSymbol.coefficient u x =
      e.complexChartCompression he φ ψ (star (toConv P)).ofConv
        (ContMDiffMap.ofContDiff u (u.smooth ⊤)) x := by
  set v := SchwartzMap.conjPostcompCLM (starL ℂ : ℂ ≃L⋆[ℂ] ℂ).toContinuousLinearMap u
  have hv : ContMDiffMap.ofContDiff v (v.smooth ⊤) =
      star (ContMDiffMap.ofContDiff u (u.smooth ⊤)) := by
    ext y
    simp [v]
  rw [ClassicalSymbol.quantizeSchwartzValue_intrinsicStar, ha, hv,
    OpenPartialHomeomorph.complexChartCompression_intrinsicStar]
  simp

/-- **Conjugation of pseudodifferential operators.** The conjugate `f ↦ star (P (star f))` of a
classical pseudodifferential operator `P` of order `m` is a classical pseudodifferential operator of
order `m`. In a chart, its compression is the quantization of the conjugate
`(x, ξ) ↦ conj (a(x, -ξ))` of the chart symbol `a` of `P`. -/
theorem intrinsicStar_mem_classicalPseudodifferentialOperators
    (hP : P ∈ classicalPseudodifferentialOperators m) :
    (star (toConv P)).ofConv ∈ classicalPseudodifferentialOperators m := by
  rw [mem_classicalPseudodifferentialOperators_iff] at hP ⊢
  refine ⟨hP.1.intrinsicStar, fun e he φ ψ ↦ ?_⟩
  obtain ⟨a, ha⟩ := hP.2 e he φ ψ
  exact ⟨a.intrinsicStar, quantizeSchwartzValue_intrinsicStar_eq_complexChartCompression he ha⟩

/-- An operator is a classical pseudodifferential operator of order `m` exactly when its conjugate
is. -/
@[simp]
theorem intrinsicStar_mem_classicalPseudodifferentialOperators_iff :
    (star (toConv P)).ofConv ∈ classicalPseudodifferentialOperators m ↔
      P ∈ classicalPseudodifferentialOperators m :=
  ⟨fun h ↦ by simpa using intrinsicStar_mem_classicalPseudodifferentialOperators h,
    intrinsicStar_mem_classicalPseudodifferentialOperators⟩

/-! ### The principal symbol -/

variable [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]

/-- **The principal symbol of the conjugate.** The principal symbol of order `m` of the conjugate
`f ↦ star (P (star f))` of `P` at a covector `ξ` is the complex conjugate of the principal symbol of
`P` at `-ξ`:

`σ_m(conj P)(x, ξ) = conj (σ_m(P)(x, -ξ))`.

When `P` is not a classical pseudodifferential operator of order `m`, neither is its conjugate,
and both sides are `0`. -/
@[simp]
theorem classicalPrincipalSymbol_intrinsicStar (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol m (star (toConv P)).ofConv x ξ =
      star (classicalPrincipalSymbol m P x (-ξ)) := by
  by_cases hP : P ∈ classicalPseudodifferentialOperators m
  swap
  · rw [classicalPrincipalSymbol_of_notMem hP, classicalPrincipalSymbol_of_notMem
      (intrinsicStar_mem_classicalPseudodifferentialOperators_iff.not.2 hP), star_zero]
  -- Read both principal symbols in the preferred chart at `x`, with a cutoff equal to `1` at `x`.
  set e := chartAt (CoordinateSpace n) x
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M :=
    IsManifold.chart_mem_maximalAtlas x
  have hx : x ∈ e.source := mem_chart_source _ x
  obtain ⟨χ, -, hχ⟩ := TestFunction.exists_tsupport_subset_apply_eq
    (Ω := ⟨e.target, e.open_target⟩) (n := ⊤) (e.open_target.mem_nhds (e.map_source hx))
    subset_rfl (1 : ℝ)
  obtain ⟨a, ha⟩ := (mem_classicalPseudodifferentialOperators_iff.1 hP).2 e he χ χ
  have h₁ := coefficient_principal_apply_eq_classicalPrincipalSymbol
    (intrinsicStar_mem_classicalPseudodifferentialOperators hP) he χ χ
    (quantizeSchwartzValue_intrinsicStar_eq_complexChartCompression he ha) hx ξ
  have h₂ := coefficient_principal_apply_eq_classicalPrincipalSymbol hP he χ χ ha hx (-ξ)
  rw [ClassicalSymbol.coefficient_principal_intrinsicStar] at h₁
  simp only [hχ, mul_one, Complex.ofReal_one, one_mul] at h₁ h₂
  rw [← h₁, ← h₂]
  simp [ContinuousLinearMap.neg_comp]

/-- **The principal symbol of a real operator.** If `P` commutes with conjugation, as the
complexification of a real operator does, then `σ_m(P)(x, -ξ) = conj (σ_m(P)(x, ξ))`. -/
theorem classicalPrincipalSymbol_neg_covector_of_isSelfAdjoint (hP : IsSelfAdjoint (toConv P))
    (x : M) (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol m P x (-ξ) = star (classicalPrincipalSymbol m P x ξ) := by
  have hP' : (star (toConv P)).ofConv = P := by
    rw [hP.star_eq, ofConv_toConv]
  conv_lhs => rw [← hP']
  rw [classicalPrincipalSymbol_intrinsicStar, neg_neg]

end TauCeti
