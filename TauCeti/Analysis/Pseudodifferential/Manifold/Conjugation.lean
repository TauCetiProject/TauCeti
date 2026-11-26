/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.PrincipalSymbol
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Pseudodifferential.Conjugation

/-!
# Complex conjugation of pseudodifferential operators on a manifold

Let `M` be a manifold modelled on `ℝⁿ`. Pseudodifferential operators on `M` act on complex-valued
smooth functions (`TauCeti.classicalPseudodifferentialOperators`), with symbols in the Fourier
convention, so operators on real-valued functions, such as real differential operators, enter
through their complexifications. This file shows that the class is compatible with complex
conjugation, which recovers the real operators.

The **conjugate** of an operator `P` is `Pᶜ : f ↦ conj (P (conj f))`
(`ContMDiffMap.intrinsicConj`). If `P` is a classical pseudodifferential operator of order `m`, so
is `Pᶜ` (`TauCeti.intrinsicConj_mem_classicalPseudodifferentialOperators_iff`), and its principal
symbol is

`σ_m(Pᶜ)(x, ξ) = conj σ_m(P)(x, -ξ)`

(`TauCeti.classicalPrincipalSymbol_intrinsicConj`). In a chart this is the Euclidean identity
`conj (Op(a) u) = Op(ã) (conj u)` with `ã(x, ξ) = conj a(x, -ξ)`
(`TauCeti.ClassicalSymbol.quantizeSchwartzValue_conjCLM`): conjugation reverses the phase
`exp(i x·ξ)` and so the sign of the frequency.

The operators commuting with conjugation are exactly the complexifications of real-linear
operators on real-valued functions (`ContMDiffMap.intrinsicConj_eq_self_iff`). For them the
principal symbol satisfies `σ_m(P)(x, -ξ) = conj σ_m(P)(x, ξ)`
(`TauCeti.classicalPrincipalSymbol_neg_covector_of_intrinsicConj_eq_self`); for instance `∂ⱼ` has
principal symbol `i ξⱼ`. Every classical pseudodifferential operator is `A + i B` with `A`
and `B` complexifications of real operators, and `A`, `B` are classical pseudodifferential
operators of the same order
(`TauCeti.exists_complexifyLinearMap_add_I_smul_complexifyLinearMap_eq`).

## Main results

* `TauCeti.IsProperlySupported.intrinsicConj`: conjugation preserves proper support.
* `TauCeti.intrinsicConj_mem_classicalPseudodifferentialOperators_iff`: `Pᶜ` is a classical
  pseudodifferential operator of order `m` exactly when `P` is.
* `TauCeti.classicalPrincipalSymbol_intrinsicConj`: `σ_m(Pᶜ)(x, ξ) = conj σ_m(P)(x, -ξ)`.
* `TauCeti.classicalPrincipalSymbol_neg_covector_of_intrinsicConj_eq_self`: the principal symbol
  of a real operator satisfies `σ_m(P)(x, -ξ) = conj σ_m(P)(x, ξ)`.
* `TauCeti.exists_complexifyLinearMap_add_I_smul_complexifyLinearMap_eq`: the decomposition of a
  classical pseudodifferential operator into real and imaginary parts.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open Filter Set
open scoped ContDiff Manifold Distributions SchwartzMap Topology ComplexConjugate

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M] {m : ℝ}
  {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}

/-- **Conjugation preserves proper support.** -/
theorem IsProperlySupported.intrinsicConj (hP : IsProperlySupported P) :
    IsProperlySupported (ContMDiffMap.intrinsicConj P) := by
  rw [isProperlySupported_iff] at hP ⊢
  intro K hK
  obtain ⟨K', hK', hsupp, hloc⟩ := hP K hK
  refine ⟨K', hK', fun f hf ↦ ?_, fun f hf x hx ↦ ?_⟩
  · rw [ContMDiffMap.intrinsicConj_apply, ContMDiffMap.tsupport_conj]
    exact hsupp _ ((ContMDiffMap.tsupport_conj f).trans_subset hf)
  · rw [ContMDiffMap.intrinsicConj_apply, ContMDiffMap.conj_apply,
      hloc _ (hf.mono fun y hy ↦ by simp [hy]) x hx, star_zero]

variable [T2Space M]

/-- If the classical symbol `a` represents the chart compression of `P` by the cutoffs `φ`, `ψ`,
then `ã = (a ∘ (id × -id))†`, with `ã(x, ξ) = conj a(x, -ξ)`, represents the chart compression of
the conjugate `f ↦ conj (P (conj f))` by the same cutoffs. -/
private theorem quantizeSchwartzValue_eq_complexChartCompression_intrinsicConj
    {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    {φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)} {a : ClassicalSymbol n ℂ ℂ m}
    (ha : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n),
      quantizeSchwartzValue a.toSymbol.coefficient u x =
        e.complexChartCompression he φ ψ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) x)
    (u : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n) :
    quantizeSchwartzValue
        (ClassicalSymbol.compProdMap (.id ℝ _) (.neg ℝ) a).pointwiseAdjoint.toSymbol.coefficient
        u x =
      e.complexChartCompression he φ ψ (ContMDiffMap.intrinsicConj P)
        (ContMDiffMap.ofContDiff u (u.smooth ⊤)) x := by
  have hconj : ContMDiffMap.conj (ContMDiffMap.ofContDiff u (u.smooth ⊤)) =
      ContMDiffMap.ofContDiff (SchwartzMap.conjCLM u) ((SchwartzMap.conjCLM u).smooth ⊤) := by
    ext y
    simp [ContMDiffMap.coe_ofContDiff]
  -- The Euclidean identity, applied to `conj u`.
  have hq := ClassicalSymbol.quantizeSchwartzValue_conjCLM a (SchwartzMap.conjCLM u) x
  rw [SchwartzMap.conjCLM_conjCLM] at hq
  rw [hq, e.complexChartCompression_intrinsicConj, ContMDiffMap.intrinsicConj_apply,
    ContMDiffMap.conj_apply, hconj, ← ha, starRingEnd_apply]

/-- The conjugate of a classical pseudodifferential operator of order `m` is one. In each chart
compression the symbol `a` is replaced by `ã(x, ξ) = conj a(x, -ξ)`. -/
theorem intrinsicConj_mem_classicalPseudodifferentialOperators
    (hP : P ∈ classicalPseudodifferentialOperators m) :
    ContMDiffMap.intrinsicConj P ∈ classicalPseudodifferentialOperators m := by
  rw [mem_classicalPseudodifferentialOperators_iff] at hP
  refine mem_classicalPseudodifferentialOperators_iff.2 ⟨hP.1.intrinsicConj, fun e he φ ψ ↦ ?_⟩
  obtain ⟨a, ha⟩ := hP.2 e he φ ψ
  exact ⟨_, quantizeSchwartzValue_eq_complexChartCompression_intrinsicConj he ha⟩

/-- **Conjugation and the class.** The conjugate `f ↦ conj (P (conj f))` of `P` is a classical
pseudodifferential operator of order `m` exactly when `P` is. -/
@[simp]
theorem intrinsicConj_mem_classicalPseudodifferentialOperators_iff :
    ContMDiffMap.intrinsicConj P ∈ classicalPseudodifferentialOperators m ↔
      P ∈ classicalPseudodifferentialOperators m :=
  ⟨fun h ↦ ContMDiffMap.intrinsicConj_intrinsicConj P ▸
    intrinsicConj_mem_classicalPseudodifferentialOperators h,
    intrinsicConj_mem_classicalPseudodifferentialOperators⟩

/-- **Real and imaginary parts.** Every classical pseudodifferential operator `P` of order `m` is
`A + i B`, where `A = (P + Pᶜ) / 2` and `B = (P - Pᶜ) / (2 i)` are complexifications of real-linear
operators on real-valued functions and classical pseudodifferential operators of order `m`. -/
theorem exists_complexifyLinearMap_add_I_smul_complexifyLinearMap_eq
    (hP : P ∈ classicalPseudodifferentialOperators m) :
    ∃ A B : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯,
      ContMDiffMap.complexifyLinearMap A ∈ classicalPseudodifferentialOperators m ∧
      ContMDiffMap.complexifyLinearMap B ∈ classicalPseudodifferentialOperators m ∧
      ContMDiffMap.complexifyLinearMap A + Complex.I • ContMDiffMap.complexifyLinearMap B = P := by
  obtain ⟨A, B, hA, hB, hAB⟩ :=
    ContMDiffMap.exists_complexifyLinearMap_add_I_smul_complexifyLinearMap_eq P
  have hP' := intrinsicConj_mem_classicalPseudodifferentialOperators hP
  exact ⟨A, B, hA ▸ Submodule.smul_mem _ _ (Submodule.add_mem _ hP hP'),
    hB ▸ Submodule.smul_mem _ _ (Submodule.sub_mem _ hP hP'), hAB⟩

variable [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]

/-- **The principal symbol of the conjugate.** `σ_m(Pᶜ)(x, ξ) = conj σ_m(P)(x, -ξ)`: conjugation
reverses the sign of the frequency. -/
theorem classicalPrincipalSymbol_intrinsicConj (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol m (ContMDiffMap.intrinsicConj P) x ξ =
      conj (classicalPrincipalSymbol m P x (-ξ)) := by
  by_cases hP : P ∈ classicalPseudodifferentialOperators m
  swap
  · rw [classicalPrincipalSymbol_of_notMem hP, classicalPrincipalSymbol_of_notMem
      (intrinsicConj_mem_classicalPseudodifferentialOperators_iff.not.2 hP), map_zero]
  -- Read both principal symbols in the preferred chart at `x`, with a cutoff equal to `1` at `x`.
  set e := chartAt (CoordinateSpace n) x
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M :=
    IsManifold.chart_mem_maximalAtlas x
  have hx : x ∈ e.source := mem_chart_source _ x
  obtain ⟨χ, -, hχ⟩ := TestFunction.exists_tsupport_subset_apply_eq
    (Ω := ⟨e.target, e.open_target⟩) (n := ⊤) (e.open_target.mem_nhds (e.map_source hx))
    subset_rfl (1 : ℝ)
  obtain ⟨a, ha⟩ := (mem_classicalPseudodifferentialOperators_iff.1 hP).2 e he χ χ
  obtain ⟨b, hb⟩ := (mem_classicalPseudodifferentialOperators_iff.1
    (intrinsicConj_mem_classicalPseudodifferentialOperators hP)).2 e he χ χ
  -- The symbol of the conjugate compression is `ã(y, η) = conj a(y, -η)`.
  have hba : b = (ClassicalSymbol.compProdMap (.id ℝ _) (.neg ℝ) a).pointwiseAdjoint := by
    refine ClassicalSymbol.ext <| Symbol.ext <|
      Symbol.coefficient_eq_of_forall_quantizeSchwartzValue_eq fun u _ ↦ funext fun y ↦ ?_
    rw [hb, ← quantizeSchwartzValue_eq_complexChartCompression_intrinsicConj he ha]
  have h₁ := coefficient_principal_apply_eq_classicalPrincipalSymbol
    (intrinsicConj_mem_classicalPseudodifferentialOperators hP) he χ χ hb hx ξ
  have h₂ := coefficient_principal_apply_eq_classicalPrincipalSymbol hP he χ χ ha hx (-ξ)
  rw [hχ, mul_one, Complex.ofReal_one, one_mul] at h₁ h₂
  rw [← h₁, ← h₂, hba, ClassicalSymbol.coefficient_principal_pointwiseAdjoint_compProdMap_neg,
    ContinuousLinearMap.neg_comp, map_neg]

/-- **The principal symbol of a real operator.** If `P` commutes with conjugation, that is, `P` is
the complexification of a real-linear operator on real-valued functions, then
`σ_m(P)(x, -ξ) = conj σ_m(P)(x, ξ)`. -/
theorem classicalPrincipalSymbol_neg_covector_of_intrinsicConj_eq_self
    (hP : ContMDiffMap.intrinsicConj P = P) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol m P x (-ξ) = conj (classicalPrincipalSymbol m P x ξ) := by
  conv_lhs => rw [← hP]
  rw [classicalPrincipalSymbol_intrinsicConj, neg_neg]

end TauCeti
