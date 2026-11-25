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
(`ContMDiffMap.conjLinearMap`). If `P` is a classical pseudodifferential operator of order `m`, so
is `Pᶜ` (`TauCeti.conjLinearMap_mem_classicalPseudodifferentialOperators_iff`), and its principal
symbol is

`σ_m(Pᶜ)(x, ξ) = conj σ_m(P)(x, -ξ)`

(`TauCeti.classicalPrincipalSymbol_conjLinearMap`). In a chart this is the Euclidean identity
`conj (Op(a) u) = Op(ã) (conj u)` with `ã(x, ξ) = conj a(x, -ξ)`
(`TauCeti.ClassicalSymbol.quantizeSchwartzValue_conjCLM`): conjugation reverses the phase
`exp(i x·ξ)` and so the sign of the frequency.

The operators commuting with conjugation are exactly the complexifications of real-linear
operators on real-valued functions (`ContMDiffMap.conjLinearMap_eq_self_iff`). For them the
principal symbol satisfies `σ_m(P)(x, -ξ) = conj σ_m(P)(x, ξ)`
(`TauCeti.classicalPrincipalSymbol_neg_covector_of_conjLinearMap_eq_self`); for instance `∂ⱼ` has
principal symbol `i ξⱼ`. Every classical pseudodifferential operator is `A + i B` with `A`
and `B` complexifications of real operators, and `A`, `B` are classical pseudodifferential
operators of the same order
(`TauCeti.exists_complexifyLinearMap_add_I_smul_complexifyLinearMap_eq`).

## Main results

* `TauCeti.IsProperlySupported.conjLinearMap`: conjugation preserves proper support.
* `TauCeti.conjLinearMap_mem_classicalPseudodifferentialOperators_iff`: `Pᶜ` is a classical
  pseudodifferential operator of order `m` exactly when `P` is.
* `TauCeti.classicalPrincipalSymbol_conjLinearMap`: `σ_m(Pᶜ)(x, ξ) = conj σ_m(P)(x, -ξ)`.
* `TauCeti.classicalPrincipalSymbol_neg_covector_of_conjLinearMap_eq_self`: the principal symbol
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

/-- Conjugation does not change the support of a function. -/
private theorem tsupport_conj (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    tsupport (ContMDiffMap.conj f) = tsupport f := by
  simp only [tsupport]
  congr 1
  ext x
  simp

/-- **Conjugation preserves proper support.** -/
theorem IsProperlySupported.conjLinearMap (hP : IsProperlySupported P) :
    IsProperlySupported (ContMDiffMap.conjLinearMap P) := by
  rw [isProperlySupported_iff] at hP ⊢
  intro K hK
  obtain ⟨K', hK', hsupp, hloc⟩ := hP K hK
  refine ⟨K', hK', fun f hf ↦ ?_, fun f hf x hx ↦ ?_⟩
  · rw [ContMDiffMap.conjLinearMap_apply, tsupport_conj]
    exact hsupp _ ((tsupport_conj f).trans_subset hf)
  · rw [ContMDiffMap.conjLinearMap_apply, ContMDiffMap.conj_apply,
      hloc _ (hf.mono fun y hy ↦ by simp [hy]) x hx, star_zero]

variable [T2Space M]

/-- The conjugate of a classical pseudodifferential operator of order `m` is one. In each chart
compression the symbol `a` is replaced by `ã(x, ξ) = conj a(x, -ξ)`. -/
theorem conjLinearMap_mem_classicalPseudodifferentialOperators
    (hP : P ∈ classicalPseudodifferentialOperators m) :
    ContMDiffMap.conjLinearMap P ∈ classicalPseudodifferentialOperators m := by
  rw [mem_classicalPseudodifferentialOperators_iff] at hP
  refine mem_classicalPseudodifferentialOperators_iff.2 ⟨hP.1.conjLinearMap, fun e he φ ψ ↦ ?_⟩
  obtain ⟨a, ha⟩ := hP.2 e he φ ψ
  refine ⟨(ClassicalSymbol.compProdMap (.id ℝ _) (.neg ℝ) a).pointwiseAdjoint, fun u x ↦ ?_⟩
  have hconj : ContMDiffMap.conj (ContMDiffMap.ofContDiff u (u.smooth ⊤)) =
      ContMDiffMap.ofContDiff (SchwartzMap.conjCLM u) ((SchwartzMap.conjCLM u).smooth ⊤) := by
    ext y
    simp [ContMDiffMap.coe_ofContDiff]
  rw [e.complexChartCompression_conjLinearMap, ContMDiffMap.conjLinearMap_apply,
    ContMDiffMap.conj_apply, hconj, ← ha, ← SchwartzMap.conjCLM_conjCLM u,
    ClassicalSymbol.quantizeSchwartzValue_conjCLM, SchwartzMap.conjCLM_conjCLM]
  rfl

/-- **Conjugation and the class.** The conjugate `f ↦ conj (P (conj f))` of `P` is a classical
pseudodifferential operator of order `m` exactly when `P` is. -/
@[simp]
theorem conjLinearMap_mem_classicalPseudodifferentialOperators_iff :
    ContMDiffMap.conjLinearMap P ∈ classicalPseudodifferentialOperators m ↔
      P ∈ classicalPseudodifferentialOperators m :=
  ⟨fun h ↦ ContMDiffMap.conjLinearMap_conjLinearMap P ▸
    conjLinearMap_mem_classicalPseudodifferentialOperators h,
    conjLinearMap_mem_classicalPseudodifferentialOperators⟩

/-- **Real and imaginary parts.** Every classical pseudodifferential operator `P` of order `m` is
`A + i B`, where `A = (P + Pᶜ) / 2` and `B = (P - Pᶜ) / (2 i)` are complexifications of real-linear
operators on real-valued functions and classical pseudodifferential operators of order `m`. -/
theorem exists_complexifyLinearMap_add_I_smul_complexifyLinearMap_eq
    (hP : P ∈ classicalPseudodifferentialOperators m) :
    ∃ A B : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯,
      ContMDiffMap.complexifyLinearMap A ∈ classicalPseudodifferentialOperators m ∧
      ContMDiffMap.complexifyLinearMap B ∈ classicalPseudodifferentialOperators m ∧
      ContMDiffMap.complexifyLinearMap A + Complex.I • ContMDiffMap.complexifyLinearMap B = P := by
  have hP' := conjLinearMap_mem_classicalPseudodifferentialOperators hP
  obtain ⟨A, hA⟩ := (ContMDiffMap.conjLinearMap_eq_self_iff
    (P := (2⁻¹ : ℂ) • (P + ContMDiffMap.conjLinearMap P))).1 (by
      rw [ContMDiffMap.conjLinearMap_smul, ContMDiffMap.conjLinearMap_add,
        ContMDiffMap.conjLinearMap_conjLinearMap, add_comm]
      simp)
  have hstar : star (2 * Complex.I)⁻¹ = -(2 * Complex.I)⁻¹ := by
    rw [star_inv₀, star_mul', Complex.star_def, Complex.conj_I, map_ofNat, mul_neg, inv_neg]
  obtain ⟨B, hB⟩ := (ContMDiffMap.conjLinearMap_eq_self_iff
    (P := (2 * Complex.I)⁻¹ • (P - ContMDiffMap.conjLinearMap P))).1 (by
      rw [ContMDiffMap.conjLinearMap_smul, ContMDiffMap.conjLinearMap_sub,
        ContMDiffMap.conjLinearMap_conjLinearMap, hstar]
      module)
  refine ⟨A, B, hA ▸ Submodule.smul_mem _ _ (Submodule.add_mem _ hP hP'),
    hB ▸ Submodule.smul_mem _ _ (Submodule.sub_mem _ hP hP'), ?_⟩
  have hI : Complex.I * (2 * Complex.I)⁻¹ = 2⁻¹ := by
    field_simp
  rw [hA, hB, smul_smul, hI, ← smul_add, add_add_sub_cancel, ← two_smul ℂ P, smul_smul,
    inv_mul_cancel₀ two_ne_zero, one_smul]

variable [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]

/-- **The principal symbol of the conjugate.** `σ_m(Pᶜ)(x, ξ) = conj σ_m(P)(x, -ξ)`: conjugation
reverses the sign of the frequency. -/
theorem classicalPrincipalSymbol_conjLinearMap (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol m (ContMDiffMap.conjLinearMap P) x ξ =
      conj (classicalPrincipalSymbol m P x (-ξ)) := by
  by_cases hP : P ∈ classicalPseudodifferentialOperators m
  swap
  · rw [classicalPrincipalSymbol_of_notMem hP, classicalPrincipalSymbol_of_notMem
      (conjLinearMap_mem_classicalPseudodifferentialOperators_iff.not.2 hP), map_zero]
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
    (conjLinearMap_mem_classicalPseudodifferentialOperators hP)).2 e he χ χ
  -- The symbol of the conjugate compression is `ã(y, η) = conj a(y, -η)`.
  have hba : b = (ClassicalSymbol.compProdMap (.id ℝ _) (.neg ℝ) a).pointwiseAdjoint := by
    refine ClassicalSymbol.ext <| Symbol.ext <|
      Symbol.coefficient_eq_of_forall_quantizeSchwartzValue_eq fun u _ ↦ funext fun y ↦ ?_
    rw [hb, e.complexChartCompression_conjLinearMap, ContMDiffMap.conjLinearMap_apply,
      ContMDiffMap.conj_apply, ← SchwartzMap.conjCLM_conjCLM u,
      ClassicalSymbol.quantizeSchwartzValue_conjCLM, ha]
    congr 3
    ext z
    simp [ContMDiffMap.coe_ofContDiff]
  have h₁ := coefficient_principal_apply_eq_classicalPrincipalSymbol
    (conjLinearMap_mem_classicalPseudodifferentialOperators hP) he χ χ hb hx ξ
  have h₂ := coefficient_principal_apply_eq_classicalPrincipalSymbol hP he χ χ ha hx (-ξ)
  rw [hχ, mul_one, Complex.ofReal_one, one_mul] at h₁ h₂
  rw [← h₁, ← h₂, hba, ClassicalSymbol.coefficient_principal_pointwiseAdjoint_compProdMap_neg,
    ContinuousLinearMap.neg_comp, map_neg]

/-- **The principal symbol of a real operator.** If `P` commutes with conjugation, that is, `P` is
the complexification of a real-linear operator on real-valued functions, then
`σ_m(P)(x, -ξ) = conj σ_m(P)(x, ξ)`. -/
theorem classicalPrincipalSymbol_neg_covector_of_conjLinearMap_eq_self
    (hP : ContMDiffMap.conjLinearMap P = P) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol m P x (-ξ) = conj (classicalPrincipalSymbol m P x ξ) := by
  conv_lhs => rw [← hP]
  rw [classicalPrincipalSymbol_conjLinearMap, neg_neg]

end TauCeti
