/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.PrincipalSymbol
public import TauCeti.Geometry.Manifold.PullbackGroupoid
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# Classical pseudodifferential operators under diffeomorphisms

Let `Φ : M → N` be a smooth diffeomorphism of manifolds modelled on `ℝⁿ`. An operator `P` on the
complex-valued smooth functions on `M` is carried to the operator

`Φ_* P : u ↦ P (u ∘ Φ) ∘ Φ⁻¹`

on `N` (`Diffeomorph.pushforwardOperator`). This file shows that `Φ_*` preserves the classical
pseudodifferential operators of every order `m`
(`TauCeti.pushforwardOperator_mem_classicalPseudodifferentialOperators_iff`) and that the principal
symbol transforms through the cotangent map of `Φ`:

`σ_m(Φ_* P)(Φ x, ξ) = σ_m(P)(x, ξ ∘ dΦ_x)`

for every covector `ξ ∈ T*_{Φ x} N` (`TauCeti.classicalPrincipalSymbol_pushforwardOperator`). So
the class of classical pseudodifferential operators and their principal symbols are intrinsic to
the smooth structure: an isometry or a group of diffeomorphisms acts on them, and an operator
commuting with such an action has an invariant principal symbol.

Both statements reduce to one identity of chart compressions. For a chart `e` of the maximal atlas
of `N`, the chart `Φ ≫ e` of `M` has the same target, and the compression of `Φ_* P` in `e` by any
cutoffs equals the compression of `P` in `Φ ≫ e` by the same cutoffs
(`TauCeti.complexChartCompression_pushforwardOperator`). The definition of the class tests every
chart of the maximal atlas, so the chart symbols of `Φ_* P` are chart symbols of `P`; the principal
symbol is then compared through the chain rule `d(e ∘ Φ)_x = de_{Φ x} ∘ dΦ_x`.

## Main results

* `TauCeti.IsProperlySupported.pushforwardOperator`: `Φ_*` preserves proper support.
* `TauCeti.complexChartCompression_pushforwardOperator`: the chart compressions of `Φ_* P` in a
  chart `e` are those of `P` in the chart `Φ ≫ e`.
* `TauCeti.pushforwardOperator_mem_classicalPseudodifferentialOperators`,
  `TauCeti.pushforwardOperator_mem_classicalPseudodifferentialOperators_iff`: `Φ_* P` is a
  classical pseudodifferential operator of order `m` exactly when `P` is.
* `TauCeti.classicalPrincipalSymbol_pushforwardOperator`: the principal symbol of `Φ_* P` at
  `(Φ x, ξ)` is that of `P` at `(x, ξ ∘ dΦ_x)`, and
  `TauCeti.classicalPrincipalSymbol_pushforwardOperator_apply` reads it at any point `y` of `N`.
* `TauCeti.classicalPrincipalSymbol_apply_eq_of_pushforwardOperator_eq`: an operator invariant
  under a diffeomorphism of `M` has a principal symbol invariant under its cotangent map.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1, Theorem 18.1.17
  and the discussion after Definition 18.1.20.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
-/

public section

noncomputable section

open Filter Set
open scoped ContDiff Manifold Distributions SchwartzMap Topology

namespace TauCeti

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [TopologicalSpace N] [ChartedSpace (CoordinateSpace n) N]
  {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
  (Φ : M ≃ₘ^∞⟮𝓘(ℝ, CoordinateSpace n), 𝓘(ℝ, CoordinateSpace n)⟯ N)

/-- **Proper support is invariant under diffeomorphisms.** If `P` is properly supported on `M`,
then so is its pushforward `u ↦ P (u ∘ Φ) ∘ Φ⁻¹` on `N`. -/
theorem IsProperlySupported.pushforwardOperator (hP : IsProperlySupported P) :
    IsProperlySupported (Φ.pushforwardOperator P) := by
  refine isProperlySupported_iff.2 fun K hK ↦ ?_
  obtain ⟨K', hK', hP₁, hP₂⟩ :=
    isProperlySupported_iff.1 hP (Φ ⁻¹' K) (Φ.toHomeomorph.isCompact_preimage.2 hK)
  -- The compact set for `P` and `Φ⁻¹(K)` is carried to `N` by `Φ`.
  refine ⟨Φ '' K', hK'.image Φ.continuous, fun f hf ↦ ?_, fun f hf y hy ↦ ?_⟩
  · have hsupp := hP₁ _ (by
      rw [Φ.coe_compRightComplexAlgEquiv_apply f, ← Φ.coe_toHomeomorph,
        tsupport_comp_eq_preimage]
      exact preimage_mono hf)
    rw [Φ.coe_pushforwardOperator_apply P f, ← Φ.coe_toHomeomorph_symm,
      tsupport_comp_eq_preimage]
    exact fun y hy ↦ ⟨Φ.symm y, hsupp hy, Φ.apply_symm_apply y⟩
  · rw [Diffeomorph.pushforwardOperator_apply_apply]
    refine hP₂ _ ?_ _ (by simpa using hy)
    simpa using (Φ.continuous.tendsto_nhdsSet (mapsTo_image Φ K')).eventually hf

variable [T2Space M] [T2Space N]

/-- **Chart compressions of the pushforward.** For a chart `e` of the maximal atlas of `N` and
cutoffs `φ`, `ψ` in its target, the chart compression of `u ↦ P (u ∘ Φ) ∘ Φ⁻¹` in `e` is the chart
compression of `P` in the chart `Φ ≫ e` of `M`, which has the same target. -/
theorem complexChartCompression_pushforwardOperator [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
    {e : OpenPartialHomeomorph N (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ N)
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) :
    e.complexChartCompression he φ ψ (Φ.pushforwardOperator P) =
      (Φ.toHomeomorph.transOpenPartialHomeomorph e).complexChartCompression
        (Φ.transOpenPartialHomeomorph_mem_maximalAtlas le_rfl he) φ ψ P := by
  set e' := Φ.toHomeomorph.transOpenPartialHomeomorph e
  have he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M :=
    Φ.transOpenPartialHomeomorph_mem_maximalAtlas le_rfl he
  -- Pulling back to `N` through `e` and then to `M` through `Φ` is pulling back through `e'`.
  have hpull (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; 𝓘(ℝ, ℂ), ℂ⟯) :
      Φ.compRightComplexAlgEquiv (e.complexCutoffPullback he ψ u) =
        e'.complexCutoffPullback he' ψ u := by
    ext x
    rw [Diffeomorph.compRightComplexAlgEquiv_apply]
    by_cases hx : Φ x ∈ e.source
    · rw [OpenPartialHomeomorph.complexCutoffPullback_apply_of_mem he _ _ hx]
      exact (OpenPartialHomeomorph.complexCutoffPullback_apply_of_mem he' ψ u
        (by simpa [e'] using hx)).symm
    · rw [OpenPartialHomeomorph.complexCutoffPullback_apply_of_notMem he _ _ hx]
      exact (OpenPartialHomeomorph.complexCutoffPullback_apply_of_notMem he' ψ u
        (by simpa [e'] using hx)).symm
  ext u y
  rw [OpenPartialHomeomorph.complexChartCompression_apply,
    Diffeomorph.pushforwardOperator_apply_apply, hpull]
  refine Eq.symm ((OpenPartialHomeomorph.complexChartCompression_apply he' φ ψ P u y).trans ?_)
  rw [Homeomorph.transOpenPartialHomeomorph_symm_apply, Function.comp_apply,
    Diffeomorph.coe_toHomeomorph_symm]
  -- The two sides differ only in reading `φ` as a cutoff in the target of `e` or in the target of
  -- `e'`, which is the target of `e` by definition.
  rfl

/-- **Diffeomorphism invariance of the classical pseudodifferential operators.** If `P` is a
classical pseudodifferential operator of order `m` on `M`, then its pushforward
`u ↦ P (u ∘ Φ) ∘ Φ⁻¹` along a diffeomorphism `Φ : M → N` is one on `N`. -/
theorem pushforwardOperator_mem_classicalPseudodifferentialOperators
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] {m : ℝ}
    (hP : P ∈ classicalPseudodifferentialOperators m) :
    Φ.pushforwardOperator P ∈ classicalPseudodifferentialOperators m := by
  have hP' := mem_classicalPseudodifferentialOperators_iff.1 hP
  refine mem_classicalPseudodifferentialOperators_iff.2
    ⟨hP'.1.pushforwardOperator Φ, fun e he φ ψ ↦ ?_⟩
  -- Each chart compression of `Φ_* P` is a chart compression of `P`.
  obtain ⟨a, ha⟩ := hP'.2 _ (Φ.transOpenPartialHomeomorph_mem_maximalAtlas le_rfl he) φ ψ
  exact ⟨a, fun u x ↦ by rw [ha, complexChartCompression_pushforwardOperator]⟩

/-- The pushforward `u ↦ P (u ∘ Φ) ∘ Φ⁻¹` along a diffeomorphism `Φ : M → N` is a classical
pseudodifferential operator of order `m` on `N` exactly when `P` is one on `M`. -/
@[simp]
theorem pushforwardOperator_mem_classicalPseudodifferentialOperators_iff
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ N] {m : ℝ} :
    Φ.pushforwardOperator P ∈ classicalPseudodifferentialOperators m ↔
      P ∈ classicalPseudodifferentialOperators m := by
  refine ⟨fun h ↦ ?_, pushforwardOperator_mem_classicalPseudodifferentialOperators Φ⟩
  have h' := pushforwardOperator_mem_classicalPseudodifferentialOperators Φ.symm h
  rwa [← Diffeomorph.pushforwardOperator_symm, AlgEquiv.symm_apply_apply] at h'

/-- **The principal symbol under diffeomorphisms.** The principal symbol of order `m` of the
pushforward `u ↦ P (u ∘ Φ) ∘ Φ⁻¹` at a covector `ξ ∈ T*_{Φ x} N` is the principal symbol of `P` at
the pulled-back covector `ξ ∘ dΦ_x ∈ T*ₓ M`. Both sides vanish when `P` is not a classical
pseudodifferential operator of order `m`. -/
theorem classicalPrincipalSymbol_pushforwardOperator [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ N] {m : ℝ} (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) (Φ x) →L[ℝ] ℝ) :
    classicalPrincipalSymbol m (Φ.pushforwardOperator P) (Φ x) ξ =
      classicalPrincipalSymbol m P x
        (ξ.comp (mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) Φ x)) := by
  by_cases hP : P ∈ classicalPseudodifferentialOperators m
  swap
  · rw [classicalPrincipalSymbol_of_notMem hP,
      classicalPrincipalSymbol_of_notMem
        (by rwa [pushforwardOperator_mem_classicalPseudodifferentialOperators_iff])]
  -- Read both principal symbols in the preferred chart `e` at `Φ x` and the chart `Φ ≫ e` at `x`,
  -- with one cutoff `χ` equal to `1` at `e (Φ x)`: the two chart symbols coincide.
  set e := chartAt (CoordinateSpace n) (Φ x)
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ N :=
    IsManifold.chart_mem_maximalAtlas (Φ x)
  have hx : Φ x ∈ e.source := mem_chart_source _ (Φ x)
  set e' := Φ.toHomeomorph.transOpenPartialHomeomorph e
  have he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M :=
    Φ.transOpenPartialHomeomorph_mem_maximalAtlas le_rfl he
  have hx' : x ∈ e'.source := by simpa [e'] using hx
  obtain ⟨χ, -, hχ⟩ := TestFunction.exists_tsupport_subset_apply_eq
    (Ω := ⟨e.target, e.open_target⟩) (n := ⊤) (e.open_target.mem_nhds (e.map_source hx))
    (fun _ hz ↦ hz) (1 : ℝ)
  obtain ⟨a, ha⟩ := (mem_classicalPseudodifferentialOperators_iff.1 hP).2 e' he' χ χ
  have ha' : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n),
      quantizeSchwartzValue a.toSymbol.coefficient u y =
        e.complexChartCompression he χ χ (Φ.pushforwardOperator P)
          (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y := fun u y ↦ by
    rw [ha, complexChartCompression_pushforwardOperator]
  -- The frequency `η` whose covector `⟪η, ·⟫ ∘ de_{Φ x}` is `ξ`.
  set η := (InnerProductSpace.toDual ℝ (CoordinateSpace n)).symm
    (ξ.comp (mvfderiv 𝓘(ℝ, CoordinateSpace n) e (Φ x)).inverse)
  have hη : (innerSL ℝ η).comp (mvfderiv 𝓘(ℝ, CoordinateSpace n) e (Φ x)) = ξ :=
    innerSL_toDual_symm_comp_inverse_mvfderiv
      (IsManifold.maximalAtlas_subset_of_le (by simp) he) hx ξ
  -- The chain rule `d(e ∘ Φ)_x = de_{Φ x} ∘ dΦ_x`.
  have hchain : mvfderiv 𝓘(ℝ, CoordinateSpace n) e' x =
      (mvfderiv 𝓘(ℝ, CoordinateSpace n) e (Φ x)).comp
        (mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) Φ x) :=
    Φ.mvfderiv_comp_diffeomorph (by simp) e x
  have hN := coefficient_principal_eq_classicalPrincipalSymbol
    (pushforwardOperator_mem_classicalPseudodifferentialOperators Φ hP) he χ χ ha' hx η
  have hM := coefficient_principal_eq_classicalPrincipalSymbol hP he' χ χ ha hx' η
  have he'x : e' x = e (Φ x) := by simp [e']
  rw [he'x, hN, hchain, ← ContinuousLinearMap.comp_assoc, hη] at hM
  have h1 := congrArg (fun L : ℂ →L[ℂ] ℂ ↦ L 1) hM
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    mul_one] at h1
  -- Both sides carry the factor `χ(e (Φ x))² = 1`, once with `χ` read as a cutoff in the target
  -- of `e` and once in the equal target of `Φ ≫ e`.
  exact mul_left_cancel₀ (a := ((χ (e (Φ x)) * χ (e (Φ x)) : ℝ) : ℂ)) (by simp [hχ]) h1

/-- The principal symbol of order `m` of the pushforward `u ↦ P (u ∘ Φ) ∘ Φ⁻¹` at a covector
`ξ ∈ T*_y N` is the principal symbol of `P` at the preimage `Φ⁻¹ y` and the pulled-back covector
`ξ ∘ dΦ_{Φ⁻¹ y}`: `classicalPrincipalSymbol_pushforwardOperator` read at an arbitrary point of
`N`. -/
@[simp]
theorem classicalPrincipalSymbol_pushforwardOperator_apply
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ N] {m : ℝ}
    (y : N) (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) y →L[ℝ] ℝ) :
    classicalPrincipalSymbol m (Φ.pushforwardOperator P) y ξ =
      classicalPrincipalSymbol m P (Φ.symm y)
        (ξ.comp (mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) Φ (Φ.symm y))) := by
  have h := classicalPrincipalSymbol_pushforwardOperator (P := P) (m := m) Φ (Φ.symm y) ξ
  rwa [Φ.apply_symm_apply] at h

/-- **Invariant operators have invariant principal symbols.** If an operator `P` on `M` is invariant
under a diffeomorphism `Ψ` of `M`, in the sense that `P (u ∘ Ψ) ∘ Ψ⁻¹ = P u` for every `u`, then
its principal symbol is invariant under the cotangent map of `Ψ`:
`σ_m(P)(Ψ x, ξ) = σ_m(P)(x, ξ ∘ dΨ_x)`. -/
theorem classicalPrincipalSymbol_apply_eq_of_pushforwardOperator_eq
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] {m : ℝ}
    (Ψ : M ≃ₘ^∞⟮𝓘(ℝ, CoordinateSpace n), 𝓘(ℝ, CoordinateSpace n)⟯ M)
    (hΨ : Ψ.pushforwardOperator P = P) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) (Ψ x) →L[ℝ] ℝ) :
    classicalPrincipalSymbol m P (Ψ x) ξ =
      classicalPrincipalSymbol m P x
        (ξ.comp (mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) Ψ x)) := by
  have h := classicalPrincipalSymbol_pushforwardOperator (P := P) (m := m) Ψ x ξ
  rwa [hΨ] at h

end TauCeti
