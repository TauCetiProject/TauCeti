/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Adjoint.Weighted
public import TauCeti.Analysis.Pseudodifferential.Manifold.PrincipalSymbol
public import TauCeti.Geometry.Manifold.Measure.SmoothDensity
import TauCeti.Analysis.Distribution.TestFunction.Inner

/-!
# Formal adjoints of classical pseudodifferential operators on a manifold

Let `M` be a manifold modelled on `ℝⁿ` and `μ` a measure on `M` with a smooth positive density
(`TauCeti.HasSmoothPositiveDensity`): in every chart `e` of the maximal smooth atlas, `μ` is
`ρ(y) dy` for a function `ρ` smooth and positive on the chart target. An operator `Q` on the
complex-valued smooth functions on `M` is a **formal adjoint** of `P` for `μ` when
`∫ ⟪P u, v⟫ dμ = ∫ ⟪u, Q v⟫ dμ` for all compactly supported smooth `u` and `v`.

This file shows that if `P` is a classical pseudodifferential operator of order `m`
(`TauCeti.classicalPseudodifferentialOperators`) and `Q` is a properly supported formal adjoint of
`P`, then `Q` is a classical pseudodifferential operator of order `m`
(`TauCeti.mem_classicalPseudodifferentialOperators_of_forall_integral_inner_eq`), whose principal
symbol is the complex conjugate of that of `P`:

`σ_m(Q)(x, ξ) = conj σ_m(P)(x, ξ)`

(`TauCeti.classicalPrincipalSymbol_eq_conj_of_forall_integral_inner_eq`). In particular a
formally self-adjoint classical pseudodifferential operator has a real principal symbol
(`TauCeti.conj_classicalPrincipalSymbol_eq_of_forall_integral_inner_eq`).

Proper support of `Q` is a hypothesis, not a consequence: the adjoint identity only involves the
values of `Q` on compactly supported functions, while membership in
`TauCeti.classicalPseudodifferentialOperators` constrains `Q` on all smooth functions.

## The argument

Fix a chart `e` and cutoffs `φ`, `ψ` in its target, and let `ρ` be the density of `μ` in `e`.
For Schwartz functions `u` and `v` on `ℝⁿ`, change variables to `M`, use the adjoint identity and
change variables back:

`∫ ⟪v, φ (Q ((ψ u) ∘ e)) ∘ e⁻¹⟫ dy = ∫ ⟪(ρ⁻¹ φ v) ∘ e, Q ((ψ u) ∘ e)⟫ dμ`
`= ∫ ⟪P ((ρ⁻¹ φ v) ∘ e), (ψ u) ∘ e⟫ dμ = ∫ ⟪χ (P ((ρ⁻¹ φ v) ∘ e)) ∘ e⁻¹, ρ ψ u⟫ dy`,

for a cutoff `χ` equal to `1` on the support of `ψ`. The operator
`v ↦ χ (P ((ρ⁻¹ φ v) ∘ e)) ∘ e⁻¹` is the chart compression of `P` by `χ` and `ρ⁻¹ φ`, so it is
`Op(a)` for a classical symbol `a` of order `m` with compact spatial support. By the weighted
adjoint identity (`TauCeti.Symbol.integral_inner_quantizeSchwartzValue_weightedAdjoint`), the last
integral is `∫ ⟪v, Op(b) u⟫` for the weighted adjoint symbol `b` of `a` with weight `ρ ψ`, a
classical symbol of order `m` (`TauCeti.ClassicalSymbol.weightedAdjoint`) with principal symbol
`ρ ψ conj(a_m) = φ ψ conj σ_m(P)`. As `v` is arbitrary, the compression of `Q` by `φ` and `ψ` is
`Op(b)`.

## Main results

* `TauCeti.mem_classicalPseudodifferentialOperators_of_forall_integral_inner_eq`: a properly
  supported formal adjoint of a classical pseudodifferential operator of order `m` is a classical
  pseudodifferential operator of order `m`.
* `TauCeti.classicalPrincipalSymbol_eq_conj_of_forall_integral_inner_eq`: its principal symbol is
  the complex conjugate of the principal symbol of the operator.
* `TauCeti.conj_classicalPrincipalSymbol_eq_of_forall_integral_inner_eq`: a formally self-adjoint
  classical pseudodifferential operator has a real principal symbol.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.7
  (adjoints on `ℝⁿ`) and the discussion after Definition 18.1.20 (operators on manifolds).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (2.3) and §8.
-/

public section

noncomputable section

open Filter Set MeasureTheory ComplexConjugate
open scoped ContDiff Manifold Distributions SchwartzMap Topology

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [MeasurableSpace M] [T2Space M] {μ : Measure M}

/-! ### Changing variables in a chart -/

section Chart

variable {e : OpenPartialHomeomorph M (CoordinateSpace n)}
  (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)

include he

omit [MeasurableSpace M] in
/-- A complex-valued function on `M` whose support lies in the support of the pullback of a
function on `ℝⁿ` by a cutoff `ψ` in a chart `e` has compact support inside the chart source. -/
private theorem hasCompactSupport_and_tsupport_subset_source_of_subset
    (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) {f : M → ℂ}
    {g : C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; 𝓘(ℝ, ℂ), ℂ⟯}
    (hf : tsupport f ⊆ tsupport (e.complexCutoffPullback he ψ g)) :
    HasCompactSupport f ∧ tsupport f ⊆ e.source := by
  have hK := hf.trans (e.tsupport_complexCutoffPullback_subset he ψ g)
  refine ⟨(e.isCompact_symm_image_tsupport ψ).of_isClosed_subset (isClosed_tsupport f) hK,
    hK.trans ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact e.map_target (ψ.tsupport_subset hy)

section ChangeOfVariables

variable {ρ : CoordinateSpace n → ℝ}
  (hint : ∀ f : M → ℂ, Continuous f → HasCompactSupport f → tsupport f ⊆ e.source →
    ∫ x, f x ∂μ = ∫ y in e.target, (ρ y : ℂ) * f (e.symm y))

include hint

/-- **Changing variables in a chart.** Let `ρ` be the density in the chart `e` of a measure `μ`
on `M`. Pairing a continuous function `F` on `M` with the pullback `(θ f) ∘ e` of a function `f`
on `ℝⁿ` by a cutoff `θ` in the chart target is pairing `F ∘ e⁻¹` with `f` against `ρ θ dy`. -/
private theorem integral_inner_complexCutoffPullback (θ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; 𝓘(ℝ, ℂ), ℂ⟯) {F : M → ℂ}
    (hF : Continuous F) :
    ∫ x, inner ℂ (F x) (e.complexCutoffPullback he θ f x) ∂μ =
      ∫ y, ((ρ y * θ y : ℝ) : ℂ) * inner ℂ (F (e.symm y)) (f y) := by
  have hsupp : tsupport (fun x ↦ inner ℂ (F x) (e.complexCutoffPullback he θ f x)) ⊆
      tsupport (e.complexCutoffPullback he θ f) :=
    closure_mono <| Function.support_subset_iff'.2 fun x hx ↦ by
      simp [Function.notMem_support.1 hx]
  obtain ⟨hc, hs⟩ := hasCompactSupport_and_tsupport_subset_source_of_subset he θ hsupp
  rw [hint _ (hF.inner (e.complexCutoffPullback he θ f).contMDiff.continuous) hc hs,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) (s := e.target)
      (f := fun y ↦ ((ρ y * θ y : ℝ) : ℂ) * inner ℂ (F (e.symm y)) (f y)) fun y hy ↦ by
        simp [image_eq_zero_of_notMem_tsupport fun h ↦ hy (θ.tsupport_subset h)]]
  refine setIntegral_congr_fun e.open_target.measurableSet fun y hy ↦ ?_
  simp only [OpenPartialHomeomorph.complexCutoffPullback_apply_of_mem he _ _ (e.map_target hy),
    e.right_inv hy, RCLike.inner_apply', Complex.real_smul]
  push_cast
  ring

/-- The pullback on the left: pairing `(θ f) ∘ e` with a continuous function `F` on `M` is pairing
`f` with `F ∘ e⁻¹` against `ρ θ dy`. -/
private theorem integral_inner_complexCutoffPullback_left
    (θ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; 𝓘(ℝ, ℂ), ℂ⟯) {F : M → ℂ}
    (hF : Continuous F) :
    ∫ x, inner ℂ (e.complexCutoffPullback he θ f x) (F x) ∂μ =
      ∫ y, ((ρ y * θ y : ℝ) : ℂ) * inner ℂ (f y) (F (e.symm y)) := by
  have h := congrArg conj (integral_inner_complexCutoffPullback he hint θ f hF)
  rw [← integral_conj, ← integral_conj] at h
  simpa only [inner_conj_symm, map_mul, Complex.conj_ofReal] using h

variable {m : ℝ}
  {P Q : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}

/-- **The formal adjoint in a chart, as an operator.** Let `ρ` be the density of `μ` in the chart
`e`, let `χ` be a cutoff equal to `1` where `ψ ≠ 0`, and `a` the symbol of the chart compression
of `P` by `χ` and `ρ⁻¹ φ`. If `Q` is a formal adjoint of `P` for `μ`, the compression of `Q` by
`φ` and `ψ` is the quantization of the weighted adjoint symbol of `a` for the weight `ρ ψ`. -/
private theorem quantizeSchwartzValue_weightedAdjoint_eq_complexChartCompression
    (hρpos : ∀ y ∈ e.target, 0 < ρ y)
    (hPQ : ∀ u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯, HasCompactSupport u →
      HasCompactSupport v → ∫ x, inner ℂ (P u x) (v x) ∂μ = ∫ x, inner ℂ (u x) (Q v x) ∂μ)
    {φ φ' ψ ψ' χ : 𝓓(⟨e.target, e.open_target⟩, ℝ)} (hφ' : ∀ y, φ' y = (ρ y)⁻¹ * φ y)
    (hψ' : ∀ y, ψ' y = ρ y * ψ y) (hχ : ∀ y, ψ y ≠ 0 → χ y = 1) {a : ClassicalSymbol n ℂ ℂ m}
    (ha : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n),
      quantizeSchwartzValue a.toSymbol.coefficient u y =
        e.complexChartCompression he χ φ' P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y)
    (ha' : a.toSymbol.HasCompactSpatialSupport)
    (hid : ∀ _ : CoordinateSpace n, (ContinuousLinearMap.id ℂ ℂ).IsInvertible)
    (hk : ContDiff ℝ ∞ fun y ↦ (ψ' y : ℂ) • ContinuousLinearMap.id ℂ ℂ)
    (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n) :
    quantizeSchwartzValue (a.weightedAdjoint ha' contDiff_const hid hk).toSymbol.coefficient u y =
      e.complexChartCompression he φ ψ Q (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y := by
  -- Both sides are continuous; compare their pairings with every test function `v`.
  refine congrFun (eq_of_forall_integral_inner_eq_of_continuous (𝕜 := ℂ) (μ := volume)
    ((a.weightedAdjoint ha' contDiff_const hid hk).toSymbol.contDiff_quantizeSchwartzValue
      u).continuous
    (ContMDiffMap.contMDiff _).continuous fun v ↦ ?_) y
  set w := v.hasCompactSupport.toSchwartzMap v.contDiff
  set G := e.complexCutoffPullback he ψ (ContMDiffMap.ofContDiff u (u.smooth ⊤))
  set H := e.complexCutoffPullback he φ' (ContMDiffMap.ofContDiff w (w.smooth ⊤))
  have hG := (hasCompactSupport_and_tsupport_subset_source_of_subset he ψ (f := G) subset_rfl).1
  have hH := (hasCompactSupport_and_tsupport_subset_source_of_subset he φ' (f := H) subset_rfl).1
  have hφ0 (z : CoordinateSpace n) (hz : z ∉ e.target) : φ z = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hz (φ.tsupport_subset h)
  calc ∫ z, inner ℂ (v z) (quantizeSchwartzValue
          (a.weightedAdjoint ha' contDiff_const hid hk).toSymbol.coefficient u z)
      _ = ∫ z, inner ℂ (quantizeSchwartzValue a.toSymbol.coefficient w z)
            (((ψ' z : ℂ) • ContinuousLinearMap.id ℂ ℂ) (u z)) := by
        rw [Symbol.integral_inner_quantizeSchwartzValue_weightedAdjoint a.toSymbol ha'
          contDiff_const hid hk w u]
        simp [w]
      _ = ∫ z, ((ρ z * ψ z : ℝ) : ℂ) * inner ℂ (P H (e.symm z)) (u z) := by
        -- `Op(a) w = χ (P H) ∘ e⁻¹`, and `χ = 1` where `ψ ≠ 0`.
        refine integral_congr_ae (.of_forall fun z ↦ ?_)
        simp only [ha, OpenPartialHomeomorph.complexChartCompression_apply, hψ', smul_apply,
          ContinuousLinearMap.id_apply, RCLike.inner_apply', Complex.real_smul, map_mul,
          Complex.conj_ofReal, H, w]
        by_cases hψz : ψ z = 0
        · simp [hψz]
        · rw [hχ z hψz]
          push_cast
          ring
      _ = ∫ x, inner ℂ (H x) (Q G x) ∂μ := by
        rw [← hPQ H G hH hG, integral_inner_complexCutoffPullback he hint ψ _
          (P H).contMDiff.continuous]
        simp
      _ = ∫ z, inner ℂ (v z)
            (e.complexChartCompression he φ ψ Q (ContMDiffMap.ofContDiff u (u.smooth ⊤)) z) := by
        rw [integral_inner_complexCutoffPullback_left he hint φ' _ (Q G).contMDiff.continuous]
        refine integral_congr_ae (.of_forall fun z ↦ ?_)
        by_cases hz : z ∈ e.target
        · have hρz : (ρ z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hρpos z hz).ne'
          simp only [hφ', OpenPartialHomeomorph.complexChartCompression_apply,
            ContMDiffMap.coe_ofContDiff, RCLike.inner_apply', Complex.real_smul, G, w,
            HasCompactSupport.toSchwartzMap_toFun]
          push_cast
          field_simp
        · simp [hφ', hφ0 z hz]

end ChangeOfVariables

variable [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] {m : ℝ}
  {P Q : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}

/-- **The formal adjoint in a chart.** Let `P` be a classical pseudodifferential operator of order
`m`, and `Q` a formal adjoint of `P` for a measure `μ` with a smooth positive density. Then every
chart compression of `Q`, by cutoffs `φ` and `ψ`, is the quantization of a classical symbol `b`
of order `m`, whose principal symbol at `e x` is `φ(e x) ψ(e x)` times the complex conjugate of
the principal symbol of `P` at `x`. -/
private theorem exists_eq_complexChartCompression_of_forall_integral_inner_eq
    (hμ : HasSmoothPositiveDensity (CoordinateSpace n) μ)
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (hPQ : ∀ u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯, HasCompactSupport u →
      HasCompactSupport v → ∫ x, inner ℂ (P u x) (v x) ∂μ = ∫ x, inner ℂ (u x) (Q v x) ∂μ)
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) :
    ∃ b : ClassicalSymbol n ℂ ℂ m,
      (∀ (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n),
        quantizeSchwartzValue b.toSymbol.coefficient u y =
          e.complexChartCompression he φ ψ Q (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y) ∧
      ∀ x ∈ e.source, ∀ ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ,
        b.principal.coefficient (e x, (InnerProductSpace.toDual ℝ (CoordinateSpace n)).symm
          (ξ.comp (mvfderiv 𝓘(ℝ, CoordinateSpace n) e x).inverse)) 1 =
          (φ (e x) * ψ (e x) : ℝ) * conj (classicalPrincipalSymbol m P x ξ) := by
  obtain ⟨ρ, hρ, hρpos, hint⟩ := hasSmoothPositiveDensity_iff.1 hμ e he
  -- The cutoffs `ρ⁻¹ φ` and `ρ ψ`, and a cutoff `χ` equal to `1` near the support of `ψ`.
  set φ' := TestFunction.smulLeftCLMOfContDiffOn (hρ.inv fun y hy ↦ (hρpos y hy).ne') φ
  set ψ' := TestFunction.smulLeftCLMOfContDiffOn hρ ψ
  have hφ' (y : CoordinateSpace n) : φ' y = (ρ y)⁻¹ * φ y := by
    simp [φ', TestFunction.smulLeftCLMOfContDiffOn_apply]
  have hψ' (y : CoordinateSpace n) : ψ' y = ρ y * ψ y := by
    simp [ψ', TestFunction.smulLeftCLMOfContDiffOn_apply]
  obtain ⟨χ, hχ, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤)
    ψ.hasCompactSupport.isCompact ψ.tsupport_subset
  have hχ1 (y : CoordinateSpace n) (hy : ψ y ≠ 0) : χ y = 1 :=
    (hχ.filter_mono (nhds_le_nhdsSet (subset_tsupport _ hy))).self_of_nhds
  -- The symbol `a` of the compression of `P` by `χ` and `ρ⁻¹ φ`, and its weighted adjoint.
  obtain ⟨a, ha⟩ := (mem_classicalPseudodifferentialOperators_iff.1 hP).2 e he χ φ'
  have ha' := hasCompactSpatialSupport_of_eq_complexChartCompression he ha
  have hk : ContDiff ℝ ∞ fun y ↦ (ψ' y : ℂ) • ContinuousLinearMap.id ℂ ℂ :=
    (Complex.ofRealCLM.contDiff.comp ψ'.contDiff).smul contDiff_const
  have hid : ∀ _ : CoordinateSpace n, (ContinuousLinearMap.id ℂ ℂ).IsInvertible := fun _ ↦
    ContinuousLinearEquiv.coe_refl (R₁ := ℂ) (M₁ := ℂ) ▸ ContinuousLinearMap.isInvertible_equiv
  refine ⟨a.weightedAdjoint ha' contDiff_const hid hk,
    quantizeSchwartzValue_weightedAdjoint_eq_complexChartCompression he hint hρpos hPQ hφ' hψ'
      hχ1 ha ha' hid hk, fun x hx ξ ↦ ?_⟩
  -- The principal symbol of the weighted adjoint at `e x` is `ρ ψ` times the conjugate of that
  -- of `a`, which is `χ ρ⁻¹ φ σ_m(P)`, and `χ = 1` where `ψ ≠ 0`.
  have hlin (f : ℂ →L[ℂ] ℂ) : f = f 1 • ContinuousLinearMap.id ℂ ℂ :=
    ContinuousLinearMap.ext_ring (by simp)
  rw [ClassicalSymbol.coefficient_principal_weightedAdjoint, hlin (a.principal.coefficient _),
    coefficient_principal_apply_eq_classicalPrincipalSymbol hP he χ φ' ha hx ξ]
  by_cases hψx : ψ (e x) = 0
  · simp [hψ', hψx]
  · have hρx : (ρ (e x) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hρpos _ (e.map_source hx)).ne'
    simp only [hφ', hψ', hχ1 _ hψx, map_smulₛₗ, ContinuousLinearMap.adjoint_id,
      ContinuousLinearMap.inverse_id, ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, map_mul, Complex.conj_ofReal]
    push_cast
    field_simp

end Chart

/-! ### Formal adjoints -/

variable [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] {m : ℝ}
  {P Q : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}

/-- **Formal adjoints of classical pseudodifferential operators.** Let `μ` be a measure on `M`
with a smooth positive density, and `P` a classical pseudodifferential operator of order `m`. A
properly supported operator `Q` with `∫ ⟪P u, v⟫ dμ = ∫ ⟪u, Q v⟫ dμ` for all compactly supported
smooth functions `u` and `v` is a classical pseudodifferential operator of order `m`. -/
theorem mem_classicalPseudodifferentialOperators_of_forall_integral_inner_eq
    (hμ : HasSmoothPositiveDensity (CoordinateSpace n) μ)
    (hP : P ∈ classicalPseudodifferentialOperators m) (hQ : IsProperlySupported Q)
    (hPQ : ∀ u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯, HasCompactSupport u →
      HasCompactSupport v → ∫ x, inner ℂ (P u x) (v x) ∂μ = ∫ x, inner ℂ (u x) (Q v x) ∂μ) :
    Q ∈ classicalPseudodifferentialOperators m :=
  mem_classicalPseudodifferentialOperators_iff.2 ⟨hQ, fun _ he φ ψ ↦
    (exists_eq_complexChartCompression_of_forall_integral_inner_eq he hμ hP hPQ φ ψ).imp
      fun _ hb ↦ hb.1⟩

/-- **The principal symbol of a formal adjoint** is the complex conjugate of the principal symbol:
under the hypotheses of
`TauCeti.mem_classicalPseudodifferentialOperators_of_forall_integral_inner_eq`,
`σ_m(Q)(x, ξ) = conj σ_m(P)(x, ξ)` for every covector `ξ ∈ T*ₓM`. -/
theorem classicalPrincipalSymbol_eq_conj_of_forall_integral_inner_eq
    (hμ : HasSmoothPositiveDensity (CoordinateSpace n) μ)
    (hP : P ∈ classicalPseudodifferentialOperators m) (hQ : IsProperlySupported Q)
    (hPQ : ∀ u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯, HasCompactSupport u →
      HasCompactSupport v → ∫ x, inner ℂ (P u x) (v x) ∂μ = ∫ x, inner ℂ (u x) (Q v x) ∂μ)
    (x : M) (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol m Q x ξ = conj (classicalPrincipalSymbol m P x ξ) := by
  -- Read both principal symbols in the preferred chart at `x`, with cutoffs equal to `1` there.
  set e := chartAt (CoordinateSpace n) x
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M :=
    IsManifold.chart_mem_maximalAtlas x
  obtain ⟨θ, hθ⟩ := TestFunction.exists_eventually_eq_one_nhds (n := ⊤)
    (Ω := ⟨e.target, e.open_target⟩) (mem_chart_target (CoordinateSpace n) x)
  obtain ⟨b, hb, hbσ⟩ :=
    exists_eq_complexChartCompression_of_forall_integral_inner_eq he hμ hP hPQ θ θ
  have h := coefficient_principal_apply_eq_classicalPrincipalSymbol
    (mem_classicalPseudodifferentialOperators_of_forall_integral_inner_eq hμ hP hQ hPQ) he θ θ hb
    (mem_chart_source _ x) ξ
  rw [hbσ x (mem_chart_source _ x) ξ, hθ.self_of_nhds] at h
  simpa using h.symm

/-- **Formally self-adjoint operators have real principal symbols.** If a classical
pseudodifferential operator `P` of order `m` satisfies `∫ ⟪P u, v⟫ dμ = ∫ ⟪u, P v⟫ dμ` for all
compactly supported smooth functions `u` and `v`, for a measure `μ` with a smooth positive
density, then its principal symbol is real: `conj σ_m(P)(x, ξ) = σ_m(P)(x, ξ)`. -/
theorem conj_classicalPrincipalSymbol_eq_of_forall_integral_inner_eq
    (hμ : HasSmoothPositiveDensity (CoordinateSpace n) μ)
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (hPP : ∀ u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯, HasCompactSupport u →
      HasCompactSupport v → ∫ x, inner ℂ (P u x) (v x) ∂μ = ∫ x, inner ℂ (u x) (P v x) ∂μ)
    (x : M) (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    conj (classicalPrincipalSymbol m P x ξ) = classicalPrincipalSymbol m P x ξ :=
  (classicalPrincipalSymbol_eq_conj_of_forall_integral_inner_eq hμ hP
    (mem_classicalPseudodifferentialOperators_iff.1 hP).1 hPP x ξ).symm

end TauCeti
