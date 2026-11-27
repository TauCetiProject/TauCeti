/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Adjoint.Weighted
public import TauCeti.Analysis.Pseudodifferential.Manifold.Elliptic.Basic
public import TauCeti.Analysis.Pseudodifferential.Manifold.PrincipalSymbol
public import TauCeti.Geometry.Manifold.Measure.SmoothDensity
import TauCeti.Analysis.Pseudodifferential.Manifold.FormalAdjoint
import TauCeti.Analysis.Pseudodifferential.Manifold.PatchedQuantization
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
(`TauCeti.conj_classicalPrincipalSymbol_eq_of_forall_integral_inner_eq`), and `Q` is elliptic
exactly where `P` is (`TauCeti.isClassicalEllipticAt_iff_of_forall_integral_inner_eq`).

Proper support of `Q` is a hypothesis, not a consequence: the adjoint identity only involves the
values of `Q` on compactly supported functions, while membership in
`TauCeti.classicalPseudodifferentialOperators` constrains `Q` on all smooth functions.

On a σ-compact manifold of positive dimension, compact or not, with `μ` finite on compact sets,
every classical pseudodifferential operator `P` of order `m` has a formal adjoint, which is a
classical pseudodifferential operator of order `m`, in particular properly supported, with
conjugate principal symbol
(`exists_mem_classicalPseudodifferentialOperators_forall_hasCompactSupport_integral_inner_eq`, in
the namespace `TauCeti`).
Take a locally finite partition of unity `gᵢ` in charts. Every piece `gᵢ P gⱼ` is a finite sum of
chart quantizations (`TauCeti.exists_mulLeft_comp_comp_mulLeft_eq_sum_chartQuantization`), `μ`
reads in each of their charts as a smooth positive density
(`TauCeti.HasSmoothPositiveDensity.exists_map_restrict_source_eq_withDensity`), and a finite sum of
chart quantizations has a formal adjoint which is again one
(`TauCeti.exists_mem_classicalPseudodifferentialOperators_integral_inner_sum_chartQuantization_eq`).
The formal adjoint of `P` is the locally finite sum of these adjoints, localized near the supports
of `gⱼ` and `gᵢ`. On a noncompact manifold infinitely many pieces occur, but proper support of `P`
leaves only finitely many nonzero pieces near every compact set
(`TauCeti.IsProperlySupported.locallyFinite_setOf_mem_union_and_mulLeft_comp_comp_mulLeft_ne_zero`).

On a compact manifold, with `μ` finite, the formal adjoint satisfies the adjoint identity for all
smooth `u` and `v`
(`TauCeti.exists_mem_classicalPseudodifferentialOperators_forall_integral_inner_eq`), and it is
unique (`TauCeti.eq_of_forall_integral_inner_eq_of_forall_integral_inner_eq`), because
`μ` is positive on nonempty open sets, so a smooth function orthogonal to itself vanishes. In
particular the formal adjoint of an elliptic operator is elliptic
(`TauCeti.IsClassicalElliptic.exists_isClassicalElliptic_forall_integral_inner_eq`). In the
Fredholm theory of elliptic operators on compact manifolds, the kernel of the formal adjoint
describes the cokernel of `P`.

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
* `TauCeti.isClassicalEllipticAt_iff_of_forall_integral_inner_eq`,
  `TauCeti.isClassicalElliptic_iff_of_forall_integral_inner_eq`: a properly supported formal
  adjoint is elliptic exactly where the operator is.
* `exists_mem_classicalPseudodifferentialOperators_forall_hasCompactSupport_integral_inner_eq`:
  on a σ-compact manifold of positive dimension, every classical pseudodifferential operator has a
  formal adjoint of the same order with conjugate principal symbol.
* `TauCeti.exists_mem_classicalPseudodifferentialOperators_forall_integral_inner_eq`: on a compact
  manifold of positive dimension, the formal adjoint satisfies the adjoint identity for all smooth
  functions.
* `TauCeti.eq_of_forall_integral_inner_eq_of_forall_integral_inner_eq`: on a compact
  manifold, formal adjoints for a finite measure positive on open sets are unique.
* `TauCeti.IsClassicalElliptic.exists_isClassicalElliptic_forall_integral_inner_eq`: on a compact
  manifold of positive dimension, the formal adjoint of an elliptic operator is elliptic.

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

/-- **The formal adjoint of an elliptic operator is elliptic.** Under the hypotheses of
`TauCeti.mem_classicalPseudodifferentialOperators_of_forall_integral_inner_eq`, the formal adjoint
`Q` of `P` is elliptic at `x` exactly when `P` is, since its principal symbol is the complex
conjugate of that of `P`. -/
theorem isClassicalEllipticAt_iff_of_forall_integral_inner_eq
    (hμ : HasSmoothPositiveDensity (CoordinateSpace n) μ)
    (hP : P ∈ classicalPseudodifferentialOperators m) (hQ : IsProperlySupported Q)
    (hPQ : ∀ u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯, HasCompactSupport u →
      HasCompactSupport v → ∫ x, inner ℂ (P u x) (v x) ∂μ = ∫ x, inner ℂ (u x) (Q v x) ∂μ)
    (x : M) : IsClassicalEllipticAt m Q x ↔ IsClassicalEllipticAt m P x := by
  simp only [isClassicalEllipticAt_iff,
    classicalPrincipalSymbol_eq_conj_of_forall_integral_inner_eq hμ hP hQ hPQ x, ne_eq,
    map_eq_zero]

/-- **The formal adjoint of an elliptic operator is elliptic.** Under the hypotheses of
`TauCeti.mem_classicalPseudodifferentialOperators_of_forall_integral_inner_eq`, the formal adjoint
`Q` of `P` is elliptic exactly when `P` is. -/
theorem isClassicalElliptic_iff_of_forall_integral_inner_eq
    (hμ : HasSmoothPositiveDensity (CoordinateSpace n) μ)
    (hP : P ∈ classicalPseudodifferentialOperators m) (hQ : IsProperlySupported Q)
    (hPQ : ∀ u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯, HasCompactSupport u →
      HasCompactSupport v → ∫ x, inner ℂ (P u x) (v x) ∂μ = ∫ x, inner ℂ (u x) (Q v x) ∂μ) :
    IsClassicalElliptic m Q ↔ IsClassicalElliptic m P := by
  simp only [isClassicalElliptic_iff,
    isClassicalEllipticAt_iff_of_forall_integral_inner_eq hμ hP hQ hPQ]

/-! ### Existence on a σ-compact manifold -/

section SigmaCompact

variable [BorelSpace M] [IsFiniteMeasureOnCompacts μ]

omit [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] in
/-- For a measure finite on compact sets, the pairing of two smooth functions one of which has
compact support is integrable. -/
private theorem integrable_inner_of_hasCompactSupport
    {f g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
    (h : HasCompactSupport f ∨ HasCompactSupport g) :
    Integrable (fun x ↦ inner ℂ (f x) (g x)) μ := by
  refine (f.contMDiff.continuous.inner g.contMDiff.continuous).integrable_of_hasCompactSupport ?_
  rcases h with h | h
  · exact h.mono fun x hx h0 ↦ hx (by simp [h0])
  · exact h.mono fun x hx h0 ↦ hx (by simp [h0])

/-- **Formal adjoints of localized operators.** If `ρ` and `τ` are cutoffs in two charts and `P` is
a classical pseudodifferential operator of order `m`, then `ρ P τ`, with the cutoffs read on `M`,
has a formal adjoint for `μ` which is a classical pseudodifferential operator of order `m`. Indeed
`ρ P τ` is a finite sum of chart quantizations
(`TauCeti.exists_mulLeft_comp_comp_mulLeft_eq_sum_chartQuantization`). -/
private theorem exists_mem_forall_integral_inner_mulLeft_comp_comp_mulLeft_eq [NeZero n]
    (hμ : HasSmoothPositiveDensity (CoordinateSpace n) μ)
    (hP : P ∈ classicalPseudodifferentialOperators m)
    {e e' : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ρ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (τ : 𝓓(⟨e'.target, e'.open_target⟩, ℝ)) :
    ∃ Q ∈ classicalPseudodifferentialOperators m,
      ∀ u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
        ∫ x, inner ℂ ((LinearMap.mulLeft ℂ (e.complexCutoffPullback he ρ 1) ∘ₗ P ∘ₗ
          LinearMap.mulLeft ℂ (e'.complexCutoffPullback he' τ 1)) u x) (v x) ∂μ =
          ∫ x, inner ℂ (u x) (Q v x) ∂μ := by
  obtain ⟨k, e'', he'', φ, ψ, a, h⟩ :=
    exists_mulLeft_comp_comp_mulLeft_eq_sum_chartQuantization hP he ρ he' τ
  choose ρ' hρ hρ0 hρμ using fun i ↦ hμ.exists_map_restrict_source_eq_withDensity (he'' i)
  obtain ⟨Q, hQ, hadj, -⟩ :=
    exists_mem_classicalPseudodifferentialOperators_integral_inner_sum_chartQuantization_eq
      Finset.univ he'' (fun i _ ↦ hρ i) (fun i _ ↦ hρ0 i) (fun i _ ↦ hρμ i) φ ψ a
  exact ⟨Q, hQ, fun u v ↦ by rw [h]; exact hadj u v⟩

omit [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] in
/-- **Splitting a pairing along a partition of unity.** If the functions `gᵢ` add up to `1` and `u`,
`v` have compact supports, met only by the supports of the `gⱼ` with `j ∈ Fᵤ` and of the `gᵢ` with
`i ∈ Fᵥ`, then `∫ ⟪P u, v⟫ dμ = ∑_{i ∈ Fᵥ} ∑_{j ∈ Fᵤ} ∫ ⟪gᵢ P (gⱼ u), v⟫ dμ`. -/
private theorem integral_inner_eq_sum_sum_mulLeft_comp_comp_mulLeft {ι : Type*}
    {g : ι → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} (hg : ∀ x, ∑ᶠ i, g i x = 1)
    {u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} (hv : HasCompactSupport v)
    {Fu Fv : Finset ι} (hFu : ∀ i, ∀ x ∈ tsupport u, g i x ≠ 0 → i ∈ Fu)
    (hFv : ∀ i, ∀ x ∈ tsupport v, g i x ≠ 0 → i ∈ Fv) :
    ∫ x, inner ℂ (P u x) (v x) ∂μ = ∑ i ∈ Fv, ∑ j ∈ Fu,
      ∫ x, inner ℂ ((LinearMap.mulLeft ℂ (g i) ∘ₗ P ∘ₗ LinearMap.mulLeft ℂ (g j)) u x) (v x)
        ∂μ := by
  -- On a compact set `K`, the `gᵢ` with `i` in a finite set containing all those not vanishing on
  -- `K` add up to `1`.
  have hsum (F : Finset ι) (K : Set M) (hF : ∀ i, ∀ x ∈ K, g i x ≠ 0 → i ∈ F) (x : M)
      (hx : x ∈ K) : ∑ i ∈ F, g i x = 1 := by
    rw [← finsum_eq_sum_of_support_subset _ fun i hi ↦ hF i x hx hi, hg x]
  -- `u = ∑_{j ∈ Fᵤ} gⱼ u`.
  have hu : u = ∑ j ∈ Fu, g j * u := by
    ext x
    rw [ContMDiffMap.coe_sum, Finset.sum_apply]
    by_cases hx : x ∈ tsupport u
    · simp [← Finset.sum_mul, hsum Fu _ hFu x hx]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  -- `⟪P u, v⟫ = ∑_{i ∈ Fᵥ} ⟪gᵢ P u, v⟫` pointwise.
  have hPu (x : M) : inner ℂ (P u x) (v x) = ∑ i ∈ Fv, inner ℂ ((g i * P u) x) (v x) := by
    by_cases hx : x ∈ tsupport v
    · have hi (i : ι) : inner ℂ ((g i * P u) x) (v x) = conj (g i x) * inner ℂ (P u x) (v x) := by
        simp only [ContMDiffMap.coe_mul, Pi.mul_apply, RCLike.inner_apply, map_mul]
        ring
      rw [Finset.sum_congr rfl fun i _ ↦ hi i, ← Finset.sum_mul, ← map_sum, hsum Fv _ hFv x hx,
        map_one, one_mul]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hint (w : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
      Integrable (fun x ↦ inner ℂ (w x) (v x)) μ := integrable_inner_of_hasCompactSupport (.inr hv)
  simp_rw [hPu]
  rw [integral_finsetSum _ fun i _ ↦ hint _]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  conv_lhs => rw [hu, map_sum, Finset.mul_sum, ContMDiffMap.coe_sum]
  simp only [Finset.sum_apply, sum_inner]
  rw [integral_finsetSum _ fun j _ ↦ hint _]
  rfl

omit [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] in
/-- **Pairing with a locally finite sum.** If `u` has compact support and, at the points of its
support, `Qₚ v` only fails to vanish for `p` in a finite set `F`, then
`∫ ⟪u, (∑ₚ Qₚ) v⟫ dμ = ∑_{p ∈ F} ∫ ⟪u, Qₚ v⟫ dμ`. -/
private theorem integral_inner_locallyFiniteSum_eq_sum {κ : Type*}
    {Q : κ → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
    {hQ : ∀ f, LocallyFinite fun p ↦ Function.support (Q p f)}
    {u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} (hu : HasCompactSupport u) {F : Finset κ}
    (hF : ∀ p, ∀ x ∈ tsupport u, Q p v x ≠ 0 → p ∈ F) :
    ∫ x, inner ℂ (u x) (ContMDiffMap.locallyFiniteSum Q hQ v x) ∂μ =
      ∑ p ∈ F, ∫ x, inner ℂ (u x) (Q p v x) ∂μ := by
  rw [← integral_finsetSum _ fun p _ ↦ integrable_inner_of_hasCompactSupport (.inl hu)]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  dsimp only
  by_cases hx : x ∈ tsupport u
  · rw [ContMDiffMap.locallyFiniteSum_apply, finsum_eq_sum_of_support_subset _
      fun p hp ↦ hF p x hx hp, inner_sum]
  · simp [image_eq_zero_of_notMem_tsupport hx]

omit [MeasurableSpace M] [BorelSpace M] [IsFiniteMeasureOnCompacts μ]
  [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] in
/-- Multiplication by a real cutoff read on `M` moves across the pairing. -/
private theorem inner_mul_complexCutoffPullback_apply
    {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (χ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (a b : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯)
    (x : M) :
    inner ℂ (a x) ((e.complexCutoffPullback he χ 1 * b) x) =
      inner ℂ ((e.complexCutoffPullback he χ 1 * a) x) (b x) := by
  simp only [ContMDiffMap.coe_mul, Pi.mul_apply, RCLike.inner_apply, map_mul,
    OpenPartialHomeomorph.complexCutoffPullback_one_apply, Complex.conj_ofReal]
  ring

omit [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] [BorelSpace M]
  [IsFiniteMeasureOnCompacts μ] in
/-- **Localizing a formal adjoint.** If `Q₀` is a formal adjoint of `g₁ P g₂`, and the real-valued
functions `h₁`, `h₂` are `1` on the supports of `g₁`, `g₂`, then `h₂ Q₀ h₁` is one as well. -/
private theorem integral_inner_mulLeft_comp_comp_mulLeft_eq_of_mul_eq
    {g₁ g₂ h₁ h₂ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} (hhg₁ : g₁ * h₁ = g₁)
    (hhg₂ : g₂ * h₂ = g₂)
    (hh₁ : ∀ a b : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯, ∀ x,
      inner ℂ (a x) ((h₁ * b) x) = inner ℂ ((h₁ * a) x) (b x))
    (hh₂ : ∀ a b : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯, ∀ x,
      inner ℂ (a x) ((h₂ * b) x) = inner ℂ ((h₂ * a) x) (b x))
    (hadj : ∀ u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ∫ x, inner ℂ ((LinearMap.mulLeft ℂ g₁ ∘ₗ P ∘ₗ LinearMap.mulLeft ℂ g₂) u x) (v x) ∂μ =
        ∫ x, inner ℂ (u x) (Q v x) ∂μ)
    (u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    ∫ x, inner ℂ ((LinearMap.mulLeft ℂ g₁ ∘ₗ P ∘ₗ LinearMap.mulLeft ℂ g₂) u x) (v x) ∂μ =
      ∫ x, inner ℂ (u x)
        ((LinearMap.mulLeft ℂ h₂ ∘ₗ Q ∘ₗ LinearMap.mulLeft ℂ h₁) v x) ∂μ := by
  have hT : (LinearMap.mulLeft ℂ g₁ ∘ₗ P ∘ₗ LinearMap.mulLeft ℂ g₂) u =
      h₁ * (LinearMap.mulLeft ℂ g₁ ∘ₗ P ∘ₗ LinearMap.mulLeft ℂ g₂) (h₂ * u) := by
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, ← mul_assoc, hhg₂,
      mul_comm h₁ g₁, hhg₁]
  rw [hT]
  calc _ = ∫ x, inner ℂ ((LinearMap.mulLeft ℂ g₁ ∘ₗ P ∘ₗ LinearMap.mulLeft ℂ g₂) (h₂ * u) x)
          ((h₁ * v) x) ∂μ := integral_congr_ae (.of_forall fun x ↦ (hh₁ _ _ x).symm)
    _ = ∫ x, inner ℂ ((h₂ * u) x) (Q (h₁ * v) x) ∂μ := hadj _ _
    _ = _ := integral_congr_ae (.of_forall fun x ↦ (hh₂ _ _ x).symm)

omit [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] in
/-- **Assembling formal adjoints of pieces.** Let `gᵢ` add up to `1`, with supports in sets `Bᵢ`
forming a locally finite family, and let `Q'ᵢⱼ` be formal adjoints of the pieces `gᵢ P gⱼ` whose
outputs lie in `Bⱼ` and which only see their inputs on `Bᵢ`. Then the locally finite sum of the
`Q'ᵢⱼ` is a formal adjoint of `P` on compactly supported functions. -/
private theorem integral_inner_eq_integral_inner_locallyFiniteSum {ι : Type*}
    {g : ι → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {B : ι → Set M} (hB : LocallyFinite B)
    (hgB : ∀ i, tsupport (g i) ⊆ B i) (hg1 : ∀ x, ∑ᶠ i, g i x = 1)
    {Q' : ι × ι → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
    {hQ' : ∀ f, LocallyFinite fun p ↦ Function.support (Q' p f)}
    (hadj : ∀ i j, ∀ u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ∫ x, inner ℂ ((LinearMap.mulLeft ℂ (g i) ∘ₗ P ∘ₗ LinearMap.mulLeft ℂ (g j)) u x) (v x) ∂μ =
        ∫ x, inner ℂ (u x) (Q' (i, j) v x) ∂μ)
    (hQ'B : ∀ p f x, Q' p f x ≠ 0 → x ∈ B p.2 ∧ ∃ y ∈ B p.1, f y ≠ 0)
    {u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} (hu : HasCompactSupport u)
    (hv : HasCompactSupport v) :
    ∫ x, inner ℂ (P u x) (v x) ∂μ =
      ∫ x, inner ℂ (u x) (ContMDiffMap.locallyFiniteSum Q' hQ' v x) ∂μ := by
  -- Only the pieces with `Bᵢ` meeting the support of `v` and `Bⱼ` meeting that of `u` contribute.
  have hmem {K : Set M} (hK : IsCompact K) {i : ι} {x : M} (hxB : x ∈ B i) (hxK : x ∈ K) :
      i ∈ (hB.finite_nonempty_inter_compact hK).toFinset :=
    (hB.finite_nonempty_inter_compact hK).mem_toFinset.2 ⟨x, hxB, hxK⟩
  have hF (p : ι × ι) (x : M) (hx : x ∈ tsupport u) (hp : Q' p v x ≠ 0) :
      p ∈ (hB.finite_nonempty_inter_compact hv).toFinset ×ˢ
        (hB.finite_nonempty_inter_compact hu).toFinset := by
    obtain ⟨hxB, y, hyB, hy⟩ := hQ'B p v x hp
    exact Finset.mem_product.2 ⟨hmem hv hyB (subset_tsupport _ hy), hmem hu hxB hx⟩
  rw [integral_inner_eq_sum_sum_mulLeft_comp_comp_mulLeft hg1 hv
      (fun i x hx hgx ↦ hmem hu (hgB i (subset_tsupport _ hgx)) hx)
      (fun i x hx hgx ↦ hmem hv (hgB i (subset_tsupport _ hgx)) hx),
    integral_inner_locallyFiniteSum_eq_sum hu hF, Finset.sum_product]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ hadj i j u v

omit [MeasurableSpace M] [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] [BorelSpace M]
  [IsFiniteMeasureOnCompacts μ] in
/-- If `h₂ Q (h₁ f)` does not vanish at `x`, then `x` lies in the support of `h₂` and `f` does not
vanish somewhere on the support of `h₁`. -/
private theorem mem_tsupport_and_exists_of_mulLeft_comp_comp_mulLeft_apply_ne_zero
    {h₁ h₂ f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {x : M}
    (hx : (LinearMap.mulLeft ℂ h₂ ∘ₗ Q ∘ₗ LinearMap.mulLeft ℂ h₁) f x ≠ 0) :
    x ∈ tsupport h₂ ∧ ∃ y ∈ tsupport h₁, f y ≠ 0 := by
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, ContMDiffMap.coe_mul,
    Pi.mul_apply] at hx
  obtain ⟨y, hy⟩ : ∃ y, (h₁ * f) y ≠ 0 := by
    by_contra! hy
    have h0 : h₁ * f = 0 := ContMDiffMap.ext fun y ↦ by simpa using hy y
    exact right_ne_zero_of_mul hx (by rw [h0, map_zero]; rfl)
  rw [ContMDiffMap.coe_mul, Pi.mul_apply] at hy
  exact ⟨subset_tsupport _ (left_ne_zero_of_mul hx), y,
    subset_tsupport _ (left_ne_zero_of_mul hy), right_ne_zero_of_mul hy⟩

omit [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] in
/-- **Formal adjoints from a partition of unity.** Let `gᵢ` add up to `1`, with supports in compact
sets `Bᵢ` forming a locally finite family, and let `hᵢ` be real-valued functions supported in `Bᵢ`
and equal to `1` on the support of `gᵢ`. If every piece `gᵢ P gⱼ` of a classical
pseudodifferential operator `P` of order `m` has a formal adjoint of order `m`, then `P` has a
formal adjoint of order `m` on compactly supported functions: the locally finite sum of the
localized adjoints `hⱼ Q₀ᵢⱼ hᵢ` of the nonzero pieces. -/
private theorem exists_mem_forall_hasCompactSupport_integral_inner_eq_of_partition {ι : Type*}
    {g h : ι → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {B : ι → Set M}
    (hB : LocallyFinite B) (hBc : ∀ i, IsCompact (B i)) (hgB : ∀ i, tsupport (g i) ⊆ B i)
    (hhB : ∀ i, tsupport (h i) ⊆ B i) (hhg : ∀ i, g i * h i = g i) (hg1 : ∀ x, ∑ᶠ i, g i x = 1)
    (hh : ∀ i, ∀ a b : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯, ∀ x,
      inner ℂ (a x) ((h i * b) x) = inner ℂ ((h i * a) x) (b x))
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (hpair : ∀ i j, ∃ Q ∈ classicalPseudodifferentialOperators m,
      ∀ u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
        ∫ x, inner ℂ ((LinearMap.mulLeft ℂ (g i) ∘ₗ P ∘ₗ LinearMap.mulLeft ℂ (g j)) u x) (v x) ∂μ =
          ∫ x, inner ℂ (u x) (Q v x) ∂μ) :
    ∃ Q ∈ classicalPseudodifferentialOperators m,
      ∀ u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯, HasCompactSupport u →
        HasCompactSupport v → ∫ x, inner ℂ (P u x) (v x) ∂μ = ∫ x, inner ℂ (u x) (Q v x) ∂μ := by
  classical
  set T := fun i j ↦ LinearMap.mulLeft ℂ (g i) ∘ₗ P ∘ₗ LinearMap.mulLeft ℂ (g j)
  -- Formal adjoints `Q₀ᵢⱼ` of the pieces, chosen zero when the piece is, localized by `hᵢ`, `hⱼ`.
  have hpair' (i j : ι) : ∃ Q ∈ classicalPseudodifferentialOperators m,
      (∀ u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
        ∫ x, inner ℂ (T i j u x) (v x) ∂μ = ∫ x, inner ℂ (u x) (Q v x) ∂μ) ∧
      (T i j = 0 → Q = 0) := by
    by_cases hT : T i j = 0
    · exact ⟨0, zero_mem _, fun u v ↦ by simp [hT], fun _ ↦ rfl⟩
    · obtain ⟨Q, hQ, hQa⟩ := hpair i j
      exact ⟨Q, hQ, hQa, fun h ↦ (hT h).elim⟩
  choose Q₀ hQ₀ hadj₀ hQ₀0 using hpair'
  set Q' := fun p : ι × ι ↦ LinearMap.mulLeft ℂ (h p.2) ∘ₗ Q₀ p.1 p.2 ∘ₗ LinearMap.mulLeft ℂ (h p.1)
  -- `Q'ᵢⱼ` has outputs supported in `Bⱼ`, only sees its input on `Bᵢ`, and vanishes with `Tᵢⱼ`.
  set S := fun p : ι × ι ↦ {x | x ∈ B p.1 ∪ B p.2 ∧ T p.1 p.2 ≠ 0}
  have hS : LocallyFinite S := (mem_classicalPseudodifferentialOperators_iff.1 hP).1
    |>.locallyFinite_setOf_mem_union_and_mulLeft_comp_comp_mulLeft_ne_zero hB hgB
      fun i ↦ (hBc i).of_isClosed_subset (isClosed_tsupport _) (hgB i)
  have hsupp (p : ι × ι) (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
      tsupport (Q' p f) ⊆ S p := by
    by_cases hT : T p.1 p.2 = 0
    · simp [Q', hQ₀0 _ _ hT]
    · intro x hx
      simp only [Q', LinearMap.comp_apply, LinearMap.mulLeft_apply, ContMDiffMap.coe_mul] at hx
      exact ⟨Or.inr (hhB _ (tsupport_mul_subset_left hx)), hT⟩
  have hloc (p : ι × ι) (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯)
      (hf : ∀ᶠ y in 𝓝ˢ (S p), f y = 0) : Q' p f = 0 := by
    by_cases hT : T p.1 p.2 = 0
    · simp [Q', hQ₀0 _ _ hT]
    · have hhf : h p.1 * f = 0 := by
        ext x
        rw [ContMDiffMap.coe_mul, Pi.mul_apply, ContMDiffMap.coe_zero, Pi.zero_apply]
        by_cases hx : x ∈ tsupport (h p.1)
        · rw [hf.self_of_nhdsSet x ⟨Or.inl (hhB _ hx), hT⟩, mul_zero]
        · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
      simp [Q', hhf]
  have hQ' (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
      LocallyFinite fun p ↦ Function.support (Q' p f) :=
    hS.subset fun p ↦ (subset_tsupport _).trans (hsupp p f)
  refine ⟨ContMDiffMap.locallyFiniteSum Q' hQ',
    locallyFiniteSum_mem_classicalPseudodifferentialOperators hS (fun p ↦ ?_)
      (fun p ↦ mulLeft_comp_mem_classicalPseudodifferentialOperators
        (comp_mulLeft_mem_classicalPseudodifferentialOperators (hQ₀ _ _) _) _) hsupp hloc,
    fun u v hu hv ↦ integral_inner_eq_integral_inner_locallyFiniteSum hB hgB hg1
      (fun i j ↦ integral_inner_mulLeft_comp_comp_mulLeft_eq_of_mul_eq (hhg i) (hhg j) (hh i)
        (hh j) (hadj₀ i j)) (fun p f x hx ↦ ?_) hu hv⟩
  · by_cases hT : T p.1 p.2 = 0
    · simp [S, hT]
    · simpa [S, hT] using (hBc p.1).union (hBc p.2)
  · exact (mem_tsupport_and_exists_of_mulLeft_comp_comp_mulLeft_apply_ne_zero hx).imp
      (fun hx ↦ hhB _ hx) fun ⟨y, hy, hfy⟩ ↦ ⟨y, hhB _ hy, hfy⟩

/-- **Classical pseudodifferential operators on a σ-compact manifold have formal adjoints.** Let `M`
be a σ-compact manifold modelled on `ℝⁿ` with `n ≠ 0`, compact or not, and `μ` a measure on `M`
finite on compact sets with a smooth positive density. A classical pseudodifferential operator `P`
of order `m` has a formal adjoint `Q` for `μ`,

`∫ ⟪P u, v⟫ dμ = ∫ ⟪u, Q v⟫ dμ`

for all compactly supported smooth `u` and `v`, which is a classical pseudodifferential operator of
order `m`, in particular properly supported, with principal symbol
`σ_m(Q)(x, ξ) = conj σ_m(P)(x, ξ)`.

With a locally finite partition of unity `gᵢ` in charts, `Q` is the locally finite sum of formal
adjoints of the pieces `gᵢ P gⱼ`, each a finite sum of chart quantizations. Proper support of `P`
leaves only finitely many nonzero pieces near every compact set. -/
theorem exists_mem_classicalPseudodifferentialOperators_forall_hasCompactSupport_integral_inner_eq
    [SigmaCompactSpace M] [NeZero n] (hμ : HasSmoothPositiveDensity (CoordinateSpace n) μ)
    (hP : P ∈ classicalPseudodifferentialOperators m) :
    ∃ Q ∈ classicalPseudodifferentialOperators m,
      (∀ u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯, HasCompactSupport u →
        HasCompactSupport v → ∫ x, inner ℂ (P u x) (v x) ∂μ = ∫ x, inner ℂ (u x) (Q v x) ∂μ) ∧
      ∀ x ξ, classicalPrincipalSymbol m Q x ξ = conj (classicalPrincipalSymbol m P x ξ) := by
  -- A locally finite partition of unity `gᵢ = ρᵢ ∘ eᵢ` in charts, and cutoffs `hᵢ = χᵢ ∘ eᵢ` equal
  -- to `1` near the supports of the `gᵢ`, supported in compact sets `Bᵢ`, `(Bᵢ)` locally finite.
  obtain ⟨ι, c, ρ, W, hW, hWf, hρ⟩ :=
    exists_locallyFinite_finsum_cutoffPullback_eq_one (E := CoordinateSpace n) (M := M)
  set e := fun i ↦ chartAt (CoordinateSpace n) (c i)
  have he (i : ι) : e i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M :=
    IsManifold.chart_mem_maximalAtlas (c i)
  choose χ _ hχ hχW using fun i ↦ TestFunction.exists_cutoff_tsupport_subset (n := ⊤)
    (Ω := ⟨(e i).target, (e i).open_target⟩) (ρ i).hasCompactSupport.isCompact (hW i).1
    (hW i).2.1 (hW i).2.2
  set g := fun i ↦ (e i).complexCutoffPullback (he i) (ρ i) 1
  set h := fun i ↦ (e i).complexCutoffPullback (he i) (χ i) 1
  have hhg (i : ι) : g i * h i = g i :=
    (e i).complexCutoffPullback_one_mul_complexCutoffPullback_one_of_tsupport_subset (he i)
      fun y hy ↦ (hχ i).self_of_nhdsSet y hy
  have hhB (i : ι) : tsupport (h i) ⊆ (e i).symm '' tsupport (χ i) :=
    (e i).tsupport_complexCutoffPullback_subset (he i) _ _
  have hg1 (x : M) : ∑ᶠ i, g i x = 1 := by
    have hfin : (Function.support fun i ↦ (e i).cutoffPullback (he i) (ρ i) 1 x).Finite :=
      (hWf.point_finite x).subset fun i hi ↦ image_mono (hW i).2.1
        ((e i).tsupport_cutoffPullback_subset (he i) _ _ (subset_tsupport _ hi))
    simp only [g, OpenPartialHomeomorph.complexCutoffPullback_one_apply]
    rw [← Complex.ofReal_one, ← hρ x]
    exact (map_finsum Complex.ofRealHom hfin).symm
  -- Each piece `gᵢ P gⱼ` is a finite sum of chart quantizations, so it has a formal adjoint.
  obtain ⟨Q, hQ, hadj⟩ := exists_mem_forall_hasCompactSupport_integral_inner_eq_of_partition
    (hWf.subset fun i ↦ image_mono (hχW i)) (fun i ↦ (e i).isCompact_symm_image_tsupport (χ i))
    (fun i ↦ by rw [← hhg i, ContMDiffMap.coe_mul]; exact tsupport_mul_subset_right.trans (hhB i))
    hhB hhg hg1 (fun i ↦ inner_mul_complexCutoffPullback_apply (he i) (χ i)) hP
    fun i j ↦ exists_mem_forall_integral_inner_mulLeft_comp_comp_mulLeft_eq hμ hP (he i) (he j)
      (ρ i) (ρ j)
  exact ⟨Q, hQ, hadj, fun x ξ ↦ classicalPrincipalSymbol_eq_conj_of_forall_integral_inner_eq hμ hP
    (mem_classicalPseudodifferentialOperators_iff.1 hQ).1 hadj x ξ⟩

end SigmaCompact

/-! ### Existence and uniqueness on a compact manifold -/

section Compact

variable [BorelSpace M] [CompactSpace M] [IsFiniteMeasure μ]

omit [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] in
/-- **Formal adjoints are unique.** On a compact manifold with a finite measure `μ` that is positive
on nonempty open sets, for instance a finite measure with a smooth positive density
(`TauCeti.HasSmoothPositiveDensity.isPositiveDensityMeasure`), an operator `P` on the
complex-valued smooth functions has at most one formal adjoint: if
`∫ ⟪P u, v⟫ dμ = ∫ ⟪u, Q₁ v⟫ dμ = ∫ ⟪u, Q₂ v⟫ dμ` for all smooth `u` and `v`, then `Q₁ = Q₂`. -/
theorem eq_of_forall_integral_inner_eq_of_forall_integral_inner_eq [μ.IsOpenPosMeasure]
    {Q₁ Q₂ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
    (h₁ : ∀ u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ∫ x, inner ℂ (P u x) (v x) ∂μ = ∫ x, inner ℂ (u x) (Q₁ v x) ∂μ)
    (h₂ : ∀ u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      ∫ x, inner ℂ (P u x) (v x) ∂μ = ∫ x, inner ℂ (u x) (Q₂ v x) ∂μ) :
    Q₁ = Q₂ := by
  refine LinearMap.ext fun v ↦ ?_
  -- `w = Q₁ v - Q₂ v` is orthogonal to every smooth function, in particular to itself.
  set w := Q₁ v - Q₂ v
  have hint : ∀ f g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      Integrable (fun x ↦ inner ℂ (f x) (g x)) μ := fun f g ↦
    (f.contMDiff.continuous.inner g.contMDiff.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hw : ∫ x, ((‖w x‖ ^ 2 : ℝ) : ℂ) ∂μ = 0 := by
    rw [← sub_eq_zero.2 ((h₁ w v).symm.trans (h₂ w v)), ← integral_sub (hint _ _) (hint _ _)]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    dsimp only
    rw [← inner_sub_right, ← Pi.sub_apply, ← ContMDiffMap.coe_sub]
    simp [w, inner_self_eq_norm_sq_to_K]
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at hw
  ext x
  by_contra hx
  refine (Continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero (μ := μ) (x := x)
    (w.contMDiff.continuous.norm.pow 2) (HasCompactSupport.of_compactSpace _)
    (fun _ ↦ sq_nonneg _) ?_).ne' hw
  simpa [w, sub_eq_zero] using hx

/-- **Classical pseudodifferential operators on a compact manifold have formal adjoints.** Let `M`
be a compact manifold modelled on `ℝⁿ` with `n ≠ 0`, and `μ` a finite measure on `M` with a smooth
positive density. A classical pseudodifferential operator `P` of
order `m` has a formal adjoint `Q` for `μ`,

`∫ ⟪P u, v⟫ dμ = ∫ ⟪u, Q v⟫ dμ`

for all smooth `u` and `v`, which is a classical pseudodifferential operator of order `m` with
principal symbol `σ_m(Q)(x, ξ) = conj σ_m(P)(x, ξ)`. It is unique
(`TauCeti.eq_of_forall_integral_inner_eq_of_forall_integral_inner_eq`), since `μ` is
positive on nonempty open sets. -/
theorem exists_mem_classicalPseudodifferentialOperators_forall_integral_inner_eq [NeZero n]
    (hμ : HasSmoothPositiveDensity (CoordinateSpace n) μ)
    (hP : P ∈ classicalPseudodifferentialOperators m) :
    ∃ Q ∈ classicalPseudodifferentialOperators m,
      (∀ u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
        ∫ x, inner ℂ (P u x) (v x) ∂μ = ∫ x, inner ℂ (u x) (Q v x) ∂μ) ∧
      ∀ x ξ, classicalPrincipalSymbol m Q x ξ = conj (classicalPrincipalSymbol m P x ξ) := by
  -- On a compact manifold every smooth function has compact support.
  obtain ⟨Q, hQ, hadj, hσ⟩ :=
    exists_mem_classicalPseudodifferentialOperators_forall_hasCompactSupport_integral_inner_eq hμ hP
  exact ⟨Q, hQ, fun u v ↦ hadj u v (.of_compactSpace _) (.of_compactSpace _), hσ⟩

/-- **The formal adjoint of an elliptic operator is elliptic.** On a compact manifold modelled on
`ℝⁿ` with `n ≠ 0`, with a finite measure `μ` that has a smooth positive density, the formal adjoint
of an elliptic classical pseudodifferential operator `P` of order `m`
(`TauCeti.exists_mem_classicalPseudodifferentialOperators_forall_integral_inner_eq`) is an elliptic
classical pseudodifferential operator of order `m`. -/
theorem IsClassicalElliptic.exists_isClassicalElliptic_forall_integral_inner_eq [NeZero n]
    (hμ : HasSmoothPositiveDensity (CoordinateSpace n) μ)
    (hP : P ∈ classicalPseudodifferentialOperators m) (hPe : IsClassicalElliptic m P) :
    ∃ Q ∈ classicalPseudodifferentialOperators m, IsClassicalElliptic m Q ∧
      ∀ u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
        ∫ x, inner ℂ (P u x) (v x) ∂μ = ∫ x, inner ℂ (u x) (Q v x) ∂μ := by
  obtain ⟨Q, hQ, hPQ, hσ⟩ :=
    exists_mem_classicalPseudodifferentialOperators_forall_integral_inner_eq hμ hP
  refine ⟨Q, hQ, isClassicalElliptic_iff.2 fun x ↦ isClassicalEllipticAt_iff.2 fun ξ hξ ↦ ?_, hPQ⟩
  simpa [hσ] using isClassicalEllipticAt_iff.1 (isClassicalElliptic_iff.1 hPe x) ξ hξ

end Compact

end TauCeti
