/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.SymbolQuantization
public import TauCeti.Analysis.Pseudodifferential.Adjoint.Classical
public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical.SmulLeft
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.InnerProductSpace.OperatorIdentities
import TauCeti.Geometry.Manifold.Measure.Chart

/-!
# Formal adjoints of chart quantizations

Let `M` be a manifold modelled on `ℝⁿ` and `μ` a measure on `M` that reads in a chart `e` of the
maximal atlas as `ρ(y) dy`, with `ρ` smooth and positive on the chart target, as a Riemannian
volume does in every chart. An operator `Q` on the complex-valued smooth functions on `M` is a
formal adjoint of `P` for `μ` when

`∫ ⟪P u, v⟫ dμ = ∫ ⟪u, Q v⟫ dμ`

for all smooth `u` and `v`. This file shows that the chart quantization
`Op_e(a) : u ↦ (φ · Op(a) (ψ · (u ∘ e⁻¹))) ∘ e` of a classical symbol `a` of order `m`
(`OpenPartialHomeomorph.chartQuantization`) has a formal adjoint which is again a chart
quantization `Op_e(b)` of a classical symbol `b` of order `m`, localized by cutoffs `θ` and `χ`
equal to `1` on the supports of `ψ` and `φ`
(`OpenPartialHomeomorph.exists_integral_inner_chartQuantization_eq`). In the chart, the pairing
of `Op_e(a) u` with `v` against `μ` is the pairing of `Op(c) (ψ · (u ∘ e⁻¹))` with
`χ · (v ∘ e⁻¹)` against Lebesgue measure, for the symbol `c = φ ρ a` with compact spatial support,
so the Euclidean adjoint symbol `c*` (`TauCeti.ClassicalSymbol.adjoint`) gives `b = (ψ / ρ) c*`.
Its principal symbol is `φ ψ σ(a)†`.

So the formal adjoint of a chart quantization is a classical pseudodifferential operator of
order `m` whose principal symbol is the complex conjugate of that of `Op_e(a)`
(`exists_mem_classicalPseudodifferentialOperators_integral_inner_chartQuantization_eq`, in the
namespace `OpenPartialHomeomorph`), and the same holds for finite sums of chart quantizations in
charts where `μ` has smooth positive densities
(`exists_mem_classicalPseudodifferentialOperators_integral_inner_sum_chartQuantization_eq`, in the
namespace `TauCeti`).

## Main results

* `OpenPartialHomeomorph.exists_integral_inner_chartQuantization_eq`: the formal adjoint of a chart
  quantization is a chart quantization, with principal symbol `φ ψ σ(a)†`.
* `OpenPartialHomeomorph.integrable_inner_chartQuantization_apply`,
  `OpenPartialHomeomorph.integrable_inner_apply_chartQuantization`: the pairings of a chart
  quantization with smooth functions are integrable.
* `exists_mem_classicalPseudodifferentialOperators_integral_inner_chartQuantization_eq`:
  the formal adjoint of a chart quantization is a classical pseudodifferential operator of the
  same order with conjugate principal symbol.
* `exists_mem_classicalPseudodifferentialOperators_integral_inner_sum_chartQuantization_eq`:
  the same for finite sums of chart quantizations.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.7 and
  §18.1 after Definition 18.1.20.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (2.3)
  and §8.
-/

public section

noncomputable section

open MeasureTheory Set Filter TauCeti
open scoped ContDiff Manifold Distributions SchwartzMap Topology ENNReal

namespace OpenPartialHomeomorph

section Adjoint

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] {e : OpenPartialHomeomorph M (CoordinateSpace n)}
  (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M) {m : ℝ}

include he

variable [MeasurableSpace M] [BorelSpace M] {μ : Measure M} {ρ : CoordinateSpace n → ℝ}

/-- In the chart, the pairing `∫ ⟪Op_e(a) u, v⟫ dμ` is `∫ ⟪Op(a) w₁, φ ρ w₂⟫ dy`, for the readings
`w₁ = ψ · (u ∘ e⁻¹)` and `w₂ = χ · (v ∘ e⁻¹)` of `u` and `v`, with `χ = 1` on the support of `φ`. -/
private theorem integral_inner_chartQuantization_apply_eq (hρ : ContinuousOn ρ e.target)
    (hρ0 : ∀ y ∈ e.target, 0 < ρ y)
    (hμ : (μ.restrict e.source).map e =
      (volume.restrict e.target).withDensity fun y ↦ ENNReal.ofReal (ρ y))
    {φ ψ χ : 𝓓(⟨e.target, e.open_target⟩, ℝ)} (hχ : EqOn χ 1 (tsupport φ))
    (a : ClassicalSymbol n ℂ ℂ m) {u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
    {w₁ w₂ : 𝓢(CoordinateSpace n, ℂ)} (hw₁ : ∀ y, w₁ y = ψ y • u (e.symm y))
    (hw₂ : ∀ y, w₂ y = χ y • v (e.symm y)) :
    ∫ p, inner ℂ (e.chartQuantization he φ ψ a u p) (v p) ∂μ =
      ∫ y, inner ℂ (quantizeSchwartzValue a.toSymbol.coefficient w₁ y)
        (((φ y * ρ y : ℝ) : ℂ) * w₂ y) := by
  rw [integral_eq_setIntegral_target_smul hμ (hρ.aemeasurable e.open_target.measurableSet)
      (fun y hy ↦ (hρ0 y hy).le)
      ((e.chartQuantization he φ ψ a u).contMDiff.continuous.inner
        v.contMDiff.continuous).continuousOn
      fun p hp ↦ by simp [chartQuantization_apply_of_notMem he _ _ a u hp],
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := e.target)
      (f := fun y ↦ inner ℂ (quantizeSchwartzValue a.toSymbol.coefficient w₁ y)
        (((φ y * ρ y : ℝ) : ℂ) * w₂ y)) fun y hy ↦ by
      simp [image_eq_zero_of_notMem_tsupport fun h ↦ hy (φ.tsupport_subset h)]]
  refine setIntegral_congr_fun e.open_target.measurableSet fun y hy ↦ ?_
  rw [chartQuantization_apply_of_mem he φ ψ a u hw₁ (e.map_target hy), e.right_inv hy, hw₂]
  by_cases hφy : φ y = 0
  · simp [hφy]
  rw [hχ (subset_tsupport _ hφy)]
  simp only [Complex.real_smul, RCLike.inner_apply, map_mul, Complex.conj_ofReal,
    Complex.ofReal_mul, Pi.one_apply, Complex.ofReal_one]
  ring

/-- In the chart, the pairing `∫ ⟪u, Op_e(b) v⟫ dμ` is `∫_{e.target} ⟪u ∘ e⁻¹, ρ θ Op(b) w₂⟫ dy`,
for the reading `w₂ = χ · (v ∘ e⁻¹)` of `v`. -/
private theorem integral_inner_apply_chartQuantization_eq (hρ : ContinuousOn ρ e.target)
    (hρ0 : ∀ y ∈ e.target, 0 < ρ y)
    (hμ : (μ.restrict e.source).map e =
      (volume.restrict e.target).withDensity fun y ↦ ENNReal.ofReal (ρ y))
    (θ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) {χ : 𝓓(⟨e.target, e.open_target⟩, ℝ)}
    (b : ClassicalSymbol n ℂ ℂ m) (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯)
    {v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {w₂ : 𝓢(CoordinateSpace n, ℂ)}
    (hw₂ : ∀ y, w₂ y = χ y • v (e.symm y)) :
    ∫ p, inner ℂ (u p) (e.chartQuantization he θ χ b v p) ∂μ =
      ∫ y in e.target, inner ℂ (u (e.symm y))
        (((ρ y * θ y : ℝ) : ℂ) * quantizeSchwartzValue b.toSymbol.coefficient w₂ y) := by
  rw [integral_eq_setIntegral_target_smul hμ (hρ.aemeasurable e.open_target.measurableSet)
    (fun y hy ↦ (hρ0 y hy).le)
    (u.contMDiff.continuous.inner
      (e.chartQuantization he θ χ b v).contMDiff.continuous).continuousOn
    fun p hp ↦ by simp [chartQuantization_apply_of_notMem he _ _ _ v hp]]
  refine setIntegral_congr_fun e.open_target.measurableSet fun y hy ↦ ?_
  rw [chartQuantization_apply_of_mem he θ χ b v hw₂ (e.map_target hy), e.right_inv hy]
  simp only [Complex.real_smul, RCLike.inner_apply, Complex.ofReal_mul]
  ring

/-- **The formal adjoint of a chart quantization.** Let `μ` be a measure on `M` that reads in the
chart `e` as `ρ(y) dy`, with `ρ` smooth and positive on the chart target. For cutoffs `φ`, `ψ`
and a classical symbol `a` of order `m`, there is a classical symbol `b` of order `m` such that
`Op_e(b)`, localized by cutoffs `θ` and `χ` equal to `1` on the supports of `ψ` and `φ`, is the
formal adjoint of `Op_e(a)` localized by `φ` and `ψ`:

`∫ ⟪Op_e(a) u, v⟫ dμ = ∫ ⟪u, Op_e(b) v⟫ dμ`

for all smooth `u` and `v`. The principal symbol of `b` is `φ(y) ψ(y) σ(a)(y, ξ)†`. -/
theorem exists_integral_inner_chartQuantization_eq (hρ : ContDiffOn ℝ ∞ ρ e.target)
    (hρ0 : ∀ y ∈ e.target, 0 < ρ y)
    (hμ : (μ.restrict e.source).map e =
      (volume.restrict e.target).withDensity fun y ↦ ENNReal.ofReal (ρ y))
    (φ ψ θ χ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (hθ : EqOn θ 1 (tsupport ψ))
    (hχ : EqOn χ 1 (tsupport φ)) (a : ClassicalSymbol n ℂ ℂ m) :
    ∃ b : ClassicalSymbol n ℂ ℂ m,
      (∀ u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
        ∫ p, inner ℂ (e.chartQuantization he φ ψ a u p) (v p) ∂μ =
          ∫ p, inner ℂ (u p) (e.chartQuantization he θ χ b v p) ∂μ) ∧
      ∀ y ξ, b.principal.coefficient (y, ξ) =
        ((φ y * ψ y : ℝ) : ℂ) • ContinuousLinearMap.adjoint (a.principal.coefficient (y, ξ)) := by
  -- The weight `k = φ ρ` and the factor `q = ψ / ρ`, smooth on `ℝⁿ` and supported in the target.
  set k : CoordinateSpace n → ℂ := fun y ↦ ((φ y * ρ y : ℝ) : ℂ)
  have hk : ContDiff ℝ ∞ k := Complex.ofRealCLM.contDiff.comp
    (hρ.contDiff_smul_of_tsupport_subset e.open_target φ.contDiff.contDiffOn φ.tsupport_subset)
  have hkc : HasCompactSupport k :=
    (φ.hasCompactSupport.mul_right (f' := ρ)).comp_left Complex.ofReal_zero
  set q : CoordinateSpace n → ℂ := fun y ↦ ((ψ y * (ρ y)⁻¹ : ℝ) : ℂ)
  have hq : ContDiff ℝ ∞ q := Complex.ofRealCLM.contDiff.comp
    ((hρ.inv fun y hy ↦ (hρ0 y hy).ne').contDiff_smul_of_tsupport_subset e.open_target
      ψ.contDiff.contDiffOn ψ.tsupport_subset)
  -- `c = k a` has compact spatial support, and `b = q c*`.
  set c := ClassicalSymbol.smulLeft hk a
  have hc : c.toSymbol.HasCompactSpatialSupport :=
    ClassicalSymbol.toSymbol_smulLeft hk a ▸ Symbol.hasCompactSpatialSupport_smulLeft hk hkc _
  refine ⟨ClassicalSymbol.smulLeft hq (c.adjoint hc), fun u v ↦ ?_, fun y ξ ↦ ?_⟩
  · -- Read `u` and `v` in the chart and apply the adjoint identity of `Op(c)` on `ℝⁿ`.
    set w₁ := e.cutoffPushforwardSchwartz he ψ u
    set w₂ := e.cutoffPushforwardSchwartz he χ v
    have hw₁ : ∀ y, w₁ y = ψ y • u (e.symm y) := e.cutoffPushforwardSchwartz_apply he ψ u
    have hw₂ : ∀ y, w₂ y = χ y • v (e.symm y) := e.cutoffPushforwardSchwartz_apply he χ v
    rw [integral_inner_chartQuantization_apply_eq he hρ.continuousOn hρ0 hμ hχ a hw₁ hw₂,
      integral_inner_apply_chartQuantization_eq he hρ.continuousOn hρ0 hμ θ _ u hw₂]
    convert Symbol.integral_inner_quantizeSchwartzValue_adjoint c.toSymbol hc w₁ w₂ using 1
    · -- `⟪Op(a) w₁, k w₂⟫ = ⟪Op(c) w₁, w₂⟫`, since `k` is real.
      refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
      simp only [c, k, ClassicalSymbol.toSymbol_smulLeft, Symbol.quantizeSchwartzValue_smulLeft,
        smul_eq_mul, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
      ring
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := e.target)
      (f := fun y ↦ inner ℂ (w₁ y) (quantizeSchwartzValue (c.toSymbol.adjoint hc).coefficient w₂ y))
      fun y hy ↦ by simp [hw₁, image_eq_zero_of_notMem_tsupport fun h ↦ hy (ψ.tsupport_subset h)]]
    refine setIntegral_congr_fun e.open_target.measurableSet fun y hy ↦ ?_
    rw [ClassicalSymbol.toSymbol_smulLeft, Symbol.quantizeSchwartzValue_smulLeft, hw₁,
      ClassicalSymbol.toSymbol_adjoint]
    -- On the target, `ρ θ q = ψ`.
    by_cases hψy : ψ y = 0
    · simp [q, hψy]
    rw [hθ (subset_tsupport _ hψy)]
    simp only [q, smul_eq_mul, Complex.real_smul, RCLike.inner_apply, map_mul,
      Complex.conj_ofReal, Complex.ofReal_mul, Complex.ofReal_inv, Pi.one_apply,
      Complex.ofReal_one]
    field_simp [(hρ0 y hy).ne']
  · -- `σ(b) = q (k σ(a))† = (ψ / ρ) (φ ρ) σ(a)† = φ ψ σ(a)†`.
    simp only [ClassicalSymbol.coefficient_principal_smulLeft, ClassicalSymbol.principal_adjoint,
      HomogeneousSymbol.coefficient_adjoint, map_smulₛₗ, Complex.conj_ofReal, smul_smul,
      ← Complex.ofReal_mul, c, q, k]
    congr 2
    by_cases hy : y ∈ e.target
    · field_simp [(hρ0 y hy).ne']
    · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hy (φ.tsupport_subset h)]

/-- The pairing `p ↦ ⟪Op_e(a) u (p), v (p)⟫` of a chart quantization with a smooth function is
integrable, for a measure with a continuous chart density. -/
theorem integrable_inner_chartQuantization_apply (hρ : ContinuousOn ρ e.target)
    (hμ : (μ.restrict e.source).map e =
      (volume.restrict e.target).withDensity fun y ↦ ENNReal.ofReal (ρ y))
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (a : ClassicalSymbol n ℂ ℂ m)
    (u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    Integrable (fun p ↦ inner ℂ (e.chartQuantization he φ ψ a u p) (v p)) μ :=
  integrable_of_support_subset_symm_image hμ hρ
    ((e.chartQuantization he φ ψ a u).contMDiff.continuous.inner
      v.contMDiff.continuous).continuousOn φ.hasCompactSupport.isCompact φ.tsupport_subset
    fun p hp ↦ tsupport_chartQuantization_subset he φ ψ a u
      (subset_tsupport _ fun h ↦ hp (by simp [h]))

/-- The pairing `p ↦ ⟪u (p), Op_e(a) v (p)⟫` of a smooth function with a chart quantization is
integrable, for a measure with a continuous chart density. -/
theorem integrable_inner_apply_chartQuantization (hρ : ContinuousOn ρ e.target)
    (hμ : (μ.restrict e.source).map e =
      (volume.restrict e.target).withDensity fun y ↦ ENNReal.ofReal (ρ y))
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (a : ClassicalSymbol n ℂ ℂ m)
    (u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    Integrable (fun p ↦ inner ℂ (u p) (e.chartQuantization he φ ψ a v p)) μ :=
  integrable_of_support_subset_symm_image hμ hρ
    (u.contMDiff.continuous.inner
      (e.chartQuantization he φ ψ a v).contMDiff.continuous).continuousOn
    φ.hasCompactSupport.isCompact φ.tsupport_subset
    fun p hp ↦ tsupport_chartQuantization_subset he φ ψ a v
      (subset_tsupport _ fun h ↦ hp (by simp [h]))

/-- The formal adjoint of `Op_e(a)` given by `exists_integral_inner_chartQuantization_eq`, with
cutoffs equal to `1` on the supports of `ψ` and `φ`, has the conjugate principal symbol. -/
private theorem exists_chartQuantization_integral_inner_eq_and_classicalPrincipalSymbol_eq
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] (hρ : ContDiffOn ℝ ∞ ρ e.target)
    (hρ0 : ∀ y ∈ e.target, 0 < ρ y)
    (hμ : (μ.restrict e.source).map e =
      (volume.restrict e.target).withDensity fun y ↦ ENNReal.ofReal (ρ y))
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (a : ClassicalSymbol n ℂ ℂ m) :
    ∃ (θ χ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (b : ClassicalSymbol n ℂ ℂ m),
      (∀ u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
        ∫ p, inner ℂ (e.chartQuantization he φ ψ a u p) (v p) ∂μ =
          ∫ p, inner ℂ (u p) (e.chartQuantization he θ χ b v p) ∂μ) ∧
      ∀ x ξ, classicalPrincipalSymbol m (e.chartQuantization he θ χ b) x ξ =
        starRingEnd ℂ (classicalPrincipalSymbol m (e.chartQuantization he φ ψ a) x ξ) := by
  obtain ⟨θ, hθ, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤)
    ψ.hasCompactSupport.isCompact ψ.tsupport_subset
  obtain ⟨χ, hχ, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤)
    φ.hasCompactSupport.isCompact φ.tsupport_subset
  have hθ1 : EqOn θ 1 (tsupport ψ) := fun y hy ↦ hθ.self_of_nhdsSet y hy
  have hχ1 : EqOn χ 1 (tsupport φ) := fun y hy ↦ hχ.self_of_nhdsSet y hy
  obtain ⟨b, hadj, hb⟩ :=
    exists_integral_inner_chartQuantization_eq he hρ hρ0 hμ φ ψ θ χ hθ1 hχ1 a
  refine ⟨θ, χ, b, hadj, fun x ξ ↦ ?_⟩
  by_cases hx : x ∈ e.source
  · rw [classicalPrincipalSymbol_chartQuantization he _ _ _ hx,
      classicalPrincipalSymbol_chartQuantization he _ _ _ hx, hb, smul_apply,
      ContinuousLinearMap.adjoint_apply_one]
    -- Where `φ ψ ≠ 0`, the cutoffs `θ` and `χ` are equal to `1`.
    by_cases hφψ : φ (e x) * ψ (e x) = 0
    · simp [hφψ]
    rw [hθ1 (subset_tsupport _ (right_ne_zero_of_mul hφψ)),
      hχ1 (subset_tsupport _ (left_ne_zero_of_mul hφψ))]
    simp
  · rw [classicalPrincipalSymbol_chartQuantization_of_notMem he _ _ _ hx,
      classicalPrincipalSymbol_chartQuantization_of_notMem he _ _ _ hx, map_zero]

/-- **The formal adjoint of a chart quantization is a classical pseudodifferential operator.** If
`μ` reads in the chart `e` as `ρ(y) dy`, with `ρ` smooth and positive on the chart target, the chart
quantization `Op_e(a)` of a classical symbol of order `m` has a formal adjoint `Q` for `μ`,
`∫ ⟪Op_e(a) u, v⟫ dμ = ∫ ⟪u, Q v⟫ dμ` for all smooth `u` and `v`, which is a classical
pseudodifferential operator of order `m` whose principal symbol is the complex conjugate of that of
`Op_e(a)`. -/
theorem exists_mem_classicalPseudodifferentialOperators_integral_inner_chartQuantization_eq
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] (hρ : ContDiffOn ℝ ∞ ρ e.target)
    (hρ0 : ∀ y ∈ e.target, 0 < ρ y)
    (hμ : (μ.restrict e.source).map e =
      (volume.restrict e.target).withDensity fun y ↦ ENNReal.ofReal (ρ y))
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (a : ClassicalSymbol n ℂ ℂ m) :
    ∃ Q ∈ classicalPseudodifferentialOperators m,
      (∀ u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
        ∫ p, inner ℂ (e.chartQuantization he φ ψ a u p) (v p) ∂μ = ∫ p, inner ℂ (u p) (Q v p) ∂μ) ∧
      ∀ x ξ, classicalPrincipalSymbol m Q x ξ =
        starRingEnd ℂ (classicalPrincipalSymbol m (e.chartQuantization he φ ψ a) x ξ) :=
  let ⟨θ, χ, b, hadj, hb⟩ :=
    exists_chartQuantization_integral_inner_eq_and_classicalPrincipalSymbol_eq he hρ hρ0 hμ φ ψ a
  ⟨_, chartQuantization_mem_classicalPseudodifferentialOperators he θ χ b, hadj, hb⟩

end Adjoint

end OpenPartialHomeomorph

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  {μ : Measure M} {m : ℝ}

/-- **Formal adjoints of patched quantizations.** Let `∑ᵢ Op_{eᵢ}(aᵢ)` be a finite sum of chart
quantizations of classical symbols of order `m`, and let `μ` read in each chart `eᵢ` as
`ρᵢ(y) dy`, with `ρᵢ` smooth and positive on the chart target. Then the sum has a formal adjoint
`Q` for `μ`, `∫ ⟪(∑ᵢ Op_{eᵢ}(aᵢ)) u, v⟫ dμ = ∫ ⟪u, Q v⟫ dμ` for all smooth `u` and `v`, which is a
classical pseudodifferential operator of order `m` whose principal symbol is the complex conjugate
of that of the sum. -/
theorem exists_mem_classicalPseudodifferentialOperators_integral_inner_sum_chartQuantization_eq
    {ι : Type*} (s : Finset ι) {e : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    {ρ : ι → CoordinateSpace n → ℝ} (hρ : ∀ i ∈ s, ContDiffOn ℝ ∞ (ρ i) (e i).target)
    (hρ0 : ∀ i ∈ s, ∀ y ∈ (e i).target, 0 < ρ i y)
    (hμ : ∀ i ∈ s, (μ.restrict (e i).source).map (e i) =
      (volume.restrict (e i).target).withDensity fun y ↦ ENNReal.ofReal (ρ i y))
    (φ ψ : ∀ i, 𝓓(⟨(e i).target, (e i).open_target⟩, ℝ)) (a : ι → ClassicalSymbol n ℂ ℂ m) :
    ∃ Q ∈ classicalPseudodifferentialOperators m,
      (∀ u v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
        ∫ p, inner ℂ ((∑ i ∈ s, (e i).chartQuantization (he i) (φ i) (ψ i) (a i)) u p) (v p) ∂μ =
          ∫ p, inner ℂ (u p) (Q v p) ∂μ) ∧
      ∀ x ξ, classicalPrincipalSymbol m Q x ξ = starRingEnd ℂ (classicalPrincipalSymbol m
        (∑ i ∈ s, (e i).chartQuantization (he i) (φ i) (ψ i) (a i)) x ξ) := by
  choose! θ χ b hadj hb using fun i (hi : i ∈ s) ↦
    (e i).exists_chartQuantization_integral_inner_eq_and_classicalPrincipalSymbol_eq (he i)
      (hρ i hi) (hρ0 i hi) (hμ i hi) (φ i) (ψ i) (a i)
  refine ⟨∑ i ∈ s, (e i).chartQuantization (he i) (θ i) (χ i) (b i),
    Submodule.sum_mem _ fun i _ ↦ (e i).chartQuantization_mem_classicalPseudodifferentialOperators
      (he i) _ _ _, fun u v ↦ ?_, fun x ξ ↦ ?_⟩
  · simp only [LinearMap.sum_apply, ContMDiffMap.coe_sum, Finset.sum_apply, sum_inner,
      inner_sum]
    rw [integral_finsetSum _ fun i hi ↦ (e i).integrable_inner_chartQuantization_apply (he i)
        (hρ i hi).continuousOn (hμ i hi) _ _ _ u v,
      integral_finsetSum _ fun i hi ↦ (e i).integrable_inner_apply_chartQuantization (he i)
        (hρ i hi).continuousOn (hμ i hi) _ _ _ u v]
    exact Finset.sum_congr rfl fun i hi ↦ hadj i hi u v
  · rw [classicalPrincipalSymbol_sum s (fun i _ ↦
        (e i).chartQuantization_mem_classicalPseudodifferentialOperators (he i) _ _ _),
      classicalPrincipalSymbol_sum s (fun i _ ↦
        (e i).chartQuantization_mem_classicalPseudodifferentialOperators (he i) _ _ _), map_sum]
    exact Finset.sum_congr rfl fun i hi ↦ hb i hi x ξ

end TauCeti
