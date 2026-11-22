/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import TauCeti.Topology.Grassmannian.StarProjection
import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.Analysis.InnerProductSpace.Trace.OpNorm

/-!
# The first variation of a varifold on an open subset of a Euclidean space

Let `E` be a finite-dimensional real inner product space, `W ⊆ E` open and `k : ℕ`. A `k`-varifold
on `W` is a Radon measure `V` on `W × G(E, k)`, where `G(E, k)` is the Grassmannian
`Euclidean.grassmannian E k` of orthogonal projections onto the `k`-planes of `E`; in Lean, a
`Measure (W × grassmannian E k)` with `IsFiniteMeasureOnCompacts`.

For a vector field `X : E → E` and a plane recorded by its orthogonal projection `P`, the
**tangential divergence** of `X` at `x` along `P` is `div_P X (x) = tr (P ∘ DX(x))`
(`Euclidean.tangentialDivergence`). The **first variation** of `V` is the linear functional

`δV(X) = ∫ div_P X (x) dV(x, P)`

on the `C¹` vector fields `X` with compact support in `W` (`Euclidean.firstVariation`), bundled as
a continuous linear map on the test functions `𝓓^{1}(W, E)`. Classically `δV(X)` is the derivative
at `t = 0` of the mass of `V` moved by the flow of `X`, and the stationary varifolds, those with
`δV = 0`, generalise minimal submanifolds. This file defines the functional and proves its basic
properties; the characterisation through flows is not proved here.

The integrand `(x, P) ↦ div_P X (x)` is continuous with compact support in `W × G(E, k)`, so
`δV(X)` is finite. It satisfies `|div_P X (x)| ≤ k ‖DX(x)‖` for `P ∈ G(E, k)`, which gives the bound
`|δV(X)| ≤ k V(π⁻¹ K) sup ‖DX‖` for `X` supported in a compact `K ⊆ W`; the order-one bound makes
`δV` continuous on `𝓓^{1}(W, E)`. The first variation is additive and positively homogeneous in
`V`, and it passes to limits under varifold convergence (convergence against every compactly
supported continuous function on `W × G(E, k)`). In the degenerate dimensions, `δV = 0` for
`k = 0`, and for `k = dim E` the only plane is `E` itself, so that `δV(X) = ∫ tr (DX(x)) dV`.

## Main definitions

* `Euclidean.tangentialDivergence X x P`: the tangential divergence `tr (P ∘ DX(x))`.
* `Euclidean.firstVariation V`: the first variation `δV : 𝓓^{1}(W, E) →L[ℝ] ℝ` of a varifold `V`
  on `W`. It is `0` by convention when `V` is not finite on compact sets.

## Main results

* `Euclidean.abs_tangentialDivergence_le`: `|div_P X (x)| ≤ k ‖DX(x)‖` for `P ∈ G(E, k)`.
* `Euclidean.firstVariation_apply`: `δV(X) = ∫ div_P X (x) dV(x, P)`.
* `Euclidean.abs_firstVariation_le`: `|δV(X)| ≤ k V(π⁻¹ K) sup ‖DX‖` for `X` supported in a
  compact `K ⊆ W`.
* `Euclidean.firstVariation_add_measure`, `Euclidean.firstVariation_smul_measure`: additivity and
  positive homogeneity in `V`.
* `Euclidean.tendsto_firstVariation`: varifold convergence `V_i → V` implies `δV_i(X) → δV(X)`.
* `Euclidean.firstVariation_zero_dim`, `Euclidean.firstVariation_apply_finrank`: the cases
  `k = 0` and `k = dim E`.

## References

* W. K. Allard, *On the first variation of a varifold*, Ann. of Math. 95 (1972), Section 4.
* L. Simon, *Lectures on Geometric Measure Theory*, §39.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Filter Module
open scoped Distributions Topology NNReal CompactlySupported

namespace Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {k : ℕ}

/-! ### The tangential divergence -/

/-- The **tangential divergence** `div_P X (x) = tr (P ∘ DX(x))` of a vector field `X : E → E` at
`x` along a continuous endomorphism `P` of `E`. When `P` is the orthogonal projection onto a
`k`-plane `S`, a point of `G(E, k)`, this is the divergence of `X` along `S` (Simon, *Lectures on
Geometric Measure Theory*, §39). -/
def tangentialDivergence (X : E → E) (x : E) (P : E →L[ℝ] E) : ℝ :=
  LinearMap.trace ℝ E ((P ∘L fderiv ℝ X x : E →L[ℝ] E) : E →ₗ[ℝ] E)

/-- The tangential divergence unfolds to the trace of `P ∘ DX(x)`. -/
theorem tangentialDivergence_def (X : E → E) (x : E) (P : E →L[ℝ] E) :
    tangentialDivergence X x P =
      LinearMap.trace ℝ E ((P ∘L fderiv ℝ X x : E →L[ℝ] E) : E →ₗ[ℝ] E) :=
  (rfl)

/-- The tangential divergence is additive in the vector field, at a point where both fields are
differentiable. -/
theorem tangentialDivergence_add {X Y : E → E} {x : E} (hX : DifferentiableAt ℝ X x)
    (hY : DifferentiableAt ℝ Y x) (P : E →L[ℝ] E) :
    tangentialDivergence (X + Y) x P = tangentialDivergence X x P + tangentialDivergence Y x P := by
  simp [tangentialDivergence_def, fderiv_add hX hY]

/-- The tangential divergence is homogeneous in the vector field. -/
@[simp]
theorem tangentialDivergence_const_smul (c : ℝ) (X : E → E) (x : E) (P : E →L[ℝ] E) :
    tangentialDivergence (c • X) x P = c * tangentialDivergence X x P := by
  simp [tangentialDivergence_def, fderiv_const_smul_field]

/-- The tangential divergence vanishes outside the closed support of the vector field. -/
theorem tangentialDivergence_eq_zero_of_notMem_tsupport {X : E → E} {x : E} (hx : x ∉ tsupport X)
    (P : E →L[ℝ] E) : tangentialDivergence X x P = 0 := by
  rw [tangentialDivergence_def,
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (tsupport_fderiv_subset ℝ h)]
  simp

variable [FiniteDimensional ℝ E]

/-- For a `C¹` vector field, the tangential divergence is jointly continuous in the point and the
endomorphism. -/
theorem continuous_tangentialDivergence {X : E → E} (hX : ContDiff ℝ 1 X) :
    Continuous fun q : E × (E →L[ℝ] E) ↦ tangentialDivergence X q.1 q.2 := by
  simp_rw [tangentialDivergence_def, ← TauCeti.traceCLM_apply]
  exact (TauCeti.traceCLM ℝ E).continuous.comp
    (continuous_snd.clm_comp ((hX.continuous_fderiv one_ne_zero).comp continuous_fst))

/-- Along a plane of `G(E, k)`, the tangential divergence is bounded by `k` times the operator norm
of the derivative: `|div_P X (x)| ≤ k ‖DX(x)‖`. -/
theorem abs_tangentialDivergence_le {P : E →L[ℝ] E} (hP : P ∈ grassmannian E k) (X : E → E)
    (x : E) : |tangentialDivergence X x P| ≤ k * ‖fderiv ℝ X x‖ := by
  rw [tangentialDivergence_def, ← TauCeti.traceCLM_apply, ← Real.norm_eq_abs]
  refine (P ∘L fderiv ℝ X x).norm_traceCLM_le_finrank_range_mul.trans
    (mul_le_mul ?_ ?_ (norm_nonneg _) (Nat.cast_nonneg _))
  · rw [← grassmannian.finrank_range hP]
    exact_mod_cast Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
  · exact (P.opNorm_comp_le _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (grassmannian.norm_le_one hP))

/-- Along the zero plane, the only point of `G(E, 0)`, the tangential divergence vanishes. -/
theorem tangentialDivergence_eq_zero_of_mem_grassmannian_zero {P : E →L[ℝ] E}
    (hP : P ∈ grassmannian E 0) (X : E → E) (x : E) : tangentialDivergence X x P = 0 := by
  simpa using abs_tangentialDivergence_le hP X x

/-- Along the whole space, the only point of `G(E, dim E)`, the tangential divergence is the
divergence `tr (DX(x))`. -/
theorem tangentialDivergence_of_mem_grassmannian_finrank {P : E →L[ℝ] E}
    (hP : P ∈ grassmannian E (finrank ℝ E)) (X : E → E) (x : E) :
    tangentialDivergence X x P = LinearMap.trace ℝ E (fderiv ℝ X x : E →ₗ[ℝ] E) := by
  -- A star projection whose range is all of `E` is the identity.
  have htop : P.range = ⊤ := Submodule.eq_top_of_finrank_eq (grassmannian.finrank_range hP)
  have hP1 : P = 1 := by
    ext v
    obtain ⟨w, rfl⟩ := LinearMap.range_eq_top.1 htop v
    simpa using DFunLike.congr_fun (grassmannian.isStarProjection hP).isIdempotentElem.eq w
  simp [tangentialDivergence_def, hP1, Module.End.one_eq_id]

/-! ### The first variation -/

section FirstVariation

variable [MeasurableSpace E] [BorelSpace E] {W : Opens E} {V V₁ V₂ : Measure (W × grassmannian E k)}

omit [MeasurableSpace E] [BorelSpace E] in
/-- The pairs whose base point lies in a compact `K ⊆ W` form a compact subset of
`W × G(E, k)`. -/
private theorem isCompact_setOf_coe_fst_mem {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W) :
    IsCompact {p : W × grassmannian E k | (p.1 : E) ∈ K} := by
  have hK' : IsCompact ((↑) ⁻¹' K : Set W) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hK (by simpa using hKW)
  have h := hK'.prod (isCompact_univ (X := grassmannian E k))
  rw [prod_univ] at h
  exact h

omit [MeasurableSpace E] [BorelSpace E] in
/-- For a vector field with compact support in `W`, the tangential divergence has compact support
as a function on `W × G(E, k)`. -/
theorem hasCompactSupport_tangentialDivergence {X : E → E} (hX : HasCompactSupport X)
    (hXW : tsupport X ⊆ W) :
    HasCompactSupport fun p : W × grassmannian E k ↦ tangentialDivergence X p.1 p.2 :=
  HasCompactSupport.intro (isCompact_setOf_coe_fst_mem hX hXW) fun _ hp ↦
    tangentialDivergence_eq_zero_of_notMem_tsupport hp _

/-- The tangential divergence of a `C¹` test vector field, as a compactly supported continuous
function on `W × G(E, k)`. -/
private def tangentialDivergenceCc (X : 𝓓^{1}(W, E)) : C_c(W × grassmannian E k, ℝ) where
  toFun p := tangentialDivergence X p.1 p.2
  continuous_toFun := (continuous_tangentialDivergence X.contDiff).comp
    ((continuous_subtypeVal.comp continuous_fst).prodMk
      (continuous_subtypeVal.comp continuous_snd))
  hasCompactSupport' := hasCompactSupport_tangentialDivergence X.hasCompactSupport X.tsupport_subset

/-- The integrand of the first variation of a `C¹` test vector field is integrable. -/
theorem integrable_tangentialDivergence [IsFiniteMeasureOnCompacts V] (X : 𝓓^{1}(W, E)) :
    Integrable (fun p : W × grassmannian E k ↦ tangentialDivergence X p.1 p.2) V :=
  (tangentialDivergenceCc X).continuous.integrable_of_hasCompactSupport
    (tangentialDivergenceCc X).hasCompactSupport

omit [BorelSpace E] in
/-- The order-one bound on the integral of the tangential divergence. -/
private theorem abs_integral_tangentialDivergence_le [IsFiniteMeasureOnCompacts V] {X : E → E}
    {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W) (hXK : tsupport X ⊆ K) {c : ℝ}
    (hc : ∀ x, ‖fderiv ℝ X x‖ ≤ c) :
    |∫ p, tangentialDivergence X p.1 p.2 ∂V| ≤ k * V.real {p | (p.1 : E) ∈ K} * c := by
  set S := {p : W × grassmannian E k | (p.1 : E) ∈ K}
  have hS : ∫ p in S, tangentialDivergence X p.1 p.2 ∂V = ∫ p, tangentialDivergence X p.1 p.2 ∂V :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp ↦
      tangentialDivergence_eq_zero_of_notMem_tsupport (fun h ↦ hp (hXK h)) _
  rw [← hS, ← Real.norm_eq_abs]
  refine (norm_setIntegral_le_of_norm_le_const (C := k * c)
    (isCompact_setOf_coe_fst_mem hK hKW).measure_lt_top fun p _ ↦ ?_).trans_eq (by ring)
  exact (abs_tangentialDivergence_le p.2.property _ _).trans
    (mul_le_mul_of_nonneg_left (hc _) (Nat.cast_nonneg _))

/-- The first variation of a varifold that is finite on compact sets, as a linear map. -/
private def firstVariationLinearMap (V : Measure (W × grassmannian E k))
    [IsFiniteMeasureOnCompacts V] : 𝓓^{1}(W, E) →ₗ[ℝ] ℝ where
  toFun X := ∫ p, tangentialDivergence X p.1 p.2 ∂V
  map_add' X Y := by
    rw [← integral_add (integrable_tangentialDivergence X) (integrable_tangentialDivergence Y)]
    refine integral_congr_ae (Eventually.of_forall fun p ↦ ?_)
    exact tangentialDivergence_add (X.contDiff.differentiable one_ne_zero _)
      (Y.contDiff.differentiable one_ne_zero _) _
  map_smul' c X := by
    simp [← integral_const_mul]

/-- The first variation is continuous on `𝓓^{1}(W, E)`: on the tests supported in a compact `K`
it is bounded by the seminorm `sup ‖DX‖`. -/
private theorem continuous_firstVariationLinearMap (V : Measure (W × grassmannian E k))
    [IsFiniteMeasureOnCompacts V] : Continuous (firstVariationLinearMap V) := by
  refine (TestFunction.continuous_iff_continuous_comp _).2 fun K hK ↦ ?_
  let L := firstVariationLinearMap V ∘ₗ (TestFunction.ofSupportedInCLM ℝ hK).toLinearMap
  set C := k * V.real {p : W × grassmannian E k | (p.1 : E) ∈ K}
  have hL (ψ : 𝓓^{1}_{K}(E, E)) :
      ‖L ψ‖ ≤ C * (({1} : Finset ℕ).sup fun i ↦ N[ℝ]_{K, 1, i}) ψ := by
    rw [Finset.sup_singleton, Real.norm_eq_abs]
    refine abs_integral_tangentialDivergence_le K.isCompact hK ψ.tsupport_subset fun x ↦ ?_
    rw [← norm_iteratedFDeriv_one]
    exact ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm ℝ le_rfl
  exact (ContDiffMapSupportedIn.withSeminorms ℝ E E 1 K).continuous_normedSpace_rng ℝ L
    ⟨{1}, ⟨C, by positivity⟩, hL⟩

open scoped Classical in
/-- The **first variation** `δV(X) = ∫ div_P X (x) dV(x, P)` of a varifold `V` on an open set `W`
of a Euclidean space, as a continuous linear functional on the `C¹` vector fields with compact
support in `W` (Allard, *On the first variation of a varifold*, Section 4; Simon, *Lectures on
Geometric Measure Theory*, §39). It is `0` by convention when `V` is not finite on compact sets. -/
def firstVariation (V : Measure (W × grassmannian E k)) : 𝓓^{1}(W, E) →L[ℝ] ℝ :=
  if _ : IsFiniteMeasureOnCompacts V then
    ⟨firstVariationLinearMap V, continuous_firstVariationLinearMap V⟩
  else 0

/-- The first variation integrates the tangential divergence against the varifold. -/
theorem firstVariation_apply [IsFiniteMeasureOnCompacts V] (X : 𝓓^{1}(W, E)) :
    firstVariation V X = ∫ p, tangentialDivergence X p.1 p.2 ∂V := by
  rw [firstVariation, dite_eq_left ‹_›]
  rfl

/-- A measure that is not finite on compact sets has first variation `0` by convention. -/
theorem firstVariation_of_not_isFiniteMeasureOnCompacts (hV : ¬IsFiniteMeasureOnCompacts V) :
    firstVariation V = 0 :=
  dite_eq_right hV

/-- **The first variation is a distribution of order one.** If `X` is supported in a compact
`K ⊆ W` and `‖DX‖ ≤ c`, then `|δV(X)| ≤ k V(π⁻¹ K) c`. -/
theorem abs_firstVariation_le [IsFiniteMeasureOnCompacts V] (X : 𝓓^{1}(W, E)) {K : Set E}
    (hK : IsCompact K) (hKW : K ⊆ W) (hXK : tsupport X ⊆ K) {c : ℝ}
    (hc : ∀ x, ‖fderiv ℝ X x‖ ≤ c) :
    |firstVariation V X| ≤ k * V.real {p | (p.1 : E) ∈ K} * c := by
  rw [firstVariation_apply]
  exact abs_integral_tangentialDivergence_le hK hKW hXK hc

/-- The first variation is additive in the varifold. -/
theorem firstVariation_add_measure [IsFiniteMeasureOnCompacts V₁] [IsFiniteMeasureOnCompacts V₂] :
    firstVariation (V₁ + V₂) = firstVariation V₁ + firstVariation V₂ := by
  have : IsFiniteMeasureOnCompacts (V₁ + V₂) :=
    ⟨fun _ hK ↦ by simp [hK.measure_lt_top]⟩
  ext X
  simp only [add_apply, firstVariation_apply]
  exact integral_add_measure (integrable_tangentialDivergence X) (integrable_tangentialDivergence X)

/-- The first variation is positively homogeneous in the varifold. -/
theorem firstVariation_smul_measure (c : ℝ≥0) (V : Measure (W × grassmannian E k)) :
    firstVariation (c • V) = (c : ℝ) • firstVariation V := by
  by_cases hV : IsFiniteMeasureOnCompacts V
  · ext X
    simp [firstVariation_apply, integral_smul_nnreal_measure, NNReal.smul_def]
  · obtain rfl | hc := eq_or_ne c 0
    · ext X
      simp [firstVariation_apply]
    refine (firstVariation_of_not_isFiniteMeasureOnCompacts fun h ↦ hV ?_).trans
      (by rw [firstVariation_of_not_isFiniteMeasureOnCompacts hV, smul_zero])
    have := IsFiniteMeasureOnCompacts.smul_nnreal (c • V) c⁻¹
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

/-- The zero varifold has first variation `0`. -/
@[simp]
theorem firstVariation_zero_measure : firstVariation (0 : Measure (W × grassmannian E k)) = 0 := by
  simpa using firstVariation_smul_measure 0 (0 : Measure (W × grassmannian E k))

/-- A varifold of `0`-planes has first variation `0`. -/
@[simp]
theorem firstVariation_zero_dim (V : Measure (W × grassmannian E 0)) : firstVariation V = 0 := by
  by_cases hV : IsFiniteMeasureOnCompacts V
  · ext X
    simp [firstVariation_apply, tangentialDivergence_eq_zero_of_mem_grassmannian_zero _]
  · exact firstVariation_of_not_isFiniteMeasureOnCompacts hV

/-- For a varifold of `(dim E)`-planes, every plane is `E` itself and the first variation
integrates the divergence: `δV(X) = ∫ tr (DX(x)) dV(x, P)`. -/
theorem firstVariation_apply_finrank (V : Measure (W × grassmannian E (finrank ℝ E)))
    [IsFiniteMeasureOnCompacts V] (X : 𝓓^{1}(W, E)) :
    firstVariation V X = ∫ p, LinearMap.trace ℝ E (fderiv ℝ X p.1 : E →ₗ[ℝ] E) ∂V := by
  rw [firstVariation_apply]
  exact integral_congr_ae (Eventually.of_forall fun p ↦
    tangentialDivergence_of_mem_grassmannian_finrank p.2.property _ _)

/-- **Continuity of the first variation under varifold convergence.** If `∫ f dV_i → ∫ f dV` for
every compactly supported continuous function `f` on `W × G(E, k)`, then `δV_i(X) → δV(X)` for every
`C¹` vector field `X` with compact support in `W`. -/
theorem tendsto_firstVariation {ι : Type*} {l : Filter ι} {V : ι → Measure (W × grassmannian E k)}
    {V₀ : Measure (W × grassmannian E k)} [∀ i, IsFiniteMeasureOnCompacts (V i)]
    [IsFiniteMeasureOnCompacts V₀]
    (h : ∀ f : C_c(W × grassmannian E k, ℝ),
      Tendsto (fun i ↦ ∫ p, f p ∂V i) l (𝓝 (∫ p, f p ∂V₀)))
    (X : 𝓓^{1}(W, E)) : Tendsto (fun i ↦ firstVariation (V i) X) l (𝓝 (firstVariation V₀ X)) := by
  simp_rw [firstVariation_apply]
  exact h (tangentialDivergenceCc X)

end FirstVariation

end Euclidean
