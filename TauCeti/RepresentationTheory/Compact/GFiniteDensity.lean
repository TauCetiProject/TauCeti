/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.RepresentativeDensity
public import TauCeti.RepresentationTheory.GFinite

/-!
# Density of the `G`-finite vectors in a Banach representation of a compact group

Let `π` be a representation of a compact group `G` on a Banach space `E` over `ℝ` or `ℂ` that is
**strongly continuous**: every orbit `g ↦ π g v` is continuous. This file proves that the
`G`-finite vectors, those whose orbit spans a finite-dimensional subspace, are dense in `E`
(`ContRepresentation.dense_gFiniteSubmodule`). No continuity of `g ↦ π g` in the operator norm is
assumed, and none would be available in the examples that matter, such as the regular
representations on `Lᵖ(G)`.

The proof smooths a vector against continuous functions on `G`. For `a ∈ C(G, 𝕜)` and `v ∈ E` put

`T_a v = ∫ g, a g • π g⁻¹ v`,

the integral against normalized Haar measure. Right invariance of Haar measure gives
`π h (T_a v) = T_{a(· h)} v`, so the orbit of `T_a v` lies in the image of the span of the right
translates of `a`. When `a` is a representative function, a matrix coefficient of a
finite-dimensional continuous representation or a combination of such, that span is
finite-dimensional (`TauCeti.finiteDimensional_span_range_comp_mulRight`), so `T_a v` is
`G`-finite.

It remains to approximate `v` by such vectors.

* If `u` is a mollifying kernel supported where `‖π g⁻¹ v - v‖ ≤ δ`, then `‖T_u v - v‖ ≤ δ`, since
  `u` is a probability density. Such kernels exist because the orbit of `v` is continuous at `1`
  (`TauCeti.exists_isMollifier`).
* The orbit of `v` is bounded by some `M` on the compact group, so `‖T_a v - T_b v‖ ≤ M ‖a - b‖`
  in the uniform norm; and representative functions are uniformly dense in `C(G, 𝕜)`
  (`TauCeti.dense_representativeSubmodule`), the analytic core of the Peter-Weyl theorem.

Only the boundedness of each single orbit is used, never a uniform bound on the operators `π g`.

## Main statements

* `ContRepresentation.dense_gFiniteSubmodule`: the `G`-finite vectors of a strongly continuous
  representation of a compact group on a Banach space are dense.
* `ContRepresentation.continuousLinearMap_ext_of_isGFinite`: so two continuous linear maps out of
  such a representation that agree on the `G`-finite vectors are equal.

## References

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC (2016), Theorem 5.11.
* N. R. Wallach, *Real Reductive Groups I*, Academic Press (1988), Lemma 1.4.4.
-/

public section

open MeasureTheory Filter Topology TauCeti

namespace ContRepresentation

variable {𝕜 G E : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

section Smoothing

variable [MeasurableSpace G] [BorelSpace G] [NormedSpace ℝ E] [SMulCommClass ℝ 𝕜 E]
  (π : ContRepresentation 𝕜 G E) (hπ : ∀ v, Continuous fun g => π g v)

/-- The continuous map `g ↦ a g • π g⁻¹ v` whose Haar average smooths `v` against `a`. -/
private noncomputable def weightedOrbit (a : C(G, 𝕜)) (v : E) : C(G, E) :=
  ⟨fun g => a g • π g⁻¹ v, a.continuous.smul ((hπ v).comp continuous_inv)⟩

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [NormedSpace ℝ E] [SMulCommClass ℝ 𝕜 E] in
private theorem weightedOrbit_apply (a : C(G, 𝕜)) (v : E) (g : G) :
    weightedOrbit π hπ a v g = a g • π g⁻¹ v :=
  (rfl)

/-- Smoothing a vector against continuous functions: `a ↦ ∫ g, a g • π g⁻¹ v`. -/
private noncomputable def smoothing (v : E) : C(G, 𝕜) →ₗ[𝕜] E where
  toFun a := haarAverage G (𝕜 := 𝕜) (weightedOrbit π hπ a v)
  map_add' a b := by
    rw [← map_add]
    congr 1
    ext g
    simp only [weightedOrbit_apply, ContinuousMap.add_apply, add_smul]
  map_smul' c a := by
    rw [RingHom.id_apply, ← map_smul]
    congr 1
    ext g
    simp only [weightedOrbit_apply, ContinuousMap.smul_apply, smul_eq_mul, mul_smul]

private theorem smoothing_eq_haarAverage (v : E) (a : C(G, 𝕜)) :
    smoothing π hπ v a = haarAverage G (𝕜 := 𝕜) (weightedOrbit π hπ a v) :=
  (rfl)

private theorem smoothing_apply (v : E) (a : C(G, 𝕜)) :
    smoothing π hπ v a = ∫ g, a g • π g⁻¹ v ∂haarProb G :=
  haarAverage_apply G _

/-- Translating a smoothed vector translates the smoothing function on the right. -/
private theorem apply_smoothing [CompleteSpace E] (v : E) (a : C(G, 𝕜)) (h : G) :
    π h (smoothing π hπ v a) = smoothing π hπ v (a.comp (ContinuousMap.mulRight h)) := by
  rw [smoothing_eq_haarAverage, smoothing_eq_haarAverage,
    ← ContinuousLinearMap.haarAverage_comp_comm]
  conv_rhs => rw [← haarAverage_comp_mulRight G _ h⁻¹]
  congr 1
  ext g
  simp [weightedOrbit_apply, map_mul]

/-- Smoothing against a representative function produces a `G`-finite vector. -/
private theorem isGFinite_smoothing [CompleteSpace E] (v : E) {a : C(G, 𝕜)}
    (ha : a ∈ representativeSubmodule 𝕜 G) :
    π.toRepresentation.IsGFinite (smoothing π hπ v a) := by
  have := finiteDimensional_span_range_comp_mulRight ha
  exact Representation.IsGFinite.of_apply_eq (smoothing π hπ v) (apply_smoothing π hπ v a)

/-- The orbit map `g ↦ π g⁻¹ v`, as a continuous map; its uniform norm bounds the orbit. -/
private noncomputable def invOrbit (v : E) : C(G, E) :=
  ⟨fun g => π g⁻¹ v, (hπ v).comp continuous_inv⟩

/-- Smoothing is bounded in the uniform norm of the smoothing function, with the bound of the
orbit as constant. -/
private theorem norm_smoothing_le (v : E) (a : C(G, 𝕜)) :
    ‖smoothing π hπ v a‖ ≤ ‖a‖ * ‖invOrbit π hπ v‖ := by
  refine (norm_haarAverage_apply_le G _).trans (ContinuousMap.norm_le _ (by positivity) |>.2
    fun g => ?_)
  rw [weightedOrbit_apply, norm_smul]
  exact mul_le_mul (a.norm_coe_le_norm g) ((invOrbit π hπ v).norm_coe_le_norm g)
    (norm_nonneg _) (norm_nonneg _)

/-- Smoothing against a mollifying kernel supported where the orbit stays `δ`-close to `v` moves
`v` by at most `δ`. -/
private theorem norm_smoothing_sub_le [CompleteSpace E] (v : E) {U : Set G} {u : C(G, 𝕜)}
    (hu : IsMollifier U u) {δ : ℝ} (hU : ∀ g ∈ U, ‖π g⁻¹ v - v‖ ≤ δ) :
    ‖smoothing π hπ v u - v‖ ≤ δ := by
  have hint : Integrable (fun g => u g • π g⁻¹ v) (haarProb G) :=
    integrable_continuousMap G (weightedOrbit π hπ u v)
  have hint' : Integrable (fun g => u g • v) (haarProb G) :=
    integrable_continuousMap G ⟨fun g => u g • v, u.continuous.smul continuous_const⟩
  have hv : ∫ g, u g • v ∂haarProb G = v := by
    rw [integral_smul_const, hu.integral_eq_one, one_smul]
  have hbound : ∀ g, ‖u g • (π g⁻¹ v - v)‖ ≤ ‖u g‖ * δ := by
    intro g
    rw [norm_smul]
    by_cases hg : g ∈ U
    · exact mul_le_mul_of_nonneg_left (hU g hg) (norm_nonneg _)
    · simp [hu.eq_zero_of_notMem g hg]
  have hsub : smoothing π hπ v u - v = ∫ g, u g • (π g⁻¹ v - v) ∂haarProb G := by
    simp_rw [smoothing_apply, smul_sub]
    rw [integral_sub hint hint', hv]
  calc ‖smoothing π hπ v u - v‖
      = ‖∫ g, u g • (π g⁻¹ v - v) ∂haarProb G‖ := by rw [hsub]
    _ ≤ ∫ g, ‖u g‖ * δ ∂haarProb G :=
        norm_integral_le_of_norm_le
          (integrable_continuousMap G ⟨fun g => ‖u g‖ * δ, by fun_prop⟩)
          (Eventually.of_forall hbound)
    _ = δ := by rw [integral_mul_const, hu.integral_norm_eq_one, one_mul]

end Smoothing

/-- **The `G`-finite vectors are dense.** For a strongly continuous representation `π` of a compact
group on a Banach space, the vectors whose orbit spans a finite-dimensional subspace are dense.

Strong continuity means continuity of each orbit `g ↦ π g v`; continuity of `g ↦ π g` in the
operator norm is not assumed. -/
theorem dense_gFiniteSubmodule [CompleteSpace E] (π : ContRepresentation 𝕜 G E)
    (hπ : ∀ v, Continuous fun g => π g v) :
    Dense (π.toRepresentation.gFiniteSubmodule : Set E) := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have _ : IsScalarTower ℝ 𝕜 E := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  refine Metric.dense_iff.2 fun v ε hε => ?_
  -- A mollifying kernel supported where the orbit of `v` stays `ε / 2`-close to `v`.
  have hU : {g : G | ‖π g⁻¹ v - v‖ < ε / 2} ∈ 𝓝 (1 : G) :=
    (isOpen_lt (((hπ v).comp continuous_inv).sub continuous_const).norm continuous_const).mem_nhds
      (by simpa using half_pos hε)
  obtain ⟨u, hu⟩ := exists_isMollifier 𝕜 hU
  have hu_close := norm_smoothing_sub_le π hπ v hu fun g hg => le_of_lt hg
  -- A representative function uniformly close to the kernel.
  set M := ‖invOrbit π hπ v‖
  have hM : 0 < M + 1 := by positivity
  obtain ⟨a, ha, hau⟩ := Metric.mem_closure_iff.1 (dense_representativeSubmodule 𝕜 G u)
    (ε / 2 / (M + 1)) (by positivity)
  refine ⟨smoothing π hπ v a, ?_,
    (Representation.mem_gFiniteSubmodule _).2 (isGFinite_smoothing π hπ v ha)⟩
  rw [Metric.mem_ball, dist_eq_norm]
  have hdiff : ‖smoothing π hπ v a - smoothing π hπ v u‖ < ε / 2 := by
    rw [← map_sub]
    calc ‖smoothing π hπ v (a - u)‖
        ≤ ‖a - u‖ * M := norm_smoothing_le π hπ v (a - u)
      _ ≤ ‖a - u‖ * (M + 1) := by gcongr; linarith
      _ < ε / 2 / (M + 1) * (M + 1) := by
          gcongr
          rwa [← dist_eq_norm, dist_comm]
      _ = ε / 2 := div_mul_cancel₀ _ hM.ne'
  calc ‖smoothing π hπ v a - v‖
      ≤ ‖smoothing π hπ v a - smoothing π hπ v u‖ + ‖smoothing π hπ v u - v‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le hdiff hu_close
    _ = ε := add_halves ε

/-- Two continuous linear maps out of a strongly continuous Banach representation of a compact
group that agree on the `G`-finite vectors are equal, since those vectors are dense. -/
theorem continuousLinearMap_ext_of_isGFinite [CompleteSpace E] (π : ContRepresentation 𝕜 G E)
    (hπ : ∀ v, Continuous fun g => π g v) {F : Type*} [TopologicalSpace F] [T2Space F]
    [AddCommMonoid F] [Module 𝕜 F] {T T' : E →L[𝕜] F}
    (h : ∀ v, π.toRepresentation.IsGFinite v → T v = T' v) : T = T' :=
  ContinuousLinearMap.coeFn_injective <| T.continuous.ext_on (dense_gFiniteSubmodule π hπ)
    T'.continuous fun v hv => h v ((Representation.mem_gFiniteSubmodule _).1 hv)

end ContRepresentation
