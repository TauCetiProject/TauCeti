/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Trace
public import TauCeti.Analysis.InnerProductSpace.Projection.Basic

/-!
# Traces of compressions to subspaces

The compression of an operator `T` on an inner product space `E` to a subspace `W` with an
orthogonal projection is the operator `P_W ∘ T ∘ ι_W` on `W`. Along an orthonormal basis of `W`
its trace is the sum of the diagonal entries of `T` along that basis.

This lets conditions on the diagonal sums `∑ᵢ ⟪wᵢ, T wᵢ⟫` along orthonormal families of `k`
vectors, such as `k`-nonnegativity and `k`-positivity of an operator, be restated as
basis-independent conditions on the traces of the compressions of `T` to `k`-dimensional
subspaces, without assuming that `E` itself is finite-dimensional.

For a rectangular map `Δ : E →ₗ[𝕜] F` between finite-dimensional inner product spaces, the
tangent–normal split `Δ = (Δ - P_W Δ P_K) + P_W Δ P_K` is orthogonal for the Hilbert–Schmidt
trace pairing `tr (A† B)`.

## Main statements

* `LinearMap.trace_orthogonalProjectionOnto_comp_comp_subtype_eq_sum_inner`: the trace of the
  compression of `T` to `W` is its diagonal sum along an orthonormal basis of `W`.
* `LinearMap.re_trace_orthogonalProjectionOnto_comp_comp_subtype_eq_sum_re_inner`: the same
  identity for real parts, written with the diagonal entries `re ⟪T bᵢ, bᵢ⟫`.
* `LinearMap.forall_orthonormal_sum_inner_iff_forall_trace`: a condition on the diagonal sums
  `∑ᵢ ⟪wᵢ, T wᵢ⟫` along all orthonormal families of `k` vectors is the same condition on the
  traces of the compressions of `T` to all `k`-dimensional subspaces.
* `LinearMap.forall_orthonormal_sum_re_inner_iff_forall_re_trace`: the same statement for a
  condition on the real parts `∑ᵢ re ⟪T wᵢ, wᵢ⟫` of the diagonal sums and the real parts of the
  traces.
* `LinearMap.trace_adjoint_comp_starProjection_comp_comm`,
  `LinearMap.trace_adjoint_sub_starProjection_comp_eq_zero`,
  `LinearMap.trace_adjoint_sub_normalPart_comp_normalPart_eq_zero`: self-adjointness and trace
  orthogonality of the tangent–normal projection split.
-/

public section

open Module Finset

namespace LinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- Along an orthonormal basis `b` of a subspace `W`, the trace of the compression
`P_W ∘ T ∘ ι_W` of `T` to `W` is the sum of the diagonal entries `⟪bᵢ, T bᵢ⟫` of `T` along `b`. -/
theorem trace_orthogonalProjectionOnto_comp_comp_subtype_eq_sum_inner (T : E →ₗ[𝕜] E)
    (W : Submodule 𝕜 E) [W.HasOrthogonalProjection] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι 𝕜 W) :
    trace 𝕜 W ((W.orthogonalProjectionOnto : E →ₗ[𝕜] W) ∘ₗ T ∘ₗ W.subtype) =
      ∑ i, ⟪(b i : E), T (b i)⟫ := by
  rw [trace_eq_sum_inner _ b]
  refine sum_congr rfl fun i _ ↦ ?_
  simp only [coe_comp, Function.comp_apply, Submodule.coe_subtype, ContinuousLinearMap.coe_coe,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]

/-- Along an orthonormal basis `b` of a subspace `W`, the real part of the trace of the
compression of `T` to `W` is the sum of the real diagonal entries `re ⟪T bᵢ, bᵢ⟫` of `T`
along `b`. -/
theorem re_trace_orthogonalProjectionOnto_comp_comp_subtype_eq_sum_re_inner (T : E →ₗ[𝕜] E)
    (W : Submodule 𝕜 E) [W.HasOrthogonalProjection] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι 𝕜 W) :
    RCLike.re (trace 𝕜 W ((W.orthogonalProjectionOnto : E →ₗ[𝕜] W) ∘ₗ T ∘ₗ W.subtype)) =
      ∑ i, RCLike.re ⟪T (b i), b i⟫ := by
  rw [trace_orthogonalProjectionOnto_comp_comp_subtype_eq_sum_inner T W b, map_sum]
  exact sum_congr rfl fun i _ ↦ inner_re_symm _ _

/-- A condition on the diagonal sums `∑ᵢ ⟪wᵢ, T wᵢ⟫` of `T` along all orthonormal families of `k`
vectors is the same condition on the traces of the compressions of `T` to all `k`-dimensional
subspaces. -/
theorem forall_orthonormal_sum_inner_iff_forall_trace (T : E →ₗ[𝕜] E) {k : ℕ} (P : 𝕜 → Prop) :
    (∀ w : Fin k → E, Orthonormal 𝕜 w → P (∑ i, ⟪w i, T (w i)⟫)) ↔
      ∀ (W : Submodule 𝕜 E) [FiniteDimensional 𝕜 W], finrank 𝕜 W = k →
        P (trace 𝕜 W ((W.orthogonalProjectionOnto : E →ₗ[𝕜] W) ∘ₗ T ∘ₗ W.subtype)) := by
  refine ⟨fun h W _ hW ↦ ?_, fun h w hw ↦ ?_⟩
  · let b := (stdOrthonormalBasis 𝕜 W).reindex (finCongr hW)
    rw [trace_orthogonalProjectionOnto_comp_comp_subtype_eq_sum_inner T W b]
    exact h _ (b.orthonormal.comp_linearIsometry W.subtypeₗᵢ)
  · -- Test the hypothesis on the span of `w`, with the orthonormal basis given by `w`.
    set W := Submodule.span 𝕜 (Set.range w)
    have : FiniteDimensional 𝕜 W := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range w)
    have hli := hw.linearIndependent
    let b : OrthonormalBasis (Fin k) 𝕜 W := (Basis.span hli).toOrthonormalBasis (by
      convert orthonormal_span hw
      simp [Basis.span_apply])
    have hb (i : Fin k) : (b i : E) = w i := by simp [b, Basis.span_apply]
    have := h W ((finrank_span_eq_card hli).trans (Fintype.card_fin k))
    simpa [trace_orthogonalProjectionOnto_comp_comp_subtype_eq_sum_inner T W b, hb] using this

/-- A condition on the real parts `∑ᵢ re ⟪T wᵢ, wᵢ⟫` of the diagonal sums of `T` along all
orthonormal families of `k` vectors is the same condition on the real parts of the traces of the
compressions of `T` to all `k`-dimensional subspaces. -/
theorem forall_orthonormal_sum_re_inner_iff_forall_re_trace (T : E →ₗ[𝕜] E) {k : ℕ}
    (P : ℝ → Prop) :
    (∀ w : Fin k → E, Orthonormal 𝕜 w → P (∑ i, RCLike.re ⟪T (w i), w i⟫)) ↔
      ∀ (W : Submodule 𝕜 E) [FiniteDimensional 𝕜 W], finrank 𝕜 W = k →
        P (RCLike.re (trace 𝕜 W ((W.orthogonalProjectionOnto : E →ₗ[𝕜] W) ∘ₗ T ∘ₗ W.subtype))) := by
  have h (w : Fin k → E) :
      ∑ i, RCLike.re ⟪T (w i), w i⟫ = RCLike.re (∑ i, ⟪w i, T (w i)⟫) := by
    rw [map_sum]
    exact sum_congr rfl fun i _ ↦ inner_re_symm _ _
  simp only [h]
  exact T.forall_orthonormal_sum_inner_iff_forall_trace fun z ↦ P (RCLike.re z)

section NormalPart

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

/-- Two-sided projection compression `B ↦ P_W B P_K` is self-adjoint for the Hilbert–Schmidt
trace pairing: `tr (A† (P_W B P_K)) = tr ((P_W A P_K)† B)`. -/
theorem trace_adjoint_comp_starProjection_comp_comm (A B : E →ₗ[𝕜] F)
    (W : Submodule 𝕜 F) (K : Submodule 𝕜 E) :
    trace 𝕜 E
        (adjoint A ∘ₗ (W.starProjection.toLinearMap ∘ₗ B ∘ₗ K.starProjection.toLinearMap)) =
      trace 𝕜 E
        (adjoint (W.starProjection.toLinearMap ∘ₗ A ∘ₗ K.starProjection.toLinearMap) ∘ₗ B) := by
  calc trace 𝕜 E
          (adjoint A ∘ₗ (W.starProjection.toLinearMap ∘ₗ B ∘ₗ K.starProjection.toLinearMap))
      = trace 𝕜 E
          ((adjoint A ∘ₗ W.starProjection.toLinearMap ∘ₗ B) ∘ₗ K.starProjection.toLinearMap) := by
        simp only [comp_assoc]
    _ = trace 𝕜 E
          (K.starProjection.toLinearMap ∘ₗ (adjoint A ∘ₗ W.starProjection.toLinearMap ∘ₗ B)) :=
        trace_comp_comm' _ _
    _ = trace 𝕜 E
          (adjoint (W.starProjection.toLinearMap ∘ₗ A ∘ₗ K.starProjection.toLinearMap) ∘ₗ B) := by
        simp only [adjoint_comp, W.starProjection_isSymmetric.adjoint_eq,
          K.starProjection_isSymmetric.adjoint_eq, comp_assoc]

/-- The tangent part `Δ - P_W Δ P_K` and the normal part `P_W Δ P_K` are orthogonal for the
Hilbert–Schmidt trace pairing: `tr ((Δ - P_W Δ P_K)† (P_W Δ P_K)) = 0`. -/
theorem trace_adjoint_sub_starProjection_comp_eq_zero (Δ : E →ₗ[𝕜] F) (W : Submodule 𝕜 F)
    (K : Submodule 𝕜 E) :
    trace 𝕜 E
      (adjoint (Δ - W.starProjection.toLinearMap ∘ₗ Δ ∘ₗ K.starProjection.toLinearMap) ∘ₗ
        (W.starProjection.toLinearMap ∘ₗ Δ ∘ₗ K.starProjection.toLinearMap)) = 0 := by
  set Δ₂ : E →ₗ[𝕜] F := W.starProjection.toLinearMap ∘ₗ Δ ∘ₗ K.starProjection.toLinearMap
  have htr : trace 𝕜 E (adjoint Δ ∘ₗ Δ₂) = trace 𝕜 E (adjoint Δ₂ ∘ₗ Δ₂) := by
    calc trace 𝕜 E (adjoint Δ ∘ₗ Δ₂)
        = trace 𝕜 E (adjoint Δ ∘ₗ
            (W.starProjection.toLinearMap ∘ₗ Δ₂ ∘ₗ K.starProjection.toLinearMap)) := by
          dsimp only [Δ₂]
          rw [W.starProjection_comp_comp_starProjection_idem K Δ]
      _ = trace 𝕜 E (adjoint Δ₂ ∘ₗ Δ₂) :=
          trace_adjoint_comp_starProjection_comp_comm Δ Δ₂ W K
  rw [map_sub, sub_comp, map_sub, htr, sub_self]

/-- The canonical tangent part `Δ - Θ.normalPart Δ` and normal part `Θ.normalPart Δ` are
orthogonal for the Hilbert–Schmidt trace pairing:
`tr ((Δ - Θ.normalPart Δ)† (Θ.normalPart Δ)) = 0`. -/
theorem trace_adjoint_sub_normalPart_comp_normalPart_eq_zero (Θ Δ : E →ₗ[𝕜] F) :
    trace 𝕜 E (adjoint (Δ - Θ.normalPart Δ) ∘ₗ Θ.normalPart Δ) = 0 := by
  rw [normalPart_def]
  exact Δ.trace_adjoint_sub_starProjection_comp_eq_zero (range Θ)ᗮ (ker Θ)

end NormalPart

end LinearMap
