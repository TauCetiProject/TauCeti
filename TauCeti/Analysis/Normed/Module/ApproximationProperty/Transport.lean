/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.ApproximationProperty.Basic

/-!
# Transport of approximation properties

Approximation properties pass to bounded linear retracts. If `i : F →L[𝕜] E` and
`p : E →L[𝕜] F` satisfy `p ∘ i = id`, an approximating operator `T` on `E` gives
the finite-rank approximant `p ∘ T ∘ i` on `F`. A bound `C` becomes
`C * ‖p‖₊ * ‖i‖₊`.

Consequently AP and BAP are invariant under continuous linear equivalence, and a
projection onto a subspace transfers a BAP bound `C` to `C * ‖p‖₊`. Linear
isometric equivalences preserve the bound and hence MAP; contractive projections
also preserve MAP. These results do not require completeness or a nonzero space.

## References

* R. E. Megginson, *An Introduction to Banach Space Theory*, Section 3.4.
* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Chapter 1.
-/

public section

open Function Set
open scoped NNReal

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace TauCeti

/-- The approximation property passes to a bounded linear retract. -/
theorem HasApproximationProperty.of_leftInverse (h : HasApproximationProperty 𝕜 E)
    (i : F →L[𝕜] E) (p : E →L[𝕜] F) (hp : LeftInverse p i) :
    HasApproximationProperty 𝕜 F := by
  rw [hasApproximationProperty_iff] at h ⊢
  intro K hK ε hε
  obtain ⟨T, hT, herr⟩ := h (i '' K) (hK.image i.continuous) (ε / (‖p‖ + 1))
    (div_pos hε (by positivity))
  refine ⟨p.comp (T.comp i), (hT.comp_right i.toLinearMap).comp_left p.toLinearMap,
    fun x hx ↦ ?_⟩
  have herror := herr (i x) (mem_image_of_mem i hx)
  calc
    ‖p.comp (T.comp i) x - x‖ = ‖p (T (i x) - i x)‖ := by simp [hp x]
    _ ≤ ‖p‖ * ‖T (i x) - i x‖ := p.le_opNorm _
    _ ≤ (‖p‖ + 1) * ‖T (i x) - i x‖ := by gcongr; linarith
    _ < (‖p‖ + 1) * (ε / (‖p‖ + 1)) := by gcongr
    _ = ε := mul_div_cancel₀ _ (by positivity)

/-- A bounded linear retract inherits a BAP bound multiplied by the norms of the
retraction and section. -/
theorem HasBoundedApproximationPropertyWith.of_leftInverse {C : ℝ≥0}
    (h : HasBoundedApproximationPropertyWith 𝕜 E C)
    (i : F →L[𝕜] E) (p : E →L[𝕜] F) (hp : LeftInverse p i) :
    HasBoundedApproximationPropertyWith 𝕜 F (C * ‖p‖₊ * ‖i‖₊) := by
  rw [hasBoundedApproximationPropertyWith_iff] at h ⊢
  intro K hK ε hε
  obtain ⟨T, hT, hnorm, herr⟩ := h (i '' K) (hK.image i.continuous) (ε / (‖p‖ + 1))
    (div_pos hε (by positivity))
  refine ⟨p.comp (T.comp i), (hT.comp_right i.toLinearMap).comp_left p.toLinearMap, ?_,
    fun x hx ↦ ?_⟩
  · calc
      ‖p.comp (T.comp i)‖ ≤ ‖p‖ * (‖T‖ * ‖i‖) :=
        (p.opNorm_comp_le _).trans (by gcongr; exact T.opNorm_comp_le i)
      _ ≤ ‖p‖ * (C * ‖i‖) := by gcongr
      _ = ↑(C * ‖p‖₊ * ‖i‖₊) := by push_cast; ring
  · have herror := herr (i x) (mem_image_of_mem i hx)
    calc
      ‖p.comp (T.comp i) x - x‖ = ‖p (T (i x) - i x)‖ := by simp [hp x]
      _ ≤ ‖p‖ * ‖T (i x) - i x‖ := p.le_opNorm _
      _ ≤ (‖p‖ + 1) * ‖T (i x) - i x‖ := by gcongr; linarith
      _ < (‖p‖ + 1) * (ε / (‖p‖ + 1)) := by gcongr
      _ = ε := mul_div_cancel₀ _ (by positivity)

/-- The bounded approximation property passes to a bounded linear retract. -/
theorem HasBoundedApproximationProperty.of_leftInverse
    (h : HasBoundedApproximationProperty 𝕜 E)
    (i : F →L[𝕜] E) (p : E →L[𝕜] F) (hp : LeftInverse p i) :
    HasBoundedApproximationProperty 𝕜 F := by
  obtain ⟨C, hC⟩ := hasBoundedApproximationProperty_iff.mp h
  exact (hC.of_leftInverse i p hp).hasBoundedApproximationProperty

/-- The approximation property passes to the range of a bounded projection. -/
theorem HasApproximationProperty.of_projection (h : HasApproximationProperty 𝕜 E)
    (S : Submodule 𝕜 E) (p : E →L[𝕜] S) (hp : ∀ x : S, p x = x) :
    HasApproximationProperty 𝕜 S :=
  h.of_leftInverse S.subtypeL p hp

/-- A projection onto a subspace multiplies its inherited BAP bound by at most
the norm of the projection. -/
theorem HasBoundedApproximationPropertyWith.of_projection {C : ℝ≥0}
    (h : HasBoundedApproximationPropertyWith 𝕜 E C)
    (S : Submodule 𝕜 E) (p : E →L[𝕜] S) (hp : ∀ x : S, p x = x) :
    HasBoundedApproximationPropertyWith 𝕜 S (C * ‖p‖₊) := by
  apply (h.of_leftInverse S.subtypeL p hp).mono
  have hsub : ‖S.subtypeL‖₊ ≤ 1 := S.norm_subtypeL_le
  simpa using mul_le_mul_of_nonneg_left
    hsub (by positivity : 0 ≤ C * ‖p‖₊)

/-- The bounded approximation property passes to the range of a bounded projection. -/
theorem HasBoundedApproximationProperty.of_projection
    (h : HasBoundedApproximationProperty 𝕜 E)
    (S : Submodule 𝕜 E) (p : E →L[𝕜] S) (hp : ∀ x : S, p x = x) :
    HasBoundedApproximationProperty 𝕜 S :=
  h.of_leftInverse S.subtypeL p hp

/-- A contractive projection preserves the metric approximation property. -/
theorem HasMetricApproximationProperty.of_projection (h : HasMetricApproximationProperty 𝕜 E)
    (S : Submodule 𝕜 E) (p : E →L[𝕜] S) (hp : ∀ x : S, p x = x) (hnorm : ‖p‖ ≤ 1) :
    HasMetricApproximationProperty 𝕜 S := by
  apply hasMetricApproximationProperty_iff.mpr
  apply (hasMetricApproximationProperty_iff.mp h |>.of_projection S p hp).mono
  have hpbound : ‖p‖₊ ≤ 1 := hnorm
  simpa using hpbound

end TauCeti

namespace ContinuousLinearEquiv

/-- The approximation property is invariant under continuous linear equivalence. -/
theorem hasApproximationProperty_iff (e : E ≃L[𝕜] F) :
    TauCeti.HasApproximationProperty 𝕜 E ↔ TauCeti.HasApproximationProperty 𝕜 F :=
  ⟨fun h ↦ h.of_leftInverse e.symm.toContinuousLinearMap e.toContinuousLinearMap e.apply_symm_apply,
    fun h ↦ h.of_leftInverse e.toContinuousLinearMap e.symm.toContinuousLinearMap
      e.symm_apply_apply⟩

/-- Transport a prescribed BAP bound along a continuous linear equivalence. -/
theorem hasBoundedApproximationPropertyWith (e : E ≃L[𝕜] F) {C : ℝ≥0}
    (h : TauCeti.HasBoundedApproximationPropertyWith 𝕜 E C) :
    TauCeti.HasBoundedApproximationPropertyWith 𝕜 F
      (C * ‖e.toContinuousLinearMap‖₊ * ‖e.symm.toContinuousLinearMap‖₊) :=
  h.of_leftInverse e.symm.toContinuousLinearMap e.toContinuousLinearMap e.apply_symm_apply

/-- The bounded approximation property is invariant under continuous linear equivalence. -/
theorem hasBoundedApproximationProperty_iff (e : E ≃L[𝕜] F) :
    TauCeti.HasBoundedApproximationProperty 𝕜 E ↔
      TauCeti.HasBoundedApproximationProperty 𝕜 F :=
  ⟨fun h ↦ h.of_leftInverse e.symm.toContinuousLinearMap e.toContinuousLinearMap e.apply_symm_apply,
    fun h ↦ h.of_leftInverse e.toContinuousLinearMap e.symm.toContinuousLinearMap
      e.symm_apply_apply⟩

end ContinuousLinearEquiv

namespace LinearIsometryEquiv

/-- Linear isometric equivalences preserve a prescribed BAP bound, including on
the zero space. -/
theorem hasBoundedApproximationPropertyWith (e : E ≃ₗᵢ[𝕜] F) {C : ℝ≥0}
    (h : TauCeti.HasBoundedApproximationPropertyWith 𝕜 E C) :
    TauCeti.HasBoundedApproximationPropertyWith 𝕜 F C := by
  apply (h.of_leftInverse e.symm.toLinearIsometry.toContinuousLinearMap
    e.toLinearIsometry.toContinuousLinearMap e.apply_symm_apply).mono
  calc
    C * ‖e.toLinearIsometry.toContinuousLinearMap‖₊ *
        ‖e.symm.toLinearIsometry.toContinuousLinearMap‖₊ ≤ C * 1 * 1 := by
      gcongr
      · exact e.toLinearIsometry.norm_toContinuousLinearMap_le
      · exact e.symm.toLinearIsometry.norm_toContinuousLinearMap_le
    _ = C := by simp

/-- A prescribed bounded approximation property is invariant under linear
isometric equivalence. -/
theorem hasBoundedApproximationPropertyWith_iff (e : E ≃ₗᵢ[𝕜] F) {C : ℝ≥0} :
    TauCeti.HasBoundedApproximationPropertyWith 𝕜 E C ↔
      TauCeti.HasBoundedApproximationPropertyWith 𝕜 F C :=
  ⟨e.hasBoundedApproximationPropertyWith, e.symm.hasBoundedApproximationPropertyWith⟩

/-- The metric approximation property is invariant under linear isometric equivalence. -/
theorem hasMetricApproximationProperty_iff (e : E ≃ₗᵢ[𝕜] F) :
    TauCeti.HasMetricApproximationProperty 𝕜 E ↔
      TauCeti.HasMetricApproximationProperty 𝕜 F := by
  simp only [TauCeti.hasMetricApproximationProperty_iff,
    e.hasBoundedApproximationPropertyWith_iff]

end LinearIsometryEquiv
