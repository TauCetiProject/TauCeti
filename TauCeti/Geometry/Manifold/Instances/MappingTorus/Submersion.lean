/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.Distribution.Submersion
public import TauCeti.Geometry.Manifold.Instances.MappingTorus.Vertical
public import TauCeti.Geometry.Manifold.VectorField.MappingTorus
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph

/-!
# The mapping torus fibres over the circle

Let `φ : M ≃ₘ^n⟮I, I⟯ M` be a `C^n` diffeomorphism of a locally compact Hausdorff manifold and let
`Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` be its smooth mapping torus, with projection
`p : Y_φ → ℝ / ℤ`, `[t, x] ↦ [t]` (`TauCeti.SmoothMappingTorus.proj`). This file shows that `p`
is a `C^n` submersion whose kernels form the smooth vertical bundle of `Y_φ`, and that the fibre
inclusions are smooth embeddings.

* `p` is a `C^n` submersion, with the model space `E` of `M` as complement
  (`TauCeti.SmoothMappingTorus.isSubmersionOfComplement_proj`). In the coordinates `(t, x)` it is
  the first projection `ℝ × M → ℝ` followed by the local diffeomorphism `ℝ → ℝ / ℤ`, and the
  quotient map `ℝ × M → Y_φ` is a surjective local diffeomorphism.
* Hence, for a `C^n` diffeomorphism of a finite-dimensional manifold and `m + 1 ≤ n`, the
  vertical tangent spaces `V_y = ker dp_y` form a `C^m` distribution of rank `dim M`
  (`TauCeti.SmoothMappingTorus.isContMDiffDistribution_ker_mfderiv_proj`), the kernel distribution
  of the submersion `p`. Through `TauCeti.IsContMDiffDistribution.contMDiffVectorBundle` it is the
  vertical tangent bundle `V` of `Y_φ`. For a smooth diffeomorphism, the line field spanned by
  the suspension vector field `T = ∂_t` is a smooth distribution of rank one
  (`TauCeti.SmoothMappingTorus.isContMDiffDistribution_span_timeVectorField`), and the two split
  the tangent bundle as `T Y_φ = ℝ T ⊕ V`
  (`TauCeti.SmoothMappingTorus.isCompl_span_timeVectorField_ker_mfderiv_proj`).
* For each real `t`, the fibre inclusion `x ↦ [t, x]` is a `C^n` smooth embedding of `M` onto the
  fibre `p⁻¹ [t]` (`TauCeti.SmoothMappingTorus.isSmoothEmbedding_mk`): in product charts the
  slice `x ↦ (0, x)` is the inclusion `u ↦ (0, u)`, and it is a closed embedding by
  `TauCeti.SmoothMappingTorus.isClosedEmbedding_mk`. The inclusions for two lifts `t` and
  `t + k` of the same point of the circle differ by `φ ^ k`
  (`TauCeti.SmoothMappingTorus.mk_add_intCast`).

No compactness of `M` is needed.

## Main results

* `TauCeti.SmoothMappingTorus.isSubmersionOfComplement_proj`,
  `TauCeti.SmoothMappingTorus.isSubmersion_proj` and
  `TauCeti.SmoothMappingTorus.isContMDiffDistribution_ker_mfderiv_proj`, in
  `TauCeti.Geometry.Manifold.Instances.MappingTorus.Vertical`: the projection to the circle is a
  submersion whose kernels form a distribution of rank `dim M`.
* `TauCeti.SmoothMappingTorus.isContMDiffDistribution_span_timeVectorField`: this distribution is
  complementary to the smooth line field `ℝ T`.
* `TauCeti.SmoothMappingTorus.isSmoothEmbedding_mk`: the fibre inclusions are smooth embeddings.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 4 (submersions and smooth embeddings) and Chapter 21
  (quotients by discrete group actions).
-/

public noncomputable section

open Set Function Topology Module Manifold
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothMappingTorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}
  (φ : M ≃ₘ^n⟮I, I⟯ M)

section Vertical

variable [T2Space M] [LocallyCompactSpace M] [IsManifold I ∞ M] (ψ : M ≃ₘ⟮I, I⟯ M)

/-- The line field `ℝ T` spanned by the suspension vector field `T = ∂_t` is a smooth distribution
of rank one, with global frame `T`. Together with
`TauCeti.SmoothMappingTorus.isContMDiffDistribution_ker_mfderiv_proj` and the pointwise splitting
`TauCeti.SmoothMappingTorus.isCompl_span_timeVectorField_ker_mfderiv_proj`, this splits the
tangent bundle of the mapping torus as `T Y_φ = ℝ T ⊕ V` into smooth subbundles. -/
theorem isContMDiffDistribution_span_timeVectorField :
    IsContMDiffDistribution (𝓘(ℝ).prod I) ∞ 1
      (fun y : SmoothMappingTorus ψ ↦ ℝ ∙ timeVectorField ψ y) := by
  refine isContMDiffDistribution_iff.2 fun _ ↦ ⟨univ, isOpen_univ, mem_univ _,
    fun _ ↦ timeVectorField ψ,
    ⟨fun _ ↦ (contMDiff_timeVectorField ψ).contMDiffOn, fun {y} _ ↦ ?_, fun {y} _ ↦ ?_⟩⟩
  · -- `T` does not vanish, since `dp(T) = 1`.
    refine linearIndependent_unique_iff.2 fun hT ↦ one_ne_zero (α := ℝ) ?_
    rw [← mfderiv_proj_timeVectorField ψ y, hT, map_zero]
    -- The zero of the tangent line `TangentSpace 𝓘(ℝ) _` is the real number `0`.
    rfl
  · rw [range_const]

end Vertical

/-! ### The fibre inclusions -/

section Fibre

variable [T2Space M] [LocallyCompactSpace M] [IsManifold I n M]

/-- **The fibre inclusions are smooth embeddings.** For each real `t`, the fibre inclusion
`x ↦ [t, x]` is a `C^n` smooth embedding of `M` onto the fibre over the class of `t`. -/
theorem isSmoothEmbedding_mk (t : ℝ) : IsSmoothEmbedding I (𝓘(ℝ).prod I) n (mk φ t) := by
  refine ⟨?_, (isClosedEmbedding_mk φ t).isEmbedding⟩
  -- The fibre inclusion at height `t` is the slice `x ↦ (0, x)`, followed by the quotient map and
  -- the time-`t` map of the suspension flow.
  have h : flowDiffeomorph φ t ∘ (uncurry (mk φ) ∘ Prod.mk 0) = mk φ t :=
    funext fun x ↦ by simp [flow_mk]
  rw [← h, isImmersion_diffeomorph_comp_iff]
  exact isImmersion_isLocalDiffeomorphAt_comp (fun x ↦ isLocalDiffeomorph_uncurry_mk φ _)
    (isImmersion_prodMkRight_of_extChartAt_eq_zero (by simp))

end Fibre

end SmoothMappingTorus

end TauCeti
