/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.Distribution.Submersion
public import TauCeti.Geometry.Manifold.VectorField.MappingTorus
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph
import TauCeti.Topology.MappingTorus.LocalProduct

/-!
# The mapping torus fibres over the circle

Let `φ : M ≃ₘ^n⟮I, I⟯ M` be a `C^n` diffeomorphism of a locally compact Hausdorff manifold and let
`Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` be its smooth mapping torus, with projection
`p : Y_φ → ℝ / ℤ`, `[t, x] ↦ [t]` (`TauCeti.SmoothMappingTorus.proj`). This file shows that `p`
is a smooth fibration in the sense used by the tangent splitting and the vertical bundle of `Y_φ`.

* `p` is a `C^n` submersion, with the model space `E` of `M` as complement
  (`TauCeti.SmoothMappingTorus.isSubmersionOfComplement_proj`). In the coordinates `(t, x)` it is
  the first projection `ℝ × M → ℝ` followed by the local diffeomorphism `ℝ → ℝ / ℤ`, and the
  quotient map `ℝ × M → Y_φ` is a surjective local diffeomorphism.
* Hence, for a diffeomorphism of a finite-dimensional smooth manifold, the vertical tangent spaces
  `V_y = ker dp_y` form a smooth distribution of rank `dim M`
  (`TauCeti.SmoothMappingTorus.isContMDiffDistribution_ker_mfderiv_proj`), the kernel distribution
  of the submersion `p`. Through `TauCeti.IsContMDiffDistribution.contMDiffVectorBundle` it is the
  vertical tangent bundle `V` of `Y_φ`. The line field spanned by the suspension vector field
  `T = ∂_t` is a smooth distribution of rank one
  (`TauCeti.SmoothMappingTorus.isContMDiffDistribution_span_timeVectorField`), and the two split
  the tangent bundle as `T Y_φ = ℝ T ⊕ V`
  (`TauCeti.SmoothMappingTorus.isCompl_span_timeVectorField_ker_mfderiv_proj`).
* For each real `t`, the fibre inclusion `x ↦ [t, x]` is a closed embedding of `M` onto the fibre
  `p⁻¹ [t]` (`TauCeti.SmoothMappingTorus.isClosedEmbedding_mk`), and a `C^n` smooth embedding when
  `M` is finite-dimensional and boundaryless
  (`TauCeti.SmoothMappingTorus.isSmoothEmbedding_mk`). The inclusions for two lifts `t` and
  `t + k` of the same point of the circle differ by `φ ^ k`
  (`TauCeti.SmoothMappingTorus.mk_add_intCast`).

No compactness of `M` is needed.

## Main results

* `TauCeti.SmoothMappingTorus.isSubmersionOfComplement_proj`,
  `TauCeti.SmoothMappingTorus.isSubmersion_proj`: the projection to the circle is a submersion.
* `TauCeti.SmoothMappingTorus.isContMDiffDistribution_ker_mfderiv_proj`,
  `TauCeti.SmoothMappingTorus.isContMDiffDistribution_span_timeVectorField`: its kernels form a
  smooth distribution of rank `dim M`, complementary to the smooth line field `ℝ T`.
* `TauCeti.SmoothMappingTorus.isClosedEmbedding_mk`,
  `TauCeti.SmoothMappingTorus.isSmoothEmbedding_mk`: the fibre inclusions are closed embeddings,
  and smooth embeddings.

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

/-! ### The projection is a submersion -/

section Submersion

variable [T2Space M] [LocallyCompactSpace M] [IsManifold I n M]

/-- **The projection of the mapping torus to the circle is a submersion**, with the model space
`E` of the fibre as complement. In the coordinates `(t, x)` it is the first projection of
`ℝ × M` followed by the local diffeomorphism `ℝ → ℝ / ℤ`. -/
theorem isSubmersionOfComplement_proj :
    IsSubmersionOfComplement E (𝓘(ℝ).prod I) 𝓘(ℝ) n (proj φ) := by
  refine isSubmersionOfComplement_iff.2 fun y ↦ ?_
  obtain ⟨p, rfl⟩ := uncurry_mk_surjective φ y
  rw [← (isLocalDiffeomorph_uncurry_mk φ p).isSubmersionAtOfComplement_comp_iff,
    proj_comp_uncurry_mk]
  exact (AddCircle.isLocalDiffeomorph_coe 1 n p.1).comp_isSubmersionAtOfComplement
    (isSubmersionOfComplement_iff.1 isSubmersionOfComplement_fst p)

/-- The projection of the mapping torus to the circle is a submersion. -/
theorem isSubmersion_proj : IsSubmersion (𝓘(ℝ).prod I) 𝓘(ℝ) n (proj φ) :=
  (isSubmersionOfComplement_proj φ).isSubmersion

end Submersion

section Vertical

variable [T2Space M] [LocallyCompactSpace M] [IsManifold I ∞ M] (ψ : M ≃ₘ⟮I, I⟯ M)

/-- **The vertical distribution of the mapping torus.** For a diffeomorphism of a
finite-dimensional smooth manifold `M`, the vertical tangent spaces `V_y = ker dp_y` of the
mapping torus form a smooth distribution of rank `dim M`: they are the kernels of the derivative of
the submersion `p`. -/
theorem isContMDiffDistribution_ker_mfderiv_proj [FiniteDimensional ℝ E] :
    IsContMDiffDistribution (𝓘(ℝ).prod I) ∞ (finrank ℝ E)
      (fun y : SmoothMappingTorus ψ ↦ (mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ) (proj ψ) y).ker) := by
  have h := (isSubmersion_proj ψ).isContMDiffDistribution_ker_mfderiv (m := ∞) le_rfl
  rwa [finrank_prod, finrank_self, Nat.add_sub_cancel_left] at h

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

/-- The fibre inclusion at height zero is a topological embedding: through the homeomorphism with
the topological mapping torus, it is the inclusion of the fibre over `0`. -/
private theorem isEmbedding_mk_zero : IsEmbedding (mk φ 0) := by
  have h : mk φ 0 = (homeomorphMappingTorus φ).symm ∘ MappingTorus.incl φ.toHomeomorph.symm :=
    funext fun x ↦ by
      rw [comp_apply, MappingTorus.incl_apply, homeomorphMappingTorus_symm_mk]
  rw [h]
  exact (homeomorphMappingTorus φ).symm.isEmbedding.comp
    (MappingTorus.isEmbedding_incl φ.toHomeomorph.symm)

/-- For each real `t`, the fibre inclusion `x ↦ [t, x]` is a closed embedding of `M` onto the
fibre over the class of `t`. -/
theorem isClosedEmbedding_mk (t : ℝ) : IsClosedEmbedding (mk φ t) := by
  refine ⟨?_, ?_⟩
  · -- The fibre inclusion at height `t` is the one at height `0` followed by the time-`t` map.
    have h : (flow φ).toHomeomorph t ∘ mk φ 0 = mk φ t :=
      funext fun x ↦ by rw [comp_apply, Flow.toHomeomorph_apply, flow_mk, zero_add]
    rw [← h]
    exact ((flow φ).toHomeomorph t).isEmbedding.comp (isEmbedding_mk_zero φ)
  · rw [range_mk]
    exact isClosed_singleton.preimage (continuous_proj φ)

variable [T2Space M] [LocallyCompactSpace M] [IsManifold I n M]

/-- The differential of the fibre inclusion `x ↦ [t, x]` is injective: it is `v ↦ (0, v)` followed
by the invertible differential of the quotient map `(t, x) ↦ [t, x]`. -/
theorem injective_mfderiv_mk (hn : n ≠ 0) (t : ℝ) (x : M) :
    Injective (mfderiv I (𝓘(ℝ).prod I) (mk φ t) x) := by
  have hincl : HasMFDerivAt I (𝓘(ℝ).prod I) (fun x : M ↦ (t, x)) x
      ((0 : TangentSpace I x →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (TangentSpace I x))) :=
    (hasMFDerivAt_const t x).prodMk (hasMFDerivAt_id x)
  have h := mfderiv_comp x ((contMDiff_uncurry_mk φ (t, x)).mdifferentiableAt hn)
    hincl.mdifferentiableAt
  -- `mk φ t` is the quotient map `(t, x) ↦ [t, x]` composed with `x ↦ (t, x)`, so its differential
  -- sends `u` to the differential of the quotient map applied to `(0, u)`.
  have hcomp : uncurry (mk φ) ∘ Prod.mk t = mk φ t := rfl
  rw [hcomp, hincl.mfderiv] at h
  have hu (u : TangentSpace I x) : mfderiv I (𝓘(ℝ).prod I) (mk φ t) x u =
      mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
        ((Manifold.tangentSpaceProdEquiv (t, x)).symm (0, u)) := by
    rw [h, Manifold.tangentSpaceProdEquiv_symm_apply]
    -- The model of `TangentSpace I x` is `E`, so `ContinuousLinearMap.prod` cannot be rewritten
    -- here; the composite sends `u` to the image of `(0 u, u)` by definition.
    rfl
  intro v w hvw
  rw [hu, hu] at hvw
  exact congrArg Prod.snd ((Manifold.tangentSpaceProdEquiv (t, x)).symm.injective
    (((isLocalDiffeomorph_uncurry_mk φ).isInvertible_mfderiv hn (t, x)).injective hvw))

/-- **The fibre inclusions are smooth embeddings.** For a finite-dimensional boundaryless fibre
`M` and `1 ≤ n`, the fibre inclusion `x ↦ [t, x]` is a `C^n` smooth embedding of `M` onto the
fibre over the class of `t`. -/
theorem isSmoothEmbedding_mk [I.Boundaryless] [FiniteDimensional ℝ E] (hn : 1 ≤ n) (t : ℝ) :
    IsSmoothEmbedding I (𝓘(ℝ).prod I) n (mk φ t) := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  exact ⟨(contMDiff_mk φ t).isImmersion_of_injective_mfderiv hn (injective_mfderiv_mk φ hn0 t),
    (isClosedEmbedding_mk φ t).isEmbedding⟩

end Fibre

end SmoothMappingTorus

end TauCeti
