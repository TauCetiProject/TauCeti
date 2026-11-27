/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Bounded operators on a finite-dimensional space

Bounded operators out of a finite-dimensional space are determined by the images of a basis,
with operator norm controlled by the norms of those images. Hence such operators into `E` are
approximated in operator norm by operators factoring through any operator `g : F →L[𝕜] E` of
dense range. On a finite-dimensional domain over a locally compact field, such as `ℝ`, `ℂ` or a
`p`-adic field, strict pointwise norm bounds are equivalent to strict operator-norm bounds.

## Main results

* `ContinuousLinearMap.denseRange_comp`: on operators out of a finite-dimensional space,
  postcomposition with an operator of dense range has dense range.
* `ContinuousLinearMap.tendsto_opNorm_zero_of_forall_tendsto_zero`: on a finite-dimensional
  domain, pointwise convergence to zero gives operator-norm convergence to zero.
* `ContinuousLinearMap.opNorm_lt_iff`: a strict norm bound can be checked on
  every nonzero vector of a finite-dimensional domain over a locally compact field.
* `IsCompact.isCompact_setOfPred_mapsTo`: out of a finite-dimensional space over a complete field,
  the operators sending a neighbourhood of `0` into a compact set form a compact set.
* `LinearMap.norm_toContinuousLinearMap_pos`: a nonzero linear map out of a finite-dimensional
  space has positive operator norm.
* `LinearMap.norm_toContinuousLinearMap_linearIsometry_comp`,
  `LinearMap.norm_toContinuousLinearMap_comp_linearIsometryEquiv`: the operator norm of a linear
  map out of a finite-dimensional space is unchanged by a linear isometry on the left and an
  isometric isomorphism on the right.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]

/-- On continuous linear maps out of a finite-dimensional space, postcomposition with a
continuous linear map of dense range has dense range: each `T : V →L[𝕜] E` is approximated in
operator norm by maps `g.comp U` with `U : V →L[𝕜] F`. -/
theorem denseRange_comp {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] {g : F →L[𝕜] E} (hg : DenseRange g) :
    DenseRange (g.comp : (V →L[𝕜] F) → V →L[𝕜] E) := by
  rw [Metric.denseRange_iff]
  intro T r hr
  -- Approximate the images of a basis of `V` by points of the range of `g`.
  let v := Module.finBasis 𝕜 V
  obtain ⟨C, hC, hv⟩ := v.exists_opNorm_le (F := E)
  have hrC : 0 < r / (2 * C) := by positivity
  choose y hy using fun i ↦ Metric.denseRange_iff.1 hg (T (v i)) _ hrC
  refine ⟨v.constrL y, ?_⟩
  rw [dist_eq_norm]
  calc ‖T - g.comp (v.constrL y)‖ ≤ C * (r / (2 * C)) :=
        hv hrC.le fun i ↦ by
          simpa [Module.Basis.constrL_basis, ← dist_eq_norm] using (hy i).le
    _ = r / 2 := by field_simp
    _ < r := half_lt_self hr

open Filter Topology in
/-- On a finite-dimensional space, operators that tend to zero at every point tend to zero in
operator norm: pointwise smallness at the finitely many vectors of a basis is uniform smallness on
the unit ball (`Module.Basis.exists_opNorm_le`). -/
theorem tendsto_opNorm_zero_of_forall_tendsto_zero {F ι : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {l : Filter ι} {T : ι → V →L[𝕜] F}
    (h : ∀ x, Tendsto (fun i ↦ T i x) l (𝓝 0)) :
    Tendsto (fun i ↦ ‖T i‖) l (𝓝 0) := by
  set v := Module.finBasis 𝕜 V
  obtain ⟨C, -, hC⟩ := v.exists_opNorm_le (F := F)
  have hsum : Tendsto (fun i ↦ C * ∑ j, ‖T i (v j)‖) l (𝓝 0) := by
    simpa using (tendsto_finsetSum _ fun j _ ↦ (h (v j)).norm).const_mul C
  refine squeeze_zero (fun i ↦ norm_nonneg _)
    (fun i ↦ hC (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) fun j ↦ ?_) hsum
  exact Finset.single_le_sum (f := fun j ↦ ‖T i (v j)‖) (fun _ _ ↦ norm_nonneg _)
    (Finset.mem_univ j)

section StrictNorm

open Metric

variable {𝕜 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜] [LocallyCompactSpace 𝕜]
  [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F]

/-- On a finite-dimensional domain over a locally compact field, the operator norm is less than
`c > 0` exactly when `‖A x‖ < c * ‖x‖` for every nonzero vector `x`: the supremum defining the
operator norm is attained. The positivity of `c` is needed for the zero-dimensional domain. -/
theorem opNorm_lt_iff (A : E →SL[σ₁₂] F) {c : ℝ} (hc : 0 < c) :
    ‖A‖ < c ↔ ∀ x ≠ 0, ‖A x‖ < c * ‖x‖ := by
  refine ⟨fun h x hx ↦ (A.le_opNorm x).trans_lt ?_, fun h ↦ ?_⟩
  · exact mul_lt_mul_of_pos_right h (norm_pos_iff.mpr hx)
  cases subsingleton_or_nontrivial E
  · simpa only [Subsingleton.elim A 0, norm_zero] using hc
  have := FiniteDimensional.proper 𝕜 E
  obtain ⟨k, hk⟩ := NormedField.exists_one_lt_norm 𝕜
  -- The ratio `‖A x‖ / ‖x‖` attains its maximum on the compact shell `S`, which contains a
  -- rescaling of every nonzero vector; by `opNorm_le_of_shell` this maximum bounds `‖A‖`.
  let S := closedBall (0 : E) 1 ∩ {x | 1 / ‖k‖ ≤ ‖x‖}
  have hmem {x : E} (h₁ : 1 / ‖k‖ ≤ ‖x‖) (h₂ : ‖x‖ < 1) : x ∈ S :=
    ⟨mem_closedBall_zero_iff.2 h₂.le, h₁⟩
  have hpos {x : E} (hx : x ∈ S) : 0 < ‖x‖ := (one_div_pos.2 (one_pos.trans hk)).trans_le hx.2
  have hS : IsCompact S :=
    (isCompact_closedBall 0 1).inter_right (isClosed_le continuous_const continuous_norm)
  obtain ⟨y, hy⟩ := exists_ne (0 : E)
  obtain ⟨d, -, hd₁, hd₂, -⟩ := rescale_to_shell hk one_pos hy
  obtain ⟨x, hx, hmax⟩ := hS.exists_isMaxOn ⟨d • y, hmem hd₂ hd₁⟩
    (A.continuous.norm.continuousOn.div continuous_norm.continuousOn fun x hx ↦ (hpos hx).ne')
  calc ‖A‖ ≤ ‖A x‖ / ‖x‖ := A.opNorm_le_of_shell one_pos (by positivity) hk fun z hz₁ hz₂ ↦
        (div_le_iff₀ (hpos (hmem hz₁ hz₂))).1 (hmax (hmem hz₁ hz₂))
    _ < c := (div_lt_iff₀ (hpos hx)).2 (h x (norm_pos_iff.1 (hpos hx)))

end StrictNorm

end ContinuousLinearMap

section MapsTo

open Filter Set Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Out of a finite-dimensional normed space over a complete field, the operators sending a
neighbourhood `s` of `0` into a compact set `K` form a compact set. -/
theorem IsCompact.isCompact_setOfPred_mapsTo {K : Set F} (hK : IsCompact K) {s : Set E}
    (hs : s ∈ 𝓝 (0 : E)) : IsCompact {T : E →L[𝕜] F | MapsTo T s K} := by
  -- An operator is determined by its values on a basis contained in `s`, and these values lie
  -- in `K`.
  let v := Module.finBasis 𝕜 E
  -- Some nonzero multiple `a • v` of a basis lies in `s`.
  have hev : ∀ᶠ a in 𝓝[≠] (0 : 𝕜), ∀ i, a • v i ∈ s := eventually_all.2 fun i ↦
    nhdsWithin_le_nhds <| (continuous_id.smul continuous_const).tendsto' 0 (0 : E)
      (zero_smul 𝕜 _) hs
  obtain ⟨a, hav, ha : a ≠ 0⟩ := (hev.and self_mem_nhdsWithin).exists
  -- Operators out of `E` are identified with their values on the basis `w = a • v` inside `s`.
  let w := v.map (LinearEquiv.smulOfNeZero 𝕜 E a ha)
  let e : (E →L[𝕜] F) ≃L[𝕜] (Fin _ → F) :=
    (w.equivFunL.arrowCongr (1 : F ≃L[𝕜] F)).trans (ContinuousLinearEquiv.piRing _)
  refine (e.toHomeomorph.isCompact_preimage.2 (isCompact_univ_pi fun _ ↦ hK)).of_isClosed_subset
    (hK.isClosed.setOfPred_mapsTo fun x _ ↦ continuous_eval_const x) fun T hT ↦ ?_
  simp only [mem_preimage, mem_univ_pi]
  intro i
  -- `piRing` evaluates at `Pi.single i 1`, the coordinate vector of `w i`; the inverse of
  -- `equivFunL` is that of `equivFun` by definition.
  have hwi : w.equivFunL.symm (Pi.single i 1) = w i := Basis.equivFun_symm_single w i
  have hw : w i = a • v i := by simp [w]
  change T (w.equivFunL.symm (Pi.single i 1)) ∈ K
  exact hwi ▸ hw ▸ hT (hav i)

end MapsTo

namespace LinearMap

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- A nonzero linear map out of a finite-dimensional space has positive operator norm. -/
theorem norm_toContinuousLinearMap_pos {A : E →ₗ[𝕜] F} (hA : A ≠ 0) :
    0 < ‖toContinuousLinearMap A‖ := by
  rw [norm_pos_iff]
  exact (map_ne_zero_iff _ toContinuousLinearMap.injective).mpr hA

/-- Composing a linear map out of a finite-dimensional space on the left with a linear isometry
leaves its operator norm unchanged. -/
theorem norm_toContinuousLinearMap_linearIsometry_comp (W : F →ₗᵢ[𝕜] G) (A : E →ₗ[𝕜] F) :
    ‖toContinuousLinearMap (W.toLinearMap ∘ₗ A)‖ = ‖toContinuousLinearMap A‖ := by
  have h : toContinuousLinearMap (W.toLinearMap ∘ₗ A) =
      W.toContinuousLinearMap.comp (toContinuousLinearMap A) := by
    ext; simp
  rw [h, W.norm_toContinuousLinearMap_comp]

/-- Composing a linear map out of a finite-dimensional space on the right with an isometric
isomorphism leaves its operator norm unchanged. -/
theorem norm_toContinuousLinearMap_comp_linearIsometryEquiv [FiniteDimensional 𝕜 G]
    (A : E →ₗ[𝕜] F) (U : G ≃ₗᵢ[𝕜] E) :
    ‖toContinuousLinearMap (A ∘ₗ (U : G →ₗ[𝕜] E))‖ = ‖toContinuousLinearMap A‖ := by
  have h : toContinuousLinearMap (A ∘ₗ (U : G →ₗ[𝕜] E)) =
      (toContinuousLinearMap A).comp (U : G →L[𝕜] E) := by
    ext; simp
  rw [h, (toContinuousLinearMap A).opNorm_comp_linearIsometryEquiv]

end LinearMap
