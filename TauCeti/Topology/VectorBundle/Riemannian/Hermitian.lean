/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Topology.VectorBundle.Hom
public import TauCeti.Topology.VectorBundle.Pullback.Basic
public import TauCeti.Topology.VectorBundle.Riemannian.Basic
import Mathlib.Analysis.RCLike.Lemmas

/-!
# Continuous Hermitian metrics on vector bundles

Mathlib's `IsContinuousRiemannianBundle` asks for real inner products on the fibres depending
continuously on the base point, so it does not apply to complex vector bundles with Hermitian
fibre metrics. This file records the continuity of a fibre metric over any `RCLike` field `𝕜`
through its norm: `TauCeti.ContinuousFiberNorm F E` asks that the fibre norm be continuous on
the total space. By polarization, the inner product of two continuous maps into the fibres of a
vector bundle over `𝕜` with such a norm is then continuous
(`ContinuousWithinAt.inner_bundle_of_continuousFiberNorm`), as it is for Mathlib's continuous
Riemannian bundles. A continuous Riemannian bundle has a continuous fibre norm, so the real case
is an instance of this class; so is every trivial bundle, whose fibre is any normed space, in
particular a complex inner product space. The class passes to pullback bundles.

This is the continuity hypothesis under which the Gram–Schmidt process is continuous in
`TauCeti.Topology.VectorBundle.GramSchmidt`, and under which the orthonormal frame bundle over
`𝕜` is locally trivial; for `𝕜 = ℂ` the latter is the unitary frame bundle of a Hermitian
vector bundle.

## Main definitions

* `TauCeti.ContinuousFiberNorm F E`: the fibre norm is continuous on the total space.
* `TauCeti.bundleToDual F E 𝕜 b`: for a complete model fibre `F`, the Riesz isometric
  isomorphism `E_b ≃ E_b*`, `v ↦ ⟪v, ·⟫`.

## Main results

* `ContinuousWithinAt.norm_bundle_of_continuousFiberNorm`: the fibre norm of a continuous map
  into the fibres is continuous, with `ContinuousAt`, `ContinuousOn` and `Continuous` versions.
* `ContinuousWithinAt.inner_bundle_of_continuousFiberNorm`: inner products of continuous maps into
  the fibres are continuous, with `ContinuousAt`, `ContinuousOn` and `Continuous` versions.
* `Bundle.Trivialization.exists_norm_symm_le_and_norm_le_of_isCompact`: with a finite-dimensional
  model fibre, the fibre norms are uniformly comparable to the norm of the model fibre over each
  compact subset of the base set of a linear trivialization.
* `TauCeti.continuous_bundleToDual`: for a finite-dimensional model fibre and a continuous fibre
  norm, the fibrewise Riesz isomorphism is continuous from the total space of `E` to that of its
  dual bundle.
-/

public section

open Bundle Filter Set
open scoped Topology InnerProductSpace

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]

namespace TauCeti

variable (F E) in
/-- The fibres of the bundle `E` with model fibre `F` carry norms that vary continuously: the
fibre norm is a continuous function on the total space. For fibres with inner products over an
`RCLike` field, this is continuity of the fibre metric. -/
class ContinuousFiberNorm : Prop where
  /-- The fibre norm is continuous on the total space. -/
  continuous_norm : Continuous fun z : TotalSpace F E ↦ ‖z.snd‖

/-- The fibre norm of a continuous Riemannian bundle is continuous. -/
instance [NormedSpace ℝ F] [∀ x, InnerProductSpace ℝ (E x)] [FiberBundle F E]
    [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E] : ContinuousFiberNorm F E :=
  ⟨continuous_norm_bundle F E⟩

/-- The fibre norm of a trivial bundle is the norm of the model fibre, which is continuous. -/
instance (B : Type*) [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F] :
    ContinuousFiberNorm F (Trivial B F) :=
  ⟨continuous_norm.comp (continuous_snd.comp (Trivial.isInducing_toProd B F).continuous)⟩

/-- The fibre norm of a pullback bundle is the fibre norm of the original bundle composed with
the canonical lift of total spaces, which is continuous. -/
instance [ContinuousFiberNorm F E] {B' : Type*} [TopologicalSpace B'] (f : B' → B) :
    ContinuousFiberNorm F (f *ᵖ E) :=
  ⟨(ContinuousFiberNorm.continuous_norm (F := F) (E := E)).comp (Pullback.continuous_lift F E f)⟩

end TauCeti

open TauCeti

section Norm

omit [TopologicalSpace B] [NormedAddCommGroup F]

variable [ContinuousFiberNorm F E] {X : Type*} [TopologicalSpace X] {b : X → B}
  {v : ∀ y, E (b y)} {s : Set X} {x : X}

/-- Given a map into the fibres of a bundle with a continuous fibre norm, continuous within `s`
at `x`, its fibre norm is continuous within `s` at `x`. -/
theorem ContinuousWithinAt.norm_bundle_of_continuousFiberNorm
    (hv : ContinuousWithinAt (fun y ↦ (v y : TotalSpace F E)) s x) :
    ContinuousWithinAt (fun y ↦ ‖v y‖) s x :=
  ContinuousFiberNorm.continuous_norm.continuousAt.comp_continuousWithinAt hv

/-- Given a map into the fibres of a bundle with a continuous fibre norm, continuous at `x`, its
fibre norm is continuous at `x`. -/
theorem ContinuousAt.norm_bundle_of_continuousFiberNorm
    (hv : ContinuousAt (fun y ↦ (v y : TotalSpace F E)) x) :
    ContinuousAt (fun y ↦ ‖v y‖) x :=
  ContinuousFiberNorm.continuous_norm.continuousAt.comp hv

/-- Given a map into the fibres of a bundle with a continuous fibre norm, continuous on `s`, its
fibre norm is continuous on `s`. -/
theorem ContinuousOn.norm_bundle_of_continuousFiberNorm
    (hv : ContinuousOn (fun y ↦ (v y : TotalSpace F E)) s) :
    ContinuousOn (fun y ↦ ‖v y‖) s :=
  ContinuousFiberNorm.continuous_norm.comp_continuousOn hv

/-- Given a continuous map into the fibres of a bundle with a continuous fibre norm, its fibre
norm is continuous. -/
theorem Continuous.norm_bundle_of_continuousFiberNorm
    (hv : Continuous fun y ↦ (v y : TotalSpace F E)) :
    Continuous fun y ↦ ‖v y‖ :=
  ContinuousFiberNorm.continuous_norm.comp hv

end Norm

section Compact

variable {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 F] [∀ x, NormedSpace 𝕜 (E x)] [FiberBundle F E]
  [ContinuousFiberNorm F E] [FiniteDimensional 𝕜 F]

namespace Bundle.Trivialization

variable (𝕜) in
include 𝕜 in
/-- **Comparison with the model fibre over compact sets.** Over a compact subset `K` of the base
set of a linear trivialization `e` of a vector bundle with finite-dimensional model fibre `F` and
continuous fibre norm, the fibre norms are uniformly comparable to the norm of `F`: there are
constants `C` and `C'` with `‖e.symm x v‖ ≤ C ‖v‖` and `‖v‖ ≤ C' ‖e.symm x v‖` for all `x ∈ K`
and `v : F`. On a noncompact part of the base set no such constants need exist. -/
theorem exists_norm_symm_le_and_norm_le_of_isCompact (e : Trivialization F (π F E))
    [e.IsLinear 𝕜] {K : Set B} (hK : IsCompact K) (hKe : K ⊆ e.baseSet) :
    ∃ C C' : NNReal, ∀ x ∈ K, ∀ v : F, ‖e.symm x v‖ ≤ C * ‖v‖ ∧ ‖v‖ ≤ C' * ‖e.symm x v‖ := by
  -- On `K × sphere 0 1`, the continuous function `(x, u) ↦ ‖e.symm x u‖` is bounded above, and
  -- below by its positive minimum; homogeneity in `u` extends both bounds to all of `F`.
  have := FiniteDimensional.proper_rclike 𝕜 F
  set S := K ×ˢ Metric.sphere (0 : F) 1
  have hS : IsCompact S := hK.prod (isCompact_sphere 0 1)
  have hφ : ContinuousOn (fun z : B × F ↦ ‖e.symm z.1 z.2‖) S :=
    (e.continuousOn_symm.norm_bundle_of_continuousFiberNorm).mono
      (Set.prod_mono hKe (Set.subset_univ _))
  -- Over the base set, `e.symm x` is the inverse of the linear equivalence
  -- `e.continuousLinearEquivAt 𝕜 x`.
  have hΦ (x : B) (hx : x ∈ K) : ⇑(e.continuousLinearEquivAt 𝕜 x (hKe hx)).symm = e.symm x :=
    e.continuousLinearEquivAt_symm_apply 𝕜 x (hKe hx)
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hφ
  -- The minimum of `‖e.symm x u‖` on `S` is positive, as `e.symm x` is injective on the base set.
  obtain ⟨m, hm, hmS⟩ : ∃ m : ℝ, 0 < m ∧ ∀ z ∈ S, m ≤ ‖e.symm z.1 z.2‖ := by
    rcases S.eq_empty_or_nonempty with hSe | hSne
    · exact ⟨1, one_pos, by simp [hSe]⟩
    obtain ⟨z, hz, hmin⟩ := hS.exists_isMinOn hSne hφ
    refine ⟨‖e.symm z.1 z.2‖, ?_, fun w hw ↦ hmin hw⟩
    rw [← hΦ z.1 hz.1, norm_pos_iff, ne_eq, ContinuousLinearEquiv.map_eq_zero_iff]
    exact fun h ↦ by simpa [h] using hz.2
  refine ⟨Real.toNNReal C, Real.toNNReal m⁻¹, fun x hx v ↦ ?_⟩
  have hup (u : F) (hu : u ∈ Metric.sphere (0 : F) 1) : ‖e.symm x u‖ ≤ C := by
    simpa using hC (x, u) ⟨hx, hu⟩
  have hlow (u : F) (hu : u ∈ Metric.sphere (0 : F) 1) : m ≤ ‖e.symm x u‖ := hmS (x, u) ⟨hx, hu⟩
  rw [← hΦ x hx] at hup hlow ⊢
  set Φ := (e.continuousLinearEquivAt 𝕜 x (hKe hx)).symm
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  -- Writing `v = ‖v‖ • u` with `‖u‖ = 1`, linearity of `Φ` reduces both bounds to `u`.
  have hv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  set u : F := ((‖v‖⁻¹ : ℝ) : 𝕜) • v
  have hu : u ∈ Metric.sphere (0 : F) 1 := by simp [u, norm_smul, hv']
  have hnorm : ‖Φ v‖ = ‖v‖ * ‖Φ u‖ := by simp [u, norm_smul, hv']
  -- Prove both bounds with real constants, then enlarge them to their `toNNReal`.
  have h₁ : ‖Φ v‖ ≤ C * ‖v‖ := by rw [hnorm, mul_comm]; gcongr; exact hup u hu
  have h₂ : ‖v‖ ≤ m⁻¹ * ‖Φ v‖ :=
    calc ‖v‖ = m⁻¹ * (‖v‖ * m) := by field_simp
      _ ≤ m⁻¹ * ‖Φ v‖ := by rw [hnorm]; gcongr; exact hlow u hu
  exact ⟨h₁.trans (by gcongr; exact C.le_coe_toNNReal),
    h₂.trans (by gcongr; exact m⁻¹.le_coe_toNNReal)⟩

end Bundle.Trivialization

end Compact

variable {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 F] [∀ x, InnerProductSpace 𝕜 (E x)]
  [FiberBundle F E] [VectorBundle 𝕜 F E] [ContinuousFiberNorm F E]
  {X : Type*} [TopologicalSpace X] {b : X → B} {v w : ∀ y, E (b y)} {s : Set X} {x : X}

/-- Given two maps into the same fibres of a vector bundle with a continuous fibre norm, both
continuous within `s` at `x`, their inner product is continuous within `s` at `x`. -/
theorem ContinuousWithinAt.inner_bundle_of_continuousFiberNorm
    (hv : ContinuousWithinAt (fun y ↦ (v y : TotalSpace F E)) s x)
    (hw : ContinuousWithinAt (fun y ↦ (w y : TotalSpace F E)) s x) :
    ContinuousWithinAt (fun y ↦ ⟪v y, w y⟫_𝕜) s x := by
  -- By polarization, the inner product is a combination of the norms of `v + c • w` for
  -- `c ∈ {1, -1, -I, I}`. These combinations are continuous: over the base set of the
  -- trivialization `e` at `b x`, their coordinates are those of `v` plus `c` times those of `w`.
  obtain ⟨hb, hv'⟩ := (FiberBundle.continuousWithinAt_totalSpace F _).1 hv
  have hw' := ((FiberBundle.continuousWithinAt_totalSpace F _).1 hw).2
  let e := trivializationAt F E (b x)
  have hx : b x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' (b x)
  have hmem : ∀ᶠ y in 𝓝[s] x, b y ∈ e.baseSet := hb (e.open_baseSet.mem_nhds hx)
  have hformula (c : 𝕜) (y : X) (hy : b y ∈ e.baseSet) :
      (e ⟨b y, v y + c • w y⟩).2 = (e ⟨b y, v y⟩).2 + c • (e ⟨b y, w y⟩).2 := by
    simp only [← e.continuousLinearMapAt_apply_of_mem (R := 𝕜) hy, map_add, map_smul]
  have hn (c : 𝕜) : ContinuousWithinAt (fun y ↦ ((‖v y + c • w y‖ : ℝ) : 𝕜)) s x := by
    have hvw : ContinuousWithinAt (fun y ↦ (⟨b y, v y + c • w y⟩ : TotalSpace F E)) s x :=
      (FiberBundle.continuousWithinAt_totalSpace F _).2 ⟨hb, (hv'.add (hw'.const_smul c))
        |>.congr_of_eventuallyEq (hmem.mono (hformula c)) (hformula c x hx)⟩
    exact RCLike.continuous_ofReal.continuousAt.comp_continuousWithinAt
      hvw.norm_bundle_of_continuousFiberNorm
  have h1 := hn 1
  have h2 := hn (-1)
  have h3 := hn (-RCLike.I)
  have h4 := hn RCLike.I
  simp only [one_smul, neg_smul, ← sub_eq_add_neg] at h1 h2 h3 h4
  exact ((((h1.pow 2).sub (h2.pow 2)).add (((h3.pow 2).sub (h4.pow 2)).mul
    continuousWithinAt_const)).div_const 4).congr
      (fun y _ ↦ inner_eq_sum_norm_sq_div_four _ _) (inner_eq_sum_norm_sq_div_four _ _)

/-- Given two maps into the same fibres of a vector bundle with a continuous fibre norm, both
continuous at `x`, their inner product is continuous at `x`. -/
theorem ContinuousAt.inner_bundle_of_continuousFiberNorm
    (hv : ContinuousAt (fun y ↦ (v y : TotalSpace F E)) x)
    (hw : ContinuousAt (fun y ↦ (w y : TotalSpace F E)) x) :
    ContinuousAt (fun y ↦ ⟪v y, w y⟫_𝕜) x := by
  simp only [← continuousWithinAt_univ] at hv hw ⊢
  exact hv.inner_bundle_of_continuousFiberNorm hw

/-- Given two maps into the same fibres of a vector bundle with a continuous fibre norm, both
continuous on `s`, their inner product is continuous on `s`. -/
theorem ContinuousOn.inner_bundle_of_continuousFiberNorm
    (hv : ContinuousOn (fun y ↦ (v y : TotalSpace F E)) s)
    (hw : ContinuousOn (fun y ↦ (w y : TotalSpace F E)) s) :
    ContinuousOn (fun y ↦ ⟪v y, w y⟫_𝕜) s :=
  fun y hy ↦ (hv y hy).inner_bundle_of_continuousFiberNorm (hw y hy)

/-- Given two continuous maps into the same fibres of a vector bundle with a continuous fibre
norm, their inner product is continuous. -/
theorem Continuous.inner_bundle_of_continuousFiberNorm
    (hv : Continuous fun y ↦ (v y : TotalSpace F E))
    (hw : Continuous fun y ↦ (w y : TotalSpace F E)) :
    Continuous fun y ↦ ⟪v y, w y⟫_𝕜 :=
  continuous_iff_continuousAt.2 fun _ ↦
    hv.continuousAt.inner_bundle_of_continuousFiberNorm hw.continuousAt

/-! ### The fibrewise Riesz isomorphism -/

namespace TauCeti

variable [CompleteSpace F]

variable (F E 𝕜) in
omit [ContinuousFiberNorm F E] in
/-- The fibrewise Riesz isomorphism `v ↦ ⟪v, ·⟫` of a bundle `E` of inner product spaces over `𝕜`
with complete model fibre `F`, a conjugate-linear isometric isomorphism `E_b ≃ E_b*`. -/
noncomputable def bundleToDual (b : B) : E b ≃ₗᵢ⋆[𝕜] StrongDual 𝕜 (E b) :=
  haveI := VectorBundle.completeSpace (R := 𝕜) F E b
  InnerProductSpace.toDual 𝕜 (E b)

omit [ContinuousFiberNorm F E] in
@[simp] theorem bundleToDual_apply (b : B) (v w : E b) :
    bundleToDual F E 𝕜 b v w = ⟪v, w⟫_𝕜 :=
  haveI := VectorBundle.completeSpace (R := 𝕜) F E b
  InnerProductSpace.toDual_apply_apply

omit [ContinuousFiberNorm F E] in
@[simp] theorem bundleToDual_symm_apply (b : B) (φ : StrongDual 𝕜 (E b)) (w : E b) :
    ⟪(bundleToDual F E 𝕜 b).symm φ, w⟫_𝕜 = φ w :=
  haveI := VectorBundle.completeSpace (R := 𝕜) F E b
  InnerProductSpace.toDual_symm_apply

variable [FiniteDimensional 𝕜 F]

variable (𝕜) in
/-- **The Riesz isomorphism of a bundle with continuous fibre norm is continuous.** If the model
fibre `F` is finite-dimensional and the fibre norm is continuous on the total space, `v ↦ ⟪v, ·⟫`
is continuous from the total space of `E` to that of its dual. -/
theorem continuous_bundleToDual :
    Continuous fun v : TotalSpace F E ↦
      TotalSpace.mk' (StrongDual 𝕜 F) (E := fun b ↦ StrongDual 𝕜 (E b)) v.proj
        (bundleToDual F E 𝕜 v.proj v.snd) := by
  refine continuous_iff_continuousAt.mpr fun p ↦ ?_
  rw [continuousAt_hom_bundle]
  refine ⟨(FiberBundle.continuous_proj F E).continuousAt, continuousAt_clm_apply.mpr fun w ↦ ?_⟩
  let e := trivializationAt F E p.proj
  have hp : p.proj ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F E p.proj
  have hs : ContinuousAt (fun q : TotalSpace F E ↦ TotalSpace.mk' F q.proj (e.symm q.proj w)) p :=
    (e.continuousOn_symm.continuousAt
      ((e.open_baseSet.prod isOpen_univ).mem_nhds ⟨hp, mem_univ w⟩)).comp
        ((FiberBundle.continuous_proj F E).continuousAt.prodMk continuousAt_const)
  have hi : ContinuousAt (fun q : TotalSpace F E ↦ ⟪q.snd, e.symm q.proj w⟫_𝕜) p :=
    ContinuousAt.inner_bundle_of_continuousFiberNorm (b := TotalSpace.proj)
      (v := fun q ↦ q.snd) continuousAt_id hs
  refine hi.congr_of_eventuallyEq ?_
  filter_upwards [(FiberBundle.continuous_proj F E).continuousAt.preimage_mem_nhds
    (e.open_baseSet.mem_nhds hp)] with q hq
  simp only [ContinuousLinearMap.inCoordinates, Trivial.eq_trivialization,
    Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_comp,
    ContinuousLinearMap.comp_apply, bundleToDual_apply]
  exact congrArg (⟪q.snd, ·⟫_𝕜) (e.symmL_apply hq w)

end TauCeti
