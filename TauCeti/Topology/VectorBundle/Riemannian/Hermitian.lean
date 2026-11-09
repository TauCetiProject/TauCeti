/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Pullback
public import TauCeti.Topology.VectorBundle.Riemannian.Basic

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

## Main results

* `ContinuousWithinAt.norm_bundle_of_continuousFiberNorm`: the fibre norm of a continuous map
  into the fibres is continuous, with `ContinuousAt`, `ContinuousOn` and `Continuous` versions.
* `ContinuousWithinAt.inner_bundle_of_continuousFiberNorm`: inner products of continuous maps into
  the fibres are continuous, with `ContinuousAt`, `ContinuousOn` and `Continuous` versions.
-/

public section

open Bundle Filter
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
  continuous_norm : Continuous fun z : TotalSpace F E ↦ ‖z.2‖

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
