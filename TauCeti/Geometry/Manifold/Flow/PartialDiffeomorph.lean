/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Flow.Basic
import TauCeti.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Geometry.Manifold.VectorField.Pullback
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# Vector fields and flows through partial diffeomorphisms

Let `Φ` be a partial diffeomorphism from a manifold `M` to a manifold `M'`, such as a chart, and
let it carry a vector field `X` on `M` to a vector field `Y` on `M'` on its source:
`dΦ_x (X x) = Y (Φ x)` for `x ∈ Φ.source`. Then `Φ⁻¹` carries `Y` back to `X` on the target
(`PartialDiffeomorph.mfderiv_symm_apply_eq_of_mfderiv_apply_eq`), and so it carries the pieces of
trajectories of `Y` that stay in the target to trajectories of `X`. Hence the flows correspond for
as long as the trajectory of `Y` stays in the target:

`flowOf X t x = Φ⁻¹ (flowOf Y t (Φ x))` if `flowOf Y s (Φ x) ∈ Φ.target` for `s ∈ [0, t]`

(`PartialDiffeomorph.flowOf_eq_symm_flowOf`). In contrast with a global diffeomorphism
(`Diffeomorph.apply_flowOf`), the flow of `X` may exist longer than the trajectory of `Y` stays in
the target, so only this direction holds in general. Since the trajectories of points near `x`
stay in the target for the same times, the identity holds near `x`
(`PartialDiffeomorph.eventually_flowOf_eq_symm_flowOf`), and the time-`t` maps have corresponding
derivatives (`PartialDiffeomorph.hasMFDerivAt_flowOf`).

This is how the flow of a vector field on a manifold is computed in a chart: near a point where
the field does not vanish, a straightening chart carries it to a constant field, whose flow is
translation, and a perturbation of the field supported in the chart is computed in the model
space. Such perturbations are built in the model space and carried to the manifold: a `C^m` field
`W₀` with compact support in the target of a `C^n` partial diffeomorphism `Φ` onto an open subset
of a normed space, with `m + 1 ≤ n`, is the image under `Φ` of a `C^m` field on the manifold which
vanishes outside `Φ⁻¹ (tsupport W₀)` (`PartialDiffeomorph.exists_contMDiff_mfderiv_apply_eq`). On
the source of `Φ` it is the pullback `VectorField.mpullback` of `W₀`, extended by zero. For the
extended chart at a point, possibly with boundary, this is `TauCeti.chartField`; here `Φ` is any
partial diffeomorphism onto an open subset of the normed space, such as a straightening chart.

## Main results

* `PartialDiffeomorph.exists_contMDiff_mfderiv_apply_eq`: a compactly supported vector field on
  the target of a partial diffeomorphism into a normed space is the image of a vector field on the
  manifold, of the same regularity, vanishing off the preimage of its support.
* `PartialDiffeomorph.mfderiv_symm_apply_eq_of_mfderiv_apply_eq`: the inverse of a partial
  diffeomorphism carrying `X` to `Y` carries `Y` to `X` on its target.
* `PartialDiffeomorph.flowOf_eq_symm_flowOf`: the flow of `X` is read off the flow of `Y` while
  the trajectory of `Y` stays in the target.
* `PartialDiffeomorph.eventually_flowOf_eq_symm_flowOf`: the same identity holds near the initial
  point.
* `PartialDiffeomorph.hasMFDerivAt_flowOf`: the derivative of the time-`t` map of `X` is that of
  `Y` conjugated by the differentials of `Φ`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Proposition 9.13 (naturality of flows).
-/

public section

open Filter Function Set
open scoped ContDiff Manifold Topology

namespace PartialDiffeomorph

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

section Transplant

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CompleteSpace E] [T2Space M] [IsManifold I 1 M]

/-- **Transplanting a vector field through a partial diffeomorphism.** Let `Φ` be a `C^n` partial
diffeomorphism from `M` onto an open subset of a normed space `V`, and let `W₀` be a
`C^m` vector field on `V` with compact support in the target of `Φ`, where `m + 1 ≤ n`. Then there
is a `C^m` vector field `W` on `M`, vanishing outside the compact set `Φ⁻¹ (tsupport W₀)`, which
`Φ` carries to `W₀`: `dΦ_x (W x) = W₀ (Φ x)` for `x ∈ Φ.source`. -/
theorem exists_contMDiff_mfderiv_apply_eq {m : ℕ∞ω} (Φ : PartialDiffeomorph I 𝓘(ℝ, V) M V n)
    (hmn : m + 1 ≤ n) {W₀ : V → V} (hW₀ : ContDiff ℝ m W₀) (hc : HasCompactSupport W₀)
    (hsupp : tsupport W₀ ⊆ Φ.target) :
    ∃ W : (x : M) → TangentSpace I x,
      CMDiff m (fun x ↦ (⟨x, W x⟩ : TangentBundle I M)) ∧
        (∀ x ∉ Φ.symm '' tsupport W₀, W x = 0) ∧
        ∀ x ∈ Φ.source, mfderiv I 𝓘(ℝ, V) Φ x (W x) = W₀ (Φ x) := by
  classical
  have hn : n ≠ 0 := ne_bot_of_le_ne_bot (by simp) hmn
  set K := Φ.symm '' tsupport W₀
  have hK : IsCompact K :=
    hc.isCompact.image_of_continuousOn (Φ.symm.contMDiffOn.continuousOn.mono hsupp)
  have hKs : K ⊆ Φ.source := image_subset_iff.2 fun y hy ↦ Φ.map_target (hsupp hy)
  -- Off `K`, the pullback of `W₀` vanishes at the points of the source.
  have hW₀K {x : M} (hx : x ∈ Φ.source) (hxK : x ∉ K) : W₀ (Φ x) = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hxK ⟨Φ x, h, Φ.left_inv hx⟩
  -- The pullback of `W₀`, a field on `M` defined on the source of `Φ`, extended by zero.
  let W₀' : (y : V) → TangentSpace 𝓘(ℝ, V) y := W₀
  let W : (x : M) → TangentSpace I x :=
    fun x ↦ if x ∈ Φ.source then VectorField.mpullback I 𝓘(ℝ, V) Φ W₀' x else 0
  have hWK {x : M} (hxK : x ∉ K) : W x = 0 := by
    by_cases hx : x ∈ Φ.source
    · simp only [W, hx, ↓reduceIte]
      rw [VectorField.mpullback_apply, show W₀' (Φ x) = 0 from hW₀K hx hxK, map_zero]
    · simp only [W, hx, ↓reduceIte]
  refine ⟨W, fun x ↦ ?_, fun x hxK ↦ hWK hxK, fun x hx ↦ ?_⟩
  · by_cases hx : x ∈ Φ.source
    · -- On the source, the field is the pullback of `W₀` by the differentials of `Φ`.
      refine (ContMDiffAt.mpullback_vectorField_preimage
        ((contMDiff_vectorSpace_iff_contDiff.2 hW₀) (Φ x))
        (Φ.contMDiffOn.contMDiffAt (Φ.open_source.mem_nhds hx))
        (Φ.isInvertible_mfderiv hn hx) hmn).congr_of_eventuallyEq ?_
      filter_upwards [Φ.open_source.mem_nhds hx] with z hz
      simp only [W, hz, ↓reduceIte]
      rfl
    · -- Off the source, the field vanishes near `x`, which is not in the compact set `K`.
      refine ((Bundle.contMDiff_zeroSection ℝ (TangentSpace I : M → Type _))
        x).congr_of_eventuallyEq ?_
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds fun h ↦ hx (hKs h)] with z hz
      rw [hWK hz]
      rfl
  · simp only [W, hx, ↓reduceIte]
    rw [VectorField.mpullback_apply]
    exact (Φ.isInvertible_mfderiv hn hx).self_apply_inverse _

end Transplant

section Flow

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  (Φ : PartialDiffeomorph I I' M M' n) (hn : n ≠ 0)
  {X : (x : M) → TangentSpace I x} {Y : (y : M') → TangentSpace I' y}

include hn

/-- If a partial diffeomorphism carries the vector field `X` to `Y` on its source, its inverse
carries `Y` to `X` on its target. -/
theorem mfderiv_symm_apply_eq_of_mfderiv_apply_eq
    (hXY : ∀ x ∈ Φ.source, mfderiv I I' Φ x (X x) = Y (Φ x)) {y : M'} (hy : y ∈ Φ.target) :
    mfderiv I' I Φ.symm y (Y y) = X (Φ.symm y) := by
  obtain ⟨x, hx, rfl⟩ : ∃ x ∈ Φ.source, Φ x = y := ⟨_, Φ.map_target hy, Φ.right_inv hy⟩
  rw [← hXY x hx, Φ.mfderiv_symm_apply_mfderiv_apply hn hx]
  -- The tangent spaces at `x` and at `Φ⁻¹ (Φ x) = x` are both the model space `E`.
  exact congrArg (fun z ↦ (X z : E)) (Φ.left_inv hx).symm

variable [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]
  [T2Space M'] [IsManifold I' 1 M'] [BoundarylessManifold I' M'] [CompleteSpace E']

omit hn in
/-- The pairs `(t, y)` such that the trajectory of `Y` through `y` is defined at time `t` and is
then in an open set `U` form an open set. -/
private theorem isOpen_setOf_mem_flowDomain_and_flowOf_mem
    (hY : CMDiff 1 (fun y ↦ (⟨y, Y y⟩ : TangentBundle I' M'))) {U : Set M'} (hU : IsOpen U) :
    IsOpen {q : ℝ × M' | q ∈ flowDomain Y ∧ flowOf Y q.1 q.2 ∈ U} :=
  ((contMDiffOn_flowOf le_rfl hY).continuousOn.isOpen_inter_preimage (isOpen_flowDomain hY)
    hU)

/-- **The flow read through a partial diffeomorphism.** Let `Φ` carry the `C¹` field `X` to the
`C¹` field `Y` on its source, and let `x ∈ Φ.source`. If the trajectory of `Y` through `Φ x` is
defined up to time `t` and stays in the target of `Φ` for the times between `0` and `t`, then the
flow of `X` is defined at `(t, x)` and `flowOf X t x = Φ⁻¹ (flowOf Y t (Φ x))`. -/
theorem flowOf_eq_symm_flowOf (hX : CMDiff 1 (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)))
    (hY : CMDiff 1 (fun y ↦ (⟨y, Y y⟩ : TangentBundle I' M')))
    (hXY : ∀ x ∈ Φ.source, mfderiv I I' Φ x (X x) = Y (Φ x)) {t : ℝ} {x : M}
    (hx : x ∈ Φ.source) (ht : (t, Φ x) ∈ flowDomain Y)
    (htarget : ∀ s ∈ uIcc 0 t, flowOf Y s (Φ x) ∈ Φ.target) :
    (t, x) ∈ flowDomain X ∧ flowOf X t x = Φ.symm (flowOf Y t (Φ x)) := by
  -- The times at which the trajectory of `Y` is defined and in the target form an open set
  -- containing the compact interval between `0` and `t`, so they contain an open interval
  -- around it.
  set S := {s : ℝ | (s, Φ x) ∈ flowDomain Y ∧ flowOf Y s (Φ x) ∈ Φ.target}
  have hS : IsOpen S := (isOpen_setOf_mem_flowDomain_and_flowOf_mem hY Φ.open_target).preimage
    (continuous_id.prodMk continuous_const)
  have hIcc : uIcc 0 t ⊆ S := fun s hs ↦ ⟨uIcc_subset_setOf_mem_flowDomain ht hs, htarget s hs⟩
  obtain ⟨l, r, ⟨hl, hr⟩, hlr⟩ := mem_nhds_iff_exists_Ioo_subset.1
    (hS.mem_nhds (hIcc ⟨le_rfl, inf_le_sup⟩))
  obtain ⟨l', r', ⟨hl', hr'⟩, hlr'⟩ := mem_nhds_iff_exists_Ioo_subset.1
    (hS.mem_nhds (hIcc ⟨inf_le_sup, le_rfl⟩))
  have hsub : Ioo l r' ⊆ S := fun s hs ↦ by
    rcases lt_or_ge s (min 0 t) with h | h
    · exact hlr ⟨hs.1, h.trans hr⟩
    rcases lt_or_ge (max 0 t) s with h' | h'
    · exact hlr' ⟨hl'.trans h', hs.2⟩
    exact hIcc ⟨h, h'⟩
  have h0 : (0 : ℝ) ∈ Ioo l r' := ⟨hl.trans_le (min_le_left _ _), (le_max_left _ _).trans_lt hr'⟩
  have ht' : t ∈ Ioo l r' := ⟨hl.trans_le (min_le_right _ _), (le_max_right _ _).trans_lt hr'⟩
  -- On that interval, `Φ⁻¹` carries the trajectory of `Y` to an integral curve of `X` through `x`.
  have hγ : IsMIntegralCurveOn (Φ.symm ∘ fun s ↦ flowOf Y s (Φ x)) X (Ioo l r') :=
    ((isMIntegralCurveOn_flowOf hY (Φ x)).mono fun s hs ↦ (hsub hs).1).map_of_mfderiv_eq
      (fun s hs ↦ Φ.symm.mdifferentiableAt hn (hsub hs).2)
      (fun s hs ↦ Φ.mfderiv_symm_apply_eq_of_mfderiv_apply_eq hn hXY (hsub hs).2)
  have hγ0 : (Φ.symm ∘ fun s ↦ flowOf Y s (Φ x)) 0 = x := by
    simp only [comp_apply, flowOf_zero]
    exact Φ.left_inv hx
  refine ⟨mem_flowDomain.mpr (hγ.subset_maximalIntegralCurveInterval h0 hγ0 ht'), ?_⟩
  rw [flowOf_apply]
  exact hγ.eqOn_maximalIntegralCurve hX h0 hγ0 ht'

/-- **The flow read through a partial diffeomorphism, near the initial point.** Under the
hypotheses of `PartialDiffeomorph.flowOf_eq_symm_flowOf` at `x`, the identity
`flowOf X t z = Φ⁻¹ (flowOf Y t (Φ z))` holds for every `z` near `x`, with the flow of `X` defined
at `(t, z)`. -/
theorem eventually_flowOf_eq_symm_flowOf
    (hX : CMDiff 1 (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)))
    (hY : CMDiff 1 (fun y ↦ (⟨y, Y y⟩ : TangentBundle I' M')))
    (hXY : ∀ x ∈ Φ.source, mfderiv I I' Φ x (X x) = Y (Φ x)) {t : ℝ} {x : M}
    (hx : x ∈ Φ.source) (ht : (t, Φ x) ∈ flowDomain Y)
    (htarget : ∀ s ∈ uIcc 0 t, flowOf Y s (Φ x) ∈ Φ.target) :
    ∀ᶠ z in 𝓝 x, (t, z) ∈ flowDomain X ∧ flowOf X t z = Φ.symm (flowOf Y t (Φ z)) := by
  have hO := isOpen_setOf_mem_flowDomain_and_flowOf_mem hY Φ.open_target
  -- By the tube lemma, the trajectories of the points near `Φ x` stay in the target for the
  -- times between `0` and `t`.
  have hev : ∀ᶠ y in 𝓝 (Φ x), ∀ s ∈ uIcc 0 t,
      (s, y) ∈ flowDomain Y ∧ flowOf Y s y ∈ Φ.target :=
    isCompact_uIcc.eventually_forall_of_forall_eventually fun s hs ↦
      (continuous_swap.tendsto (Φ x, s)).eventually
        (hO.mem_nhds ⟨uIcc_subset_setOf_mem_flowDomain ht hs, htarget s hs⟩)
  filter_upwards [(Φ.toOpenPartialHomeomorph.continuousAt hx).eventually hev,
    Φ.open_source.mem_nhds hx] with z hz hzs
  exact Φ.flowOf_eq_symm_flowOf hn hX hY hXY hzs (hz t right_mem_uIcc).1 fun s hs ↦ (hz s hs).2

/-- **The derivative of the flow read through a partial diffeomorphism.** Under the hypotheses of
`PartialDiffeomorph.flowOf_eq_symm_flowOf` at `x`, if the time-`t` map of `Y` has derivative `L` at
`Φ x`, then the time-`t` map of `X` has derivative `dΦ⁻¹ ∘ L ∘ dΦ_x` at `x`. -/
theorem hasMFDerivAt_flowOf (hX : CMDiff 1 (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)))
    (hY : CMDiff 1 (fun y ↦ (⟨y, Y y⟩ : TangentBundle I' M')))
    (hXY : ∀ x ∈ Φ.source, mfderiv I I' Φ x (X x) = Y (Φ x)) {t : ℝ} {x : M}
    (hx : x ∈ Φ.source) (ht : (t, Φ x) ∈ flowDomain Y)
    (htarget : ∀ s ∈ uIcc 0 t, flowOf Y s (Φ x) ∈ Φ.target)
    {L : TangentSpace I' (Φ x) →L[ℝ] TangentSpace I' (flowOf Y t (Φ x))}
    (hL : HasMFDerivAt I' I' (flowOf Y t) (Φ x) L) :
    HasMFDerivAt I I (flowOf X t) x
      ((mfderiv I' I Φ.symm (flowOf Y t (Φ x))).comp (L.comp (mfderiv I I' Φ x))) :=
  ((Φ.symm.mdifferentiableAt hn (htarget t right_mem_uIcc)).hasMFDerivAt.comp x
    (hL.comp x (Φ.mdifferentiableAt hn hx).hasMFDerivAt)).congr_of_eventuallyEq
    ((Φ.eventually_flowOf_eq_symm_flowOf hn hX hY hXY hx ht htarget).mono fun _ hz ↦ hz.2)

end Flow

end PartialDiffeomorph
