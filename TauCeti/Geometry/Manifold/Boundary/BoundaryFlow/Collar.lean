/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.BoundaryFlow.Global
public import TauCeti.Geometry.Manifold.Flow.Basic
public import TauCeti.Geometry.Manifold.IntegralCurve.Interior
import TauCeti.Geometry.Manifold.Boundary.BoundaryFlow.LocalDiffeomorph
import TauCeti.Geometry.Manifold.Boundary.Collar.Local
import TauCeti.Geometry.Manifold.Flow.TimeDependent
import TauCeti.Geometry.Manifold.IntegralCurve.Maximal
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic

/-!
# The backward flow collar of the boundary

Let `M` be a compact smooth Hausdorff manifold modeled on the Euclidean half-space `𝓡∂ (n + 1)`
and `V` a smooth vector field on `M` pointing outward along the whole boundary
(`TauCeti.IsOutwardPointingField`). Its backward flow from the boundary,

`Φ (t, s) = forwardIntegralCurve (-V) s (-t)`, for `t < 0` and `s ∈ ∂M`,

is defined for all negative times, lies in the interior of `M` and is injective
(`TauCeti.IsOutwardPointingField.injOn_forwardIntegralCurve_neg`). This file shows that it is a
diffeomorphism from the open half-cylinder `(-∞, 0) × ∂M` onto an open subset of the interior of
`M` (`TauCeti.IsOutwardPointingField.exists_partialDiffeomorph_backwardFlow`). Here `∂M` carries
the manifold structure of `TauCeti.isManifold_boundary`, modeled on `EuclideanSpace ℝ (Fin n)`, and
the interior carries its charts in `EuclideanSpace ℝ (Fin (n + 1))`
(`ModelWithCorners.instChartedSpaceInterior`), so that source and target are boundaryless. For
every `c < 0`, the part of the interior outside the collar `Φ ((c, 0) × ∂M)` is compact: with the
boundary, the collar is an open subset of `M`, because near a boundary point the forward flow-out
of `∂M × [0, -c)` covers a neighbourhood.

Inside the interior, `Φ` intertwines the flow of the restriction of `V` to the interior with the
translations of the time coordinate: `φ_T (Φ (r, s)) = Φ (r + T, s)` as long as `r + T < 0`
(`TauCeti.IsOutwardPointingField.flowOf_restrictInterior`).

For the Liouville field of a compact Liouville domain `W`, which points outward along `∂W`, `Φ` is
the collar `(-∞, 0) × ∂W ⇀ int W` along which the cylindrical end `[0, ∞) × ∂W` is attached to
`W` in its completion, in the coordinate `t = log r` of the radial coordinate `r`.

The proof is local. Near the boundary, the forward flow-out `(s, u) ↦ forwardIntegralCurve (-V) s u`
of `∂M × [0, ∞)` is a local diffeomorphism at `(a, 0)` for each boundary point `a`
(`TauCeti.isLocalDiffeomorphAt_flowOut_boundary`), hence at `(s, u)` for `(s, u)` near `(a, 0)`.
At such a point with `u > 0`, reading the time coordinate `u = -t` of the half-line in `ℝ` and the
interior of `M` in its own charts (`ModelWithCorners.isLocalDiffeomorph_subtypeVal_interior`) shows
that `Φ` is a local diffeomorphism at `(-u, s)`. A point `(t, s)` far from the boundary is carried
there by the flow of `V` in the interior: near `(t, s)`, `Φ` is the composite of a translation of
the time coordinate, `Φ` near `(-u, s)`, and the time-`(t + u)` map of the flow of `V` in the
interior, which is a local diffeomorphism (`TauCeti.isLocalDiffeomorphAt_flowOf`).

## Main results

* `TauCeti.IsOutwardPointingField.flowOf_restrictInterior`: the backward flow of `V` from any
  point is, at negative times, a trajectory of the restriction of `V` to the interior.
* `TauCeti.IsOutwardPointingField.exists_partialDiffeomorph_backwardFlow`: the backward flow-out
  of the boundary is a diffeomorphism from `(-∞, 0) × ∂M` onto an open subset of the interior,
  outside each collar `(c, 0) × ∂M` of which the interior is compact.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 9.20 (the flow-out theorem) and Theorem 9.25 (flowing the boundary
  inward).
* P. Seidel, *A biased view of symplectic cohomology*, Current Developments in Mathematics 2006,
  Section 2(a) (the collar of a Liouville domain and its completion).
-/

public section

open Filter Function Manifold Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ∞ M]

/-! ### Negative times as depths in the half-line -/

/-- At a negative time `t`, the depth map `u ↦ normalRay (-u)` from `ℝ` to the half-line is a
local diffeomorphism: the normal ray at `-t > 0` composed with negation. -/
private theorem isLocalDiffeomorphAt_normalRay_neg {t : ℝ} (ht : t < 0) :
    IsLocalDiffeomorphAt 𝓘(ℝ) (𝓡∂ 1) ∞ (fun u ↦ EuclideanHalfSpace.normalRay (-u)) t :=
  IsLocalDiffeomorphAt.comp (hf := (ContinuousLinearEquiv.neg ℝ).toDiffeomorph.isLocalDiffeomorph t)
    (hg := EuclideanHalfSpace.isLocalDiffeomorphAt_normalRay (neg_pos.2 ht))

variable [T2Space M] [CompactSpace M]

namespace IsOutwardPointingField

variable {V : (x : M) → TangentSpace (𝓡∂ (n + 1)) x} (hV : IsOutwardPointingField V)
include hV

/-! ### The backward flow in the interior -/

/-- The backward flow of `V` from `x` as a curve in the interior of `M`; its values at nonnegative
times are junk. -/
private noncomputable def backwardFlowInterior (x : M) (t : ℝ) : (𝓡∂ (n + 1)).interior M :=
  if ht : t < 0 then
    ⟨forwardIntegralCurve (-V) x (-t), hV.forwardIntegralCurve_neg_mem_interior x ht⟩
  else ⟨_, hV.forwardIntegralCurve_neg_mem_interior x neg_one_lt_zero⟩

private theorem coe_backwardFlowInterior (x : M) {t : ℝ} (ht : t < 0) :
    (hV.backwardFlowInterior x t : M) = forwardIntegralCurve (-V) x (-t) := by
  simp only [backwardFlowInterior, ht, ↓reduceDIte]

/-- At negative times, the backward flow of `V` is an integral curve of the restriction of `V` to
the interior. -/
private theorem isMIntegralCurveOn_backwardFlowInterior (x : M) :
    IsMIntegralCurveOn (hV.backwardFlowInterior x) ((𝓡∂ (n + 1)).restrictInterior V)
      (Iio 0) :=
  (𝓡∂ (n + 1)).isMIntegralCurveOn_subtypeVal_comp_iff.1
    (((hV.isMIntegralCurveOn_Iic_forwardIntegralCurve_neg x).mono Iio_subset_Iic_self).congr
      fun _ ht ↦ hV.coe_backwardFlowInterior x ht)

/-- Inside the interior, the flow of `V` carries the backward flow at time `r` to the backward
flow at time `r + T`, as long as `r + T < 0`. -/
private theorem flowOf_backwardFlowInterior (x : M) {r T : ℝ} (hr : r < 0) (hrT : r + T < 0) :
    (T, hV.backwardFlowInterior x r) ∈ flowDomain ((𝓡∂ (n + 1)).restrictInterior V) ∧
      flowOf ((𝓡∂ (n + 1)).restrictInterior V) T (hV.backwardFlowInterior x r) =
        hV.backwardFlowInterior x (r + T) := by
  -- The translated backward flow is an integral curve on an open interval containing `0` and `T`.
  have hγ : IsMIntegralCurveOn (hV.backwardFlowInterior x ∘ (· + r))
      ((𝓡∂ (n + 1)).restrictInterior V) (Ioo (min T 0 - 1) (-r)) :=
    ((hV.isMIntegralCurveOn_backwardFlowInterior x).comp_add r).mono fun u hu ↦ by
      simp only [mem_ofPred_eq, mem_Iio]
      linarith [hu.2]
  have h0 : (0 : ℝ) ∈ Ioo (min T 0 - 1) (-r) :=
    ⟨by linarith [min_le_right T 0], by linarith⟩
  have hT : T ∈ Ioo (min T 0 - 1) (-r) := ⟨by linarith [min_le_left T 0], by linarith⟩
  have hγ0 : (hV.backwardFlowInterior x ∘ (· + r)) 0 = hV.backwardFlowInterior x r := by
    simp
  have hW : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).tangent 1 (T% ((𝓡∂ (n + 1)).restrictInterior V)) :=
    ((𝓡∂ (n + 1)).contMDiff_restrictInterior hV.contMDiff).of_le (by simp)
  refine ⟨mem_flowDomain.2 (hγ.subset_maximalIntegralCurveInterval h0 hγ0 hT), ?_⟩
  rw [flowOf_apply, hγ.eqOn_maximalIntegralCurve hW h0 hγ0 hT, comp_apply]
  exact congrArg _ (add_comm T r)

/-- **The backward flow is a trajectory of `V` in the interior.** For an outward-pointing field
`V` on a compact manifold with boundary and any point `x`, the flow of the restriction of `V` to
the interior carries the point `forwardIntegralCurve (-V) x (-r)` of the backward flow at a
negative time `r` to the point at time `r + T`, as long as `r + T < 0`. -/
theorem flowOf_restrictInterior (x : M) {r T : ℝ} (hr : r < 0) (hrT : r + T < 0) :
    (T, (⟨forwardIntegralCurve (-V) x (-r), hV.forwardIntegralCurve_neg_mem_interior x hr⟩ :
        (𝓡∂ (n + 1)).interior M)) ∈ flowDomain ((𝓡∂ (n + 1)).restrictInterior V) ∧
      flowOf ((𝓡∂ (n + 1)).restrictInterior V) T
          ⟨forwardIntegralCurve (-V) x (-r), hV.forwardIntegralCurve_neg_mem_interior x hr⟩ =
        ⟨forwardIntegralCurve (-V) x (-(r + T)),
          hV.forwardIntegralCurve_neg_mem_interior x hrT⟩ := by
  have hx (t : ℝ) (ht : t < 0) : hV.backwardFlowInterior x t =
      ⟨forwardIntegralCurve (-V) x (-t), hV.forwardIntegralCurve_neg_mem_interior x ht⟩ :=
    Subtype.ext (hV.coe_backwardFlowInterior x ht)
  rw [← hx r hr, ← hx (r + T) hrT]
  exact hV.flowOf_backwardFlowInterior x hr hrT

/-! ### The backward flow-out of the boundary as a local diffeomorphism -/

/-- The backward flow-out of the boundary, `(t, s) ↦ forwardIntegralCurve (-V) s (-t)`, as a map
into the interior; its values at nonnegative times are junk. -/
private noncomputable def collarMap (p : ℝ × (𝓡∂ (n + 1)).boundary M) :
    (𝓡∂ (n + 1)).interior M :=
  hV.backwardFlowInterior p.2 p.1

/-- The forward flow-out of the boundary is a local diffeomorphism at every point of the zero
slice. -/
private theorem isLocalDiffeomorphAt_flowOut_zero (a : (𝓡∂ (n + 1)).boundary M) :
    IsLocalDiffeomorphAt ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) ∞
      (fun p : (𝓡∂ (n + 1)).boundary M × EuclideanHalfSpace 1 ↦
        forwardIntegralCurve (-V) p.1 (p.2.val 0)) (a, 0) :=
  isLocalDiffeomorphAt_flowOut_boundary (-V) hV.contMDiff_neg
    (hV.isOutwardPointing_neg_neg a a.property) univ_mem fun x _ _ _ _ ↦
      ⟨forwardIntegralCurve_zero _ _,
        (isMIntegralCurveOn_forwardIntegralCurve_of_isOutwardPointing_neg hV.contMDiff_neg
          hV.isOutwardPointing_neg_neg x).mono Icc_subset_Ici_self⟩

omit [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space M] [CompactSpace M] hV in
/-- At a negative time, the map `(t, s) ↦ (s, depth -t)` from `ℝ × ∂M` to `∂M × [0, ∞)` is a local
diffeomorphism. -/
private theorem isLocalDiffeomorphAt_swap_normalRay_neg {p : ℝ × (𝓡∂ (n + 1)).boundary M}
    (hp : p.1 < 0) :
    IsLocalDiffeomorphAt (𝓘(ℝ).prod (𝓡 n)) ((𝓡 n).prod (𝓡∂ 1)) ∞
      (fun q : ℝ × (𝓡∂ (n + 1)).boundary M ↦ (q.2, EuclideanHalfSpace.normalRay (-q.1))) p :=
  (IsLocalDiffeomorphAt.comp (hf := (isLocalDiffeomorphAt_normalRay_neg hp).prodMap
    ((Diffeomorph.refl (𝓡 n) ((𝓡∂ (n + 1)).boundary M) ∞).isLocalDiffeomorph p.2))
    (hg := (Diffeomorph.prodComm (𝓡∂ 1) (𝓡 n) (EuclideanHalfSpace 1) ((𝓡∂ (n + 1)).boundary M)
      ∞).isLocalDiffeomorph _)).congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl)

/-- **Near the boundary**, the backward flow-out of the boundary is a local diffeomorphism at a
point `(t, s)`, `t < 0`, at which the forward flow-out is a local diffeomorphism. -/
private theorem isLocalDiffeomorphAt_collarMap_of_flowOut {p : ℝ × (𝓡∂ (n + 1)).boundary M}
    (hp : p.1 < 0)
    (hF : IsLocalDiffeomorphAt ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) ∞
      (fun q : (𝓡∂ (n + 1)).boundary M × EuclideanHalfSpace 1 ↦
        forwardIntegralCurve (-V) q.1 (q.2.val 0)) (p.2, EuclideanHalfSpace.normalRay (-p.1))) :
    IsLocalDiffeomorphAt (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞
      hV.collarMap p := by
  -- Read in `M`, the collar map is the forward flow-out composed with `(t, s) ↦ (s, depth -t)`.
  have h : IsLocalDiffeomorphAt (𝓘(ℝ).prod (𝓡 n)) (𝓡∂ (n + 1)) ∞
      (Subtype.val ∘ hV.collarMap) p := by
    refine (IsLocalDiffeomorphAt.comp (hf := isLocalDiffeomorphAt_swap_normalRay_neg hp)
      (hg := hF)).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_Iio.preimage continuous_fst).mem_nhds (hp : p ∈ Prod.fst ⁻¹' Iio 0)]
      with q hq
    simp only [comp_apply, collarMap, EuclideanHalfSpace.normalRay_coe_apply,
      max_eq_left (neg_nonneg.2 (le_of_lt (hq : q.1 < 0))),
      hV.coe_backwardFlowInterior q.2 hq]
  exact h.of_comp_left
    ((𝓡∂ (n + 1)).isLocalDiffeomorph_subtypeVal_interior _)
    (IsInducing.subtypeVal.continuousAt_iff.2 h.contMDiffAt.continuousAt)

/-- **The backward flow-out of the boundary is a local diffeomorphism** at every point `(t, s)`
with `t < 0`. -/
private theorem isLocalDiffeomorphAt_collarMap {p : ℝ × (𝓡∂ (n + 1)).boundary M}
    (hp : p.1 < 0) :
    IsLocalDiffeomorphAt (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞
      hV.collarMap p := by
  -- Choose a time `u ∈ (t, 0)` at which the forward flow-out is a local diffeomorphism.
  have hev : ∀ᶠ u in 𝓝 (0 : ℝ), IsLocalDiffeomorphAt ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) ∞
      (fun q : (𝓡∂ (n + 1)).boundary M × EuclideanHalfSpace 1 ↦
        forwardIntegralCurve (-V) q.1 (q.2.val 0)) (p.2, EuclideanHalfSpace.normalRay (-u)) := by
    have hcont : Continuous fun u : ℝ ↦ (p.2, EuclideanHalfSpace.normalRay (-u)) :=
      continuous_const.prodMk (EuclideanHalfSpace.continuous_normalRay.comp continuous_neg)
    have h := hcont.tendsto 0
    rw [neg_zero, EuclideanHalfSpace.normalRay_zero] at h
    exact h.eventually (hV.isLocalDiffeomorphAt_flowOut_zero p.2).eventually
  obtain ⟨u, hFu, hu⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsLT hp)).exists
  have hcu := hV.isLocalDiffeomorphAt_collarMap_of_flowOut (p := (u, p.2)) hu.2 hFu
  set T := p.1 - u with hTdef
  -- The translation `(t, s) ↦ (t - T, s)` carries `p` to `(u, s)`.
  let τ : ℝ ≃ₘ^∞⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ :=
    { toEquiv := Equiv.subRight T
      contMDiff_toFun := (contDiff_id.sub contDiff_const).contMDiff
      contMDiff_invFun := (contDiff_id.add contDiff_const).contMDiff }
  have hτ (x : ℝ) : τ x = x - T := rfl
  have htr : IsLocalDiffeomorphAt (𝓘(ℝ).prod (𝓡 n)) (𝓘(ℝ).prod (𝓡 n)) ∞
      (Prod.map τ id) p :=
    (τ.isLocalDiffeomorph p.1).prodMap
      ((Diffeomorph.refl (𝓡 n) ((𝓡∂ (n + 1)).boundary M) ∞).isLocalDiffeomorph p.2)
  have hτp : Prod.map τ id p = (u, p.2) :=
    Prod.ext (by rw [Prod.map_fst, hτ, hTdef]; ring) rfl
  rw [← hτp] at hcu
  -- After the translation, flow for time `T` in the interior.
  have hdom : (T, hV.collarMap (Prod.map τ id p)) ∈
      flowDomain ((𝓡∂ (n + 1)).restrictInterior V) := by
    rw [hτp]
    exact (hV.flowOf_backwardFlowInterior p.2 hu.2 (by linarith)).1
  have hflow := isLocalDiffeomorphAt_flowOf (n := ⊤) le_top
    ((𝓡∂ (n + 1)).contMDiff_restrictInterior hV.contMDiff) hdom
  have hpT : p.1 - T < 0 := by simp [hTdef, hu.2]
  refine (IsLocalDiffeomorphAt.comp (hf := htr)
    (hg := IsLocalDiffeomorphAt.comp (hf := hcu) (hg := hflow))).congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_Iio.preimage continuous_fst).mem_nhds (hp : p ∈ Prod.fst ⁻¹' Iio 0),
    (isOpen_Iio.preimage (continuous_fst.sub continuous_const)).mem_nhds
      (hpT : p ∈ (fun q : ℝ × (𝓡∂ (n + 1)).boundary M ↦ q.1 - T) ⁻¹' Iio 0)] with q hq hqT
  have h := hV.flowOf_backwardFlowInterior q.2 (r := q.1 - T) (T := T) hqT
    (by rw [sub_add_cancel]; exact hq)
  rw [sub_add_cancel] at h
  simp only [comp_apply, collarMap, Prod.map_fst, Prod.map_snd, id_eq, hτ]
  exact h.2.symm

/-! ### The backward flow-out of the boundary as a partial diffeomorphism -/

/-- The backward flow-out of the boundary is injective on `(-∞, 0) × ∂M`. -/
private theorem injOn_collarMap : InjOn hV.collarMap (Prod.fst ⁻¹' Iio 0) := by
  intro p hp q hq hpq
  have h := congrArg Subtype.val hpq
  simp only [collarMap, hV.coe_backwardFlowInterior _ (hp : p.1 < 0),
    hV.coe_backwardFlowInterior _ (hq : q.1 < 0)] at h
  have h' := hV.injOn_forwardIntegralCurve_neg (x₁ := ((p.2 : M), p.1))
    ⟨p.2.property, le_of_lt (hp : p.1 < 0)⟩ (x₂ := ((q.2 : M), q.1))
    ⟨q.2.property, le_of_lt (hq : q.1 < 0)⟩ h
  simp only [Prod.mk.injEq] at h'
  exact Prod.ext h'.2 (Subtype.ext h'.1)

/-- For `c < 0`, the boundary together with the collar `(c, 0) × ∂M` is a neighbourhood of each
boundary point: near it, the forward flow-out for times in `[0, -c)` is a diffeomorphism onto a
neighbourhood. -/
private theorem boundary_union_image_collarMap_mem_nhds {c : ℝ} (hc : c < 0) {y : M}
    (hy : y ∈ (𝓡∂ (n + 1)).boundary M) :
    (𝓡∂ (n + 1)).boundary M ∪ Subtype.val '' (hV.collarMap '' (Prod.fst ⁻¹' Ioo c 0)) ∈ 𝓝 y := by
  obtain ⟨Ψ, haΨ, hΨs, hΨ⟩ :=
    (hV.isLocalDiffeomorphAt_flowOut_zero ⟨y, hy⟩).exists_partialDiffeomorph_eqOn
    (s := {q | q.2.val 0 < -c})
    (isOpen_lt ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
      (continuous_subtypeVal.comp continuous_snd)) continuous_const)
    (by simpa using hc)
  have hy' : y ∈ Ψ.target := by
    have h := Ψ.toPartialEquiv.map_source haΨ
    rw [← hΨ haΨ] at h
    simpa using h
  refine mem_of_superset (Ψ.open_target.mem_nhds hy') fun w hw ↦ ?_
  -- A point `w` of the image is reached at the depth `u ∈ [0, -c)` of its preimage.
  set q := Ψ.toPartialEquiv.symm w
  have hq : q ∈ Ψ.source := Ψ.toPartialEquiv.map_target hw
  have hu : q.2.val 0 < -c := hΨs hq
  have hw' : w = forwardIntegralCurve (-V) q.1 (q.2.val 0) :=
    (Ψ.toPartialEquiv.right_inv hw).symm.trans (hΨ hq).symm
  rcases q.2.property.eq_or_lt with hz | hpos
  · left
    rw [hw', ← hz, forwardIntegralCurve_zero]
    exact q.1.property
  · right
    refine ⟨hV.collarMap (-q.2.val 0, q.1), ⟨_, ⟨by linarith, neg_neg_of_pos hpos⟩, rfl⟩, ?_⟩
    rw [collarMap, hV.coe_backwardFlowInterior _ (neg_neg_of_pos hpos), neg_neg]
    exact hw'.symm

/-- For `c < 0`, if the collar `(c, 0) × ∂M` has open image in the interior, the part of the
interior outside it is compact: with the boundary, the collar is an open subset of the compact
manifold `M`. -/
private theorem isCompact_compl_image_collarMap {c : ℝ} (hc : c < 0)
    (hA : IsOpen (hV.collarMap '' (Prod.fst ⁻¹' Ioo c 0))) :
    IsCompact (hV.collarMap '' (Prod.fst ⁻¹' Ioo c 0))ᶜ := by
  set O : Set M := (𝓡∂ (n + 1)).boundary M ∪ Subtype.val '' (hV.collarMap '' (Prod.fst ⁻¹' Ioo c 0))
  have hO : IsOpen O := by
    refine isOpen_iff_mem_nhds.2 fun y hy ↦ ?_
    rcases hy with hy | ⟨z, hz, rfl⟩
    · exact hV.boundary_union_image_collarMap_mem_nhds hc hy
    · exact mem_of_superset
        (((𝓡∂ (n + 1)).isOpen_interior_of_finiteDimensional M).isOpenEmbedding_subtypeVal.isOpenMap
          _ hA |>.mem_nhds ⟨z, hz, rfl⟩) subset_union_right
  have hAO : (hV.collarMap '' (Prod.fst ⁻¹' Ioo c 0))ᶜ = Subtype.val ⁻¹' Oᶜ := by
    ext z
    have hz : (z : M) ∉ (𝓡∂ (n + 1)).boundary M := fun h ↦
      (𝓡∂ (n + 1)).disjoint_interior_boundary.notMem_of_mem_left z.property h
    simp [O, hz]
  rw [hAO]
  refine IsInducing.subtypeVal.isCompact_preimage' hO.isClosed_compl.isCompact fun y hy ↦ ?_
  have hy' : y ∈ ((𝓡∂ (n + 1)).boundary M)ᶜ := fun h ↦ hy (Or.inl h)
  rw [(𝓡∂ (n + 1)).compl_boundary] at hy'
  exact ⟨⟨y, hy'⟩, rfl⟩

/-- **The backward flow collar of the boundary.** Let `V` be a smooth vector field pointing
outward along the boundary of a compact Hausdorff manifold `M` modeled on the half-space, with
nonempty boundary. Then the backward flow-out of the boundary,
`(t, s) ↦ forwardIntegralCurve (-V) s (-t)`, is a diffeomorphism `Φ` from the open half-cylinder
`(-∞, 0) × ∂M` onto an open subset of the interior of `M`. Here `∂M` and the interior of `M` are
boundaryless manifolds, modeled on `EuclideanSpace ℝ (Fin n)` and `EuclideanSpace ℝ (Fin (n + 1))`.
For every `c < 0`, the part of the interior outside the collar `Φ ((c, 0) × ∂M)` is compact. -/
theorem exists_partialDiffeomorph_backwardFlow [Nonempty ((𝓡∂ (n + 1)).boundary M)] :
    ∃ Φ : PartialDiffeomorph (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        (ℝ × (𝓡∂ (n + 1)).boundary M) ((𝓡∂ (n + 1)).interior M) ∞,
      Φ.source = Prod.fst ⁻¹' Iio 0 ∧
        (∀ p ∈ Φ.source, (Φ p : M) = forwardIntegralCurve (-V) p.2 (-p.1)) ∧
        ∀ c < 0, IsCompact (Φ '' (Prod.fst ⁻¹' Ioo c 0))ᶜ := by
  have hloc : IsLocalDiffeomorphOn (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞
      hV.collarMap (Prod.fst ⁻¹' Iio 0) := fun p ↦
    hV.isLocalDiffeomorphAt_collarMap p.property
  have hs : IsOpen (Prod.fst ⁻¹' Iio (0 : ℝ) : Set (ℝ × (𝓡∂ (n + 1)).boundary M)) :=
    isOpen_Iio.preimage continuous_fst
  set Φ := hloc.partialDiffeomorphOfInjOn hs hV.injOn_collarMap
  have hsrc : Φ.source = Prod.fst ⁻¹' Iio 0 :=
    hloc.partialDiffeomorphOfInjOn_source hs hV.injOn_collarMap
  have hcoe : ⇑Φ = hV.collarMap := hloc.coe_partialDiffeomorphOfInjOn hs hV.injOn_collarMap
  refine ⟨Φ, hsrc, fun p hp ↦ ?_, fun c hc ↦ ?_⟩
  · rw [hsrc] at hp
    rw [hcoe]
    exact hV.coe_backwardFlowInterior p.2 hp
  · have hsub : Prod.fst ⁻¹' Ioo c 0 ⊆ Φ.toOpenPartialHomeomorph.source := by
      rw [PartialDiffeomorph.toOpenPartialHomeomorph_source, hsrc]
      exact fun p hp ↦ hp.2
    have hA := Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      (isOpen_Ioo.preimage continuous_fst) hsub
    rw [PartialDiffeomorph.toFun'_toOpenPartialHomeomorph, hcoe] at hA
    rw [hcoe]
    exact hV.isCompact_compl_image_collarMap hc hA

end IsOutwardPointingField

end TauCeti
