/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import TauCeti.Geometry.Manifold.Instances.Icc
public import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Tangent-bundle trivializations, coordinate changes on `T(TM)`, and open submanifolds

The canonical tangent-bundle trivialization at a point `x` is built from the chart at `x`, so on
the fibre over `x` itself it is the identity.  This file records that fact in both directions, and
notes that reading a tangent vector through the preferred trivializations of two charts is the
tangent coordinate change between them, which is `C^n` in the base point.

It then computes the coordinate changes of the tangent bundle of the tangent bundle: a tangent
vector `(u, w)` to `TM` at a point with `x`-coordinates `u`, read in the tangent-bundle chart
centred at the zero vector over `x₀`, has base component the tangent coordinate change of `u`, and
fibre component the product-rule sum of the derivative of that coordinate change in the base point
and the coordinate change applied to `w`.  This is the transformation law obeyed by a second-order
vector field on `TM`, such as a geodesic spray, when it is carried between tangent-bundle charts.

It then identifies the tangent spaces of an open submanifold with those of its ambient manifold
and shows that, near each point, the inverse tangent-bundle trivializations agree under that
identification.

It then identifies the tangent space of a product manifold with the product of the tangent
spaces of the factors, and shows that under this identification tangent coordinate changes and
inverse tangent-bundle trivializations act componentwise. Finally, the charts of a disjoint union
are those of its summands, so its tangent coordinate changes are those of the summands.

## Main results

* `TauCeti.Manifold.mfderiv_atlas_eq_continuousLinearMapAt`: the derivative of an atlas chart
  is the actual continuous linear map of its tangent-core trivialization.
* `TauCeti.Manifold.continuousLinearMapAt_trivializationAt_self` and
  `TauCeti.Manifold.symmL_trivializationAt_self`: the canonical trivialization at `x` and its
  inverse act as the identity on the fibre over `x`.
* `TauCeti.Manifold.localFrame_trivializationAt_self`: consequently its local frame at `x` is the
  chosen basis of the model space.
* `TauCeti.Manifold.inverse_mfderiv_extChartAt`: the inverse of the differential of an extended
  chart is the inverse of the canonical tangent-bundle trivialization at its centre.
* `TauCeti.Manifold.contDiffOn_tangentCoordChange`: the tangent coordinate change between the
  charts at two points is `C^n` on the overlap of their sources, read in the chart at the first
  point.
* `TauCeti.Manifold.contMDiffAt_tangentCoordChange`: that coordinate change is `C^n` at the base
  point of its first chart, as a map of manifolds into the linear endomorphisms of the model
  space.
* `TauCeti.Manifold.tangentCoordChange_tangent_apply`: the coordinate-change formula on the
  tangent bundle of the tangent bundle.
* `TauCeti.Manifold.continuousLinearMapAt_symmL_coordChange`: reading a tangent vector through the
  preferred trivializations of two charts is the tangent coordinate change between them.
* `TauCeti.Manifold.tangentCoordChange_toMatrix`: in a finite basis, this coordinate change is the
  change-of-basis matrix between the corresponding chart-local frames.
* `TauCeti.Manifold.tangentSpaceOpenEquiv`: the canonical continuous linear equivalence between
  the tangent space of an open submanifold and the ambient tangent space.
* `TauCeti.Manifold.mfderiv_subtype_val`: the differential of the inclusion is the canonical
  tangent-space equivalence.
* `TauCeti.Manifold.tangentMap_subtype_val`: the tangent map of the inclusion under this
  equivalence.
* `TauCeti.Manifold.tangentSpaceOpenEquiv_mfderiv_apply`: under this equivalence, the differential
  of a map between open submanifolds is that of any ambient map it restricts.
* `TauCeti.Manifold.instT2SpaceTangentBundleModelSpace`: a model space has a Hausdorff tangent
  bundle. It is an instance in the `TauCeti` scope, for model spaces `H` whose Hausdorffness is
  not already an instance; over a Hausdorff manifold the tangent bundle is Hausdorff by the general
  instance `TauCeti.FiberBundle.t2Space_totalSpace`.
* `TauCeti.Manifold.eventually_tangentSpaceOpenEquiv_symmL_trivializationAt_eq`: near a point, the
  inverse tangent-bundle trivializations agree through this equivalence.
* `TauCeti.Manifold.restrictOpenTangentSpaceBilin`: the restriction of a field of bilinear maps on
  the tangent spaces to an open submanifold, and
  `TauCeti.Manifold.contMDiffAt_restrictOpenTangentSpaceBilin`: restriction preserves `C^n`
  regularity.
* `TauCeti.Manifold.tangentSpaceProdEquiv`: the canonical continuous linear equivalence between
  the tangent space of a product and the product of the tangent spaces.
* `TauCeti.Manifold.mfderiv_prodMap_apply`: differentials of product maps act componentwise
  under this equivalence.
* `TauCeti.Manifold.isInvertible_mfderiv_prodMap`: the differential of a product map is invertible
  where the differentials of both factors are.
* `TauCeti.Manifold.tangentSpaceProdEquiv_mfderiv_prodMap_id` and
  `TauCeti.Manifold.isInvertible_mfderiv_prodMap_id`: the differential of `(x, t) ↦ (x, φ t)` on
  `M × 𝕜` multiplies the `𝕜`-component by `φ' t`, so it is invertible where `φ' t ≠ 0`.
* `TauCeti.Manifold.isInvertible_mfderiv_prodMap_id_subtypeVal_Icc`: the differential of the
  inclusion `M × [a, b] → M × ℝ` is invertible, also at the boundary.
* `TauCeti.Manifold.tangentCoordChange_prod`: the tangent coordinate change of a product is the
  product of the tangent coordinate changes of the factors.
* `TauCeti.Manifold.tangentSpaceProdEquiv_symmL_trivializationAt`: the inverse tangent-bundle
  trivialization of a product is the product of those of the factors.
* `TauCeti.Manifold.tangentCoordChange_sumInl` and `TauCeti.Manifold.tangentCoordChange_sumInr`:
  the tangent coordinate changes of a disjoint union between charts at points of one summand are
  those of that summand.
* `TauCeti.Manifold.symmL_trivializationAt_sumInl` and
  `TauCeti.Manifold.symmL_trivializationAt_sumInr`: so are its inverse tangent-bundle
  trivializations.
-/

public section

open Bundle Filter Manifold Module Set TopologicalSpace
open scoped Bundle Manifold Topology ContDiff

noncomputable section

namespace TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section BasePoint

variable [IsManifold I 1 M]

/-- The derivative of an atlas chart reads tangent vectors in that chart's core trivialization. -/
theorem mfderiv_atlas_eq_continuousLinearMapAt (e : atlas H M) {x : M}
    (hx : x ∈ e.val.source) :
    mfderiv I I e.val x =
      ((tangentBundleCore I M).localTriv e).continuousLinearMapAt 𝕜 x := by
  rw [(tangentBundleCore I M).localTriv_continuousLinearMapAt hx,
    (mdifferentiableAt_atlas e.property hx).mfderiv]
  simp only [writtenInExtChartAt, extChartAt_self_eq]
  rw [tangentBundleCore_coordChange, tangentBundleCore_indexAt, achart_val]
  simp only [extChartAt, OpenPartialHomeomorph.extend_coe, Function.comp_assoc]
  -- At this foundational bridge, both implementation casts identify the tangent fibre with E.
  ext v
  simp only [ContinuousLinearMap.comp_apply, tangentSpaceCastModel]
  rfl


/-- Read in the canonical trivialization at `x`, a tangent vector at `x` itself is its own
coordinate vector: the trivialization is built from the chart at `x`, whose transition function
with itself has derivative the identity. -/
@[simp]
theorem continuousLinearMapAt_trivializationAt_self (x : M) (v : TangentSpace I x) :
    (trivializationAt E (TangentSpace I) x).continuousLinearMapAt 𝕜 x v = v := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (mem_chart_source H x)]
  exact (tangentBundleCore I M).coordChange_self (achart H x) x (mem_chart_source H x) v

/-- The inverse form of `TauCeti.Manifold.continuousLinearMapAt_trivializationAt_self`: over its
own base point, the inverse of the canonical trivialization is the identity. -/
@[simp]
theorem symmL_trivializationAt_self (x : M) (v : E) :
    (trivializationAt E (TangentSpace I) x).symmL 𝕜 x v = v := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source H x)]
  exact (tangentBundleCore I M).coordChange_self (achart H x) x (mem_chart_source H x) v

/-- The differential of the extended chart at `x₀`, at a point `x` of its source, is inverted by
the inverse of the canonical tangent-bundle trivialization at `x₀`.  This is the inverse form of
`TangentBundle.symmL_trivializationAt`. -/
theorem inverse_mfderiv_extChartAt (x₀ : M) {x : M} (hx : x ∈ (extChartAt I x₀).source) :
    (mfderiv% (extChartAt I x₀) x).inverse =
      (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x := by
  rw [ContinuousLinearMap.inverse_eq
    (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' hx)
    (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hx),
    ← TangentBundle.symmL_trivializationAt (by simpa using hx)]

end BasePoint

section TangentChart

section TangentBundleChart

variable [IsManifold I 1 M]

namespace TangentBundle

/-- The second component of the chart of a tangent bundle at `q`, read at a point with base point
in the chart source.  Together with `TangentBundle.coe_chartAt_fst` this describes the
tangent-bundle charts completely. -/
@[simp, mfld_simps]
theorem coe_chartAt_snd {p q : TangentBundle I M} :
    (chartAt (ModelProd H E) q p).2 =
      tangentCoordChange I p.1 q.1 p.1 p.2 := by
  -- After unfolding the tangent-bundle chart, the fibre-to-model-space conversion is
  -- definitionally the tangent coordinate change; no separate conversion lemma is needed.
  rw [TangentBundle.chartAt]
  rfl

end TangentBundle

end TangentBundleChart

/-- The tangent coordinate change between the charts at `x` and `y` is `C^n` on the overlap of
the two chart sources, read in the chart at `x`.  This is Mathlib's
`contDiffOn_fderiv_coord_change` for the preferred charts at two points. -/
theorem contDiffOn_tangentCoordChange {n : ℕ∞ω} [IsManifold I (n + 1) M] (x y : M) :
    haveI : IsManifold I 1 M := IsManifold.of_le (n := n + 1) le_add_self
    ContDiffOn 𝕜 n (fun a : E => tangentCoordChange I x y ((extChartAt I x).symm a))
      (((extChartAt I x).symm ≫ extChartAt I y).source) := by
  have _ : IsManifold I 1 M := IsManifold.of_le (n := n + 1) le_add_self
  refine (contDiffOn_fderiv_coord_change (𝕜 := 𝕜) (n := n) (I := I) (M := M)
    (achart H x) (achart H y)).congr (fun a ha => ?_)
  have ha2 : a ∈ (extChartAt I x).target := by
    rw [PartialEquiv.trans_source] at ha
    exact ha.1
  rw [tangentCoordChange_def, (extChartAt I x).right_inv ha2]
  rfl

/-- The tangent coordinate change between the charts at `x` and `y` is `C^n` at `x`, as a map of
manifolds into the continuous linear endomorphisms of the model space. -/
theorem contMDiffAt_tangentCoordChange {n : ℕ∞ω} [IsManifold I (n + 1) M] {x y : M}
    (hy : x ∈ (extChartAt I y).source) :
    haveI : IsManifold I 1 M := IsManifold.of_le (n := n + 1) le_add_self
    ContMDiffAt I 𝓘(𝕜, E →L[𝕜] E) n (tangentCoordChange I x y) x := by
  have hI : IsManifold I 1 M := IsManifold.of_le (n := n + 1) le_add_self
  rw [contMDiffAt_iff]
  refine ⟨?_, ?_⟩
  · refine (continuousOn_tangentCoordChange (I := I) (𝕜 := 𝕜) x y).continuousAt ?_
    exact Filter.inter_mem (extChartAt_source_mem_nhds (I := I) (x := x))
      ((isOpen_extChartAt_source y).mem_nhds hy)
  · have hmem : extChartAt I x x ∈ ((extChartAt I x).symm ≫ extChartAt I y).source := by
      rw [PartialEquiv.trans_source'', PartialEquiv.symm_symm, PartialEquiv.symm_target]
      exact mem_image_of_mem _ ⟨mem_extChartAt_source x, hy⟩
    have hychart : x ∈ (chartAt H y).source := by
      rw [← OpenPartialHomeomorph.extend_source (f := chartAt H y) (I := I)]
      exact hy
    have hset : ((extChartAt I x).symm ≫ extChartAt I y).source
        ∈ nhdsWithin (extChartAt I x x) (range I) :=
      I.extendCoordChange_source_mem_nhdsWithin' (e := chartAt H x) (e' := chartAt H y)
        (ChartedSpace.mem_chart_source x) hychart
    refine ((contDiffOn_tangentCoordChange (I := I) (𝕜 := 𝕜) x y).contDiffWithinAt
      hmem).mono_of_mem_nhdsWithin hset

/-! ### Coordinate changes on the tangent of the tangent bundle -/

private theorem tangentCoordChange_tangent_eventuallyEq [IsManifold I 1 M] {x x₀ : M}
    (hx₀ : x ∈ (extChartAt I x₀).source) (u : E) :
    ((extChartAt I.tangent (TotalSpace.mk' E x₀ 0) : TangentBundle I M → E × E) ∘
        (extChartAt I.tangent (TotalSpace.mk' E x
          ((trivializationAt E (TangentSpace I) x).symmL 𝕜 x u))).symm) =ᶠ[nhdsWithin
          (extChartAt I.tangent
            (TotalSpace.mk' E x ((trivializationAt E (TangentSpace I) x).symmL 𝕜 x u))
            (TotalSpace.mk' E x ((trivializationAt E (TangentSpace I) x).symmL 𝕜 x u)))
            (range I.tangent)]
      fun a ↦
        let y := (extChartAt I x).symm a.1
        (extChartAt I x₀ y, tangentCoordChange I x x₀ y a.2) := by
  let z : TangentBundle I M :=
    TotalSpace.mk' E x ((trivializationAt E (TangentSpace I) x).symmL 𝕜 x u)
  let q : TangentBundle I M := TotalSpace.mk' E x₀ 0
  let p := extChartAt I.tangent z z
  let G := (extChartAt I.tangent q : TangentBundle I M → E × E) ∘
    (extChartAt I.tangent z).symm
  let T : E × E → E × E := fun a ↦
    let y := (extChartAt I x).symm a.1
    (extChartAt I x₀ y, tangentCoordChange I x x₀ y a.2)
  -- There is no rewriting lemma that folds the four local abbreviations in this `EventuallyEq`;
  -- expose their definitional expansion so the chart-source argument can use the shorter names.
  change G =ᶠ[nhdsWithin p (range I.tangent)] T
  have hz : z ∈ (chartAt (ModelProd H E) z).source := mem_chart_source _ _
  have hzq : z ∈ (chartAt (ModelProd H E) q).source := by
    rw [TangentBundle.mem_chart_source_iff (I := I) (M := M)]
    rw [← extChartAt_source I x₀]
    exact hx₀
  have hN := (I.tangent.extendCoordChange_source_mem_nhdsWithin'
    (e := chartAt (ModelProd H E) z) (e' := chartAt (ModelProd H E) q) hz hzq)
  filter_upwards [hN] with a ha
  -- Membership in the extended coordinate-change source supplies membership in both tangent
  -- charts; unfold that source once to name the corresponding total-space point `b`.
  change a ∈ ((extChartAt I.tangent z).symm ≫ extChartAt I.tangent q).source at ha
  let b := (extChartAt I.tangent z).symm a
  have ha_target : a ∈ (extChartAt I.tangent z).target := ha.1
  have hbzT : b ∈ (extChartAt I.tangent z).source :=
    (extChartAt I.tangent z).map_target ha_target
  have hbqT : b ∈ (extChartAt I.tangent q).source := ha.2
  have hbz : b.proj ∈ (extChartAt I x).source := by
    rw [extChartAt_source] at hbzT ⊢
    exact (TangentBundle.mem_chart_source_iff b z).1 hbzT
  have hbq : b.proj ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source] at hbqT ⊢
    exact (TangentBundle.mem_chart_source_iff b q).1 hbqT
  have hright : extChartAt I.tangent z b = a :=
    (extChartAt I.tangent z).right_inv ha_target
  -- A tangent-bundle chart is a product of the base chart and the fibre coordinate change.
  -- Projecting `hright` exposes those two definitional components.
  have hbase : extChartAt I x b.proj = a.1 := by
    have h := congrArg Prod.fst hright
    change extChartAt I x b.proj = a.1 at h
    exact h
  have hfiber : tangentCoordChange I b.proj x b.proj b.2 = a.2 := by
    have h := congrArg Prod.snd hright
    change tangentCoordChange I b.proj x b.proj b.2 = a.2 at h
    exact h
  have hy : (extChartAt I x).symm a.1 = b.proj := by
    rw [← hbase]
    exact (extChartAt I x).left_inv hbz
  have hsecond : (extChartAt I.tangent q b).2 =
      tangentCoordChange I x x₀ b.proj a.2 := by
    rw [← hfiber]
    have hcomp := tangentCoordChange_comp (I := I) (w := b.proj) (x := x)
      (y := x₀) (z := b.proj) (v := b.2)
      ⟨⟨mem_extChartAt_source b.proj, hbz⟩, hbq⟩
    -- The domain and codomain tangent spaces are modelled by `E`; expose that representation to
    -- apply the coordinate-change composition theorem.
    change tangentCoordChange I b.proj x₀ b.proj b.2 = _
    exact hcomp.symm
  -- Unfold the local names and compare the two product coordinates separately.
  change extChartAt I.tangent q b = T a
  apply Prod.ext
  · change extChartAt I x₀ b.proj = extChartAt I x₀ ((extChartAt I x).symm a.1)
    rw [hy]
  · change (extChartAt I.tangent q b).2 =
      tangentCoordChange I x x₀ ((extChartAt I x).symm a.1) a.2
    simpa only [hy] using hsecond

private theorem fderivWithin_tangentCoordChange_tangent_model [IsManifold I 2 M] {x x₀ : M}
    (hx₀ : x ∈ (extChartAt I x₀).source) (u w : E) :
    (fderivWithin 𝕜 (fun a : E × E ↦
        (extChartAt I x₀ ((extChartAt I x).symm a.1),
          tangentCoordChange I x x₀ ((extChartAt I x).symm a.1) a.2))
      (range I ×ˢ univ) (extChartAt I x x, u)) (u, w) =
      (tangentCoordChange I x x₀ x u,
        mvfderiv I (fun y ↦ tangentCoordChange I x x₀ y u) x
            ((trivializationAt E (TangentSpace I) x).symmL 𝕜 x u) +
          tangentCoordChange I x x₀ x w) := by
  let a₀ := extChartAt I x x
  let F : E → E := fun a ↦ extChartAt I x₀ ((extChartAt I x).symm a)
  let C : E → E →L[𝕜] E := fun a ↦ tangentCoordChange I x x₀ ((extChartAt I x).symm a)
  have ha₀ : a₀ ∈ ((extChartAt I x).symm ≫ extChartAt I x₀).source := by
    rw [PartialEquiv.trans_source]
    exact ⟨(extChartAt I x).map_source (mem_extChartAt_source x), by
      -- `PartialEquiv.trans_source` leaves this as preimage membership; there is no chart lemma
      -- rewriting that wrapper, so expose its defining application before using
      -- `extChartAt_to_inv`.
      change (extChartAt I x).symm a₀ ∈ (extChartAt I x₀).source
      simpa only [a₀, extChartAt_to_inv] using hx₀⟩
  have hF : DifferentiableWithinAt 𝕜 F (range I) a₀ :=
    (contDiffWithinAt_ext_coord_change x₀ x ha₀).differentiableWithinAt
      (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  -- Normalize `2` to the `1 + 1` instance expected by `contMDiffAt_tangentCoordChange` below.
  let hI₂ : IsManifold I (1 + 1) M := inferInstanceAs (IsManifold I 2 M)
  have hCMD : MDifferentiableAt I 𝓘(𝕜, E →L[𝕜] E)
      (tangentCoordChange I x x₀) x :=
    (@contMDiffAt_tangentCoordChange 𝕜 _ E _ _ H _ I M _ _ 1 hI₂ x x₀ hx₀).mdifferentiableAt
      one_ne_zero
  have hC : DifferentiableWithinAt 𝕜 C (range I) a₀ := by
    have h := (mdifferentiableAt_iff (tangentCoordChange I x x₀) x).1 hCMD |>.2
    simp only [writtenInExtChartAt, extChartAt_model_space_eq_id,
      PartialEquiv.refl_coe] at h
    -- With a model-space target, `writtenInExtChartAt` reduces to `C`; expose that reduction so
    -- the ordinary differentiability statement can be reused below.
    change DifferentiableWithinAt 𝕜 C (range I) a₀ at h
    exact h
  have hmaps : MapsTo (Prod.fst : E × E → E) (range I ×ˢ univ) (range I) :=
    fun _ h ↦ h.1
  have huniqBase : UniqueDiffWithinAt 𝕜 (range I) a₀ := I.uniqueDiffWithinAt_image
  have huniq : UniqueDiffWithinAt 𝕜 (range I ×ˢ univ) (a₀, u) :=
    huniqBase.prod uniqueDiffWithinAt_univ
  -- The calculus lemmas below are stated for explicit compositions with the two projections.
  -- The `change` steps only eta-expand those compositions and their derivatives.
  have hFp : DifferentiableWithinAt 𝕜 (fun a : E × E ↦ F a.1)
      (range I ×ˢ univ) (a₀, u) := by
    change DifferentiableWithinAt 𝕜 (F ∘ Prod.fst) (range I ×ˢ univ) (a₀, u)
    exact hF.comp (a₀, u) differentiableWithinAt_fst hmaps
  have hCp : DifferentiableWithinAt 𝕜 (fun a : E × E ↦ C a.1)
      (range I ×ˢ univ) (a₀, u) := by
    change DifferentiableWithinAt 𝕜 (C ∘ Prod.fst) (range I ×ˢ univ) (a₀, u)
    exact hC.comp (a₀, u) differentiableWithinAt_fst hmaps
  have hAp : DifferentiableWithinAt 𝕜 (fun a : E × E ↦ C a.1 a.2)
      (range I ×ˢ univ) (a₀, u) :=
    hCp.clm_apply differentiableWithinAt_snd
  change (fderivWithin 𝕜 (fun a : E × E ↦ (F a.1, C a.1 a.2))
    (range I ×ˢ univ) (a₀, u)) (u, w) = _
  have hFp_eq := fderivWithin_comp (a₀, u) hF differentiableWithinAt_fst hmaps huniq
  change fderivWithin 𝕜 (fun a : E × E ↦ F a.1) (range I ×ˢ univ) (a₀, u) = _ at hFp_eq
  have hCp_eq := fderivWithin_comp (a₀, u) hC differentiableWithinAt_fst hmaps huniq
  change fderivWithin 𝕜 (fun a : E × E ↦ C a.1) (range I ×ˢ univ) (a₀, u) = _ at hCp_eq
  have hAp_eq := fderivWithin_clm_apply huniq hCp differentiableWithinAt_snd
  change fderivWithin 𝕜 (fun a : E × E ↦ C a.1 a.2) (range I ×ˢ univ) (a₀, u) = _ at hAp_eq
  have hfst_app : (fderivWithin 𝕜 (Prod.fst : E × E → E) (range I ×ˢ univ) (a₀, u))
      (u, w) = u := by
    rw [fderivWithin_fst huniq]
    rfl
  have hsnd_app : (fderivWithin 𝕜 (Prod.snd : E × E → E) (range I ×ˢ univ) (a₀, u))
      (u, w) = w := by
    rw [fderivWithin_snd huniq]
    rfl
  rw [hFp.fderivWithin_prodMk hAp huniq, ContinuousLinearMap.prod_apply, hFp_eq,
    hAp_eq, hCp_eq]
  simp only [ContinuousLinearMap.comp_apply, add_apply,
    ContinuousLinearMap.flip_apply, C, F, a₀, extChartAt_to_inv]
  rw [hfst_app, hsnd_app, add_comm]
  have hFderiv : fderivWithin 𝕜 F (range I) a₀ = tangentCoordChange I x x₀ x := by
    rw [tangentCoordChange_def]
    rfl
  rw [hFderiv]
  have hMDu : MDifferentiableAt I 𝓘(𝕜, E)
      (fun y ↦ tangentCoordChange I x x₀ y u) x :=
    hCMD.clm_apply mdifferentiableAt_const
  have hCuDeriv := fderivWithin_clm_apply huniqBase hC
    (differentiableWithinAt_const (c := u))
  have hCuDerivApp := congrArg (fun L : E →L[𝕜] E ↦ L u) hCuDeriv
  have hMv : mvfderiv I (fun y ↦ tangentCoordChange I x x₀ y u) x
      ((trivializationAt E (TangentSpace I) x).symmL 𝕜 x u) =
      fderivWithin 𝕜 C (range I) a₀ u u := by
    rw [hMDu.mvfderiv, symmL_trivializationAt_self]
    -- The manifold derivative is now the derivative of the model-space function `a ↦ C a u`.
    change fderivWithin 𝕜 (fun a ↦ C a u) (range I) a₀ u = _
    simpa [fderivWithin_const_apply] using hCuDerivApp
  rw [hMv]

/-- The tangent coordinate change on `TM` sends the tangent vector `(v, w)` at `u ∈ TₓM` to the
derivative of the base coordinate change together with the product-rule expression for the fibre
coordinate, where `v` is the coordinate of `u` in the preferred trivialization at `x`. The target
chart is centred at the zero vector over `x₀`. -/
theorem tangentCoordChange_tangent_apply [IsManifold I 2 M] {x x₀ : M}
    (hx₀ : x ∈ (extChartAt I x₀).source) (u : TangentSpace I x) (w : E) :
    let v := (trivializationAt E (TangentSpace I) x).continuousLinearMapAt 𝕜 x u
    tangentCoordChange I.tangent
        (TotalSpace.mk' E x u)
        (TotalSpace.mk' E x₀ 0)
        (TotalSpace.mk' E x u) (v, w) =
      (tangentCoordChange I x x₀ x v,
        mvfderiv I (fun y ↦ tangentCoordChange I x x₀ y v) x u +
          tangentCoordChange I x x₀ x w) := by
  dsimp only
  let v : E := (trivializationAt E (TangentSpace I) x).continuousLinearMapAt 𝕜 x u
  -- Fold the repeated preferred-chart reading of `u` into the local model coordinate `v`.
  change tangentCoordChange I.tangent (TotalSpace.mk' E x u) (TotalSpace.mk' E x₀ 0)
      (TotalSpace.mk' E x u) (v, w) =
    (tangentCoordChange I x x₀ x v,
      mvfderiv I (fun y ↦ tangentCoordChange I x x₀ y v) x u +
        tangentCoordChange I x x₀ x w)
  have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x
  have huv : (trivializationAt E (TangentSpace I) x).symmL 𝕜 x v = u :=
    (trivializationAt E (TangentSpace I) x).symmL_continuousLinearMapAt hx u
  rw [← huv]
  let z : TangentBundle I M :=
    TotalSpace.mk' E x ((trivializationAt E (TangentSpace I) x).symmL 𝕜 x v)
  let q : TangentBundle I M := TotalSpace.mk' E x₀ 0
  let p := extChartAt I.tangent z z
  let G := (extChartAt I.tangent q : TangentBundle I M → E × E) ∘
    (extChartAt I.tangent z).symm
  let T : E × E → E × E := fun a ↦
    let y := (extChartAt I x).symm a.1
    (extChartAt I x₀ y, tangentCoordChange I x x₀ y a.2)
  have hGT : G =ᶠ[nhdsWithin p (range I.tangent)] T := by
    simpa only [z, q, p, G, T] using
      tangentCoordChange_tangent_eventuallyEq (I := I) (M := M) hx₀ v
  rw [tangentCoordChange_def]
  -- By definition, a tangent coordinate change is the derivative of the extended chart change.
  change fderivWithin 𝕜 G (range I.tangent) p (v, w) = _
  have hp_mem : p ∈ range I.tangent :=
    (extChartAt_target_subset_range z) ((extChartAt I.tangent z).map_source
      (mem_extChartAt_source z))
  rw [hGT.fderivWithin_eq (hGT.self_of_nhdsWithin hp_mem)]
  have hpcoord : p = (extChartAt I x x, v) := by
    apply Prod.ext
    · rfl
    · change tangentCoordChange I x x x
          ((trivializationAt E (TangentSpace I) x).symmL 𝕜 x v) = v
      rw [symmL_trivializationAt_self]
      exact tangentCoordChange_self (I := I) (M := M) (mem_extChartAt_source x)
  rw [hpcoord, ModelWithCorners.range_prod, ModelWithCorners.range_eq_univ 𝓘(𝕜, E)]
  exact fderivWithin_tangentCoordChange_tangent_model hx₀ v w

section TangentReading

variable [IsManifold I 1 M]

/-- The reading map of the preferred trivialization centred at `x₀` sends the tangent vector at
`y` whose `x`-coordinates are `u` to its `x₀`-coordinates. -/
theorem continuousLinearMapAt_symmL_coordChange {x x₀ y : M}
    (hyx : y ∈ (chartAt H x).source) (hyx₀ : y ∈ (chartAt H x₀).source) (u : E) :
    (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 y
        ((trivializationAt E (TangentSpace I) x).symmL 𝕜 y u)
      = tangentCoordChange I x x₀ y u := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (I := I) (b₀ := x) (b := y) hyx,
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (I := I) (b₀ := x₀) (b := y)
      hyx₀]
  simp only [tangentBundleCore_coordChange_achart]
  have hy1 : y ∈ (extChartAt I x).source := by rw [extChartAt_source]; exact hyx
  have hy2 : y ∈ (extChartAt I y).source := by
    rw [extChartAt_source]
    exact mem_chart_source H y
  have hy3 : y ∈ (extChartAt I x₀).source := by rw [extChartAt_source]; exact hyx₀
  exact tangentCoordChange_comp (I := I) (w := x) (x := y) (y := x₀) (z := y) (v := u)
    ⟨⟨hy1, hy2⟩, hy3⟩

/-- The matrix of a tangent coordinate change in a finite basis of the model space is the
change-of-basis matrix between the corresponding chart-local frames. -/
theorem tangentCoordChange_toMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (α β : M)
    (b : Basis ι 𝕜 E) {x : M}
    (hα : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hβ : x ∈ (trivializationAt E (TangentSpace I) β).baseSet) :
    LinearMap.toMatrix b b (tangentCoordChange I α β x).toLinearMap =
      ((trivializationAt E (TangentSpace I) β).basisAt b hβ).toMatrix
        ((trivializationAt E (TangentSpace I) α).basisAt b hα) := by
  rw [← coordChangeL_toMatrix b hα hβ]
  congr 1
  ext v
  exact (VectorBundleCore.trivializationAt_coordChange_eq
    (Z := tangentBundleCore I M) ⟨hα, hβ⟩ v).symm

end TangentReading

end TangentChart

section BasePoint

variable [IsManifold I 1 M]

private theorem localFrame_apply_eq_symmL {ι : Type*} (b : Basis ι 𝕜 E)
    (e : Trivialization E (TotalSpace.proj : TangentBundle I M → M)) [MemTrivializationAtlas e]
    {x : M} (hx : x ∈ e.baseSet) (i : ι) :
    e.localFrame b i x = e.symmL 𝕜 x (b i) := by
  rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet _ _ hx,
    Bundle.Trivialization.basisAt, Basis.map_apply,
    Bundle.Trivialization.linearEquivAt_symm_apply, ← e.symmL_apply (R := 𝕜) hx]

/-- Over its own base point, the local frame attached to the canonical trivialization at `x` is
the given basis of the model space. -/
@[simp]
theorem localFrame_trivializationAt_self {ι : Type*} (b : Basis ι 𝕜 E) (x : M) (i : ι) :
    (trivializationAt E (TangentSpace I) x).localFrame b i x = b i := by
  have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) x
  rw [localFrame_apply_eq_symmL b _ hx]
  exact symmL_trivializationAt_self (I := I) x (b i)

end BasePoint

/-- The canonical identification between the tangent space of an open submanifold and the ambient
tangent space. Both are Mathlib's type synonym for the common model vector space.

This is deliberately a named equivalence rather than `ContinuousLinearEquiv.refl 𝕜 E`: because
`TangentSpace` is not reducible, a statement phrased with `refl` is type-correct only after
unfolding it, so `rw` and `simp` fail on such statements. Mathlib introduces
`NormedSpace.fromTangentSpace` for the analogous identification for the same reason. -/
noncomputable def tangentSpaceOpenEquiv {U : Opens M} (x : U) :
    TangentSpace I x ≃L[𝕜] TangentSpace I (x : M) where
  toFun v := v
  invFun v := v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

@[simp]
theorem tangentSpaceOpenEquiv_apply {U : Opens M} (x : U) (v : TangentSpace I x) :
    tangentSpaceOpenEquiv (I := I) x v = v := by
  exact (rfl)

@[simp]
theorem tangentSpaceOpenEquiv_symm_apply {U : Opens M} (x : U)
    (v : TangentSpace I (x : M)) :
    (tangentSpaceOpenEquiv (I := I) x).symm v = v := by
  exact (rfl)

/-- In inherited charts, the tangent-bundle coordinate changes of an open submanifold and its
ambient manifold agree locally. -/
private theorem eventually_tangentBundleCore_coordChange_open_eq
    [IsManifold I 1 M] {U : Opens M} (x : U) :
    ∀ᶠ y in nhds x,
      (tangentBundleCore I U).coordChange (achart H x) (achart H y) y =
        (tangentBundleCore I M).coordChange
          (achart H (x : M)) (achart H (y : M)) (y : M) := by
  rcases mem_nhds_iff.mp
      (Opens.chartAt_subtype_val_symm_eventuallyEq (H := H) U (x := x)) with
    ⟨V, hV, hVopen, hxV⟩
  have hxV' : chartAt H x x ∈ V := by
    simpa [Opens.chartAt_eq] using hxV
  have hVevent : ∀ᶠ y in nhds x, chartAt H x y ∈ V :=
    ((chartAt H x).continuousAt (by simp)).eventually (hVopen.mem_nhds hxV')
  filter_upwards [hVevent] with y hyV
  have hinv : (chartAt H (x : M)).symm =ᶠ[nhds (chartAt H (x : M) (y : M))]
      Subtype.val ∘ (chartAt H x).symm :=
    Filter.eventuallyEq_of_mem (hVopen.mem_nhds hyV) hV
  have hIsymm : Tendsto I.symm
      (nhds (I (chartAt H (x : M) (y : M))))
      (nhds (chartAt H (x : M) (y : M))) := by
    have hc : Tendsto I.symm
        (nhds (I (chartAt H (x : M) (y : M))))
        (nhds (I.symm (I (chartAt H (x : M) (y : M))))) :=
      I.continuous_symm.continuousAt
    simpa only [I.left_inv] using hc
  have htrans := Filter.EventuallyEq.comp_tendsto
    (hinv.fun_comp (↑I ∘ chartAt H (y : M))) hIsymm
  have hd : fderivWithin 𝕜
      (((↑I ∘ chartAt H (y : M)) ∘ (chartAt H (x : M)).symm) ∘ I.symm)
        (Set.range I) (I (chartAt H (x : M) (y : M))) =
      fderivWithin 𝕜
        (((↑I ∘ chartAt H (y : M)) ∘ Subtype.val ∘ (chartAt H x).symm) ∘ I.symm)
          (Set.range I) (I (chartAt H (x : M) (y : M))) :=
    htrans.fderivWithin_eq_of_nhds
  ext z
  simpa [tangentBundleCore_coordChange_achart, Function.comp_def, Opens.chartAt_eq,
    tangentSpaceOpenEquiv_apply] using DFunLike.congr_fun hd.symm z

/-- The differential of the inclusion of an open submanifold is the canonical tangent-space
identification. -/
@[simp]
theorem mfderiv_subtype_val {U : Opens M} (x : U) :
    mfderiv I I (Subtype.val : U → M) x =
      (tangentSpaceOpenEquiv (I := I) x).toContinuousLinearMap := by
  ext v
  rw [ContinuousLinearEquiv.coe_coe, tangentSpaceOpenEquiv_apply, mfderiv]
  simp only [contMDiff_subtype_val.mdifferentiableAt one_ne_zero, ↓reduceIte]
  have h : writtenInExtChartAt I I x (Subtype.val : U → M) =ᶠ[
      nhdsWithin (extChartAt I x x) (Set.range I)] id := by
    have hmem : I.symm ⁻¹' (chartAt H x).target ∩ Set.range I ∈
        nhdsWithin (extChartAt I x x) (Set.range I) := by
      rw [← I.image_eq (chartAt H x).target]
      exact (chartAt H x).extend_image_target_mem_nhds (mem_chart_source H x)
    filter_upwards [hmem] with y hy
    rcases hy with ⟨hyT, ⟨z, rfl⟩⟩
    have hzT : z ∈ (chartAt H x).target := by
      simpa only [Set.mem_preimage, I.left_inv] using hyT
    simp only [writtenInExtChartAt, Function.comp_apply, extChartAt,
      OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm, I.left_inv, id_eq]
    -- The chart of `U` at `x` is by definition the subtype restriction of the ambient chart, so
    -- its inverse followed by the inclusion is the ambient inverse chart on the restricted target.
    have hsymm : ((chartAt H x).symm z : M) = (chartAt H (x : M)).symm z := by
      rw [Opens.chartAt_eq]
      exact (chartAt H (x : M)).subtypeRestr_symm_apply ⟨x⟩ hzT
    rw [hsymm]
    simp only [(chartAt H (x : M)).right_inv
        ((chartAt H (x : M)).subtypeRestr_target_subset ⟨x⟩ hzT)]
  have hxRange : extChartAt I x x ∈ Set.range I :=
    ⟨chartAt H x x, rfl⟩
  rw [h.fderivWithin_eq_of_mem hxRange,
    fderivWithin_id
      (I.uniqueDiffOn.uniqueDiffWithinAt hxRange)]
  rfl

/-- The tangent map of an open submanifold's inclusion identifies its tangent vectors with
ambient tangent vectors through `tangentSpaceOpenEquiv`. -/
@[simp]
theorem tangentMap_subtype_val {U : Opens M}
    (p : TangentBundle I U) :
    tangentMap I I (Subtype.val : U → M) p =
      ⟨(p.proj : M), tangentSpaceOpenEquiv (I := I) p.proj p.2⟩ := by
  simp only [tangentMap, mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe]

/-- If a differentiable map `f` between open submanifolds is the restriction of a map `A` of the
ambient manifolds, then under the canonical tangent-space identifications the differential of `f`
at `x` is the differential of `A` at `x`. -/
theorem tangentSpaceOpenEquiv_mfderiv_apply
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {U : Opens M} {V : Opens M'} {f : U → V} {A : M → M'} {x : U}
    (hf : MDifferentiableAt I I' f x) (hA : MDifferentiableAt I I' A x)
    (hcomp : Subtype.val ∘ f = A ∘ Subtype.val) (v : TangentSpace I x) :
    tangentSpaceOpenEquiv (I := I') (f x) (mfderiv I I' f x v) =
      mfderiv I I' A x (tangentSpaceOpenEquiv (I := I) x v) := by
  have h := mfderiv_comp_apply x
    (contMDiff_subtype_val.mdifferentiableAt one_ne_zero (x := f x)) hf v
  rw [hcomp, mfderiv_comp_apply x hA (contMDiff_subtype_val.mdifferentiableAt one_ne_zero) v,
    mfderiv_subtype_val, mfderiv_subtype_val] at h
  exact h.symm

/-- The differential of the inclusion of nested open submanifolds is the identity of the common
model vector space. -/
@[simp]
theorem mfderiv_inclusion_apply {U V : Opens M} (h : U ≤ V) (x : U)
    (v : TangentSpace I x) : mfderiv I I (Opens.inclusion h) x v = v := by
  have h' := tangentSpaceOpenEquiv_mfderiv_apply (A := id)
    ((contMDiff_inclusion h).mdifferentiableAt one_ne_zero) mdifferentiableAt_id rfl v
  rw [tangentSpaceOpenEquiv_apply, tangentSpaceOpenEquiv_apply, mfderiv_id] at h'
  exact h'

/-- The tangent bundle of a model space is Hausdorff. -/
theorem instT2SpaceTangentBundleModelSpace :
    T2Space (TangentBundle I H) := by
  let _ : T2Space H := I.isClosedEmbedding.toIsEmbedding.t2Space
  let _ : T2Space (ModelProd H E) := Prod.t2Space
  exact (tangentBundleModelSpaceHomeomorph I).symm.t2Space

scoped[TauCeti] attribute [instance] Manifold.instT2SpaceTangentBundleModelSpace

/-- Near a point of an open submanifold, its inverse tangent-bundle trivialization agrees with the
ambient inverse trivialization under the canonical tangent-space identification. -/
theorem eventually_tangentSpaceOpenEquiv_symmL_trivializationAt_eq
    [IsManifold I 1 M] {U : Opens M} (x : U) :
    ∀ᶠ y in nhds x, ∀ z : E,
      tangentSpaceOpenEquiv (I := I) y
          ((trivializationAt E (TangentSpace I : U → Type _) x).symmL 𝕜 y z) =
        (trivializationAt E (TangentSpace I : M → Type _) (x : M)).symmL 𝕜 (y : M) z := by
  filter_upwards [
    (trivializationAt E (TangentSpace I : U → Type _) x).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I : U → Type _) x),
    continuousAt_subtype_val.eventually
      ((trivializationAt E (TangentSpace I : M → Type _) (x : M)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) (x : M))),
    eventually_tangentBundleCore_coordChange_open_eq (I := I) x] with y hyU hyM hcoord
  intro z
  have hyU' : y ∈ (chartAt H x).source := by
    simpa using hyU
  have hyM' : (y : M) ∈ (chartAt H (x : M)).source := by
    exact hyM
  rw [TangentBundle.symmL_trivializationAt_eq_core hyU',
    TangentBundle.symmL_trivializationAt_eq_core hyM']
  -- The preceding rewrites identify the two `symmL` maps with core coordinate changes, but their
  -- applications still use the definitional identification `TangentSpace I b = E`. The following
  -- `change` intentionally unfolds those map coercions and the local `tangentSpaceOpenEquiv`; no
  -- application-level rewrite lemma exposes this conversion.
  change (tangentBundleCore I U).coordChange (achart H x) (achart H y) y z =
    (tangentBundleCore I M).coordChange (achart H (x : M)) (achart H (y : M)) (y : M) z
  exact DFunLike.congr_fun hcoord z

section RestrictOpenBilin

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Restrict a field of continuous bilinear maps on the tangent spaces of `M` to an open
submanifold `U`, through the canonical tangent-space identification. -/
noncomputable def restrictOpenTangentSpaceBilin
    (b : Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] F) (U : Opens M) (x : U) :
    TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] F :=
  let e := tangentSpaceOpenEquiv (I := I) x
  e.symm.arrowCongr (e.symm.arrowCongr (ContinuousLinearEquiv.refl 𝕜 F)) (b x)

/-- The restriction of a bilinear field to an open submanifold evaluates the ambient field through
the canonical tangent-space identification. -/
@[simp]
theorem restrictOpenTangentSpaceBilin_apply
    (b : Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] F) (U : Opens M) (x : U)
    (v w : TangentSpace I x) :
    restrictOpenTangentSpaceBilin b U x v w =
      b x (tangentSpaceOpenEquiv (I := I) x v) (tangentSpaceOpenEquiv (I := I) x w) :=
  (rfl)

/-- Restricting a bilinear field on the tangent bundle to an open submanifold preserves `C^n`
regularity at a point. -/
theorem contMDiffAt_restrictOpenTangentSpaceBilin [IsManifold I 1 M] {n : ℕ∞ω}
    {b : Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] F} {U : Opens M} {x : U}
    (hb : ContMDiffAt I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] F)) n
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] F) y (b y)) x) :
    ContMDiffAt I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] F)) n
      (fun y : U ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] F) y (restrictOpenTangentSpaceBilin b U y))
      x := by
  -- Pull ambient `C^n` regularity back along the inclusion and compare the inherited and ambient
  -- tangent-bundle coordinates on a common neighbourhood of `x`.
  rw [contMDiffAt_section]
  have h := hb.comp x (contMDiff_subtype_val (I := I) (U := U)).contMDiffAt
  rw [contMDiffAt_totalSpace] at h
  apply h.2.congr_of_eventuallyEq
  filter_upwards [
    (trivializationAt E (TangentSpace I : U → Type _) x).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I : U → Type _) x),
    continuousAt_subtype_val.eventually
      ((trivializationAt E (TangentSpace I : M → Type _) x.1).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x.1)),
    eventually_tangentSpaceOpenEquiv_symmL_trivializationAt_eq (I := I) x] with y hyU hyM hsymm
  have hyU' : y ∈ (chartAt H x).source := by simpa using hyU
  have hyM' : (y : M) ∈ (chartAt H (x : M)).source := hyM
  have hyUhom : y ∈ (trivializationAt (E →L[𝕜] F)
      (fun z : U ↦ TangentSpace I z →L[𝕜] F) x).baseSet := by
    simpa using hyU'
  have hyMhom : (y : M) ∈ (trivializationAt (E →L[𝕜] F)
      (fun z : M ↦ TangentSpace I z →L[𝕜] F) (x : M)).baseSet := by
    simpa using hyM'
  ext v w
  simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    Trivialization.continuousLinearMapAt_apply, Trivialization.symmL_apply,
    Trivialization.linearMapAt_apply,
    hyU, hyUhom, hyMhom, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ite_true]
  rw [restrictOpenTangentSpaceBilin_apply]
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.trivialization_baseSet,
    Set.mem_univ, ite_true, Trivial.trivialization_apply]
  have hsymm' (z : E) :
      tangentSpaceOpenEquiv (I := I) y
          ((trivializationAt E (TangentSpace I : U → Type _) x).symm y z) =
        (trivializationAt E (TangentSpace I : M → Type _) (x : M)).symmL 𝕜 (y : M) z := by
    simpa only [Trivialization.symmL_apply _ hyU] using hsymm z
  rw [hsymm' v, hsymm' w, Trivialization.symmL_apply _ hyM, Trivialization.symmL_apply _ hyM]

end RestrictOpenBilin

section Prod

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

/-- The canonical identification of the tangent space of a product manifold with the product of
the tangent spaces of the factors. Both are Mathlib's type synonym for the product of the model
vector spaces; as for `tangentSpaceOpenEquiv`, the identification is named so that statements
using it are type-correct without unfolding `TangentSpace`. -/
noncomputable def tangentSpaceProdEquiv (p : M × N) :
    TangentSpace (I.prod J) p ≃L[𝕜] TangentSpace I p.1 × TangentSpace J p.2 where
  toFun v := v
  invFun v := v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

@[simp]
theorem tangentSpaceProdEquiv_apply (p : M × N) (v : TangentSpace (I.prod J) p) :
    tangentSpaceProdEquiv (I := I) (J := J) p v = v := by
  exact (rfl)

@[simp]
theorem tangentSpaceProdEquiv_symm_apply (p : M × N)
    (v : TangentSpace I p.1 × TangentSpace J p.2) :
    (tangentSpaceProdEquiv (I := I) (J := J) p).symm v = v := by
  exact (rfl)

/-- The differential of a product map acts componentwise under the canonical
identifications of the product tangent spaces. -/
theorem mfderiv_prodMap_apply
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
    {G' : Type*} [TopologicalSpace G'] {J' : ModelWithCorners 𝕜 F' G'}
    {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
    {f : M → M'} {g : N → N'} {p : M × N}
    (hf : MDifferentiableAt I I' f p.1) (hg : MDifferentiableAt J J' g p.2)
    (v : TangentSpace I p.1 × TangentSpace J p.2) :
    mfderiv (I.prod J) (I'.prod J') (Prod.map f g) p
        ((tangentSpaceProdEquiv p).symm v) =
      (tangentSpaceProdEquiv (f p.1, g p.2)).symm
        (mfderiv I I' f p.1 v.1, mfderiv J J' g p.2 v.2) := by
  rw [mfderiv_prodMap hf hg]
  rfl

/-- The differential of a product map is invertible at a point where the differentials of both
factors are invertible. -/
theorem isInvertible_mfderiv_prodMap
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
    {G' : Type*} [TopologicalSpace G'] {J' : ModelWithCorners 𝕜 F' G'}
    {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
    {f : M → M'} {g : N → N'} {p : M × N}
    (hf : MDifferentiableAt I I' f p.1) (hg : MDifferentiableAt J J' g p.2)
    (hf' : (mfderiv I I' f p.1).IsInvertible) (hg' : (mfderiv J J' g p.2).IsInvertible) :
    (mfderiv (I.prod J) (I'.prod J') (Prod.map f g) p).IsInvertible := by
  obtain ⟨e₁, he₁⟩ := hf'
  obtain ⟨e₂, he₂⟩ := hg'
  rw [mfderiv_prodMap hf hg, ← he₁, ← he₂]
  exact ⟨e₁.prodCongr e₂, rfl⟩

/-- The differential of `(x, t) ↦ (x, φ t)` on `M × 𝕜` fixes the `M`-component and multiplies the
`𝕜`-component by `φ' t`. -/
theorem tangentSpaceProdEquiv_mfderiv_prodMap_id {φ : 𝕜 → 𝕜} {p : M × 𝕜}
    (hφ : DifferentiableAt 𝕜 φ p.2) (v : TangentSpace (I.prod 𝓘(𝕜)) p) :
    tangentSpaceProdEquiv (p.1, φ p.2)
        (mfderiv (I.prod 𝓘(𝕜)) (I.prod 𝓘(𝕜)) (Prod.map id φ) p v) =
      ((tangentSpaceProdEquiv p v).1, (NormedSpace.fromTangentSpace (φ p.2)).symm
        (deriv φ p.2 * NormedSpace.fromTangentSpace p.2 (tangentSpaceProdEquiv p v).2)) := by
  rw [mfderiv_prodMap mdifferentiableAt_id hφ.mdifferentiableAt, mfderiv_id, mfderiv_eq_fderiv,
    tangentSpaceProdEquiv_apply p v]
  -- Both sides now live in the product of the model spaces; the remaining identifications
  -- `tangentSpaceProdEquiv` and `NormedSpace.fromTangentSpace` are the identity on elements.
  exact (tangentSpaceProdEquiv_apply _ _).trans (Prod.ext rfl
    (congrArg (NormedSpace.fromTangentSpace (φ p.2)).symm
      ((fderiv_eq_smul_deriv _).trans (mul_comm _ _))))

/-- If `φ' t ≠ 0`, the differential of `(x, t) ↦ (x, φ t)` on `M × 𝕜` at `(x, t)` is
invertible. -/
theorem isInvertible_mfderiv_prodMap_id {φ : 𝕜 → 𝕜} {p : M × 𝕜}
    (hφ : DifferentiableAt 𝕜 φ p.2) (hφ' : deriv φ p.2 ≠ 0) :
    (mfderiv (I.prod 𝓘(𝕜)) (I.prod 𝓘(𝕜)) (Prod.map id φ) p).IsInvertible := by
  refine ⟨(tangentSpaceProdEquiv p).trans
    (((ContinuousLinearEquiv.refl 𝕜 (TangentSpace I p.1)).prodCongr
      ((NormedSpace.fromTangentSpace p.2).trans
        ((ContinuousLinearEquiv.unitsEquivAut 𝕜 (Units.mk0 _ hφ')).trans
          (NormedSpace.fromTangentSpace (φ p.2)).symm))).trans
      (tangentSpaceProdEquiv (p.1, φ p.2)).symm),
    ContinuousLinearMap.ext fun v ↦ (tangentSpaceProdEquiv (p.1, φ p.2)).injective ?_⟩
  rw [tangentSpaceProdEquiv_mfderiv_prodMap_id hφ]
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.prodCongr_apply,
    ContinuousLinearEquiv.refl_apply, ContinuousLinearEquiv.unitsEquivAut_apply, Units.val_mk0,
    Prod.map, mul_comm]

/-- On the common domain of two product charts, the tangent coordinate change of a product
manifold is the product of the tangent coordinate changes of the factors. -/
theorem tangentCoordChange_prod [IsManifold I 1 M] [IsManifold J 1 N] {p q z : M × N}
    (hz : z ∈ (extChartAt (I.prod J) p).source ∩ (extChartAt (I.prod J) q).source) :
    tangentCoordChange (I.prod J) p q z =
      (tangentCoordChange I p.1 q.1 z.1).prodMap (tangentCoordChange J p.2 q.2 z.2) := by
  simp only [extChartAt_prod, PartialEquiv.prod_source, Set.mem_inter_iff,
    Set.mem_prod] at hz
  have h₁ := hasFDerivWithinAt_tangentCoordChange (I := I) (x := p.1) (y := q.1) (z := z.1)
    ⟨hz.1.1, hz.2.1⟩
  have h₂ := hasFDerivWithinAt_tangentCoordChange (I := J) (x := p.2) (y := q.2) (z := z.2)
    ⟨hz.1.2, hz.2.2⟩
  have h := HasFDerivWithinAt.prodMap (s := range I ×ˢ range J)
    (p := (extChartAt I p.1 z.1, extChartAt J p.2 z.2))
    (h₁.mono (fst_image_prod_subset _ _)) (h₂.mono (snd_image_prod_subset _ _))
  rw [tangentCoordChange_def, extChartAt_prod, extChartAt_prod, ModelWithCorners.range_prod]
  exact h.fderivWithin ((I.uniqueDiffOn.prod J.uniqueDiffOn) _
    ⟨mem_range_self _, mem_range_self _⟩)

/-- Over the domain of the chart at `p`, the inverse of the canonical tangent-bundle
trivialization of a product manifold at `p` is the product of the inverse trivializations of the
factors. -/
theorem tangentSpaceProdEquiv_symmL_trivializationAt [IsManifold I 1 M] [IsManifold J 1 N]
    {p q : M × N} (hq : q ∈ (chartAt (ModelProd H G) p).source) (v : E × F) :
    tangentSpaceProdEquiv q
        ((trivializationAt (E × F) (TangentSpace (I.prod J)) p).symmL 𝕜 q v) =
      ((trivializationAt E (TangentSpace I) p.1).symmL 𝕜 q.1 v.1,
        (trivializationAt F (TangentSpace J) p.2).symmL 𝕜 q.2 v.2) := by
  have hq' : q.1 ∈ (chartAt H p.1).source ∧ q.2 ∈ (chartAt G p.2).source := by
    simpa only [prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_source, mem_prod] using hq
  rw [TangentBundle.symmL_trivializationAt_eq_core hq,
    TangentBundle.symmL_trivializationAt_eq_core hq'.1,
    TangentBundle.symmL_trivializationAt_eq_core hq'.2]
  have h := tangentCoordChange_prod (I := I) (J := J) (p := p) (q := q) (z := q)
    ⟨by simpa [extChartAt_source] using hq, by simp⟩
  exact congrArg (fun L : E × F →L[𝕜] E × F ↦ L v) h

end Prod

section Sum

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] [IsManifold I 1 M]
  [IsManifold I 1 M']

/-- The tangent coordinate changes of a disjoint union `M ⊕ M'` between charts at points of `M`
are those of `M`. -/
theorem tangentCoordChange_sumInl (x y z : M) :
    tangentCoordChange I (Sum.inl x : M ⊕ M') (Sum.inl y) (Sum.inl z) =
      tangentCoordChange I x y z := by
  simp only [tangentCoordChange_def, extChartAt_inl_apply]
  congr 1
  have : Nonempty H := nonempty_of_chartedSpace x
  ext w
  simp [ChartedSpace.sum_chartAt_inl, Sum.inl_injective.extend_apply]

/-- The tangent coordinate changes of a disjoint union `M ⊕ M'` between charts at points of `M'`
are those of `M'`. -/
theorem tangentCoordChange_sumInr (x y z : M') :
    tangentCoordChange I (Sum.inr x : M ⊕ M') (Sum.inr y) (Sum.inr z) =
      tangentCoordChange I x y z := by
  simp only [tangentCoordChange_def, extChartAt_inr_apply]
  congr 1
  have : Nonempty H := nonempty_of_chartedSpace x
  ext w
  simp [ChartedSpace.sum_chartAt_inr, Sum.inr_injective.extend_apply]

/-- Over the domain of the chart at `x`, the inverse of the canonical tangent-bundle trivialization
of `M ⊕ M'` at a point `x` of `M` is the inverse trivialization of `M` at `x`. -/
theorem symmL_trivializationAt_sumInl {x z : M} (hz : z ∈ (chartAt H x).source) :
    (trivializationAt E (TangentSpace I : M ⊕ M' → Type _) (Sum.inl x)).symmL 𝕜 (Sum.inl z) =
      (trivializationAt E (TangentSpace I : M → Type _) x).symmL 𝕜 z := by
  have : Nonempty H := nonempty_of_chartedSpace x
  rw [TangentBundle.symmL_trivializationAt_eq_core
      (by simpa [ChartedSpace.sum_chartAt_inl] using hz),
    TangentBundle.symmL_trivializationAt_eq_core hz]
  exact tangentCoordChange_sumInl x z z

/-- Over the domain of the chart at `y`, the inverse of the canonical tangent-bundle trivialization
of `M ⊕ M'` at a point `y` of `M'` is the inverse trivialization of `M'` at `y`. -/
theorem symmL_trivializationAt_sumInr {y z : M'} (hz : z ∈ (chartAt H y).source) :
    (trivializationAt E (TangentSpace I : M ⊕ M' → Type _) (Sum.inr y)).symmL 𝕜 (Sum.inr z) =
      (trivializationAt E (TangentSpace I : M' → Type _) y).symmL 𝕜 z := by
  have : Nonempty H := nonempty_of_chartedSpace y
  rw [TangentBundle.symmL_trivializationAt_eq_core
      (by simpa [ChartedSpace.sum_chartAt_inr] using hz),
    TangentBundle.symmL_trivializationAt_eq_core hz]
  exact tangentCoordChange_sumInr y z z

end Sum

end TauCeti.Manifold

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {a b : ℝ} [Fact (a < b)]

/-- The differential of the inclusion `M × [a, b] → M × ℝ` is invertible, also at the boundary. -/
theorem isInvertible_mfderiv_prodMap_id_subtypeVal_Icc (p : M × Icc a b) :
    (mfderiv (I.prod (𝓡∂ 1)) (I.prod 𝓘(ℝ)) (Prod.map id Subtype.val : M × Icc a b → M × ℝ)
      p).IsInvertible :=
  isInvertible_mfderiv_prodMap mdifferentiableAt_id
    ((contMDiff_subtypeVal_Icc (n := 1)).mdifferentiableAt one_ne_zero)
    (by rw [mfderiv_id]; exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩)
    (TauCeti.isInvertible_mfderiv_subtypeVal_Icc p.2)

end TauCeti.Manifold
