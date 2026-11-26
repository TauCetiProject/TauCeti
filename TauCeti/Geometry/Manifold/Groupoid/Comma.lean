/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Submersion
public import TauCeti.Geometry.Manifold.PullbackGroupoid
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
public import TauCeti.Topology.CategoryTheory.Comma

import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Smooth object spaces of weak fiber products

Given functors `L : A ⥤ T` and `R : B ⥤ T` whose object maps `L.obj : A → T` and `R.obj : B → T` and
target source-target maps `Quiver.Total.left, Quiver.Total.right : Quiver.Total T → T` are `C^n`
(`1 ≤ n`) between boundaryless finite-dimensional real manifolds, the comma object space `Comma L R`
is homeomorphic via `CategoryTheory.Comma.objectHomeomorph` to the fiber product of
`Prod.map L.obj R.obj : A × B → T × T` with `(left, right) : Quiver.Total T → T × T`.

Under fiberwise transversality (`CategoryTheory.Comma.IsFiberwiseTransverse`), pulling
`CategoryTheory.Comma.fiberProductChartedSpace` back along `CategoryTheory.Comma.objectHomeomorph`
equips `Comma L R` with a `C^n` manifold structure (`chartedSpaceObjects`, `isManifold_objects`)
whose coordinate map into `(A × B) × Quiver.Total T` is a `C^n` smooth embedding
(`isSmoothEmbedding_objects`), with differential and tangent space characterized componentwise in
`TangentSpace IT (L.obj X.left)` and `TangentSpace IT (R.obj X.right)` (`mfderiv_objects_apply`,
`mem_range_mfderiv_objects_iff`). When the source map of `T` and `R.obj` are submersions or local
diffeomorphisms, transversality holds automatically
(`isFiberwiseTransverse_of_isSubmersion_source_rightObj`) and `Comma.left` inherits the submersion
or local-diffeomorphism property (`isSubmersion_left`, `isLocalDiffeomorph_left`), with dual
statements on the right.

## References

* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Section 5.3.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
-/

public section

open Function Module Topology
open scoped Manifold ContDiff

namespace CategoryTheory.Comma

section FiberwiseTransverse

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EA HA A EB HB B ET HT T EJT HJT : Type*}
  [Category A] [Category B] [Category T]
  [NormedAddCommGroup EA] [NormedSpace 𝕜 EA] [TopologicalSpace HA]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  [NormedAddCommGroup ET] [NormedSpace 𝕜 ET] [TopologicalSpace HT]
  [NormedAddCommGroup EJT] [NormedSpace 𝕜 EJT] [TopologicalSpace HJT]
  {IA : ModelWithCorners 𝕜 EA HA} {IB : ModelWithCorners 𝕜 EB HB}
  {IT : ModelWithCorners 𝕜 ET HT} {JT : ModelWithCorners 𝕜 EJT HJT}
  [TopologicalSpace A] [ChartedSpace HA A]
  [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace T] [ChartedSpace HT T]
  [TopologicalSpace (Quiver.Total T)] [ChartedSpace HJT (Quiver.Total T)]
  {n : ℕ∞ω} {L : A ⥤ T} {R : B ⥤ T}

/-- Fiberwise transversality of functors `L : A ⥤ T` and `R : B ⥤ T` on `Comma L R`: at every comma
object `X`, every pair of target tangent vectors `(u₁, u₂)` at `(L.obj X.left, R.obj X.right)`
decomposes as `(dL(vA) + ds(w), dR(vB) + dt(w))` for tangent vectors `vA`, `vB`, and `w`. -/
def IsFiberwiseTransverse (IA : ModelWithCorners 𝕜 EA HA) (IB : ModelWithCorners 𝕜 EB HB)
    (IT : ModelWithCorners 𝕜 ET HT) (JT : ModelWithCorners 𝕜 EJT HJT)
    (L : A ⥤ T) (R : B ⥤ T) : Prop :=
  ∀ X : Comma L R,
    ∀ (u₁ : TangentSpace IT (L.obj X.left)) (u₂ : TangentSpace IT (R.obj X.right)),
      ∃ (vA : TangentSpace IA X.left) (vB : TangentSpace IB X.right)
        (w : TangentSpace JT (⟨L.obj X.left, R.obj X.right, X.hom⟩ : Quiver.Total T)),
        mfderiv IA IT L.obj X.left vA +
          mfderiv JT IT Quiver.Total.left ⟨_, _, X.hom⟩ w = u₁ ∧
        mfderiv IB IT R.obj X.right vB +
          mfderiv JT IT Quiver.Total.right ⟨_, _, X.hom⟩ w = u₂

/-- Unfolding characterization of `CategoryTheory.Comma.IsFiberwiseTransverse`. -/
theorem isFiberwiseTransverse_iff :
    IsFiberwiseTransverse IA IB IT JT L R ↔
      ∀ X : Comma L R,
        ∀ (u₁ : TangentSpace IT (L.obj X.left)) (u₂ : TangentSpace IT (R.obj X.right)),
          ∃ (vA : TangentSpace IA X.left) (vB : TangentSpace IB X.right)
            (w : TangentSpace JT (⟨L.obj X.left, R.obj X.right, X.hom⟩ : Quiver.Total T)),
            mfderiv IA IT L.obj X.left vA +
              mfderiv JT IT Quiver.Total.left ⟨_, _, X.hom⟩ w = u₁ ∧
            mfderiv IB IT R.obj X.right vB +
              mfderiv JT IT Quiver.Total.right ⟨_, _, X.hom⟩ w = u₂ :=
  (Iff.rfl)

/-- Surjective differentials of `Quiver.Total.left` on `T` and of `R.obj` guarantee fiberwise
transversality of `Comma L R` for every functor `L : A ⥤ T`. -/
theorem isFiberwiseTransverse_of_surjective_mfderiv_source_rightObj (L : A ⥤ T)
    (hsT_surj : ∀ c : Quiver.Total T, Surjective (mfderiv JT IT Quiver.Total.left c))
    (hR_surj : ∀ b : B, Surjective (mfderiv IB IT R.obj b)) :
    IsFiberwiseTransverse IA IB IT JT L R :=
  isFiberwiseTransverse_iff.mpr fun X u₁ u₂ ↦ by
    obtain ⟨w, hw⟩ := hsT_surj ⟨_, _, X.hom⟩ u₁
    obtain ⟨vB, hvB⟩ := hR_surj X.right (u₂ - mfderiv JT IT Quiver.Total.right ⟨_, _, X.hom⟩ w)
    exact ⟨0, vB, w, by simp [hw], by simp [hvB]⟩

/-- When `Quiver.Total.left` on `T` and `R.obj` are `C^n` submersions (`n ≠ 0`), `Comma L R` is
fiberwise transverse for every functor `L : A ⥤ T`. -/
theorem isFiberwiseTransverse_of_isSubmersion_source_rightObj (hn : n ≠ 0) (L : A ⥤ T)
    (hsT_sub : Manifold.IsSubmersion JT IT n (Quiver.Total.left : Quiver.Total T → T))
    (hR_sub : Manifold.IsSubmersion IB IT n R.obj) :
    IsFiberwiseTransverse IA IB IT JT L R :=
  isFiberwiseTransverse_of_surjective_mfderiv_source_rightObj L
    (hsT_sub.surjective_mfderiv hn) (hR_sub.surjective_mfderiv hn)

/-- Surjective differentials of `Quiver.Total.right` on `T` and of `L.obj` guarantee fiberwise
transversality of `Comma L R` for every functor `R : B ⥤ T`. -/
theorem isFiberwiseTransverse_of_surjective_mfderiv_target_leftObj (R : B ⥤ T)
    (htT_surj : ∀ c : Quiver.Total T, Surjective (mfderiv JT IT Quiver.Total.right c))
    (hL_surj : ∀ a : A, Surjective (mfderiv IA IT L.obj a)) :
    IsFiberwiseTransverse IA IB IT JT L R :=
  isFiberwiseTransverse_iff.mpr fun X u₁ u₂ ↦ by
    obtain ⟨w, hw⟩ := htT_surj ⟨_, _, X.hom⟩ u₂
    obtain ⟨vA, hvA⟩ := hL_surj X.left (u₁ - mfderiv JT IT Quiver.Total.left ⟨_, _, X.hom⟩ w)
    exact ⟨vA, 0, w, by simp [hvA], by simp [hw]⟩

/-- When `Quiver.Total.right` on `T` and `L.obj` are `C^n` submersions (`n ≠ 0`), `Comma L R` is
fiberwise transverse for every functor `R : B ⥤ T`. -/
theorem isFiberwiseTransverse_of_isSubmersion_target_leftObj (hn : n ≠ 0) (R : B ⥤ T)
    (htT_sub : Manifold.IsSubmersion JT IT n (Quiver.Total.right : Quiver.Total T → T))
    (hL_sub : Manifold.IsSubmersion IA IT n L.obj) :
    IsFiberwiseTransverse IA IB IT JT L R :=
  isFiberwiseTransverse_of_surjective_mfderiv_target_leftObj R
    (htT_sub.surjective_mfderiv hn) (hL_sub.surjective_mfderiv hn)

/-- Fiberwise transversality on `Comma L R` implies transversality of `Prod.map L.obj R.obj` and
`(left, right) : Quiver.Total T → T × T` along their fiber product. -/
theorem fiberProduct_transverse (hn : 1 ≤ n)
    (hL : ContMDiff IA IT n L.obj) (hR : ContMDiff IB IT n R.obj)
    (hsT : ContMDiff JT IT n (Quiver.Total.left : Quiver.Total T → T))
    (htT : ContMDiff JT IT n (Quiver.Total.right : Quiver.Total T → T))
    (htrans : IsFiberwiseTransverse IA IB IT JT L R) :
    ∀ p : (A × B) × Quiver.Total T,
      _root_.Prod.map L.obj R.obj p.1 = (p.2.left, p.2.right) →
      (mfderiv (IA.prod IB) (IT.prod IT) (_root_.Prod.map L.obj R.obj) p.1).range ⊔
        (((tangentSpaceCast (IT.prod IT) (p.2.left, p.2.right)
          (_root_.Prod.map L.obj R.obj p.1)).toContinuousLinearMap).comp
            (mfderiv JT (IT.prod IT) (fun d : Quiver.Total T ↦ (d.left, d.right)) p.2)).range =
          ⊤ := by
  have hn0 := ENat.one_le_iff_ne_zero_withTop.1 hn
  rintro ⟨⟨a, b⟩, ⟨l, r, h⟩⟩ hp
  obtain ⟨rfl, rfl⟩ := _root_.Prod.mk.inj hp
  apply top_unique; rintro ⟨u₁, u₂⟩ -
  obtain ⟨vA, vB, w, hu₁, hu₂⟩ := isFiberwiseTransverse_iff.mp htrans ⟨a, b, h⟩ u₁ u₂
  have hL_eq := TauCeti.Manifold.mfderiv_prodMap_apply (p := (a, b))
    ((hL a).mdifferentiableAt hn0) ((hR b).mdifferentiableAt hn0) (vA, vB)
  rw [TauCeti.Manifold.tangentSpaceProdEquiv_symm_apply,
    TauCeti.Manifold.tangentSpaceProdEquiv_symm_apply] at hL_eq
  refine Submodule.mem_sup.mpr ⟨(mfderiv IA IT L.obj a vA, mfderiv IB IT R.obj b vB),
    ⟨(vA, vB), hL_eq⟩,
    (mfderiv JT IT Quiver.Total.left ⟨L.obj a, R.obj b, h⟩ w,
      mfderiv JT IT Quiver.Total.right ⟨L.obj a, R.obj b, h⟩ w),
    ⟨w, congrArg (tangentSpaceCast (IT.prod IT) (L.obj a, R.obj b) (L.obj a, R.obj b))
      (((hsT ⟨L.obj a, R.obj b, h⟩).mdifferentiableAt hn0).mfderiv_prodMk_apply
        ((htT ⟨L.obj a, R.obj b, h⟩).mdifferentiableAt hn0) w)⟩,
    _root_.Prod.ext hu₁ hu₂⟩

end FiberwiseTransverse

section Transverse

variable {EA HA A EB HB B ET HT T EJT HJT : Type*}
  [Category A] [Category B] [Category T]
  [NormedAddCommGroup EA] [NormedSpace ℝ EA] [FiniteDimensional ℝ EA] [TopologicalSpace HA]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup ET] [NormedSpace ℝ ET] [FiniteDimensional ℝ ET] [TopologicalSpace HT]
  [NormedAddCommGroup EJT] [NormedSpace ℝ EJT] [FiniteDimensional ℝ EJT] [TopologicalSpace HJT]
  {IA : ModelWithCorners ℝ EA HA} {IB : ModelWithCorners ℝ EB HB}
  {IT : ModelWithCorners ℝ ET HT} {JT : ModelWithCorners ℝ EJT HJT}
  [IA.Boundaryless] [IB.Boundaryless] [IT.Boundaryless] [JT.Boundaryless]
  {n : ℕ∞ω} {L : A ⥤ T} {R : B ⥤ T}
  [TopologicalSpace A] [ChartedSpace HA A] [IsManifold IA n A]
  [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB n B]
  [TopologicalSpace T] [ChartedSpace HT T] [IsManifold IT n T]
  [TopologicalSpace (Quiver.Total T)] [ChartedSpace HJT (Quiver.Total T)]
  [IsManifold JT n (Quiver.Total T)]
  (hn : 1 ≤ n)
  (hL : ContMDiff IA IT n L.obj) (hR : ContMDiff IB IT n R.obj)
  (hsT : ContMDiff JT IT n (Quiver.Total.left : Quiver.Total T → T))
  (htT : ContMDiff JT IT n (Quiver.Total.right : Quiver.Total T → T))
  (htrans : IsFiberwiseTransverse IA IB IT JT L R)

local notation "KComma" =>
  𝓘(ℝ, Fin (finrank ℝ (EA × EB) + finrank ℝ EJT - finrank ℝ (ET × ET)) → ℝ)

include hn hL hR hsT htT htrans

/-- The transverse fiber-product charted-space structure on
`{p : (A × B) × Quiver.Total T // Prod.map L.obj R.obj p.1 = (p.2.left, p.2.right)}`. -/
noncomputable abbrev fiberProductChartedSpace :
    ChartedSpace (Fin (finrank ℝ (EA × EB) + finrank ℝ EJT - finrank ℝ (ET × ET)) → ℝ)
      {p : (A × B) × Quiver.Total T // _root_.Prod.map L.obj R.obj p.1 = (p.2.left, p.2.right)} :=
  TauCeti.transverseFiberProductChartedSpace hn (hL.prodMap hR) (hsT.prodMk htT)
    (fiberProduct_transverse hn hL hR hsT htT htrans)

/-- The `C^n` charted-space structure on `Comma L R`, pulled back from
`CategoryTheory.Comma.fiberProductChartedSpace` along `CategoryTheory.Comma.objectHomeomorph`. -/
@[instance_reducible]
noncomputable def chartedSpaceObjects :
    ChartedSpace (Fin (finrank ℝ (EA × EB) + finrank ℝ EJT - finrank ℝ (ET × ET)) → ℝ)
      (Comma L R) :=
  letI := fiberProductChartedSpace hn hL hR hsT htT htrans
  (objectHomeomorph L R).pullbackChartedSpace

/-- With `chartedSpaceObjects`, `Comma L R` is a `C^n` manifold. -/
theorem isManifold_objects :
    letI := chartedSpaceObjects hn hL hR hsT htT htrans
    IsManifold KComma n (Comma L R) :=
  letI := fiberProductChartedSpace hn hL hR hsT htT htrans
  haveI := TauCeti.isManifold_transverseFiberProduct hn (hL.prodMap hR) (hsT.prodMk htT)
    (fiberProduct_transverse hn hL hR hsT htT htrans)
  (objectHomeomorph L R).pullback_isManifold KComma n

/-- `CategoryTheory.Comma.objectHomeomorph` upgraded to a `C^n` diffeomorphism between `Comma L R`
and the transverse fiber product `(A × B) ×_{T × T} Quiver.Total T`. -/
noncomputable def objectDiffeomorph :
    letI := chartedSpaceObjects hn hL hR hsT htT htrans
    letI := fiberProductChartedSpace hn hL hR hsT htT htrans
    Comma L R ≃ₘ^n⟮KComma, KComma⟯
      {p : (A × B) × Quiver.Total T // _root_.Prod.map L.obj R.obj p.1 = (p.2.left, p.2.right)} :=
  letI := fiberProductChartedSpace hn hL hR hsT htT htrans
  (objectHomeomorph L R).pullbackDiffeomorph KComma n

@[simp]
theorem coe_objectDiffeomorph :
    letI := chartedSpaceObjects hn hL hR hsT htT htrans
    letI := fiberProductChartedSpace hn hL hR hsT htT htrans
    ⇑(objectDiffeomorph hn hL hR hsT htT htrans) = ⇑(objectEquiv L R) := by
  let := fiberProductChartedSpace hn hL hR hsT htT htrans
  simp [objectDiffeomorph, Homeomorph.coe_pullbackDiffeomorph]

@[simp]
theorem coe_objectDiffeomorph_symm :
    letI := chartedSpaceObjects hn hL hR hsT htT htrans
    letI := fiberProductChartedSpace hn hL hR hsT htT htrans
    ⇑(objectDiffeomorph hn hL hR hsT htT htrans).symm = ⇑(objectEquiv L R).symm := by
  let := fiberProductChartedSpace hn hL hR hsT htT htrans
  simp [objectDiffeomorph, Homeomorph.coe_pullbackDiffeomorph_symm]

/-- The coordinate inclusion `X ↦ ((X.left, X.right), ⟨_, _, X.hom⟩)` of `Comma L R` into
`(A × B) × Quiver.Total T` is a `C^n` smooth embedding. -/
theorem isSmoothEmbedding_objects :
    letI := chartedSpaceObjects hn hL hR hsT htT htrans
    Manifold.IsSmoothEmbedding KComma ((IA.prod IB).prod JT) n
      (fun X : Comma L R ↦ ((X.left, X.right), (⟨_, _, X.hom⟩ : Quiver.Total T))) := by
  let := chartedSpaceObjects hn hL hR hsT htT htrans
  have := isManifold_objects hn hL hR hsT htT htrans
  let := fiberProductChartedSpace hn hL hR hsT htT htrans
  simpa only [Function.comp_def, coe_objectDiffeomorph, objectEquiv_apply_coe] using
    TauCeti.isSmoothEmbedding_comp_diffeomorph (objectDiffeomorph hn hL hR hsT htT htrans)
      (TauCeti.isSmoothEmbedding_coe_transverseFiberProduct hn (hL.prodMap hR) (hsT.prodMk htT)
        (fiberProduct_transverse hn hL hR hsT htT htrans))

/-- Smooth universal property of `Comma L R` on objects: a map into `Comma L R` is `C^n` if and
only if its left object, structure arrow in `Quiver.Total T`, and right object are `C^n`, with no
separate continuity assumption. -/
theorem contMDiff_objects_iff {EM HM M : Type*}
    [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
    {IM : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M]
    {g : M → Comma L R} :
    letI := chartedSpaceObjects hn hL hR hsT htT htrans
    ContMDiff IM KComma n g ↔
      ContMDiff IM IA n (fun x ↦ (g x).left) ∧
      ContMDiff IM JT n (fun x ↦ (⟨_, _, (g x).hom⟩ : Quiver.Total T)) ∧
      ContMDiff IM IB n (fun x ↦ (g x).right) := by
  let := chartedSpaceObjects hn hL hR hsT htT htrans
  rw [(isSmoothEmbedding_objects hn hL hR hsT htT htrans).contMDiff_iff_comp]
  exact ⟨fun h ↦ ⟨h.fst.fst, h.snd, h.fst.snd⟩, fun ⟨h₁, h₂, h₃⟩ ↦ (h₁.prodMk h₃).prodMk h₂⟩

/-- The left object projection `Comma.left : Comma L R → A` is `C^n`. -/
theorem contMDiff_left :
    letI := chartedSpaceObjects hn hL hR hsT htT htrans
    ContMDiff KComma IA n (Comma.left : Comma L R → A) :=
  letI := chartedSpaceObjects hn hL hR hsT htT htrans
  ((contMDiff_objects_iff hn hL hR hsT htT htrans).mp contMDiff_id).1

/-- The structure-arrow projection `X ↦ ⟨_, _, X.hom⟩` from `Comma L R` to `Quiver.Total T` is
`C^n`. -/
theorem contMDiff_totalHom :
    letI := chartedSpaceObjects hn hL hR hsT htT htrans
    ContMDiff KComma JT n (fun X : Comma L R ↦ (⟨_, _, X.hom⟩ : Quiver.Total T)) :=
  letI := chartedSpaceObjects hn hL hR hsT htT htrans
  ((contMDiff_objects_iff hn hL hR hsT htT htrans).mp contMDiff_id).2.1

/-- The right object projection `Comma.right : Comma L R → B` is `C^n`. -/
theorem contMDiff_right :
    letI := chartedSpaceObjects hn hL hR hsT htT htrans
    ContMDiff KComma IB n (Comma.right : Comma L R → B) :=
  letI := chartedSpaceObjects hn hL hR hsT htT htrans
  ((contMDiff_objects_iff hn hL hR hsT htT htrans).mp contMDiff_id).2.2

/-- The differential of the coordinate inclusion of `Comma L R` into `(A × B) × Quiver.Total T`
acts componentwise by the differentials of `Comma.left`, `Comma.right`, and the structure arrow. -/
theorem mfderiv_objects_apply (X : Comma L R) :
    letI := chartedSpaceObjects hn hL hR hsT htT htrans
    ∀ ξ : TangentSpace KComma X,
      mfderiv KComma ((IA.prod IB).prod JT)
          (fun Y : Comma L R ↦ ((Y.left, Y.right), (⟨_, _, Y.hom⟩ : Quiver.Total T))) X ξ =
        ((mfderiv KComma IA Comma.left X ξ, mfderiv KComma IB Comma.right X ξ),
          mfderiv KComma JT (fun Y : Comma L R ↦ (⟨_, _, Y.hom⟩ : Quiver.Total T)) X ξ) := by
  let := chartedSpaceObjects hn hL hR hsT htT htrans
  intro ξ
  have hn0 := ENat.one_le_iff_ne_zero_withTop.1 hn
  have hleft := ((contMDiff_left hn hL hR hsT htT htrans) X).mdifferentiableAt hn0
  have hright := ((contMDiff_right hn hL hR hsT htT htrans) X).mdifferentiableAt hn0
  have hhom := ((contMDiff_totalHom hn hL hR hsT htT htrans) X).mdifferentiableAt hn0
  rw [(hleft.prodMk hright).mfderiv_prodMk_apply hhom ξ, hleft.mfderiv_prodMk_apply hright ξ]
  rfl

/-- A tangent triple `((vA, vB), w)` lies in the tangent image of `Comma L R` at `X` if and only if
`dL(vA) = ds(w)` and `dR(vB) = dt(w)`. -/
theorem mem_range_mfderiv_objects_iff (X : Comma L R)
    (v : TangentSpace ((IA.prod IB).prod JT)
      ((X.left, X.right), (⟨_, _, X.hom⟩ : Quiver.Total T))) :
    letI := chartedSpaceObjects hn hL hR hsT htT htrans
    v ∈ (mfderiv KComma ((IA.prod IB).prod JT)
        (fun Y : Comma L R ↦ ((Y.left, Y.right), (⟨_, _, Y.hom⟩ : Quiver.Total T))) X).range ↔
      mfderiv IA IT L.obj X.left v.1.1 =
        mfderiv JT IT Quiver.Total.left ⟨_, _, X.hom⟩ v.2 ∧
      mfderiv IB IT R.obj X.right v.1.2 =
        mfderiv JT IT Quiver.Total.right ⟨_, _, X.hom⟩ v.2 := by
  let := chartedSpaceObjects hn hL hR hsT htT htrans
  let := fiberProductChartedSpace hn hL hR hsT htT htrans
  have hn0 := ENat.one_le_iff_ne_zero_withTop.1 hn
  let e := objectDiffeomorph hn hL hR hsT htT htrans
  have hcomp : (fun Y : Comma L R ↦ ((Y.left, Y.right), (⟨_, _, Y.hom⟩ : Quiver.Total T))) =
      Subtype.val ∘ ⇑e := by funext Y; simp [e]
  have hrange := (e.isLocalDiffeomorph X).range_mfderiv_comp
    (K := (IA.prod IB).prod JT) (g := Subtype.val) hn0
  let pX : {p : (A × B) × Quiver.Total T //
      _root_.Prod.map L.obj R.obj p.1 = (p.2.left, p.2.right)} :=
    ⟨((X.left, X.right), ⟨_, _, X.hom⟩), rfl⟩
  have heX : e X = pX := Subtype.ext (by simp [e, pX])
  rw [← hcomp, heX] at hrange
  rw [hrange, TauCeti.mem_range_mfderiv_coe_transverseFiberProduct_iff hn (hL.prodMap hR)
    (hsT.prodMk htT) (fiberProduct_transverse hn hL hR hsT htT htrans) pX v]
  have hL_eq := TauCeti.Manifold.mfderiv_prodMap_apply (p := (X.left, X.right))
    ((hL X.left).mdifferentiableAt hn0) ((hR X.right).mdifferentiableAt hn0) (v.1.1, v.1.2)
  rw [TauCeti.Manifold.tangentSpaceProdEquiv_symm_apply,
    TauCeti.Manifold.tangentSpaceProdEquiv_symm_apply] at hL_eq
  have hR_eq := ((hsT ⟨_, _, X.hom⟩).mdifferentiableAt hn0).mfderiv_prodMk_apply
    ((htT ⟨_, _, X.hom⟩).mdifferentiableAt hn0) v.2
  exact ⟨fun h ↦ _root_.Prod.ext_iff.mp (hL_eq.symm.trans (h.trans hR_eq)),
    fun h ↦ hL_eq.trans ((_root_.Prod.ext_iff.mpr h).trans hR_eq.symm)⟩

/-- Along `Comma L R`, the differential of `L.obj ∘ Comma.left` equals the differential of
`Quiver.Total.left` applied to the differential of the structure arrow. -/
theorem mfderiv_left_obj_eq (X : Comma L R) :
    letI := chartedSpaceObjects hn hL hR hsT htT htrans
    ∀ ξ : TangentSpace KComma X,
      mfderiv IA IT L.obj X.left (mfderiv KComma IA Comma.left X ξ) =
        mfderiv JT IT Quiver.Total.left ⟨_, _, X.hom⟩
          (mfderiv KComma JT (fun Y : Comma L R ↦ (⟨_, _, Y.hom⟩ : Quiver.Total T)) X ξ) := by
  let := chartedSpaceObjects hn hL hR hsT htT htrans
  have hn0 := ENat.one_le_iff_ne_zero_withTop.1 hn
  have h₁ := mfderiv_comp X ((hL X.left).mdifferentiableAt hn0)
    (((contMDiff_left hn hL hR hsT htT htrans) X).mdifferentiableAt hn0)
  have h₂ := mfderiv_comp X ((hsT ⟨_, _, X.hom⟩).mdifferentiableAt hn0)
    (((contMDiff_totalHom hn hL hR hsT htT htrans) X).mdifferentiableAt hn0)
  -- For `Y : Comma L R`, `(⟨L.obj Y.left, R.obj Y.right, Y.hom⟩ : Quiver.Total T).left` is
  -- definitionally `L.obj Y.left`.
  have hcomp : (L.obj ∘ Comma.left : Comma L R → T) =
      Quiver.Total.left ∘ fun Y : Comma L R ↦ (⟨_, _, Y.hom⟩ : Quiver.Total T) := rfl
  rw [hcomp] at h₁
  exact DFunLike.congr_fun (h₁.symm.trans h₂)

/-- Along `Comma L R`, the differential of `R.obj ∘ Comma.right` equals the differential of
`Quiver.Total.right` applied to the differential of the structure arrow. -/
theorem mfderiv_right_obj_eq (X : Comma L R) :
    letI := chartedSpaceObjects hn hL hR hsT htT htrans
    ∀ ξ : TangentSpace KComma X,
      mfderiv IB IT R.obj X.right (mfderiv KComma IB Comma.right X ξ) =
        mfderiv JT IT Quiver.Total.right ⟨_, _, X.hom⟩
          (mfderiv KComma JT (fun Y : Comma L R ↦ (⟨_, _, Y.hom⟩ : Quiver.Total T)) X ξ) := by
  let := chartedSpaceObjects hn hL hR hsT htT htrans
  have hn0 := ENat.one_le_iff_ne_zero_withTop.1 hn
  have h₁ := mfderiv_comp X ((hR X.right).mdifferentiableAt hn0)
    (((contMDiff_right hn hL hR hsT htT htrans) X).mdifferentiableAt hn0)
  have h₂ := mfderiv_comp X ((htT ⟨_, _, X.hom⟩).mdifferentiableAt hn0)
    (((contMDiff_totalHom hn hL hR hsT htT htrans) X).mdifferentiableAt hn0)
  -- For `Y : Comma L R`, `(⟨L.obj Y.left, R.obj Y.right, Y.hom⟩ : Quiver.Total T).right` is
  -- definitionally `R.obj Y.right`.
  have hcomp : (R.obj ∘ Comma.right : Comma L R → T) =
      Quiver.Total.right ∘ fun Y : Comma L R ↦ (⟨_, _, Y.hom⟩ : Quiver.Total T) := rfl
  rw [hcomp] at h₁
  exact DFunLike.congr_fun (h₁.symm.trans h₂)

/-- Every compatible tangent triple `(vA, vB, w)` at `X : Comma L R` arises as the differentials of
`Comma.left`, `Comma.right`, and `X ↦ ⟨_, _, X.hom⟩` applied to a tangent vector `ξ`. -/
theorem exists_mfderiv_eq_of_comma (X : Comma L R)
    (vA : TangentSpace IA X.left) (vB : TangentSpace IB X.right)
    (w : TangentSpace JT (⟨L.obj X.left, R.obj X.right, X.hom⟩ : Quiver.Total T))
    (hLw : mfderiv IA IT L.obj X.left vA = mfderiv JT IT Quiver.Total.left ⟨_, _, X.hom⟩ w)
    (hRw : mfderiv IB IT R.obj X.right vB = mfderiv JT IT Quiver.Total.right ⟨_, _, X.hom⟩ w) :
    letI := chartedSpaceObjects hn hL hR hsT htT htrans
    ∃ ξ : TangentSpace KComma X,
      mfderiv KComma IA Comma.left X ξ = vA ∧
      mfderiv KComma IB Comma.right X ξ = vB ∧
      mfderiv KComma JT (fun Y : Comma L R ↦ (⟨_, _, Y.hom⟩ : Quiver.Total T)) X ξ = w := by
  let := chartedSpaceObjects hn hL hR hsT htT htrans
  obtain ⟨ξ, hξ⟩ := (mem_range_mfderiv_objects_iff hn hL hR hsT htT htrans X ((vA, vB), w)).2
    ⟨hLw, hRw⟩
  simp only [ContinuousLinearMap.coe_coe] at hξ
  have hξ' := (mfderiv_objects_apply hn hL hR hsT htT htrans X ξ).symm.trans hξ
  exact ⟨ξ, congrArg (fun z ↦ z.1.1) hξ', congrArg (fun z ↦ z.1.2) hξ',
    congrArg _root_.Prod.snd hξ'⟩

/-- A tangent vector of `Comma L R` whose three coordinate differentials vanish is zero. -/
theorem eq_zero_of_mfderiv_comma (X : Comma L R) :
    letI := chartedSpaceObjects hn hL hR hsT htT htrans
    ∀ ξ : TangentSpace KComma X,
      mfderiv KComma IA Comma.left X ξ = 0 →
      mfderiv KComma IB Comma.right X ξ = 0 →
      mfderiv KComma JT (fun Y : Comma L R ↦ (⟨_, _, Y.hom⟩ : Quiver.Total T)) X ξ = 0 →
      ξ = 0 := by
  let := chartedSpaceObjects hn hL hR hsT htT htrans
  intro ξ h₁ h₂ h₃
  have hn0 := ENat.one_le_iff_ne_zero_withTop.1 hn
  have hi := isSmoothEmbedding_objects hn hL hR hsT htT htrans
  refine (injective_iff_map_eq_zero _).1 ((hi.isImmersion.isImmersionAt X).mfderiv_injective hn0)
    ξ ?_
  rw [mfderiv_objects_apply hn hL hR hsT htT htrans X ξ, h₁, h₂, h₃]
  rfl

/-- When `Quiver.Total.left` on `T` and `R.obj` have surjective differentials, the left projection
`Comma.left : Comma L R → A` is a `C^n` submersion. -/
theorem isSubmersion_left_of_surjective_mfderiv
    (hsT_surj : ∀ c : Quiver.Total T, Surjective (mfderiv JT IT Quiver.Total.left c))
    (hR_surj : ∀ b : B, Surjective (mfderiv IB IT R.obj b)) :
    letI := chartedSpaceObjects hn hL hR hsT htT htrans
    Manifold.IsSubmersion KComma IA n (Comma.left : Comma L R → A) := by
  let := chartedSpaceObjects hn hL hR hsT htT htrans
  have := isManifold_objects hn hL hR hsT htT htrans
  refine ((contMDiff_left hn hL hR hsT htT htrans).isSubmersionOfComplement_of_surjective_mfderiv
    hn fun X vA ↦ ?_).isSubmersion
  obtain ⟨w, hw⟩ := hsT_surj ⟨_, _, X.hom⟩ (mfderiv IA IT L.obj X.left vA)
  obtain ⟨vB, hvB⟩ := hR_surj X.right (mfderiv JT IT Quiver.Total.right ⟨_, _, X.hom⟩ w)
  obtain ⟨ξ, hξ, -, -⟩ := exists_mfderiv_eq_of_comma hn hL hR hsT htT htrans X vA vB w hw.symm hvB
  exact ⟨ξ, hξ⟩

/-- When `Quiver.Total.left` on `T` and `R.obj` are `C^n` submersions, the left projection
`Comma.left : Comma L R → A` is a `C^n` submersion. -/
theorem isSubmersion_left
    (hsT_sub : Manifold.IsSubmersion JT IT n (Quiver.Total.left : Quiver.Total T → T))
    (hR_sub : Manifold.IsSubmersion IB IT n R.obj) :
    letI := chartedSpaceObjects hn hL hR hsT htT htrans
    Manifold.IsSubmersion KComma IA n (Comma.left : Comma L R → A) :=
  have hn0 := ENat.one_le_iff_ne_zero_withTop.1 hn
  isSubmersion_left_of_surjective_mfderiv hn hL hR hsT htT htrans
    (hsT_sub.surjective_mfderiv hn0) (hR_sub.surjective_mfderiv hn0)

/-- When `Quiver.Total.right` on `T` and `L.obj` have surjective differentials, the right
projection `Comma.right : Comma L R → B` is a `C^n` submersion. -/
theorem isSubmersion_right_of_surjective_mfderiv
    (htT_surj : ∀ c : Quiver.Total T, Surjective (mfderiv JT IT Quiver.Total.right c))
    (hL_surj : ∀ a : A, Surjective (mfderiv IA IT L.obj a)) :
    letI := chartedSpaceObjects hn hL hR hsT htT htrans
    Manifold.IsSubmersion KComma IB n (Comma.right : Comma L R → B) := by
  let := chartedSpaceObjects hn hL hR hsT htT htrans
  have := isManifold_objects hn hL hR hsT htT htrans
  refine ((contMDiff_right hn hL hR hsT htT htrans).isSubmersionOfComplement_of_surjective_mfderiv
    hn fun X vB ↦ ?_).isSubmersion
  obtain ⟨w, hw⟩ := htT_surj ⟨_, _, X.hom⟩ (mfderiv IB IT R.obj X.right vB)
  obtain ⟨vA, hvA⟩ := hL_surj X.left (mfderiv JT IT Quiver.Total.left ⟨_, _, X.hom⟩ w)
  obtain ⟨ξ, -, hξ, -⟩ := exists_mfderiv_eq_of_comma hn hL hR hsT htT htrans X vA vB w hvA hw.symm
  exact ⟨ξ, hξ⟩

/-- When `Quiver.Total.right` on `T` and `L.obj` are `C^n` submersions, the right projection
`Comma.right : Comma L R → B` is a `C^n` submersion. -/
theorem isSubmersion_right
    (htT_sub : Manifold.IsSubmersion JT IT n (Quiver.Total.right : Quiver.Total T → T))
    (hL_sub : Manifold.IsSubmersion IA IT n L.obj) :
    letI := chartedSpaceObjects hn hL hR hsT htT htrans
    Manifold.IsSubmersion KComma IB n (Comma.right : Comma L R → B) :=
  have hn0 := ENat.one_le_iff_ne_zero_withTop.1 hn
  isSubmersion_right_of_surjective_mfderiv hn hL hR hsT htT htrans
    (htT_sub.surjective_mfderiv hn0) (hL_sub.surjective_mfderiv hn0)

/-- Smooth base change of étale object maps on the left: when `Quiver.Total.left` on `T` and `R.obj`
are `C^n` local diffeomorphisms, the left projection `Comma.left : Comma L R → A` is a `C^n` local
diffeomorphism. -/
theorem isLocalDiffeomorph_left
    (hsT_loc : IsLocalDiffeomorph JT IT n (Quiver.Total.left : Quiver.Total T → T))
    (hR_loc : IsLocalDiffeomorph IB IT n R.obj) :
    letI := chartedSpaceObjects hn hL hR hsT htT htrans
    IsLocalDiffeomorph KComma IA n (Comma.left : Comma L R → A) := by
  let := chartedSpaceObjects hn hL hR hsT htT htrans
  have := isManifold_objects hn hL hR hsT htT htrans
  have hn0 := ENat.one_le_iff_ne_zero_withTop.1 hn
  intro X
  have hJT := (hsT_loc ⟨_, _, X.hom⟩).finrank_eq hn0
  have hB := (hR_loc X.right).finrank_eq hn0
  exact (isSubmersion_left_of_surjective_mfderiv hn hL hR hsT htT htrans
    (fun c ↦ ((hsT_loc c).isInvertible_mfderiv hn0).surjective)
    (fun b ↦ ((hR_loc b).isInvertible_mfderiv hn0).surjective)).isLocalDiffeomorph_of_finrank_eq hn
    (by simp only [Module.finrank_fin_fun, Module.finrank_prod]; omega) X

/-- Smooth base change of étale object maps on the right: when `Quiver.Total.right` on `T` and
`L.obj` are `C^n` local diffeomorphisms, the right projection `Comma.right : Comma L R → B` is a
`C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_right
    (htT_loc : IsLocalDiffeomorph JT IT n (Quiver.Total.right : Quiver.Total T → T))
    (hL_loc : IsLocalDiffeomorph IA IT n L.obj) :
    letI := chartedSpaceObjects hn hL hR hsT htT htrans
    IsLocalDiffeomorph KComma IB n (Comma.right : Comma L R → B) := by
  let := chartedSpaceObjects hn hL hR hsT htT htrans
  have := isManifold_objects hn hL hR hsT htT htrans
  have hn0 := ENat.one_le_iff_ne_zero_withTop.1 hn
  intro X
  have hJT := (htT_loc ⟨_, _, X.hom⟩).finrank_eq hn0
  have hA := (hL_loc X.left).finrank_eq hn0
  exact (isSubmersion_right_of_surjective_mfderiv hn hL hR hsT htT htrans
    (fun c ↦ ((htT_loc c).isInvertible_mfderiv hn0).surjective)
    (fun a ↦ ((hL_loc a).isInvertible_mfderiv hn0).surjective)).isLocalDiffeomorph_of_finrank_eq hn
    (by simp only [Module.finrank_fin_fun, Module.finrank_prod]; omega) X

end Transverse

end CategoryTheory.Comma
