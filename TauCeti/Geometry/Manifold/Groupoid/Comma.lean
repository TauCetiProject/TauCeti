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

import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# Smooth object spaces of weak fiber products

Given functors `L : A ⥤ T` and `R : B ⥤ T` whose object maps `L.obj : A → T` and `R.obj : B → T` and
target source-target maps `Quiver.Total.left, Quiver.Total.right : Quiver.Total T → T` are `C^n`
(`1 ≤ n`) between boundaryless finite-dimensional real manifolds, the comma object space `Comma L R`
is homeomorphic via `CategoryTheory.Comma.objectHomeomorph` to the fiber product of
`Prod.map L.obj R.obj : A × B → T × T` with `(left, right) : Quiver.Total T → T × T`.

Under fiberwise transversality (`htrans`), pulling `TauCeti.transverseFiberProductChartedSpace` back
along `CategoryTheory.Comma.objectHomeomorph` equips `Comma L R` with a `C^n` manifold structure
(`chartedSpaceObjects`, `isManifold_objects`) whose coordinate map into `(A × B) × Quiver.Total T`
is a `C^n` smooth embedding (`isSmoothEmbedding_objects`), with tangent space characterized directly
in `TangentSpace IT (L.obj X.left)` and `TangentSpace IT (R.obj X.right)`
(`mem_range_mfderiv_objects_iff`). When the source map of `T` and `R.obj` are submersions or local
diffeomorphisms, transversality holds automatically (`transverse_of_isSubmersion_source_rightObj`)
and `Comma.left` inherits the submersion or local-diffeomorphism property (`isSubmersion_left`,
`isLocalDiffeomorph_left`), with dual statements on the right.

## References

* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Section 5.3.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
-/

public section

open Function Module Topology
open scoped Manifold ContDiff

namespace CategoryTheory.Comma

variable {EA HA A EB HB B ET HT T EJT HJT : Type*}
  [Category A] [Category B] [Category T]
  [NormedAddCommGroup EA] [NormedSpace ℝ EA] [TopologicalSpace HA]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup ET] [NormedSpace ℝ ET] [TopologicalSpace HT]
  [NormedAddCommGroup EJT] [NormedSpace ℝ EJT] [TopologicalSpace HJT]
  {IA : ModelWithCorners ℝ EA HA} {IB : ModelWithCorners ℝ EB HB}
  {IT : ModelWithCorners ℝ ET HT} {JT : ModelWithCorners ℝ EJT HJT}
  [TopologicalSpace A] [ChartedSpace HA A]
  [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace T] [ChartedSpace HT T]
  [TopologicalSpace (Quiver.Total T)] [ChartedSpace HJT (Quiver.Total T)]
  {n : ℕ∞ω} {L : A ⥤ T} {R : B ⥤ T}

local notation "KComma" =>
  𝓘(ℝ, Fin (finrank ℝ (EA × EB) + finrank ℝ EJT - finrank ℝ (ET × ET)) → ℝ)

section Transverse

variable [FiniteDimensional ℝ EA] [FiniteDimensional ℝ EB]
  [FiniteDimensional ℝ ET] [FiniteDimensional ℝ EJT]
  [IA.Boundaryless] [IB.Boundaryless] [IT.Boundaryless] [JT.Boundaryless]
  [IsManifold IA n A] [IsManifold IB n B] [IsManifold IT n T] [IsManifold JT n (Quiver.Total T)]
  (hn : 1 ≤ n)
  (hL : ContMDiff IA IT n L.obj) (hR : ContMDiff IB IT n R.obj)
  (hsT : ContMDiff JT IT n (Quiver.Total.left : Quiver.Total T → T))
  (htT : ContMDiff JT IT n (Quiver.Total.right : Quiver.Total T → T))
  (htrans : ∀ X : Comma L R,
    ∀ (u₁ : TangentSpace IT (L.obj X.left)) (u₂ : TangentSpace IT (R.obj X.right)),
      ∃ (vA : TangentSpace IA X.left) (vB : TangentSpace IB X.right)
        (w : TangentSpace JT (⟨L.obj X.left, R.obj X.right, X.hom⟩ : Quiver.Total T)),
        mfderiv IA IT L.obj X.left vA +
          mfderiv JT IT Quiver.Total.left ⟨_, _, X.hom⟩ w = u₁ ∧
        mfderiv IB IT R.obj X.right vB +
          mfderiv JT IT Quiver.Total.right ⟨_, _, X.hom⟩ w = u₂)

include hn hL hR hsT htT htrans

omit [FiniteDimensional ℝ EA] [FiniteDimensional ℝ EB] [FiniteDimensional ℝ ET]
  [FiniteDimensional ℝ EJT] [IA.Boundaryless] [IB.Boundaryless] [IT.Boundaryless]
  [JT.Boundaryless] [IsManifold IA n A] [IsManifold IB n B] [IsManifold IT n T]
  [IsManifold JT n (Quiver.Total T)] in
/-- Fiberwise transversality on `Comma L R` implies transversality of `Prod.map L.obj R.obj` and
`(left, right) : Quiver.Total T → T × T` along their fiber product. -/
theorem fiberProduct_transverse :
    ∀ p : (A × B) × Quiver.Total T,
      _root_.Prod.map L.obj R.obj p.1 = (p.2.left, p.2.right) →
      (mfderiv (IA.prod IB) (IT.prod IT) (_root_.Prod.map L.obj R.obj) p.1).range ⊔
        (((tangentSpaceCast (IT.prod IT) (p.2.left, p.2.right)
          (_root_.Prod.map L.obj R.obj p.1)).toContinuousLinearMap).comp
            (mfderiv JT (IT.prod IT) (fun d : Quiver.Total T ↦ (d.left, d.right)) p.2)).range =
          ⊤ := by
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  rintro ⟨⟨a, b⟩, ⟨l, r, h⟩⟩ hp
  obtain ⟨rfl, rfl⟩ := _root_.Prod.mk.inj hp
  apply top_unique; rintro ⟨u₁, u₂⟩ -
  obtain ⟨vA, vB, w, hu₁, hu₂⟩ := htrans ⟨a, b, h⟩ u₁ u₂
  refine Submodule.mem_sup.mpr ⟨(mfderiv IA IT L.obj a vA, mfderiv IB IT R.obj b vB),
    ⟨(vA, vB), by rw [mfderiv_prodMap ((hL a).mdifferentiableAt hn0)
      ((hR b).mdifferentiableAt hn0)]; rfl⟩,
    (mfderiv JT IT Quiver.Total.left ⟨L.obj a, R.obj b, h⟩ w,
      mfderiv JT IT Quiver.Total.right ⟨L.obj a, R.obj b, h⟩ w),
    ⟨w, ?_⟩, _root_.Prod.ext hu₁ hu₂⟩
  have hd := mfderiv_prodMk ((hsT ⟨L.obj a, R.obj b, h⟩).mdifferentiableAt hn0)
    ((htT ⟨L.obj a, R.obj b, h⟩).mdifferentiableAt hn0)
  exact congrArg (tangentSpaceCast (IT.prod IT) (L.obj a, R.obj b) (L.obj a, R.obj b))
    (DFunLike.congr_fun hd w)

/-- The `C^n` charted-space structure on `Comma L R`, pulled back from the transverse fiber product
of `Prod.map L.obj R.obj` and `(left, right) : Quiver.Total T → T × T` along
`CategoryTheory.Comma.objectHomeomorph`. -/
@[instance_reducible]
noncomputable def chartedSpaceObjects :
    ChartedSpace (Fin (finrank ℝ (EA × EB) + finrank ℝ EJT - finrank ℝ (ET × ET)) → ℝ)
      (Comma L R) :=
  letI := TauCeti.transverseFiberProductChartedSpace hn (hL.prodMap hR) (hsT.prodMk htT)
    (fiberProduct_transverse hn hL hR hsT htT htrans)
  (objectHomeomorph L R).pullbackChartedSpace

/-- With `chartedSpaceObjects`, `Comma L R` is a `C^n` manifold. -/
theorem isManifold_objects :
    letI := chartedSpaceObjects hn hL hR hsT htT htrans
    IsManifold KComma n (Comma L R) :=
  letI := TauCeti.transverseFiberProductChartedSpace hn (hL.prodMap hR) (hsT.prodMk htT)
    (fiberProduct_transverse hn hL hR hsT htT htrans)
  haveI := TauCeti.isManifold_transverseFiberProduct hn (hL.prodMap hR) (hsT.prodMk htT)
    (fiberProduct_transverse hn hL hR hsT htT htrans)
  (objectHomeomorph L R).pullback_isManifold KComma n

/-- `CategoryTheory.Comma.objectHomeomorph` upgraded to a `C^n` diffeomorphism between `Comma L R`
and the transverse fiber product `(A × B) ×_{T × T} Quiver.Total T`. -/
noncomputable def objectDiffeomorph :
    letI := chartedSpaceObjects hn hL hR hsT htT htrans
    letI := TauCeti.transverseFiberProductChartedSpace hn (hL.prodMap hR) (hsT.prodMk htT)
      (fiberProduct_transverse hn hL hR hsT htT htrans)
    Comma L R ≃ₘ^n⟮KComma, KComma⟯
      {p : (A × B) × Quiver.Total T // _root_.Prod.map L.obj R.obj p.1 = (p.2.left, p.2.right)} :=
  letI := TauCeti.transverseFiberProductChartedSpace hn (hL.prodMap hR) (hsT.prodMk htT)
    (fiberProduct_transverse hn hL hR hsT htT htrans)
  (objectHomeomorph L R).pullbackDiffeomorph KComma n

@[simp]
theorem coe_objectDiffeomorph :
    letI := chartedSpaceObjects hn hL hR hsT htT htrans
    letI := TauCeti.transverseFiberProductChartedSpace hn (hL.prodMap hR) (hsT.prodMk htT)
      (fiberProduct_transverse hn hL hR hsT htT htrans)
    ⇑(objectDiffeomorph hn hL hR hsT htT htrans) = ⇑(objectEquiv L R) := by
  let := TauCeti.transverseFiberProductChartedSpace hn (hL.prodMap hR) (hsT.prodMk htT)
    (fiberProduct_transverse hn hL hR hsT htT htrans)
  simp [objectDiffeomorph, Homeomorph.coe_pullbackDiffeomorph]

@[simp]
theorem coe_objectDiffeomorph_symm :
    letI := chartedSpaceObjects hn hL hR hsT htT htrans
    letI := TauCeti.transverseFiberProductChartedSpace hn (hL.prodMap hR) (hsT.prodMk htT)
      (fiberProduct_transverse hn hL hR hsT htT htrans)
    ⇑(objectDiffeomorph hn hL hR hsT htT htrans).symm = ⇑(objectEquiv L R).symm := by
  let := TauCeti.transverseFiberProductChartedSpace hn (hL.prodMap hR) (hsT.prodMk htT)
    (fiberProduct_transverse hn hL hR hsT htT htrans)
  simp [objectDiffeomorph, Homeomorph.coe_pullbackDiffeomorph_symm]

/-- The coordinate inclusion `X ↦ ((X.left, X.right), ⟨_, _, X.hom⟩)` of `Comma L R` into
`(A × B) × Quiver.Total T` is a `C^n` smooth embedding. -/
theorem isSmoothEmbedding_objects :
    letI := chartedSpaceObjects hn hL hR hsT htT htrans
    Manifold.IsSmoothEmbedding KComma ((IA.prod IB).prod JT) n
      (fun X : Comma L R ↦ ((X.left, X.right), (⟨_, _, X.hom⟩ : Quiver.Total T))) := by
  let := chartedSpaceObjects hn hL hR hsT htT htrans
  have := isManifold_objects hn hL hR hsT htT htrans
  let := TauCeti.transverseFiberProductChartedSpace hn (hL.prodMap hR) (hsT.prodMk htT)
    (fiberProduct_transverse hn hL hR hsT htT htrans)
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
  let := TauCeti.transverseFiberProductChartedSpace hn (hL.prodMap hR) (hsT.prodMk htT)
    (fiberProduct_transverse hn hL hR hsT htT htrans)
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  let e := objectDiffeomorph hn hL hR hsT htT htrans
  have hcomp : (fun Y : Comma L R ↦ ((Y.left, Y.right), (⟨_, _, Y.hom⟩ : Quiver.Total T))) =
      Subtype.val ∘ ⇑e := by funext Y; simp [e, coe_objectDiffeomorph, objectEquiv_apply_coe]
  have hrange := (e.isLocalDiffeomorph X).range_mfderiv_comp
    (K := (IA.prod IB).prod JT) (g := Subtype.val) hn0
  let pX : {p : (A × B) × Quiver.Total T //
      _root_.Prod.map L.obj R.obj p.1 = (p.2.left, p.2.right)} :=
    ⟨((X.left, X.right), ⟨_, _, X.hom⟩), rfl⟩
  have heX : e X = pX := Subtype.ext <| by
    simpa only [pX] using congrFun (coe_objectDiffeomorph hn hL hR hsT htT htrans) X ▸
      objectEquiv_apply_coe L R X
  rw [← hcomp, heX] at hrange
  rw [hrange, TauCeti.mem_range_mfderiv_coe_transverseFiberProduct_iff hn (hL.prodMap hR)
    (hsT.prodMk htT) (fiberProduct_transverse hn hL hR hsT htT htrans) pX v]
  have hL_eq : mfderiv (IA.prod IB) (IT.prod IT) (_root_.Prod.map L.obj R.obj)
      (X.left, X.right) (v.1 : TangentSpace (IA.prod IB) (X.left, X.right)) =
      (mfderiv IA IT L.obj X.left v.1.1, mfderiv IB IT R.obj X.right v.1.2) := by
    rw [mfderiv_prodMap ((hL X.left).mdifferentiableAt hn0) ((hR X.right).mdifferentiableAt hn0)]
    rfl
  have hR_eq : mfderiv JT (IT.prod IT) (fun d : Quiver.Total T ↦ (d.left, d.right))
      ⟨_, _, X.hom⟩ (v.2 : TangentSpace JT (⟨_, _, X.hom⟩ : Quiver.Total T)) =
      (mfderiv JT IT Quiver.Total.left ⟨_, _, X.hom⟩ v.2,
        mfderiv JT IT Quiver.Total.right ⟨_, _, X.hom⟩ v.2) := by
    rw [mfderiv_prodMk ((hsT ⟨_, _, X.hom⟩).mdifferentiableAt hn0)
      ((htT ⟨_, _, X.hom⟩).mdifferentiableAt hn0)]
    rfl
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
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have h₁ := mfderiv_comp X ((hL X.left).mdifferentiableAt hn0)
    (((contMDiff_left hn hL hR hsT htT htrans) X).mdifferentiableAt hn0)
  have h₂ := mfderiv_comp X ((hsT ⟨_, _, X.hom⟩).mdifferentiableAt hn0)
    (((contMDiff_totalHom hn hL hR hsT htT htrans) X).mdifferentiableAt hn0)
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
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have h₁ := mfderiv_comp X ((hR X.right).mdifferentiableAt hn0)
    (((contMDiff_right hn hL hR hsT htT htrans) X).mdifferentiableAt hn0)
  have h₂ := mfderiv_comp X ((htT ⟨_, _, X.hom⟩).mdifferentiableAt hn0)
    (((contMDiff_totalHom hn hL hR hsT htT htrans) X).mdifferentiableAt hn0)
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
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have hΦ := ((isSmoothEmbedding_objects hn hL hR hsT htT htrans).contMDiff X).mdifferentiableAt hn0
  obtain ⟨ξ, hξ⟩ := (mem_range_mfderiv_objects_iff hn hL hR hsT htT htrans X ((vA, vB), w)).2
    ⟨hLw, hRw⟩
  exact ⟨ξ, (hΦ.fst.mfderiv_fst_apply ξ).trans
      ((congrArg _root_.Prod.fst (hΦ.mfderiv_fst_apply ξ)).trans (congrArg (fun z ↦ z.1.1) hξ)),
    (hΦ.fst.mfderiv_snd_apply ξ).trans
      ((congrArg _root_.Prod.snd (hΦ.mfderiv_fst_apply ξ)).trans (congrArg (fun z ↦ z.1.2) hξ)),
    (hΦ.mfderiv_snd_apply ξ).trans (congrArg _root_.Prod.snd hξ)⟩

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
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have hi := isSmoothEmbedding_objects hn hL hR hsT htT htrans
  have hΦ := (hi.contMDiff X).mdifferentiableAt hn0
  refine (injective_iff_map_eq_zero _).1 ((hi.isImmersion.isImmersionAt X).mfderiv_injective hn0)
    ξ (_root_.Prod.ext (_root_.Prod.ext ?_ ?_) (by rwa [hΦ.mfderiv_snd_apply] at h₃))
  · exact (congrArg _root_.Prod.fst (hΦ.mfderiv_fst_apply ξ)).symm.trans
      ((hΦ.fst.mfderiv_fst_apply ξ).symm.trans h₁)
  · exact (congrArg _root_.Prod.snd (hΦ.mfderiv_fst_apply ξ)).symm.trans
      ((hΦ.fst.mfderiv_snd_apply ξ).symm.trans h₂)

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
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
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
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
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
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  refine TauCeti.isLocalDiffeomorph_of_mfderiv_eq
    (contMDiff_left hn hL hR hsT htT htrans) hn fun X ↦ ?_
  have hbij : Bijective (mfderiv KComma IA Comma.left X) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun ξ hξ ↦ ?_, fun vA ↦ ?_⟩
    · have hw0 := (injective_iff_map_eq_zero _).1
        ((hsT_loc ⟨_, _, X.hom⟩).isInvertible_mfderiv hn0).injective _
        ((mfderiv_left_obj_eq hn hL hR hsT htT htrans X ξ).symm.trans
          ((congrArg (mfderiv IA IT L.obj X.left) hξ).trans (map_zero _)))
      have hvB0 := (injective_iff_map_eq_zero _).1
        ((hR_loc X.right).isInvertible_mfderiv hn0).injective _
        ((mfderiv_right_obj_eq hn hL hR hsT htT htrans X ξ).trans
          ((congrArg (mfderiv JT IT Quiver.Total.right ⟨_, _, X.hom⟩) hw0).trans (map_zero _)))
      exact eq_zero_of_mfderiv_comma hn hL hR hsT htT htrans X ξ hξ hvB0 hw0
    · obtain ⟨w, hw⟩ := ((hsT_loc ⟨_, _, X.hom⟩).isInvertible_mfderiv hn0).surjective
        (mfderiv IA IT L.obj X.left vA)
      obtain ⟨vB, hvB⟩ := ((hR_loc X.right).isInvertible_mfderiv hn0).surjective
        (mfderiv JT IT Quiver.Total.right ⟨_, _, X.hom⟩ w)
      obtain ⟨ξ, hξ, -, -⟩ := exists_mfderiv_eq_of_comma hn hL hR hsT htT htrans X vA vB w
        hw.symm hvB
      exact ⟨ξ, hξ⟩
  have : FiniteDimensional ℝ (TangentSpace KComma X) :=
    inferInstanceAs (FiniteDimensional ℝ (Fin _ → ℝ))
  have : FiniteDimensional ℝ (TangentSpace IA X.left) := inferInstanceAs (FiniteDimensional ℝ EA)
  exact ⟨(LinearEquiv.ofBijective (mfderiv KComma IA Comma.left X).toLinearMap
    hbij).toContinuousLinearEquiv, rfl⟩

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
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  refine TauCeti.isLocalDiffeomorph_of_mfderiv_eq
    (contMDiff_right hn hL hR hsT htT htrans) hn fun X ↦ ?_
  have hbij : Bijective (mfderiv KComma IB Comma.right X) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun ξ hξ ↦ ?_, fun vB ↦ ?_⟩
    · have hw0 := (injective_iff_map_eq_zero _).1
        ((htT_loc ⟨_, _, X.hom⟩).isInvertible_mfderiv hn0).injective _
        ((mfderiv_right_obj_eq hn hL hR hsT htT htrans X ξ).symm.trans
          ((congrArg (mfderiv IB IT R.obj X.right) hξ).trans (map_zero _)))
      have hvA0 := (injective_iff_map_eq_zero _).1
        ((hL_loc X.left).isInvertible_mfderiv hn0).injective _
        ((mfderiv_left_obj_eq hn hL hR hsT htT htrans X ξ).trans
          ((congrArg (mfderiv JT IT Quiver.Total.left ⟨_, _, X.hom⟩) hw0).trans (map_zero _)))
      exact eq_zero_of_mfderiv_comma hn hL hR hsT htT htrans X ξ hvA0 hξ hw0
    · obtain ⟨w, hw⟩ := ((htT_loc ⟨_, _, X.hom⟩).isInvertible_mfderiv hn0).surjective
        (mfderiv IB IT R.obj X.right vB)
      obtain ⟨vA, hvA⟩ := ((hL_loc X.left).isInvertible_mfderiv hn0).surjective
        (mfderiv JT IT Quiver.Total.left ⟨_, _, X.hom⟩ w)
      obtain ⟨ξ, -, hξ, -⟩ := exists_mfderiv_eq_of_comma hn hL hR hsT htT htrans X vA vB w
        hvA hw.symm
      exact ⟨ξ, hξ⟩
  have : FiniteDimensional ℝ (TangentSpace KComma X) :=
    inferInstanceAs (FiniteDimensional ℝ (Fin _ → ℝ))
  have : FiniteDimensional ℝ (TangentSpace IB X.right) := inferInstanceAs (FiniteDimensional ℝ EB)
  exact ⟨(LinearEquiv.ofBijective (mfderiv KComma IB Comma.right X).toLinearMap
    hbij).toContinuousLinearEquiv, rfl⟩

end Transverse

section TransversalityCriteria

/-- Surjective differentials of `Quiver.Total.left` on `T` and of `R.obj` guarantee fiberwise
transversality of `Comma L R` for every functor `L : A ⥤ T`. -/
theorem transverse_of_surjective_mfderiv_source_rightObj (L : A ⥤ T)
    (hsT_surj : ∀ c : Quiver.Total T, Surjective (mfderiv JT IT Quiver.Total.left c))
    (hR_surj : ∀ b : B, Surjective (mfderiv IB IT R.obj b)) :
    ∀ X : Comma L R,
      ∀ (u₁ : TangentSpace IT (L.obj X.left)) (u₂ : TangentSpace IT (R.obj X.right)),
        ∃ (vA : TangentSpace IA X.left) (vB : TangentSpace IB X.right)
          (w : TangentSpace JT (⟨L.obj X.left, R.obj X.right, X.hom⟩ : Quiver.Total T)),
          mfderiv IA IT L.obj X.left vA +
            mfderiv JT IT Quiver.Total.left ⟨_, _, X.hom⟩ w = u₁ ∧
          mfderiv IB IT R.obj X.right vB +
            mfderiv JT IT Quiver.Total.right ⟨_, _, X.hom⟩ w = u₂ := fun X u₁ u₂ ↦ by
  obtain ⟨w, hw⟩ := hsT_surj ⟨_, _, X.hom⟩ u₁
  obtain ⟨vB, hvB⟩ := hR_surj X.right (u₂ - mfderiv JT IT Quiver.Total.right ⟨_, _, X.hom⟩ w)
  exact ⟨0, vB, w, by simp [hw], by simp [hvB]⟩

/-- When `Quiver.Total.left` on `T` and `R.obj` are `C^n` submersions (`n ≠ 0`), `Comma L R` is
fiberwise transverse for every functor `L : A ⥤ T`. -/
theorem transverse_of_isSubmersion_source_rightObj (hn : n ≠ 0) (L : A ⥤ T)
    (hsT_sub : Manifold.IsSubmersion JT IT n (Quiver.Total.left : Quiver.Total T → T))
    (hR_sub : Manifold.IsSubmersion IB IT n R.obj) :
    ∀ X : Comma L R,
      ∀ (u₁ : TangentSpace IT (L.obj X.left)) (u₂ : TangentSpace IT (R.obj X.right)),
        ∃ (vA : TangentSpace IA X.left) (vB : TangentSpace IB X.right)
          (w : TangentSpace JT (⟨L.obj X.left, R.obj X.right, X.hom⟩ : Quiver.Total T)),
          mfderiv IA IT L.obj X.left vA +
            mfderiv JT IT Quiver.Total.left ⟨_, _, X.hom⟩ w = u₁ ∧
          mfderiv IB IT R.obj X.right vB +
            mfderiv JT IT Quiver.Total.right ⟨_, _, X.hom⟩ w = u₂ :=
  transverse_of_surjective_mfderiv_source_rightObj L
    (hsT_sub.surjective_mfderiv hn) (hR_sub.surjective_mfderiv hn)

/-- Surjective differentials of `Quiver.Total.right` on `T` and of `L.obj` guarantee fiberwise
transversality of `Comma L R` for every functor `R : B ⥤ T`. -/
theorem transverse_of_surjective_mfderiv_target_leftObj (R : B ⥤ T)
    (htT_surj : ∀ c : Quiver.Total T, Surjective (mfderiv JT IT Quiver.Total.right c))
    (hL_surj : ∀ a : A, Surjective (mfderiv IA IT L.obj a)) :
    ∀ X : Comma L R,
      ∀ (u₁ : TangentSpace IT (L.obj X.left)) (u₂ : TangentSpace IT (R.obj X.right)),
        ∃ (vA : TangentSpace IA X.left) (vB : TangentSpace IB X.right)
          (w : TangentSpace JT (⟨L.obj X.left, R.obj X.right, X.hom⟩ : Quiver.Total T)),
          mfderiv IA IT L.obj X.left vA +
            mfderiv JT IT Quiver.Total.left ⟨_, _, X.hom⟩ w = u₁ ∧
          mfderiv IB IT R.obj X.right vB +
            mfderiv JT IT Quiver.Total.right ⟨_, _, X.hom⟩ w = u₂ := fun X u₁ u₂ ↦ by
  obtain ⟨w, hw⟩ := htT_surj ⟨_, _, X.hom⟩ u₂
  obtain ⟨vA, hvA⟩ := hL_surj X.left (u₁ - mfderiv JT IT Quiver.Total.left ⟨_, _, X.hom⟩ w)
  exact ⟨vA, 0, w, by simp [hvA], by simp [hw]⟩

/-- When `Quiver.Total.right` on `T` and `L.obj` are `C^n` submersions (`n ≠ 0`), `Comma L R` is
fiberwise transverse for every functor `R : B ⥤ T`. -/
theorem transverse_of_isSubmersion_target_leftObj (hn : n ≠ 0) (R : B ⥤ T)
    (htT_sub : Manifold.IsSubmersion JT IT n (Quiver.Total.right : Quiver.Total T → T))
    (hL_sub : Manifold.IsSubmersion IA IT n L.obj) :
    ∀ X : Comma L R,
      ∀ (u₁ : TangentSpace IT (L.obj X.left)) (u₂ : TangentSpace IT (R.obj X.right)),
        ∃ (vA : TangentSpace IA X.left) (vB : TangentSpace IB X.right)
          (w : TangentSpace JT (⟨L.obj X.left, R.obj X.right, X.hom⟩ : Quiver.Total T)),
          mfderiv IA IT L.obj X.left vA +
            mfderiv JT IT Quiver.Total.left ⟨_, _, X.hom⟩ w = u₁ ∧
          mfderiv IB IT R.obj X.right vB +
            mfderiv JT IT Quiver.Total.right ⟨_, _, X.hom⟩ w = u₂ :=
  transverse_of_surjective_mfderiv_target_leftObj R
    (htT_sub.surjective_mfderiv hn) (hL_sub.surjective_mfderiv hn)

end TransversalityCriteria

end CategoryTheory.Comma
