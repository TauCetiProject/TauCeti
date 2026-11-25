/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Comma.WeakPullback
public import TauCeti.Geometry.Manifold.Etale.Functor
public import TauCeti.Geometry.Manifold.Instances.Comap
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Topology.CategoryTheory.Comma
public import TauCeti.Topology.CategoryTheory.Functor.Comma
public import TauCeti.Topology.CategoryTheory.Groupoid.Constructions

import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition

/-!
# Étale arrow manifold of a smooth comma groupoid

When `A`, `B`, and `T` are topological groupoids, `L : A ⥤ T` and `R : B ⥤ T` are topologically
continuous functors, and the source maps of `A` and `B` are local homeomorphisms, the source map
`Quiver.Total.left : Quiver.Total (Comma L R) → Comma L R` of the comma groupoid is also a local
homeomorphism (`CategoryTheory.Comma.isLocalHomeomorph_source_of_isTopologicalGroupoid`). Given any
`C^n` manifold structure on the object space `Comma L R`, pulling back its charts along the source
equips `Quiver.Total (Comma L R)` with a `C^n` manifold structure
(`CategoryTheory.Comma.chartedSpaceArrows`, `CategoryTheory.Comma.isManifold_arrows`) for which
`Quiver.Total.left` is a `C^n` local diffeomorphism
(`CategoryTheory.Comma.isLocalDiffeomorph_source`).

When `Comma L R` embeds smoothly into `(A × B) × Quiver.Total T`, the sources of `A`, `B`, and `T`
are `C^n` local diffeomorphisms, the targets of `A` and `B` are `C^n`, and `L.obj` is `C^n`, the
target map `Quiver.Total.right` on `Comma L R` is also a `C^n` local diffeomorphism
(`CategoryTheory.Comma.isLocalDiffeomorph_target`). Using
`CategoryTheory.Functor.IsTopologicallyContinuous.contMDiff_mapTotal` and
`CategoryTheory.Functor.IsTopologicallyContinuous.isLocalDiffeomorph_mapTotal`, we also record
smooth functoriality of `Comma.fst`, `Comma.snd`, and `Comma.lift` on both objects and total arrows.

## References

* I. Moerdijk, D. A. Pronk, *Orbifolds, sheaves and groupoids*, Section 2.
* I. Moerdijk, J. Mrčun, *Introduction to Foliations and Lie Groupoids*, Section 5.3.
-/

public section

open CategoryTheory Topology TauCeti
open scoped Manifold ContDiff

namespace CategoryTheory.Comma

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {EA HA EJA HJA EB HB EJB HJB ET HT EJT HJT EK HK A B T : Type*}
  [NormedAddCommGroup EA] [NormedSpace 𝕜 EA] [TopologicalSpace HA] {IA : ModelWithCorners 𝕜 EA HA}
  [NormedAddCommGroup EJA] [NormedSpace 𝕜 EJA] [TopologicalSpace HJA]
  {JA : ModelWithCorners 𝕜 EJA HJA}
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  [NormedAddCommGroup EJB] [NormedSpace 𝕜 EJB] [TopologicalSpace HJB]
  {JB : ModelWithCorners 𝕜 EJB HJB}
  [NormedAddCommGroup ET] [NormedSpace 𝕜 ET] [TopologicalSpace HT] {IT : ModelWithCorners 𝕜 ET HT}
  [NormedAddCommGroup EJT] [NormedSpace 𝕜 EJT] [TopologicalSpace HJT]
  {JT : ModelWithCorners 𝕜 EJT HJT}
  [NormedAddCommGroup EK] [NormedSpace 𝕜 EK] [TopologicalSpace HK] {IK : ModelWithCorners 𝕜 EK HK}
  [Category A] [IsGroupoid A] [Category B] [IsGroupoid B] [Category T] [IsGroupoid T]
  {L : A ⥤ T} {R : B ⥤ T}
  [TopologicalSpace A] [TopologicalSpace (Quiver.Total A)] [IsTopologicalGroupoid A]
  [TopologicalSpace B] [TopologicalSpace (Quiver.Total B)] [IsTopologicalGroupoid B]
  [TopologicalSpace T] [TopologicalSpace (Quiver.Total T)] [IsTopologicalGroupoid T]

/-- When `A`, `B`, and `T` are topological groupoids, `L` and `R` are topologically continuous, and
the sources of `A` and `B` are local homeomorphisms, the source map of `Comma L R` is a local
homeomorphism. -/
theorem isLocalHomeomorph_source_of_isTopologicalGroupoid
    (hL_cont : L.IsTopologicallyContinuous) (hR_cont : R.IsTopologicallyContinuous)
    (hsA : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total A → A))
    (hsB : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total B → B)) :
    IsLocalHomeomorph (Quiver.Total.left : Quiver.Total (Comma L R) → Comma L R) :=
  isLocalHomeomorph_source hsA hsB IsTopologicalGroupoid.continuous_target
    IsTopologicalGroupoid.continuous_inverse hL_cont.continuous_mapTotal
    hR_cont.continuous_mapTotal
    (by simpa only [Quiver.Total.comp_def] using (IsTopologicalGroupoid.continuous_comp (C := T)))

section ArrowsChartedSpace

variable [ChartedSpace HK (Comma L R)]

/-- The charted-space structure on `Quiver.Total (Comma L R)` pulled back from `Comma L R` along
the source local homeomorphism. -/
@[instance_reducible]
noncomputable def chartedSpaceArrows
    (hL_cont : L.IsTopologicallyContinuous) (hR_cont : R.IsTopologicallyContinuous)
    (hsA : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total A → A))
    (hsB : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total B → B)) :
    ChartedSpace HK (Quiver.Total (Comma L R)) :=
  (isLocalHomeomorph_source_of_isTopologicalGroupoid hL_cont hR_cont hsA hsB).chartedSpaceComap

/-- When `Comma L R` is a `C^n` manifold, the pulled-back charts on `Quiver.Total (Comma L R)` form
a `C^n` manifold. -/
theorem isManifold_arrows [IsManifold IK n (Comma L R)]
    (hL_cont : L.IsTopologicallyContinuous) (hR_cont : R.IsTopologicallyContinuous)
    (hsA : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total A → A))
    (hsB : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total B → B)) :
    letI := chartedSpaceArrows (HK := HK) hL_cont hR_cont hsA hsB
    IsManifold IK n (Quiver.Total (Comma L R)) :=
  (isLocalHomeomorph_source_of_isTopologicalGroupoid
    hL_cont hR_cont hsA hsB).isManifold_chartedSpaceComap

/-- The source map of `Comma L R` is a `C^n` local diffeomorphism for `chartedSpaceArrows`. -/
theorem isLocalDiffeomorph_source
    (hL_cont : L.IsTopologicallyContinuous) (hR_cont : R.IsTopologicallyContinuous)
    (hsA : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total A → A))
    (hsB : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total B → B)) :
    letI := chartedSpaceArrows (HK := HK) hL_cont hR_cont hsA hsB
    IsLocalDiffeomorph IK IK n (Quiver.Total.left : Quiver.Total (Comma L R) → Comma L R) :=
  (isLocalHomeomorph_source_of_isTopologicalGroupoid
    hL_cont hR_cont hsA hsB).isLocalDiffeomorph_chartedSpaceComap

/-- Any `C^n` manifold structure on `Quiver.Total (Comma L R)` for which `Quiver.Total.left` is a
`C^n` local diffeomorphism is compatible with `chartedSpaceArrows`. -/
theorem compatible_chartedSpaceArrows [IsManifold IK n (Comma L R)]
    (hL_cont : L.IsTopologicallyContinuous) (hR_cont : R.IsTopologicallyContinuous)
    (hsA : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total A → A))
    (hsB : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total B → B))
    [c : ChartedSpace HK (Quiver.Total (Comma L R))]
    [IsManifold IK n (Quiver.Total (Comma L R))]
    (hsc : IsLocalDiffeomorph IK IK n
      (Quiver.Total.left : Quiver.Total (Comma L R) → Comma L R)) :
    ∀ e ∈ c.atlas, ∀ e' ∈ (chartedSpaceArrows (HK := HK) hL_cont hR_cont hsA hsB).atlas,
      e.symm.trans e' ∈ contDiffGroupoid n IK :=
  (isLocalHomeomorph_source_of_isTopologicalGroupoid
    hL_cont hR_cont hsA hsB).compatible_chartedSpaceComap hsc

/-- A map into `Quiver.Total (Comma L R)` is `C^n` iff it is continuous and its composite with the
source map is `C^n`. -/
theorem contMDiff_arrows_iff {EN HN N : Type*}
    [NormedAddCommGroup EN] [NormedSpace 𝕜 EN] [TopologicalSpace HN] {IN : ModelWithCorners 𝕜 EN HN}
    [TopologicalSpace N] [ChartedSpace HN N] {f : N → Quiver.Total (Comma L R)}
    (hL_cont : L.IsTopologicallyContinuous) (hR_cont : R.IsTopologicallyContinuous)
    (hsA : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total A → A))
    (hsB : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total B → B)) :
    letI := chartedSpaceArrows (HK := HK) hL_cont hR_cont hsA hsB
    ContMDiff IN IK n f ↔ Continuous f ∧ ContMDiff IN IK n (Quiver.Total.left ∘ f) :=
  (isLocalHomeomorph_source_of_isTopologicalGroupoid
    hL_cont hR_cont hsA hsB).contMDiff_chartedSpaceComap_iff

section Projections

variable [ChartedSpace HA A] [ChartedSpace HJA (Quiver.Total A)]
  [ChartedSpace HB B] [ChartedSpace HJB (Quiver.Total B)]

omit [ChartedSpace HB B] [ChartedSpace HJB (Quiver.Total B)] in
/-- When `Comma.left` is `C^n` and the source of `A` is a `C^n` local diffeomorphism, `Comma.fst`
is `C^n` on total arrows. -/
theorem contMDiff_fst_mapTotal
    (hL_cont : L.IsTopologicallyContinuous) (hR_cont : R.IsTopologicallyContinuous)
    (hsA : IsLocalDiffeomorph JA IA n (Quiver.Total.left : Quiver.Total A → A))
    (hsB : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total B → B))
    (hleft : ContMDiff IK IA n (Comma.left : Comma L R → A)) :
    letI := chartedSpaceArrows (HK := HK) hL_cont hR_cont hsA.isLocalHomeomorph hsB
    ContMDiff IK JA n (fst L R).toPrefunctor.mapTotal := by
  let := chartedSpaceArrows (HK := HK) hL_cont hR_cont hsA.isLocalHomeomorph hsB
  exact (isTopologicallyContinuous_fst L R).contMDiff_mapTotal
    (isLocalDiffeomorph_source hL_cont hR_cont hsA.isLocalHomeomorph hsB).contMDiff hsA
    (funext (fst_obj L R) ▸ hleft)

omit [ChartedSpace HB B] [ChartedSpace HJB (Quiver.Total B)] in
/-- When `Comma.left` and the source of `A` are `C^n` local diffeomorphisms, `Comma.fst` acts by a
`C^n` local diffeomorphism on total arrows. -/
theorem isLocalDiffeomorph_fst_mapTotal
    (hL_cont : L.IsTopologicallyContinuous) (hR_cont : R.IsTopologicallyContinuous)
    (hsA : IsLocalDiffeomorph JA IA n (Quiver.Total.left : Quiver.Total A → A))
    (hsB : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total B → B))
    (hleft : IsLocalDiffeomorph IK IA n (Comma.left : Comma L R → A)) :
    letI := chartedSpaceArrows (HK := HK) hL_cont hR_cont hsA.isLocalHomeomorph hsB
    IsLocalDiffeomorph IK JA n (fst L R).toPrefunctor.mapTotal := by
  let := chartedSpaceArrows (HK := HK) hL_cont hR_cont hsA.isLocalHomeomorph hsB
  exact (isTopologicallyContinuous_fst L R).isLocalDiffeomorph_mapTotal
    (isLocalDiffeomorph_source hL_cont hR_cont hsA.isLocalHomeomorph hsB) hsA
    (funext (fst_obj L R) ▸ hleft)

omit [ChartedSpace HA A] [ChartedSpace HJA (Quiver.Total A)] in
/-- When `Comma.right` is `C^n` and the source of `B` is a `C^n` local diffeomorphism, `Comma.snd`
is `C^n` on total arrows. -/
theorem contMDiff_snd_mapTotal
    (hL_cont : L.IsTopologicallyContinuous) (hR_cont : R.IsTopologicallyContinuous)
    (hsA : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total A → A))
    (hsB : IsLocalDiffeomorph JB IB n (Quiver.Total.left : Quiver.Total B → B))
    (hright : ContMDiff IK IB n (Comma.right : Comma L R → B)) :
    letI := chartedSpaceArrows (HK := HK) hL_cont hR_cont hsA hsB.isLocalHomeomorph
    ContMDiff IK JB n (snd L R).toPrefunctor.mapTotal := by
  let := chartedSpaceArrows (HK := HK) hL_cont hR_cont hsA hsB.isLocalHomeomorph
  exact (isTopologicallyContinuous_snd L R).contMDiff_mapTotal
    (isLocalDiffeomorph_source hL_cont hR_cont hsA hsB.isLocalHomeomorph).contMDiff hsB
    (funext (snd_obj L R) ▸ hright)

omit [ChartedSpace HA A] [ChartedSpace HJA (Quiver.Total A)] in
/-- When `Comma.right` and the source of `B` are `C^n` local diffeomorphisms, `Comma.snd` acts by a
`C^n` local diffeomorphism on total arrows. -/
theorem isLocalDiffeomorph_snd_mapTotal
    (hL_cont : L.IsTopologicallyContinuous) (hR_cont : R.IsTopologicallyContinuous)
    (hsA : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total A → A))
    (hsB : IsLocalDiffeomorph JB IB n (Quiver.Total.left : Quiver.Total B → B))
    (hright : IsLocalDiffeomorph IK IB n (Comma.right : Comma L R → B)) :
    letI := chartedSpaceArrows (HK := HK) hL_cont hR_cont hsA hsB.isLocalHomeomorph
    IsLocalDiffeomorph IK JB n (snd L R).toPrefunctor.mapTotal := by
  let := chartedSpaceArrows (HK := HK) hL_cont hR_cont hsA hsB.isLocalHomeomorph
  exact (isTopologicallyContinuous_snd L R).isLocalDiffeomorph_mapTotal
    (isLocalDiffeomorph_source hL_cont hR_cont hsA hsB.isLocalHomeomorph) hsB
    (funext (snd_obj L R) ▸ hright)

end Projections

section SmoothEmbedding

variable [ChartedSpace HA A] [ChartedSpace HJA (Quiver.Total A)]
  [ChartedSpace HB B] [ChartedSpace HJB (Quiver.Total B)]
  [ChartedSpace HT T] [ChartedSpace HJT (Quiver.Total T)]

/-- When `Comma L R` embeds smoothly into `(A × B) × Quiver.Total T`, the sources of `A`, `B`, and
`T` are `C^n` local diffeomorphisms, the targets of `A` and `B` are `C^n`, and `L.obj` is `C^n`,
the target map on `Quiver.Total (Comma L R)` is `C^n`. -/
theorem contMDiff_target
    (hL_cont : L.IsTopologicallyContinuous) (hR_cont : R.IsTopologicallyContinuous)
    (hemb : Manifold.IsSmoothEmbedding IK ((IA.prod IB).prod JT) n
      (fun X : Comma L R ↦ ((X.left, X.right), (⟨_, _, X.hom⟩ : Quiver.Total T))))
    (hsA : IsLocalDiffeomorph JA IA n (Quiver.Total.left : Quiver.Total A → A))
    (hsB : IsLocalDiffeomorph JB IB n (Quiver.Total.left : Quiver.Total B → B))
    (htA : ContMDiff JA IA n (Quiver.Total.right : Quiver.Total A → A))
    (htB : ContMDiff JB IB n (Quiver.Total.right : Quiver.Total B → B))
    (hsT : IsLocalDiffeomorph JT IT n (Quiver.Total.left : Quiver.Total T → T))
    (hL_obj : ContMDiff IA IT n L.obj) :
    letI := chartedSpaceArrows (HK := HK) hL_cont hR_cont
      hsA.isLocalHomeomorph hsB.isLocalHomeomorph
    ContMDiff IK IK n (Quiver.Total.right : Quiver.Total (Comma L R) → Comma L R) := by
  let := chartedSpaceArrows (HK := HK) hL_cont hR_cont hsA.isLocalHomeomorph hsB.isLocalHomeomorph
  rw [hemb.contMDiff_iff_comp]
  have hfA : ContMDiff IK IA n (fun f : Quiver.Total (Comma L R) ↦ f.right.left) := by
    simpa only [Function.comp_def, Prefunctor.mapTotal_right, Functor.toPrefunctor_obj, fst_obj]
      using htA.comp (contMDiff_fst_mapTotal hL_cont hR_cont hsA hsB.isLocalHomeomorph
        hemb.contMDiff.fst.fst)
  have hfB : ContMDiff IK IB n (fun f : Quiver.Total (Comma L R) ↦ f.right.right) := by
    simpa only [Function.comp_def, Prefunctor.mapTotal_right, Functor.toPrefunctor_obj, snd_obj]
      using htB.comp (contMDiff_snd_mapTotal hL_cont hR_cont hsA.isLocalHomeomorph hsB
        hemb.contMDiff.fst.snd)
  have hfT : ContMDiff IK JT n
      (fun f : Quiver.Total (Comma L R) ↦ (⟨_, _, f.right.hom⟩ : Quiver.Total T)) :=
    (hL_obj.comp hfA).of_comp_isLocalDiffeomorph hsT
      (continuous_totalHom.comp IsTopologicalGroupoid.continuous_target)
  exact (hfA.prodMk hfB).prodMk hfT

/-- Under the hypotheses of `contMDiff_target`, the target map on `Quiver.Total (Comma L R)` is a
`C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_target
    (hL_cont : L.IsTopologicallyContinuous) (hR_cont : R.IsTopologicallyContinuous)
    (hemb : Manifold.IsSmoothEmbedding IK ((IA.prod IB).prod JT) n
      (fun X : Comma L R ↦ ((X.left, X.right), (⟨_, _, X.hom⟩ : Quiver.Total T))))
    (hsA : IsLocalDiffeomorph JA IA n (Quiver.Total.left : Quiver.Total A → A))
    (hsB : IsLocalDiffeomorph JB IB n (Quiver.Total.left : Quiver.Total B → B))
    (htA : ContMDiff JA IA n (Quiver.Total.right : Quiver.Total A → A))
    (htB : ContMDiff JB IB n (Quiver.Total.right : Quiver.Total B → B))
    (hsT : IsLocalDiffeomorph JT IT n (Quiver.Total.left : Quiver.Total T → T))
    (hL_obj : ContMDiff IA IT n L.obj) :
    letI := chartedSpaceArrows (HK := HK) hL_cont hR_cont
      hsA.isLocalHomeomorph hsB.isLocalHomeomorph
    IsLocalDiffeomorph IK IK n (Quiver.Total.right : Quiver.Total (Comma L R) → Comma L R) := by
  let := chartedSpaceArrows (HK := HK) hL_cont hR_cont hsA.isLocalHomeomorph hsB.isLocalHomeomorph
  -- Inversion is `C^n` and involutive, hence a `C^n` diffeomorphism intertwining source and target.
  have hinv : ContMDiff IK IK n (fun f : Quiver.Total (Comma L R) ↦
      (⟨f.right, f.left, inv f.hom⟩ : Quiver.Total (Comma L R))) :=
    (contMDiff_arrows_iff hL_cont hR_cont hsA.isLocalHomeomorph hsB.isLocalHomeomorph).mpr
      ⟨IsTopologicalGroupoid.continuous_inverse,
        contMDiff_target hL_cont hR_cont hemb hsA hsB htA htB hsT hL_obj⟩
  let e : Quiver.Total (Comma L R) ≃ₘ^n⟮IK, IK⟯ Quiver.Total (Comma L R) :=
    { toFun f := ⟨f.right, f.left, inv f.hom⟩
      invFun f := ⟨f.right, f.left, inv f.hom⟩
      left_inv f := by cases f; simp
      right_inv f := by cases f; simp
      contMDiff_toFun := hinv
      contMDiff_invFun := hinv }
  exact fun f ↦ (e.isLocalDiffeomorph f).comp
    (hg := isLocalDiffeomorph_source hL_cont hR_cont hsA.isLocalHomeomorph hsB.isLocalHomeomorph
      (e f))

section Lift

variable {EW HW EJW HJW W : Type*}
  [NormedAddCommGroup EW] [NormedSpace 𝕜 EW] [TopologicalSpace HW] {IW : ModelWithCorners 𝕜 EW HW}
  [NormedAddCommGroup EJW] [NormedSpace 𝕜 EJW] [TopologicalSpace HJW]
  {JW : ModelWithCorners 𝕜 EJW HJW}
  [Category W] [TopologicalSpace W] [ChartedSpace HW W]

omit [IsGroupoid A] [IsGroupoid B] [IsGroupoid T]
  [TopologicalSpace (Quiver.Total A)] [IsTopologicalGroupoid A] [ChartedSpace HJA (Quiver.Total A)]
  [TopologicalSpace (Quiver.Total B)] [IsTopologicalGroupoid B] [ChartedSpace HJB (Quiver.Total B)]
  [TopologicalSpace T] [ChartedSpace HT T] [IsTopologicalGroupoid T] in
/-- When `Comma L R` embeds smoothly into `(A × B) × Quiver.Total T`, the induced functor
`Comma.lift F₁ F₂ α : W ⥤ Comma L R` is `C^n` on objects if and only if `F₁.obj`, `F₂.obj`, and
`w ↦ ⟨_, _, α.app w⟩` are `C^n`. -/
theorem contMDiff_lift_obj_iff (F₁ : W ⥤ A) (F₂ : W ⥤ B) (α : F₁ ⋙ L ⟶ F₂ ⋙ R)
    (hemb : Manifold.IsSmoothEmbedding IK ((IA.prod IB).prod JT) n
      (fun X : Comma L R ↦ ((X.left, X.right), (⟨_, _, X.hom⟩ : Quiver.Total T)))) :
    ContMDiff IW IK n (Comma.lift F₁ F₂ α).obj ↔
      ContMDiff IW IA n F₁.obj ∧ ContMDiff IW IB n F₂.obj ∧
      ContMDiff IW JT n (fun w : W ↦ (⟨_, _, α.app w⟩ : Quiver.Total T)) := by
  rw [hemb.contMDiff_iff_comp]
  simp only [Function.comp_def, lift_obj_left, lift_obj_right, lift_obj_hom]
  exact ⟨fun h ↦ ⟨h.fst.fst, h.fst.snd, h.snd⟩, fun ⟨h₁, h₂, h₃⟩ ↦ (h₁.prodMk h₂).prodMk h₃⟩

omit [ChartedSpace HJA (Quiver.Total A)] [ChartedSpace HJB (Quiver.Total B)]
  [ChartedSpace HT T] in
/-- When `Comma L R` embeds smoothly into `(A × B) × Quiver.Total T` and `F₁`, `F₂` are
topologically continuous with `C^n` object maps and `C^n` natural transformation `α`, `Comma.lift`
is `C^n` on total arrows whenever `W` has `C^n` source and continuous target. -/
theorem contMDiff_lift_mapTotal [TopologicalSpace (Quiver.Total W)]
    [ChartedSpace HJW (Quiver.Total W)]
    {F₁ : W ⥤ A} {F₂ : W ⥤ B} {α : F₁ ⋙ L ⟶ F₂ ⋙ R}
    (hL_cont : L.IsTopologicallyContinuous) (hR_cont : R.IsTopologicallyContinuous)
    (hemb : Manifold.IsSmoothEmbedding IK ((IA.prod IB).prod JT) n
      (fun X : Comma L R ↦ ((X.left, X.right), (⟨_, _, X.hom⟩ : Quiver.Total T))))
    (hsA : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total A → A))
    (hsB : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total B → B))
    (hsW : ContMDiff JW IW n (Quiver.Total.left : Quiver.Total W → W))
    (htW : Continuous (Quiver.Total.right : Quiver.Total W → W))
    (hF₁_cont : F₁.IsTopologicallyContinuous) (hF₂_cont : F₂.IsTopologicallyContinuous)
    (hF₁ : ContMDiff IW IA n F₁.obj) (hF₂ : ContMDiff IW IB n F₂.obj)
    (hα : ContMDiff IW JT n (fun w : W ↦ (⟨_, _, α.app w⟩ : Quiver.Total T))) :
    letI := chartedSpaceArrows (HK := HK) hL_cont hR_cont hsA hsB
    ContMDiff JW IK n (Comma.lift F₁ F₂ α).toPrefunctor.mapTotal := by
  let := chartedSpaceArrows (HK := HK) hL_cont hR_cont hsA hsB
  exact ((isTopologicallyContinuous_lift_iff hsW.continuous htW F₁ F₂ α).mpr
    ⟨hF₁_cont, hF₂_cont, hα.continuous⟩).contMDiff_mapTotal hsW
      (isLocalDiffeomorph_source hL_cont hR_cont hsA hsB)
      ((contMDiff_lift_obj_iff F₁ F₂ α hemb).mpr ⟨hF₁, hF₂, hα⟩)

end Lift

end SmoothEmbedding

end ArrowsChartedSpace

end CategoryTheory.Comma
