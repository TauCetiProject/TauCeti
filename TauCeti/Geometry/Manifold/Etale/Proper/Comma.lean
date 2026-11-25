/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Etale.Comma
public import TauCeti.Geometry.Manifold.Etale.Proper.Basic
public import TauCeti.Geometry.Manifold.Groupoid.Comma

/-!
# Proper étale Lie groupoid presentations of weak fiber products

When `A` and `B` are proper étale Lie groupoid presentations (`TauCeti.IsProperEtaleGroupoid`), `T`
is an étale Lie groupoid with Hausdorff total arrows, and `L : A ⥤ T` and `R : B ⥤ T` are smooth on
objects, continuous on total arrows, and fiberwise transverse
(`CategoryTheory.Comma.IsFiberwiseTransverse`), the comma groupoid `Comma L R` equipped with
`CategoryTheory.Comma.chartedSpaceObjects` and `CategoryTheory.Comma.chartedSpaceArrows` is itself a
Hausdorff proper étale Lie groupoid presentation (`CategoryTheory.Comma.isProperEtaleGroupoid`),
with no properness hypothesis required on `T` or on the functors `L` and `R`.

In particular, fiberwise transversality holds automatically whenever `R.obj` or `L.obj` is a smooth
submersion (`CategoryTheory.Comma.isProperEtaleGroupoid_of_isSubmersion_right`,
`CategoryTheory.Comma.isProperEtaleGroupoid_of_isSubmersion_left`).

## References

* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Section 5.3.
* I. Moerdijk, [*Orbifolds as groupoids: an introduction*](https://arxiv.org/abs/math/0203100),
  Section 2.3.
-/

public section

open Function Module Topology TauCeti
open scoped Manifold ContDiff

namespace CategoryTheory.Comma

variable {EA HA EJA HJA A EB HB EJB HJB B ET HT EJT HJT T : Type*}
  [Category A] [IsGroupoid A] [Category B] [IsGroupoid B] [Category T] [IsGroupoid T]
  [NormedAddCommGroup EA] [NormedSpace ℝ EA] [FiniteDimensional ℝ EA] [TopologicalSpace HA]
  [NormedAddCommGroup EJA] [NormedSpace ℝ EJA] [FiniteDimensional ℝ EJA] [TopologicalSpace HJA]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup EJB] [NormedSpace ℝ EJB] [FiniteDimensional ℝ EJB] [TopologicalSpace HJB]
  [NormedAddCommGroup ET] [NormedSpace ℝ ET] [FiniteDimensional ℝ ET] [TopologicalSpace HT]
  [NormedAddCommGroup EJT] [NormedSpace ℝ EJT] [FiniteDimensional ℝ EJT] [TopologicalSpace HJT]
  {IA : ModelWithCorners ℝ EA HA} {JA : ModelWithCorners ℝ EJA HJA}
  {IB : ModelWithCorners ℝ EB HB} {JB : ModelWithCorners ℝ EJB HJB}
  {IT : ModelWithCorners ℝ ET HT} {JT : ModelWithCorners ℝ EJT HJT}
  [IA.Boundaryless] [JA.Boundaryless] [IB.Boundaryless] [JB.Boundaryless]
  [IT.Boundaryless] [JT.Boundaryless]
  [TopologicalSpace A] [ChartedSpace HA A] [IsManifold IA ∞ A]
  [TopologicalSpace (Quiver.Total A)] [ChartedSpace HJA (Quiver.Total A)]
  [IsManifold JA ∞ (Quiver.Total A)] [IsProperEtaleGroupoid IA JA A]
  [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  [TopologicalSpace (Quiver.Total B)] [ChartedSpace HJB (Quiver.Total B)]
  [IsManifold JB ∞ (Quiver.Total B)] [IsProperEtaleGroupoid IB JB B]
  [TopologicalSpace T] [ChartedSpace HT T] [IsManifold IT ∞ T]
  [TopologicalSpace (Quiver.Total T)] [ChartedSpace HJT (Quiver.Total T)]
  [IsManifold JT ∞ (Quiver.Total T)] [IsLieGroupoid IT JT T] [T2Space (Quiver.Total T)]
  {L : A ⥤ T} {R : B ⥤ T}

local notation "HComma" => Fin (finrank ℝ (EA × EB) + finrank ℝ EJT - finrank ℝ (ET × ET)) → ℝ
local notation "KComma" => 𝓘(ℝ, HComma)

/-- **Proper étale weak fiber product.** When `A` and `B` are proper étale Lie groupoid
presentations, `T` is an étale Lie groupoid with Hausdorff arrows, and `L : A ⥤ T`, `R : B ⥤ T` are
smooth on objects, continuous on total arrows, and fiberwise transverse, `Comma L R` is a proper
étale Lie groupoid presentation. -/
theorem isProperEtaleGroupoid
    (hsT : IsLocalDiffeomorph JT IT ∞ (Quiver.Total.left : Quiver.Total T → T))
    (hL_obj : ContMDiff IA IT ∞ L.obj) (hR_obj : ContMDiff IB IT ∞ R.obj)
    (hL : Continuous L.toPrefunctor.mapTotal) (hR : Continuous R.toPrefunctor.mapTotal)
    (htrans : IsFiberwiseTransverse IA IB IT JT L R) :
    let := IsLieGroupoid.isTopologicalGroupoid IA JA A
    let := IsLieGroupoid.isTopologicalGroupoid IB JB B
    let := IsLieGroupoid.isTopologicalGroupoid IT JT T
    let := chartedSpaceObjects (n := ∞) (by simp) hL_obj hR_obj
      (IsLieGroupoid.contMDiff_source IT JT T) (IsLieGroupoid.contMDiff_target IT JT T) htrans
    let : IsManifold KComma ∞ (Comma L R) :=
      isManifold_objects (n := ∞) (by simp) hL_obj hR_obj
        (IsLieGroupoid.contMDiff_source IT JT T) (IsLieGroupoid.contMDiff_target IT JT T) htrans
    let := chartedSpaceArrows (HK := HComma) hL hR
      (IsProperEtaleGroupoid.isLocalDiffeomorph_source (I := IA) (J := JA)).isLocalHomeomorph
      (IsProperEtaleGroupoid.isLocalDiffeomorph_source (I := IB) (J := JB)).isLocalHomeomorph
    let : IsManifold KComma ∞ (Quiver.Total (Comma L R)) :=
      isManifold_arrows (IK := KComma) (n := ∞) hL hR
        (IsProperEtaleGroupoid.isLocalDiffeomorph_source (I := IA) (J := JA)).isLocalHomeomorph
        (IsProperEtaleGroupoid.isLocalDiffeomorph_source (I := IB) (J := JB)).isLocalHomeomorph
    IsProperEtaleGroupoid KComma KComma (Comma L R) := by
  intro _ _ _ _ _ _ _
  have := IsLieGroupoid.t2Space_objects (I := IA) (J := JA) (C := A)
  have := IsLieGroupoid.t2Space_objects (I := IB) (J := JB) (C := B)
  have := IsProperEtaleGroupoid.t2Space_arrows (I := IA) (J := JA) (C := A)
  have := IsProperEtaleGroupoid.t2Space_arrows (I := IB) (J := JB) (C := B)
  have := IsLieGroupoid.secondCountableTopology_objects IA JA A
  have := IsLieGroupoid.secondCountableTopology_objects IB JB B
  have := IsLieGroupoid.secondCountableTopology_arrows (I := IA) (J := JA) (C := A)
  have := IsLieGroupoid.secondCountableTopology_arrows (I := IB) (J := JB) (C := B)
  have := IsLieGroupoid.secondCountableTopology_arrows (I := IT) (J := JT) (C := T)
  have hsA := IsProperEtaleGroupoid.isLocalDiffeomorph_source (I := IA) (J := JA) (C := A)
  have hsB := IsProperEtaleGroupoid.isLocalDiffeomorph_source (I := IB) (J := JB) (C := B)
  have hemb := isSmoothEmbedding_objects (n := ∞) (by simp) hL_obj hR_obj
    (IsLieGroupoid.contMDiff_source IT JT T) (IsLieGroupoid.contMDiff_target IT JT T) htrans
  exact
    { toIsLieGroupoid := isLieGroupoid hL hR hemb hsA hsB
        (IsLieGroupoid.contMDiff_target IA JA A) (IsLieGroupoid.contMDiff_target IB JB B)
        hsT hL_obj
      isLocalDiffeomorph_source := isLocalDiffeomorph_source (IK := KComma) (n := ∞) hL hR
        hsA.isLocalHomeomorph hsB.isLocalHomeomorph
      isProperMap_source_target := isProperMap_source_target
        (IsProperEtaleGroupoid.isProperMap_source_target (I := IA) (J := JA))
        (IsProperEtaleGroupoid.isProperMap_source_target (I := IB) (J := JB)) hL hR
        (by simpa only [Quiver.Total.comp_def] using
          (IsTopologicalGroupoid.continuous_comp (C := T))) }

/-- When `R.obj` is a smooth submersion, fiberwise transversality holds automatically and
`Comma L R` is a proper étale Lie groupoid presentation. -/
theorem isProperEtaleGroupoid_of_isSubmersion_right
    (hsT : IsLocalDiffeomorph JT IT ∞ (Quiver.Total.left : Quiver.Total T → T))
    (hL_obj : ContMDiff IA IT ∞ L.obj) (hR_sub : Manifold.IsSubmersion IB IT ∞ R.obj)
    (hL : Continuous L.toPrefunctor.mapTotal) (hR : Continuous R.toPrefunctor.mapTotal) :
    let := IsLieGroupoid.isTopologicalGroupoid IA JA A
    let := IsLieGroupoid.isTopologicalGroupoid IB JB B
    let := IsLieGroupoid.isTopologicalGroupoid IT JT T
    let htrans := isFiberwiseTransverse_of_isSubmersion_source_rightObj (n := ∞) (by simp) L
      (IsLieGroupoid.isSubmersion_source (I := IT) (J := JT) (C := T)) hR_sub
    let := chartedSpaceObjects (n := ∞) (by simp) hL_obj hR_sub.contMDiff
      (IsLieGroupoid.contMDiff_source IT JT T) (IsLieGroupoid.contMDiff_target IT JT T) htrans
    let : IsManifold KComma ∞ (Comma L R) :=
      isManifold_objects (n := ∞) (by simp) hL_obj hR_sub.contMDiff
        (IsLieGroupoid.contMDiff_source IT JT T) (IsLieGroupoid.contMDiff_target IT JT T) htrans
    let := chartedSpaceArrows (HK := HComma) hL hR
      (IsProperEtaleGroupoid.isLocalDiffeomorph_source (I := IA) (J := JA)).isLocalHomeomorph
      (IsProperEtaleGroupoid.isLocalDiffeomorph_source (I := IB) (J := JB)).isLocalHomeomorph
    let : IsManifold KComma ∞ (Quiver.Total (Comma L R)) :=
      isManifold_arrows (IK := KComma) (n := ∞) hL hR
        (IsProperEtaleGroupoid.isLocalDiffeomorph_source (I := IA) (J := JA)).isLocalHomeomorph
        (IsProperEtaleGroupoid.isLocalDiffeomorph_source (I := IB) (J := JB)).isLocalHomeomorph
    IsProperEtaleGroupoid KComma KComma (Comma L R) :=
  isProperEtaleGroupoid (JA := JA) (JB := JB) hsT hL_obj hR_sub.contMDiff hL hR
    (isFiberwiseTransverse_of_isSubmersion_source_rightObj (n := ∞) (by simp) L
      (IsLieGroupoid.isSubmersion_source (I := IT) (J := JT) (C := T)) hR_sub)

/-- When `L.obj` is a smooth submersion, fiberwise transversality holds automatically and
`Comma L R` is a proper étale Lie groupoid presentation. -/
theorem isProperEtaleGroupoid_of_isSubmersion_left
    (hsT : IsLocalDiffeomorph JT IT ∞ (Quiver.Total.left : Quiver.Total T → T))
    (hL_sub : Manifold.IsSubmersion IA IT ∞ L.obj) (hR_obj : ContMDiff IB IT ∞ R.obj)
    (hL : Continuous L.toPrefunctor.mapTotal) (hR : Continuous R.toPrefunctor.mapTotal) :
    let := IsLieGroupoid.isTopologicalGroupoid IA JA A
    let := IsLieGroupoid.isTopologicalGroupoid IB JB B
    let := IsLieGroupoid.isTopologicalGroupoid IT JT T
    let htrans := isFiberwiseTransverse_of_isSubmersion_target_leftObj (n := ∞) (by simp) R
      (IsLieGroupoid.isSubmersion_target IT JT T) hL_sub
    let := chartedSpaceObjects (n := ∞) (by simp) hL_sub.contMDiff hR_obj
      (IsLieGroupoid.contMDiff_source IT JT T) (IsLieGroupoid.contMDiff_target IT JT T) htrans
    let : IsManifold KComma ∞ (Comma L R) :=
      isManifold_objects (n := ∞) (by simp) hL_sub.contMDiff hR_obj
        (IsLieGroupoid.contMDiff_source IT JT T) (IsLieGroupoid.contMDiff_target IT JT T) htrans
    let := chartedSpaceArrows (HK := HComma) hL hR
      (IsProperEtaleGroupoid.isLocalDiffeomorph_source (I := IA) (J := JA)).isLocalHomeomorph
      (IsProperEtaleGroupoid.isLocalDiffeomorph_source (I := IB) (J := JB)).isLocalHomeomorph
    let : IsManifold KComma ∞ (Quiver.Total (Comma L R)) :=
      isManifold_arrows (IK := KComma) (n := ∞) hL hR
        (IsProperEtaleGroupoid.isLocalDiffeomorph_source (I := IA) (J := JA)).isLocalHomeomorph
        (IsProperEtaleGroupoid.isLocalDiffeomorph_source (I := IB) (J := JB)).isLocalHomeomorph
    IsProperEtaleGroupoid KComma KComma (Comma L R) :=
  isProperEtaleGroupoid (JA := JA) (JB := JB) hsT hL_sub.contMDiff hR_obj hL hR
    (isFiberwiseTransverse_of_isSubmersion_target_leftObj (n := ∞) (by simp) R
      (IsLieGroupoid.isSubmersion_target IT JT T) hL_sub)

end CategoryTheory.Comma
