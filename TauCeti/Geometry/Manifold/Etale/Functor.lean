/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Combinatorics.Quiver.Prefunctor

import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition

/-!
# Smoothness and local diffeomorphicity of functors into étale categories

For a functor `F : C ⥤ D` between categories whose objects and total arrows (`Quiver.Total`) are
charted spaces, the source projection intertwines the arrow and object maps via
`Quiver.Total.left ∘ F.toPrefunctor.mapTotal = F.obj ∘ Quiver.Total.left`. When
`F.toPrefunctor.mapTotal` is continuous and the target source map
`Quiver.Total.left : Quiver.Total D → D` is a `C^n` local diffeomorphism, cancelling that local
diffeomorphism upgrades regularity of `F.obj` on objects to regularity of `F.toPrefunctor.mapTotal`
on total arrows:

* `CategoryTheory.Functor.contMDiff_mapTotal`: `F.toPrefunctor.mapTotal` is `C^n` whenever `F.obj`
  and the source map of `C` are `C^n`.
* `CategoryTheory.Functor.isLocalDiffeomorph_mapTotal`: `F.toPrefunctor.mapTotal` is a `C^n` local
  diffeomorphism whenever `F.obj` and the source map of `C` are `C^n` local diffeomorphisms.

## References

* I. Moerdijk, D. A. Pronk, *Orbifolds, sheaves and groupoids*, Section 2.
* I. Moerdijk, J. Mrčun, *Introduction to Foliations and Lie Groupoids*, Section 5.1.
-/

public section

open CategoryTheory Topology TauCeti
open scoped Manifold ContDiff

namespace CategoryTheory.Functor

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {EC HC EJC HJC ED HD EJD HJD C D : Type*}
  [NormedAddCommGroup EC] [NormedSpace 𝕜 EC] [TopologicalSpace HC] {IC : ModelWithCorners 𝕜 EC HC}
  [NormedAddCommGroup EJC] [NormedSpace 𝕜 EJC] [TopologicalSpace HJC]
  {JC : ModelWithCorners 𝕜 EJC HJC}
  [NormedAddCommGroup ED] [NormedSpace 𝕜 ED] [TopologicalSpace HD] {ID : ModelWithCorners 𝕜 ED HD}
  [NormedAddCommGroup EJD] [NormedSpace 𝕜 EJD] [TopologicalSpace HJD]
  {JD : ModelWithCorners 𝕜 EJD HJD}
  [Category C] [Category D]
  [TopologicalSpace C] [ChartedSpace HC C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace HJC (Quiver.Total C)]
  [TopologicalSpace D] [ChartedSpace HD D]
  [TopologicalSpace (Quiver.Total D)] [ChartedSpace HJD (Quiver.Total D)]

/-- A functor `F : C ⥤ D` continuous on total arrows into a category whose source map is a `C^n`
local diffeomorphism acts as a `C^n` map on total arrows whenever `F.obj` and the source map of `C`
are `C^n`. -/
theorem contMDiff_mapTotal (F : C ⥤ D) (hF_cont : Continuous F.toPrefunctor.mapTotal)
    (hsC : ContMDiff JC IC n (Quiver.Total.left : Quiver.Total C → C))
    (hsD : IsLocalDiffeomorph JD ID n (Quiver.Total.left : Quiver.Total D → D))
    (hF : ContMDiff IC ID n F.obj) :
    ContMDiff JC JD n F.toPrefunctor.mapTotal := by
  refine ContMDiff.of_comp_isLocalDiffeomorph hsD hF_cont ?_
  simpa only [Function.comp_def, Prefunctor.mapTotal_left, Functor.toPrefunctor_obj] using
    hF.comp hsC

/-- A functor `F : C ⥤ D` continuous on total arrows between categories whose source maps are `C^n`
local diffeomorphisms acts by a `C^n` local diffeomorphism on total arrows whenever `F.obj` is a
`C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_mapTotal (F : C ⥤ D) (hF_cont : Continuous F.toPrefunctor.mapTotal)
    (hsC : IsLocalDiffeomorph JC IC n (Quiver.Total.left : Quiver.Total C → C))
    (hsD : IsLocalDiffeomorph JD ID n (Quiver.Total.left : Quiver.Total D → D))
    (hF : IsLocalDiffeomorph IC ID n F.obj) :
    IsLocalDiffeomorph JC JD n F.toPrefunctor.mapTotal := fun a ↦ by
  refine IsLocalDiffeomorphAt.of_comp_left ?_ (hsD _) hF_cont.continuousAt
  simpa only [Function.comp_def, Prefunctor.mapTotal_left, Functor.toPrefunctor_obj] using
    (hsC a).comp (hg := hF a.left)

end CategoryTheory.Functor
