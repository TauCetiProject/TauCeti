/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Groupoid.LieGroupoid
public import TauCeti.Geometry.Manifold.PullbackGroupoid
public import TauCeti.Topology.CategoryTheory.Groupoid.Examples
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph

/-!
# Smooth unit and pair groupoids

Given a `C^n` manifold `N`, the unit groupoid `Discrete N` inherits `C^n` manifold structures on
objects and total arrows by pulling charts back along `TauCeti.UnitGroupoid.objectHomeomorph` and
`TauCeti.UnitGroupoid.arrowHomeomorph` (`Homeomorph.pullbackChartedSpace`), making source and target
global (hence local) `C^n` diffeomorphisms (`TauCeti.UnitGroupoid.sourceDiffeomorph`,
`TauCeti.UnitGroupoid.isLocalDiffeomorph_source`, `TauCeti.UnitGroupoid.isLocalDiffeomorph_target`).
Likewise the pair groupoid `Codiscrete N` has objects `C^n` diffeomorphic to `N` and total arrows
`C^n` diffeomorphic to `N × N`, in (target, source) coordinates
(`TauCeti.PairGroupoid.objectDiffeomorph`, `TauCeti.PairGroupoid.arrowDiffeomorph`).

Over a Hausdorff second-countable smooth manifold with a boundaryless finite-dimensional real
model, both are Lie groupoids (`TauCeti.UnitGroupoid.lieGroupoid`,
`TauCeti.PairGroupoid.lieGroupoid`); the source fibres of the pair groupoid are copies of `N`.
The unit groupoid is étale, while the arrow manifold of the pair groupoid has twice the dimension
of its object manifold.

## Main declarations

* `TauCeti.UnitGroupoid.instChartedSpaceObjects`, `TauCeti.UnitGroupoid.instIsManifoldObjects`,
  `TauCeti.UnitGroupoid.objectDiffeomorph`: `C^n` manifold structure on `Discrete N` and
  `Discrete N ≃ₘ^n⟮I, I⟯ N`.
* `TauCeti.UnitGroupoid.instChartedSpaceArrows`, `TauCeti.UnitGroupoid.instIsManifoldArrows`,
  `TauCeti.UnitGroupoid.arrowDiffeomorph`: `C^n` manifold structure on `Quiver.Total (Discrete N)`
  and `Quiver.Total (Discrete N) ≃ₘ^n⟮I, I⟯ N`.
* `TauCeti.UnitGroupoid.sourceDiffeomorph`, `TauCeti.UnitGroupoid.isLocalDiffeomorph_source`,
  `TauCeti.UnitGroupoid.isLocalDiffeomorph_target`: source diffeomorphism and local diffeomorphisms.
* `TauCeti.PairGroupoid.objectDiffeomorph`, `TauCeti.PairGroupoid.arrowDiffeomorph`: the `C^n`
  manifold structures on `Codiscrete N` and on its total arrows.
* `TauCeti.UnitGroupoid.lieGroupoid`, `TauCeti.PairGroupoid.lieGroupoid`: the unit and pair
  groupoids are Lie groupoids.

## References

* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Section 5.1.
-/

public section

open CategoryTheory Topology
open scoped Manifold ContDiff

namespace TauCeti.UnitGroupoid

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]

/-- Objects of `Discrete N` carry the charted-space structure pulled back from `N`. -/
instance instChartedSpaceObjects : ChartedSpace H (Discrete N) :=
  (objectHomeomorph N).pullbackChartedSpace

/-- Objects of `Discrete N` form a `C^n` manifold whenever `N` does. -/
instance instIsManifoldObjects (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) [IsManifold I n N] :
    IsManifold I n (Discrete N) :=
  (objectHomeomorph N).pullback_isManifold I n

/-- Forgetting the categorical wrapper on `Discrete N` as a `C^n` diffeomorphism. -/
def objectDiffeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (N : Type*) [TopologicalSpace N] [ChartedSpace H N] : Discrete N ≃ₘ^n⟮I, I⟯ N :=
  (objectHomeomorph N).pullbackDiffeomorph I n

@[simp]
theorem objectDiffeomorph_apply (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) (x : Discrete N) :
    objectDiffeomorph I n N x = x.as := by simp [objectDiffeomorph]

@[simp]
theorem objectDiffeomorph_symm_apply (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) (x : N) :
    (objectDiffeomorph I n N).symm x = Discrete.mk x := by simp [objectDiffeomorph]

@[simp]
theorem objectDiffeomorph_toHomeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    (objectDiffeomorph I n N).toHomeomorph = objectHomeomorph N := by simp [objectDiffeomorph]

/-- Total arrows of `Discrete N` carry the charted-space structure pulled back from `N` along
`arrowHomeomorph`. -/
instance instChartedSpaceArrows : ChartedSpace H (Quiver.Total (Discrete N)) :=
  (arrowHomeomorph N).pullbackChartedSpace

/-- Total arrows of `Discrete N` form a `C^n` manifold whenever `N` does. -/
instance instIsManifoldArrows (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) [IsManifold I n N] :
    IsManifold I n (Quiver.Total (Discrete N)) :=
  (arrowHomeomorph N).pullback_isManifold I n

/-- The total-arrow space of `Discrete N` is `C^n` diffeomorphic to `N`. -/
def arrowDiffeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (N : Type*) [TopologicalSpace N] [ChartedSpace H N] : Quiver.Total (Discrete N) ≃ₘ^n⟮I, I⟯ N :=
  (arrowHomeomorph N).pullbackDiffeomorph I n

@[simp]
theorem arrowDiffeomorph_apply (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (a : Quiver.Total (Discrete N)) : arrowDiffeomorph I n N a = a.left.as := by
  simp [arrowDiffeomorph]

@[simp]
theorem arrowDiffeomorph_symm_apply (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) (x : N) :
    (arrowDiffeomorph I n N).symm x = ⟨⟨x⟩, ⟨x⟩, 𝟙 _⟩ := by simp [arrowDiffeomorph]

@[simp]
theorem arrowDiffeomorph_toHomeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    (arrowDiffeomorph I n N).toHomeomorph = arrowHomeomorph N := by simp [arrowDiffeomorph]

/-- The source map of `Discrete N` as a global `C^n` diffeomorphism. -/
def sourceDiffeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (N : Type*) [TopologicalSpace N] [ChartedSpace H N] :
    Quiver.Total (Discrete N) ≃ₘ^n⟮I, I⟯ Discrete N :=
  (arrowDiffeomorph I n N).trans (objectDiffeomorph I n N).symm

@[simp]
theorem coe_sourceDiffeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    ⇑(sourceDiffeomorph I n N) = (Quiver.Total.left : Quiver.Total (Discrete N) → Discrete N) :=
  funext fun _ ↦ by simp [sourceDiffeomorph]

@[simp]
theorem coe_sourceDiffeomorph_symm (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    ⇑(sourceDiffeomorph I n N).symm =
      fun x : Discrete N ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total (Discrete N)) :=
  funext fun _ ↦ (sourceDiffeomorph I n N).injective (by simp)

/-- The source map of `Discrete N` is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_source {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω} :
    IsLocalDiffeomorph I I n (Quiver.Total.left : Quiver.Total (Discrete N) → Discrete N) :=
  coe_sourceDiffeomorph I n (N := N) ▸ (sourceDiffeomorph I n N).isLocalDiffeomorph

/-- The target map of `Discrete N` is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_target {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω} :
    IsLocalDiffeomorph I I n (Quiver.Total.right : Quiver.Total (Discrete N) → Discrete N) :=
  target_eq_source N ▸ isLocalDiffeomorph_source

end TauCeti.UnitGroupoid

namespace TauCeti.UnitGroupoid

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] in
private theorem contMDiff_arrow :
    ContMDiff I I ∞ fun a : Quiver.Total (Discrete N) ↦ a.left.as := by
  simpa only [← funext (arrowDiffeomorph_apply I ∞ (N := N))] using
    (arrowDiffeomorph I ∞ N).contMDiff

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
private theorem isSubmersion_source :
    Manifold.IsSubmersion I I ∞ (Quiver.Total.left : Quiver.Total (Discrete N) → Discrete N) := by
  simpa using (sourceDiffeomorph I ∞ N).isLocalDiffeomorph.comp_isSubmersion
    (Manifold.IsSubmersion.id (I := I) (n := ∞) (M := Quiver.Total (Discrete N)))

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] in
private theorem contMDiff_inverse : ContMDiff I I ∞ fun a : Quiver.Total (Discrete N) ↦
    (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total (Discrete N)) := by
  refine ((arrowDiffeomorph I ∞ N).contMDiff_diffeomorph_comp_iff le_rfl).1 ?_
  simpa [Function.comp_def] using contMDiff_arrow (I := I) (N := N)

/-- The unit groupoid of a Hausdorff second-countable smooth manifold is a Lie groupoid. Its arrow
manifold is the object manifold, every structure map is the identity in these coordinates, and its
source fibres are points. -/
instance lieGroupoid [T2Space N] [SecondCountableTopology N] : LieGroupoid I I (Discrete N) where
  isSubmersion_source := isSubmersion_source
  contMDiff_unit :=
    coe_sourceDiffeomorph_symm I ∞ (N := N) ▸ (sourceDiffeomorph I ∞ N).symm.contMDiff
  contMDiff_inverse := contMDiff_inverse
  -- An arrow of the unit groupoid is determined by its source, so composition is the first
  -- projection.
  contMDiff_comp := contMDiff_composablePairs_comp_of_eq isSubmersion_source contMDiff_inverse
    contMDiff_fst fun p ↦ (arrowHomeomorph N).injective (by simp)
  t2Space_objects := inferInstance
  secondCountableTopology_arrows := inferInstance
  t2Space_sourceFiber _ := inferInstance

end TauCeti.UnitGroupoid

namespace TauCeti.PairGroupoid

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]

/-- Objects of `Codiscrete N` carry the charted-space structure pulled back from `N`. -/
instance instChartedSpaceObjects : ChartedSpace H (Codiscrete N) :=
  (objectHomeomorph N).pullbackChartedSpace

/-- Objects of `Codiscrete N` form a `C^n` manifold whenever `N` does. -/
instance instIsManifoldObjects (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) [IsManifold I n N] :
    IsManifold I n (Codiscrete N) :=
  (objectHomeomorph N).pullback_isManifold I n

/-- Forgetting the categorical wrapper on `Codiscrete N` as a `C^n` diffeomorphism. -/
def objectDiffeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (N : Type*) [TopologicalSpace N] [ChartedSpace H N] : Codiscrete N ≃ₘ^n⟮I, I⟯ N :=
  (objectHomeomorph N).pullbackDiffeomorph I n

@[simp]
theorem objectDiffeomorph_apply (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) (x : Codiscrete N) :
    objectDiffeomorph I n N x = x.as := by simp [objectDiffeomorph]

@[simp]
theorem objectDiffeomorph_symm_apply (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) (x : N) :
    (objectDiffeomorph I n N).symm x = Codiscrete.mk x := by simp [objectDiffeomorph]

@[simp]
theorem objectDiffeomorph_toHomeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    (objectDiffeomorph I n N).toHomeomorph = objectHomeomorph N := by simp [objectDiffeomorph]

/-- Total arrows of `Codiscrete N` carry the charted-space structure of `N × N` pulled back along
`arrowHomeomorph`, in (target, source) coordinates. -/
instance instChartedSpaceArrows : ChartedSpace (ModelProd H H) (Quiver.Total (Codiscrete N)) :=
  (arrowHomeomorph N).pullbackChartedSpace

/-- Total arrows of `Codiscrete N` form a `C^n` manifold whenever `N` does. -/
instance instIsManifoldArrows (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) [IsManifold I n N] :
    IsManifold (I.prod I) n (Quiver.Total (Codiscrete N)) :=
  (arrowHomeomorph N).pullback_isManifold (I.prod I) n

/-- The total-arrow space of `Codiscrete N` is `C^n` diffeomorphic to `N × N`, by the
(target, source) coordinates. -/
def arrowDiffeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (N : Type*) [TopologicalSpace N] [ChartedSpace H N] :
    Quiver.Total (Codiscrete N) ≃ₘ^n⟮I.prod I, I.prod I⟯ N × N :=
  (arrowHomeomorph N).pullbackDiffeomorph (I.prod I) n

@[simp]
theorem arrowDiffeomorph_apply (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (a : Quiver.Total (Codiscrete N)) : arrowDiffeomorph I n N a = (a.right.as, a.left.as) := by
  simp [arrowDiffeomorph]

@[simp]
theorem arrowDiffeomorph_symm_apply (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) (p : N × N) :
    (arrowDiffeomorph I n N).symm p = ⟨⟨p.2⟩, ⟨p.1⟩, default⟩ := by simp [arrowDiffeomorph]

@[simp]
theorem arrowDiffeomorph_toHomeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    (arrowDiffeomorph I n N).toHomeomorph = arrowHomeomorph N := by simp [arrowDiffeomorph]

section LieGroupoid

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] in
private theorem contMDiff_object : ContMDiff I I ∞ fun x : Codiscrete N ↦ x.as := by
  simpa only [← funext (objectDiffeomorph_apply I ∞ (N := N))] using
    (objectDiffeomorph I ∞ N).contMDiff

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] in
private theorem contMDiff_arrow : ContMDiff (I.prod I) (I.prod I) ∞
    fun a : Quiver.Total (Codiscrete N) ↦ (a.right.as, a.left.as) := by
  simpa only [← funext (arrowDiffeomorph_apply I ∞ (N := N))] using
    (arrowDiffeomorph I ∞ N).contMDiff

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
private theorem isSubmersion_source :
    Manifold.IsSubmersion (I.prod I) I ∞
      (Quiver.Total.left : Quiver.Total (Codiscrete N) → Codiscrete N) := by
  have h : (Quiver.Total.left : Quiver.Total (Codiscrete N) → Codiscrete N) =
      (objectDiffeomorph I ∞ N).symm ∘ (Prod.fst ∘
        ((arrowDiffeomorph I ∞ N).trans (Diffeomorph.prodComm I I N N ∞))) := by
    funext a
    simp
  rw [h]
  exact (objectDiffeomorph I ∞ N).symm.isLocalDiffeomorph.comp_isSubmersion
    (((arrowDiffeomorph I ∞ N).trans (Diffeomorph.prodComm I I N N ∞)).isLocalDiffeomorph
      |>.isSubmersion_comp Manifold.isSubmersion_fst)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] in
private theorem contMDiff_inverse : ContMDiff (I.prod I) (I.prod I) ∞
    fun a : Quiver.Total (Codiscrete N) ↦
      (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total (Codiscrete N)) := by
  refine ((arrowDiffeomorph I ∞ N).contMDiff_diffeomorph_comp_iff le_rfl).1 ?_
  have ha := contMDiff_arrow (I := I) (N := N)
  simpa [Function.comp_def] using ha.snd.prodMk ha.fst

/-- The pair groupoid of a Hausdorff second-countable smooth manifold `N` is a Lie groupoid. Its
arrow manifold is `N × N` in (target, source) coordinates, source and target are the two
projections, and each source fibre is a copy of `N`. -/
instance lieGroupoid [T2Space N] [SecondCountableTopology N] :
    LieGroupoid I (I.prod I) (Codiscrete N) where
  isSubmersion_source := isSubmersion_source
  contMDiff_unit := by
    refine ((arrowDiffeomorph I ∞ N).contMDiff_diffeomorph_comp_iff le_rfl).1 ?_
    simpa [Function.comp_def] using contMDiff_object.prodMk (contMDiff_object (I := I) (N := N))
  contMDiff_inverse := contMDiff_inverse
  -- The composite of `x → y` and `y → z` is the arrow with coordinates `(z, x)`.
  contMDiff_comp := by
    have ha := (arrowDiffeomorph I ∞ N).contMDiff
    exact contMDiff_composablePairs_comp_of_eq isSubmersion_source contMDiff_inverse
      ((arrowDiffeomorph I ∞ N).symm.contMDiff.comp
        ((ha.comp contMDiff_snd).fst.prodMk (ha.comp contMDiff_fst).snd))
      fun p ↦ (arrowHomeomorph N).injective (by simp)
  t2Space_objects := inferInstance
  secondCountableTopology_arrows := inferInstance
  t2Space_sourceFiber _ := inferInstance

end LieGroupoid

end TauCeti.PairGroupoid
