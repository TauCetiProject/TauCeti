/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Groupoid.Fibers
public import TauCeti.Geometry.Manifold.PullbackGroupoid
public import TauCeti.Topology.CategoryTheory.Groupoid.Examples
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph

/-!
# Unit, pair, and one-object smooth and Lie groupoids

The native topological groupoids `Discrete N`, `Codiscrete M`, and `SingleObj G` from
`TauCeti.Topology.CategoryTheory.Groupoid.Examples` inherit canonical `C^n` manifold structures on
objects and total arrows by pulling charts back along their object and arrow homeomorphisms via
`Homeomorph.pullbackChartedSpace`, and over `ℝ` each becomes a `TauCeti.IsLieGroupoid`:

* the **unit groupoid** `Discrete N` of a `C^n` manifold `N` has object and arrow manifolds `C^n`
  diffeomorphic to `N` (`TauCeti.UnitGroupoid.objectDiffeomorph`,
  `TauCeti.UnitGroupoid.arrowDiffeomorph`), making source and target global (hence local) `C^n`
  diffeomorphisms (`TauCeti.UnitGroupoid.sourceDiffeomorph`,
  `TauCeti.UnitGroupoid.isLocalDiffeomorph_source`,
  `TauCeti.UnitGroupoid.isLocalDiffeomorph_target`). When `N` is a Hausdorff second-countable real
  smooth manifold, `Discrete N` is a Lie groupoid (`TauCeti.UnitGroupoid.isLieGroupoid`);
* the **pair groupoid** `Codiscrete M` of a `C^n` manifold `M` has object manifold `C^n`
  diffeomorphic to `M` and arrow manifold `C^n` diffeomorphic to `M × M` in `(target, source)`
  coordinates, with `C^n` submersive source and target (`TauCeti.PairGroupoid.isSubmersion_source`,
  `TauCeti.PairGroupoid.isSubmersion_target`), yielding a Lie groupoid
  (`TauCeti.PairGroupoid.isLieGroupoid`) on any Hausdorff second-countable real smooth manifold `M`
  whose source and target fibres are canonically diffeomorphic to `M`
  (`TauCeti.PairGroupoid.sourceFiberDiffeomorph`, `TauCeti.PairGroupoid.targetFiberDiffeomorph`);
* the **one-object groupoid** `SingleObj G` of a `C^n` manifold `G` has singleton object manifold
  modelled on `𝓘(𝕜, Unit)` and arrow manifold `C^n` diffeomorphic to `G`, yielding a Lie groupoid
  (`TauCeti.OneObjectGroupoid.isLieGroupoid`) for every second-countable real Lie group `G` (no
  separate Hausdorffness hypothesis on `G` is needed, as every real Lie group is Hausdorff).

## Main declarations

* `TauCeti.UnitGroupoid.instChartedSpaceObjects`, `TauCeti.UnitGroupoid.instIsManifoldObjects`,
  `TauCeti.UnitGroupoid.objectDiffeomorph`: `C^n` manifold structure on `Discrete N` and
  `Discrete N ≃ₘ^n⟮I, I⟯ N`.
* `TauCeti.UnitGroupoid.instChartedSpaceArrows`, `TauCeti.UnitGroupoid.instIsManifoldArrows`,
  `TauCeti.UnitGroupoid.arrowDiffeomorph`: `C^n` manifold structure on `Quiver.Total (Discrete N)`
  and `Quiver.Total (Discrete N) ≃ₘ^n⟮I, I⟯ N`.
* `TauCeti.UnitGroupoid.sourceDiffeomorph`, `TauCeti.UnitGroupoid.isLocalDiffeomorph_source`,
  `TauCeti.UnitGroupoid.isLocalDiffeomorph_target`, `TauCeti.UnitGroupoid.isLieGroupoid`: source
  diffeomorphism, local diffeomorphisms, and Lie groupoid instance on `Discrete N`.
* `TauCeti.PairGroupoid.instChartedSpaceObjects`, `TauCeti.PairGroupoid.instChartedSpaceArrows`,
  `TauCeti.PairGroupoid.objectDiffeomorph`, `TauCeti.PairGroupoid.arrowDiffeomorph`,
  `TauCeti.PairGroupoid.isSubmersion_source`, `TauCeti.PairGroupoid.isSubmersion_target`,
  `TauCeti.PairGroupoid.isLieGroupoid`, `TauCeti.PairGroupoid.sourceFiberDiffeomorph`,
  `TauCeti.PairGroupoid.targetFiberDiffeomorph`: smooth structure, Lie groupoid instance, and fibre
  diffeomorphisms on `Codiscrete M`.
* `TauCeti.OneObjectGroupoid.instChartedSpaceObjects`,
  `TauCeti.OneObjectGroupoid.instChartedSpaceArrows`,
  `TauCeti.OneObjectGroupoid.arrowDiffeomorph`, `TauCeti.OneObjectGroupoid.isLieGroupoid`: smooth
  structure and Lie groupoid instance on `SingleObj G`.

## References

* K. C. H. Mackenzie, *General Theory of Lie Groupoids and Lie Algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), Examples 1.1.9–1.1.11.
* I. Moerdijk and J. Mrčun, *Introduction to Foliations and Lie Groupoids*, Cambridge Stud. Adv.
  Math. 91, Cambridge University Press (2003), Section 5.1, Examples 5.1(1)–(3).
-/

public section

open CategoryTheory Topology
open scoped Manifold ContDiff

namespace TauCeti

/-! ### The unit smooth and Lie groupoid `Discrete N` -/

namespace UnitGroupoid

section Smooth

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

end Smooth

section LieGroupoid

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

private theorem contMDiff_inverse_aux :
    ContMDiff I I ∞ (fun a : Quiver.Total (Discrete M) ↦
      (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total (Discrete M))) := by
  rw [← (arrowDiffeomorph I ∞ M).contMDiff_diffeomorph_comp_iff le_rfl]
  exact (arrowDiffeomorph I ∞ M).contMDiff.congr fun a ↦ by simp

variable [IsManifold I ∞ M]

private theorem isSubmersion_source_aux :
    Manifold.IsSubmersion I I ∞ (Quiver.Total.left : Quiver.Total (Discrete M) → Discrete M) := by
  simpa using (sourceDiffeomorph I ∞ M).isLocalDiffeomorph.comp_isSubmersion
    (Manifold.IsSubmersion.id (I := I) (n := ∞) (M := Quiver.Total (Discrete M)))

variable [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [SecondCountableTopology M]

/-- The unit groupoid on a Hausdorff second-countable smooth manifold is a Lie groupoid. -/
instance isLieGroupoid : IsLieGroupoid I I (Discrete M) where
  isSubmersion_source := isSubmersion_source_aux I M
  contMDiff_unit :=
    ((arrowDiffeomorph I ∞ M).symm.contMDiff.comp
      (objectDiffeomorph I ∞ M).contMDiff).congr fun x ↦ by simp
  contMDiff_inverse := contMDiff_inverse_aux I M
  -- An arrow of the unit groupoid is determined by its source, so composition is the first
  -- projection.
  contMDiff_comp := contMDiff_composablePairs_comp_of_eq (isSubmersion_source_aux I M)
    (contMDiff_inverse_aux I M) contMDiff_fst fun p ↦ (arrowHomeomorph M).injective (by simp)

end LieGroupoid

end UnitGroupoid

/-! ### The pair smooth and Lie groupoid `Codiscrete M` -/

namespace PairGroupoid

section Smooth

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The object manifold of the pair groupoid pulls back the charts of `M` along
`PairGroupoid.objectHomeomorph`. -/
instance instChartedSpaceObjects : ChartedSpace H (Codiscrete M) :=
  (objectHomeomorph M).pullbackChartedSpace

/-- Objects of `Codiscrete M` form a `C^n` manifold whenever `M` does. -/
instance instIsManifoldObjects (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) [IsManifold I n M] :
    IsManifold I n (Codiscrete M) :=
  (objectHomeomorph M).pullback_isManifold I n

/-- The objects of `Codiscrete M` are `C^n` diffeomorphic to `M`. -/
def objectDiffeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] : Codiscrete M ≃ₘ^n⟮I, I⟯ M :=
  (objectHomeomorph M).pullbackDiffeomorph I n

@[simp]
theorem objectDiffeomorph_apply (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) (x : Codiscrete M) :
    objectDiffeomorph I n M x = x.as := by
  simp [objectDiffeomorph]

@[simp]
theorem objectDiffeomorph_symm_apply (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) (x : M) :
    (objectDiffeomorph I n M).symm x = Codiscrete.mk x := by
  simp [objectDiffeomorph]

@[simp]
theorem objectDiffeomorph_toHomeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    (objectDiffeomorph I n M).toHomeomorph = objectHomeomorph M := by
  simp [objectDiffeomorph]

/-- The arrow manifold of the pair groupoid pulls back the product charts of `M × M` in
`(target, source)` coordinates along `PairGroupoid.arrowHomeomorph`. -/
instance instChartedSpaceArrows : ChartedSpace (ModelProd H H) (Quiver.Total (Codiscrete M)) :=
  (arrowHomeomorph M).pullbackChartedSpace

/-- Total arrows of `Codiscrete M` form a `C^n` manifold whenever `M` does. -/
instance instIsManifoldArrows (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) [IsManifold I n M] :
    IsManifold (I.prod I) n (Quiver.Total (Codiscrete M)) :=
  (arrowHomeomorph M).pullback_isManifold (I.prod I) n

/-- The total arrows of `Codiscrete M` are `C^n` diffeomorphic to `M × M` in `(target, source)`
coordinates. -/
def arrowDiffeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] :
    Quiver.Total (Codiscrete M) ≃ₘ^n⟮I.prod I, I.prod I⟯ (M × M) :=
  (arrowHomeomorph M).pullbackDiffeomorph (I.prod I) n

@[simp]
theorem arrowDiffeomorph_apply (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (a : Quiver.Total (Codiscrete M)) :
    arrowDiffeomorph I n M a = (a.right.as, a.left.as) := by
  simp [arrowDiffeomorph]

@[simp]
theorem arrowDiffeomorph_symm_apply (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) (p : M × M) :
    (arrowDiffeomorph I n M).symm p = ⟨⟨p.2⟩, ⟨p.1⟩, default⟩ := by
  simp [arrowDiffeomorph]

@[simp]
theorem arrowDiffeomorph_toHomeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    (arrowDiffeomorph I n M).toHomeomorph = arrowHomeomorph M := by
  simp [arrowDiffeomorph]

/-- The source map of the pair groupoid is a `C^n` submersion: in `(target, source)` coordinates it
is the second projection `M × M → M`. -/
theorem isSubmersion_source (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M] :
    Manifold.IsSubmersion (I.prod I) I n
      (Quiver.Total.left : Quiver.Total (Codiscrete M) → Codiscrete M) := by
  have h : (Quiver.Total.left : Quiver.Total (Codiscrete M) → Codiscrete M) =
      (objectDiffeomorph I n M).symm ∘ (Prod.fst ∘
        ((arrowDiffeomorph I n M).trans (Diffeomorph.prodComm I I M M n))) := by
    funext a
    simp
  rw [h]
  exact (objectDiffeomorph I n M).symm.isLocalDiffeomorph.comp_isSubmersion
    (((arrowDiffeomorph I n M).trans (Diffeomorph.prodComm I I M M n)).isLocalDiffeomorph
      |>.isSubmersion_comp Manifold.isSubmersion_fst)

/-- The target map of the pair groupoid is a `C^n` submersion: in `(target, source)` coordinates it
is the first projection `M × M → M`. -/
theorem isSubmersion_target (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M] :
    Manifold.IsSubmersion (I.prod I) I n
      (Quiver.Total.right : Quiver.Total (Codiscrete M) → Codiscrete M) := by
  have h : (Quiver.Total.right : Quiver.Total (Codiscrete M) → Codiscrete M) =
      (objectDiffeomorph I n M).symm ∘ (Prod.fst ∘ arrowDiffeomorph I n M) := by
    funext a
    simp
  rw [h]
  exact (objectDiffeomorph I n M).symm.isLocalDiffeomorph.comp_isSubmersion
    ((arrowDiffeomorph I n M).isLocalDiffeomorph.isSubmersion_comp Manifold.isSubmersion_fst)

end Smooth

section LieGroupoid

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

private theorem contMDiff_inverse_aux :
    ContMDiff (I.prod I) (I.prod I) ∞ (fun a : Quiver.Total (Codiscrete M) ↦
      (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total (Codiscrete M))) := by
  rw [← (arrowDiffeomorph I ∞ M).contMDiff_diffeomorph_comp_iff le_rfl]
  exact ((contMDiff_snd.comp (arrowDiffeomorph I ∞ M).contMDiff).prodMk
    (contMDiff_fst.comp (arrowDiffeomorph I ∞ M).contMDiff)).congr fun a ↦ by simp

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]

section FiberTranslations

variable [IsLieGroupoid I (I.prod I) (Codiscrete M)]

/-- Target identifies each canonical source fibre `s⁻¹(x)` of `Codiscrete M` diffeomorphically with
`M`, sending an arrow `x ⟶ z` to `z`. -/
noncomputable def sourceFiberDiffeomorph (x : Codiscrete M) :
    letI := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) x
    {a : Quiver.Total (Codiscrete M) // a.left = x} ≃ₘ^∞⟮
      𝓘(ℝ, Fin (Module.finrank ℝ (E × E) - Module.finrank ℝ E) → ℝ), I⟯ M :=
  RegularFiber.diffeomorphOfProd (by simp)
    (IsLieGroupoid.contMDiff_source I (I.prod I) (Codiscrete M))
    BoundarylessManifold.isInteriorPoint (IsLieGroupoid.isRegularValue_source I (I.prod I) x)
    (arrowDiffeomorph I ∞ M) (objectDiffeomorph I ∞ M) (by funext a; simp)

@[simp]
theorem sourceFiberDiffeomorph_apply (x : Codiscrete M)
    (a : {a : Quiver.Total (Codiscrete M) // a.left = x}) :
    letI := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) x
    sourceFiberDiffeomorph I M x a = a.val.right.as := by
  simp [sourceFiberDiffeomorph, RegularFiber.diffeomorphOfProd_apply]

@[simp]
theorem coe_sourceFiberDiffeomorph_symm_apply (x : Codiscrete M) (z : M) :
    letI := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) x
    ((sourceFiberDiffeomorph I M x).symm z).val = ⟨x, ⟨z⟩, default⟩ := by
  simp [sourceFiberDiffeomorph, RegularFiber.coe_diffeomorphOfProd_symm_apply]

/-- Source identifies each canonical target fibre `t⁻¹(x)` of `Codiscrete M` diffeomorphically with
`M`, sending an arrow `w ⟶ x` to `w`. -/
noncomputable def targetFiberDiffeomorph (x : Codiscrete M) :
    letI := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) x
    {a : Quiver.Total (Codiscrete M) // a.right = x} ≃ₘ^∞⟮
      𝓘(ℝ, Fin (Module.finrank ℝ (E × E) - Module.finrank ℝ E) → ℝ), I⟯ M :=
  RegularFiber.diffeomorphOfProd (by simp)
    (IsLieGroupoid.contMDiff_target I (I.prod I) (Codiscrete M))
    BoundarylessManifold.isInteriorPoint (IsLieGroupoid.isRegularValue_target I (I.prod I) x)
    ((arrowDiffeomorph I ∞ M).trans (Diffeomorph.prodComm I I M M ∞))
    (objectDiffeomorph I ∞ M) (by funext a; simp)

@[simp]
theorem targetFiberDiffeomorph_apply (x : Codiscrete M)
    (a : {a : Quiver.Total (Codiscrete M) // a.right = x}) :
    letI := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) x
    targetFiberDiffeomorph I M x a = a.val.left.as := by
  simp [targetFiberDiffeomorph, RegularFiber.diffeomorphOfProd_apply]

@[simp]
theorem coe_targetFiberDiffeomorph_symm_apply (x : Codiscrete M) (w : M) :
    letI := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) x
    ((targetFiberDiffeomorph I M x).symm w).val = ⟨⟨w⟩, x, default⟩ := by
  simp [targetFiberDiffeomorph, RegularFiber.coe_diffeomorphOfProd_symm_apply]

/-- Under the target-coordinate identifications `s⁻¹(t(g)) ≃ₘ^∞ M ≃ₘ^∞ s⁻¹(s(g))`, right
translation in the pair groupoid acts as the identity on `M`. -/
theorem sourceFiberDiffeomorph_rightMulDiffeomorph (g : Quiver.Total (Codiscrete M))
    (h : {a : Quiver.Total (Codiscrete M) // a.left = g.right}) :
    letI := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) g.right
    letI := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) g.left
    sourceFiberDiffeomorph I M g.left (IsLieGroupoid.rightMulDiffeomorph I (I.prod I) g h) =
      sourceFiberDiffeomorph I M g.right h := by
  simp

/-- Under the source-coordinate identifications `t⁻¹(s(g)) ≃ₘ^∞ M ≃ₘ^∞ t⁻¹(t(g))`, left
translation in the pair groupoid acts as the identity on `M`. -/
theorem targetFiberDiffeomorph_leftMulDiffeomorph (g : Quiver.Total (Codiscrete M))
    (h : {a : Quiver.Total (Codiscrete M) // a.right = g.left}) :
    letI := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) g.left
    letI := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) g.right
    targetFiberDiffeomorph I M g.right (IsLieGroupoid.leftMulDiffeomorph I (I.prod I) g h) =
      targetFiberDiffeomorph I M g.left h := by
  simp

end FiberTranslations

variable [T2Space M] [SecondCountableTopology M]

/-- The pair groupoid on a Hausdorff second-countable smooth manifold is a Lie groupoid. -/
instance isLieGroupoid : IsLieGroupoid I (I.prod I) (Codiscrete M) where
  isSubmersion_source := isSubmersion_source I ∞ M
  contMDiff_unit := by
    rw [← (arrowDiffeomorph I ∞ M).contMDiff_diffeomorph_comp_iff le_rfl]
    exact ((objectDiffeomorph I ∞ M).contMDiff.prodMk
      (objectDiffeomorph I ∞ M).contMDiff).congr fun x ↦ by simp
  contMDiff_inverse := contMDiff_inverse_aux I M
  -- The composite of `x → y` and `y → z` is the arrow with coordinates `(z, x)`.
  contMDiff_comp := by
    have ha := (arrowDiffeomorph I ∞ M).contMDiff
    exact contMDiff_composablePairs_comp_of_eq (isSubmersion_source I ∞ M)
      (contMDiff_inverse_aux I M)
      ((arrowDiffeomorph I ∞ M).symm.contMDiff.comp
        ((ha.comp contMDiff_snd).fst.prodMk (ha.comp contMDiff_fst).snd))
      fun p ↦ (arrowHomeomorph M).injective (by simp)

end LieGroupoid

end PairGroupoid

/-! ### The one-object smooth and Lie groupoid `SingleObj G` -/

namespace OneObjectGroupoid

/-- The singleton object space `SingleObj G` carries the canonical zero-dimensional charted-space
structure of `Unit`. -/
instance instChartedSpaceObjects {G : Type*} :
    ChartedSpace Unit (SingleObj G) :=
  inferInstanceAs (ChartedSpace Unit Unit)

/-- The singleton object space `SingleObj G` is a `C^n` manifold modelled on `𝓘(𝕜, Unit)`. -/
instance instIsManifoldObjects (𝕜 : Type*) [NontriviallyNormedField 𝕜] (n : ℕ∞ω)
    {G : Type*} : IsManifold 𝓘(𝕜, Unit) n (SingleObj G) :=
  inferInstanceAs (IsManifold 𝓘(𝕜, Unit) n Unit)

section Smooth

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G]

/-- The arrow manifold of `SingleObj G` pulls back the charts of `G` along
`OneObjectGroupoid.arrowHomeomorph`. -/
instance instChartedSpaceArrows : ChartedSpace H (Quiver.Total (SingleObj G)) :=
  (arrowHomeomorph G).pullbackChartedSpace

/-- Total arrows of `SingleObj G` form a `C^n` manifold whenever `G` does. -/
instance instIsManifoldArrows (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) [IsManifold I n G] :
    IsManifold I n (Quiver.Total (SingleObj G)) :=
  (arrowHomeomorph G).pullback_isManifold I n

/-- The total arrows of `SingleObj G` are `C^n` diffeomorphic to `G`. -/
def arrowDiffeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (G : Type*) [TopologicalSpace G] [ChartedSpace H G] :
    Quiver.Total (SingleObj G) ≃ₘ^n⟮I, I⟯ G :=
  (arrowHomeomorph G).pullbackDiffeomorph I n

@[simp]
theorem arrowDiffeomorph_apply (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (a : Quiver.Total (SingleObj G)) :
    arrowDiffeomorph I n G a = a.hom := by
  simp [arrowDiffeomorph]

@[simp]
theorem arrowDiffeomorph_symm_apply (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) (g : G) :
    (arrowDiffeomorph I n G).symm g = ⟨SingleObj.star G, SingleObj.star G, g⟩ := by
  simp [arrowDiffeomorph]

@[simp]
theorem arrowDiffeomorph_toHomeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    (arrowDiffeomorph I n G).toHomeomorph = arrowHomeomorph G := by
  simp [arrowDiffeomorph]

end Smooth

section LieGroupoid

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (G : Type*) [TopologicalSpace G] [ChartedSpace H G]

private theorem isSubmersion_source_aux [FiniteDimensional ℝ E] [I.Boundaryless]
    [IsManifold I ∞ G] :
    Manifold.IsSubmersion I 𝓘(ℝ, Unit) ∞
      (Quiver.Total.left : Quiver.Total (SingleObj G) → SingleObj G) := by
  have hs : ContMDiff I 𝓘(ℝ, Unit) ∞
      (Quiver.Total.left : Quiver.Total (SingleObj G) → SingleObj G) :=
    contMDiff_const.congr fun _ ↦ Subsingleton.elim _ (SingleObj.star G)
  exact (hs.isSubmersionOfComplement_of_surjective_mfderiv (by simp) fun _ v ↦
    ⟨0, Subsingleton.elim (α := Unit) _ v⟩).isSubmersion

variable [Group G] [FiniteDimensional ℝ E] [I.Boundaryless] [LieGroup I ∞ G]

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
private theorem contMDiff_inverse_aux :
    ContMDiff I I ∞ (fun a : Quiver.Total (SingleObj G) ↦
      (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total (SingleObj G))) := by
  rw [← (arrowDiffeomorph I ∞ G).contMDiff_diffeomorph_comp_iff le_rfl]
  exact (arrowDiffeomorph I ∞ G).contMDiff.inv.congr fun a ↦ by simp [SingleObj.inv_as_inv]

variable [SecondCountableTopology G]

/-- Every second-countable real Lie group `G` defines a one-object Lie groupoid `SingleObj G`. -/
instance isLieGroupoid : IsLieGroupoid 𝓘(ℝ, Unit) I (SingleObj G) where
  t2Space_objects := inferInstanceAs (T2Space Unit)
  isSubmersion_source := isSubmersion_source_aux I G
  contMDiff_unit :=
    contMDiff_const.congr fun x ↦ by
      cases Subsingleton.elim x (SingleObj.star G)
      rfl
  contMDiff_inverse := contMDiff_inverse_aux I G
  contMDiff_comp := by
    let := transverseFiberProductChartedSpace
      (f := (Quiver.Total.right : Quiver.Total (SingleObj G) → SingleObj G))
      (g := (Quiver.Total.left : Quiver.Total (SingleObj G) → SingleObj G)) (n := ∞) (by simp)
      ((isSubmersion_source_aux I G).contMDiff.comp (contMDiff_inverse_aux I G))
      (isSubmersion_source_aux I G).contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_right (by simp) (isSubmersion_source_aux I G) p)
    have hemb := isSmoothEmbedding_coe_transverseFiberProduct
      (f := (Quiver.Total.right : Quiver.Total (SingleObj G) → SingleObj G))
      (g := (Quiver.Total.left : Quiver.Total (SingleObj G) → SingleObj G)) (n := ∞) (by simp)
      ((isSubmersion_source_aux I G).contMDiff.comp (contMDiff_inverse_aux I G))
      (isSubmersion_source_aux I G).contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_right (by simp) (isSubmersion_source_aux I G) p)
    rw [← (arrowDiffeomorph I ∞ G).contMDiff_diffeomorph_comp_iff le_rfl]
    refine (((arrowDiffeomorph I ∞ G).contMDiff.comp (contMDiff_snd.comp hemb.contMDiff)).mul
      ((arrowDiffeomorph I ∞ G).contMDiff.comp (contMDiff_fst.comp hemb.contMDiff))).congr
      fun p ↦ ?_
    simpa only [Function.comp_apply, Pi.mul_apply, arrowDiffeomorph_apply,
      arrowHomeomorph_apply] using arrowHomeomorph_comp G p.val.1 p.val.2 p.property
  t2Space_sourceFiber _ := by
    have := topologicalGroup_of_lieGroup I ∞ (G := G)
    have := I.t1Space G
    exact inferInstance

end LieGroupoid

end OneObjectGroupoid

end TauCeti
