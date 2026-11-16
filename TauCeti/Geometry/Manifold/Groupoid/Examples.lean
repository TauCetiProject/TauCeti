/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Groupoid.Translation
public import TauCeti.Geometry.Manifold.PullbackGroupoid
public import TauCeti.Topology.CategoryTheory.Groupoid.Examples
import Mathlib.Topology.Bases
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph

/-!
# Smooth unit groupoids and unit and pair Lie groupoids

Given a `C^n` manifold `N`, the unit groupoid `Discrete N` inherits `C^n` manifold structures on
objects and total arrows by pulling charts back along `TauCeti.UnitGroupoid.objectHomeomorph` and
`TauCeti.UnitGroupoid.arrowHomeomorph` (`Homeomorph.pullbackChartedSpace`), making source and target
global (hence local) `C^n` diffeomorphisms (`TauCeti.UnitGroupoid.sourceDiffeomorph`,
`TauCeti.UnitGroupoid.isLocalDiffeomorph_source`, `TauCeti.UnitGroupoid.isLocalDiffeomorph_target`).
Similarly, the pair groupoid `Codiscrete N` inherits `C^n` manifold structures on objects and total
arrows pulled back from `N` and `N × N`, with source a `C^n` submersion
(`TauCeti.PairGroupoid.isSubmersion_source`).

For any Hausdorff second-countable finite-dimensional boundaryless smooth real manifold `X`:

* **The unit Lie groupoid** `Discrete X` (`TauCeti.UnitGroupoid.isLieGroupoid`): objects and total
  arrows are both canonically diffeomorphic to `X`, and source is a global diffeomorphism (the
  canonical étale witness).
* **The pair Lie groupoid** `Codiscrete X` (`TauCeti.PairGroupoid.isLieGroupoid`): objects are
  diffeomorphic to `X` and total arrows are diffeomorphic to `X × X` in `(target, source)`
  coordinates. Every source fibre `s⁻¹(x)` is diffeomorphic to `X` via target
  (`TauCeti.PairGroupoid.sourceFiberDiffeomorph`), every target fibre `t⁻¹(x)` is diffeomorphic to
  `X` via source (`TauCeti.PairGroupoid.targetFiberDiffeomorph`), and right/left translations act as
  `id_X` under these identifications.

## References

* K. C. H. Mackenzie, *General Theory of Lie Groupoids and Lie Algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), Examples 1.1.7 and 1.1.8.
* I. Moerdijk and J. Mrčun, *Introduction to Foliations and Lie Groupoids*, Cambridge Stud. Adv.
  Math. 91, Cambridge University Press (2003), Section 5.1, Examples 5.1(1)–(2).
-/

public section

open CategoryTheory Function Module Set Topology
open scoped Manifold ContDiff

namespace TauCeti

/-! ### Smooth unit groupoid and unit Lie groupoid -/

namespace UnitGroupoid

section Charts

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

end Charts

/-- The unit groupoid on any Hausdorff second-countable boundaryless smooth manifold is a Lie
groupoid. -/
instance isLieGroupoid {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (X : Type*) [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [T2Space X] [SecondCountableTopology X] : IsLieGroupoid I I (Discrete X) := by
  have hs : Manifold.IsSubmersion I I ∞
      (Quiver.Total.left : Quiver.Total (Discrete X) → Discrete X) :=
    isLocalDiffeomorph_source.isSubmersion
  have hinv : ContMDiff I I ∞ fun a : Quiver.Total (Discrete X) ↦
      (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total (Discrete X)) :=
    contMDiff_id.congr fun ⟨⟨_⟩, ⟨_⟩, f⟩ ↦ by
      obtain rfl := Discrete.eq_of_hom f
      exact Quiver.Total.ext rfl rfl (heq_of_eq (Subsingleton.elim _ _))
  refine IsLieGroupoid.of_isSubmersion_source hs hinv ?_
    (arrowHomeomorph X).isEmbedding.secondCountableTopology
    (objectHomeomorph X).isEmbedding.t2Space fun _ ↦ inferInstance
  let := transverseFiberProductChartedSpace (f := Quiver.Total.right) (g := Quiver.Total.left)
    (by simp : (1 : ℕ∞ω) ≤ ∞) (hs.contMDiff.comp hinv) hs.contMDiff
    (fun p _ ↦ hs.transverse_right (by simp) _ p)
  have hι := isSmoothEmbedding_coe_transverseFiberProduct
    (f := Quiver.Total.right) (g := Quiver.Total.left)
    (by simp : (1 : ℕ∞ω) ≤ ∞) (hs.contMDiff.comp hinv) hs.contMDiff
    (fun p _ ↦ hs.transverse_right (by simp) _ p)
  exact hι.contMDiff.fst.congr fun ⟨⟨⟨⟨_⟩, ⟨_⟩, f⟩, ⟨⟨_⟩, ⟨_⟩, g⟩⟩, hp⟩ ↦ by
    obtain rfl := Discrete.eq_of_hom f; obtain rfl := Discrete.eq_of_hom g
    dsimp only at hp; cases hp; rw [Quiver.Total.comp_def]
    exact Quiver.Total.ext rfl rfl (heq_of_eq (Subsingleton.elim _ _))

end UnitGroupoid

/-! ### Smooth pair groupoid and pair Lie groupoid -/

namespace PairGroupoid

noncomputable section

section Charts

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X]

/-- Objects of `Codiscrete X` carry the charted-space structure pulled back from `X`. -/
instance instChartedSpaceObjects : ChartedSpace H (Codiscrete X) :=
  (objectHomeomorph X).pullbackChartedSpace

/-- Objects of `Codiscrete X` form a `C^n` manifold whenever `X` does. -/
instance instIsManifoldObjects (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) [IsManifold I n X] :
    IsManifold I n (Codiscrete X) :=
  (objectHomeomorph X).pullback_isManifold I n

/-- `C^n` diffeomorphism identifying objects of the pair groupoid with `X`. -/
def objectDiffeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (X : Type*) [TopologicalSpace X] [ChartedSpace H X] : Codiscrete X ≃ₘ^n⟮I, I⟯ X :=
  (objectHomeomorph X).pullbackDiffeomorph I n

@[simp]
theorem coe_objectDiffeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    ⇑(objectDiffeomorph I n X) = objectHomeomorph X :=
  (objectHomeomorph X).coe_pullbackDiffeomorph I n

@[simp]
theorem coe_objectDiffeomorph_symm (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    ⇑(objectDiffeomorph I n X).symm = (objectHomeomorph X).symm :=
  (objectHomeomorph X).coe_pullbackDiffeomorph_symm I n

/-- Total arrows of `Codiscrete X` carry the charted-space structure pulled back from `X × X` in
`(target, source)` coordinates. -/
instance instChartedSpaceArrows : ChartedSpace (ModelProd H H) (Quiver.Total (Codiscrete X)) :=
  (arrowHomeomorph X).pullbackChartedSpace

/-- Total arrows of `Codiscrete X` form a `C^n` manifold whenever `X` does. -/
instance instIsManifoldArrows (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) [IsManifold I n X] :
    IsManifold (I.prod I) n (Quiver.Total (Codiscrete X)) :=
  (arrowHomeomorph X).pullback_isManifold (I.prod I) n

/-- `C^n` diffeomorphism identifying total arrows of the pair groupoid with `X × X` via
`a ↦ (a.right.as, a.left.as)`. -/
def arrowDiffeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (X : Type*) [TopologicalSpace X] [ChartedSpace H X] :
    Quiver.Total (Codiscrete X) ≃ₘ^n⟮I.prod I, I.prod I⟯ X × X :=
  (arrowHomeomorph X).pullbackDiffeomorph (I.prod I) n

@[simp]
theorem coe_arrowDiffeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    ⇑(arrowDiffeomorph I n X) = arrowHomeomorph X :=
  (arrowHomeomorph X).coe_pullbackDiffeomorph (I.prod I) n

@[simp]
theorem coe_arrowDiffeomorph_symm (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    ⇑(arrowDiffeomorph I n X).symm = (arrowHomeomorph X).symm :=
  (arrowHomeomorph X).coe_pullbackDiffeomorph_symm (I.prod I) n

/-- Source on the pair groupoid is a `C^n` submersion: in `(target, source)` coordinates it is the
second projection `X × X → X`. -/
theorem isSubmersion_source (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (X : Type*) [TopologicalSpace X] [ChartedSpace H X] [IsManifold I n X] :
    Manifold.IsSubmersion (I.prod I) I n
      (Quiver.Total.left : Quiver.Total (Codiscrete X) → Codiscrete X) := by
  let e := (arrowDiffeomorph I n X).trans (Diffeomorph.prodComm I I X X n)
  have heq : (Quiver.Total.left : Quiver.Total (Codiscrete X) → Codiscrete X) =
      ⇑(objectDiffeomorph I n X).symm ∘ Prod.fst ∘ ⇑e := by
    ext ⟨⟨_⟩, ⟨_⟩, _⟩; simp [e]
  rw [heq]
  exact (objectDiffeomorph I n X).symm.isLocalDiffeomorph.comp_isSubmersion
    (e.isLocalDiffeomorph.isSubmersion_comp Manifold.isSubmersion_fst)

end Charts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  (X : Type*) [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]

/-- The pair groupoid on any Hausdorff second-countable boundaryless smooth manifold is a Lie
groupoid. -/
instance isLieGroupoid [T2Space X] [SecondCountableTopology X] :
    IsLieGroupoid I (I.prod I) (Codiscrete X) := by
  have hs := isSubmersion_source I ∞ X
  have hinv : ContMDiff (I.prod I) (I.prod I) ∞ fun a : Quiver.Total (Codiscrete X) ↦
      (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total (Codiscrete X)) :=
    ((arrowDiffeomorph I ∞ X).symm.contMDiff.comp
      ((arrowDiffeomorph I ∞ X).contMDiff.snd.prodMk
        (arrowDiffeomorph I ∞ X).contMDiff.fst)).congr
      fun a ↦ (arrowHomeomorph X).injective (by simp)
  refine IsLieGroupoid.of_isSubmersion_source hs hinv ?_
    (arrowHomeomorph X).isEmbedding.secondCountableTopology
    (objectHomeomorph X).isEmbedding.t2Space fun _ ↦ by
      have : T2Space (Quiver.Total (Codiscrete X)) := (arrowHomeomorph X).isEmbedding.t2Space
      exact Topology.IsEmbedding.subtypeVal.t2Space
  let := transverseFiberProductChartedSpace (f := Quiver.Total.right) (g := Quiver.Total.left)
    (by simp : (1 : ℕ∞ω) ≤ ∞) (hs.contMDiff.comp hinv) hs.contMDiff
    (fun p _ ↦ hs.transverse_right (by simp) _ p)
  have hι := isSmoothEmbedding_coe_transverseFiberProduct
    (f := Quiver.Total.right) (g := Quiver.Total.left)
    (by simp : (1 : ℕ∞ω) ≤ ∞) (hs.contMDiff.comp hinv) hs.contMDiff
    (fun p _ ↦ hs.transverse_right (by simp) _ p)
  exact ((arrowDiffeomorph I ∞ X).symm.contMDiff.comp
    (((arrowDiffeomorph I ∞ X).contMDiff.comp hι.contMDiff.snd).fst.prodMk
      ((arrowDiffeomorph I ∞ X).contMDiff.comp hι.contMDiff.fst).snd)).congr
    fun p ↦ (arrowHomeomorph X).injective (by simp)

section FiberTranslations

variable [T2Space X] [SecondCountableTopology X]

/-- Target identifies each source fibre `s⁻¹(x)` of the pair groupoid diffeomorphically with `X`,
sending `(z, x)` to `z`. -/
def sourceFiberDiffeomorph (x : Codiscrete X) :
    letI := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) (Codiscrete X) x
    IsLieGroupoid.SourceFiber (Codiscrete X) x ≃ₘ^∞⟮
      𝓘(ℝ, Fin (finrank ℝ (E × E) - finrank ℝ E) → ℝ), I⟯ X :=
  letI := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) (Codiscrete X) x
  { toFun := fun h ↦ h.1.right.as, invFun := fun z ↦ ⟨⟨x, ⟨z⟩, default⟩, rfl⟩
    left_inv := fun ⟨⟨⟨_⟩, ⟨_⟩, ⟨⟩⟩, rfl⟩ ↦ rfl, right_inv := fun _ ↦ rfl
    contMDiff_toFun :=
      (((arrowDiffeomorph I ∞ X).contMDiff.comp
        (IsLieGroupoid.isSmoothEmbedding_coe_sourceFiber
          I (I.prod I) (Codiscrete X) x).contMDiff).fst).congr fun h ↦ by simp
    contMDiff_invFun :=
      (IsLieGroupoid.isSmoothEmbedding_coe_sourceFiber
        I (I.prod I) (Codiscrete X) x).contMDiff_iff_comp.mpr
        (((arrowDiffeomorph I ∞ X).symm.contMDiff.comp
          (contMDiff_id.prodMk (contMDiff_const (c := x.as)))).congr
          fun z ↦ (arrowHomeomorph X).injective (by simp)) }

@[simp] theorem sourceFiberDiffeomorph_apply (x : Codiscrete X)
    (h : IsLieGroupoid.SourceFiber (Codiscrete X) x) :
    letI := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) (Codiscrete X) x
    sourceFiberDiffeomorph I X x h = h.1.right.as := (rfl)

@[simp] theorem sourceFiberDiffeomorph_symm_apply (x : Codiscrete X) (z : X) :
    letI := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) (Codiscrete X) x
    (sourceFiberDiffeomorph I X x).symm z = ⟨⟨x, ⟨z⟩, default⟩, rfl⟩ := (rfl)

/-- Source identifies each target fibre `t⁻¹(x)` of the pair groupoid diffeomorphically with `X`,
sending `(x, w)` to `w`. -/
def targetFiberDiffeomorph (x : Codiscrete X) :
    letI := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) (Codiscrete X) x
    IsLieGroupoid.TargetFiber (Codiscrete X) x ≃ₘ^∞⟮
      𝓘(ℝ, Fin (finrank ℝ (E × E) - finrank ℝ E) → ℝ), I⟯ X :=
  letI := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) (Codiscrete X) x
  { toFun := fun h ↦ h.1.left.as, invFun := fun w ↦ ⟨⟨⟨w⟩, x, default⟩, rfl⟩
    left_inv := fun ⟨⟨⟨_⟩, ⟨_⟩, ⟨⟩⟩, rfl⟩ ↦ rfl, right_inv := fun _ ↦ rfl
    contMDiff_toFun :=
      (((arrowDiffeomorph I ∞ X).contMDiff.comp
        (IsLieGroupoid.isSmoothEmbedding_coe_targetFiber
          I (I.prod I) (Codiscrete X) x).contMDiff).snd).congr fun h ↦ by simp
    contMDiff_invFun :=
      (IsLieGroupoid.isSmoothEmbedding_coe_targetFiber
        I (I.prod I) (Codiscrete X) x).contMDiff_iff_comp.mpr
        (((arrowDiffeomorph I ∞ X).symm.contMDiff.comp
          ((contMDiff_const (c := x.as)).prodMk contMDiff_id)).congr
          fun w ↦ (arrowHomeomorph X).injective (by simp)) }

@[simp] theorem targetFiberDiffeomorph_apply (x : Codiscrete X)
    (h : IsLieGroupoid.TargetFiber (Codiscrete X) x) :
    letI := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) (Codiscrete X) x
    targetFiberDiffeomorph I X x h = h.1.left.as := (rfl)

@[simp] theorem targetFiberDiffeomorph_symm_apply (x : Codiscrete X) (w : X) :
    letI := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) (Codiscrete X) x
    (targetFiberDiffeomorph I X x).symm w = ⟨⟨⟨w⟩, x, default⟩, rfl⟩ := (rfl)

/-- In `(target, source)` coordinates, right translation along an arrow `g` with coordinates
`(y, x)` sends `(z, y) ∈ s⁻¹(y)` to `(z, x) ∈ s⁻¹(x)`. -/
theorem arrowHomeomorph_rightTranslateDiffeomorph (g : Quiver.Total (Codiscrete X))
    (h : IsLieGroupoid.SourceFiber (Codiscrete X) g.right) :
    letI := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) (Codiscrete X) g.right
    letI := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) (Codiscrete X) g.left
    arrowHomeomorph X
      (IsLieGroupoid.rightTranslateDiffeomorph I (I.prod I) (Codiscrete X) g h).1 =
      (h.1.right.as, g.left.as) := by simp

/-- Under the target-coordinate identifications `s⁻¹(y) ≃ₘ X ≃ₘ s⁻¹(x)`, right translation in the
pair groupoid is the identity on `X`. -/
theorem sourceFiberDiffeomorph_rightTranslateDiffeomorph (g : Quiver.Total (Codiscrete X))
    (h : IsLieGroupoid.SourceFiber (Codiscrete X) g.right) :
    letI := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) (Codiscrete X) g.right
    letI := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) (Codiscrete X) g.left
    sourceFiberDiffeomorph I X g.left
      (IsLieGroupoid.rightTranslateDiffeomorph I (I.prod I) (Codiscrete X) g h) =
      sourceFiberDiffeomorph I X g.right h := by simp

/-- In `(target, source)` coordinates, left translation along an arrow `g` with coordinates
`(y, x)` sends `(x, w) ∈ t⁻¹(x)` to `(y, w) ∈ t⁻¹(y)`. -/
theorem arrowHomeomorph_leftTranslateDiffeomorph (g : Quiver.Total (Codiscrete X))
    (h : IsLieGroupoid.TargetFiber (Codiscrete X) g.left) :
    letI := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) (Codiscrete X) g.left
    letI := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) (Codiscrete X) g.right
    arrowHomeomorph X
      (IsLieGroupoid.leftTranslateDiffeomorph I (I.prod I) (Codiscrete X) g h).1 =
      (g.right.as, h.1.left.as) := by simp

/-- Under the source-coordinate identifications `t⁻¹(x) ≃ₘ X ≃ₘ t⁻¹(y)`, left translation in the
pair groupoid is the identity on `X`. -/
theorem targetFiberDiffeomorph_leftTranslateDiffeomorph (g : Quiver.Total (Codiscrete X))
    (h : IsLieGroupoid.TargetFiber (Codiscrete X) g.left) :
    letI := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) (Codiscrete X) g.left
    letI := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) (Codiscrete X) g.right
    targetFiberDiffeomorph I X g.right
      (IsLieGroupoid.leftTranslateDiffeomorph I (I.prod I) (Codiscrete X) g h) =
      targetFiberDiffeomorph I X g.left h := by simp

end FiberTranslations

end

end PairGroupoid

end TauCeti
