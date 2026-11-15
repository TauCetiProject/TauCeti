/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Groupoid.Translation
public import TauCeti.Geometry.Manifold.PullbackGroupoid
public import TauCeti.Topology.CategoryTheory.Groupoid.Examples
import Mathlib.Topology.Bases

/-!
# Unit and pair Lie groupoids

For any finite-dimensional boundaryless smooth real manifold `X`:

* **The unit Lie groupoid** `Discrete X` (`TauCeti.UnitGroupoid.isLieGroupoid`): objects and total
  arrows are both canonically diffeomorphic to `X`, source is a global diffeomorphism (providing a
  canonical étale Lie groupoid witness), and `[SecondCountableTopology X]` suffices without
  global Hausdorffness of `X` because every source fibre is a subsingleton.
* **The pair Lie groupoid** `Codiscrete X` (`TauCeti.PairGroupoid.isLieGroupoid`): for Hausdorff
  second-countable `X`, objects are diffeomorphic to `X` and total arrows are diffeomorphic to
  `X × X` in `(target, source)` coordinates. Every source fibre `s⁻¹(x)` is diffeomorphic to `X`
  via target (`PairGroupoid.sourceFiberDiffeomorph`), every target fibre `t⁻¹(x)` is diffeomorphic
  to `X` via source (`PairGroupoid.targetFiberDiffeomorph`), and for an arrow `g` with coordinates
  `(y, x)` right translation sends `(z, y) ↦ (z, x)` (acting as `id_X` under the target-coordinate
  identifications of `s⁻¹(y)` and `s⁻¹(x)` with `X`).

## References

* K. C. H. Mackenzie, *General Theory of Lie Groupoids and Lie Algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), Examples 1.1.7 and 1.1.8.
* I. Moerdijk and J. Mrčun, *Introduction to Foliations and Lie Groupoids*, Cambridge Stud. Adv.
  Math. 91, Cambridge University Press (2003), Examples 5.1(1)–(2).
-/

public section

noncomputable section

open CategoryTheory Function Module Set Topology
open scoped Manifold ContDiff

namespace TauCeti

/-! ### Unit Lie groupoid -/

namespace UnitGroupoid

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (X : Type*) [TopologicalSpace X] [ChartedSpace H X]

/-- Smooth atlas on the objects of the unit groupoid pulled back from `X`. -/
instance instChartedSpaceObjects : ChartedSpace H (Discrete X) :=
  (objectHomeomorph X).pullbackChartedSpace

instance instIsManifoldObjects [IsManifold I ∞ X] : IsManifold I ∞ (Discrete X) :=
  (objectHomeomorph X).pullback_isManifold I ∞

/-- Smooth diffeomorphism identifying objects of the unit groupoid with `X`. -/
def objectDiffeomorph : Discrete X ≃ₘ^∞⟮I, I⟯ X :=
  (objectHomeomorph X).pullbackDiffeomorph I ∞

@[simp]
theorem coe_objectDiffeomorph : ⇑(objectDiffeomorph I X) = objectHomeomorph X :=
  (objectHomeomorph X).coe_pullbackDiffeomorph I ∞

@[simp]
theorem coe_objectDiffeomorph_symm :
    ⇑(objectDiffeomorph I X).symm = (objectHomeomorph X).symm :=
  (objectHomeomorph X).coe_pullbackDiffeomorph_symm I ∞

/-- Smooth atlas on the total arrows of the unit groupoid pulled back from `X`. -/
instance instChartedSpaceArrows : ChartedSpace H (Quiver.Total (Discrete X)) :=
  (arrowHomeomorph X).pullbackChartedSpace

instance instIsManifoldArrows [IsManifold I ∞ X] : IsManifold I ∞ (Quiver.Total (Discrete X)) :=
  (arrowHomeomorph X).pullback_isManifold I ∞

/-- Smooth diffeomorphism identifying total arrows of the unit groupoid with `X`. -/
def arrowDiffeomorph : Quiver.Total (Discrete X) ≃ₘ^∞⟮I, I⟯ X :=
  (arrowHomeomorph X).pullbackDiffeomorph I ∞

@[simp]
theorem coe_arrowDiffeomorph : ⇑(arrowDiffeomorph I X) = arrowHomeomorph X :=
  (arrowHomeomorph X).coe_pullbackDiffeomorph I ∞

@[simp]
theorem coe_arrowDiffeomorph_symm :
    ⇑(arrowDiffeomorph I X).symm = (arrowHomeomorph X).symm :=
  (arrowHomeomorph X).coe_pullbackDiffeomorph_symm I ∞

/-- Source on the unit groupoid as a global smooth diffeomorphism. -/
def sourceDiffeomorph : Quiver.Total (Discrete X) ≃ₘ^∞⟮I, I⟯ Discrete X :=
  (arrowDiffeomorph I X).trans (objectDiffeomorph I X).symm

@[simp]
theorem coe_sourceDiffeomorph : ⇑(sourceDiffeomorph I X) = Quiver.Total.left := by
  funext ⟨⟨_⟩, _, _⟩
  simp [sourceDiffeomorph]

/-- Source on the unit Lie groupoid is a local diffeomorphism (the canonical étale witness). -/
theorem isLocalDiffeomorph_source :
    IsLocalDiffeomorph I I ∞ (Quiver.Total.left : Quiver.Total (Discrete X) → Discrete X) := by
  rw [← coe_sourceDiffeomorph I X]
  exact (sourceDiffeomorph I X).isLocalDiffeomorph

/-- Every source fibre of the unit groupoid is a subsingleton, hence Hausdorff without assuming
`[T2Space X]`. -/
instance instSubsingletonSourceFiber {X : Type*} (x : Discrete X) :
    Subsingleton {a : Quiver.Total (Discrete X) // a.left = x} :=
  ⟨fun ⟨⟨⟨_⟩, ⟨_⟩, f⟩, ha⟩ ⟨⟨⟨_⟩, ⟨_⟩, g⟩, hb⟩ ↦ by
    obtain ⟨x⟩ := x
    obtain rfl := Discrete.eq_of_hom f
    obtain rfl := Discrete.eq_of_hom g
    cases ha
    cases hb
    exact Subtype.ext (Quiver.Total.ext rfl rfl (heq_of_eq (Subsingleton.elim _ _)))⟩

/-- The unit groupoid on any second-countable boundaryless smooth manifold is a Lie groupoid. -/
instance isLieGroupoid [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ X]
    [SecondCountableTopology X] : IsLieGroupoid I I (Discrete X) := by
  have hs : Manifold.IsSubmersion I I ∞
      (Quiver.Total.left : Quiver.Total (Discrete X) → Discrete X) := by
    rw [← coe_sourceDiffeomorph I X]
    exact ((sourceDiffeomorph I X).contMDiff.isSubmersionOfComplement_of_surjective_mfderiv
      (by simp) fun a ↦
        ((sourceDiffeomorph I X).isLocalDiffeomorph a).mfderivToContinuousLinearEquiv
          (by simp) |>.surjective).isSubmersion
  have hu : ContMDiff I I ∞ fun x : Discrete X ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total (Discrete X)) := by
    convert (arrowDiffeomorph I X).symm.contMDiff.comp (objectDiffeomorph I X).contMDiff using 1
    funext ⟨_⟩
    simp
  have hinv : ContMDiff I I ∞ fun a : Quiver.Total (Discrete X) ↦
      (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total (Discrete X)) := by
    have heq : (fun a : Quiver.Total (Discrete X) ↦
        (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total (Discrete X))) = id := by
      funext ⟨⟨_⟩, ⟨_⟩, f⟩
      obtain rfl := Discrete.eq_of_hom f
      exact Quiver.Total.ext rfl rfl (heq_of_eq (Subsingleton.elim _ _))
    rw [heq]
    exact contMDiff_id
  refine IsLieGroupoid.of_isSubmersion_source hs hu hinv ?_ ?_ fun _ ↦ inferInstance
  · let := transverseFiberProductChartedSpace (f := Quiver.Total.right) (g := Quiver.Total.left)
      (by simp : (1 : ℕ∞ω) ≤ ∞) (hs.contMDiff.comp hinv) hs.contMDiff
      (fun p _ ↦ hs.transverse_right (by simp) _ p)
    have := isManifold_transverseFiberProduct (f := Quiver.Total.right) (g := Quiver.Total.left)
      (by simp : (1 : ℕ∞ω) ≤ ∞) (hs.contMDiff.comp hinv) hs.contMDiff
      (fun p _ ↦ hs.transverse_right (by simp) _ p)
    have hι := isSmoothEmbedding_coe_transverseFiberProduct
      (f := Quiver.Total.right) (g := Quiver.Total.left)
      (by simp : (1 : ℕ∞ω) ≤ ∞) (hs.contMDiff.comp hinv) hs.contMDiff
      (fun p _ ↦ hs.transverse_right (by simp) _ p)
    have heq : (fun p : IsLieGroupoid.ComposablePairs (Discrete X) ↦ p.1.1.comp p.1.2 p.2) =
        fun p ↦ p.1.1 := by
      funext ⟨⟨⟨⟨x⟩, ⟨y⟩, f⟩, ⟨⟨y'⟩, ⟨z⟩, g⟩⟩, hp⟩
      obtain rfl := Discrete.eq_of_hom f
      obtain rfl := Discrete.eq_of_hom g
      dsimp only at hp
      cases hp
      rw [Quiver.Total.comp_def]
      exact Quiver.Total.ext rfl rfl (heq_of_eq (Subsingleton.elim _ _))
    rw [heq]
    exact hι.contMDiff.fst
  · exact (arrowHomeomorph X).isEmbedding.secondCountableTopology

end UnitGroupoid

/-! ### Pair Lie groupoid -/

namespace PairGroupoid

section Charts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (X : Type*) [TopologicalSpace X] [ChartedSpace H X]

/-- Smooth atlas on the objects of the pair groupoid pulled back from `X`. -/
instance instChartedSpaceObjects : ChartedSpace H (Codiscrete X) :=
  (objectHomeomorph X).pullbackChartedSpace

instance instIsManifoldObjects [IsManifold I ∞ X] : IsManifold I ∞ (Codiscrete X) :=
  (objectHomeomorph X).pullback_isManifold I ∞

/-- Smooth diffeomorphism identifying objects of the pair groupoid with `X`. -/
def objectDiffeomorph : Codiscrete X ≃ₘ^∞⟮I, I⟯ X :=
  (objectHomeomorph X).pullbackDiffeomorph I ∞

@[simp]
theorem coe_objectDiffeomorph : ⇑(objectDiffeomorph I X) = objectHomeomorph X :=
  (objectHomeomorph X).coe_pullbackDiffeomorph I ∞

@[simp]
theorem coe_objectDiffeomorph_symm :
    ⇑(objectDiffeomorph I X).symm = (objectHomeomorph X).symm :=
  (objectHomeomorph X).coe_pullbackDiffeomorph_symm I ∞

/-- Smooth atlas on the total arrows of the pair groupoid pulled back from `X × X` in
`(target, source)` coordinates. -/
instance instChartedSpaceArrows : ChartedSpace (ModelProd H H) (Quiver.Total (Codiscrete X)) :=
  (arrowHomeomorph X).pullbackChartedSpace

instance instIsManifoldArrows [IsManifold I ∞ X] :
    IsManifold (I.prod I) ∞ (Quiver.Total (Codiscrete X)) :=
  (arrowHomeomorph X).pullback_isManifold (I.prod I) ∞

/-- Smooth diffeomorphism identifying total arrows of the pair groupoid with `X × X` via
`a ↦ (a.right.as, a.left.as)`. -/
def arrowDiffeomorph : Quiver.Total (Codiscrete X) ≃ₘ^∞⟮I.prod I, I.prod I⟯ X × X :=
  (arrowHomeomorph X).pullbackDiffeomorph (I.prod I) ∞

@[simp]
theorem coe_arrowDiffeomorph : ⇑(arrowDiffeomorph I X) = arrowHomeomorph X :=
  (arrowHomeomorph X).coe_pullbackDiffeomorph (I.prod I) ∞

@[simp]
theorem coe_arrowDiffeomorph_symm :
    ⇑(arrowDiffeomorph I X).symm = (arrowHomeomorph X).symm :=
  (arrowHomeomorph X).coe_pullbackDiffeomorph_symm (I.prod I) ∞

end Charts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  (X : Type*) [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]

/-- Source on the pair groupoid is a smooth submersion: in `(target, source)` coordinates it is the
second projection `X × X → X`. -/
theorem isSubmersion_source :
    Manifold.IsSubmersion (I.prod I) I ∞
      (Quiver.Total.left : Quiver.Total (Codiscrete X) → Codiscrete X) := by
  have hs_smooth : ContMDiff (I.prod I) I ∞
      (Quiver.Total.left : Quiver.Total (Codiscrete X) → Codiscrete X) := by
    convert (objectDiffeomorph I X).symm.contMDiff.comp
      (arrowDiffeomorph I X).contMDiff.snd using 1
    funext ⟨⟨_⟩, ⟨_⟩, _⟩
    simp
  refine (hs_smooth.isSubmersionOfComplement_of_surjective_mfderiv
    (by simp) fun a ↦ ?_).isSubmersion
  let σ : Codiscrete X → Quiver.Total (Codiscrete X) :=
    fun x ↦ (arrowDiffeomorph I X).symm (a.right.as, objectDiffeomorph I X x)
  have hσ : ContMDiff I (I.prod I) ∞ σ :=
    (arrowDiffeomorph I X).symm.contMDiff.comp
      (contMDiff_const.prodMk (objectDiffeomorph I X).contMDiff)
  have hσa : σ a.left = a :=
    (arrowHomeomorph X).injective (by simp [σ])
  have hleft_σ : (Quiver.Total.left ∘ σ) = id := by
    funext ⟨_⟩
    simp [σ]
  have hcomp := mfderiv_comp a.left
    ((hs_smooth (σ a.left)).mdifferentiableAt (by simp))
    ((hσ a.left).mdifferentiableAt (by simp))
  rw [hleft_σ, mfderiv_id, hσa] at hcomp
  exact Function.LeftInverse.surjective (DFunLike.congr_fun hcomp.symm)

/-- The pair groupoid on any Hausdorff second-countable boundaryless smooth manifold is a Lie
groupoid. -/
instance isLieGroupoid [T2Space X] [SecondCountableTopology X] :
    IsLieGroupoid I (I.prod I) (Codiscrete X) := by
  have hs := isSubmersion_source I X
  have hu : ContMDiff I (I.prod I) ∞
      fun x : Codiscrete X ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total (Codiscrete X)) := by
    convert (arrowDiffeomorph I X).symm.contMDiff.comp
      ((objectDiffeomorph I X).contMDiff.prodMk (objectDiffeomorph I X).contMDiff) using 1
    funext ⟨_⟩
    exact (arrowHomeomorph X).injective (by simp)
  have hinv : ContMDiff (I.prod I) (I.prod I) ∞ fun a : Quiver.Total (Codiscrete X) ↦
      (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total (Codiscrete X)) := by
    convert (arrowDiffeomorph I X).symm.contMDiff.comp
      ((arrowDiffeomorph I X).contMDiff.snd.prodMk (arrowDiffeomorph I X).contMDiff.fst) using 1
    funext a
    exact (arrowHomeomorph X).injective (by simp)
  refine IsLieGroupoid.of_isSubmersion_source hs hu hinv ?_ ?_ ?_
  · let := transverseFiberProductChartedSpace (f := Quiver.Total.right) (g := Quiver.Total.left)
      (by simp : (1 : ℕ∞ω) ≤ ∞) (hs.contMDiff.comp hinv) hs.contMDiff
      (fun p _ ↦ hs.transverse_right (by simp) _ p)
    have := isManifold_transverseFiberProduct (f := Quiver.Total.right) (g := Quiver.Total.left)
      (by simp : (1 : ℕ∞ω) ≤ ∞) (hs.contMDiff.comp hinv) hs.contMDiff
      (fun p _ ↦ hs.transverse_right (by simp) _ p)
    have hι := isSmoothEmbedding_coe_transverseFiberProduct
      (f := Quiver.Total.right) (g := Quiver.Total.left)
      (by simp : (1 : ℕ∞ω) ≤ ∞) (hs.contMDiff.comp hinv) hs.contMDiff
      (fun p _ ↦ hs.transverse_right (by simp) _ p)
    have heq : (fun p : IsLieGroupoid.ComposablePairs (Codiscrete X) ↦ p.1.1.comp p.1.2 p.2) =
        fun p ↦ (arrowDiffeomorph I X).symm
          ((arrowDiffeomorph I X p.1.2).1, (arrowDiffeomorph I X p.1.1).2) := by
      funext p
      exact (arrowHomeomorph X).injective (by simp)
    rw [heq]
    exact (arrowDiffeomorph I X).symm.contMDiff.comp
      (((arrowDiffeomorph I X).contMDiff.comp hι.contMDiff.snd).fst.prodMk
        ((arrowDiffeomorph I X).contMDiff.comp hι.contMDiff.fst).snd)
  · exact (arrowHomeomorph X).isEmbedding.secondCountableTopology
  · intro x
    have : T2Space (Quiver.Total (Codiscrete X)) := (arrowHomeomorph X).isEmbedding.t2Space
    exact Topology.IsEmbedding.subtypeVal.t2Space

section FiberTranslations

variable [T2Space X] [SecondCountableTopology X]

/-- Target identifies each source fibre `s⁻¹(x)` of the pair groupoid diffeomorphically with `X`,
sending `(z, x)` to `z`. -/
def sourceFiberDiffeomorph (x : Codiscrete X) :
    letI := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) (Codiscrete X) x
    IsLieGroupoid.SourceFiber (Codiscrete X) x ≃ₘ^∞⟮
      𝓘(ℝ, Fin (finrank ℝ (E × E) - finrank ℝ E) → ℝ), I⟯ X :=
  letI := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) (Codiscrete X) x
  { toFun := fun h ↦ h.1.right.as
    invFun := fun z ↦ ⟨⟨x, ⟨z⟩, default⟩, rfl⟩
    left_inv := fun ⟨⟨⟨_⟩, ⟨_⟩, ⟨⟩⟩, rfl⟩ ↦ rfl
    right_inv := fun _ ↦ rfl
    contMDiff_toFun := by
      have := IsLieGroupoid.isManifold_sourceFiber I (I.prod I) (Codiscrete X) x
      convert ((arrowDiffeomorph I X).contMDiff.comp
        (IsLieGroupoid.isSmoothEmbedding_coe_sourceFiber
          I (I.prod I) (Codiscrete X) x).contMDiff).fst using 1
      funext h
      simp
    contMDiff_invFun := by
      have := IsLieGroupoid.isManifold_sourceFiber I (I.prod I) (Codiscrete X) x
      apply (IsLieGroupoid.isSmoothEmbedding_coe_sourceFiber
        I (I.prod I) (Codiscrete X) x).contMDiff_iff_comp.mpr
      convert (arrowDiffeomorph I X).symm.contMDiff.comp
        (contMDiff_id.prodMk (contMDiff_const (c := x.as))) using 1
      funext z
      exact (arrowHomeomorph X).injective (by simp) }

@[simp]
theorem sourceFiberDiffeomorph_apply (x : Codiscrete X)
    (h : IsLieGroupoid.SourceFiber (Codiscrete X) x) :
    letI := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) (Codiscrete X) x
    sourceFiberDiffeomorph I X x h = h.1.right.as :=
  (rfl)

@[simp]
theorem sourceFiberDiffeomorph_symm_apply (x : Codiscrete X) (z : X) :
    letI := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) (Codiscrete X) x
    (sourceFiberDiffeomorph I X x).symm z = ⟨⟨x, ⟨z⟩, default⟩, rfl⟩ :=
  (rfl)

/-- Source identifies each target fibre `t⁻¹(x)` of the pair groupoid diffeomorphically with `X`,
sending `(x, w)` to `w`. -/
def targetFiberDiffeomorph (x : Codiscrete X) :
    letI := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) (Codiscrete X) x
    IsLieGroupoid.TargetFiber (Codiscrete X) x ≃ₘ^∞⟮
      𝓘(ℝ, Fin (finrank ℝ (E × E) - finrank ℝ E) → ℝ), I⟯ X :=
  letI := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) (Codiscrete X) x
  { toFun := fun h ↦ h.1.left.as
    invFun := fun w ↦ ⟨⟨⟨w⟩, x, default⟩, rfl⟩
    left_inv := fun ⟨⟨⟨_⟩, ⟨_⟩, ⟨⟩⟩, rfl⟩ ↦ rfl
    right_inv := fun _ ↦ rfl
    contMDiff_toFun := by
      have := IsLieGroupoid.isManifold_targetFiber I (I.prod I) (Codiscrete X) x
      convert ((arrowDiffeomorph I X).contMDiff.comp
        (IsLieGroupoid.isSmoothEmbedding_coe_targetFiber
          I (I.prod I) (Codiscrete X) x).contMDiff).snd using 1
      funext h
      simp
    contMDiff_invFun := by
      have := IsLieGroupoid.isManifold_targetFiber I (I.prod I) (Codiscrete X) x
      apply (IsLieGroupoid.isSmoothEmbedding_coe_targetFiber
        I (I.prod I) (Codiscrete X) x).contMDiff_iff_comp.mpr
      convert (arrowDiffeomorph I X).symm.contMDiff.comp
        ((contMDiff_const (c := x.as)).prodMk contMDiff_id) using 1
      funext w
      exact (arrowHomeomorph X).injective (by simp) }

@[simp]
theorem targetFiberDiffeomorph_apply (x : Codiscrete X)
    (h : IsLieGroupoid.TargetFiber (Codiscrete X) x) :
    letI := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) (Codiscrete X) x
    targetFiberDiffeomorph I X x h = h.1.left.as :=
  (rfl)

@[simp]
theorem targetFiberDiffeomorph_symm_apply (x : Codiscrete X) (w : X) :
    letI := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) (Codiscrete X) x
    (targetFiberDiffeomorph I X x).symm w = ⟨⟨⟨w⟩, x, default⟩, rfl⟩ :=
  (rfl)

/-- In `(target, source)` coordinates, right translation along an arrow `g` with coordinates
`(y, x)` sends `(z, y) ∈ s⁻¹(y)` to `(z, x) ∈ s⁻¹(x)`. -/
theorem arrowHomeomorph_rightTranslateDiffeomorph (g : Quiver.Total (Codiscrete X))
    (h : IsLieGroupoid.SourceFiber (Codiscrete X) g.right) :
    letI := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) (Codiscrete X) g.right
    letI := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) (Codiscrete X) g.left
    arrowHomeomorph X
      (IsLieGroupoid.rightTranslateDiffeomorph I (I.prod I) (Codiscrete X) g h).1 =
      (h.1.right.as, g.left.as) := by
  simp

/-- Under the target-coordinate identifications `s⁻¹(y) ≃ₘ X ≃ₘ s⁻¹(x)`, right translation in the
pair groupoid is the identity on `X`. -/
theorem sourceFiberDiffeomorph_rightTranslateDiffeomorph (g : Quiver.Total (Codiscrete X))
    (h : IsLieGroupoid.SourceFiber (Codiscrete X) g.right) :
    letI := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) (Codiscrete X) g.right
    letI := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) (Codiscrete X) g.left
    sourceFiberDiffeomorph I X g.left
      (IsLieGroupoid.rightTranslateDiffeomorph I (I.prod I) (Codiscrete X) g h) =
      sourceFiberDiffeomorph I X g.right h := by
  simp

/-- In `(target, source)` coordinates, left translation along an arrow `g` with coordinates
`(y, x)` sends `(x, w) ∈ t⁻¹(x)` to `(y, w) ∈ t⁻¹(y)`. -/
theorem arrowHomeomorph_leftTranslateDiffeomorph (g : Quiver.Total (Codiscrete X))
    (h : IsLieGroupoid.TargetFiber (Codiscrete X) g.left) :
    letI := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) (Codiscrete X) g.left
    letI := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) (Codiscrete X) g.right
    arrowHomeomorph X
      (IsLieGroupoid.leftTranslateDiffeomorph I (I.prod I) (Codiscrete X) g h).1 =
      (g.right.as, h.1.left.as) := by
  simp

/-- Under the source-coordinate identifications `t⁻¹(x) ≃ₘ X ≃ₘ t⁻¹(y)`, left translation in the
pair groupoid is the identity on `X`. -/
theorem targetFiberDiffeomorph_leftTranslateDiffeomorph (g : Quiver.Total (Codiscrete X))
    (h : IsLieGroupoid.TargetFiber (Codiscrete X) g.left) :
    letI := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) (Codiscrete X) g.left
    letI := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) (Codiscrete X) g.right
    targetFiberDiffeomorph I X g.right
      (IsLieGroupoid.leftTranslateDiffeomorph I (I.prod I) (Codiscrete X) g h) =
      targetFiberDiffeomorph I X g.left h := by
  simp

end FiberTranslations

end PairGroupoid

end TauCeti
