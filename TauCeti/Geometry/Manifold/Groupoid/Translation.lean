/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Groupoid.Basic
public import TauCeti.Geometry.Manifold.RegularValue.ManifoldLevel
import Mathlib.Topology.Bases

/-!
# Source and target fibres and smooth translations in a Lie groupoid

Every source fibre `SourceFiber C x = {a : Quiver.Total C // a.left = x}` and every target fibre
`TargetFiber C x = {a : Quiver.Total C // a.right = x}` of a Lie groupoid `C` is a regular fibre of
a smooth submersion between boundaryless manifolds, hence carries a smooth embedded submanifold
structure of dimension `dim Γ - dim M` retaining its subspace topology. Because `IsLieGroupoid`
requires second-countable total arrows and Hausdorff source fibres, every source fibre and every
target fibre is a Hausdorff second-countable smooth manifold even when `Quiver.Total C` itself is
non-Hausdorff.

Each arrow `g : Quiver.Total C` induces two canonical smooth fibre diffeomorphisms:
* **Right translation** `rightTranslateDiffeomorph I J C g`: sends `h ∈ SourceFiber C g.right` to
  `g.comp h` in `SourceFiber C g.left` (the geometric right-multiplication `h ↦ hg` from
  `s⁻¹(t(g))` to `s⁻¹(s(g))`), mapping the unit at `g.right` to `g` and preserving targets.
* **Left translation** `leftTranslateDiffeomorph I J C g`: sends `h ∈ TargetFiber C g.left` to
  `h.comp g` in `TargetFiber C g.right` (the geometric left-multiplication `h ↦ gh` from
  `t⁻¹(s(g))` to `t⁻¹(t(g))`), mapping the unit at `g.left` to `g` and preserving sources.

Inversion restricts to a smooth diffeomorphism `inverseSourceTargetDiffeomorph I J C x` between
`SourceFiber C x` and `TargetFiber C x`.

## References

* K. C. H. Mackenzie, *General Theory of Lie Groupoids and Lie Algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), Section 1.1 and Section 3.5.
* I. Moerdijk and J. Mrčun, *Introduction to Foliations and Lie Groupoids*, Cambridge Stud. Adv.
  Math. 91, Cambridge University Press (2003), Section 5.1.
-/

public section

noncomputable section

open CategoryTheory Function Module Set
open scoped Manifold ContDiff

namespace TauCeti.IsLieGroupoid

/-- The source fibre `s⁻¹(x)` over an object `x : C`. -/
abbrev SourceFiber (C : Type*) [Quiver C] (x : C) : Type _ :=
  {a : Quiver.Total C // a.left = x}

/-- The target fibre `t⁻¹(x)` over an object `x : C`. -/
abbrev TargetFiber (C : Type*) [Quiver C] (x : C) : Type _ :=
  {a : Quiver.Total C // a.right = x}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H') [J.Boundaryless]
  (C : Type*) [Category C] [IsGroupoid C]
  [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
  [IsManifold J ∞ (Quiver.Total C)] [IsLieGroupoid I J C]

/-! ### Embedded manifold structures on source and target fibres -/

/-- The regular-fibre smooth atlas of dimension `dim Γ - dim M` on the source fibre over `x`. -/
@[instance_reducible]
def sourceFiberChartedSpace (x : C) :
    ChartedSpace (Fin (finrank ℝ E' - finrank ℝ E) → ℝ) (SourceFiber C x) :=
  regularFiberChartedSpace (by simp : (1 : ℕ∞ω) ≤ ∞) (contMDiff_source I J C)
    BoundarylessManifold.isInteriorPoint (isRegularValue_source I J C x)

/-- Every source fibre of a Lie groupoid is a smooth manifold with its regular-fibre atlas. -/
theorem isManifold_sourceFiber (x : C) :
    letI := sourceFiberChartedSpace I J C x
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ∞ (SourceFiber C x) :=
  isManifold_regularFiber (by simp : (1 : ℕ∞ω) ≤ ∞) (contMDiff_source I J C)
    BoundarylessManifold.isInteriorPoint (isRegularValue_source I J C x)

/-- Inclusion of the source fibre over `x` into `Quiver.Total C` is a smooth embedding. -/
theorem isSmoothEmbedding_coe_sourceFiber (x : C) :
    letI := sourceFiberChartedSpace I J C x
    Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (Subtype.val : SourceFiber C x → Quiver.Total C) :=
  isSmoothEmbedding_coe_regularFiber (by simp : (1 : ℕ∞ω) ≤ ∞) (contMDiff_source I J C)
    BoundarylessManifold.isInteriorPoint (isRegularValue_source I J C x)

/-- The tangent space of the source fibre at `z` embeds onto the vertical kernel `ker (ds_{z.1})`.
At `1_x` this identifies the tangent space of `SourceFiber C x` with the Lie algebroid fibre over
`x`. -/
theorem range_mfderiv_coe_sourceFiber (x : C) :
    letI := sourceFiberChartedSpace I J C x
    ∀ z : SourceFiber C x,
      (mfderiv 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) J Subtype.val z).range =
        (mfderiv J I Quiver.Total.left z.1).ker :=
  range_mfderiv_coe_regularFiber (by simp : (1 : ℕ∞ω) ≤ ∞) (contMDiff_source I J C)
    BoundarylessManifold.isInteriorPoint (isRegularValue_source I J C x)

include I J in
/-- Every source fibre has a second-countable topology. -/
theorem secondCountableTopology_sourceFiber (x : C) :
    SecondCountableTopology (SourceFiber C x) := by
  have := secondCountable_arrows (I := I) (J := J) (C := C)
  exact Topology.IsEmbedding.subtypeVal.secondCountableTopology

/-- The regular-fibre smooth atlas of dimension `dim Γ - dim M` on the target fibre over `x`. -/
@[instance_reducible]
def targetFiberChartedSpace (x : C) :
    ChartedSpace (Fin (finrank ℝ E' - finrank ℝ E) → ℝ) (TargetFiber C x) :=
  regularFiberChartedSpace (by simp : (1 : ℕ∞ω) ≤ ∞) (contMDiff_target I J C)
    BoundarylessManifold.isInteriorPoint (isRegularValue_target I J C x)

/-- Every target fibre of a Lie groupoid is a smooth manifold with its regular-fibre atlas. -/
theorem isManifold_targetFiber (x : C) :
    letI := targetFiberChartedSpace I J C x
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ∞ (TargetFiber C x) :=
  isManifold_regularFiber (by simp : (1 : ℕ∞ω) ≤ ∞) (contMDiff_target I J C)
    BoundarylessManifold.isInteriorPoint (isRegularValue_target I J C x)

/-- Inclusion of the target fibre over `x` into `Quiver.Total C` is a smooth embedding. -/
theorem isSmoothEmbedding_coe_targetFiber (x : C) :
    letI := targetFiberChartedSpace I J C x
    Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (Subtype.val : TargetFiber C x → Quiver.Total C) :=
  isSmoothEmbedding_coe_regularFiber (by simp : (1 : ℕ∞ω) ≤ ∞) (contMDiff_target I J C)
    BoundarylessManifold.isInteriorPoint (isRegularValue_target I J C x)

/-- The tangent space of the target fibre at `z` embeds onto `ker (dt_{z.1})`. -/
theorem range_mfderiv_coe_targetFiber (x : C) :
    letI := targetFiberChartedSpace I J C x
    ∀ z : TargetFiber C x,
      (mfderiv 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) J Subtype.val z).range =
        (mfderiv J I Quiver.Total.right z.1).ker :=
  range_mfderiv_coe_regularFiber (by simp : (1 : ℕ∞ω) ≤ ∞) (contMDiff_target I J C)
    BoundarylessManifold.isInteriorPoint (isRegularValue_target I J C x)

include I J in
/-- Every target fibre has a second-countable topology. -/
theorem secondCountableTopology_targetFiber (x : C) :
    SecondCountableTopology (TargetFiber C x) := by
  have := secondCountable_arrows (I := I) (J := J) (C := C)
  exact Topology.IsEmbedding.subtypeVal.secondCountableTopology

/-! ### Inversion between source and target fibres -/

/-- Inversion restricts to a smooth diffeomorphism between the source fibre and the target fibre
over the same object `x`. -/
def inverseSourceTargetDiffeomorph (x : C) :
    letI := sourceFiberChartedSpace I J C x
    letI := targetFiberChartedSpace I J C x
    SourceFiber C x ≃ₘ^∞⟮𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)⟯ TargetFiber C x :=
  letI := sourceFiberChartedSpace I J C x
  letI := targetFiberChartedSpace I J C x
  { toFun := fun a ↦ ⟨inverseDiffeomorph I J C a.1, (inverseDiffeomorph_right I J C a.1).trans a.2⟩
    invFun := fun a ↦ ⟨inverseDiffeomorph I J C a.1, (inverseDiffeomorph_left I J C a.1).trans a.2⟩
    left_inv := fun a ↦ Subtype.ext (by obtain ⟨⟨_, _, _⟩, _⟩ := a; simp)
    right_inv := fun a ↦ Subtype.ext (by obtain ⟨⟨_, _, _⟩, _⟩ := a; simp)
    contMDiff_toFun := by
      have := isManifold_sourceFiber I J C x
      have := isManifold_targetFiber I J C x
      exact (isSmoothEmbedding_coe_targetFiber I J C x).contMDiff_iff_comp.mpr
        ((inverseDiffeomorph I J C).contMDiff.comp
          (isSmoothEmbedding_coe_sourceFiber I J C x).contMDiff)
    contMDiff_invFun := by
      have := isManifold_sourceFiber I J C x
      have := isManifold_targetFiber I J C x
      exact (isSmoothEmbedding_coe_sourceFiber I J C x).contMDiff_iff_comp.mpr
        ((inverseDiffeomorph I J C).contMDiff.comp
          (isSmoothEmbedding_coe_targetFiber I J C x).contMDiff) }

@[simp]
theorem inverseSourceTargetDiffeomorph_coe_apply (x : C) (a : SourceFiber C x) :
    letI := sourceFiberChartedSpace I J C x
    letI := targetFiberChartedSpace I J C x
    (inverseSourceTargetDiffeomorph I J C x a : Quiver.Total C) =
      inverseDiffeomorph I J C a.1 :=
  (rfl)

@[simp]
theorem inverseSourceTargetDiffeomorph_symm_coe_apply (x : C) (a : TargetFiber C x) :
    letI := sourceFiberChartedSpace I J C x
    letI := targetFiberChartedSpace I J C x
    ((inverseSourceTargetDiffeomorph I J C x).symm a : Quiver.Total C) =
      inverseDiffeomorph I J C a.1 :=
  (rfl)

/-! ### Smooth right and left translations along fibres -/

/-- Categorical left-composition by a fixed arrow `g` is smooth from `SourceFiber C g.right` to
`SourceFiber C g.left`. -/
theorem contMDiff_comp_left_sourceFiber (g : Quiver.Total C) :
    letI := sourceFiberChartedSpace I J C g.right
    letI := sourceFiberChartedSpace I J C g.left
    ContMDiff
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (fun h : SourceFiber C g.right ↦
        (⟨g.comp h.1 h.2.symm, g.comp_left h.1 h.2.symm⟩ : SourceFiber C g.left)) := by
  let := composablePairsChartedSpace I J C
  let := sourceFiberChartedSpace I J C g.right
  let := sourceFiberChartedSpace I J C g.left
  have := isManifold_composablePairs I J C
  have := isManifold_sourceFiber I J C g.right
  have := isManifold_sourceFiber I J C g.left
  have hpair : ContMDiff
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (fun h : SourceFiber C g.right ↦ (⟨(g, h.1), h.2.symm⟩ : ComposablePairs C)) :=
    (isSmoothEmbedding_coe_composablePairs I J C).contMDiff_iff_comp.mpr
      (contMDiff_const.prodMk (isSmoothEmbedding_coe_sourceFiber I J C g.right).contMDiff)
  exact (isSmoothEmbedding_coe_sourceFiber I J C g.left).contMDiff_iff_comp.mpr
    ((contMDiff_composablePairs_comp I J C).comp hpair)

/-- **Right translation along source fibres.** Pre-composing categorically with `g` (geometric
right multiplication `h ↦ hg`) is a smooth diffeomorphism from `SourceFiber C g.right` onto
`SourceFiber C g.left`, with smooth inverse given by right translation by `inv g`. -/
def rightTranslateDiffeomorph (g : Quiver.Total C) :
    letI := sourceFiberChartedSpace I J C g.right
    letI := sourceFiberChartedSpace I J C g.left
    SourceFiber C g.right ≃ₘ^∞⟮𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)⟯ SourceFiber C g.left :=
  letI := sourceFiberChartedSpace I J C g.right
  letI := sourceFiberChartedSpace I J C g.left
  { toFun := fun h ↦ ⟨g.comp h.1 h.2.symm, g.comp_left h.1 h.2.symm⟩
    invFun := fun k ↦
      ⟨(inverseDiffeomorph I J C g).comp k.1 ((inverseDiffeomorph_right I J C g).trans k.2.symm),
        ((inverseDiffeomorph I J C g).comp_left k.1 _).trans (inverseDiffeomorph_left I J C g)⟩
    left_inv := fun h ↦
      Subtype.ext
        ((Quiver.Total.comp_congr (inverseDiffeomorph_apply I J C g) rfl _
          (g.comp_left h.1 h.2.symm).symm).trans
          (Quiver.Total.inv_comp_comp g h.1 h.2.symm _))
    right_inv := fun k ↦
      Subtype.ext
        ((Quiver.Total.comp_congr rfl
          (Quiver.Total.comp_congr (inverseDiffeomorph_apply I J C g) rfl _ k.2.symm) _
          (Quiver.Total.comp_left ⟨g.right, g.left, inv g.hom⟩ k.1 k.2.symm).symm).trans
          (Quiver.Total.comp_inv_comp g k.1 k.2.symm _))
    contMDiff_toFun := contMDiff_comp_left_sourceFiber I J C g
    contMDiff_invFun := by
      let := composablePairsChartedSpace I J C
      have := isManifold_composablePairs I J C
      have := isManifold_sourceFiber I J C g.right
      have := isManifold_sourceFiber I J C g.left
      have hpair : ContMDiff
          𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
          𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
          (fun k : SourceFiber C g.left ↦
            (⟨(inverseDiffeomorph I J C g, k.1),
              (inverseDiffeomorph_right I J C g).trans k.2.symm⟩ : ComposablePairs C)) :=
        (isSmoothEmbedding_coe_composablePairs I J C).contMDiff_iff_comp.mpr
          (contMDiff_const.prodMk (isSmoothEmbedding_coe_sourceFiber I J C g.left).contMDiff)
      exact (isSmoothEmbedding_coe_sourceFiber I J C g.right).contMDiff_iff_comp.mpr
        ((contMDiff_composablePairs_comp I J C).comp hpair) }

@[simp]
theorem rightTranslateDiffeomorph_coe_apply (g : Quiver.Total C) (h : SourceFiber C g.right) :
    letI := sourceFiberChartedSpace I J C g.right
    letI := sourceFiberChartedSpace I J C g.left
    (rightTranslateDiffeomorph I J C g h : Quiver.Total C) = g.comp h.1 h.2.symm :=
  (rfl)

@[simp]
theorem rightTranslateDiffeomorph_symm_coe_apply (g : Quiver.Total C) (k : SourceFiber C g.left) :
    letI := sourceFiberChartedSpace I J C g.right
    letI := sourceFiberChartedSpace I J C g.left
    ((rightTranslateDiffeomorph I J C g).symm k : Quiver.Total C) =
      (inverseDiffeomorph I J C g).comp k.1
        ((inverseDiffeomorph_right I J C g).trans k.2.symm) :=
  (rfl)

/-- Right translation preserves target endpoints. -/
theorem rightTranslateDiffeomorph_right (g : Quiver.Total C) (h : SourceFiber C g.right) :
    letI := sourceFiberChartedSpace I J C g.right
    letI := sourceFiberChartedSpace I J C g.left
    (rightTranslateDiffeomorph I J C g h).1.right = h.1.right :=
  g.comp_right h.1 h.2.symm

@[simp]
theorem rightTranslateDiffeomorph_apply_unit (g : Quiver.Total C) :
    letI := sourceFiberChartedSpace I J C g.right
    letI := sourceFiberChartedSpace I J C g.left
    rightTranslateDiffeomorph I J C g ⟨⟨g.right, g.right, 𝟙 g.right⟩, rfl⟩ = ⟨g, rfl⟩ :=
  Subtype.ext (Quiver.Total.comp_unit g)

@[simp]
theorem rightTranslateDiffeomorph_unit (x : C) (h : SourceFiber C x) :
    letI := sourceFiberChartedSpace I J C x
    rightTranslateDiffeomorph I J C ⟨x, x, 𝟙 x⟩ h = h := by
  obtain ⟨a, rfl⟩ := h
  exact Subtype.ext (Quiver.Total.unit_comp a)

/-- Categorical right-composition by a fixed arrow `g` is smooth from `TargetFiber C g.left` to
`TargetFiber C g.right`. -/
theorem contMDiff_comp_right_targetFiber (g : Quiver.Total C) :
    letI := targetFiberChartedSpace I J C g.left
    letI := targetFiberChartedSpace I J C g.right
    ContMDiff
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (fun h : TargetFiber C g.left ↦
        (⟨h.1.comp g h.2, h.1.comp_right g h.2⟩ : TargetFiber C g.right)) := by
  let := composablePairsChartedSpace I J C
  let := targetFiberChartedSpace I J C g.left
  let := targetFiberChartedSpace I J C g.right
  have := isManifold_composablePairs I J C
  have := isManifold_targetFiber I J C g.left
  have := isManifold_targetFiber I J C g.right
  have hpair : ContMDiff
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (fun h : TargetFiber C g.left ↦ (⟨(h.1, g), h.2⟩ : ComposablePairs C)) :=
    (isSmoothEmbedding_coe_composablePairs I J C).contMDiff_iff_comp.mpr
      ((isSmoothEmbedding_coe_targetFiber I J C g.left).contMDiff.prodMk contMDiff_const)
  exact (isSmoothEmbedding_coe_targetFiber I J C g.right).contMDiff_iff_comp.mpr
    ((contMDiff_composablePairs_comp I J C).comp hpair)

/-- **Left translation along target fibres.** Post-composing categorically with `g` (geometric
left multiplication `h ↦ gh`) is a smooth diffeomorphism from `TargetFiber C g.left` onto
`TargetFiber C g.right`, with smooth inverse given by left translation by `inv g`. -/
def leftTranslateDiffeomorph (g : Quiver.Total C) :
    letI := targetFiberChartedSpace I J C g.left
    letI := targetFiberChartedSpace I J C g.right
    TargetFiber C g.left ≃ₘ^∞⟮𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)⟯ TargetFiber C g.right :=
  letI := targetFiberChartedSpace I J C g.left
  letI := targetFiberChartedSpace I J C g.right
  { toFun := fun h ↦ ⟨h.1.comp g h.2, h.1.comp_right g h.2⟩
    invFun := fun k ↦
      ⟨k.1.comp (inverseDiffeomorph I J C g) (k.2.trans (inverseDiffeomorph_left I J C g).symm),
        (k.1.comp_right (inverseDiffeomorph I J C g) _).trans (inverseDiffeomorph_right I J C g)⟩
    left_inv := fun h ↦
      Subtype.ext
        ((Quiver.Total.comp_congr rfl (inverseDiffeomorph_apply I J C g) _
          (h.1.comp_right g h.2)).trans
          (Quiver.Total.comp_inv_cancel_right h.1 g h.2 _))
    right_inv := fun k ↦
      Subtype.ext
        ((Quiver.Total.comp_congr
          (Quiver.Total.comp_congr rfl (inverseDiffeomorph_apply I J C g) _ k.2) rfl _
          (Quiver.Total.comp_right k.1 ⟨g.right, g.left, inv g.hom⟩ k.2)).trans
          (Quiver.Total.comp_inv_cancel_left k.1 g k.2 _))
    contMDiff_toFun := contMDiff_comp_right_targetFiber I J C g
    contMDiff_invFun := by
      let := composablePairsChartedSpace I J C
      have := isManifold_composablePairs I J C
      have := isManifold_targetFiber I J C g.left
      have := isManifold_targetFiber I J C g.right
      have hpair : ContMDiff
          𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
          𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
          (fun k : TargetFiber C g.right ↦
            (⟨(k.1, inverseDiffeomorph I J C g),
              k.2.trans (inverseDiffeomorph_left I J C g).symm⟩ : ComposablePairs C)) :=
        (isSmoothEmbedding_coe_composablePairs I J C).contMDiff_iff_comp.mpr
          ((isSmoothEmbedding_coe_targetFiber I J C g.right).contMDiff.prodMk contMDiff_const)
      exact (isSmoothEmbedding_coe_targetFiber I J C g.left).contMDiff_iff_comp.mpr
        ((contMDiff_composablePairs_comp I J C).comp hpair) }

@[simp]
theorem leftTranslateDiffeomorph_coe_apply (g : Quiver.Total C) (h : TargetFiber C g.left) :
    letI := targetFiberChartedSpace I J C g.left
    letI := targetFiberChartedSpace I J C g.right
    (leftTranslateDiffeomorph I J C g h : Quiver.Total C) = h.1.comp g h.2 :=
  (rfl)

@[simp]
theorem leftTranslateDiffeomorph_symm_coe_apply (g : Quiver.Total C) (k : TargetFiber C g.right) :
    letI := targetFiberChartedSpace I J C g.left
    letI := targetFiberChartedSpace I J C g.right
    ((leftTranslateDiffeomorph I J C g).symm k : Quiver.Total C) =
      k.1.comp (inverseDiffeomorph I J C g)
        (k.2.trans (inverseDiffeomorph_left I J C g).symm) :=
  (rfl)

/-- Left translation preserves source endpoints. -/
theorem leftTranslateDiffeomorph_left (g : Quiver.Total C) (h : TargetFiber C g.left) :
    letI := targetFiberChartedSpace I J C g.left
    letI := targetFiberChartedSpace I J C g.right
    (leftTranslateDiffeomorph I J C g h).1.left = h.1.left :=
  h.1.comp_left g h.2

@[simp]
theorem leftTranslateDiffeomorph_apply_unit (g : Quiver.Total C) :
    letI := targetFiberChartedSpace I J C g.left
    letI := targetFiberChartedSpace I J C g.right
    leftTranslateDiffeomorph I J C g ⟨⟨g.left, g.left, 𝟙 g.left⟩, rfl⟩ = ⟨g, rfl⟩ :=
  Subtype.ext (Quiver.Total.unit_comp g)

@[simp]
theorem leftTranslateDiffeomorph_unit (x : C) (h : TargetFiber C x) :
    letI := targetFiberChartedSpace I J C x
    leftTranslateDiffeomorph I J C ⟨x, x, 𝟙 x⟩ h = h := by
  obtain ⟨a, rfl⟩ := h
  exact Subtype.ext (Quiver.Total.comp_unit a)

end TauCeti.IsLieGroupoid
