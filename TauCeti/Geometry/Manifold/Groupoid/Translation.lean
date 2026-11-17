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

/-- Defining equality of `sourceFiberChartedSpace` as a regular-fibre charted space. -/
theorem sourceFiberChartedSpace_eq_regularFiberChartedSpace (x : C) :
    sourceFiberChartedSpace I J C x =
      regularFiberChartedSpace (by simp : (1 : ℕ∞ω) ≤ ∞) (contMDiff_source I J C)
        BoundarylessManifold.isInteriorPoint (isRegularValue_source I J C x) :=
  (rfl)

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

/-- The range of the differential of the source-fibre inclusion at `z` equals the vertical kernel
`ker (ds_{z.1})`. -/
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
  have := secondCountableTopology_arrows (I := I) (J := J) (C := C)
  exact Topology.IsEmbedding.subtypeVal.secondCountableTopology

/-- The regular-fibre smooth atlas of dimension `dim Γ - dim M` on the target fibre over `x`. -/
@[instance_reducible]
def targetFiberChartedSpace (x : C) :
    ChartedSpace (Fin (finrank ℝ E' - finrank ℝ E) → ℝ) (TargetFiber C x) :=
  regularFiberChartedSpace (by simp : (1 : ℕ∞ω) ≤ ∞) (contMDiff_target I J C)
    BoundarylessManifold.isInteriorPoint (isRegularValue_target I J C x)

/-- Defining equality of `targetFiberChartedSpace` as a regular-fibre charted space. -/
theorem targetFiberChartedSpace_eq_regularFiberChartedSpace (x : C) :
    targetFiberChartedSpace I J C x =
      regularFiberChartedSpace (by simp : (1 : ℕ∞ω) ≤ ∞) (contMDiff_target I J C)
        BoundarylessManifold.isInteriorPoint (isRegularValue_target I J C x) :=
  (rfl)

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

/-- The range of the differential of the target-fibre inclusion at `z` equals `ker (dt_{z.1})`. -/
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
  have := secondCountableTopology_arrows (I := I) (J := J) (C := C)
  exact Topology.IsEmbedding.subtypeVal.secondCountableTopology

/-! ### Inversion between source and target fibres -/

/-- Inversion restricts to a smooth diffeomorphism between the source fibre and the target fibre
over the same object `x`. -/
def inverseSourceTargetDiffeomorph (x : C) :
    letI := sourceFiberChartedSpace I J C x; letI := targetFiberChartedSpace I J C x
    SourceFiber C x ≃ₘ^∞⟮𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)⟯ TargetFiber C x :=
  letI := sourceFiberChartedSpace I J C x; letI := targetFiberChartedSpace I J C x
  { toFun := fun a ↦ ⟨inverseDiffeomorph I J C a.1, (inverseDiffeomorph_right I J C a.1).trans a.2⟩
    invFun := fun a ↦ ⟨inverseDiffeomorph I J C a.1, (inverseDiffeomorph_left I J C a.1).trans a.2⟩
    left_inv := fun a ↦ Subtype.ext (by obtain ⟨⟨_, _, _⟩, _⟩ := a; simp)
    right_inv := fun a ↦ Subtype.ext (by obtain ⟨⟨_, _, _⟩, _⟩ := a; simp)
    contMDiff_toFun :=
      (isSmoothEmbedding_coe_targetFiber I J C x).contMDiff_iff_comp.mpr
        ((inverseDiffeomorph I J C).contMDiff.comp
          (isSmoothEmbedding_coe_sourceFiber I J C x).contMDiff)
    contMDiff_invFun :=
      (isSmoothEmbedding_coe_sourceFiber I J C x).contMDiff_iff_comp.mpr
        ((inverseDiffeomorph I J C).contMDiff.comp
          (isSmoothEmbedding_coe_targetFiber I J C x).contMDiff) }

@[simp]
theorem inverseSourceTargetDiffeomorph_coe_apply (x : C) (a : SourceFiber C x) :
    letI := sourceFiberChartedSpace I J C x; letI := targetFiberChartedSpace I J C x
    (inverseSourceTargetDiffeomorph I J C x a : Quiver.Total C) =
      inverseDiffeomorph I J C a.1 := (rfl)

@[simp]
theorem inverseSourceTargetDiffeomorph_symm_coe_apply (x : C) (a : TargetFiber C x) :
    letI := sourceFiberChartedSpace I J C x; letI := targetFiberChartedSpace I J C x
    ((inverseSourceTargetDiffeomorph I J C x).symm a : Quiver.Total C) =
      inverseDiffeomorph I J C a.1 := (rfl)

/-! ### Smooth right and left translations along fibres -/

private theorem contMDiff_comp_left_sourceFiber_of_eq (g : Quiver.Total C) {x y : C}
    (hx : g.right = x) (hy : g.left = y) :
    letI := sourceFiberChartedSpace I J C x; letI := sourceFiberChartedSpace I J C y
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (fun h : SourceFiber C x ↦
        (⟨g.comp h.1 (hx.trans h.2.symm), (g.comp_left h.1 _).trans hy⟩ : SourceFiber C y)) := by
  subst hx hy
  let := composablePairsChartedSpace I J C
  let := sourceFiberChartedSpace I J C g.right; let := sourceFiberChartedSpace I J C g.left
  have hpair : ContMDiff 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (fun h : SourceFiber C g.right ↦ (⟨(g, h.1), h.2.symm⟩ : ComposablePairs C)) :=
    (isSmoothEmbedding_coe_composablePairs I J C).contMDiff_iff_comp.mpr
      (contMDiff_const.prodMk (isSmoothEmbedding_coe_sourceFiber I J C g.right).contMDiff)
  exact (isSmoothEmbedding_coe_sourceFiber I J C g.left).contMDiff_iff_comp.mpr
    ((contMDiff_composablePairs_comp I J C).comp hpair)

/-- Categorical left-composition by a fixed arrow `g` is smooth from `SourceFiber C g.right` to
`SourceFiber C g.left`. -/
theorem contMDiff_comp_left_sourceFiber (g : Quiver.Total C) :
    letI := sourceFiberChartedSpace I J C g.right; letI := sourceFiberChartedSpace I J C g.left
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (fun h : SourceFiber C g.right ↦
        (⟨g.comp h.1 h.2.symm, g.comp_left h.1 h.2.symm⟩ : SourceFiber C g.left)) :=
  contMDiff_comp_left_sourceFiber_of_eq I J C g rfl rfl

/-- **Right translation along source fibres.** Pre-composing categorically with `g` (geometric
right multiplication `h ↦ hg`) is a smooth diffeomorphism from `SourceFiber C g.right` onto
`SourceFiber C g.left`, with smooth inverse given by right translation by `inv g`. -/
def rightTranslateDiffeomorph (g : Quiver.Total C) :
    letI := sourceFiberChartedSpace I J C g.right; letI := sourceFiberChartedSpace I J C g.left
    SourceFiber C g.right ≃ₘ^∞⟮𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)⟯ SourceFiber C g.left :=
  letI := sourceFiberChartedSpace I J C g.right; letI := sourceFiberChartedSpace I J C g.left
  { toFun := fun h ↦ ⟨g.comp h.1 h.2.symm, g.comp_left h.1 h.2.symm⟩
    invFun := fun k ↦
      ⟨(inverseDiffeomorph I J C g).comp k.1 ((inverseDiffeomorph_right I J C g).trans k.2.symm),
        ((inverseDiffeomorph I J C g).comp_left k.1 _).trans (inverseDiffeomorph_left I J C g)⟩
    left_inv := fun h ↦ Subtype.ext
      ((Quiver.Total.comp_congr (inverseDiffeomorph_apply I J C g) rfl _
        (g.comp_left h.1 h.2.symm).symm).trans (Quiver.Total.inv_comp_comp g h.1 h.2.symm _))
    right_inv := fun k ↦ Subtype.ext
      ((Quiver.Total.comp_congr rfl
        (Quiver.Total.comp_congr (inverseDiffeomorph_apply I J C g) rfl _ k.2.symm) _
        (Quiver.Total.comp_left ⟨g.right, g.left, inv g.hom⟩ k.1 k.2.symm).symm).trans
        (Quiver.Total.comp_inv_comp g k.1 k.2.symm _))
    contMDiff_toFun := contMDiff_comp_left_sourceFiber I J C g
    contMDiff_invFun := contMDiff_comp_left_sourceFiber_of_eq I J C (inverseDiffeomorph I J C g)
      (inverseDiffeomorph_right I J C g) (inverseDiffeomorph_left I J C g) }

@[simp]
theorem rightTranslateDiffeomorph_coe_apply (g : Quiver.Total C) (h : SourceFiber C g.right) :
    letI := sourceFiberChartedSpace I J C g.right; letI := sourceFiberChartedSpace I J C g.left
    (rightTranslateDiffeomorph I J C g h : Quiver.Total C) = g.comp h.1 h.2.symm := (rfl)

@[simp]
theorem rightTranslateDiffeomorph_symm_coe_apply (g : Quiver.Total C) (k : SourceFiber C g.left) :
    letI := sourceFiberChartedSpace I J C g.right; letI := sourceFiberChartedSpace I J C g.left
    ((rightTranslateDiffeomorph I J C g).symm k : Quiver.Total C) =
      (inverseDiffeomorph I J C g).comp k.1
        ((inverseDiffeomorph_right I J C g).trans k.2.symm) := (rfl)

/-- Right translation preserves target endpoints. -/
theorem rightTranslateDiffeomorph_right (g : Quiver.Total C) (h : SourceFiber C g.right) :
    letI := sourceFiberChartedSpace I J C g.right; letI := sourceFiberChartedSpace I J C g.left
    (rightTranslateDiffeomorph I J C g h).1.right = h.1.right :=
  g.comp_right h.1 h.2.symm

@[simp]
theorem rightTranslateDiffeomorph_apply_unit (g : Quiver.Total C) :
    letI := sourceFiberChartedSpace I J C g.right; letI := sourceFiberChartedSpace I J C g.left
    rightTranslateDiffeomorph I J C g ⟨⟨g.right, g.right, 𝟙 g.right⟩, rfl⟩ = ⟨g, rfl⟩ :=
  Subtype.ext (Quiver.Total.comp_unit g rfl)

@[simp]
theorem rightTranslateDiffeomorph_unit (x : C) (h : SourceFiber C x) :
    letI := sourceFiberChartedSpace I J C x
    rightTranslateDiffeomorph I J C ⟨x, x, 𝟙 x⟩ h = h := by
  obtain ⟨a, rfl⟩ := h; exact Subtype.ext (Quiver.Total.unit_comp a rfl)

/-- The inverse of right translation by `g` is right translation by `inv g`. -/
theorem rightTranslateDiffeomorph_symm (g : Quiver.Total C) :
    letI := sourceFiberChartedSpace I J C g.right; letI := sourceFiberChartedSpace I J C g.left
    (rightTranslateDiffeomorph I J C g).symm =
      rightTranslateDiffeomorph I J C ⟨g.right, g.left, inv g.hom⟩ := by
  let := sourceFiberChartedSpace I J C g.right; let := sourceFiberChartedSpace I J C g.left
  exact Diffeomorph.ext fun k ↦ Subtype.ext
    (Quiver.Total.comp_congr (inverseDiffeomorph_apply I J C g) rfl _ k.2.symm)

/-- Functoriality of right translation as diffeomorphisms: right translating by `g : y ⟶ z` and
then by `f : x ⟶ y` equals right translating by `f ≫ g : x ⟶ z`. -/
theorem rightTranslateDiffeomorph_trans {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    letI := sourceFiberChartedSpace I J C z; letI := sourceFiberChartedSpace I J C y
    letI := sourceFiberChartedSpace I J C x
    (rightTranslateDiffeomorph I J C ⟨y, z, g⟩).trans
      (rightTranslateDiffeomorph I J C ⟨x, y, f⟩) =
      rightTranslateDiffeomorph I J C ⟨x, z, f ≫ g⟩ := by
  let := sourceFiberChartedSpace I J C z; let := sourceFiberChartedSpace I J C y
  let := sourceFiberChartedSpace I J C x
  refine Diffeomorph.ext fun h ↦ Subtype.ext ?_
  have hbc' : ((⟨x, y, f⟩ : Quiver.Total C).comp ⟨y, z, g⟩ rfl).right = h.1.left :=
    ((⟨x, y, f⟩ : Quiver.Total C).comp_right ⟨y, z, g⟩ rfl).trans h.2.symm
  exact (Quiver.Total.comp_assoc ⟨x, y, f⟩ ⟨y, z, g⟩ h.1 rfl h.2.symm hbc' _).symm.trans
    (Quiver.Total.comp_congr (Quiver.Total.mk_comp_mk f g) rfl hbc' h.2.symm)

/-- Pointwise functoriality of right translation along arbitrary composable total arrows, on
underlying total arrows. -/
theorem rightTranslateDiffeomorph_comp_coe_apply {g₁ g₂ : Quiver.Total C} (hg : g₁.right = g₂.left)
    (k : SourceFiber C g₂.right) :
    letI := sourceFiberChartedSpace I J C g₂.right; letI := sourceFiberChartedSpace I J C g₁.right
    letI := sourceFiberChartedSpace I J C g₁.left
    letI := sourceFiberChartedSpace I J C (g₁.comp g₂ hg).right
    letI := sourceFiberChartedSpace I J C (g₁.comp g₂ hg).left
    (rightTranslateDiffeomorph I J C g₁
      ⟨(rightTranslateDiffeomorph I J C g₂ k).1,
        (rightTranslateDiffeomorph I J C g₂ k).2.trans hg.symm⟩ : Quiver.Total C) =
      rightTranslateDiffeomorph I J C (g₁.comp g₂ hg)
        ⟨k.1, k.2.trans (g₁.comp_right g₂ hg).symm⟩ :=
  (Quiver.Total.comp_assoc g₁ g₂ k.1 hg k.2.symm _ _).symm

private theorem contMDiff_comp_right_targetFiber_of_eq (g : Quiver.Total C) {x y : C}
    (hx : g.left = x) (hy : g.right = y) :
    letI := targetFiberChartedSpace I J C x; letI := targetFiberChartedSpace I J C y
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (fun h : TargetFiber C x ↦
        (⟨h.1.comp g (h.2.trans hx.symm), (h.1.comp_right g _).trans hy⟩ : TargetFiber C y)) := by
  subst hx hy
  let := composablePairsChartedSpace I J C
  let := targetFiberChartedSpace I J C g.left; let := targetFiberChartedSpace I J C g.right
  have hpair : ContMDiff 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (fun h : TargetFiber C g.left ↦ (⟨(h.1, g), h.2⟩ : ComposablePairs C)) :=
    (isSmoothEmbedding_coe_composablePairs I J C).contMDiff_iff_comp.mpr
      ((isSmoothEmbedding_coe_targetFiber I J C g.left).contMDiff.prodMk contMDiff_const)
  exact (isSmoothEmbedding_coe_targetFiber I J C g.right).contMDiff_iff_comp.mpr
    ((contMDiff_composablePairs_comp I J C).comp hpair)

/-- Categorical right-composition by a fixed arrow `g` is smooth from `TargetFiber C g.left` to
`TargetFiber C g.right`. -/
theorem contMDiff_comp_right_targetFiber (g : Quiver.Total C) :
    letI := targetFiberChartedSpace I J C g.left; letI := targetFiberChartedSpace I J C g.right
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (fun h : TargetFiber C g.left ↦
        (⟨h.1.comp g h.2, h.1.comp_right g h.2⟩ : TargetFiber C g.right)) :=
  contMDiff_comp_right_targetFiber_of_eq I J C g rfl rfl

/-- **Left translation along target fibres.** Post-composing categorically with `g` (geometric
left multiplication `h ↦ gh`) is a smooth diffeomorphism from `TargetFiber C g.left` onto
`TargetFiber C g.right`, with smooth inverse given by left translation by `inv g`. -/
def leftTranslateDiffeomorph (g : Quiver.Total C) :
    letI := targetFiberChartedSpace I J C g.left; letI := targetFiberChartedSpace I J C g.right
    TargetFiber C g.left ≃ₘ^∞⟮𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)⟯ TargetFiber C g.right :=
  letI := targetFiberChartedSpace I J C g.left; letI := targetFiberChartedSpace I J C g.right
  { toFun := fun h ↦ ⟨h.1.comp g h.2, h.1.comp_right g h.2⟩
    invFun := fun k ↦
      ⟨k.1.comp (inverseDiffeomorph I J C g) (k.2.trans (inverseDiffeomorph_left I J C g).symm),
        (k.1.comp_right (inverseDiffeomorph I J C g) _).trans (inverseDiffeomorph_right I J C g)⟩
    left_inv := fun h ↦ Subtype.ext
      ((Quiver.Total.comp_congr rfl (inverseDiffeomorph_apply I J C g) _
        (h.1.comp_right g h.2)).trans (Quiver.Total.comp_inv_cancel_right h.1 g h.2 _))
    right_inv := fun k ↦ Subtype.ext
      ((Quiver.Total.comp_congr
        (Quiver.Total.comp_congr rfl (inverseDiffeomorph_apply I J C g) _ k.2) rfl _
        (Quiver.Total.comp_right k.1 ⟨g.right, g.left, inv g.hom⟩ k.2)).trans
        (Quiver.Total.inv_comp_cancel_right k.1 g k.2 _))
    contMDiff_toFun := contMDiff_comp_right_targetFiber I J C g
    contMDiff_invFun := contMDiff_comp_right_targetFiber_of_eq I J C (inverseDiffeomorph I J C g)
      (inverseDiffeomorph_left I J C g) (inverseDiffeomorph_right I J C g) }

@[simp]
theorem leftTranslateDiffeomorph_coe_apply (g : Quiver.Total C) (h : TargetFiber C g.left) :
    letI := targetFiberChartedSpace I J C g.left; letI := targetFiberChartedSpace I J C g.right
    (leftTranslateDiffeomorph I J C g h : Quiver.Total C) = h.1.comp g h.2 := (rfl)

@[simp]
theorem leftTranslateDiffeomorph_symm_coe_apply (g : Quiver.Total C) (k : TargetFiber C g.right) :
    letI := targetFiberChartedSpace I J C g.left; letI := targetFiberChartedSpace I J C g.right
    ((leftTranslateDiffeomorph I J C g).symm k : Quiver.Total C) =
      k.1.comp (inverseDiffeomorph I J C g)
        (k.2.trans (inverseDiffeomorph_left I J C g).symm) := (rfl)

/-- Left translation preserves source endpoints. -/
theorem leftTranslateDiffeomorph_left (g : Quiver.Total C) (h : TargetFiber C g.left) :
    letI := targetFiberChartedSpace I J C g.left; letI := targetFiberChartedSpace I J C g.right
    (leftTranslateDiffeomorph I J C g h).1.left = h.1.left :=
  h.1.comp_left g h.2

@[simp]
theorem leftTranslateDiffeomorph_apply_unit (g : Quiver.Total C) :
    letI := targetFiberChartedSpace I J C g.left; letI := targetFiberChartedSpace I J C g.right
    leftTranslateDiffeomorph I J C g ⟨⟨g.left, g.left, 𝟙 g.left⟩, rfl⟩ = ⟨g, rfl⟩ :=
  Subtype.ext (Quiver.Total.unit_comp g rfl)

@[simp]
theorem leftTranslateDiffeomorph_unit (x : C) (h : TargetFiber C x) :
    letI := targetFiberChartedSpace I J C x
    leftTranslateDiffeomorph I J C ⟨x, x, 𝟙 x⟩ h = h := by
  obtain ⟨a, rfl⟩ := h; exact Subtype.ext (Quiver.Total.comp_unit a rfl)

/-- The inverse of left translation by `g` is left translation by `inv g`. -/
theorem leftTranslateDiffeomorph_symm (g : Quiver.Total C) :
    letI := targetFiberChartedSpace I J C g.left; letI := targetFiberChartedSpace I J C g.right
    (leftTranslateDiffeomorph I J C g).symm =
      leftTranslateDiffeomorph I J C ⟨g.right, g.left, inv g.hom⟩ := by
  let := targetFiberChartedSpace I J C g.left; let := targetFiberChartedSpace I J C g.right
  exact Diffeomorph.ext fun k ↦ Subtype.ext
    (Quiver.Total.comp_congr rfl (inverseDiffeomorph_apply I J C g) _ k.2)

/-- Functoriality of left translation as diffeomorphisms: left translating by `f : x ⟶ y` and then
by `g : y ⟶ z` equals left translating by `f ≫ g : x ⟶ z`. -/
theorem leftTranslateDiffeomorph_trans {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    letI := targetFiberChartedSpace I J C x; letI := targetFiberChartedSpace I J C y
    letI := targetFiberChartedSpace I J C z
    (leftTranslateDiffeomorph I J C ⟨x, y, f⟩).trans
      (leftTranslateDiffeomorph I J C ⟨y, z, g⟩) =
      leftTranslateDiffeomorph I J C ⟨x, z, f ≫ g⟩ := by
  let := targetFiberChartedSpace I J C x; let := targetFiberChartedSpace I J C y
  let := targetFiberChartedSpace I J C z
  refine Diffeomorph.ext fun h ↦ Subtype.ext ?_
  have hab' : h.1.right = ((⟨x, y, f⟩ : Quiver.Total C).comp ⟨y, z, g⟩ rfl).left :=
    h.2.trans ((⟨x, y, f⟩ : Quiver.Total C).comp_left ⟨y, z, g⟩ rfl).symm
  exact (Quiver.Total.comp_assoc h.1 ⟨x, y, f⟩ ⟨y, z, g⟩ h.2 rfl _ hab').trans
    (Quiver.Total.comp_congr rfl (Quiver.Total.mk_comp_mk f g) hab' h.2)

/-- Pointwise functoriality of left translation along arbitrary composable total arrows, on
underlying total arrows. -/
theorem leftTranslateDiffeomorph_comp_coe_apply {g₁ g₂ : Quiver.Total C} (hg : g₁.right = g₂.left)
    (h : TargetFiber C g₁.left) :
    letI := targetFiberChartedSpace I J C g₁.left; letI := targetFiberChartedSpace I J C g₂.left
    letI := targetFiberChartedSpace I J C g₂.right
    letI := targetFiberChartedSpace I J C (g₁.comp g₂ hg).left
    letI := targetFiberChartedSpace I J C (g₁.comp g₂ hg).right
    (leftTranslateDiffeomorph I J C g₂
      ⟨(leftTranslateDiffeomorph I J C g₁ h).1,
        (leftTranslateDiffeomorph I J C g₁ h).2.trans hg⟩ : Quiver.Total C) =
      leftTranslateDiffeomorph I J C (g₁.comp g₂ hg)
        ⟨h.1, h.2.trans (g₁.comp_left g₂ hg).symm⟩ :=
  Quiver.Total.comp_assoc h.1 g₁ g₂ h.2 hg _ _

/-- Intertwining of right and left fibre translations under `inverseSourceTargetDiffeomorph`:
right translating by `g` and inverting agrees with inverting and left translating by `inv g`. -/
theorem rightTranslateDiffeomorph_trans_inverseSourceTargetDiffeomorph (g : Quiver.Total C) :
    letI := sourceFiberChartedSpace I J C g.right; letI := sourceFiberChartedSpace I J C g.left
    letI := targetFiberChartedSpace I J C g.right; letI := targetFiberChartedSpace I J C g.left
    (rightTranslateDiffeomorph I J C g).trans (inverseSourceTargetDiffeomorph I J C g.left) =
      (inverseSourceTargetDiffeomorph I J C g.right).trans
        (leftTranslateDiffeomorph I J C ⟨g.right, g.left, inv g.hom⟩) := by
  let := sourceFiberChartedSpace I J C g.right; let := sourceFiberChartedSpace I J C g.left
  let := targetFiberChartedSpace I J C g.right; let := targetFiberChartedSpace I J C g.left
  exact Diffeomorph.ext fun h ↦ Subtype.ext
    ((inverseDiffeomorph_apply I J C (g.comp h.1 h.2.symm)).trans
      ((Quiver.Total.inv_comp_rev g h.1 h.2.symm).trans
        (Quiver.Total.comp_congr (inverseDiffeomorph_apply I J C h.1).symm rfl h.2 _)))

/-- Conjugating `rightTranslateDiffeomorph I J C g` by `inverseSourceTargetDiffeomorph` yields left
translation by `inv g`. -/
theorem inverseSourceTargetDiffeomorph_conj_rightTranslateDiffeomorph (g : Quiver.Total C) :
    letI := sourceFiberChartedSpace I J C g.right; letI := sourceFiberChartedSpace I J C g.left
    letI := targetFiberChartedSpace I J C g.right; letI := targetFiberChartedSpace I J C g.left
    ((inverseSourceTargetDiffeomorph I J C g.right).symm.trans
      (rightTranslateDiffeomorph I J C g)).trans (inverseSourceTargetDiffeomorph I J C g.left) =
      leftTranslateDiffeomorph I J C ⟨g.right, g.left, inv g.hom⟩ := by
  let := sourceFiberChartedSpace I J C g.right; let := sourceFiberChartedSpace I J C g.left
  let := targetFiberChartedSpace I J C g.right; let := targetFiberChartedSpace I J C g.left
  refine Diffeomorph.ext fun k ↦ ?_
  have h := congrArg (· ((inverseSourceTargetDiffeomorph I J C g.right).symm k))
    (rightTranslateDiffeomorph_trans_inverseSourceTargetDiffeomorph I J C g)
  simpa only [Diffeomorph.coe_trans, Function.comp_apply, Diffeomorph.apply_symm_apply] using h

/-- Conjugating `leftTranslateDiffeomorph I J C g` by `inverseSourceTargetDiffeomorph` yields right
translation by `inv g`. -/
theorem inverseSourceTargetDiffeomorph_conj_leftTranslateDiffeomorph (g : Quiver.Total C) :
    letI := sourceFiberChartedSpace I J C g.left; letI := sourceFiberChartedSpace I J C g.right
    letI := targetFiberChartedSpace I J C g.left; letI := targetFiberChartedSpace I J C g.right
    ((inverseSourceTargetDiffeomorph I J C g.left).trans
      (leftTranslateDiffeomorph I J C g)).trans
      (inverseSourceTargetDiffeomorph I J C g.right).symm =
      rightTranslateDiffeomorph I J C ⟨g.right, g.left, inv g.hom⟩ := by
  let := sourceFiberChartedSpace I J C g.left; let := sourceFiberChartedSpace I J C g.right
  let := targetFiberChartedSpace I J C g.left; let := targetFiberChartedSpace I J C g.right
  refine Diffeomorph.ext fun h ↦ ?_
  obtain ⟨x, y, f⟩ := g
  have hinv := rightTranslateDiffeomorph_trans_inverseSourceTargetDiffeomorph I J C ⟨y, x, inv f⟩
  dsimp only at hinv
  rw [IsIso.inv_inv] at hinv
  have h' := congrArg (fun e ↦ (inverseSourceTargetDiffeomorph I J C y).symm (e h)) hinv
  simpa only [Diffeomorph.coe_trans, Function.comp_apply, Diffeomorph.symm_apply_apply] using
    h'.symm

end TauCeti.IsLieGroupoid
