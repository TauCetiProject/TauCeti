/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Associativity
public import TauCeti.Geometry.Manifold.Groupoid.Basic
public import TauCeti.Geometry.Manifold.RegularValue.ManifoldLevel
import TauCeti.Geometry.Manifold.FiberProduct.Submersion
import TauCeti.Geometry.Manifold.SmoothEmbedding.LeftInverse
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph

/-!
# Source and target fibres, smooth translations, and composable arrows

For a Lie groupoid `C` with object model `I` and arrow model `J`, source and target are smooth
submersions, so every source fibre `s⁻¹(x)` and target fibre `t⁻¹(y)` carries the canonical
regular-fibre smooth manifold structure of dimension `dim (Quiver.Total C) - dim C`, embedded
smoothly in `Quiver.Total C` with tangent space `ker ds` or `ker dt`.

Inversion restricts to a diffeomorphism between `s⁻¹(x)` and `t⁻¹(x)`
(`TauCeti.IsLieGroupoid.inverseFiberDiffeomorph`), transporting the Hausdorffness of source fibres
to target fibres (`TauCeti.IsLieGroupoid.t2Space_targetFiber`). Left translation by an arrow `g`
gives a diffeomorphism `t⁻¹(s(g)) ≃ₘ t⁻¹(t(g))` sending `h ↦ gh = h ≫ g`
(`TauCeti.IsLieGroupoid.leftTranslateDiffeomorph`), and right translation by `g` gives a
diffeomorphism `s⁻¹(t(g)) ≃ₘ s⁻¹(s(g))` sending `h ↦ hg = g ≫ h`
(`TauCeti.IsLieGroupoid.rightTranslateDiffeomorph`).

On composable pairs `Γ^{(2)} = {(g, h) // s(g) = t(h)}`, all three simplicial face maps — the two
projections `(g, h) ↦ g`, `(g, h) ↦ h` and groupoid multiplication `(g, h) ↦ gh` — are smooth
submersions (`TauCeti.IsLieGroupoid.isSubmersion_fst_composablePairs`,
`TauCeti.IsLieGroupoid.isSubmersion_snd_composablePairs`,
`TauCeti.IsLieGroupoid.isSubmersion_mul`), the last deduced from the groupoid shearing
diffeomorphism `(g, h) ↦ (gh, g)` onto pairs sharing a target
(`TauCeti.IsLieGroupoid.shearDiffeomorph`). Both unit-insertion maps `g ↦ (g, 1_{s(g)})` and
`h ↦ (1_{t(h)}, h)` are smooth embeddings into `Γ^{(2)}`. Finally, the left- and right-associated
spaces of composable triples carry transverse fibre-product manifold structures linked by the
canonical smooth associator (`TauCeti.IsLieGroupoid.composableTriplesAssocDiffeomorph`), along
which the two ternary multiplication maps agree.

## Main definitions

* `TauCeti.IsLieGroupoid.sourceFiberChartedSpace`,
  `TauCeti.IsLieGroupoid.targetFiberChartedSpace`: regular-fibre smooth atlases on `s⁻¹(x)` and
  `t⁻¹(y)`.
* `TauCeti.IsLieGroupoid.inverseFiberDiffeomorph`: inversion `s⁻¹(x) ≃ₘ t⁻¹(x)`.
* `TauCeti.IsLieGroupoid.leftTranslateDiffeomorph`,
  `TauCeti.IsLieGroupoid.rightTranslateDiffeomorph`: left translation on target fibres and right
  translation on source fibres.
* `TauCeti.IsLieGroupoid.shearDiffeomorph`: the division diffeomorphism `(g, h) ↦ (gh, g)` from
  composable pairs onto pairs with matching targets.
* `TauCeti.IsLieGroupoid.composableTriplesLeftChartedSpace`,
  `TauCeti.IsLieGroupoid.composableTriplesRightChartedSpace`,
  `TauCeti.IsLieGroupoid.composableTriplesAssocDiffeomorph`: smooth atlases and associator on
  composable triples.

## Main results

* `TauCeti.IsLieGroupoid.t2Space_targetFiber`: every target fibre of a Lie groupoid is Hausdorff.
* `TauCeti.IsLieGroupoid.isSubmersion_fst_composablePairs`,
  `TauCeti.IsLieGroupoid.isSubmersion_snd_composablePairs`,
  `TauCeti.IsLieGroupoid.isSubmersion_mul`: all three face maps `Γ^{(2)} → Γ` are submersions.
* `TauCeti.IsLieGroupoid.isSmoothEmbedding_insertUnitRight`,
  `TauCeti.IsLieGroupoid.isSmoothEmbedding_insertUnitLeft`: the degeneracy sections `Γ → Γ^{(2)}`
  are smooth embeddings.
* `TauCeti.IsLieGroupoid.mulComposableTriplesLeft_eq`: associativity of smooth ternary
  multiplication along `composableTriplesAssocDiffeomorph`.

## References

* I. Moerdijk and J. Mrčun, *Introduction to Foliations and Lie Groupoids*, Cambridge Studies in
  Advanced Mathematics 91, Cambridge University Press (2003), Section 5.1.
* K. C. H. Mackenzie, *General Theory of Lie Groupoids and Lie Algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), Section 1.1.
-/

public section

open CategoryTheory Function Module Set Topology
open scoped Manifold ContDiff

namespace TauCeti.IsLieGroupoid

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H') [J.Boundaryless]
  (C : Type*) [Category C] [IsGroupoid C]
  [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
  [IsManifold J ∞ (Quiver.Total C)] [IsLieGroupoid I J C]

section Fibers

/-- The regular-fibre smooth atlas on the source fibre `s⁻¹(x)` of a Lie groupoid, of dimension
`dim (Quiver.Total C) - dim C`. It uses the subspace topology and is not a global instance. -/
@[instance_reducible]
noncomputable def sourceFiberChartedSpace (x : C) :
    ChartedSpace (Fin (finrank ℝ E' - finrank ℝ E) → ℝ) {a : Quiver.Total C // a.left = x} :=
  regularFiberChartedSpace (by simp : (1 : ℕ∞ω) ≤ ∞) (contMDiff_source I J C)
    BoundarylessManifold.isInteriorPoint
    ((isSubmersion_source (I := I) (J := J) (C := C)).isRegularValue (by simp) x)

/-- Every source fibre of a Lie groupoid is a smooth manifold in its regular-fibre atlas. -/
theorem isManifold_sourceFiber (x : C) :
    letI := sourceFiberChartedSpace I J C x
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ∞ {a : Quiver.Total C // a.left = x} :=
  isManifold_regularFiber (by simp : (1 : ℕ∞ω) ≤ ∞) (contMDiff_source I J C)
    BoundarylessManifold.isInteriorPoint
    ((isSubmersion_source (I := I) (J := J) (C := C)).isRegularValue (by simp) x)

/-- Inclusion of a source fibre into the total arrow manifold is a smooth embedding. -/
theorem isSmoothEmbedding_coe_sourceFiber (x : C) :
    letI := sourceFiberChartedSpace I J C x
    Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (Subtype.val : {a : Quiver.Total C // a.left = x} → Quiver.Total C) :=
  isSmoothEmbedding_coe_regularFiber (by simp : (1 : ℕ∞ω) ≤ ∞) (contMDiff_source I J C)
    BoundarylessManifold.isInteriorPoint
    ((isSubmersion_source (I := I) (J := J) (C := C)).isRegularValue (by simp) x)

/-- The tangent image of the source-fibre inclusion is the kernel of the differential of source. -/
theorem range_mfderiv_coe_sourceFiber (x : C) :
    letI := sourceFiberChartedSpace I J C x
    ∀ a : {a : Quiver.Total C // a.left = x},
      (mfderiv 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) J Subtype.val a).range =
        (mfderiv J I Quiver.Total.left a.1).ker :=
  range_mfderiv_coe_regularFiber (by simp : (1 : ℕ∞ω) ≤ ∞) (contMDiff_source I J C)
    BoundarylessManifold.isInteriorPoint
    ((isSubmersion_source (I := I) (J := J) (C := C)).isRegularValue (by simp) x)

/-- The regular-fibre smooth atlas on the target fibre `t⁻¹(y)` of a Lie groupoid, of dimension
`dim (Quiver.Total C) - dim C`. It uses the subspace topology and is not a global instance. -/
@[instance_reducible]
noncomputable def targetFiberChartedSpace (y : C) :
    ChartedSpace (Fin (finrank ℝ E' - finrank ℝ E) → ℝ) {a : Quiver.Total C // a.right = y} :=
  regularFiberChartedSpace (by simp : (1 : ℕ∞ω) ≤ ∞) (contMDiff_target I J C)
    BoundarylessManifold.isInteriorPoint
    ((isSubmersion_target (I := I) (J := J) (C := C)).isRegularValue (by simp) y)

/-- Every target fibre of a Lie groupoid is a smooth manifold in its regular-fibre atlas. -/
theorem isManifold_targetFiber (y : C) :
    letI := targetFiberChartedSpace I J C y
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ∞ {a : Quiver.Total C // a.right = y} :=
  isManifold_regularFiber (by simp : (1 : ℕ∞ω) ≤ ∞) (contMDiff_target I J C)
    BoundarylessManifold.isInteriorPoint
    ((isSubmersion_target (I := I) (J := J) (C := C)).isRegularValue (by simp) y)

/-- Inclusion of a target fibre into the total arrow manifold is a smooth embedding. -/
theorem isSmoothEmbedding_coe_targetFiber (y : C) :
    letI := targetFiberChartedSpace I J C y
    Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (Subtype.val : {a : Quiver.Total C // a.right = y} → Quiver.Total C) :=
  isSmoothEmbedding_coe_regularFiber (by simp : (1 : ℕ∞ω) ≤ ∞) (contMDiff_target I J C)
    BoundarylessManifold.isInteriorPoint
    ((isSubmersion_target (I := I) (J := J) (C := C)).isRegularValue (by simp) y)

/-- The tangent image of the target-fibre inclusion is the kernel of the differential of target. -/
theorem range_mfderiv_coe_targetFiber (y : C) :
    letI := targetFiberChartedSpace I J C y
    ∀ a : {a : Quiver.Total C // a.right = y},
      (mfderiv 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) J Subtype.val a).range =
        (mfderiv J I Quiver.Total.right a.1).ker :=
  range_mfderiv_coe_regularFiber (by simp : (1 : ℕ∞ω) ≤ ∞) (contMDiff_target I J C)
    BoundarylessManifold.isInteriorPoint
    ((isSubmersion_target (I := I) (J := J) (C := C)).isRegularValue (by simp) y)

/-- Arrow inversion restricts to a diffeomorphism between the source fibre `s⁻¹(x)` and the target
fibre `t⁻¹(x)`. -/
noncomputable def inverseFiberDiffeomorph (x : C) :
    letI := sourceFiberChartedSpace I J C x
    letI := targetFiberChartedSpace I J C x
    {a : Quiver.Total C // a.left = x} ≃ₘ^∞⟮𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)⟯ {a : Quiver.Total C // a.right = x} :=
  letI := sourceFiberChartedSpace I J C x
  letI := targetFiberChartedSpace I J C x
  { toFun := fun a ↦ ⟨⟨a.1.right, a.1.left, inv a.1.hom⟩, a.2⟩
    invFun := fun b ↦ ⟨⟨b.1.right, b.1.left, inv b.1.hom⟩, b.2⟩
    left_inv := fun a ↦ Subtype.ext <| by obtain ⟨⟨_, _, _⟩, _⟩ := a; simp
    right_inv := fun b ↦ Subtype.ext <| by obtain ⟨⟨_, _, _⟩, _⟩ := b; simp
    contMDiff_toFun := (isSmoothEmbedding_coe_targetFiber I J C x).contMDiff_iff_comp.mpr <|
      (contMDiff_inverse (I := I) (J := J) (C := C)).comp
        (isSmoothEmbedding_coe_sourceFiber I J C x).contMDiff
    contMDiff_invFun := (isSmoothEmbedding_coe_sourceFiber I J C x).contMDiff_iff_comp.mpr <|
      (contMDiff_inverse (I := I) (J := J) (C := C)).comp
        (isSmoothEmbedding_coe_targetFiber I J C x).contMDiff }

@[simp]
theorem coe_inverseFiberDiffeomorph (x : C) (a : {a : Quiver.Total C // a.left = x}) :
    letI := sourceFiberChartedSpace I J C x
    letI := targetFiberChartedSpace I J C x
    (inverseFiberDiffeomorph I J C x a : Quiver.Total C) = ⟨a.1.right, a.1.left, inv a.1.hom⟩ :=
  (rfl)

@[simp]
theorem coe_inverseFiberDiffeomorph_symm (x : C) (b : {a : Quiver.Total C // a.right = x}) :
    letI := sourceFiberChartedSpace I J C x
    letI := targetFiberChartedSpace I J C x
    ((inverseFiberDiffeomorph I J C x).symm b : Quiver.Total C) =
      ⟨b.1.right, b.1.left, inv b.1.hom⟩ := (rfl)

include I J in
/-- Every target fibre of a Lie groupoid is Hausdorff in its subspace topology, transported from
the corresponding source fibre along `inverseFiberDiffeomorph`. -/
theorem t2Space_targetFiber (y : C) : T2Space {a : Quiver.Total C // a.right = y} := by
  let _ := sourceFiberChartedSpace I J C y
  let _ := targetFiberChartedSpace I J C y
  have : T2Space {a : Quiver.Total C // a.left = y} := t2Space_sourceFiber (I := I) (J := J) y
  exact (inverseFiberDiffeomorph I J C y).symm.toHomeomorph.isEmbedding.t2Space

/-- **Left translation on target fibres.** For an arrow `g : Quiver.Total C`, left multiplication
`h ↦ gh = h ≫ g` is a smooth diffeomorphism `t⁻¹(s(g)) ≃ₘ t⁻¹(t(g))` with inverse `k ↦ g⁻¹ k`. -/
noncomputable def leftTranslateDiffeomorph (g : Quiver.Total C) :
    letI := targetFiberChartedSpace I J C g.left
    letI := targetFiberChartedSpace I J C g.right
    {h : Quiver.Total C // h.right = g.left} ≃ₘ^∞⟮𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)⟯ {k : Quiver.Total C // k.right = g.right} :=
  letI := targetFiberChartedSpace I J C g.left
  letI := targetFiberChartedSpace I J C g.right
  { toFun := fun h ↦ ⟨h.1.comp g h.2, Quiver.Total.comp_right h.1 g h.2⟩
    invFun := fun k ↦ ⟨k.1.comp ⟨g.right, g.left, inv g.hom⟩ k.2,
      Quiver.Total.comp_right _ _ _⟩
    left_inv := fun h ↦ Subtype.ext <|
      Quiver.Total.comp_inv_cancel_right h.1 g h.2 (Quiver.Total.comp_right h.1 g h.2)
    right_inv := fun k ↦ Subtype.ext <|
      Quiver.Total.inv_comp_cancel_right k.1 g k.2 (Quiver.Total.comp_right _ _ _)
    contMDiff_toFun := (isSmoothEmbedding_coe_targetFiber I J C g.right).contMDiff_iff_comp.mpr <|
      (isSmoothEmbedding_coe_targetFiber I J C g.left).contMDiff.quiverTotalComp (I := I)
        contMDiff_const fun h ↦ h.2
    contMDiff_invFun := (isSmoothEmbedding_coe_targetFiber I J C g.left).contMDiff_iff_comp.mpr <|
      (isSmoothEmbedding_coe_targetFiber I J C g.right).contMDiff.quiverTotalComp (I := I)
        contMDiff_const fun k ↦ k.2 }

@[simp]
theorem coe_leftTranslateDiffeomorph (g : Quiver.Total C)
    (h : {h : Quiver.Total C // h.right = g.left}) :
    letI := targetFiberChartedSpace I J C g.left
    letI := targetFiberChartedSpace I J C g.right
    (leftTranslateDiffeomorph I J C g h : Quiver.Total C) = h.1.comp g h.2 := (rfl)

@[simp]
theorem coe_leftTranslateDiffeomorph_symm (g : Quiver.Total C)
    (k : {k : Quiver.Total C // k.right = g.right}) :
    letI := targetFiberChartedSpace I J C g.left
    letI := targetFiberChartedSpace I J C g.right
    ((leftTranslateDiffeomorph I J C g).symm k : Quiver.Total C) =
      k.1.comp ⟨g.right, g.left, inv g.hom⟩ k.2 := (rfl)

/-- Left translation by an identity arrow `1_x` is the identity diffeomorphism of `t⁻¹(x)`. -/
@[simp]
theorem leftTranslateDiffeomorph_unit (x : C) :
    letI := targetFiberChartedSpace I J C x
    leftTranslateDiffeomorph I J C ⟨x, x, 𝟙 x⟩ =
      Diffeomorph.refl 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
        {h : Quiver.Total C // h.right = x} ∞ := by
  let _ := targetFiberChartedSpace I J C x
  ext h : 1
  exact Subtype.ext (Quiver.Total.comp_id h.1 h.2)

include I J in
/-- Left translation is covariant with respect to groupoid multiplication `gh = h ≫ g`:
translating by `h` and then by `g` agrees pointwise with translating by `gh`. -/
theorem coe_leftTranslateDiffeomorph_comp (g h : Quiver.Total C) (hgh : g.left = h.right)
    (a : {a : Quiver.Total C // a.right = h.left}) :
    letI := targetFiberChartedSpace I J C h.left
    letI := targetFiberChartedSpace I J C g.left
    letI := targetFiberChartedSpace I J C g.right
    (leftTranslateDiffeomorph I J C g
      ⟨(leftTranslateDiffeomorph I J C h a : Quiver.Total C),
        by simp [hgh]⟩ : Quiver.Total C) =
      (leftTranslateDiffeomorph I J C (h.comp g hgh.symm)
        ⟨a.1, a.2.trans (Quiver.Total.comp_left h g hgh.symm).symm⟩ : Quiver.Total C) := by
  let _ := targetFiberChartedSpace I J C h.left
  let _ := targetFiberChartedSpace I J C g.left
  let _ := targetFiberChartedSpace I J C g.right
  simp only [coe_leftTranslateDiffeomorph]
  exact Quiver.Total.comp_assoc a.1 h g a.2 hgh.symm _ _

/-- **Right translation on source fibres.** For an arrow `g : Quiver.Total C`, right multiplication
`h ↦ hg = g ≫ h` is a smooth diffeomorphism `s⁻¹(t(g)) ≃ₘ s⁻¹(s(g))` with inverse `k ↦ k g⁻¹`. -/
noncomputable def rightTranslateDiffeomorph (g : Quiver.Total C) :
    letI := sourceFiberChartedSpace I J C g.right
    letI := sourceFiberChartedSpace I J C g.left
    {h : Quiver.Total C // h.left = g.right} ≃ₘ^∞⟮𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)⟯ {k : Quiver.Total C // k.left = g.left} :=
  letI := sourceFiberChartedSpace I J C g.right
  letI := sourceFiberChartedSpace I J C g.left
  { toFun := fun h ↦ ⟨g.comp h.1 h.2.symm, Quiver.Total.comp_left g h.1 h.2.symm⟩
    invFun := fun k ↦ ⟨(⟨g.right, g.left, inv g.hom⟩ : Quiver.Total C).comp k.1 k.2.symm,
      Quiver.Total.comp_left _ _ _⟩
    left_inv := fun h ↦ Subtype.ext <|
      Quiver.Total.inv_comp_comp g h.1 h.2.symm (by simp)
    right_inv := fun k ↦ Subtype.ext <|
      Quiver.Total.comp_inv_comp g k.1 k.2.symm (by simp)
    contMDiff_toFun := (isSmoothEmbedding_coe_sourceFiber I J C g.left).contMDiff_iff_comp.mpr <|
      contMDiff_const.quiverTotalComp (I := I)
        (isSmoothEmbedding_coe_sourceFiber I J C g.right).contMDiff fun h ↦ h.2.symm
    contMDiff_invFun := (isSmoothEmbedding_coe_sourceFiber I J C g.right).contMDiff_iff_comp.mpr <|
      contMDiff_const.quiverTotalComp (I := I)
        (isSmoothEmbedding_coe_sourceFiber I J C g.left).contMDiff fun k ↦ k.2.symm }

@[simp]
theorem coe_rightTranslateDiffeomorph (g : Quiver.Total C)
    (h : {h : Quiver.Total C // h.left = g.right}) :
    letI := sourceFiberChartedSpace I J C g.right
    letI := sourceFiberChartedSpace I J C g.left
    (rightTranslateDiffeomorph I J C g h : Quiver.Total C) = g.comp h.1 h.2.symm := (rfl)

@[simp]
theorem coe_rightTranslateDiffeomorph_symm (g : Quiver.Total C)
    (k : {k : Quiver.Total C // k.left = g.left}) :
    letI := sourceFiberChartedSpace I J C g.right
    letI := sourceFiberChartedSpace I J C g.left
    ((rightTranslateDiffeomorph I J C g).symm k : Quiver.Total C) =
      (⟨g.right, g.left, inv g.hom⟩ : Quiver.Total C).comp k.1 k.2.symm := (rfl)

/-- Right translation by an identity arrow `1_x` is the identity diffeomorphism of `s⁻¹(x)`. -/
@[simp]
theorem rightTranslateDiffeomorph_unit (x : C) :
    letI := sourceFiberChartedSpace I J C x
    rightTranslateDiffeomorph I J C ⟨x, x, 𝟙 x⟩ =
      Diffeomorph.refl 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
        {h : Quiver.Total C // h.left = x} ∞ := by
  let _ := sourceFiberChartedSpace I J C x
  ext h : 1
  exact Subtype.ext (Quiver.Total.id_comp h.1 h.2.symm)

include I J in
/-- Right translation is contravariant with respect to groupoid multiplication `gh = h ≫ g`:
right-translating by `g` and then by `h` agrees pointwise with right-translating by `gh`. -/
theorem coe_rightTranslateDiffeomorph_comp (g h : Quiver.Total C) (hgh : g.left = h.right)
    (a : {a : Quiver.Total C // a.left = g.right}) :
    letI := sourceFiberChartedSpace I J C g.right
    letI := sourceFiberChartedSpace I J C h.right
    letI := sourceFiberChartedSpace I J C h.left
    (rightTranslateDiffeomorph I J C h
      ⟨(rightTranslateDiffeomorph I J C g a : Quiver.Total C),
        by simp [hgh]⟩ : Quiver.Total C) =
      (rightTranslateDiffeomorph I J C (h.comp g hgh.symm)
        ⟨a.1, a.2.trans (Quiver.Total.comp_right h g hgh.symm).symm⟩ : Quiver.Total C) := by
  let _ := sourceFiberChartedSpace I J C g.right
  let _ := sourceFiberChartedSpace I J C h.right
  let _ := sourceFiberChartedSpace I J C h.left
  simp only [coe_rightTranslateDiffeomorph]
  exact (Quiver.Total.comp_assoc h g a.1 hgh.symm a.2.symm _ _).symm

end Fibers

section Composable

/-- The first projection `(g, h) ↦ g` from composable pairs to arrows is a smooth submersion, by
base change of the target submersion along source. -/
theorem isSubmersion_fst_composablePairs :
    letI := composablePairsChartedSpace I J C
    Manifold.IsSubmersion 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (fun p : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} ↦ p.1.1) := by
  rw [composablePairsChartedSpace_eq]
  exact isSubmersion_fst_transverseFiberProduct (by simp : (1 : ℕ∞ω) ≤ ∞)
    (isSubmersion_source (I := I) (J := J) (C := C)).contMDiff
    (isSubmersion_target (I := I) (J := J) (C := C)).contMDiff
    (transverse_of_isSubmersion_left
      (isSubmersion_source (I := I) (J := J) (C := C)) (by simp))
    (isSubmersion_target (I := I) (J := J) (C := C))

/-- The second projection `(g, h) ↦ h` from composable pairs to arrows is a smooth submersion, by
base change of the source submersion along target. -/
theorem isSubmersion_snd_composablePairs :
    letI := composablePairsChartedSpace I J C
    Manifold.IsSubmersion 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (fun p : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} ↦ p.1.2) := by
  rw [composablePairsChartedSpace_eq]
  exact isSubmersion_snd_transverseFiberProduct (by simp : (1 : ℕ∞ω) ≤ ∞)
    (isSubmersion_source (I := I) (J := J) (C := C)).contMDiff
    (isSubmersion_target (I := I) (J := J) (C := C)).contMDiff
    (transverse_of_isSubmersion_left
      (isSubmersion_source (I := I) (J := J) (C := C)) (by simp))
    (isSubmersion_source (I := I) (J := J) (C := C))

/-- The transverse fibre-product smooth atlas on pairs of arrows `(k, g)` sharing a target
`t(k) = t(g)`. -/
@[instance_reducible]
noncomputable def sameTargetPairsChartedSpace :
    ChartedSpace (Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
      {q : Quiver.Total C × Quiver.Total C // q.1.right = q.2.right} :=
  transverseFiberProductChartedSpace (by simp : (1 : ℕ∞ω) ≤ ∞)
    (isSubmersion_target (I := I) (J := J) (C := C)).contMDiff
    (isSubmersion_target (I := I) (J := J) (C := C)).contMDiff
    (transverse_of_isSubmersion_left
      (isSubmersion_target (I := I) (J := J) (C := C)) (by simp))

/-- Pairs of arrows sharing a target form a smooth manifold in their transverse fibre-product
atlas. -/
theorem isManifold_sameTargetPairs :
    letI := sameTargetPairsChartedSpace I J C
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      {q : Quiver.Total C × Quiver.Total C // q.1.right = q.2.right} :=
  isManifold_transverseFiberProduct (by simp : (1 : ℕ∞ω) ≤ ∞)
    (isSubmersion_target (I := I) (J := J) (C := C)).contMDiff
    (isSubmersion_target (I := I) (J := J) (C := C)).contMDiff
    (transverse_of_isSubmersion_left
      (isSubmersion_target (I := I) (J := J) (C := C)) (by simp))

/-- Inclusion of pairs sharing a target into the arrow product is a smooth embedding. -/
theorem isSmoothEmbedding_coe_sameTargetPairs :
    letI := sameTargetPairsChartedSpace I J C
    Manifold.IsSmoothEmbedding
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) (J.prod J) ∞
      (Subtype.val : {q : Quiver.Total C × Quiver.Total C // q.1.right = q.2.right} →
        Quiver.Total C × Quiver.Total C) :=
  isSmoothEmbedding_coe_transverseFiberProduct (by simp : (1 : ℕ∞ω) ≤ ∞)
    (isSubmersion_target (I := I) (J := J) (C := C)).contMDiff
    (isSubmersion_target (I := I) (J := J) (C := C)).contMDiff
    (transverse_of_isSubmersion_left
      (isSubmersion_target (I := I) (J := J) (C := C)) (by simp))

/-- **The groupoid shearing (division) diffeomorphism.** Sending `(g, h)` with `s(g) = t(h)` to
`(gh, g)` with `t(gh) = t(g)` is a smooth diffeomorphism from composable pairs onto pairs sharing
a target, with inverse `(k, g) ↦ (g, g⁻¹ k)`. -/
noncomputable def shearDiffeomorph :
    letI := composablePairsChartedSpace I J C
    letI := sameTargetPairsChartedSpace I J C
    {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} ≃ₘ^∞⟮
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)⟯
      {q : Quiver.Total C × Quiver.Total C // q.1.right = q.2.right} :=
  letI := composablePairsChartedSpace I J C
  letI := sameTargetPairsChartedSpace I J C
  { toFun := fun p ↦ ⟨(p.1.2.comp p.1.1 p.2.symm, p.1.1),
      Quiver.Total.comp_right p.1.2 p.1.1 p.2.symm⟩
    invFun := fun q ↦ ⟨(q.1.2, q.1.1.comp ⟨q.1.2.right, q.1.2.left, inv q.1.2.hom⟩ q.2),
      (Quiver.Total.comp_right q.1.1 ⟨q.1.2.right, q.1.2.left, inv q.1.2.hom⟩ q.2).symm⟩
    left_inv := fun p ↦ Subtype.ext <| Prod.ext rfl
      (Quiver.Total.comp_inv_cancel_right p.1.2 p.1.1 p.2.symm (by simp))
    right_inv := fun q ↦ Subtype.ext <| Prod.ext
      (Quiver.Total.inv_comp_cancel_right q.1.1 q.1.2 q.2 (by simp)) rfl
    contMDiff_toFun := (isSmoothEmbedding_coe_sameTargetPairs I J C).contMDiff_iff_comp.mpr <|
      (contMDiff_mul_composablePairs I J C).prodMk
        (contMDiff_fst.comp (isSmoothEmbedding_coe_composablePairs I J C).contMDiff)
    contMDiff_invFun := (isSmoothEmbedding_coe_composablePairs I J C).contMDiff_iff_comp.mpr <|
      (contMDiff_snd.comp (isSmoothEmbedding_coe_sameTargetPairs I J C).contMDiff).prodMk <|
        (contMDiff_fst.comp (isSmoothEmbedding_coe_sameTargetPairs I J C).contMDiff).quiverTotalComp
          (I := I)
          ((contMDiff_inverse (I := I) (J := J) (C := C)).comp
            (contMDiff_snd.comp (isSmoothEmbedding_coe_sameTargetPairs I J C).contMDiff))
          fun q ↦ q.2 }

@[simp]
theorem shearDiffeomorph_apply
    (p : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right}) :
    letI := composablePairsChartedSpace I J C
    letI := sameTargetPairsChartedSpace I J C
    shearDiffeomorph I J C p =
      ⟨(p.1.2.comp p.1.1 p.2.symm, p.1.1), Quiver.Total.comp_right p.1.2 p.1.1 p.2.symm⟩ := (rfl)

@[simp]
theorem shearDiffeomorph_symm_apply
    (q : {q : Quiver.Total C × Quiver.Total C // q.1.right = q.2.right}) :
    letI := composablePairsChartedSpace I J C
    letI := sameTargetPairsChartedSpace I J C
    (shearDiffeomorph I J C).symm q =
      ⟨(q.1.2, q.1.1.comp ⟨q.1.2.right, q.1.2.left, inv q.1.2.hom⟩ q.2),
        (Quiver.Total.comp_right q.1.1 ⟨q.1.2.right, q.1.2.left, inv q.1.2.hom⟩ q.2).symm⟩ := (rfl)

/-- **Groupoid multiplication is a smooth submersion.** It factors as the shearing diffeomorphism
`shearDiffeomorph` followed by the first projection on `sameTargetPairs`, which is a base-change
submersion of target. -/
theorem isSubmersion_mul :
    letI := composablePairsChartedSpace I J C
    Manifold.IsSubmersion 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (fun p : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} ↦
        p.1.2.comp p.1.1 p.2.symm) := by
  let _ := composablePairsChartedSpace I J C
  let _ := sameTargetPairsChartedSpace I J C
  have := isManifold_composablePairs I J C
  have := isManifold_sameTargetPairs I J C
  have hfst : Manifold.IsSubmersion
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (fun q : {q : Quiver.Total C × Quiver.Total C // q.1.right = q.2.right} ↦ q.1.1) :=
    isSubmersion_fst_transverseFiberProduct (by simp : (1 : ℕ∞ω) ≤ ∞)
      (isSubmersion_target (I := I) (J := J) (C := C)).contMDiff
      (isSubmersion_target (I := I) (J := J) (C := C)).contMDiff
      (transverse_of_isSubmersion_left
        (isSubmersion_target (I := I) (J := J) (C := C)) (by simp))
      (isSubmersion_target (I := I) (J := J) (C := C))
  exact (Manifold.isSubmersionOfComplement_iff.mpr fun p ↦
    ((shearDiffeomorph I J C).isLocalDiffeomorph p).isSubmersionAtOfComplement_comp
      (Manifold.isSubmersionOfComplement_iff.mp hfst.isSubmersionOfComplement_complement
        (shearDiffeomorph I J C p))).isSubmersion

/-- Inserting a right identity arrow `g ↦ (g, 1_{s(g)})` is a smooth embedding into composable
pairs, retracted by the first projection. -/
theorem isSmoothEmbedding_insertUnitRight :
    letI := composablePairsChartedSpace I J C
    Manifold.IsSmoothEmbedding J
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (fun g : Quiver.Total C ↦
        (⟨(g, ⟨g.left, g.left, 𝟙 g.left⟩), rfl⟩ :
          {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right})) := by
  let _ := composablePairsChartedSpace I J C
  have := isManifold_composablePairs I J C
  refine ((isSmoothEmbedding_coe_composablePairs I J C).contMDiff_iff_comp.mpr <|
    contMDiff_id.prodMk
      ((contMDiff_unit (I := I) (J := J) (C := C)).comp
        (contMDiff_source I J C))).isSmoothEmbedding_of_leftInverse (by simp)
    ((isSubmersion_fst_composablePairs I J C).contMDiff.of_le (by simp)) fun _ ↦ rfl

/-- Inserting a left identity arrow `h ↦ (1_{t(h)}, h)` is a smooth embedding into composable
pairs, retracted by the second projection. -/
theorem isSmoothEmbedding_insertUnitLeft :
    letI := composablePairsChartedSpace I J C
    Manifold.IsSmoothEmbedding J
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (fun h : Quiver.Total C ↦
        (⟨(⟨h.right, h.right, 𝟙 h.right⟩, h), rfl⟩ :
          {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right})) := by
  let _ := composablePairsChartedSpace I J C
  have := isManifold_composablePairs I J C
  refine ((isSmoothEmbedding_coe_composablePairs I J C).contMDiff_iff_comp.mpr <|
    ((contMDiff_unit (I := I) (J := J) (C := C)).comp
      (contMDiff_target I J C)).prodMk contMDiff_id).isSmoothEmbedding_of_leftInverse (by simp)
    ((isSubmersion_snd_composablePairs I J C).contMDiff.of_le (by simp)) fun _ ↦ rfl

/-- Smooth atlas on left-parenthesized composable triples `((g, h), k)` with `s(g) = t(h)` and
`s(h) = t(k)`, constructed as the transverse fibre product of `s ∘ snd` and `t`. -/
@[instance_reducible]
noncomputable def composableTriplesLeftChartedSpace :
    letI := composablePairsChartedSpace I J C
    ChartedSpace
      (Fin (finrank ℝ (Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) +
        finrank ℝ E' - finrank ℝ E) → ℝ)
      {p : {q : Quiver.Total C × Quiver.Total C // q.1.left = q.2.right} × Quiver.Total C //
        p.1.1.2.left = p.2.right} :=
  letI := composablePairsChartedSpace I J C
  haveI := isManifold_composablePairs I J C
  transverseFiberProductChartedSpace (by simp : (1 : ℕ∞ω) ≤ ∞)
    ((contMDiff_source I J C).comp (isSubmersion_snd_composablePairs I J C).contMDiff)
    (isSubmersion_target (I := I) (J := J) (C := C)).contMDiff
    (transverse_of_isSubmersion_right
      (isSubmersion_target (I := I) (J := J) (C := C)) (by simp))

/-- Left-parenthesized composable triples form a smooth manifold. -/
theorem isManifold_composableTriplesLeft :
    letI := composablePairsChartedSpace I J C
    letI := composableTriplesLeftChartedSpace I J C
    IsManifold
      𝓘(ℝ, Fin (finrank ℝ (Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) +
        finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      {p : {q : Quiver.Total C × Quiver.Total C // q.1.left = q.2.right} × Quiver.Total C //
        p.1.1.2.left = p.2.right} := by
  let _ := composablePairsChartedSpace I J C
  have := isManifold_composablePairs I J C
  exact isManifold_transverseFiberProduct (by simp : (1 : ℕ∞ω) ≤ ∞)
    ((contMDiff_source I J C).comp (isSubmersion_snd_composablePairs I J C).contMDiff)
    (isSubmersion_target (I := I) (J := J) (C := C)).contMDiff
    (transverse_of_isSubmersion_right
      (isSubmersion_target (I := I) (J := J) (C := C)) (by simp))

/-- Inclusion of left-parenthesized composable triples into `Γ^{(2)} × Γ` is a smooth embedding. -/
theorem isSmoothEmbedding_coe_composableTriplesLeft :
    letI := composablePairsChartedSpace I J C
    letI := composableTriplesLeftChartedSpace I J C
    Manifold.IsSmoothEmbedding
      𝓘(ℝ, Fin (finrank ℝ (Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) +
        finrank ℝ E' - finrank ℝ E) → ℝ)
      (𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ).prod J) ∞
      (Subtype.val :
        {p : {q : Quiver.Total C × Quiver.Total C // q.1.left = q.2.right} × Quiver.Total C //
          p.1.1.2.left = p.2.right} →
        {q : Quiver.Total C × Quiver.Total C // q.1.left = q.2.right} × Quiver.Total C) := by
  let _ := composablePairsChartedSpace I J C
  have := isManifold_composablePairs I J C
  exact isSmoothEmbedding_coe_transverseFiberProduct (by simp : (1 : ℕ∞ω) ≤ ∞)
    ((contMDiff_source I J C).comp (isSubmersion_snd_composablePairs I J C).contMDiff)
    (isSubmersion_target (I := I) (J := J) (C := C)).contMDiff
    (transverse_of_isSubmersion_right
      (isSubmersion_target (I := I) (J := J) (C := C)) (by simp))

/-- Smooth atlas on right-parenthesized composable triples `(g, (h, k))` with `s(g) = t(h)` and
`s(h) = t(k)`, constructed as the transverse fibre product of `s` and `t ∘ fst`. -/
@[instance_reducible]
noncomputable def composableTriplesRightChartedSpace :
    letI := composablePairsChartedSpace I J C
    ChartedSpace
      (Fin (finrank ℝ E' +
        finrank ℝ (Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) - finrank ℝ E) → ℝ)
      {p : Quiver.Total C × {q : Quiver.Total C × Quiver.Total C // q.1.left = q.2.right} //
        p.1.left = p.2.1.1.right} :=
  letI := composablePairsChartedSpace I J C
  haveI := isManifold_composablePairs I J C
  transverseFiberProductChartedSpace (by simp : (1 : ℕ∞ω) ≤ ∞)
    (isSubmersion_source (I := I) (J := J) (C := C)).contMDiff
    ((contMDiff_target I J C).comp (isSubmersion_fst_composablePairs I J C).contMDiff)
    (transverse_of_isSubmersion_left
      (isSubmersion_source (I := I) (J := J) (C := C)) (by simp))

/-- Right-parenthesized composable triples form a smooth manifold. -/
theorem isManifold_composableTriplesRight :
    letI := composablePairsChartedSpace I J C
    letI := composableTriplesRightChartedSpace I J C
    IsManifold
      𝓘(ℝ, Fin (finrank ℝ E' +
        finrank ℝ (Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) - finrank ℝ E) → ℝ) ∞
      {p : Quiver.Total C × {q : Quiver.Total C × Quiver.Total C // q.1.left = q.2.right} //
        p.1.left = p.2.1.1.right} := by
  let _ := composablePairsChartedSpace I J C
  have := isManifold_composablePairs I J C
  exact isManifold_transverseFiberProduct (by simp : (1 : ℕ∞ω) ≤ ∞)
    (isSubmersion_source (I := I) (J := J) (C := C)).contMDiff
    ((contMDiff_target I J C).comp (isSubmersion_fst_composablePairs I J C).contMDiff)
    (transverse_of_isSubmersion_left
      (isSubmersion_source (I := I) (J := J) (C := C)) (by simp))

/-- Inclusion of right-parenthesized composable triples into `Γ × Γ^{(2)}` is a smooth embedding. -/
theorem isSmoothEmbedding_coe_composableTriplesRight :
    letI := composablePairsChartedSpace I J C
    letI := composableTriplesRightChartedSpace I J C
    Manifold.IsSmoothEmbedding
      𝓘(ℝ, Fin (finrank ℝ E' +
        finrank ℝ (Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) - finrank ℝ E) → ℝ)
      (J.prod 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)) ∞
      (Subtype.val :
        {p : Quiver.Total C × {q : Quiver.Total C × Quiver.Total C // q.1.left = q.2.right} //
          p.1.left = p.2.1.1.right} →
        Quiver.Total C × {q : Quiver.Total C × Quiver.Total C // q.1.left = q.2.right}) := by
  let _ := composablePairsChartedSpace I J C
  have := isManifold_composablePairs I J C
  exact isSmoothEmbedding_coe_transverseFiberProduct (by simp : (1 : ℕ∞ω) ≤ ∞)
    (isSubmersion_source (I := I) (J := J) (C := C)).contMDiff
    ((contMDiff_target I J C).comp (isSubmersion_fst_composablePairs I J C).contMDiff)
    (transverse_of_isSubmersion_left
      (isSubmersion_source (I := I) (J := J) (C := C)) (by simp))

/-- **Smooth associator of composable triples.** Regrouping `((g, h), k) ↦ (g, (h, k))` is a
smooth diffeomorphism between the two iterated transverse fibre-product atlases on composable
triples. -/
noncomputable def composableTriplesAssocDiffeomorph :
    letI := composablePairsChartedSpace I J C
    letI := composableTriplesLeftChartedSpace I J C
    letI := composableTriplesRightChartedSpace I J C
    {p : {q : Quiver.Total C × Quiver.Total C // q.1.left = q.2.right} × Quiver.Total C //
      p.1.1.2.left = p.2.right} ≃ₘ^∞⟮
      𝓘(ℝ, Fin (finrank ℝ (Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) +
        finrank ℝ E' - finrank ℝ E) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E' +
        finrank ℝ (Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) - finrank ℝ E) → ℝ)⟯
    {p : Quiver.Total C × {q : Quiver.Total C × Quiver.Total C // q.1.left = q.2.right} //
      p.1.left = p.2.1.1.right} :=
  letI := composablePairsChartedSpace I J C
  letI := composableTriplesLeftChartedSpace I J C
  letI := composableTriplesRightChartedSpace I J C
  fiberProductAssocDiffeomorph
    (isSmoothEmbedding_coe_composablePairs I J C)
    (isSmoothEmbedding_coe_composablePairs I J C)
    (isSmoothEmbedding_coe_composableTriplesLeft I J C)
    (isSmoothEmbedding_coe_composableTriplesRight I J C)

@[simp]
theorem composableTriplesAssocDiffeomorph_apply
    (p : {p : {q : Quiver.Total C × Quiver.Total C // q.1.left = q.2.right} × Quiver.Total C //
      p.1.1.2.left = p.2.right}) :
    letI := composablePairsChartedSpace I J C
    letI := composableTriplesLeftChartedSpace I J C
    letI := composableTriplesRightChartedSpace I J C
    composableTriplesAssocDiffeomorph I J C p =
      ⟨(p.1.1.1.1, ⟨(p.1.1.1.2, p.1.2), p.2⟩), p.1.1.2⟩ :=
  letI := composablePairsChartedSpace I J C
  letI := composableTriplesLeftChartedSpace I J C
  letI := composableTriplesRightChartedSpace I J C
  fiberProductAssocDiffeomorph_apply
    (isSmoothEmbedding_coe_composablePairs I J C)
    (isSmoothEmbedding_coe_composablePairs I J C)
    (isSmoothEmbedding_coe_composableTriplesLeft I J C)
    (isSmoothEmbedding_coe_composableTriplesRight I J C) p

/-- Left-associated ternary multiplication `((g, h), k) ↦ (gh)k = k ≫ (h ≫ g)` is smooth on
left-parenthesized composable triples. -/
theorem contMDiff_mulComposableTriplesLeft :
    letI := composablePairsChartedSpace I J C
    letI := composableTriplesLeftChartedSpace I J C
    ContMDiff
      𝓘(ℝ, Fin (finrank ℝ (Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) +
        finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (fun p : {p : {q : Quiver.Total C × Quiver.Total C // q.1.left = q.2.right} ×
          Quiver.Total C // p.1.1.2.left = p.2.right} ↦
        p.1.2.comp (p.1.1.1.2.comp p.1.1.1.1 p.1.1.2.symm)
          (p.2.symm.trans (Quiver.Total.comp_left _ _ _).symm)) := by
  let _ := composablePairsChartedSpace I J C
  let _ := composableTriplesLeftChartedSpace I J C
  have hL := (isSmoothEmbedding_coe_composableTriplesLeft I J C).contMDiff
  exact (((contMDiff_mul_composablePairs I J C).comp
    (contMDiff_fst.comp hL)).quiverTotalMul (I := I) (contMDiff_snd.comp hL) fun p ↦
      (Quiver.Total.comp_left _ _ _).trans p.2).congr fun _ ↦ Quiver.Total.comp_congr rfl rfl _ _

/-- Right-associated ternary multiplication `(g, (h, k)) ↦ g(hk) = (k ≫ h) ≫ g` is smooth on
right-parenthesized composable triples. -/
theorem contMDiff_mulComposableTriplesRight :
    letI := composablePairsChartedSpace I J C
    letI := composableTriplesRightChartedSpace I J C
    ContMDiff
      𝓘(ℝ, Fin (finrank ℝ E' +
        finrank ℝ (Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) - finrank ℝ E) → ℝ) J ∞
      (fun p : {p : Quiver.Total C ×
          {q : Quiver.Total C × Quiver.Total C // q.1.left = q.2.right} //
          p.1.left = p.2.1.1.right} ↦
        (p.1.2.1.2.comp p.1.2.1.1 p.1.2.2.symm).comp p.1.1
          ((Quiver.Total.comp_right _ _ _).trans p.2.symm)) := by
  let _ := composablePairsChartedSpace I J C
  let _ := composableTriplesRightChartedSpace I J C
  have hR := (isSmoothEmbedding_coe_composableTriplesRight I J C).contMDiff
  exact ((contMDiff_fst.comp hR).quiverTotalMul (I := I)
    ((contMDiff_mul_composablePairs I J C).comp (contMDiff_snd.comp hR)) fun p ↦
      p.2.trans (Quiver.Total.comp_right _ _ _).symm).congr fun _ ↦
        Quiver.Total.comp_congr rfl rfl _ _

include I J in
/-- Left- and right-associated ternary multiplications agree along
`composableTriplesAssocDiffeomorph`. -/
theorem mulComposableTriplesLeft_eq
    (p : {p : {q : Quiver.Total C × Quiver.Total C // q.1.left = q.2.right} × Quiver.Total C //
      p.1.1.2.left = p.2.right}) :
    letI := composablePairsChartedSpace I J C
    letI := composableTriplesLeftChartedSpace I J C
    letI := composableTriplesRightChartedSpace I J C
    p.1.2.comp (p.1.1.1.2.comp p.1.1.1.1 p.1.1.2.symm)
      (p.2.symm.trans (Quiver.Total.comp_left _ _ _).symm) =
      (let q := composableTriplesAssocDiffeomorph I J C p;
        (q.1.2.1.2.comp q.1.2.1.1 q.1.2.2.symm).comp q.1.1
          ((Quiver.Total.comp_right _ _ _).trans q.2.symm)) := by
  let _ := composablePairsChartedSpace I J C
  let _ := composableTriplesLeftChartedSpace I J C
  let _ := composableTriplesRightChartedSpace I J C
  dsimp only
  generalize hq : composableTriplesAssocDiffeomorph I J C p = q
  rw [composableTriplesAssocDiffeomorph_apply] at hq
  subst hq
  exact (Quiver.Total.comp_assoc p.1.2 p.1.1.1.2 p.1.1.1.1 p.2.symm p.1.1.2.symm _ _).symm

end Composable

end TauCeti.IsLieGroupoid
