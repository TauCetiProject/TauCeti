/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Groupoid.Basic
public import TauCeti.Geometry.Manifold.RegularValue.ManifoldLevel

/-!
# Source and target fibres and translation diffeomorphisms of a Lie groupoid

For a Lie groupoid `C` with object model `I` (dimension `m`) and arrow model `J` (dimension `d`),
every object `x : C` is a regular value of both the source projection `Quiver.Total.left` and the
target projection `Quiver.Total.right`. Applying `TauCeti.regularFiberChartedSpace` equips every
source fibre `{a : Quiver.Total C // a.left = x}` and every target fibre
`{a : Quiver.Total C // a.right = x}` with an embedded smooth submanifold structure of dimension
`d - m` whose tangent space inside `TangentSpace J a` is `ker(ds_a)` or `ker(dt_a)`.

Even when the total-arrow manifold `Quiver.Total C` is non-Hausdorff:

* every source fibre and every target fibre is closed in `Quiver.Total C` because `C` is Hausdorff
  (`IsLieGroupoid.isClosed_sourceFiber`, `IsLieGroupoid.isClosed_targetFiber`);
* groupoid inversion restricts to a diffeomorphism between the source fibre over `x` and the target
  fibre over `x` (`IsLieGroupoid.inverseSourceTargetDiffeomorph`), making every target fibre
  Hausdorff and second-countable (`IsLieGroupoid.t2Space_targetFiber`,
  `IsLieGroupoid.secondCountableTopology_targetFiber`).

Each arrow `g : Quiver.Total C` induces smooth translation diffeomorphisms between fibres (following
the categorical composition convention where `a.comp b _` traverses `a` then `b`, i.e. the
geometric product `b · a`):

* **left multiplication** (`IsLieGroupoid.leftMulDiffeomorph`) sends `h` with `h.right = g.left` to
  `h ≫ g` with `(h ≫ g).right = g.right`, giving a diffeomorphism between target fibres
  `t⁻¹(s(g)) ≃ₘ^∞ t⁻¹(t(g))` that carries `1_{s(g)}` to `g`, satisfies
  `(leftMulDiffeomorph g)⁻¹ = leftMulDiffeomorph g⁻¹`, and composes covariantly along morphisms
  (`IsLieGroupoid.leftMulDiffeomorph_trans`);
* **right multiplication** (`IsLieGroupoid.rightMulDiffeomorph`) sends `h` with `h.left = g.right`
  to `g ≫ h` with `(g ≫ h).left = g.left`, giving a diffeomorphism between source fibres
  `s⁻¹(t(g)) ≃ₘ^∞ s⁻¹(s(g))` that carries the identity arrow `1_{t(g)}` to `g`, satisfies
  `(rightMulDiffeomorph g)⁻¹ = rightMulDiffeomorph g⁻¹`, composes contravariantly along morphisms
  (`IsLieGroupoid.rightMulDiffeomorph_trans`), and intertwines with `leftMulDiffeomorph` under
  `inverseSourceTargetDiffeomorph`
  (`IsLieGroupoid.rightMulDiffeomorph_trans_inverseSourceTargetDiffeomorph`).

## Main definitions

* `TauCeti.IsLieGroupoid.sourceFiberChartedSpace`: regular-fibre smooth atlas on
  `{a : Quiver.Total C // a.left = x}`.
* `TauCeti.IsLieGroupoid.targetFiberChartedSpace`: regular-fibre smooth atlas on
  `{a : Quiver.Total C // a.right = x}`.
* `TauCeti.IsLieGroupoid.inverseSourceTargetDiffeomorph`: inversion diffeomorphism
  `s⁻¹(x) ≃ₘ^∞ t⁻¹(x)`.
* `TauCeti.IsLieGroupoid.leftMulDiffeomorph`: left-translation diffeomorphism
  `t⁻¹(s(g)) ≃ₘ^∞ t⁻¹(t(g))`.
* `TauCeti.IsLieGroupoid.rightMulDiffeomorph`: right-translation diffeomorphism
  `s⁻¹(t(g)) ≃ₘ^∞ s⁻¹(s(g))`.

## References

* K. C. H. Mackenzie, *General Theory of Lie Groupoids and Lie Algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), Proposition 1.1.4 and Section 3.5.
* I. Moerdijk and J. Mrčun, *Introduction to Foliations and Lie Groupoids*, Cambridge Stud. Adv.
  Math. 91, Cambridge University Press (2003), Section 5.1.
-/

public section

noncomputable section

open CategoryTheory Function Module Topology
open scoped Manifold ContDiff

namespace TauCeti

namespace IsLieGroupoid

variable {E H E' H' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
  (J : ModelWithCorners ℝ E' H') [J.Boundaryless]
  {C : Type*} [Category C] [IsGroupoid C]
  [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
  [IsManifold J ∞ (Quiver.Total C)]
  [IsLieGroupoid I J C]

/-! ### Source fibres as embedded smooth submanifolds -/

/-- Every object of a Lie groupoid is a regular value of the source projection. -/
theorem isRegularValue_source (x : C) :
    IsRegularValue J I (Quiver.Total.left : Quiver.Total C → C) x :=
  isRegularValue_iff.2 fun a _ ↦
    isRegularPoint_iff.2 ((isSubmersion_source (I := I) (J := J) (C := C)).surjective_mfderiv
      (by simp) a)

/-- The smooth manifold atlas on the source fibre `{a : Quiver.Total C // a.left = x}`, constructed
by `TauCeti.regularFiberChartedSpace`. -/
@[expose, instance_reducible]
def sourceFiberChartedSpace (x : C) :
    ChartedSpace (Fin (finrank ℝ E' - finrank ℝ E) → ℝ) {a : Quiver.Total C // a.left = x} :=
  regularFiberChartedSpace (m := ∞) (by simp) (contMDiff_source I J C)
    BoundarylessManifold.isInteriorPoint (isRegularValue_source I J x)

/-- Every source fibre of a Lie groupoid is a smooth manifold of dimension
`dim(arrows) - dim(objects)`. -/
theorem isManifold_sourceFiber (x : C) :
    letI := sourceFiberChartedSpace I J x
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ∞ {a : Quiver.Total C // a.left = x} :=
  isManifold_regularFiber (m := ∞) (by simp) (contMDiff_source I J C)
    BoundarylessManifold.isInteriorPoint (isRegularValue_source I J x)

/-- The inclusion of a source fibre into the total-arrow manifold is a smooth embedding. -/
theorem isSmoothEmbedding_coe_sourceFiber (x : C) :
    letI := sourceFiberChartedSpace I J x
    Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (Subtype.val : {a : Quiver.Total C // a.left = x} → Quiver.Total C) :=
  isSmoothEmbedding_coe_regularFiber (m := ∞) (by simp) (contMDiff_source I J C)
    BoundarylessManifold.isInteriorPoint (isRegularValue_source I J x)

/-- The tangent image of the source-fibre inclusion at `a` is `ker(mfderiv J I left a)`. -/
theorem range_mfderiv_coe_sourceFiber (x : C) :
    letI := sourceFiberChartedSpace I J x
    ∀ a : {a : Quiver.Total C // a.left = x},
      (mfderiv 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) J Subtype.val a).range =
        (mfderiv J I (Quiver.Total.left : Quiver.Total C → C) a.val).ker :=
  range_mfderiv_coe_regularFiber (m := ∞) (by simp) (contMDiff_source I J C)
    BoundarylessManifold.isInteriorPoint (isRegularValue_source I J x)

include I J in
/-- Every source fibre of a Lie groupoid is closed in `Quiver.Total C`, since `C` is Hausdorff. -/
theorem isClosed_sourceFiber (x : C) : IsClosed {a : Quiver.Total C | a.left = x} :=
  have := t2Space_objects (I := I) (J := J) (C := C)
  isClosed_singleton.preimage (contMDiff_source I J C).continuous

include I J in
/-- Every source fibre of a Lie groupoid is second-countable. -/
theorem secondCountableTopology_sourceFiber (x : C) :
    SecondCountableTopology {a : Quiver.Total C // a.left = x} :=
  have := secondCountableTopology_arrows (I := I) (J := J) (C := C)
  Topology.IsEmbedding.subtypeVal.secondCountableTopology

/-! ### Target fibres and inversion diffeomorphism between source and target fibres -/

/-- Every object of a Lie groupoid is a regular value of the target projection. -/
theorem isRegularValue_target (x : C) :
    IsRegularValue J I (Quiver.Total.right : Quiver.Total C → C) x :=
  isRegularValue_iff.2 fun a _ ↦
    isRegularPoint_iff.2 ((isSubmersion_target I J C).surjective_mfderiv (by simp) a)

/-- The smooth manifold atlas on the target fibre `{a : Quiver.Total C // a.right = x}`,
constructed by `TauCeti.regularFiberChartedSpace`. -/
@[expose, instance_reducible]
def targetFiberChartedSpace (x : C) :
    ChartedSpace (Fin (finrank ℝ E' - finrank ℝ E) → ℝ) {a : Quiver.Total C // a.right = x} :=
  regularFiberChartedSpace (m := ∞) (by simp) (contMDiff_target I J C)
    BoundarylessManifold.isInteriorPoint (isRegularValue_target I J x)

/-- Every target fibre of a Lie groupoid is a smooth manifold of dimension
`dim(arrows) - dim(objects)`. -/
theorem isManifold_targetFiber (x : C) :
    letI := targetFiberChartedSpace I J x
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) ∞ {a : Quiver.Total C // a.right = x} :=
  isManifold_regularFiber (m := ∞) (by simp) (contMDiff_target I J C)
    BoundarylessManifold.isInteriorPoint (isRegularValue_target I J x)

/-- The inclusion of a target fibre into the total-arrow manifold is a smooth embedding. -/
theorem isSmoothEmbedding_coe_targetFiber (x : C) :
    letI := targetFiberChartedSpace I J x
    Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (Subtype.val : {a : Quiver.Total C // a.right = x} → Quiver.Total C) :=
  isSmoothEmbedding_coe_regularFiber (m := ∞) (by simp) (contMDiff_target I J C)
    BoundarylessManifold.isInteriorPoint (isRegularValue_target I J x)

/-- The tangent image of the target-fibre inclusion at `a` is `ker(mfderiv J I right a)`. -/
theorem range_mfderiv_coe_targetFiber (x : C) :
    letI := targetFiberChartedSpace I J x
    ∀ a : {a : Quiver.Total C // a.right = x},
      (mfderiv 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) J Subtype.val a).range =
        (mfderiv J I (Quiver.Total.right : Quiver.Total C → C) a.val).ker :=
  range_mfderiv_coe_regularFiber (m := ∞) (by simp) (contMDiff_target I J C)
    BoundarylessManifold.isInteriorPoint (isRegularValue_target I J x)

include I J in
/-- Every target fibre of a Lie groupoid is closed in `Quiver.Total C`, since `C` is Hausdorff. -/
theorem isClosed_targetFiber (x : C) : IsClosed {a : Quiver.Total C | a.right = x} :=
  have := t2Space_objects (I := I) (J := J) (C := C)
  isClosed_singleton.preimage (contMDiff_target I J C).continuous

include I J in
/-- Every target fibre of a Lie groupoid is second-countable. -/
theorem secondCountableTopology_targetFiber (x : C) :
    SecondCountableTopology {a : Quiver.Total C // a.right = x} :=
  have := secondCountableTopology_arrows (I := I) (J := J) (C := C)
  Topology.IsEmbedding.subtypeVal.secondCountableTopology

/-- Groupoid inversion restricts to a `C^∞` diffeomorphism from the source fibre over `x` onto the
target fibre over `x`. -/
def inverseSourceTargetDiffeomorph (x : C) :
    letI := sourceFiberChartedSpace I J x
    letI := targetFiberChartedSpace I J x
    {a : Quiver.Total C // a.left = x} ≃ₘ^∞⟮
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)⟯
      {a : Quiver.Total C // a.right = x} :=
  letI := sourceFiberChartedSpace I J x
  letI := targetFiberChartedSpace I J x
  { toFun := fun a ↦ ⟨⟨a.val.right, a.val.left, inv a.val.hom⟩, a.property⟩
    invFun := fun b ↦ ⟨⟨b.val.right, b.val.left, inv b.val.hom⟩, b.property⟩
    left_inv := fun ⟨a, _⟩ ↦ Subtype.ext (by cases a; simp)
    right_inv := fun ⟨b, _⟩ ↦ Subtype.ext (by cases b; simp)
    contMDiff_toFun := by
      have := isManifold_sourceFiber I J x
      have := isManifold_targetFiber I J x
      exact ((isSmoothEmbedding_coe_targetFiber I J x).contMDiff_iff_comp
        (f := fun a : {a : Quiver.Total C // a.left = x} ↦
          (⟨⟨a.val.right, a.val.left, inv a.val.hom⟩, a.property⟩ :
            {a : Quiver.Total C // a.right = x}))).2
        ((contMDiff_inverse (I := I) (J := J) (C := C)).comp
          (isSmoothEmbedding_coe_sourceFiber I J x).contMDiff)
    contMDiff_invFun := by
      have := isManifold_sourceFiber I J x
      have := isManifold_targetFiber I J x
      exact ((isSmoothEmbedding_coe_sourceFiber I J x).contMDiff_iff_comp
        (f := fun b : {a : Quiver.Total C // a.right = x} ↦
          (⟨⟨b.val.right, b.val.left, inv b.val.hom⟩, b.property⟩ :
            {a : Quiver.Total C // a.left = x}))).2
        ((contMDiff_inverse (I := I) (J := J) (C := C)).comp
          (isSmoothEmbedding_coe_targetFiber I J x).contMDiff) }

@[simp]
theorem coe_inverseSourceTargetDiffeomorph_apply (x : C)
    (a : {a : Quiver.Total C // a.left = x}) :
    letI := sourceFiberChartedSpace I J x
    letI := targetFiberChartedSpace I J x
    (inverseSourceTargetDiffeomorph I J x a).val = ⟨a.val.right, a.val.left, inv a.val.hom⟩ :=
  (rfl)

@[simp]
theorem coe_inverseSourceTargetDiffeomorph_symm_apply (x : C)
    (b : {a : Quiver.Total C // a.right = x}) :
    letI := sourceFiberChartedSpace I J x
    letI := targetFiberChartedSpace I J x
    ((inverseSourceTargetDiffeomorph I J x).symm b).val =
      ⟨b.val.right, b.val.left, inv b.val.hom⟩ :=
  (rfl)

include I J in
/-- Every target fibre of a Lie groupoid is Hausdorff in the subspace topology, because inversion
maps it homeomorphically onto the corresponding Hausdorff source fibre. -/
theorem t2Space_targetFiber (x : C) : T2Space {a : Quiver.Total C // a.right = x} := by
  let := sourceFiberChartedSpace I J x
  let := targetFiberChartedSpace I J x
  have := t2Space_sourceFiber (I := I) (J := J) x
  exact T2Space.of_injective_continuous (inverseSourceTargetDiffeomorph I J x).symm.injective
    (inverseSourceTargetDiffeomorph I J x).symm.continuous

/-! ### Smooth left and right translations between fibres -/

/-- Postcomposing with a fixed arrow `g` is smooth on the target fibre over `g.left`. -/
theorem contMDiff_comp_const_right (g : Quiver.Total C) :
    letI := targetFiberChartedSpace I J g.left
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (fun a : {a : Quiver.Total C // a.right = g.left} ↦ a.val.comp g a.property) := by
  let := targetFiberChartedSpace I J g.left
  let := composablePairsChartedSpace I J C
  have := isManifold_targetFiber I J g.left
  have := isManifold_composablePairs I J C
  let ins : {a : Quiver.Total C // a.right = g.left} →
      {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} :=
    fun a ↦ ⟨(a.val, g), a.property⟩
  have hins : ContMDiff 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞ ins :=
    ((isSmoothEmbedding_coe_composablePairs I J C).contMDiff_iff_comp (f := ins)).2
      ((isSmoothEmbedding_coe_targetFiber I J g.left).contMDiff.prodMk contMDiff_const)
  exact (contMDiff_comp_composablePairs I J C).comp hins

/-- Precomposing with a fixed arrow `g` is smooth on the source fibre over `g.right`. -/
theorem contMDiff_comp_const_left (g : Quiver.Total C) :
    letI := sourceFiberChartedSpace I J g.right
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (fun a : {a : Quiver.Total C // a.left = g.right} ↦ g.comp a.val a.property.symm) := by
  let := sourceFiberChartedSpace I J g.right
  let := composablePairsChartedSpace I J C
  have := isManifold_sourceFiber I J g.right
  have := isManifold_composablePairs I J C
  let ins : {a : Quiver.Total C // a.left = g.right} →
      {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} :=
    fun a ↦ ⟨(g, a.val), a.property.symm⟩
  have hins : ContMDiff 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞ ins :=
    ((isSmoothEmbedding_coe_composablePairs I J C).contMDiff_iff_comp (f := ins)).2
      (contMDiff_const.prodMk (isSmoothEmbedding_coe_sourceFiber I J g.right).contMDiff)
  exact (contMDiff_comp_composablePairs I J C).comp hins

/-- **Left translation** by an arrow `g : Quiver.Total C` (`h ↦ h ≫ g`, the geometric left product
`g · h`) is a `C^∞` diffeomorphism from the target fibre `t⁻¹(s(g))` onto `t⁻¹(t(g))`, with
inverse given by left translation by `g⁻¹`. -/
def leftMulDiffeomorph (g : Quiver.Total C) :
    letI := targetFiberChartedSpace I J g.left
    letI := targetFiberChartedSpace I J g.right
    {a : Quiver.Total C // a.right = g.left} ≃ₘ^∞⟮
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)⟯
      {a : Quiver.Total C // a.right = g.right} :=
  letI := targetFiberChartedSpace I J g.left
  letI := targetFiberChartedSpace I J g.right
  { toFun := fun a ↦ ⟨a.val.comp g a.property, Quiver.Total.comp_right a.val g a.property⟩
    invFun := fun b ↦
      ⟨b.val.comp (⟨g.right, g.left, inv g.hom⟩ : Quiver.Total C) b.property,
        Quiver.Total.comp_right b.val (⟨g.right, g.left, inv g.hom⟩ : Quiver.Total C) b.property⟩
    left_inv := fun a ↦ Subtype.ext (a.val.comp_comp_inv g a.property _)
    right_inv := fun b ↦ Subtype.ext (b.val.comp_inv_comp_right g b.property _)
    contMDiff_toFun := by
      have := isManifold_targetFiber I J g.left
      have := isManifold_targetFiber I J g.right
      exact ((isSmoothEmbedding_coe_targetFiber I J g.right).contMDiff_iff_comp
        (f := fun a : {a : Quiver.Total C // a.right = g.left} ↦
          (⟨a.val.comp g a.property, Quiver.Total.comp_right a.val g a.property⟩ :
            {a : Quiver.Total C // a.right = g.right}))).2
        (contMDiff_comp_const_right I J g)
    contMDiff_invFun := by
      have := isManifold_targetFiber I J g.left
      have := isManifold_targetFiber I J g.right
      exact ((isSmoothEmbedding_coe_targetFiber I J g.left).contMDiff_iff_comp
        (f := fun b : {a : Quiver.Total C // a.right = g.right} ↦
          (⟨b.val.comp (⟨g.right, g.left, inv g.hom⟩ : Quiver.Total C) b.property,
            Quiver.Total.comp_right b.val (⟨g.right, g.left, inv g.hom⟩ : Quiver.Total C)
              b.property⟩ :
            {a : Quiver.Total C // a.right = g.left}))).2
        (contMDiff_comp_const_right I J (⟨g.right, g.left, inv g.hom⟩ : Quiver.Total C)) }

@[simp]
theorem coe_leftMulDiffeomorph_apply (g : Quiver.Total C)
    (a : {a : Quiver.Total C // a.right = g.left}) :
    letI := targetFiberChartedSpace I J g.left
    letI := targetFiberChartedSpace I J g.right
    (leftMulDiffeomorph I J g a).val = a.val.comp g a.property :=
  (rfl)

@[simp]
theorem coe_leftMulDiffeomorph_symm_apply (g : Quiver.Total C)
    (b : {a : Quiver.Total C // a.right = g.right}) :
    letI := targetFiberChartedSpace I J g.left
    letI := targetFiberChartedSpace I J g.right
    ((leftMulDiffeomorph I J g).symm b).val =
      b.val.comp (⟨g.right, g.left, inv g.hom⟩ : Quiver.Total C) b.property :=
  (rfl)

@[simp]
theorem leftMulDiffeomorph_apply_unit (g : Quiver.Total C) :
    letI := targetFiberChartedSpace I J g.left
    letI := targetFiberChartedSpace I J g.right
    leftMulDiffeomorph I J g ⟨⟨g.left, g.left, 𝟙 g.left⟩, rfl⟩ = ⟨g, rfl⟩ := by
  let := targetFiberChartedSpace I J g.left
  let := targetFiberChartedSpace I J g.right
  exact Subtype.ext g.unit_comp

@[simp]
theorem leftMulDiffeomorph_unit (x : C) :
    letI := targetFiberChartedSpace I J x
    leftMulDiffeomorph I J (⟨x, x, 𝟙 x⟩ : Quiver.Total C) =
      Diffeomorph.refl 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
        {a : Quiver.Total C // a.right = x} ∞ := by
  let := targetFiberChartedSpace I J x
  ext1 ⟨a, ha⟩
  dsimp only at ha
  subst ha
  exact Subtype.ext a.comp_unit

/-- The inverse of left translation by `g` is left translation by `g⁻¹`. -/
theorem leftMulDiffeomorph_symm (g : Quiver.Total C) :
    letI := targetFiberChartedSpace I J g.left
    letI := targetFiberChartedSpace I J g.right
    (leftMulDiffeomorph I J g).symm =
      leftMulDiffeomorph I J (⟨g.right, g.left, inv g.hom⟩ : Quiver.Total C) := by
  let := targetFiberChartedSpace I J g.left
  let := targetFiberChartedSpace I J g.right
  ext1 b
  rfl

/-- Functoriality of left translation: left translating by `f : x ⟶ y` and then by `g : y ⟶ z`
equals left translating by `f ≫ g : x ⟶ z`. -/
theorem leftMulDiffeomorph_trans {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    letI := targetFiberChartedSpace I J x
    letI := targetFiberChartedSpace I J y
    letI := targetFiberChartedSpace I J z
    (leftMulDiffeomorph I J (⟨x, y, f⟩ : Quiver.Total C)).trans
      (leftMulDiffeomorph I J (⟨y, z, g⟩ : Quiver.Total C)) =
      leftMulDiffeomorph I J (⟨x, z, f ≫ g⟩ : Quiver.Total C) := by
  let := targetFiberChartedSpace I J x
  let := targetFiberChartedSpace I J y
  let := targetFiberChartedSpace I J z
  refine Diffeomorph.ext fun h ↦ Subtype.ext ?_
  have hab : h.val.right = ((⟨x, y, f⟩ : Quiver.Total C).comp ⟨y, z, g⟩ rfl).left :=
    h.property.trans ((⟨x, y, f⟩ : Quiver.Total C).comp_left ⟨y, z, g⟩ rfl).symm
  exact (Quiver.Total.comp_assoc h.val ⟨x, y, f⟩ ⟨y, z, g⟩ h.property rfl _ hab).trans
    (Quiver.Total.comp_congr rfl (Quiver.Total.mk_comp_mk f g) hab h.property)

/-- Pointwise functoriality of left translation along arbitrary composable total arrows. -/
theorem coe_leftMulDiffeomorph_comp_apply {g₁ g₂ : Quiver.Total C} (hg : g₁.right = g₂.left)
    (h : {a : Quiver.Total C // a.right = g₁.left}) :
    letI := targetFiberChartedSpace I J g₁.left
    letI := targetFiberChartedSpace I J g₂.left
    letI := targetFiberChartedSpace I J g₂.right
    letI := targetFiberChartedSpace I J (g₁.comp g₂ hg).left
    letI := targetFiberChartedSpace I J (g₁.comp g₂ hg).right
    (leftMulDiffeomorph I J g₂
      ⟨(leftMulDiffeomorph I J g₁ h).val,
        (leftMulDiffeomorph I J g₁ h).property.trans hg⟩).val =
      (leftMulDiffeomorph I J (g₁.comp g₂ hg)
        ⟨h.val, h.property.trans (g₁.comp_left g₂ hg).symm⟩).val :=
  Quiver.Total.comp_assoc h.val g₁ g₂ h.property hg _ _

/-- **Right translation** by an arrow `g : Quiver.Total C` (`h ↦ g ≫ h`, the geometric right
product `h · g`) is a `C^∞` diffeomorphism from the source fibre `s⁻¹(t(g))` onto `s⁻¹(s(g))`, with
inverse given by right translation by `g⁻¹`. -/
def rightMulDiffeomorph (g : Quiver.Total C) :
    letI := sourceFiberChartedSpace I J g.right
    letI := sourceFiberChartedSpace I J g.left
    {a : Quiver.Total C // a.left = g.right} ≃ₘ^∞⟮
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)⟯
      {a : Quiver.Total C // a.left = g.left} :=
  letI := sourceFiberChartedSpace I J g.right
  letI := sourceFiberChartedSpace I J g.left
  { toFun := fun a ↦ ⟨g.comp a.val a.property.symm, Quiver.Total.comp_left g a.val a.property.symm⟩
    invFun := fun b ↦
      ⟨(⟨g.right, g.left, inv g.hom⟩ : Quiver.Total C).comp b.val b.property.symm,
        Quiver.Total.comp_left (⟨g.right, g.left, inv g.hom⟩ : Quiver.Total C) b.val
          b.property.symm⟩
    left_inv := fun a ↦ Subtype.ext (Quiver.Total.inv_comp_comp g a.val a.property.symm _)
    right_inv := fun b ↦ Subtype.ext (Quiver.Total.comp_inv_comp g b.val b.property.symm _)
    contMDiff_toFun := by
      have := isManifold_sourceFiber I J g.right
      have := isManifold_sourceFiber I J g.left
      exact ((isSmoothEmbedding_coe_sourceFiber I J g.left).contMDiff_iff_comp
        (f := fun a : {a : Quiver.Total C // a.left = g.right} ↦
          (⟨g.comp a.val a.property.symm, Quiver.Total.comp_left g a.val a.property.symm⟩ :
            {a : Quiver.Total C // a.left = g.left}))).2
        (contMDiff_comp_const_left I J g)
    contMDiff_invFun := by
      have := isManifold_sourceFiber I J g.right
      have := isManifold_sourceFiber I J g.left
      exact ((isSmoothEmbedding_coe_sourceFiber I J g.right).contMDiff_iff_comp
        (f := fun b : {a : Quiver.Total C // a.left = g.left} ↦
          (⟨(⟨g.right, g.left, inv g.hom⟩ : Quiver.Total C).comp b.val b.property.symm,
            Quiver.Total.comp_left (⟨g.right, g.left, inv g.hom⟩ : Quiver.Total C) b.val
              b.property.symm⟩ :
            {a : Quiver.Total C // a.left = g.right}))).2
        (contMDiff_comp_const_left I J (⟨g.right, g.left, inv g.hom⟩ : Quiver.Total C)) }

@[simp]
theorem coe_rightMulDiffeomorph_apply (g : Quiver.Total C)
    (a : {a : Quiver.Total C // a.left = g.right}) :
    letI := sourceFiberChartedSpace I J g.right
    letI := sourceFiberChartedSpace I J g.left
    (rightMulDiffeomorph I J g a).val = g.comp a.val a.property.symm :=
  (rfl)

@[simp]
theorem coe_rightMulDiffeomorph_symm_apply (g : Quiver.Total C)
    (b : {a : Quiver.Total C // a.left = g.left}) :
    letI := sourceFiberChartedSpace I J g.right
    letI := sourceFiberChartedSpace I J g.left
    ((rightMulDiffeomorph I J g).symm b).val =
      (⟨g.right, g.left, inv g.hom⟩ : Quiver.Total C).comp b.val b.property.symm :=
  (rfl)

@[simp]
theorem rightMulDiffeomorph_apply_unit (g : Quiver.Total C) :
    letI := sourceFiberChartedSpace I J g.right
    letI := sourceFiberChartedSpace I J g.left
    rightMulDiffeomorph I J g ⟨⟨g.right, g.right, 𝟙 g.right⟩, rfl⟩ = ⟨g, rfl⟩ := by
  let := sourceFiberChartedSpace I J g.right
  let := sourceFiberChartedSpace I J g.left
  exact Subtype.ext g.comp_unit

@[simp]
theorem rightMulDiffeomorph_unit (x : C) :
    letI := sourceFiberChartedSpace I J x
    rightMulDiffeomorph I J (⟨x, x, 𝟙 x⟩ : Quiver.Total C) =
      Diffeomorph.refl 𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ E) → ℝ)
        {a : Quiver.Total C // a.left = x} ∞ := by
  let := sourceFiberChartedSpace I J x
  ext1 ⟨a, ha⟩
  dsimp only at ha
  subst ha
  exact Subtype.ext a.unit_comp

/-- The inverse of right translation by `g` is right translation by `g⁻¹`. -/
theorem rightMulDiffeomorph_symm (g : Quiver.Total C) :
    letI := sourceFiberChartedSpace I J g.right
    letI := sourceFiberChartedSpace I J g.left
    (rightMulDiffeomorph I J g).symm =
      rightMulDiffeomorph I J (⟨g.right, g.left, inv g.hom⟩ : Quiver.Total C) := by
  let := sourceFiberChartedSpace I J g.right
  let := sourceFiberChartedSpace I J g.left
  ext1 b
  rfl

/-- Contravariant functoriality of right translation: right translating by `g : y ⟶ z` and then by
`f : x ⟶ y` equals right translating by `f ≫ g : x ⟶ z`. -/
theorem rightMulDiffeomorph_trans {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    letI := sourceFiberChartedSpace I J z
    letI := sourceFiberChartedSpace I J y
    letI := sourceFiberChartedSpace I J x
    (rightMulDiffeomorph I J (⟨y, z, g⟩ : Quiver.Total C)).trans
      (rightMulDiffeomorph I J (⟨x, y, f⟩ : Quiver.Total C)) =
      rightMulDiffeomorph I J (⟨x, z, f ≫ g⟩ : Quiver.Total C) := by
  let := sourceFiberChartedSpace I J z
  let := sourceFiberChartedSpace I J y
  let := sourceFiberChartedSpace I J x
  refine Diffeomorph.ext fun h ↦ Subtype.ext ?_
  have hbc : ((⟨x, y, f⟩ : Quiver.Total C).comp ⟨y, z, g⟩ rfl).right = h.val.left :=
    ((⟨x, y, f⟩ : Quiver.Total C).comp_right ⟨y, z, g⟩ rfl).trans h.property.symm
  exact (Quiver.Total.comp_assoc ⟨x, y, f⟩ ⟨y, z, g⟩ h.val rfl h.property.symm hbc _).symm.trans
    (Quiver.Total.comp_congr (Quiver.Total.mk_comp_mk f g) rfl hbc h.property.symm)

/-- Pointwise functoriality of right translation along arbitrary composable total arrows. -/
theorem coe_rightMulDiffeomorph_comp_apply {g₁ g₂ : Quiver.Total C} (hg : g₁.right = g₂.left)
    (k : {a : Quiver.Total C // a.left = g₂.right}) :
    letI := sourceFiberChartedSpace I J g₂.right
    letI := sourceFiberChartedSpace I J g₁.right
    letI := sourceFiberChartedSpace I J g₁.left
    letI := sourceFiberChartedSpace I J (g₁.comp g₂ hg).right
    letI := sourceFiberChartedSpace I J (g₁.comp g₂ hg).left
    (rightMulDiffeomorph I J g₁
      ⟨(rightMulDiffeomorph I J g₂ k).val,
        (rightMulDiffeomorph I J g₂ k).property.trans hg.symm⟩).val =
      (rightMulDiffeomorph I J (g₁.comp g₂ hg)
        ⟨k.val, k.property.trans (g₁.comp_right g₂ hg).symm⟩).val :=
  (Quiver.Total.comp_assoc g₁ g₂ k.val hg k.property.symm _ _).symm

/-- Intertwining of right and left fibre translations under `inverseSourceTargetDiffeomorph`:
right translating by `g` and inverting agrees with inverting and left translating by `g⁻¹`. -/
theorem rightMulDiffeomorph_trans_inverseSourceTargetDiffeomorph (g : Quiver.Total C) :
    letI := sourceFiberChartedSpace I J g.right
    letI := sourceFiberChartedSpace I J g.left
    letI := targetFiberChartedSpace I J g.right
    letI := targetFiberChartedSpace I J g.left
    (rightMulDiffeomorph I J g).trans (inverseSourceTargetDiffeomorph I J g.left) =
      (inverseSourceTargetDiffeomorph I J g.right).trans
        (leftMulDiffeomorph I J (⟨g.right, g.left, inv g.hom⟩ : Quiver.Total C)) := by
  let := sourceFiberChartedSpace I J g.right
  let := sourceFiberChartedSpace I J g.left
  let := targetFiberChartedSpace I J g.right
  let := targetFiberChartedSpace I J g.left
  exact Diffeomorph.ext fun h ↦ Subtype.ext (g.inv_comp h.val h.property.symm)

/-- Conjugating `rightMulDiffeomorph I J g` by `inverseSourceTargetDiffeomorph` yields left
translation by `g⁻¹`. -/
theorem inverseSourceTargetDiffeomorph_conj_rightMulDiffeomorph (g : Quiver.Total C) :
    letI := sourceFiberChartedSpace I J g.right
    letI := sourceFiberChartedSpace I J g.left
    letI := targetFiberChartedSpace I J g.right
    letI := targetFiberChartedSpace I J g.left
    ((inverseSourceTargetDiffeomorph I J g.right).symm.trans
      (rightMulDiffeomorph I J g)).trans (inverseSourceTargetDiffeomorph I J g.left) =
      leftMulDiffeomorph I J (⟨g.right, g.left, inv g.hom⟩ : Quiver.Total C) := by
  let := sourceFiberChartedSpace I J g.right
  let := sourceFiberChartedSpace I J g.left
  let := targetFiberChartedSpace I J g.right
  let := targetFiberChartedSpace I J g.left
  refine Diffeomorph.ext fun k ↦ ?_
  have h := congrArg (· ((inverseSourceTargetDiffeomorph I J g.right).symm k))
    (rightMulDiffeomorph_trans_inverseSourceTargetDiffeomorph I J g)
  simpa only [Diffeomorph.coe_trans, Function.comp_apply, Diffeomorph.apply_symm_apply] using h

/-- Conjugating `leftMulDiffeomorph I J g` by `inverseSourceTargetDiffeomorph` yields right
translation by `g⁻¹`. -/
theorem inverseSourceTargetDiffeomorph_conj_leftMulDiffeomorph (g : Quiver.Total C) :
    letI := sourceFiberChartedSpace I J g.left
    letI := sourceFiberChartedSpace I J g.right
    letI := targetFiberChartedSpace I J g.left
    letI := targetFiberChartedSpace I J g.right
    ((inverseSourceTargetDiffeomorph I J g.left).trans
      (leftMulDiffeomorph I J g)).trans
      (inverseSourceTargetDiffeomorph I J g.right).symm =
      rightMulDiffeomorph I J (⟨g.right, g.left, inv g.hom⟩ : Quiver.Total C) := by
  let := sourceFiberChartedSpace I J g.left
  let := sourceFiberChartedSpace I J g.right
  let := targetFiberChartedSpace I J g.left
  let := targetFiberChartedSpace I J g.right
  refine Diffeomorph.ext fun h ↦ ?_
  obtain ⟨x, y, f⟩ := g
  have hinv := rightMulDiffeomorph_trans_inverseSourceTargetDiffeomorph I J
    (⟨y, x, inv f⟩ : Quiver.Total C)
  dsimp only at hinv
  rw [IsIso.inv_inv] at hinv
  have h' := congrArg (fun e ↦ (inverseSourceTargetDiffeomorph I J y).symm (e h)) hinv
  simpa only [Diffeomorph.coe_trans, Function.comp_apply, Diffeomorph.symm_apply_apply] using
    h'.symm

end IsLieGroupoid

end TauCeti
