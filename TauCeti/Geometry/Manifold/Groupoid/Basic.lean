/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.FiberProduct.Submersion
public import TauCeti.Topology.CategoryTheory.Groupoid.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import TauCeti.Geometry.Manifold.SmoothEmbedding.LeftInverse
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph

/-!
# Lie groupoids

`TauCeti.IsLieGroupoid I J C` equips a categorical groupoid `C`, carrying finite-dimensional
boundaryless smooth manifold structures on its object type `C` (modelled on `I`) and its total-arrow
type `Quiver.Total C` (modelled on `J`), with smooth groupoid structure maps:

* the object manifold `C` is Hausdorff (`t2Space_objects`), while the arrow manifold
  `Quiver.Total C` is second-countable (`secondCountableTopology_arrows`) and need not be globally
  Hausdorff;
* the source map `Quiver.Total.left : Quiver.Total C → C` is a smooth submersion
  (`isSubmersion_source`);
* the unit section `x ↦ ⟨x, x, 𝟙 x⟩` and inversion `a ↦ ⟨a.right, a.left, inv a.hom⟩` are smooth
  (`contMDiff_unit`, `contMDiff_inverse`);
* composition is smooth (`contMDiff_comp`) on the composable-pair subtype
  `{p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left}` equipped with its transverse
  fibre-product manifold structure `TauCeti.transverseFiberProductChartedSpace`;
* every source fibre `{a : Quiver.Total C // a.left = x}` is Hausdorff in the subspace topology
  (`t2Space_sourceFiber`).

Allowing non-Hausdorff total-arrow manifolds with Hausdorff object manifolds and Hausdorff source
fibres accommodates holonomy and monodromy groupoids of foliations while retaining unique manifold
structures on fibres and second-countability of `C`
(`IsLieGroupoid.secondCountableTopology_objects`).

From these axioms this file derives:

* inversion is an involutive diffeomorphism (`IsLieGroupoid.inverseDiffeomorph`), so the target map
  `Quiver.Total.right` is also a smooth submersion (`IsLieGroupoid.isSubmersion_target`), both
  source and target are open maps (`IsLieGroupoid.isOpenMap_source`,
  `IsLieGroupoid.isOpenMap_target`), and forgetting smoothness yields a topological groupoid
  (`IsLieGroupoid.isTopologicalGroupoid`);
* the unit map is a smooth embedding (`IsLieGroupoid.isSmoothEmbedding_unit`), forcing `C` to be
  second-countable (`IsLieGroupoid.secondCountableTopology_objects`) and bounding the base
  dimension by the arrow dimension when `C` is nonempty (`IsLieGroupoid.finrank_le_finrank`);
* étale characterization: on a nonempty base, the source map is a local diffeomorphism if and only
  if arrow and object models have equal dimension
  (`IsLieGroupoid.isLocalDiffeomorph_source_iff_finrank_eq`), and source is a local diffeomorphism
  if and only if target is (`IsLieGroupoid.isLocalDiffeomorph_source_iff_target`);
* the left-shear diffeomorphism (`IsLieGroupoid.shearLeftDiffeomorph`) from composable pairs to
  same-source pairs `{q : Quiver.Total C × Quiver.Total C // q.1.left = q.2.left}`, from which
  groupoid composition is a smooth submersion (`IsLieGroupoid.isSubmersion_comp`);
* the differential of composition and inversion along the unit section
  (`IsLieGroupoid.mfderiv_comp_unit`, `IsLieGroupoid.mfderiv_inverse_unit`), specializing on the
  source-vertical tangent kernel to `d(inv)_{1_x}(v) = d1_x(dt(v)) - v`
  (`IsLieGroupoid.mfderiv_inverse_unit_of_mem_ker_source`).

## Main definitions

* `TauCeti.IsLieGroupoid`: smooth Lie groupoid predicate on `C` and `Quiver.Total C`.
* `TauCeti.IsLieGroupoid.inverseDiffeomorph`: groupoid inversion as a `C^∞` diffeomorphism.
* `TauCeti.IsLieGroupoid.composablePairsChartedSpace`: transverse fibre-product manifold atlas on
  composable pairs.
* `TauCeti.IsLieGroupoid.sameSourcePairsChartedSpace`: transverse fibre-product manifold atlas on
  pairs of arrows with equal source.
* `TauCeti.IsLieGroupoid.shearLeftDiffeomorph`: left-division diffeomorphism `(a, b) ↦ (a, a ≫ b)`
  from composable pairs onto same-source pairs.

## References

* K. C. H. Mackenzie, *General Theory of Lie Groupoids and Lie Algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), Section 1.1.
* I. Moerdijk and J. Mrčun, *Introduction to Foliations and Lie Groupoids*, Cambridge Stud. Adv.
  Math. 91, Cambridge University Press (2003), Section 5.1.
* M. Crainic and R. L. Fernandes, *Lectures on integrability of Lie brackets*, Geom. Topol.
  Monogr. 17 (2011), Definition 1.1.
-/

public section

noncomputable section

open CategoryTheory Function Module Topology
open scoped Manifold ContDiff

namespace TauCeti

/-- A **Lie groupoid** on a categorical groupoid `C`, equipped with finite-dimensional boundaryless
smooth manifold structures on objects `C` (model `I`) and total arrows `Quiver.Total C` (model `J`):
`C` is Hausdorff, `Quiver.Total C` is second-countable, the source projection is a smooth
submersion, units and inversion are smooth, composition is smooth on the transverse fibre product of
target and source, and every source fibre is Hausdorff. -/
class IsLieGroupoid {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H') [J.Boundaryless]
    (C : Type*) [Category C] [IsGroupoid C]
    [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C]
    [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
    [IsManifold J ∞ (Quiver.Total C)] : Prop where
  /-- The object manifold is Hausdorff. -/
  t2Space_objects : T2Space C := by infer_instance
  /-- The total-arrow manifold is second-countable. -/
  secondCountableTopology_arrows : SecondCountableTopology (Quiver.Total C) := by infer_instance
  /-- The source projection `a ↦ a.left` is a smooth submersion. -/
  isSubmersion_source : Manifold.IsSubmersion J I ∞ (Quiver.Total.left : Quiver.Total C → C)
  /-- The unit section `x ↦ ⟨x, x, 𝟙 x⟩` is smooth. -/
  contMDiff_unit : ContMDiff I J ∞ fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C)
  /-- Groupoid inversion `a ↦ ⟨a.right, a.left, inv a.hom⟩` is smooth. -/
  contMDiff_inverse : ContMDiff J J ∞ fun a : Quiver.Total C ↦
    (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total C)
  /-- Groupoid composition is smooth on the transverse fibre product of target and source. -/
  contMDiff_comp :
    letI := transverseFiberProductChartedSpace
      (f := (Quiver.Total.right : Quiver.Total C → C))
      (g := (Quiver.Total.left : Quiver.Total C → C)) (n := ∞) (by simp)
      (isSubmersion_source.contMDiff.comp contMDiff_inverse)
      isSubmersion_source.contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_right (Quiver.Total.right : Quiver.Total C → C)
        isSubmersion_source (by simp) p)
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
        p.1.1.comp p.1.2 p.2
  /-- Every source fibre is Hausdorff in the subspace topology. -/
  t2Space_sourceFiber (x : C) : T2Space {a : Quiver.Total C // a.left = x} := by infer_instance

namespace IsLieGroupoid

variable {E H E' H' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
  (J : ModelWithCorners ℝ E' H') [J.Boundaryless]
  (C : Type*) [Category C] [IsGroupoid C]
  [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
  [IsManifold J ∞ (Quiver.Total C)]
  [IsLieGroupoid I J C]

/-! ### Basic smoothness, inversion diffeomorphism, and topological consequences -/

/-- The source projection of a Lie groupoid is smooth. -/
theorem contMDiff_source : ContMDiff J I ∞ (Quiver.Total.left : Quiver.Total C → C) :=
  (isSubmersion_source (I := I) (J := J) (C := C)).contMDiff

include I in
/-- Groupoid inversion is an involutive `C^∞` diffeomorphism of the total-arrow manifold. -/
def inverseDiffeomorph : Quiver.Total C ≃ₘ^∞⟮J, J⟯ Quiver.Total C where
  toFun a := ⟨a.right, a.left, inv a.hom⟩
  invFun a := ⟨a.right, a.left, inv a.hom⟩
  left_inv a := by cases a; simp
  right_inv a := by cases a; simp
  contMDiff_toFun := contMDiff_inverse (I := I) (J := J) (C := C)
  contMDiff_invFun := contMDiff_inverse (I := I) (J := J) (C := C)

@[simp]
theorem inverseDiffeomorph_apply (a : Quiver.Total C) :
    inverseDiffeomorph I J C a = ⟨a.right, a.left, inv a.hom⟩ :=
  (rfl)

@[simp]
theorem inverseDiffeomorph_symm :
    (inverseDiffeomorph I J C).symm = inverseDiffeomorph I J C :=
  (rfl)

/-- The target projection of a Lie groupoid is smooth. -/
theorem contMDiff_target : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C) :=
  (contMDiff_source I J C).comp (contMDiff_inverse (I := I) (J := J) (C := C))

/-- The target projection of a Lie groupoid is a smooth submersion, since it is the source
projection precomposed with the inversion diffeomorphism. -/
theorem isSubmersion_target :
    Manifold.IsSubmersion J I ∞ (Quiver.Total.right : Quiver.Total C → C) := by
  refine ((contMDiff_target I J C).isSubmersionOfComplement_of_surjective_mfderiv (by simp)
    fun a ↦ ?_).isSubmersion
  exact (((inverseDiffeomorph I J C).isLocalDiffeomorph a).isSubmersionAt_comp_iff.2
    ((isSubmersion_source (I := I) (J := J) (C := C)).isSubmersionAt
      (inverseDiffeomorph I J C a))).surjective_mfderiv (by simp)

include I J in
/-- The source projection of a Lie groupoid is an open map. -/
theorem isOpenMap_source : IsOpenMap (Quiver.Total.left : Quiver.Total C → C) :=
  (isSubmersion_source (I := I) (J := J) (C := C)).isOpenMap

include I J in
/-- The target projection of a Lie groupoid is an open map. -/
theorem isOpenMap_target : IsOpenMap (Quiver.Total.right : Quiver.Total C → C) :=
  (isSubmersion_target I J C).isOpenMap

/-- The unit map `x ↦ ⟨x, x, 𝟙 x⟩` is a smooth embedding of the object manifold into the arrow
manifold, because the source projection is a smooth left inverse. -/
theorem isSmoothEmbedding_unit :
    Manifold.IsSmoothEmbedding I J ∞ (fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C)) :=
  (contMDiff_unit (I := I) (J := J) (C := C)).isSmoothEmbedding_of_leftInverse (by simp)
    ((contMDiff_source I J C).of_le (by simp)) fun _ ↦ rfl

include I J in
/-- The object manifold of a Lie groupoid is second-countable, since the unit map embeds it into
the second-countable total-arrow manifold. -/
theorem secondCountableTopology_objects : SecondCountableTopology C :=
  have := secondCountableTopology_arrows (I := I) (J := J) (C := C)
  (isSmoothEmbedding_unit I J C).isEmbedding.secondCountableTopology

include I J in
/-- Every Lie groupoid is a topological groupoid when its smooth structure is forgotten. This is a
theorem rather than an instance because `I` and `J` do not appear in `IsTopologicalGroupoid C`. -/
theorem isTopologicalGroupoid : IsTopologicalGroupoid C where
  continuous_source := (contMDiff_source I J C).continuous
  continuous_target := (contMDiff_target I J C).continuous
  continuous_unit := (contMDiff_unit (I := I) (J := J) (C := C)).continuous
  continuous_inverse := (contMDiff_inverse (I := I) (J := J) (C := C)).continuous
  continuous_comp := by
    let := transverseFiberProductChartedSpace (n := ∞) (by simp)
      (contMDiff_target I J C) (contMDiff_source I J C)
      (fun p _ ↦ transverse_of_isSubmersion_right (Quiver.Total.right : Quiver.Total C → C)
        (isSubmersion_source (I := I) (J := J) (C := C)) (by simp) p)
    exact (contMDiff_comp (I := I) (J := J) (C := C)).continuous

/-! ### Dimension bound and étale characterization -/

include I J C in
/-- On a nonempty object manifold, the dimension of the object model is at most the dimension of
the arrow model. -/
theorem finrank_le_finrank [Nonempty C] : finrank ℝ E ≤ finrank ℝ E' := by
  obtain ⟨x⟩ := ‹Nonempty C›
  have hsurj := (isSubmersion_source (I := I) (J := J) (C := C)).surjective_mfderiv
    (by simp) ⟨x, x, 𝟙 x⟩
  exact LinearMap.finrank_le_finrank_of_surjective hsurj

/-- If the arrow and object models have the same dimension, the source projection is a local
diffeomorphism (an étale Lie groupoid). -/
theorem isLocalDiffeomorph_source_of_finrank_eq (h : finrank ℝ E' = finrank ℝ E) :
    IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C) := by
  intro a
  have hsurj := (isSubmersion_source (I := I) (J := J) (C := C)).surjective_mfderiv (by simp) a
  have hinj : Injective (mfderiv J I (Quiver.Total.left : Quiver.Total C → C) a) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (mfderiv J I (Quiver.Total.left : Quiver.Total C → C) a).toLinearMap) h).2 hsurj
  exact isLocalDiffeomorphAt_of_injective_mfderiv (contMDiff_source I J C).contMDiffOn
    isOpen_univ (Set.mem_univ a) BoundarylessManifold.isInteriorPoint (by simp) hinj h

/-- On a nonempty object manifold, the source projection is a local diffeomorphism if and only if
the arrow and object models have equal dimension. -/
theorem isLocalDiffeomorph_source_iff_finrank_eq [Nonempty C] :
    IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C) ↔
      finrank ℝ E' = finrank ℝ E := by
  refine ⟨fun h ↦ ?_, isLocalDiffeomorph_source_of_finrank_eq I J C⟩
  obtain ⟨x⟩ := ‹Nonempty C›
  exact ((h ⟨x, x, 𝟙 x⟩).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv.finrank_eq

/-- The source projection is a local diffeomorphism if and only if the target projection is, since
groupoid inversion is a diffeomorphism exchanging them. -/
theorem isLocalDiffeomorph_source_iff_target :
    IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C) ↔
      IsLocalDiffeomorph J I ∞ (Quiver.Total.right : Quiver.Total C → C) := by
  constructor <;> intro h a
  · exact ((inverseDiffeomorph I J C).isLocalDiffeomorph a).comp I C
      (h (inverseDiffeomorph I J C a))
  · exact ((inverseDiffeomorph I J C).isLocalDiffeomorph a).comp I C
      (h (inverseDiffeomorph I J C a))

/-! ### Composable pairs, same-source pairs, left shear, and submersion property of composition -/

/-- The smooth manifold atlas on composable pairs `{p : Quiver.Total C × Quiver.Total C //
p.1.right = p.2.left}` of a Lie groupoid, constructed as the transverse fibre product of target
and source. -/
@[expose, instance_reducible]
def composablePairsChartedSpace :
    ChartedSpace (Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
      {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} :=
  transverseFiberProductChartedSpace (n := ∞) (by simp)
    (contMDiff_target I J C) (contMDiff_source I J C)
    (fun p _ ↦ transverse_of_isSubmersion_right (Quiver.Total.right : Quiver.Total C → C)
      (isSubmersion_source (I := I) (J := J) (C := C)) (by simp) p)

/-- Groupoid composition is smooth with respect to `composablePairsChartedSpace`. -/
theorem contMDiff_comp_composablePairs :
    letI := composablePairsChartedSpace I J C
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
        p.1.1.comp p.1.2 p.2) :=
  contMDiff_comp (I := I) (J := J) (C := C)

/-- Composable pairs of a Lie groupoid form a smooth manifold of dimension
`2 * dim(arrows) - dim(objects)`. -/
theorem isManifold_composablePairs :
    letI := composablePairsChartedSpace I J C
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} :=
  isManifold_transverseFiberProduct (n := ∞) (by simp)
    (contMDiff_target I J C) (contMDiff_source I J C)
    (fun p _ ↦ transverse_of_isSubmersion_right (Quiver.Total.right : Quiver.Total C → C)
      (isSubmersion_source (I := I) (J := J) (C := C)) (by simp) p)

/-- The inclusion of composable pairs into `Quiver.Total C × Quiver.Total C` is a smooth
embedding. -/
theorem isSmoothEmbedding_coe_composablePairs :
    letI := composablePairsChartedSpace I J C
    Manifold.IsSmoothEmbedding
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) (J.prod J) ∞
      (Subtype.val :
        {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} →
          Quiver.Total C × Quiver.Total C) :=
  isSmoothEmbedding_coe_transverseFiberProduct (n := ∞) (by simp)
    (contMDiff_target I J C) (contMDiff_source I J C)
    (fun p _ ↦ transverse_of_isSubmersion_right (Quiver.Total.right : Quiver.Total C → C)
      (isSubmersion_source (I := I) (J := J) (C := C)) (by simp) p)

/-- The first projection from composable pairs is a smooth submersion. -/
theorem isSubmersion_fst_composablePairs :
    letI := composablePairsChartedSpace I J C
    Manifold.IsSubmersion
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦ p.1.1) :=
  isSubmersion_fst_transverseFiberProduct (n := ∞) (by simp)
    (contMDiff_target I J C) (contMDiff_source I J C)
    (fun p _ ↦ transverse_of_isSubmersion_right (Quiver.Total.right : Quiver.Total C → C)
      (isSubmersion_source (I := I) (J := J) (C := C)) (by simp) p)
    (isSubmersion_source (I := I) (J := J) (C := C))

/-- The second projection from composable pairs is a smooth submersion. -/
theorem isSubmersion_snd_composablePairs :
    letI := composablePairsChartedSpace I J C
    Manifold.IsSubmersion
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦ p.1.2) :=
  isSubmersion_snd_transverseFiberProduct (n := ∞) (by simp)
    (contMDiff_target I J C) (contMDiff_source I J C)
    (fun p _ ↦ transverse_of_isSubmersion_right (Quiver.Total.right : Quiver.Total C → C)
      (isSubmersion_source (I := I) (J := J) (C := C)) (by simp) p)
    (isSubmersion_target I J C)

/-- The smooth manifold atlas on pairs of arrows `{p : Quiver.Total C × Quiver.Total C //
p.1.left = p.2.left}` sharing a source, constructed as the self-fibre-product of source. -/
@[expose, instance_reducible]
def sameSourcePairsChartedSpace :
    ChartedSpace (Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
      {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.left} :=
  transverseFiberProductChartedSpace (n := ∞) (by simp)
    (contMDiff_source I J C) (contMDiff_source I J C)
    (fun p _ ↦ transverse_of_isSubmersion_right (Quiver.Total.left : Quiver.Total C → C)
      (isSubmersion_source (I := I) (J := J) (C := C)) (by simp) p)

/-- Pairs of arrows with equal source form a smooth manifold. -/
theorem isManifold_sameSourcePairs :
    letI := sameSourcePairsChartedSpace I J C
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.left} :=
  isManifold_transverseFiberProduct (n := ∞) (by simp)
    (contMDiff_source I J C) (contMDiff_source I J C)
    (fun p _ ↦ transverse_of_isSubmersion_right (Quiver.Total.left : Quiver.Total C → C)
      (isSubmersion_source (I := I) (J := J) (C := C)) (by simp) p)

/-- The inclusion of same-source arrow pairs into `Quiver.Total C × Quiver.Total C` is a smooth
embedding. -/
theorem isSmoothEmbedding_coe_sameSourcePairs :
    letI := sameSourcePairsChartedSpace I J C
    Manifold.IsSmoothEmbedding
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) (J.prod J) ∞
      (Subtype.val :
        {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.left} →
          Quiver.Total C × Quiver.Total C) :=
  isSmoothEmbedding_coe_transverseFiberProduct (n := ∞) (by simp)
    (contMDiff_source I J C) (contMDiff_source I J C)
    (fun p _ ↦ transverse_of_isSubmersion_right (Quiver.Total.left : Quiver.Total C → C)
      (isSubmersion_source (I := I) (J := J) (C := C)) (by simp) p)

/-- The second projection from same-source arrow pairs is a smooth submersion. -/
theorem isSubmersion_snd_sameSourcePairs :
    letI := sameSourcePairsChartedSpace I J C
    Manifold.IsSubmersion
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (fun p : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.left} ↦ p.1.2) :=
  isSubmersion_snd_transverseFiberProduct (n := ∞) (by simp)
    (contMDiff_source I J C) (contMDiff_source I J C)
    (fun p _ ↦ transverse_of_isSubmersion_right (Quiver.Total.left : Quiver.Total C → C)
      (isSubmersion_source (I := I) (J := J) (C := C)) (by simp) p)
    (isSubmersion_source (I := I) (J := J) (C := C))

/-- The **left-shear diffeomorphism** `(a, b) ↦ (a, a ≫ b)` from composable pairs onto pairs of
arrows with equal source, with smooth inverse `(a, c) ↦ (a, a⁻¹ ≫ c)`. -/
def shearLeftDiffeomorph :
    letI := composablePairsChartedSpace I J C
    letI := sameSourcePairsChartedSpace I J C
    {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ≃ₘ^∞⟮
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)⟯
      {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.left} :=
  letI := composablePairsChartedSpace I J C
  letI := sameSourcePairsChartedSpace I J C
  { toFun := fun p ↦ ⟨(p.1.1, p.1.1.comp p.1.2 p.2), (Quiver.Total.comp_left p.1.1 p.1.2 p.2).symm⟩
    invFun := fun q ↦
      ⟨(q.1.1, (⟨q.1.1.right, q.1.1.left, inv q.1.1.hom⟩ : Quiver.Total C).comp q.1.2 q.2),
        (Quiver.Total.comp_left
          (⟨q.1.1.right, q.1.1.left, inv q.1.1.hom⟩ : Quiver.Total C) q.1.2 q.2).symm⟩
    left_inv := fun p ↦ Subtype.ext (Prod.ext rfl (Quiver.Total.inv_comp_comp p.1.1 p.1.2 p.2 _))
    right_inv := fun q ↦ Subtype.ext (Prod.ext rfl (Quiver.Total.comp_inv_comp q.1.1 q.1.2 q.2 _))
    contMDiff_toFun := by
      have := isManifold_composablePairs I J C
      have := isManifold_sameSourcePairs I J C
      exact ((isSmoothEmbedding_coe_sameSourcePairs I J C).contMDiff_iff_comp
        (f := fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
          (⟨(p.1.1, p.1.1.comp p.1.2 p.2), (Quiver.Total.comp_left p.1.1 p.1.2 p.2).symm⟩ :
            {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.left}))).2
        ((isSmoothEmbedding_coe_composablePairs I J C).contMDiff.fst.prodMk
          (contMDiff_comp (I := I) (J := J) (C := C)))
    contMDiff_invFun := by
      have := isManifold_composablePairs I J C
      have := isManifold_sameSourcePairs I J C
      have hemb₁ := isSmoothEmbedding_coe_composablePairs I J C
      have hemb₂ := isSmoothEmbedding_coe_sameSourcePairs I J C
      let divMap :
          {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.left} →
            {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} :=
        fun q ↦ ⟨(⟨q.1.1.right, q.1.1.left, inv q.1.1.hom⟩, q.1.2), q.2⟩
      have hdiv : ContMDiff
          𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
          𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞ divMap :=
        (hemb₁.contMDiff_iff_comp (f := divMap)).2
          (((contMDiff_inverse (I := I) (J := J) (C := C)).comp hemb₂.contMDiff.fst).prodMk
            hemb₂.contMDiff.snd)
      exact (hemb₁.contMDiff_iff_comp
        (f := fun q : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.left} ↦
          (⟨(q.1.1, (⟨q.1.1.right, q.1.1.left, inv q.1.1.hom⟩ : Quiver.Total C).comp q.1.2 q.2),
            (Quiver.Total.comp_left
              (⟨q.1.1.right, q.1.1.left, inv q.1.1.hom⟩ : Quiver.Total C) q.1.2 q.2).symm⟩ :
            {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left}))).2
        (hemb₂.contMDiff.fst.prodMk ((contMDiff_comp (I := I) (J := J) (C := C)).comp hdiv)) }

@[simp]
theorem shearLeftDiffeomorph_apply
    (p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left}) :
    letI := composablePairsChartedSpace I J C
    letI := sameSourcePairsChartedSpace I J C
    shearLeftDiffeomorph I J C p =
      ⟨(p.1.1, p.1.1.comp p.1.2 p.2), (Quiver.Total.comp_left p.1.1 p.1.2 p.2).symm⟩ :=
  (rfl)

/-- Groupoid composition on composable pairs is a smooth submersion: it factors as the left-shear
diffeomorphism followed by the second projection from same-source pairs. -/
theorem isSubmersion_comp :
    letI := composablePairsChartedSpace I J C
    Manifold.IsSubmersion
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
        p.1.1.comp p.1.2 p.2) := by
  let := composablePairsChartedSpace I J C
  let := sameSourcePairsChartedSpace I J C
  have := isManifold_composablePairs I J C
  have := isManifold_sameSourcePairs I J C
  refine ((contMDiff_comp (I := I) (J := J) (C := C)).isSubmersionOfComplement_of_surjective_mfderiv
    (by simp) fun p ↦ ?_).isSubmersion
  exact (((shearLeftDiffeomorph I J C).isLocalDiffeomorph p).isSubmersionAt_comp_iff.2
    ((isSubmersion_snd_sameSourcePairs I J C).isSubmersionAt
      (shearLeftDiffeomorph I J C p))).surjective_mfderiv (by simp)

/-! ### Differentials of unit, composition, and inversion along the identity section -/

section UnitDifferentials

variable {C}

/-- The differential of the source projection splits the differential of the unit section. -/
@[simp]
theorem mfderiv_source_mfderiv_unit (x : C) (v : TangentSpace I x) :
    mfderiv J I (Quiver.Total.left : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩
      (mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x v) = v := by
  have hs := ((contMDiff_source I J C) ⟨x, x, 𝟙 x⟩).mdifferentiableAt (by simp)
  have hu := ((contMDiff_unit (I := I) (J := J) (C := C)) x).mdifferentiableAt (by simp)
  have hcomp := DFunLike.congr_fun (mfderiv_comp x hs hu) v
  have hid : (Quiver.Total.left : Quiver.Total C → C) ∘
      (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) = id := rfl
  rw [hid, mfderiv_id, ContinuousLinearMap.id_apply] at hcomp
  exact hcomp.symm

/-- The differential of the target projection splits the differential of the unit section. -/
@[simp]
theorem mfderiv_target_mfderiv_unit (x : C) (v : TangentSpace I x) :
    mfderiv J I (Quiver.Total.right : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩
      (mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x v) = v := by
  have ht := ((contMDiff_target I J C) ⟨x, x, 𝟙 x⟩).mdifferentiableAt (by simp)
  have hu := ((contMDiff_unit (I := I) (J := J) (C := C)) x).mdifferentiableAt (by simp)
  have hcomp := DFunLike.congr_fun (mfderiv_comp x ht hu) v
  have hid : (Quiver.Total.right : Quiver.Total C → C) ∘
      (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) = id := rfl
  rw [hid, mfderiv_id, ContinuousLinearMap.id_apply] at hcomp
  exact hcomp.symm

/-- The three canonical sections `a ↦ (a, 1_{t(a)})`, `b ↦ (1_{s(b)}, b)`, and `y ↦ (1_y, 1_y)`
into composable pairs are differentiable at identity arrows. -/
private theorem mdifferentiableAt_composablePairs_sections (x : C) :
    letI := composablePairsChartedSpace I J C
    let K := 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
    MDifferentiableAt J K
        (fun a : Quiver.Total C ↦ (⟨(a, ⟨a.right, a.right, 𝟙 a.right⟩), rfl⟩ :
          {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left})) ⟨x, x, 𝟙 x⟩ ∧
      MDifferentiableAt J K
        (fun b : Quiver.Total C ↦ (⟨(⟨b.left, b.left, 𝟙 b.left⟩, b), rfl⟩ :
          {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left})) ⟨x, x, 𝟙 x⟩ ∧
      MDifferentiableAt I K
        (fun y : C ↦ (⟨(⟨y, y, 𝟙 y⟩, ⟨y, y, 𝟙 y⟩), rfl⟩ :
          {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left})) x := by
  let := composablePairsChartedSpace I J C
  have := isManifold_composablePairs I J C
  have hemb := isSmoothEmbedding_coe_composablePairs I J C
  have hu := contMDiff_unit (I := I) (J := J) (C := C)
  exact ⟨(((hemb.contMDiff_iff_comp).2
      (contMDiff_id.prodMk (hu.comp (contMDiff_target I J C)))) _).mdifferentiableAt (by simp),
    (((hemb.contMDiff_iff_comp).2
      ((hu.comp (contMDiff_source I J C)).prodMk contMDiff_id)) _).mdifferentiableAt (by simp),
    (((hemb.contMDiff_iff_comp).2 (hu.prodMk hu)) _).mdifferentiableAt (by simp)⟩

/-- Every tangent vector to composable pairs at `(1_x, 1_x)` decomposes along the sections
`a ↦ (a, 1_{t(a)})`, `b ↦ (1_{s(b)}, b)`, and `y ↦ (1_y, 1_y)`. -/
private theorem eq_linear_comb_mfderiv_composablePairs_unit (x : C) :
    letI := composablePairsChartedSpace I J C
    ∀ ξ : TangentSpace 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
        (⟨(⟨x, x, 𝟙 x⟩, ⟨x, x, 𝟙 x⟩), rfl⟩ :
          {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left}),
      ξ =
        mfderiv J 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
            (fun a : Quiver.Total C ↦ (⟨(a, ⟨a.right, a.right, 𝟙 a.right⟩), rfl⟩ :
              {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left})) ⟨x, x, 𝟙 x⟩
            (mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
              (fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦ p.1.1)
              ⟨(⟨x, x, 𝟙 x⟩, ⟨x, x, 𝟙 x⟩), rfl⟩ ξ) +
          mfderiv J 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
            (fun b : Quiver.Total C ↦ (⟨(⟨b.left, b.left, 𝟙 b.left⟩, b), rfl⟩ :
              {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left})) ⟨x, x, 𝟙 x⟩
            (mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
              (fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦ p.1.2)
              ⟨(⟨x, x, 𝟙 x⟩, ⟨x, x, 𝟙 x⟩), rfl⟩ ξ) -
          mfderiv I 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
            (fun y : C ↦ (⟨(⟨y, y, 𝟙 y⟩, ⟨y, y, 𝟙 y⟩), rfl⟩ :
              {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left})) x
            (mfderiv J I (Quiver.Total.right : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩
              (mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
                (fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦ p.1.1)
                ⟨(⟨x, x, 𝟙 x⟩, ⟨x, x, 𝟙 x⟩), rfl⟩ ξ)) := by
  let := composablePairsChartedSpace I J C
  have := isManifold_composablePairs I J C
  have hemb := isSmoothEmbedding_coe_composablePairs I J C
  let K := 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
  let e : Quiver.Total C := ⟨x, x, 𝟙 x⟩
  let p₀ : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} := ⟨(e, e), rfl⟩
  rcases mdifferentiableAt_composablePairs_sections I J x with ⟨hρ, hlam, hδ⟩
  have hfst := (hemb.contMDiff.fst p₀).mdifferentiableAt (by simp)
  have hsnd := (hemb.contMDiff.snd p₀).mdifferentiableAt (by simp)
  have hu := ((contMDiff_unit (I := I) (J := J) (C := C)) x).mdifferentiableAt (by simp)
  have hs := ((contMDiff_source I J C) e).mdifferentiableAt (by simp)
  have ht := ((contMDiff_target I J C) e).mdifferentiableAt (by simp)
  intro ξ
  set u := mfderiv K J (fun p ↦ p.1.1) p₀ ξ
  set w := mfderiv K J (fun p ↦ p.1.2) p₀ ξ
  have hts : (Quiver.Total.right : Quiver.Total C → C) ∘
      (fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦ p.1.1) =
      (Quiver.Total.left : Quiver.Total C → C) ∘ (fun p ↦ p.1.2) := funext fun p ↦ p.2
  have huw : mfderiv J I (Quiver.Total.right : Quiver.Total C → C) e u =
      mfderiv J I (Quiver.Total.left : Quiver.Total C → C) e w :=
    DFunLike.congr_fun ((mfderiv_comp p₀ ht hfst).symm.trans
      ((mfderiv_congr (I := K) (I' := I) (x := p₀) hts).trans (mfderiv_comp p₀ hs hsnd))) ξ
  rw [← sub_eq_zero]
  refine eq_zero_of_mfderiv_transverseFiberProduct (n := ∞) (by simp)
    (contMDiff_target I J C) (contMDiff_source I J C)
    (fun p _ ↦ transverse_of_isSubmersion_right _
      (isSubmersion_source (I := I) (J := J) (C := C)) (by simp) p) p₀ _
    ?_ ?_
  · have h1 : u = _ := (DFunLike.congr_fun (mfderiv_id (I := J) (x := e)) u).symm.trans
      (DFunLike.congr_fun (mfderiv_comp e hfst hρ) u)
    have h2 := (DFunLike.congr_fun (mfderiv_comp e hu hs) w).symm.trans
      (DFunLike.congr_fun (mfderiv_comp e hfst hlam) w)
    have h4 := DFunLike.congr_fun (mfderiv_comp x hfst hδ)
      (mfderiv J I (Quiver.Total.right : Quiver.Total C → C) e u)
    simp only [Function.comp_def, ContinuousLinearMap.comp_apply] at h1 h2 h4
    rw [map_sub, map_sub, map_add, ← h1, ← h2, ← h4, huw]; dsimp only [u, e]; abel
  · have h1 := (DFunLike.congr_fun (mfderiv_comp e hu ht) u).symm.trans
      (DFunLike.congr_fun (mfderiv_comp e hsnd hρ) u)
    have h3 : w = _ := (DFunLike.congr_fun (mfderiv_id (I := J) (x := e)) w).symm.trans
      (DFunLike.congr_fun (mfderiv_comp e hsnd hlam) w)
    have h4 := DFunLike.congr_fun (mfderiv_comp x hsnd hδ)
      (mfderiv J I (Quiver.Total.right : Quiver.Total C → C) e u)
    simp only [Function.comp_def, ContinuousLinearMap.comp_apply] at h1 h3 h4
    rw [map_sub, map_sub, map_add, ← h1, ← h3, ← h4]; dsimp only [w, e]; abel

/-- At a unit composable pair `(1_x, 1_x)`, the differential of composition sends a tangent vector
`ξ` with projections `(u, w)` (satisfying `dt(u) = ds(w)`) to `u + w - d1_x(dt(u))`. -/
theorem mfderiv_comp_unit (x : C) :
    letI := composablePairsChartedSpace I J C
    ∀ ξ : TangentSpace 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
        (⟨(⟨x, x, 𝟙 x⟩, ⟨x, x, 𝟙 x⟩), rfl⟩ :
          {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left}),
      mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
        (fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
          p.1.1.comp p.1.2 p.2)
        ⟨(⟨x, x, 𝟙 x⟩, ⟨x, x, 𝟙 x⟩), rfl⟩ ξ =
      mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
          (fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦ p.1.1)
          ⟨(⟨x, x, 𝟙 x⟩, ⟨x, x, 𝟙 x⟩), rfl⟩ ξ +
        mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
          (fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦ p.1.2)
          ⟨(⟨x, x, 𝟙 x⟩, ⟨x, x, 𝟙 x⟩), rfl⟩ ξ -
        mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x
          (mfderiv J I (Quiver.Total.right : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩
            (mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
              (fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦ p.1.1)
              ⟨(⟨x, x, 𝟙 x⟩, ⟨x, x, 𝟙 x⟩), rfl⟩ ξ)) := by
  let := composablePairsChartedSpace I J C
  have := isManifold_composablePairs I J C
  let K := 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
  let e : Quiver.Total C := ⟨x, x, 𝟙 x⟩
  let p₀ : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} := ⟨(e, e), rfl⟩
  let mMap : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} → Quiver.Total C :=
    fun p ↦ p.1.1.comp p.1.2 p.2
  rcases mdifferentiableAt_composablePairs_sections I J x with ⟨hρ, hlam, hδ⟩
  have hm := ((contMDiff_comp (I := I) (J := J) (C := C)) p₀).mdifferentiableAt (by simp)
  intro ξ
  set u := mfderiv K J (fun p ↦ p.1.1) p₀ ξ
  set w := mfderiv K J (fun p ↦ p.1.2) p₀ ξ
  have hmρ : mMap ∘ (fun a : Quiver.Total C ↦ ⟨(a, ⟨a.right, a.right, 𝟙 a.right⟩), rfl⟩) = id :=
    funext fun a ↦ a.comp_unit
  have hmlam : mMap ∘ (fun b : Quiver.Total C ↦ ⟨(⟨b.left, b.left, 𝟙 b.left⟩, b), rfl⟩) = id :=
    funext fun b ↦ b.unit_comp
  have hmδ : mMap ∘ (fun y : C ↦ ⟨(⟨y, y, 𝟙 y⟩, ⟨y, y, 𝟙 y⟩), rfl⟩) = fun y ↦ ⟨y, y, 𝟙 y⟩ :=
    funext fun y ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C).unit_comp
  have hc1 : (mfderiv K J mMap p₀ (mfderiv J K _ e u) : E') = u :=
    (DFunLike.congr_fun ((mfderiv_id (I := J) (x := e)).symm.trans
      ((mfderiv_congr (I := J) (I' := J) (x := e) hmρ).symm.trans (mfderiv_comp e hm hρ))) u).symm
  have hc2 : (mfderiv K J mMap p₀ (mfderiv J K _ e w) : E') = w :=
    (DFunLike.congr_fun ((mfderiv_id (I := J) (x := e)).symm.trans
      ((mfderiv_congr (I := J) (I' := J) (x := e) hmlam).symm.trans
        (mfderiv_comp e hm hlam))) w).symm
  have hc3 : (mfderiv K J mMap p₀
      (mfderiv I K _ x (mfderiv J I (Quiver.Total.right : Quiver.Total C → C) e u)) : E') =
      mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x
        (mfderiv J I (Quiver.Total.right : Quiver.Total C → C) e u) :=
    (DFunLike.congr_fun
      ((mfderiv_congr (I := I) (I' := J) (x := x) hmδ).symm.trans (mfderiv_comp x hm hδ)) _).symm
  conv_lhs => rw [eq_linear_comb_mfderiv_composablePairs_unit I J x ξ]
  rw [map_sub, map_add]
  exact congrArg₂ Sub.sub (congrArg₂ Add.add hc1 hc2) hc3

/-- At an identity arrow `⟨x, x, 𝟙 x⟩`, the differential of inversion satisfies
`d(inv)(v) = d1_x(ds(v)) + d1_x(dt(v)) - v` for every tangent vector `v`. -/
theorem mfderiv_inverse_unit (x : C)
    (v : TangentSpace J (⟨x, x, 𝟙 x⟩ : Quiver.Total C)) :
    mfderiv J J (fun a : Quiver.Total C ↦ (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total C))
      ⟨x, x, 𝟙 x⟩ v =
    mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x
        (mfderiv J I (Quiver.Total.left : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩ v) +
      mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x
        (mfderiv J I (Quiver.Total.right : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩ v) - v := by
  let := composablePairsChartedSpace I J C
  have := isManifold_composablePairs I J C
  have hemb := isSmoothEmbedding_coe_composablePairs I J C
  let K := 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
  let e : Quiver.Total C := ⟨x, x, 𝟙 x⟩
  let p₀ : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} := ⟨(e, e), rfl⟩
  let uMap : C → Quiver.Total C := fun y ↦ ⟨y, y, 𝟙 y⟩
  let invMap : Quiver.Total C → Quiver.Total C := fun a ↦ ⟨a.right, a.left, inv a.hom⟩
  let mMap : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} → Quiver.Total C :=
    fun p ↦ p.1.1.comp p.1.2 p.2
  let ι : Quiver.Total C → {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} :=
    fun a ↦ ⟨(a, invMap a), rfl⟩
  have hι := (((hemb.contMDiff_iff_comp (f := ι)).2
    (contMDiff_id.prodMk (contMDiff_inverse (I := I) (J := J) (C := C))))
    e).mdifferentiableAt (by simp)
  have hfst := (hemb.contMDiff.fst (ι e)).mdifferentiableAt (by simp)
  have hsnd := (hemb.contMDiff.snd (ι e)).mdifferentiableAt (by simp)
  have hm := ((contMDiff_comp (I := I) (J := J) (C := C)) (ι e)).mdifferentiableAt (by simp)
  have hu := ((contMDiff_unit (I := I) (J := J) (C := C)) x).mdifferentiableAt (by simp)
  have hs := ((contMDiff_source I J C) e).mdifferentiableAt (by simp)
  have hιe : ι e = p₀ :=
    Subtype.ext (Prod.ext rfl (Quiver.Total.ext rfl rfl (by simp [ι, invMap, p₀, e])))
  have hmι : mMap ∘ ι = uMap ∘ Quiver.Total.left := funext fun a ↦ a.comp_inv_self
  let ξ₀ : Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ := mfderiv J K ι e v
  have hchain : ∀ (g : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} →
      Quiver.Total C), MDifferentiableAt K J g (ι e) →
      (mfderiv K J g p₀ ξ₀ : E') = mfderiv J J (g ∘ ι) e v := fun g hg ↦
    (DFunLike.congr_fun (mfderiv_congr_point (I := K) (I' := J) (f := g) hιe).symm ξ₀).trans
      (DFunLike.congr_fun (mfderiv_comp e hg hι) v).symm
  have hcomp_eq := (hchain mMap hm).trans
    ((DFunLike.congr_fun (mfderiv_congr (I := J) (I' := J) (x := e) hmι) v).trans
      (DFunLike.congr_fun (mfderiv_comp e hu hs) v))
  have hfst_eq : (mfderiv K J (fun p ↦ p.1.1) p₀ ξ₀ : E') = v :=
    (hchain (fun p ↦ p.1.1) hfst).trans (DFunLike.congr_fun (mfderiv_id (I := J) (x := e)) v)
  have hsnd_eq : (mfderiv K J (fun p ↦ p.1.2) p₀ ξ₀ : E') = mfderiv J J invMap e v :=
    hchain (fun p ↦ p.1.2) hsnd
  have hlin := hcomp_eq.symm.trans ((mfderiv_comp_unit I J x ξ₀).trans
    (congrArg₂ Sub.sub (congrArg₂ Add.add hfst_eq hsnd_eq)
      (congrArg (fun z ↦ mfderiv I J uMap x
        (mfderiv J I (Quiver.Total.right : Quiver.Total C → C) e z)) hfst_eq)))
  simp only [Function.comp_def, ContinuousLinearMap.comp_apply] at hlin
  exact eq_sub_of_add_eq ((add_comm _ _).trans (eq_add_of_sub_eq hlin.symm))

/-- **Unit-tangent inversion identity on the source kernel.** For a source-vertical tangent vector
`v` at `⟨x, x, 𝟙 x⟩` (`ds(v) = 0`), the differential of groupoid inversion is
`d(inv)(v) = d1_x(dt(v)) - v`. -/
theorem mfderiv_inverse_unit_of_mem_ker_source (x : C)
    {v : TangentSpace J (⟨x, x, 𝟙 x⟩ : Quiver.Total C)}
    (hv : mfderiv J I (Quiver.Total.left : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩ v = 0) :
    mfderiv J J (fun a : Quiver.Total C ↦ (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total C))
      ⟨x, x, 𝟙 x⟩ v =
    mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x
      (mfderiv J I (Quiver.Total.right : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩ v) - v := by
  rw [mfderiv_inverse_unit I J x v, hv, map_zero, zero_add]

end UnitDifferentials

end IsLieGroupoid

end TauCeti
