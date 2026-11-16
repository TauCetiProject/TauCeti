/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.FiberProduct.Submersion
public import TauCeti.Topology.CategoryTheory.Groupoid.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.Topology.Bases
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.SmoothEmbedding.LeftInverse
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph

/-!
# Lie groupoids

`TauCeti.IsLieGroupoid` equips a groupoid `C` with finite-dimensional boundaryless real smooth
manifold structures on objects `C` and total arrows `Quiver.Total C` such that source and target are
smooth submersions, units and inversion are smooth, categorical composition `a.comp b h` (first `a`,
then `b`, so geometric `gh` is `h.comp g`) is smooth on the transverse fibre product
`ComposablePairs C`, `Quiver.Total C` is second-countable, and every source fibre is Hausdorff.
Global Hausdorffness of `Quiver.Total C` is not assumed (foliation and monodromy groupoids need not
be Hausdorff), and forgetting charts recovers `TauCeti.IsTopologicalGroupoid`
(`TauCeti.IsLieGroupoid.toIsTopologicalGroupoid`).

## Main definitions and results

* `TauCeti.IsLieGroupoid`, `TauCeti.IsLieGroupoid.of_isSubmersion_source`: smooth Lie groupoid
  class and constructor deriving target submersiveness from source submersiveness and inversion.
* `TauCeti.IsLieGroupoid.ComposablePairs`, `TauCeti.IsLieGroupoid.composablePairsChartedSpace`,
  `TauCeti.IsLieGroupoid.inverseDiffeomorph`: composable-pair manifold (`2 dim Γ - dim M`) and
  smooth arrow-inversion diffeomorphism.
* `TauCeti.IsLieGroupoid.isSubmersion_fst_composablePairs`,
  `TauCeti.IsLieGroupoid.isSubmersion_snd_composablePairs`,
  `TauCeti.IsLieGroupoid.isOpenMap_source`, `TauCeti.IsLieGroupoid.secondCountableTopology_objects`,
  `TauCeti.IsLieGroupoid.t2Space_targetFiber`, `TauCeti.IsLieGroupoid.isSmoothEmbedding_unit`,
  `TauCeti.IsLieGroupoid.finrank_arrows_eq_iff_isLocalDiffeomorph_source`.
* `TauCeti.IsLieGroupoid.mfderiv_comp_at_unit`, `TauCeti.IsLieGroupoid.mfderiv_inverse_at_unit`:
  at `1_x`, `dm(v, w) = v + w - du_x(dt v)` and `d(inv)(v) = du_x(ds v + dt v) - v`.

## References

* K. C. H. Mackenzie, *General Theory of Lie Groupoids and Lie Algebroids*, LMS Lecture Note Ser.
  213, Cambridge Univ. Press (2005), Ch. 1 and Prop. 3.5.3.
* I. Moerdijk, J. Mrčun, *Introduction to Foliations and Lie Groupoids*, Cambridge Univ. Press
  (2003), §5.1.
* M. Crainic, R. L. Fernandes, *Integrability of Lie brackets*, Ann. of Math. **157** (2003), §2.
-/

public section

noncomputable section

open CategoryTheory Function Module Set Topology
open scoped Manifold ContDiff

namespace TauCeti

/-- A Lie groupoid on a groupoid `C` whose objects and total arrows carry finite-dimensional
boundaryless smooth real manifold structures: source and target are smooth submersions, units and
inversion are smooth, categorical composition is smooth on the transverse fibre product of target
and source, the total arrow space is second-countable, and every source fibre is Hausdorff. The
total arrow space itself need not be Hausdorff. -/
class IsLieGroupoid
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H') [J.Boundaryless]
    (C : Type*) [Category C] [IsGroupoid C]
    [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C]
    [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
    [IsManifold J ∞ (Quiver.Total C)] : Prop where
  /-- Source is a smooth submersion. -/
  isSubmersion_source : Manifold.IsSubmersion J I ∞ (Quiver.Total.left : Quiver.Total C → C)
  /-- Target is a smooth submersion. -/
  isSubmersion_target : Manifold.IsSubmersion J I ∞ (Quiver.Total.right : Quiver.Total C → C)
  /-- Units form a smooth map from objects to total arrows. -/
  contMDiff_unit : ContMDiff I J ∞ fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C)
  /-- Inversion is a smooth map on total arrows. -/
  contMDiff_inverse : ContMDiff J J ∞ fun a : Quiver.Total C ↦
    (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total C)
  /-- Categorical composition is smooth on the transverse fibre product of target and source. -/
  contMDiff_comp :
    letI := transverseFiberProductChartedSpace (by simp : (1 : ℕ∞ω) ≤ ∞)
      isSubmersion_target.contMDiff isSubmersion_source.contMDiff
      (fun p _ ↦ isSubmersion_target.transverse_left (by simp) _ p)
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
        p.1.1.comp p.1.2 p.2
  /-- The total arrow manifold has a second-countable topology. -/
  secondCountable_arrows : SecondCountableTopology (Quiver.Total C)
  /-- Every source fibre is Hausdorff in its subspace topology. -/
  t2Space_sourceFiber (x : C) : T2Space {a : Quiver.Total C // a.left = x}

namespace IsLieGroupoid

/-- Composable pairs of total arrows in categorical order: the target of the first arrow equals the
source of the second. -/
abbrev ComposablePairs (C : Type*) [Quiver C] : Type _ :=
  {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left}

section Constructor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  {C : Type*} [Category C] [IsGroupoid C]
  [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
  [IsManifold J ∞ (Quiver.Total C)]

/-- Construct `IsLieGroupoid` from the source submersion without proving the target submersion
separately: smooth involutive inversion is a diffeomorphism exchanging source and target, so
target is automatically a submersion. -/
theorem of_isSubmersion_source
    (hs : Manifold.IsSubmersion J I ∞ (Quiver.Total.left : Quiver.Total C → C))
    (hu : ContMDiff I J ∞ fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))
    (hinv : ContMDiff J J ∞ fun a : Quiver.Total C ↦
      (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total C))
    (hcomp :
      letI := transverseFiberProductChartedSpace (f := Quiver.Total.right) (g := Quiver.Total.left)
        (by simp : (1 : ℕ∞ω) ≤ ∞) (hs.contMDiff.comp hinv) hs.contMDiff
        (fun p _ ↦ hs.transverse_right (by simp) _ p)
      ContMDiff 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
        fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
          p.1.1.comp p.1.2 p.2)
    (hsc : SecondCountableTopology (Quiver.Total C))
    (ht2 : ∀ x : C, T2Space {a : Quiver.Total C // a.left = x}) :
    IsLieGroupoid I J C := by
  let e : Quiver.Total C ≃ₘ^∞⟮J, J⟯ Quiver.Total C :=
    { toFun a := ⟨a.right, a.left, inv a.hom⟩, invFun a := ⟨a.right, a.left, inv a.hom⟩
      left_inv a := by cases a; simp, right_inv a := by cases a; simp
      contMDiff_toFun := hinv, contMDiff_invFun := hinv }
  have ht : Manifold.IsSubmersion J I ∞ (Quiver.Total.right : Quiver.Total C → C) := by
    refine ((hs.contMDiff.comp e.contMDiff : ContMDiff J I ∞ Quiver.Total.right)
      |>.isSubmersionOfComplement_of_surjective_mfderiv (by simp) fun a ↦ ?_).isSubmersion
    rw [mfderiv_comp a ((hs.contMDiff (e a)).mdifferentiableAt (by simp))
      ((e.contMDiff a).mdifferentiableAt (by simp))]
    exact (hs.surjective_mfderiv (by simp) (e a)).comp
      ((e.isLocalDiffeomorph a).mfderivToContinuousLinearEquiv (by simp)).surjective
  exact ⟨hs, ht, hu, hinv, hcomp, hsc, ht2⟩

end Constructor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H') [J.Boundaryless]
  (C : Type*) [Category C] [IsGroupoid C]
  [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
  [IsManifold J ∞ (Quiver.Total C)] [IsLieGroupoid I J C]

/-- Source is smooth. -/
theorem contMDiff_source : ContMDiff J I ∞ (Quiver.Total.left : Quiver.Total C → C) :=
  (isSubmersion_source (I := I) (J := J) (C := C)).contMDiff

/-- Target is smooth. -/
theorem contMDiff_target : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C) :=
  (isSubmersion_target (I := I) (J := J) (C := C)).contMDiff

/-- The transverse fibre-product smooth atlas of dimension `2 dim Γ - dim M` on composable pairs,
retaining the subspace topology of the product of arrow spaces. -/
@[instance_reducible]
def composablePairsChartedSpace :
    ChartedSpace (Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) (ComposablePairs C) :=
  transverseFiberProductChartedSpace (by simp : (1 : ℕ∞ω) ≤ ∞)
    (contMDiff_target I J C) (contMDiff_source I J C)
    (fun p _ ↦ (isSubmersion_target (I := I) (J := J) (C := C)).transverse_left (by simp) _ p)

/-- Composable pairs form a smooth manifold with their transverse fibre-product atlas. -/
theorem isManifold_composablePairs :
    letI := composablePairsChartedSpace I J C
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞ (ComposablePairs C) :=
  isManifold_transverseFiberProduct (by simp : (1 : ℕ∞ω) ≤ ∞)
    (contMDiff_target I J C) (contMDiff_source I J C)
    (fun p _ ↦ (isSubmersion_target (I := I) (J := J) (C := C)).transverse_left (by simp) _ p)

/-- The inclusion of composable pairs into the product of arrow spaces is a smooth embedding. -/
theorem isSmoothEmbedding_coe_composablePairs :
    letI := composablePairsChartedSpace I J C
    Manifold.IsSmoothEmbedding
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) (J.prod J) ∞
      (Subtype.val : ComposablePairs C → Quiver.Total C × Quiver.Total C) :=
  isSmoothEmbedding_coe_transverseFiberProduct (by simp : (1 : ℕ∞ω) ≤ ∞)
    (contMDiff_target I J C) (contMDiff_source I J C)
    (fun p _ ↦ (isSubmersion_target (I := I) (J := J) (C := C)).transverse_left (by simp) _ p)

/-- Categorical composition is smooth with respect to `composablePairsChartedSpace`. -/
theorem contMDiff_composablePairs_comp :
    letI := composablePairsChartedSpace I J C
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (fun p : ComposablePairs C ↦ p.1.1.comp p.1.2 p.2) :=
  contMDiff_comp (I := I) (J := J) (C := C)

/-- The first factor projection on composable pairs is a smooth submersion, as the pullback of the
source submersion along target. -/
theorem isSubmersion_fst_composablePairs :
    letI := composablePairsChartedSpace I J C
    Manifold.IsSubmersion
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (fun p : ComposablePairs C ↦ p.1.1) :=
  isSubmersion_fst_transverseFiberProduct (by simp : (1 : ℕ∞ω) ≤ ∞)
    (contMDiff_target I J C) (contMDiff_source I J C)
    (fun p _ ↦ (isSubmersion_target (I := I) (J := J) (C := C)).transverse_left (by simp) _ p)
    (isSubmersion_source (I := I) (J := J) (C := C))

/-- The second factor projection on composable pairs is a smooth submersion, as the pullback of the
target submersion along source. -/
theorem isSubmersion_snd_composablePairs :
    letI := composablePairsChartedSpace I J C
    Manifold.IsSubmersion
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (fun p : ComposablePairs C ↦ p.1.2) :=
  isSubmersion_snd_transverseFiberProduct (by simp : (1 : ℕ∞ω) ≤ ∞)
    (contMDiff_target I J C) (contMDiff_source I J C)
    (fun p _ ↦ (isSubmersion_target (I := I) (J := J) (C := C)).transverse_left (by simp) _ p)
    (isSubmersion_target (I := I) (J := J) (C := C))

/-- A pair of tangent vectors to total arrows lies in the tangent image of composable pairs
precisely when the target differential of the first agrees with the source differential of the
second. -/
theorem mem_range_mfderiv_coe_composablePairs_iff :
    letI := composablePairsChartedSpace I J C
    ∀ (p : ComposablePairs C) (v : TangentSpace (J.prod J) p.1),
      v ∈ (mfderiv
        𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) (J.prod J)
        (Subtype.val : ComposablePairs C → Quiver.Total C × Quiver.Total C) p).range ↔
      mfderiv J I Quiver.Total.right p.1.1 v.1 =
        tangentSpaceCast I p.1.2.left p.1.1.right (mfderiv J I Quiver.Total.left p.1.2 v.2) :=
  mem_range_mfderiv_coe_transverseFiberProduct_iff (by simp : (1 : ℕ∞ω) ≤ ∞)
    (contMDiff_target I J C) (contMDiff_source I J C)
    (fun p _ ↦ (isSubmersion_target (I := I) (J := J) (C := C)).transverse_left (by simp) _ p)

include I J in
/-- Forgetting the smooth atlases of a Lie groupoid recovers a topological groupoid on the same
topologies. -/
theorem toIsTopologicalGroupoid : IsTopologicalGroupoid C := by
  let := composablePairsChartedSpace I J C
  exact
    { continuous_source := (contMDiff_source I J C).continuous
      continuous_target := (contMDiff_target I J C).continuous
      continuous_unit := (contMDiff_unit (I := I) (J := J) (C := C)).continuous
      continuous_inverse := (contMDiff_inverse (I := I) (J := J) (C := C)).continuous
      continuous_comp := (contMDiff_comp (I := I) (J := J) (C := C)).continuous }

include I J in
/-- Source is an open map. -/
theorem isOpenMap_source : IsOpenMap (Quiver.Total.left : Quiver.Total C → C) :=
  (isSubmersion_source (I := I) (J := J) (C := C)).isOpenMap

include I J in
/-- Target is an open map. -/
theorem isOpenMap_target : IsOpenMap (Quiver.Total.right : Quiver.Total C → C) :=
  (isSubmersion_target (I := I) (J := J) (C := C)).isOpenMap

include I J in
/-- The object manifold of a Lie groupoid is second-countable, since units embed it into the
second-countable total arrow manifold. -/
theorem secondCountableTopology_objects : SecondCountableTopology C := by
  have := toIsTopologicalGroupoid I J C
  have := secondCountable_arrows (I := I) (J := J) (C := C)
  exact (IsTopologicalGroupoid.isEmbedding_unit C).isInducing.secondCountableTopology

include I J in
/-- Composable pairs form a second-countable space in their subspace topology. -/
theorem secondCountableTopology_composablePairs : SecondCountableTopology (ComposablePairs C) := by
  have := secondCountable_arrows (I := I) (J := J) (C := C)
  exact Topology.IsEmbedding.subtypeVal.secondCountableTopology

/-- The unit map is a smooth embedding of objects into total arrows, since source is a smooth left
inverse. -/
theorem isSmoothEmbedding_unit :
    Manifold.IsSmoothEmbedding I J ∞ (fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C)) :=
  (contMDiff_unit (I := I) (J := J) (C := C)).isSmoothEmbedding_of_leftInverse (by simp)
    ((contMDiff_source I J C).of_le (by simp)) fun _ ↦ rfl

/-- Inversion on total arrows is an involutive smooth diffeomorphism exchanging source and
target. -/
def inverseDiffeomorph : Quiver.Total C ≃ₘ^∞⟮J, J⟯ Quiver.Total C where
  toFun a := ⟨a.right, a.left, inv a.hom⟩
  invFun a := ⟨a.right, a.left, inv a.hom⟩
  left_inv a := by cases a; simp
  right_inv a := by cases a; simp
  contMDiff_toFun := contMDiff_inverse (I := I) (J := J) (C := C)
  contMDiff_invFun := contMDiff_inverse (I := I) (J := J) (C := C)

@[simp]
theorem inverseDiffeomorph_apply (a : Quiver.Total C) :
    inverseDiffeomorph I J C a = ⟨a.right, a.left, inv a.hom⟩ := (rfl)

@[simp]
theorem inverseDiffeomorph_symm :
    (inverseDiffeomorph I J C).symm = inverseDiffeomorph I J C := (rfl)

/-- The source of the inverse of an arrow is its target. -/
theorem inverseDiffeomorph_left (a : Quiver.Total C) :
    (inverseDiffeomorph I J C a).left = a.right := (rfl)

/-- The target of the inverse of an arrow is its source. -/
theorem inverseDiffeomorph_right (a : Quiver.Total C) :
    (inverseDiffeomorph I J C a).right = a.left := (rfl)

/-- Inversion fixes every unit arrow. -/
theorem inverseDiffeomorph_unit (x : C) :
    inverseDiffeomorph I J C ⟨x, x, 𝟙 x⟩ = ⟨x, x, 𝟙 x⟩ := by
  simp

include I J in
/-- Every target fibre is Hausdorff, since inversion identifies it homeomorphically with the
source fibre over the same object. -/
theorem t2Space_targetFiber (x : C) : T2Space {a : Quiver.Total C // a.right = x} := by
  have := t2Space_sourceFiber (I := I) (J := J) (C := C) x
  let f : {a : Quiver.Total C // a.right = x} → {a : Quiver.Total C // a.left = x} :=
    fun a ↦ ⟨inverseDiffeomorph I J C a.1, a.2⟩
  have hf : Topology.IsEmbedding f :=
    ⟨Topology.IsInducing.of_comp
        ((inverseDiffeomorph I J C).continuous.comp continuous_subtype_val |>.subtype_mk _)
        continuous_subtype_val
        ((inverseDiffeomorph I J C).toHomeomorph.isEmbedding.isInducing.comp
          Topology.IsEmbedding.subtypeVal.isInducing),
      Function.LeftInverse.injective (g := fun b ↦ ⟨inverseDiffeomorph I J C b.1, b.2⟩)
        fun a ↦ Subtype.ext (by obtain ⟨⟨_, _, _⟩, _⟩ := a; simp [f])⟩
  exact hf.t2Space

/-! ### Differential properties, dimension, and the étale case -/

/-- Source has a split-surjective differential at every arrow. -/
theorem isDiffSubmersionAt_source (a : Quiver.Total C) :
    IsDiffSubmersionAt J I (Quiver.Total.left : Quiver.Total C → C) a :=
  isDiffSubmersionAt_iff.mpr
    ((isSubmersion_source (I := I) (J := J) (C := C)).hasRightInverse_mfderiv (by simp) a)

/-- Target has a split-surjective differential at every arrow. -/
theorem isDiffSubmersionAt_target (a : Quiver.Total C) :
    IsDiffSubmersionAt J I (Quiver.Total.right : Quiver.Total C → C) a :=
  isDiffSubmersionAt_iff.mpr
    ((isSubmersion_target (I := I) (J := J) (C := C)).hasRightInverse_mfderiv (by simp) a)

/-- The differential of source is surjective at every arrow. -/
theorem surjective_mfderiv_source (a : Quiver.Total C) :
    Surjective (mfderiv J I (Quiver.Total.left : Quiver.Total C → C) a) :=
  (isSubmersion_source (I := I) (J := J) (C := C)).surjective_mfderiv (by simp) a

/-- The differential of target is surjective at every arrow. -/
theorem surjective_mfderiv_target (a : Quiver.Total C) :
    Surjective (mfderiv J I (Quiver.Total.right : Quiver.Total C → C) a) :=
  (isSubmersion_target (I := I) (J := J) (C := C)).surjective_mfderiv (by simp) a

/-- Every object is a regular value of the source submersion. -/
theorem isRegularValue_source (x : C) :
    IsRegularValue J I (Quiver.Total.left : Quiver.Total C → C) x :=
  isRegularValue_iff.mpr fun a _ ↦ isRegularPoint_iff.mpr (surjective_mfderiv_source I J C a)

/-- Every object is a regular value of the target submersion. -/
theorem isRegularValue_target (x : C) :
    IsRegularValue J I (Quiver.Total.right : Quiver.Total C → C) x :=
  isRegularValue_iff.mpr fun a _ ↦ isRegularPoint_iff.mpr (surjective_mfderiv_target I J C a)

include I J in
/-- On a nonempty Lie groupoid, the dimension of the arrow manifold is at least the dimension of
the object manifold. -/
theorem finrank_objects_le_finrank_arrows [Nonempty C] :
    finrank ℝ E ≤ finrank ℝ E' := by
  obtain ⟨x⟩ := ‹Nonempty C›
  let a : Quiver.Total C := ⟨x, x, 𝟙 x⟩
  have hsurj := surjective_mfderiv_source I J C a
  have hle := LinearMap.finrank_range_le (mfderiv J I Quiver.Total.left a).toLinearMap
  rwa [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hle

/-- Source is a smooth local diffeomorphism if and only if target is, since inversion is a
diffeomorphism exchanging them. -/
theorem isLocalDiffeomorph_source_iff_target :
    IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C) ↔
      IsLocalDiffeomorph J I ∞ (Quiver.Total.right : Quiver.Total C → C) :=
  ⟨fun h a ↦ (((inverseDiffeomorph I J C).isLocalDiffeomorph a).comp_iff_right).mpr
      (h (inverseDiffeomorph I J C a)),
    fun h a ↦ (((inverseDiffeomorph I J C).isLocalDiffeomorph a).comp_iff_right).mpr
      (h (inverseDiffeomorph I J C a))⟩

/-- When the arrow and object models have equal dimension, source is a smooth local diffeomorphism
(the Lie groupoid is étale). -/
theorem isLocalDiffeomorph_source_of_finrank_eq (hdim : finrank ℝ E' = finrank ℝ E) :
    IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C) := fun a ↦ by
  have : FiniteDimensional ℝ (TangentSpace J a) := inferInstanceAs (FiniteDimensional ℝ E')
  have : FiniteDimensional ℝ (TangentSpace I a.left) := inferInstanceAs (FiniteDimensional ℝ E)
  have hinj : Injective (mfderiv J I Quiver.Total.left a) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr
      (surjective_mfderiv_source I J C a)
  exact isLocalDiffeomorphAt_of_injective_mfderiv (contMDiff_source I J C).contMDiffOn
    isOpen_univ (mem_univ a) BoundarylessManifold.isInteriorPoint (by simp) hinj hdim

/-- On a nonempty Lie groupoid, the arrow and object manifolds have equal dimension if and only if
source is a smooth local diffeomorphism (the étale case). -/
theorem finrank_arrows_eq_iff_isLocalDiffeomorph_source [Nonempty C] :
    finrank ℝ E' = finrank ℝ E ↔
      IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C) := by
  refine ⟨isLocalDiffeomorph_source_of_finrank_eq I J C, fun h ↦ ?_⟩
  obtain ⟨x⟩ := ‹Nonempty C›
  exact ((h ⟨x, x, 𝟙 x⟩).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv.finrank_eq

/-! ### Tangent identities at units -/

section TangentIdentities

variable {I J C}

private theorem tangentSpaceCast_mfderiv_comp
    {EX HX MX EY HY MY EZ HZ MZ : Type*}
    [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
    {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace MX] [ChartedSpace HX MX]
    [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
    {IY : ModelWithCorners ℝ EY HY} [TopologicalSpace MY] [ChartedSpace HY MY]
    [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [TopologicalSpace HZ]
    {IZ : ModelWithCorners ℝ EZ HZ} [TopologicalSpace MZ] [ChartedSpace HZ MZ]
    {g : MY → MZ} {f : MX → MY} {h : MX → MZ} {x : MX}
    (hg : ContMDiff IY IZ ∞ g) (hf : ContMDiff IX IY ∞ f) (heq : g ∘ f = h)
    (z₀ : MZ) (v : TangentSpace IX x) :
    tangentSpaceCast IZ (g (f x)) z₀ (mfderiv IY IZ g (f x) (mfderiv IX IY f x v)) =
      tangentSpaceCast IZ (h x) z₀ (mfderiv IX IZ h x v) := by
  have hc := congrArg (fun L ↦ tangentSpaceCast IZ _ z₀ (L v)) (mfderiv_comp x
    ((hg (f x)).mdifferentiableAt (by simp)) ((hf x).mdifferentiableAt (by simp))).symm
  exact hc.trans (congrArg (fun k : MX → MZ ↦
    tangentSpaceCast IZ (k x) z₀ (mfderiv IX IZ k x v)) heq)

private theorem tangentSpaceCast_mfderiv_comp_id
    {EX HX MX EY HY MY : Type*}
    [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
    {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace MX] [ChartedSpace HX MX]
    [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
    {IY : ModelWithCorners ℝ EY HY} [TopologicalSpace MY] [ChartedSpace HY MY]
    {g : MY → MX} {f : MX → MY} {x : MX}
    (hg : ContMDiff IY IX ∞ g) (hf : ContMDiff IX IY ∞ f) (heq : g ∘ f = id)
    (v : TangentSpace IX x) :
    tangentSpaceCast IX (g (f x)) x (mfderiv IY IX g (f x) (mfderiv IX IY f x v)) = v :=
  (tangentSpaceCast_mfderiv_comp hg hf heq x v).trans (by rw [mfderiv_id]; rfl)

/-- Differentiating `s ∘ u = id` at an object `x` shows that `du_x` is a continuous linear right
inverse of `ds_{1_x}`. -/
@[simp]
theorem mfderiv_source_comp_mfderiv_unit (x : C) :
    (mfderiv J I (Quiver.Total.left : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩).comp
      (mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x) =
      ContinuousLinearMap.id ℝ (TangentSpace I x) :=
  (mfderiv_comp x ((contMDiff_source I J C _).mdifferentiableAt (by simp))
    ((contMDiff_unit (I := I) (J := J) (C := C) x).mdifferentiableAt (by simp))).symm.trans
    mfderiv_id

/-- Differentiating `t ∘ u = id` at an object `x` shows that `du_x` is a continuous linear right
inverse of `dt_{1_x}`. -/
@[simp]
theorem mfderiv_target_comp_mfderiv_unit (x : C) :
    (mfderiv J I (Quiver.Total.right : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩).comp
      (mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x) =
      ContinuousLinearMap.id ℝ (TangentSpace I x) :=
  (mfderiv_comp x ((contMDiff_target I J C _).mdifferentiableAt (by simp))
    ((contMDiff_unit (I := I) (J := J) (C := C) x).mdifferentiableAt (by simp))).symm.trans
    mfderiv_id

@[simp]
theorem mfderiv_source_mfderiv_unit_apply (x : C) (v : TangentSpace I x) :
    mfderiv J I (Quiver.Total.left : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩
      (mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x v) = v :=
  congrArg (· v) (mfderiv_source_comp_mfderiv_unit x)

@[simp]
theorem mfderiv_target_mfderiv_unit_apply (x : C) (v : TangentSpace I x) :
    mfderiv J I (Quiver.Total.right : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩
      (mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x v) = v :=
  congrArg (· v) (mfderiv_target_comp_mfderiv_unit x)

/-- Differentiating `inv ∘ u = u` shows that the differential of inversion fixes the tangent space
of units. -/
@[simp]
theorem mfderiv_inverse_comp_mfderiv_unit (x : C) :
    (mfderiv J J (inverseDiffeomorph I J C) ⟨x, x, 𝟙 x⟩).comp
      (mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x) =
      mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x := by
  ext v
  exact tangentSpaceCast_mfderiv_comp (inverseDiffeomorph I J C).contMDiff
    (contMDiff_unit (I := I) (J := J) (C := C)) (funext (inverseDiffeomorph_unit I J C))
    ⟨x, x, 𝟙 x⟩ v

/-- Differentiating `s ∘ inv = t` relates the source and target differentials through inversion. -/
theorem mfderiv_source_comp_mfderiv_inverse (a : Quiver.Total C) :
    (mfderiv J I (Quiver.Total.left : Quiver.Total C → C) (inverseDiffeomorph I J C a)).comp
      (mfderiv J J (inverseDiffeomorph I J C) a) =
      mfderiv J I (Quiver.Total.right : Quiver.Total C → C) a :=
  (mfderiv_comp a ((contMDiff_source I J C _).mdifferentiableAt (by simp))
    (((inverseDiffeomorph I J C).contMDiff a).mdifferentiableAt (by simp))).symm

/-- Differentiating `t ∘ inv = s` relates the target and source differentials through inversion. -/
theorem mfderiv_target_comp_mfderiv_inverse (a : Quiver.Total C) :
    (mfderiv J I (Quiver.Total.right : Quiver.Total C → C) (inverseDiffeomorph I J C a)).comp
      (mfderiv J J (inverseDiffeomorph I J C) a) =
      mfderiv J I (Quiver.Total.left : Quiver.Total C → C) a :=
  (mfderiv_comp a ((contMDiff_target I J C _).mdifferentiableAt (by simp))
    (((inverseDiffeomorph I J C).contMDiff a).mdifferentiableAt (by simp))).symm

private theorem isCompl_range_ker_of_leftInverse {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] {u : V →ₗ[ℝ] W} {p : W →ₗ[ℝ] V} (h : ∀ v, p (u v) = v) :
    IsCompl (LinearMap.range u) (LinearMap.ker p) := by
  have hker : LinearMap.ker (u.rangeRestrict.comp p) = LinearMap.ker p := by
    ext v; simp [LinearMap.map_eq_zero_iff u (Function.LeftInverse.injective h)]
  rw [← hker]
  refine LinearMap.isCompl_of_proj fun ⟨_, y, hy⟩ ↦ Subtype.ext ?_
  dsimp; rw [← hy, h y]

/-- At any unit `1_x`, the tangent space of arrows decomposes as the direct sum of the image of
`du_x` and the kernel of `ds_{1_x}` (the Lie algebroid fibre over `x`). -/
theorem isCompl_range_mfderiv_unit_ker_mfderiv_source (x : C) :
    IsCompl
      (LinearMap.range (mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x).toLinearMap)
      (LinearMap.ker (mfderiv J I (Quiver.Total.left : Quiver.Total C → C)
        ⟨x, x, 𝟙 x⟩).toLinearMap) :=
  isCompl_range_ker_of_leftInverse (mfderiv_source_mfderiv_unit_apply x)

/-- At any unit `1_x`, the tangent space of arrows also decomposes as the direct sum of the image
of `du_x` and the kernel of `dt_{1_x}`. -/
theorem isCompl_range_mfderiv_unit_ker_mfderiv_target (x : C) :
    IsCompl
      (LinearMap.range (mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x).toLinearMap)
      (LinearMap.ker (mfderiv J I (Quiver.Total.right : Quiver.Total C → C)
        ⟨x, x, 𝟙 x⟩).toLinearMap) :=
  isCompl_range_ker_of_leftInverse (mfderiv_target_mfderiv_unit_apply x)

/-- **Differential of composition at a unit.** At the composable pair `(1_x, 1_x)`, every tangent
vector `w` of `ComposablePairs C` projects via the two factor maps to a pair `(v₁, v₂)` with
`dt(v₁) = ds(v₂)`, and the differential of categorical composition sends `w` to
`v₁ + v₂ - du_x(dt(v₁))`. -/
theorem mfderiv_comp_at_unit (x : C) :
    letI := composablePairsChartedSpace I J C
    ∀ w : TangentSpace 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
        (⟨(⟨x, x, 𝟙 x⟩, ⟨x, x, 𝟙 x⟩), rfl⟩ : ComposablePairs C),
      mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
        (fun p : ComposablePairs C ↦ p.1.1.comp p.1.2 p.2)
        ⟨(⟨x, x, 𝟙 x⟩, ⟨x, x, 𝟙 x⟩), rfl⟩ w =
        mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
          (fun p : ComposablePairs C ↦ p.1.1) ⟨(⟨x, x, 𝟙 x⟩, ⟨x, x, 𝟙 x⟩), rfl⟩ w +
        mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
          (fun p : ComposablePairs C ↦ p.1.2) ⟨(⟨x, x, 𝟙 x⟩, ⟨x, x, 𝟙 x⟩), rfl⟩ w -
        mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x
          (mfderiv J I (Quiver.Total.right : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩
            (mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
              (fun p : ComposablePairs C ↦ p.1.1) ⟨(⟨x, x, 𝟙 x⟩, ⟨x, x, 𝟙 x⟩), rfl⟩ w)) := by
  let := composablePairsChartedSpace I J C; have := isManifold_composablePairs I J C
  let K := 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
  let u : C → Quiver.Total C := fun y ↦ ⟨y, y, 𝟙 y⟩; let u₀ : Quiver.Total C := u x
  let p₀ : ComposablePairs C := ⟨(u₀, u₀), rfl⟩; let π₁ (p : ComposablePairs C) := p.1.1
  let π₂ (p : ComposablePairs C) := p.1.2; let m (p : ComposablePairs C) := p.1.1.comp p.1.2 p.2
  have hι := isSmoothEmbedding_coe_composablePairs I J C; intro w
  have hπ₁ : ContMDiff K J ∞ π₁ := contMDiff_fst.comp hι.contMDiff
  have hπ₂ : ContMDiff K J ∞ π₂ := contMDiff_snd.comp hι.contMDiff
  have hu : ContMDiff I J ∞ u := contMDiff_unit; have hm : ContMDiff K J ∞ m := contMDiff_comp
  let σR : Quiver.Total C → ComposablePairs C := fun a ↦ ⟨(a, u a.right), rfl⟩
  let σL : Quiver.Total C → ComposablePairs C := fun b ↦ ⟨(u b.left, b), rfl⟩
  let σD : C → ComposablePairs C := fun y ↦ ⟨(u y, u y), rfl⟩
  have hσR : ContMDiff J K ∞ σR :=
    hι.contMDiff_iff_comp.mpr (contMDiff_id.prodMk (hu.comp (contMDiff_target I J C)))
  have hσL : ContMDiff J K ∞ σL :=
    hι.contMDiff_iff_comp.mpr ((hu.comp (contMDiff_source I J C)).prodMk contMDiff_id)
  have hσD : ContMDiff I K ∞ σD := hι.contMDiff_iff_comp.mpr (hu.prodMk hu)
  let v₁ : TangentSpace J u₀ := mfderiv K J π₁ p₀ w
  let v₂ : TangentSpace J u₀ := mfderiv K J π₂ p₀ w
  let ξ : TangentSpace I x := mfderiv J I Quiver.Total.right u₀ v₁
  have hv_eq : ξ = mfderiv J I Quiver.Total.left u₀ v₂ :=
    (tangentSpaceCast_mfderiv_comp (contMDiff_target I J C) hπ₁ (funext fun p ↦ p.2) x w).trans
      (tangentSpaceCast_mfderiv_comp (contMDiff_source I J C) hπ₂ rfl x w).symm
  let w' : TangentSpace K p₀ := mfderiv J K σR u₀ v₁ + mfderiv J K σL u₀ v₂ - mfderiv I K σD x ξ
  have hw_eq : w = w' := by
    refine sub_eq_zero.mp <| eq_zero_of_mfderiv_transverseFiberProduct (by simp : (1 : ℕ∞ω) ≤ ∞)
      (contMDiff_target I J C) (contMDiff_source I J C) (fun p _ ↦
        (isSubmersion_target (I := I) (J := J) (C := C)).transverse_left (by simp) _ p) p₀ _ ?_ ?_
    · have h1 : mfderiv K J π₁ p₀ _ = v₁ := tangentSpaceCast_mfderiv_comp_id hπ₁ hσR rfl v₁
      have h2 : mfderiv K J π₁ p₀ _ = mfderiv I J u x ξ :=
        (tangentSpaceCast_mfderiv_comp hπ₁ hσL rfl u₀ v₂).trans
          ((tangentSpaceCast_mfderiv_comp hu (contMDiff_source I J C) rfl u₀ v₂).symm.trans
            (congrArg (mfderiv I J u x) hv_eq.symm))
      have h3 : mfderiv K J π₁ p₀ _ = mfderiv I J u x ξ :=
        tangentSpaceCast_mfderiv_comp (h := u) hπ₁ hσD rfl u₀ ξ
      dsimp only [w', π₁, v₁] at h1 h2 h3 ⊢; rw [map_sub, map_sub, map_add, h1, h2, h3]; abel
    · have h1 : mfderiv K J π₂ p₀ _ = mfderiv I J u x ξ :=
        (tangentSpaceCast_mfderiv_comp hπ₂ hσR rfl u₀ v₁).trans
          (tangentSpaceCast_mfderiv_comp hu (contMDiff_target I J C) rfl u₀ v₁).symm
      have h2 : mfderiv K J π₂ p₀ _ = v₂ := tangentSpaceCast_mfderiv_comp_id hπ₂ hσL rfl v₂
      have h3 : mfderiv K J π₂ p₀ _ = mfderiv I J u x ξ :=
        tangentSpaceCast_mfderiv_comp (h := u) hπ₂ hσD rfl u₀ ξ
      dsimp only [w', π₂, v₂] at h1 h2 h3 ⊢; rw [map_sub, map_sub, map_add, h1, h2, h3]; abel
  have hm_σR : mfderiv K J m p₀ _ = v₁ :=
    tangentSpaceCast_mfderiv_comp_id hm hσR (funext Quiver.Total.comp_unit) v₁
  have hm_σL : mfderiv K J m p₀ _ = v₂ :=
    tangentSpaceCast_mfderiv_comp_id hm hσL (funext Quiver.Total.unit_comp) v₂
  have hm_σD : mfderiv K J m p₀ _ = mfderiv I J u x ξ :=
    tangentSpaceCast_mfderiv_comp hm hσD (funext fun z ↦ Quiver.Total.unit_comp (u z)) u₀ ξ
  change mfderiv K J m p₀ w = v₁ + v₂ - mfderiv I J u x ξ; rw [hw_eq]
  simp only [w', map_sub, map_add, hm_σR, hm_σL, hm_σD]; rfl

/-- **Differential of inversion at a unit.** For every arrow tangent vector `v` at `1_x`,
`d(inv)_{1_x}(v) = du_x(ds(v) + dt(v)) - v`. -/
theorem mfderiv_inverse_at_unit (x : C) (v : TangentSpace J (⟨x, x, 𝟙 x⟩ : Quiver.Total C)) :
    mfderiv J J (inverseDiffeomorph I J C) ⟨x, x, 𝟙 x⟩ v =
      mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x
        (mfderiv J I (Quiver.Total.left : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩ v +
          mfderiv J I (Quiver.Total.right : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩ v) - v := by
  let := composablePairsChartedSpace I J C; have := isManifold_composablePairs I J C
  let K := 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
  let u : C → Quiver.Total C := fun y ↦ ⟨y, y, 𝟙 y⟩
  let u₀ : Quiver.Total C := ⟨x, x, 𝟙 x⟩; let p₀ : ComposablePairs C := ⟨(u₀, u₀), rfl⟩
  let π₁ : ComposablePairs C → Quiver.Total C := fun p ↦ p.1.1
  let π₂ : ComposablePairs C → Quiver.Total C := fun p ↦ p.1.2
  let m : ComposablePairs C → Quiver.Total C := fun p ↦ p.1.1.comp p.1.2 p.2
  have hι := isSmoothEmbedding_coe_composablePairs I J C
  have hπ₁ : ContMDiff K J ∞ π₁ := contMDiff_fst.comp hι.contMDiff
  have hπ₂ : ContMDiff K J ∞ π₂ := contMDiff_snd.comp hι.contMDiff
  have hu : ContMDiff I J ∞ u := contMDiff_unit (I := I) (J := J) (C := C)
  have hm : ContMDiff K J ∞ m := contMDiff_comp (I := I) (J := J) (C := C)
  let τ : Quiver.Total C → ComposablePairs C := fun a ↦ ⟨(a, inverseDiffeomorph I J C a), rfl⟩
  have hτ : ContMDiff J K ∞ τ :=
    hι.contMDiff_iff_comp.mpr (contMDiff_id.prodMk (inverseDiffeomorph I J C).contMDiff)
  have hτ0 : τ u₀ = p₀ := Subtype.ext (Prod.ext rfl (inverseDiffeomorph_unit I J C x))
  have h_at_q : ∀ (q : ComposablePairs C), q = p₀ → ∀ w : TangentSpace K q,
      tangentSpaceCast J (m q) u₀ (mfderiv K J m q w) =
        tangentSpaceCast J (π₁ q) u₀ (mfderiv K J π₁ q w) +
          tangentSpaceCast J (π₂ q) u₀ (mfderiv K J π₂ q w) -
          mfderiv I J u x (mfderiv J I Quiver.Total.right u₀
            (tangentSpaceCast J (π₁ q) u₀ (mfderiv K J π₁ q w))) := by
    rintro _ rfl w; exact mfderiv_comp_at_unit x w
  let v₀ : TangentSpace J u₀ := v
  have hrhs := h_at_q (τ u₀) hτ0 (mfderiv J K τ u₀ v₀)
  have h1 := tangentSpaceCast_mfderiv_comp_id hπ₁ hτ rfl v₀
  have h2 := tangentSpaceCast_mfderiv_comp hπ₂ hτ rfl u₀ v₀
  have hlhs := (tangentSpaceCast_mfderiv_comp hm hτ (funext Quiver.Total.comp_inv) u₀ v₀).trans
    (tangentSpaceCast_mfderiv_comp hu (contMDiff_source I J C) rfl u₀ v₀).symm
  rw [hlhs, h1, h2] at hrhs
  change tangentSpaceCast J (inverseDiffeomorph I J C u₀) u₀
      (mfderiv J J (inverseDiffeomorph I J C) u₀ v₀) =
      mfderiv I J u x
        (mfderiv J I Quiver.Total.left u₀ v₀ + mfderiv J I Quiver.Total.right u₀ v₀) - v₀
  rw [map_add]; exact eq_sub_of_add_eq' (eq_add_of_sub_eq hrhs.symm)

/-- On the source-vertical tangent space `ker(ds_{1_x})` (the Lie algebroid fibre at `x`),
inversion differentiates to `v ↦ du_x(dt(v)) - v`. -/
theorem mfderiv_inverse_at_unit_of_mem_ker_source (x : C)
    {v : TangentSpace J (⟨x, x, 𝟙 x⟩ : Quiver.Total C)}
    (hv : mfderiv J I (Quiver.Total.left : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩ v = 0) :
    mfderiv J J (inverseDiffeomorph I J C) ⟨x, x, 𝟙 x⟩ v =
      mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x
        (mfderiv J I (Quiver.Total.right : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩ v) - v := by
  rw [mfderiv_inverse_at_unit, hv, zero_add]

/-- On an isotropy tangent vector `v ∈ ker(ds_{1_x}) ∩ ker(dt_{1_x})`, inversion differentiates to
`-v`. -/
theorem mfderiv_inverse_at_unit_of_mem_ker_source_of_mem_ker_target (x : C)
    {v : TangentSpace J (⟨x, x, 𝟙 x⟩ : Quiver.Total C)}
    (hs : mfderiv J I (Quiver.Total.left : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩ v = 0)
    (ht : mfderiv J I (Quiver.Total.right : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩ v = 0) :
    mfderiv J J (inverseDiffeomorph I J C) ⟨x, x, 𝟙 x⟩ v = -v := by
  rw [mfderiv_inverse_at_unit, hs, ht, add_zero, map_zero, zero_sub]

end TangentIdentities

end IsLieGroupoid

end TauCeti
