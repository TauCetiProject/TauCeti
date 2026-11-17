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
import Mathlib.Topology.Bases
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.SmoothEmbedding.LeftInverse
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph
import TauCeti.LinearAlgebra.Projection

/-!
# Lie groupoids

`TauCeti.IsLieGroupoid` equips a groupoid `C` with finite-dimensional boundaryless real smooth
manifold structures on objects `C` and total arrows `Quiver.Total C` such that source and target are
smooth submersions, units and inversion are smooth, categorical composition `a.comp b h` (first `a`,
then `b`, so geometric `gh` is `h.comp g`) is smooth on the transverse fibre product
`ComposablePairs C`, `Quiver.Total C` is second-countable, and the object manifold `C` and every
source fibre are Hausdorff. Global Hausdorffness of `Quiver.Total C` is not assumed (foliation and
monodromy groupoids need not be Hausdorff), and forgetting charts recovers
`TauCeti.IsTopologicalGroupoid` (`TauCeti.IsLieGroupoid.toIsTopologicalGroupoid`).

## Main definitions and results

* `TauCeti.IsLieGroupoid`, `TauCeti.IsLieGroupoid.of_isSubmersion_source`: smooth Lie groupoid
  class and minimal constructor deriving both target submersiveness and unit smoothness from source
  submersiveness, smooth inversion, and smooth composition.
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
and source, the total arrow space is second-countable, and both the object space `C` and every
source fibre are Hausdorff. The total arrow space itself need not be Hausdorff. -/
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
  secondCountableTopology_arrows : SecondCountableTopology (Quiver.Total C)
  /-- The object manifold is Hausdorff. -/
  t2Space_objects : T2Space C
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

/-- Construct `IsLieGroupoid` from the source submersion, smooth inversion, and smooth composition
without proving target submersiveness or unit smoothness separately: involutive inversion is a
diffeomorphism exchanging source and target, and `u ∘ s = comp ∘ (id, inv)` descends along the
surjective source submersion. -/
theorem of_isSubmersion_source
    (hs : Manifold.IsSubmersion J I ∞ (Quiver.Total.left : Quiver.Total C → C))
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
    (ht2_obj : T2Space C)
    (ht2 : ∀ x : C, T2Space {a : Quiver.Total C // a.left = x}) :
    IsLieGroupoid I J C := by
  let e : Quiver.Total C ≃ₘ^∞⟮J, J⟯ Quiver.Total C :=
    { toFun a := ⟨a.right, a.left, inv a.hom⟩, invFun a := ⟨a.right, a.left, inv a.hom⟩
      left_inv a := by cases a; simp, right_inv a := by cases a; simp
      contMDiff_toFun := hinv, contMDiff_invFun := hinv }
  have ht : Manifold.IsSubmersion J I ∞ (Quiver.Total.right : Quiver.Total C → C) :=
    e.isLocalDiffeomorph.isSubmersion_comp hs
  have hu : ContMDiff I J ∞ fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C) := by
    let := transverseFiberProductChartedSpace (f := Quiver.Total.right) (g := Quiver.Total.left)
      (by simp : (1 : ℕ∞ω) ≤ ∞) (hs.contMDiff.comp hinv) hs.contMDiff
      (fun p _ ↦ hs.transverse_right (by simp) _ p)
    have hι := isSmoothEmbedding_coe_transverseFiberProduct
      (f := Quiver.Total.right) (g := Quiver.Total.left)
      (by simp : (1 : ℕ∞ω) ≤ ∞) (hs.contMDiff.comp hinv) hs.contMDiff
      (fun p _ ↦ hs.transverse_right (by simp) _ p)
    have hτ : ContMDiff J 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
        (fun a : Quiver.Total C ↦
          (⟨(a, ⟨a.right, a.left, inv a.hom⟩), rfl⟩ : ComposablePairs C)) :=
      hι.contMDiff_iff_comp.mpr (contMDiff_id.prodMk hinv)
    exact (hs.contMDiff_comp_iff Quiver.Total.left_surjective le_rfl).mp
      ((hcomp.comp hτ).congr fun a ↦ (Quiver.Total.comp_inv a).symm)
  exact ⟨hs, ht, hu, hinv, hcomp, hsc, ht2_obj, ht2⟩

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

/-- `composablePairsChartedSpace` is the transverse fibre-product smooth atlas of target and
source. -/
theorem composablePairsChartedSpace_eq_transverseFiberProductChartedSpace :
    composablePairsChartedSpace I J C =
      transverseFiberProductChartedSpace (by simp : (1 : ℕ∞ω) ≤ ∞)
        (contMDiff_target I J C) (contMDiff_source I J C)
        (fun p _ ↦ (isSubmersion_target (I := I) (J := J) (C := C)).transverse_left
          (by simp) _ p) :=
  (rfl)

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

/-- The first factor projection on composable pairs is smooth. -/
theorem contMDiff_fst_composablePairs :
    letI := composablePairsChartedSpace I J C
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (fun p : ComposablePairs C ↦ p.1.1) :=
  letI := composablePairsChartedSpace I J C
  (isSubmersion_fst_composablePairs I J C).contMDiff

/-- The second factor projection on composable pairs is smooth. -/
theorem contMDiff_snd_composablePairs :
    letI := composablePairsChartedSpace I J C
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (fun p : ComposablePairs C ↦ p.1.2) :=
  letI := composablePairsChartedSpace I J C
  (isSubmersion_snd_composablePairs I J C).contMDiff

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

/-- Any pair `(u, w)` of arrow tangent vectors at `p : ComposablePairs C` whose target and source
differentials match arises from a tangent vector of `ComposablePairs C`. -/
theorem exists_mfderiv_eq_of_composablePairs :
    letI := composablePairsChartedSpace I J C
    ∀ (p : ComposablePairs C) (u : TangentSpace J p.1.1) (w : TangentSpace J p.1.2),
      mfderiv J I Quiver.Total.right p.1.1 u =
        tangentSpaceCast I p.1.2.left p.1.1.right (mfderiv J I Quiver.Total.left p.1.2 w) →
      ∃ ξ, mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
          (fun q : ComposablePairs C ↦ q.1.1) p ξ = u ∧
        mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
          (fun q : ComposablePairs C ↦ q.1.2) p ξ = w :=
  exists_mfderiv_eq_of_transverseFiberProduct (by simp : (1 : ℕ∞ω) ≤ ∞)
    (contMDiff_target I J C) (contMDiff_source I J C)
    (fun p _ ↦ (isSubmersion_target (I := I) (J := J) (C := C)).transverse_left (by simp) _ p)

/-- A tangent vector of `ComposablePairs C` is zero when both arrow-projection differentials vanish
on it. -/
theorem eq_zero_of_mfderiv_composablePairs :
    letI := composablePairsChartedSpace I J C
    ∀ (p : ComposablePairs C)
      (ξ : TangentSpace 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) p),
      mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
          (fun q : ComposablePairs C ↦ q.1.1) p ξ = 0 →
        mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
          (fun q : ComposablePairs C ↦ q.1.2) p ξ = 0 → ξ = 0 :=
  eq_zero_of_mfderiv_transverseFiberProduct (by simp : (1 : ℕ∞ω) ≤ ∞)
    (contMDiff_target I J C) (contMDiff_source I J C)
    (fun p _ ↦ (isSubmersion_target (I := I) (J := J) (C := C)).transverse_left (by simp) _ p)

/-- Left unit degeneracy `b ↦ (1_{s(b)}, b)` into composable pairs. -/
abbrev leftUnitPair {C : Type*} [Category C] (b : Quiver.Total C) : ComposablePairs C :=
  ⟨(⟨b.left, b.left, 𝟙 b.left⟩, b), rfl⟩

/-- Right unit degeneracy `a ↦ (a, 1_{t(a)})` into composable pairs. -/
abbrev rightUnitPair {C : Type*} [Category C] (a : Quiver.Total C) : ComposablePairs C :=
  ⟨(a, ⟨a.right, a.right, 𝟙 a.right⟩), rfl⟩

/-- Diagonal unit degeneracy `x ↦ (1_x, 1_x)` from objects into composable pairs. -/
abbrev unitPair {C : Type*} [Category C] (x : C) : ComposablePairs C :=
  ⟨(⟨x, x, 𝟙 x⟩, ⟨x, x, 𝟙 x⟩), rfl⟩

@[simp]
theorem leftUnitPair_fst {C : Type*} [Category C] (b : Quiver.Total C) :
    (leftUnitPair b).1.1 = ⟨b.left, b.left, 𝟙 b.left⟩ := (rfl)

@[simp]
theorem leftUnitPair_snd {C : Type*} [Category C] (b : Quiver.Total C) :
    (leftUnitPair b).1.2 = b := (rfl)

@[simp]
theorem rightUnitPair_fst {C : Type*} [Category C] (a : Quiver.Total C) :
    (rightUnitPair a).1.1 = a := (rfl)

@[simp]
theorem rightUnitPair_snd {C : Type*} [Category C] (a : Quiver.Total C) :
    (rightUnitPair a).1.2 = ⟨a.right, a.right, 𝟙 a.right⟩ := (rfl)

@[simp]
theorem unitPair_fst {C : Type*} [Category C] (x : C) :
    (unitPair x).1.1 = ⟨x, x, 𝟙 x⟩ := (rfl)

@[simp]
theorem unitPair_snd {C : Type*} [Category C] (x : C) :
    (unitPair x).1.2 = ⟨x, x, 𝟙 x⟩ := (rfl)

/-- Composing the arrows of `leftUnitPair b` recovers `b`. -/
theorem comp_leftUnitPair {C : Type*} [Category C] (b : Quiver.Total C) :
    (leftUnitPair b).1.1.comp (leftUnitPair b).1.2 (leftUnitPair b).2 = b :=
  Quiver.Total.unit_comp b rfl

/-- Composing the arrows of `rightUnitPair a` recovers `a`. -/
theorem comp_rightUnitPair {C : Type*} [Category C] (a : Quiver.Total C) :
    (rightUnitPair a).1.1.comp (rightUnitPair a).1.2 (rightUnitPair a).2 = a :=
  Quiver.Total.comp_unit a rfl

/-- Composing the arrows of `unitPair x` recovers the unit arrow `1_x`. -/
theorem comp_unitPair {C : Type*} [Category C] (x : C) :
    (unitPair x).1.1.comp (unitPair x).1.2 (unitPair x).2 = ⟨x, x, 𝟙 x⟩ :=
  Quiver.Total.unit_comp ⟨x, x, 𝟙 x⟩ rfl

/-- The left unit degeneracy `b ↦ (1_{s(b)}, b)` into composable pairs is smooth. -/
theorem contMDiff_leftUnitPair :
    letI := composablePairsChartedSpace I J C
    ContMDiff J 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (leftUnitPair : Quiver.Total C → ComposablePairs C) :=
  letI := composablePairsChartedSpace I J C
  (isSmoothEmbedding_coe_composablePairs I J C).contMDiff_iff_comp.mpr
    (((contMDiff_unit (I := I) (J := J) (C := C)).comp (contMDiff_source I J C)).prodMk
      contMDiff_id)

/-- The right unit degeneracy `a ↦ (a, 1_{t(a)})` into composable pairs is smooth. -/
theorem contMDiff_rightUnitPair :
    letI := composablePairsChartedSpace I J C
    ContMDiff J 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (rightUnitPair : Quiver.Total C → ComposablePairs C) :=
  letI := composablePairsChartedSpace I J C
  (isSmoothEmbedding_coe_composablePairs I J C).contMDiff_iff_comp.mpr
    (contMDiff_id.prodMk
      ((contMDiff_unit (I := I) (J := J) (C := C)).comp (contMDiff_target I J C)))

/-- The diagonal unit degeneracy `x ↦ (1_x, 1_x)` into composable pairs is smooth. -/
theorem contMDiff_unitPair :
    letI := composablePairsChartedSpace I J C
    ContMDiff I 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (unitPair : C → ComposablePairs C) :=
  letI := composablePairsChartedSpace I J C
  (contMDiff_leftUnitPair I J C).comp (contMDiff_unit (I := I) (J := J) (C := C))

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
  have := secondCountableTopology_arrows (I := I) (J := J) (C := C)
  exact (IsTopologicalGroupoid.isEmbedding_unit C).isInducing.secondCountableTopology

include I J in
/-- Composable pairs form a second-countable space in their subspace topology. -/
theorem secondCountableTopology_composablePairs : SecondCountableTopology (ComposablePairs C) := by
  have := secondCountableTopology_arrows (I := I) (J := J) (C := C)
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
  exact ((inverseDiffeomorph I J C).toHomeomorph.subtype
    (p := fun a ↦ a.left = x) (q := fun a ↦ a.right = x) fun _ ↦ Iff.rfl).t2Space

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
  exact ((isSubmersion_source (I := I) (J := J) (C := C)).isSubmersionAt
    ⟨x, x, 𝟙 x⟩).finrank_le (by simp)

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
    IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C) :=
  (isSubmersion_source (I := I) (J := J) (C := C)).isLocalDiffeomorph hdim (by simp)

/-- On a nonempty Lie groupoid, the arrow and object manifolds have equal dimension if and only if
source is a smooth local diffeomorphism (the étale case). -/
theorem finrank_arrows_eq_iff_isLocalDiffeomorph_source [Nonempty C] :
    finrank ℝ E' = finrank ℝ E ↔
      IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C) := by
  refine ⟨isLocalDiffeomorph_source_of_finrank_eq I J C, fun h ↦ ?_⟩
  obtain ⟨x⟩ := ‹Nonempty C›
  rw [← finrank_tangentSpace (I := J) (⟨x, x, 𝟙 x⟩ : Quiver.Total C),
    ← finrank_tangentSpace (I := I) x]
  exact ((h ⟨x, x, 𝟙 x⟩).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv.finrank_eq

/-! ### Tangent identities at units -/

section TangentIdentities

variable {I J C}

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
  refine eq_of_tangentSpaceCast_eq (inverseDiffeomorph_unit I J C x) ?_
  exact (tangentSpaceCast_mfderiv_comp
    (((inverseDiffeomorph I J C).contMDiff _).mdifferentiableAt (by simp))
    ((contMDiff_unit (I := I) (J := J) (C := C) x).mdifferentiableAt (by simp))
    (funext (inverseDiffeomorph_unit I J C)) ⟨x, x, 𝟙 x⟩ v).trans (tangentSpaceCast_self _ _)

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

/-- For any tangent vector `w` of `ComposablePairs C` at `p`, the target differential of its first
arrow projection agrees (up to `tangentSpaceCast` along `p.2`) with the source differential of its
second arrow projection. -/
theorem mfderiv_target_mfderiv_fst_composablePairs (p : ComposablePairs C) :
    letI := composablePairsChartedSpace I J C
    ∀ w : TangentSpace 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) p,
      mfderiv J I Quiver.Total.right p.1.1
        (mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
          (fun q : ComposablePairs C ↦ q.1.1) p w) =
        tangentSpaceCast I p.1.2.left p.1.1.right
          (mfderiv J I Quiver.Total.left p.1.2
            (mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
              (fun q : ComposablePairs C ↦ q.1.2) p w)) := by
  let := composablePairsChartedSpace I J C
  intro w
  have hval := ((isSmoothEmbedding_coe_composablePairs I J C).contMDiff p).mdifferentiableAt
    (by simp)
  have hmem := (mem_range_mfderiv_coe_composablePairs_iff I J C p
    (mfderiv _ (J.prod J) Subtype.val p w)).mp ⟨w, rfl⟩
  rwa [← hval.mfderiv_fst_apply, ← hval.mfderiv_snd_apply] at hmem

/-- Every tangent vector `w` to `ComposablePairs C` at `(1_x, 1_x)` decomposes along the right-unit,
left-unit, and diagonal-unit sections as
`d(rightUnitPair)(v₁) + d(leftUnitPair)(v₂) - d(unitPair)(dt v₁)`, where `v₁` and `v₂` are the two
arrow projections of `w`. -/
theorem mfderiv_composablePairs_at_unit_decomp (x : C) :
    letI := composablePairsChartedSpace I J C
    ∀ w : TangentSpace 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) (unitPair x),
      w = mfderiv J 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
            rightUnitPair ⟨x, x, 𝟙 x⟩
            (mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
              (fun p : ComposablePairs C ↦ p.1.1) (unitPair x) w) +
          mfderiv J 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
            leftUnitPair ⟨x, x, 𝟙 x⟩
            (mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
              (fun p : ComposablePairs C ↦ p.1.2) (unitPair x) w) -
          mfderiv I 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) unitPair x
            (mfderiv J I (Quiver.Total.right : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩
              (mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
                (fun p : ComposablePairs C ↦ p.1.1) (unitPair x) w)) := by
  let := composablePairsChartedSpace I J C
  let K := 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
  let u : C → Quiver.Total C := fun y ↦ ⟨y, y, 𝟙 y⟩
  let u₀ : Quiver.Total C := ⟨x, x, 𝟙 x⟩
  let π₁ : ComposablePairs C → Quiver.Total C := fun p ↦ p.1.1
  let π₂ : ComposablePairs C → Quiver.Total C := fun p ↦ p.1.2
  intro w
  let v₁ : TangentSpace J u₀ := mfderiv K J π₁ (unitPair x) w
  let v₂ : TangentSpace J u₀ := mfderiv K J π₂ (unitPair x) w
  let ξ : TangentSpace I x := mfderiv J I Quiver.Total.right u₀ v₁
  have hv_eq : ξ = mfderiv J I Quiver.Total.left u₀ v₂ :=
    (mfderiv_target_mfderiv_fst_composablePairs (unitPair x) w).trans (tangentSpaceCast_self _ _)
  have hπ₁_diff : MDifferentiableAt K J π₁ (unitPair x) :=
    ((contMDiff_fst_composablePairs I J C) (unitPair x)).mdifferentiableAt (by simp)
  have hπ₂_diff : MDifferentiableAt K J π₂ (unitPair x) :=
    ((contMDiff_snd_composablePairs I J C) (unitPair x)).mdifferentiableAt (by simp)
  have hσR_diff : MDifferentiableAt J K rightUnitPair u₀ :=
    ((contMDiff_rightUnitPair I J C) u₀).mdifferentiableAt (by simp)
  have hσL_diff : MDifferentiableAt J K leftUnitPair u₀ :=
    ((contMDiff_leftUnitPair I J C) u₀).mdifferentiableAt (by simp)
  have hσD_diff : MDifferentiableAt I K unitPair x :=
    ((contMDiff_unitPair I J C) x).mdifferentiableAt (by simp)
  have hu_diff : MDifferentiableAt I J u x :=
    ((contMDiff_unit (I := I) (J := J) (C := C)) x).mdifferentiableAt (by simp)
  -- Check that `w` and the linear combination have equal first and second arrow differentials.
  refine sub_eq_zero.mp (eq_zero_of_mfderiv_composablePairs I J C (unitPair x) _ ?_ ?_)
  · -- First projection: `dπ₁` sends the terms to `v₁`, `du_x(ds v₂) = du_x(ξ)`, and `du_x(ξ)`.
    have h1 : mfderiv K J π₁ (unitPair x) (mfderiv J K rightUnitPair u₀ v₁) = v₁ := by
      have hid : π₁ ∘ rightUnitPair = id := rfl
      rw [← mfderiv_comp_apply u₀ hπ₁_diff hσR_diff v₁, hid, mfderiv_id,
        ContinuousLinearMap.id_apply]
    have h2 : mfderiv K J π₁ (unitPair x) (mfderiv J K leftUnitPair u₀ v₂) =
        mfderiv I J u x ξ := by
      have heq : π₁ ∘ leftUnitPair = u ∘ Quiver.Total.left := rfl
      rw [← mfderiv_comp_apply u₀ hπ₁_diff hσL_diff v₂, heq,
        mfderiv_comp_apply u₀ hu_diff
          (((contMDiff_source I J C) u₀).mdifferentiableAt (by simp)) v₂,
        ← hv_eq]
    have h3 : mfderiv K J π₁ (unitPair x) (mfderiv I K unitPair x ξ) = mfderiv I J u x ξ := by
      have heq : π₁ ∘ unitPair = u := rfl
      rw [← mfderiv_comp_apply x hπ₁_diff hσD_diff ξ, heq]
    dsimp only [π₁, v₁] at h1 h2 h3 ⊢
    rw [map_sub, map_sub, map_add, h1, h2, h3]
    abel
  · -- Second projection: `dπ₂` sends the three terms to `du_x(ξ)`, `v₂`, and `du_x(ξ)`.
    have h1 : mfderiv K J π₂ (unitPair x) (mfderiv J K rightUnitPair u₀ v₁) =
        mfderiv I J u x ξ := by
      have heq : π₂ ∘ rightUnitPair = u ∘ Quiver.Total.right := rfl
      rw [← mfderiv_comp_apply u₀ hπ₂_diff hσR_diff v₁, heq,
        mfderiv_comp_apply u₀ hu_diff
          (((contMDiff_target I J C) u₀).mdifferentiableAt (by simp)) v₁]
    have h2 : mfderiv K J π₂ (unitPair x) (mfderiv J K leftUnitPair u₀ v₂) = v₂ := by
      have hid : π₂ ∘ leftUnitPair = id := rfl
      rw [← mfderiv_comp_apply u₀ hπ₂_diff hσL_diff v₂, hid, mfderiv_id,
        ContinuousLinearMap.id_apply]
    have h3 : mfderiv K J π₂ (unitPair x) (mfderiv I K unitPair x ξ) = mfderiv I J u x ξ := by
      have heq : π₂ ∘ unitPair = u := rfl
      rw [← mfderiv_comp_apply x hπ₂_diff hσD_diff ξ, heq]
    dsimp only [π₂, v₂] at h1 h2 h3 ⊢
    rw [map_sub, map_sub, map_add, h1, h2, h3]
    abel

private theorem tangentSpaceCast_mfderiv_comp_at_unit (x : C) :
    letI := composablePairsChartedSpace I J C
    ∀ w : TangentSpace 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) (unitPair x),
      tangentSpaceCast J ((unitPair x).1.1.comp (unitPair x).1.2 (unitPair x).2) ⟨x, x, 𝟙 x⟩
        (mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
          (fun p : ComposablePairs C ↦ p.1.1.comp p.1.2 p.2) (unitPair x) w) =
        mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
          (fun p : ComposablePairs C ↦ p.1.1) (unitPair x) w +
        mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
          (fun p : ComposablePairs C ↦ p.1.2) (unitPair x) w -
        mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x
          (mfderiv J I (Quiver.Total.right : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩
            (mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
              (fun p : ComposablePairs C ↦ p.1.1) (unitPair x) w)) := by
  let := composablePairsChartedSpace I J C
  let K := 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
  let m : ComposablePairs C → Quiver.Total C := fun p ↦ p.1.1.comp p.1.2 p.2
  let u : C → Quiver.Total C := fun y ↦ ⟨y, y, 𝟙 y⟩
  let u₀ : Quiver.Total C := ⟨x, x, 𝟙 x⟩
  intro w
  let v₁ := mfderiv K J (fun p : ComposablePairs C ↦ p.1.1) (unitPair x) w
  let v₂ := mfderiv K J (fun p : ComposablePairs C ↦ p.1.2) (unitPair x) w
  let ξ := mfderiv J I (Quiver.Total.right : Quiver.Total C → C) u₀ v₁
  have hm_diff : MDifferentiableAt K J m (unitPair x) :=
    ((contMDiff_composablePairs_comp I J C) (unitPair x)).mdifferentiableAt (by simp)
  have hw := congrArg
    (fun z ↦ tangentSpaceCast J (m (unitPair x)) u₀ (mfderiv K J m (unitPair x) z))
    (mfderiv_composablePairs_at_unit_decomp x w)
  dsimp only at hw
  rw [map_sub, map_sub, map_add, map_add] at hw
  have hR : tangentSpaceCast J (m (unitPair x)) u₀
      (mfderiv K J m (unitPair x) (mfderiv J K rightUnitPair u₀ v₁)) = v₁ :=
    tangentSpaceCast_mfderiv_comp_id hm_diff
      (((contMDiff_rightUnitPair I J C) u₀).mdifferentiableAt (by simp))
      (funext comp_rightUnitPair) v₁
  have hL : tangentSpaceCast J (m (unitPair x)) u₀
      (mfderiv K J m (unitPair x) (mfderiv J K leftUnitPair u₀ v₂)) = v₂ :=
    tangentSpaceCast_mfderiv_comp_id hm_diff
      (((contMDiff_leftUnitPair I J C) u₀).mdifferentiableAt (by simp))
      (funext comp_leftUnitPair) v₂
  have hD : tangentSpaceCast J (m (unitPair x)) u₀
      (mfderiv K J m (unitPair x) (mfderiv I K unitPair x ξ)) = mfderiv I J u x ξ :=
    (tangentSpaceCast_mfderiv_comp hm_diff
      (((contMDiff_unitPair I J C) x).mdifferentiableAt (by simp))
      (funext comp_unitPair) u₀ ξ).trans (tangentSpaceCast_self _ _)
  exact hw.trans (congrArg₂ HSub.hSub (congrArg₂ HAdd.hAdd hR hL) hD)

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
  let := composablePairsChartedSpace I J C
  intro w
  exact eq_of_tangentSpaceCast_eq (comp_unitPair x) (tangentSpaceCast_mfderiv_comp_at_unit x w)

/-- **Differential of inversion at a unit.** For every arrow tangent vector `v` at `1_x`,
`d(inv)_{1_x}(v) = du_x(ds(v) + dt(v)) - v`. -/
theorem mfderiv_inverse_at_unit (x : C) (v : TangentSpace J (⟨x, x, 𝟙 x⟩ : Quiver.Total C)) :
    mfderiv J J (inverseDiffeomorph I J C) ⟨x, x, 𝟙 x⟩ v =
      mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x
        (mfderiv J I (Quiver.Total.left : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩ v +
          mfderiv J I (Quiver.Total.right : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩ v) - v := by
  let := composablePairsChartedSpace I J C
  let K := 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
  let u : C → Quiver.Total C := fun y ↦ ⟨y, y, 𝟙 y⟩
  let u₀ : Quiver.Total C := ⟨x, x, 𝟙 x⟩
  let π₁ : ComposablePairs C → Quiver.Total C := fun p ↦ p.1.1
  let π₂ : ComposablePairs C → Quiver.Total C := fun p ↦ p.1.2
  let m : ComposablePairs C → Quiver.Total C := fun p ↦ p.1.1.comp p.1.2 p.2
  let τ : Quiver.Total C → ComposablePairs C := fun a ↦ ⟨(a, inverseDiffeomorph I J C a), rfl⟩
  refine eq_of_tangentSpaceCast_eq (inverseDiffeomorph_unit I J C x) ?_
  have hτ : ContMDiff J K ∞ τ :=
    (isSmoothEmbedding_coe_composablePairs I J C).contMDiff_iff_comp.mpr
      (contMDiff_id.prodMk (inverseDiffeomorph I J C).contMDiff)
  have hτ_diff : MDifferentiableAt J K τ u₀ := (hτ u₀).mdifferentiableAt (by simp)
  have hτ0 : τ u₀ = unitPair x := Subtype.ext (Prod.ext rfl (inverseDiffeomorph_unit I J C x))
  -- Transport `tangentSpaceCast_mfderiv_comp_at_unit` across `τ u₀ = unitPair x`.
  have h_at_q : ∀ (q : ComposablePairs C), q = unitPair x → ∀ w : TangentSpace K q,
      tangentSpaceCast J (m q) u₀ (mfderiv K J m q w) =
        tangentSpaceCast J (π₁ q) u₀ (mfderiv K J π₁ q w) +
          tangentSpaceCast J (π₂ q) u₀ (mfderiv K J π₂ q w) -
          mfderiv I J u x (mfderiv J I Quiver.Total.right u₀
            (tangentSpaceCast J (π₁ q) u₀ (mfderiv K J π₁ q w))) := by
    rintro _ rfl w
    simpa only [π₁, π₂, m, u, u₀, tangentSpaceCast_self] using
      tangentSpaceCast_mfderiv_comp_at_unit x w
  have hrhs := h_at_q (τ u₀) hτ0 (mfderiv J K τ u₀ v)
  have h1 : tangentSpaceCast J (π₁ (τ u₀)) u₀
      (mfderiv K J π₁ (τ u₀) (mfderiv J K τ u₀ v)) = v := by
    have hid : π₁ ∘ τ = id := rfl
    rw [← mfderiv_comp_apply u₀
      (((contMDiff_fst_composablePairs I J C) (τ u₀)).mdifferentiableAt (by simp)) hτ_diff v,
      hid, mfderiv_id, ContinuousLinearMap.id_apply]
    exact tangentSpaceCast_self u₀ v
  have h2 : mfderiv K J π₂ (τ u₀) (mfderiv J K τ u₀ v) =
      mfderiv J J (inverseDiffeomorph I J C) u₀ v :=
    (mfderiv_comp_apply u₀
      (((contMDiff_snd_composablePairs I J C) (τ u₀)).mdifferentiableAt (by simp)) hτ_diff v).symm
  have hlhs : tangentSpaceCast J (m (τ u₀)) u₀ (mfderiv K J m (τ u₀) (mfderiv J K τ u₀ v)) =
      mfderiv I J u x (mfderiv J I Quiver.Total.left u₀ v) := by
    have hm_τ := tangentSpaceCast_mfderiv_comp
      (((contMDiff_composablePairs_comp I J C) (τ u₀)).mdifferentiableAt (by simp)) hτ_diff
      (funext Quiver.Total.comp_inv) u₀ v
    have hu_s : mfderiv J J (u ∘ Quiver.Total.left) u₀ v =
        mfderiv I J u x (mfderiv J I Quiver.Total.left u₀ v) :=
      mfderiv_comp_apply u₀ (((contMDiff_unit (I := I) (J := J) (C := C)) x).mdifferentiableAt
        (by simp)) (((contMDiff_source I J C) u₀).mdifferentiableAt (by simp)) v
    exact hm_τ.trans ((tangentSpaceCast_self u₀ _).trans hu_s)
  rw [hlhs, h1, h2] at hrhs
  rw [map_add]
  exact eq_sub_of_add_eq' (eq_add_of_sub_eq hrhs.symm)

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
