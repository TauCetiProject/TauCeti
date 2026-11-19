/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Submersion
public import TauCeti.Geometry.Manifold.Submersion.Basic
public import TauCeti.Topology.CategoryTheory.Groupoid.Basic
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
import TauCeti.Geometry.Manifold.SmoothEmbedding.LeftInverse
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph

/-!
# Lie groupoids

A Lie groupoid is a groupoid `C` whose objects form a smooth manifold `M`, modelled on `I`, and
whose total arrow type `Quiver.Total C` forms a smooth manifold `Γ`, modelled on `J`, such that
the source is a smooth submersion, the units and inversion are smooth, and composition is smooth
on the manifold of composable pairs. Both models are finite-dimensional real and boundaryless.
As for `TauCeti.IsTopologicalGroupoid`, the groupoid structure is the categorical one: the
smooth atlases are additional data on the objects and on the total arrows, and composition is
`Quiver.Total.comp`, so `a.comp b h` first traverses `a`, then `b`.

The composable pairs `{p : Γ × Γ // p.1.right = p.2.left}` are the fibre product of the target
and the source. Since the source is a submersion the two are transverse, and the composable pairs
carry the transverse fibre-product atlas `TauCeti.composablePairsChartedSpace`, of dimension
`2 dim Γ - dim M`, with the subspace topology of `Γ × Γ`. Composition is required to be smooth for
this atlas. By the universal property of the embedded fibre product
(`TauCeti.contMDiff_composablePairs_iff`), this says that `x ↦ (a x).comp (b x) _` is smooth
whenever `a` and `b` are smooth maps into `Γ` with `right ∘ a = left ∘ b`
(`ContMDiff.totalComp`). Conversely, composition is smooth as soon as it is the restriction of a
smooth map on `Γ × Γ` (`TauCeti.contMDiff_composablePairs_comp_of_eq`).

The object manifold is required to be Hausdorff. The arrow manifold need not be: it is locally
Hausdorff through its charts and is required to be second-countable, while each source fibre
`{a : Γ // a.left = x}` is required to be Hausdorff in its subspace topology. This is the setting
of Crainic and Fernandes, which admits the non-Hausdorff integrations of regular foliations.

From the axioms, inversion is a diffeomorphism (`TauCeti.LieGroupoid.inverseDiffeomorph`),
which exchanges source and target, so the target is a submersion as well
(`TauCeti.LieGroupoid.isSubmersion_target`). Both are open maps, and forgetting the smooth
structure leaves a topological groupoid (`TauCeti.LieGroupoid.isTopologicalGroupoid`). The unit
map is a smooth embedding (`TauCeti.LieGroupoid.isSmoothEmbedding_unit`). For nonempty `M`,
`dim M ≤ dim Γ`, and equality holds exactly when the source is a local diffeomorphism, the étale
case (`TauCeti.LieGroupoid.isLocalDiffeomorph_source_iff_finrank_eq`).

The unit and pair groupoids of a manifold are Lie groupoids, in
`TauCeti.Geometry.Manifold.Groupoid.Examples`.

## Main definitions

* `TauCeti.composablePairsChartedSpace`: the atlas of the manifold of composable pairs.
* `TauCeti.LieGroupoid`: the Lie groupoid axioms on a groupoid with smooth atlases on objects and
  total arrows.
* `TauCeti.LieGroupoid.inverseDiffeomorph`: inversion as a diffeomorphism of the arrow manifold.

## References

* K. C. H. Mackenzie, *General theory of Lie groupoids and Lie algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), Definition 1.1.3.
* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Cambridge Stud. Adv.
  Math. 91, Cambridge University Press (2003), Section 5.1.
* M. Crainic and R. L. Fernandes, *Integrability of Lie brackets*, Ann. of Math. 157 (2003),
  575–620, Section 1.
-/

public section

open CategoryTheory Function Manifold Module Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {E H E' H' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H') [I.Boundaryless] [J.Boundaryless]
  (C : Type*) [Category C] [IsGroupoid C] [TopologicalSpace C] [ChartedSpace H C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
  [IsManifold I ∞ C] [IsManifold J ∞ (Quiver.Total C)]

section ComposablePairs

variable {I J C}
  (hs : IsSubmersion J I ∞ (Quiver.Total.left : Quiver.Total C → C))
  (hi : ContMDiff J J ∞ fun a : Quiver.Total C ↦ (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total C))

/-- The atlas of the manifold of composable pairs `{p : Γ × Γ // p.1.right = p.2.left}` of a
groupoid with smooth submersive source and smooth inversion: the transverse fibre product of the
target (the source composed with inversion) and the source, of dimension `2 dim Γ - dim M`, with
the subspace topology of `Γ × Γ`. It is not an instance, since it depends on these hypotheses. -/
@[instance_reducible]
noncomputable def composablePairsChartedSpace :
    ChartedSpace (Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
      {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} :=
  transverseFiberProductChartedSpace (by simp) (f := (Quiver.Total.right : Quiver.Total C → C))
    (hs.contMDiff.comp hi) hs.contMDiff fun p _ ↦
      transverse_of_surjective_mfderiv_right _ p (hs.surjective_mfderiv (by simp) p.2)

/-- The composable pairs form a smooth manifold. -/
theorem isManifold_composablePairs :
    letI := composablePairsChartedSpace hs hi
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} :=
  isManifold_transverseFiberProduct ..

/-- The inclusion of the composable pairs into `Γ × Γ` is a smooth embedding. -/
theorem isSmoothEmbedding_coe_composablePairs :
    letI := composablePairsChartedSpace hs hi
    IsSmoothEmbedding 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) (J.prod J) ∞
      (Subtype.val : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} →
        Quiver.Total C × Quiver.Total C) :=
  isSmoothEmbedding_coe_transverseFiberProduct ..

/-- **The universal property of the composable pairs.** A map into the manifold of composable
pairs is `C^n`, for `n ≤ ∞`, exactly when both of its arrows are `C^n` functions of the point. -/
theorem contMDiff_composablePairs_iff {F G X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] {K : ModelWithCorners ℝ F G} [TopologicalSpace X] [ChartedSpace G X]
    {n : ℕ∞ω} (hn : n ≤ ∞)
    {f : X → {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left}} :
    letI := composablePairsChartedSpace hs hi
    ContMDiff K 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) n f ↔
      ContMDiff K J n (fun x ↦ (f x).val.1) ∧ ContMDiff K J n (fun x ↦ (f x).val.2) := by
  let := composablePairsChartedSpace hs hi
  have := isManifold_composablePairs hs hi
  rw [(isSmoothEmbedding_coe_composablePairs hs hi).of_le hn |>.contMDiff_iff_comp,
    contMDiff_prod_iff]
  rfl

/-- Composition is smooth on the manifold of composable pairs as soon as it is the restriction of
a smooth map on `Γ × Γ`. -/
theorem contMDiff_composablePairs_comp_of_eq
    {Φ : Quiver.Total C × Quiver.Total C → Quiver.Total C}
    (hΦ : ContMDiff (J.prod J) J ∞ Φ)
    (h : ∀ p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left},
      p.val.1.comp p.val.2 p.property = Φ p.val) :
    letI := composablePairsChartedSpace hs hi
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
        p.val.1.comp p.val.2 p.property := by
  let := composablePairsChartedSpace hs hi
  simp only [h]
  exact hΦ.comp (isSmoothEmbedding_coe_composablePairs hs hi).contMDiff

end ComposablePairs

/-- A **Lie groupoid**: a groupoid `C` whose objects form a smooth manifold modelled on `I` and
whose total arrows form a smooth manifold modelled on `J`, with smooth submersive source, smooth
units and inversion, and composition smooth on the transverse fibre product of target and source.
The object manifold is Hausdorff, the arrow manifold is second-countable, and each source fibre
is Hausdorff in its subspace topology; the arrow manifold itself need not be Hausdorff. -/
class LieGroupoid : Prop where
  /-- The source map is a smooth submersion. -/
  isSubmersion_source : IsSubmersion J I ∞ (Quiver.Total.left : Quiver.Total C → C)
  /-- The unit map is smooth. -/
  contMDiff_unit : ContMDiff I J ∞ fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C)
  /-- Inversion is smooth. -/
  contMDiff_inverse : ContMDiff J J ∞ fun a : Quiver.Total C ↦
    (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total C)
  /-- Composition is smooth on the manifold of composable pairs. -/
  contMDiff_comp :
    letI := composablePairsChartedSpace isSubmersion_source contMDiff_inverse
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
        p.val.1.comp p.val.2 p.property
  /-- The object manifold is Hausdorff. -/
  t2Space_objects : T2Space C
  /-- The arrow manifold is second-countable. -/
  secondCountableTopology_arrows : SecondCountableTopology (Quiver.Total C)
  /-- Every source fibre is Hausdorff. -/
  t2Space_sourceFiber (x : C) : T2Space {a : Quiver.Total C // a.left = x}

namespace LieGroupoid

variable [LieGroupoid I J C]

/-- The source map of a Lie groupoid is smooth. -/
theorem contMDiff_source : ContMDiff J I ∞ (Quiver.Total.left : Quiver.Total C → C) :=
  (isSubmersion_source (I := I) (J := J)).contMDiff

/-- The target map of a Lie groupoid is smooth: it is the source of the inverse arrow. -/
theorem contMDiff_target : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C) :=
  (contMDiff_source I J C).comp (contMDiff_inverse (I := I))

/-- Inversion, as a diffeomorphism of the arrow manifold. It exchanges source and target. -/
noncomputable def inverseDiffeomorph : Quiver.Total C ≃ₘ^∞⟮J, J⟯ Quiver.Total C where
  toFun a := ⟨a.right, a.left, inv a.hom⟩
  invFun a := ⟨a.right, a.left, inv a.hom⟩
  left_inv a := by cases a; simp
  right_inv a := by cases a; simp
  contMDiff_toFun := contMDiff_inverse (I := I)
  contMDiff_invFun := contMDiff_inverse (I := I)

@[simp]
theorem inverseDiffeomorph_apply (a : Quiver.Total C) :
    inverseDiffeomorph I J C a = ⟨a.right, a.left, inv a.hom⟩ := (rfl)

@[simp]
theorem inverseDiffeomorph_symm : (inverseDiffeomorph I J C).symm = inverseDiffeomorph I J C :=
  (rfl)

/-- The target map of a Lie groupoid is a smooth submersion. -/
theorem isSubmersion_target : IsSubmersion J I ∞ (Quiver.Total.right : Quiver.Total C → C) :=
  (inverseDiffeomorph I J C).isLocalDiffeomorph.isSubmersion_comp (isSubmersion_source (I := I))

end LieGroupoid

/-- In a Lie groupoid, composing arrows which depend smoothly on a point gives an arrow which
depends smoothly on the point. -/
theorem _root_.ContMDiff.totalComp [LieGroupoid I J C] {F G X : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace G] {K : ModelWithCorners ℝ F G} [TopologicalSpace X]
    [ChartedSpace G X] {n : ℕ∞ω} (hn : n ≤ ∞) {a b : X → Quiver.Total C} (ha : ContMDiff K J n a)
    (hb : ContMDiff K J n b) (h : ∀ x, (a x).right = (b x).left) :
    ContMDiff K J n fun x ↦ (a x).comp (b x) (h x) := by
  have hs := LieGroupoid.isSubmersion_source (I := I) (J := J) (C := C)
  have hi := LieGroupoid.contMDiff_inverse (I := I) (J := J) (C := C)
  let := composablePairsChartedSpace hs hi
  have hp := (contMDiff_composablePairs_iff hs hi hn (f := fun x ↦ ⟨(a x, b x), h x⟩)).2 ⟨ha, hb⟩
  exact ((LieGroupoid.contMDiff_comp (I := I)).of_le hn).comp hp

namespace LieGroupoid

variable [LieGroupoid I J C]

include I J in
/-- Forgetting the smooth structure of a Lie groupoid leaves a topological groupoid. This is not
an instance, since the models `I` and `J` cannot be inferred. -/
theorem isTopologicalGroupoid : IsTopologicalGroupoid C where
  continuous_source := (contMDiff_source I J C).continuous
  continuous_target := (contMDiff_target I J C).continuous
  continuous_unit := (contMDiff_unit (I := I) (J := J)).continuous
  continuous_inverse := (contMDiff_inverse (I := I) (J := J)).continuous
  continuous_comp := by
    let := composablePairsChartedSpace (isSubmersion_source (I := I) (J := J) (C := C))
      (contMDiff_inverse (I := I))
    exact (contMDiff_comp (I := I) (J := J)).continuous

include I J in
/-- The source of a Lie groupoid is an open map. -/
theorem isOpenMap_source : IsOpenMap (Quiver.Total.left : Quiver.Total C → C) :=
  (isSubmersion_source (I := I) (J := J)).isOpenMap

include I J in
/-- The target of a Lie groupoid is an open map. -/
theorem isOpenMap_target : IsOpenMap (Quiver.Total.right : Quiver.Total C → C) :=
  (isSubmersion_target I J C).isOpenMap

/-- The unit map of a Lie groupoid is a smooth embedding of the object manifold into the arrow
manifold; the source is a smooth left inverse. -/
theorem isSmoothEmbedding_unit :
    IsSmoothEmbedding I J ∞ fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C) :=
  (contMDiff_unit (I := I) (J := J)).isSmoothEmbedding_of_leftInverse (by simp)
    ((contMDiff_source I J C).of_le (by simp)) fun _ ↦ rfl

/-- The differential of the source of a Lie groupoid is surjective at every arrow. -/
theorem surjective_mfderiv_source (a : Quiver.Total C) :
    Surjective (mfderiv J I (Quiver.Total.left : Quiver.Total C → C) a) :=
  (isSubmersion_source (I := I)).surjective_mfderiv (by simp) a

/-- The differential of the target of a Lie groupoid is surjective at every arrow. -/
theorem surjective_mfderiv_target (a : Quiver.Total C) :
    Surjective (mfderiv J I (Quiver.Total.right : Quiver.Total C → C) a) :=
  (isSubmersion_target I J C).surjective_mfderiv (by simp) a

include I J in
/-- The arrow manifold of a Lie groupoid over a nonempty object manifold has dimension at least
that of the object manifold. -/
theorem finrank_le [Nonempty C] : finrank ℝ E ≤ finrank ℝ E' :=
  have : Nonempty (Quiver.Total C) := ‹Nonempty C›.map fun x ↦ ⟨x, x, 𝟙 x⟩
  (isSubmersion_source (I := I) (J := J) (C := C)).finrank_le (by simp)

/-- **Étale Lie groupoids.** The source of a Lie groupoid over a nonempty object manifold is a
local diffeomorphism exactly when the arrow manifold has the dimension of the object manifold. -/
theorem isLocalDiffeomorph_source_iff_finrank_eq [Nonempty C] :
    IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C) ↔
      finrank ℝ E = finrank ℝ E' :=
  have : Nonempty (Quiver.Total C) := ‹Nonempty C›.map fun x ↦ ⟨x, x, 𝟙 x⟩
  ((isSubmersion_source (I := I)).isLocalDiffeomorph_iff_finrank_eq (by simp)).trans eq_comm

end LieGroupoid

end TauCeti
