/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.LinearAlgebra.Projection
public import TauCeti.Geometry.Manifold.FiberProduct.Manifold
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Geometry.Manifold.Submersion.Open
public import TauCeti.Topology.CategoryTheory.Groupoid.Basic
import TauCeti.Geometry.Manifold.SmoothEmbedding.LeftInverse
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# Lie groupoids on total arrows

`TauCeti.IsLieGroupoid` equips a categorical groupoid `C` whose objects and total arrows
`Quiver.Total C` carry finite-dimensional boundaryless smooth manifold structures with smooth
groupoid operations: source and target are smooth submersions, units and inversion are smooth,
multiplication `(g, h) ↦ gh = h ≫ g` is smooth on the transverse fibre product of source and
target (`TauCeti.IsLieGroupoid.composablePairsChartedSpace`), and every source fibre is Hausdorff.
No global Hausdorffness of `Quiver.Total C` is assumed, though every point has an open Hausdorff
chart neighbourhood (`ModelWithCorners.exists_isOpen_mem_t2Space`). Forgetting smoothness recovers a
topological groupoid (`TauCeti.IsLieGroupoid.isTopologicalGroupoid`).

Source and target are open maps, with `dim C ≤ dim (Quiver.Total C)` on nonempty bases and equality
characterizing étale Lie groupoids. Inversion is a diffeomorphism
(`TauCeti.IsLieGroupoid.inverseDiffeomorph`), units form a smooth embedding
(`TauCeti.IsLieGroupoid.isSmoothEmbedding_unit`), `T_{1_x} (Quiver.Total C)` splits as
`range(du_x) ⊕ ker(ds_{1_x})`, and `d(inv)_{1_x} ξ = du_x (dt_{1_x} ξ) - ξ` on `ker(ds_{1_x})`
(`TauCeti.IsLieGroupoid.mfderiv_inverse_eq_of_mem_ker_source`).

## References

* I. Moerdijk and J. Mrčun, *Introduction to Foliations and Lie Groupoids*, Cambridge University
  Press (2003), Section 5.1.
* K. C. H. Mackenzie, *General Theory of Lie Groupoids and Lie Algebroids*, Cambridge University
  Press (2005), Section 1.1.
* M. Crainic and R. L. Fernandes, *Integrability of Lie brackets*, Ann. of Math. (2) 157 (2003),
  575–620, Section 2.1.
-/

public section

open CategoryTheory Function Module Set Topology
open scoped Manifold ContDiff

/-- Every point of a space charted over a model with corners in a normed space admits an open
Hausdorff chart neighbourhood, even when the ambient space is not globally Hausdorff. -/
theorem ModelWithCorners.exists_isOpen_mem_t2Space
    {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
    [TopologicalSpace M] [ChartedSpace H M] (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ T2Space U :=
  have : T2Space H := I.isClosedEmbedding.isEmbedding.t2Space
  ⟨(chartAt H x).source, (chartAt H x).open_source, mem_chart_source H x,
    (chartAt H x).toHomeomorphSourceTarget.symm.t2Space⟩

namespace TauCeti

/-- A Lie groupoid on a finite-dimensional boundaryless object manifold `C` with finite-dimensional
boundaryless total-arrow manifold `Quiver.Total C`: source and target are smooth submersions, units
and inversion are smooth, multiplication `(g, h) ↦ gh = h ≫ g` is smooth on the transverse fibre
product of source and target, and every source fibre is Hausdorff in its subspace topology. -/
class IsLieGroupoid
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H') [J.Boundaryless]
    (C : Type*) [Category C] [IsGroupoid C]
    [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C]
    [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
    [IsManifold J ∞ (Quiver.Total C)] : Prop where
  /-- Source is a smooth submersion. -/
  isSubmersion_source : Manifold.IsSubmersion J I ∞ (Quiver.Total.left : Quiver.Total C → C)
  /-- Target is a smooth submersion. -/
  isSubmersion_target : Manifold.IsSubmersion J I ∞ (Quiver.Total.right : Quiver.Total C → C)
  /-- The unit map sending each object to its identity arrow is smooth. -/
  contMDiff_unit : ContMDiff I J ∞ fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C)
  /-- Arrow inversion is smooth. -/
  contMDiff_inverse : ContMDiff J J ∞ fun a : Quiver.Total C ↦
    (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total C)
  /-- Groupoid multiplication `(g, h) ↦ gh = h ≫ g` is smooth on composable pairs. -/
  contMDiff_mul :
    letI := transverseFiberProductChartedSpace (by simp : (1 : ℕ∞ω) ≤ ∞)
      isSubmersion_source.contMDiff isSubmersion_target.contMDiff
      (transverse_of_isSubmersion_left isSubmersion_source (by simp))
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      fun p : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} ↦
        p.1.2.comp p.1.1 p.2.symm
  /-- Every source fibre is Hausdorff in its subspace topology. -/
  t2Space_sourceFiber (x : C) : T2Space {a : Quiver.Total C // a.left = x}

namespace IsLieGroupoid

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H') [J.Boundaryless]
  (C : Type*) [Category C] [IsGroupoid C] [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
  [IsManifold J ∞ (Quiver.Total C)] [IsLieGroupoid I J C]

/-- The source map of a Lie groupoid is smooth. -/
theorem contMDiff_source : ContMDiff J I ∞ (Quiver.Total.left : Quiver.Total C → C) :=
  (isSubmersion_source (I := I) (J := J) (C := C)).contMDiff

/-- The target map of a Lie groupoid is smooth. -/
theorem contMDiff_target : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C) :=
  (isSubmersion_target (I := I) (J := J) (C := C)).contMDiff

/-- The transverse fibre-product smooth atlas on composable pairs `(g, h)` with `s(g) = t(h)`, of
dimension `2 dim (Quiver.Total C) - dim C`. It uses the subspace topology and is not a global
instance. -/
@[instance_reducible]
noncomputable def composablePairsChartedSpace :
    ChartedSpace (Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
      {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} :=
  transverseFiberProductChartedSpace (by simp : (1 : ℕ∞ω) ≤ ∞)
    (contMDiff_source I J C) (contMDiff_target I J C)
    (transverse_of_isSubmersion_left (isSubmersion_source (I := I) (J := J) (C := C)) (by simp))

/-- Composable pairs with their transverse fibre-product atlas form a smooth manifold. -/
theorem isManifold_composablePairs :
    letI := composablePairsChartedSpace I J C
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} :=
  isManifold_transverseFiberProduct (by simp : (1 : ℕ∞ω) ≤ ∞)
    (contMDiff_source I J C) (contMDiff_target I J C)
    (transverse_of_isSubmersion_left (isSubmersion_source (I := I) (J := J) (C := C)) (by simp))

/-- Inclusion of composable pairs into the product of arrow manifolds is a smooth embedding. -/
theorem isSmoothEmbedding_coe_composablePairs :
    letI := composablePairsChartedSpace I J C
    Manifold.IsSmoothEmbedding
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) (J.prod J) ∞
      (Subtype.val : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} →
        Quiver.Total C × Quiver.Total C) :=
  isSmoothEmbedding_coe_transverseFiberProduct (by simp : (1 : ℕ∞ω) ≤ ∞)
    (contMDiff_source I J C) (contMDiff_target I J C)
    (transverse_of_isSubmersion_left (isSubmersion_source (I := I) (J := J) (C := C)) (by simp))

/-- Definitional unfolding of `composablePairsChartedSpace` as `transverseFiberProductChartedSpace`,
for downstream theorems phrased on general transverse fibre products. -/
theorem composablePairsChartedSpace_eq :
    composablePairsChartedSpace I J C =
      transverseFiberProductChartedSpace (by simp : (1 : ℕ∞ω) ≤ ∞)
        (contMDiff_source I J C) (contMDiff_target I J C)
        (transverse_of_isSubmersion_left
          (isSubmersion_source (I := I) (J := J) (C := C)) (by simp)) := (rfl)

/-- Groupoid multiplication `(g, h) ↦ gh = h ≫ g` is smooth on `composablePairsChartedSpace`. -/
theorem contMDiff_mul_composablePairs :
    letI := composablePairsChartedSpace I J C
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (fun p : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} ↦
        p.1.2.comp p.1.1 p.2.symm) :=
  contMDiff_mul (I := I) (J := J) (C := C)

include I J in
/-- Forgetting the smooth atlases of a Lie groupoid gives a topological groupoid on the same
object and arrow topologies. -/
theorem isTopologicalGroupoid : IsTopologicalGroupoid C where
  continuous_source := (contMDiff_source I J C).continuous
  continuous_target := (contMDiff_target I J C).continuous
  continuous_unit := (contMDiff_unit (I := I) (J := J) (C := C)).continuous
  continuous_inverse := (contMDiff_inverse (I := I) (J := J) (C := C)).continuous
  continuous_comp := by
    let _ := composablePairsChartedSpace I J C
    have hswap : Continuous (fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
        (⟨(p.1.2, p.1.1), p.2.symm⟩ :
          {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right})) :=
      ((continuous_snd.comp continuous_subtype_val).prodMk
        (continuous_fst.comp continuous_subtype_val)).subtype_mk _
    exact ((contMDiff_mul (I := I) (J := J) (C := C)).continuous.comp hswap).congr fun _ ↦
      Quiver.Total.comp_congr rfl rfl _ _

include I J in
/-- The source map of a Lie groupoid is an open map. -/
theorem isOpenMap_source : IsOpenMap (Quiver.Total.left : Quiver.Total C → C) :=
  (isSubmersion_source (I := I) (J := J) (C := C)).isOpenMap

include I J in
/-- The target map of a Lie groupoid is an open map. -/
theorem isOpenMap_target : IsOpenMap (Quiver.Total.right : Quiver.Total C → C) :=
  (isSubmersion_target (I := I) (J := J) (C := C)).isOpenMap

include I J in
/-- On a Lie groupoid with nonempty object manifold, the arrow dimension is at least the object
dimension. -/
theorem finrank_le [Nonempty C] : finrank ℝ E ≤ finrank ℝ E' :=
  have : Nonempty (Quiver.Total C) := Nonempty.map (fun x : C ↦ ⟨x, x, 𝟙 x⟩) ‹Nonempty C›
  (isSubmersion_source (I := I) (J := J) (C := C)).finrank_le (by simp)

/-- Inversion in a Lie groupoid is a smooth diffeomorphism of the total arrow manifold. -/
noncomputable def inverseDiffeomorph : Quiver.Total C ≃ₘ^∞⟮J, J⟯ Quiver.Total C where
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

/-- Arrow inversion exchanges source with target: `s(a⁻¹) = t(a)`. -/
theorem left_inverseDiffeomorph (a : Quiver.Total C) :
    (inverseDiffeomorph I J C a).left = a.right := (rfl)

/-- Arrow inversion exchanges target with source: `t(a⁻¹) = s(a)`. -/
theorem right_inverseDiffeomorph (a : Quiver.Total C) :
    (inverseDiffeomorph I J C a).right = a.left := (rfl)

/-- Arrow inversion fixes every unit arrow. -/
theorem inverseDiffeomorph_unit (x : C) :
    inverseDiffeomorph I J C ⟨x, x, 𝟙 x⟩ = ⟨x, x, 𝟙 x⟩ := by simp [inverseDiffeomorph_apply]

/-- Arrow inversion reverses categorical composition of total arrows. -/
theorem inverseDiffeomorph_comp (a b : Quiver.Total C) (h : a.right = b.left) :
    inverseDiffeomorph I J C (a.comp b h) =
      (inverseDiffeomorph I J C b).comp (inverseDiffeomorph I J C a)
        ((right_inverseDiffeomorph I J C b).trans
          (h.symm.trans (left_inverseDiffeomorph I J C a).symm)) :=
  (Quiver.Total.inv_comp_eq a b h h.symm).trans (Quiver.Total.comp_congr rfl rfl _ _)

/-- Source is a smooth local diffeomorphism if and only if target is, since inversion exchanges
them. -/
theorem isLocalDiffeomorph_source_iff_target :
    IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C) ↔
      IsLocalDiffeomorph J I ∞ (Quiver.Total.right : Quiver.Total C → C) :=
  ⟨fun h a ↦ ((inverseDiffeomorph I J C).isLocalDiffeomorph a).comp I C (h _),
   fun h a ↦ ((inverseDiffeomorph I J C).isLocalDiffeomorph a).comp I C (h _)⟩

/-- On a Lie groupoid with nonempty object manifold, the source map is a smooth local
diffeomorphism (the étale case) if and only if the arrow and object models have equal dimension. -/
theorem isLocalDiffeomorph_source_iff_finrank_eq [Nonempty C] :
    IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C) ↔
      finrank ℝ E' = finrank ℝ E :=
  have : Nonempty (Quiver.Total C) := Nonempty.map (fun x : C ↦ ⟨x, x, 𝟙 x⟩) ‹Nonempty C›
  (isSubmersion_source (I := I) (J := J) (C := C)).isLocalDiffeomorph_iff_finrank_eq (by simp)

/-- On a Lie groupoid with nonempty object manifold, the target map is a smooth local
diffeomorphism if and only if the arrow and object models have equal dimension. -/
theorem isLocalDiffeomorph_target_iff_finrank_eq [Nonempty C] :
    IsLocalDiffeomorph J I ∞ (Quiver.Total.right : Quiver.Total C → C) ↔
      finrank ℝ E' = finrank ℝ E :=
  (isLocalDiffeomorph_source_iff_target I J C).symm.trans
    (isLocalDiffeomorph_source_iff_finrank_eq I J C)

private theorem mfderiv_comp_eq {E₁ H₁ M₁ E₂ H₂ M₂ E₃ H₃ M₃ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [TopologicalSpace H₃]
    {I₃ : ModelWithCorners ℝ E₃ H₃} [TopologicalSpace M₃] [ChartedSpace H₃ M₃]
    {g : M₂ → M₃} {f : M₁ → M₂} {k : M₁ → M₃} (hg : ContMDiff I₂ I₃ ∞ g)
    (hf : ContMDiff I₁ I₂ ∞ f) (h : g ∘ f = k) (x : M₁) (v : TangentSpace I₁ x) :
    mfderiv I₂ I₃ g (f x) (mfderiv I₁ I₂ f x v) = mfderiv I₁ I₃ k x v :=
  congrArg (· v) ((mfderiv_comp x (hg.mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp))).symm.trans
    (mfderiv_congr (I := I₁) (I' := I₃) (f' := k) h))

private theorem mfderiv_comp_id_eq {E₁ H₁ M₁ E₂ H₂ M₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    {g : M₂ → M₁} {f : M₁ → M₂} (hg : ContMDiff I₂ I₁ ∞ g) (hf : ContMDiff I₁ I₂ ∞ f)
    (h : g ∘ f = id) (x : M₁) (v : TangentSpace I₁ x) :
    mfderiv I₂ I₁ g (f x) (mfderiv I₁ I₂ f x v) = v :=
  (mfderiv_comp_eq hg hf h x v).trans (congrArg (· v) (mfderiv_id (I := I₁)))

private theorem isCompl_range_ker_of_leftInverse {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] {u : V →ₗ[ℝ] W} {p : W →ₗ[ℝ] V} (hpu : ∀ v, p (u v) = v) :
    IsCompl (LinearMap.range u) (LinearMap.ker p) := by
  have hinj : Injective u.rangeRestrict := fun v w hvw ↦
    (hpu v).symm.trans ((congrArg (fun z : LinearMap.range u ↦ p z.1) hvw).trans (hpu w))
  rw [← LinearMap.ker_comp_of_ker_eq_bot p (LinearMap.ker_eq_bot_of_injective hinj)]
  exact LinearMap.isCompl_of_proj fun ⟨_, v, rfl⟩ ↦ Subtype.ext (congrArg u (hpu v))

/-- At each unit arrow `1_x`, the differential of source is a left inverse to the differential of
the unit map: `ds_{1_x} ∘ du_x = id`. -/
@[simp]
theorem mfderiv_source_comp_unit (x : C) :
    (mfderiv J I Quiver.Total.left (⟨x, x, 𝟙 x⟩ : Quiver.Total C)).comp
      (mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x) =
      ContinuousLinearMap.id ℝ (TangentSpace I x) :=
  (mfderiv_comp x (((contMDiff_source I J C) ⟨x, x, 𝟙 x⟩).mdifferentiableAt (by simp))
    (((contMDiff_unit (I := I) (J := J) (C := C)) x).mdifferentiableAt (by simp))).symm.trans
    (mfderiv_id (I := I))

/-- Pointwise form of `ds_{1_x} (du_x v) = v`. -/
@[simp]
theorem mfderiv_source_unit_apply (x : C) (v : TangentSpace I x) :
    mfderiv J I Quiver.Total.left (⟨x, x, 𝟙 x⟩ : Quiver.Total C)
      (mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x v) = v :=
  congrArg (· v) (mfderiv_source_comp_unit I J C x)

/-- At each unit arrow `1_x`, the differential of target is a left inverse to the differential of
the unit map: `dt_{1_x} ∘ du_x = id`. -/
@[simp]
theorem mfderiv_target_comp_unit (x : C) :
    (mfderiv J I Quiver.Total.right (⟨x, x, 𝟙 x⟩ : Quiver.Total C)).comp
      (mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x) =
      ContinuousLinearMap.id ℝ (TangentSpace I x) :=
  (mfderiv_comp x (((contMDiff_target I J C) ⟨x, x, 𝟙 x⟩).mdifferentiableAt (by simp))
    (((contMDiff_unit (I := I) (J := J) (C := C)) x).mdifferentiableAt (by simp))).symm.trans
    (mfderiv_id (I := I))

/-- Pointwise form of `dt_{1_x} (du_x v) = v`. -/
@[simp]
theorem mfderiv_target_unit_apply (x : C) (v : TangentSpace I x) :
    mfderiv J I Quiver.Total.right (⟨x, x, 𝟙 x⟩ : Quiver.Total C)
      (mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x v) = v :=
  congrArg (· v) (mfderiv_target_comp_unit I J C x)

/-- The differential of source has a continuous linear right inverse at every arrow. -/
theorem hasRightInverse_mfderiv_source (a : Quiver.Total C) :
    (mfderiv J I Quiver.Total.left a).HasRightInverse :=
  (isSubmersion_source (I := I) (J := J) (C := C)).hasRightInverse_mfderiv (by simp) a

/-- The differential of target has a continuous linear right inverse at every arrow. -/
theorem hasRightInverse_mfderiv_target (a : Quiver.Total C) :
    (mfderiv J I Quiver.Total.right a).HasRightInverse :=
  (isSubmersion_target (I := I) (J := J) (C := C)).hasRightInverse_mfderiv (by simp) a

/-- **The unit map of a Lie groupoid is a smooth embedding**, retracted smoothly by `source`. -/
theorem isSmoothEmbedding_unit :
    Manifold.IsSmoothEmbedding I J ∞ (fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C)) :=
  (contMDiff_unit (I := I) (J := J) (C := C)).isSmoothEmbedding_of_leftInverse (by simp)
    ((contMDiff_source I J C).of_le (by simp)) fun _ ↦ rfl

/-- The unit map of a Lie groupoid as a bundled smooth embedding. -/
noncomputable def unitSmoothEmbedding : SmoothEmbedding I J ∞ C (Quiver.Total C) :=
  SmoothEmbedding.ofIsSmoothEmbedding _ (isSmoothEmbedding_unit I J C)

@[simp]
theorem unitSmoothEmbedding_apply (x : C) : unitSmoothEmbedding I J C x = ⟨x, x, 𝟙 x⟩ := by
  simp [unitSmoothEmbedding]

/-- **Tangent decomposition at units (source).** At `1_x`, `T_{1_x} (Quiver.Total C)` is the
internal direct sum of `range(du_x)` and `ker(ds_{1_x})`. -/
theorem isCompl_range_mfderiv_unit_ker_mfderiv_source (x : C) :
    IsCompl
      (LinearMap.range (mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x).toLinearMap)
      (LinearMap.ker
        (mfderiv J I Quiver.Total.left (⟨x, x, 𝟙 x⟩ : Quiver.Total C)).toLinearMap) :=
  isCompl_range_ker_of_leftInverse (mfderiv_source_unit_apply I J C x)

/-- **Tangent decomposition at units (target).** At `1_x`, `T_{1_x} (Quiver.Total C)` is the
internal direct sum of `range(du_x)` and `ker(dt_{1_x})`. -/
theorem isCompl_range_mfderiv_unit_ker_mfderiv_target (x : C) :
    IsCompl
      (LinearMap.range (mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x).toLinearMap)
      (LinearMap.ker
        (mfderiv J I Quiver.Total.right (⟨x, x, 𝟙 x⟩ : Quiver.Total C)).toLinearMap) :=
  isCompl_range_ker_of_leftInverse (mfderiv_target_unit_apply I J C x)

/-- Differentiating `s ∘ inv = t` identifies `ds_{a⁻¹} ∘ d(inv)_a` with `dt_a`. -/
theorem mfderiv_source_comp_inverse (a : Quiver.Total C) :
    (mfderiv J I Quiver.Total.left (inverseDiffeomorph I J C a)).comp
      (mfderiv J J (inverseDiffeomorph I J C) a) =
      mfderiv J I Quiver.Total.right a :=
  (mfderiv_comp a ((contMDiff_source I J C).mdifferentiableAt (by simp))
    ((inverseDiffeomorph I J C).contMDiff.mdifferentiableAt (by simp))).symm

/-- Differentiating `t ∘ inv = s` identifies `dt_{a⁻¹} ∘ d(inv)_a` with `ds_a`. -/
theorem mfderiv_target_comp_inverse (a : Quiver.Total C) :
    (mfderiv J I Quiver.Total.right (inverseDiffeomorph I J C a)).comp
      (mfderiv J J (inverseDiffeomorph I J C) a) =
      mfderiv J I Quiver.Total.left a :=
  (mfderiv_comp a ((contMDiff_target I J C).mdifferentiableAt (by simp))
    ((inverseDiffeomorph I J C).contMDiff.mdifferentiableAt (by simp))).symm

/-- Tangent vectors to composable pairs are determined by their images under the differentials of
the two arrow projections. -/
theorem ext_mfderiv_composablePairs
    {p : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right}}
    {u v :
      letI := composablePairsChartedSpace I J C
      TangentSpace 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) p}
    (hfst :
      letI := composablePairsChartedSpace I J C
      mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
        (Prod.fst ∘ Subtype.val) p u =
      mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
        (Prod.fst ∘ Subtype.val) p v)
    (hsnd :
      letI := composablePairsChartedSpace I J C
      mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
        (Prod.snd ∘ Subtype.val) p u =
      mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
        (Prod.snd ∘ Subtype.val) p v) :
    u = v := by
  let _ := composablePairsChartedSpace I J C
  refine sub_eq_zero.mp <| eq_zero_of_mfderiv_transverseFiberProduct (by simp : (1 : ℕ∞ω) ≤ ∞)
    (contMDiff_source I J C) (contMDiff_target I J C)
    (transverse_of_isSubmersion_left (isSubmersion_source (I := I) (J := J) (C := C)) (by simp))
    p (u - v) ?_ ?_
  · rw [map_sub]; exact sub_eq_zero.mpr hfst
  · rw [map_sub]; exact sub_eq_zero.mpr hsnd

/-- Inversion fixes units, so its differential fixes tangent vectors to the unit submanifold. -/
@[simp]
theorem mfderiv_inverse_unit_apply (x : C) (v : TangentSpace I x) :
    mfderiv J J (inverseDiffeomorph I J C) (⟨x, x, 𝟙 x⟩ : Quiver.Total C)
      (mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x v) =
      mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x v :=
  mfderiv_comp_eq (inverseDiffeomorph I J C).contMDiff
    (contMDiff_unit (I := I) (J := J) (C := C)) (funext (inverseDiffeomorph_unit I J C)) x v

/-- **Differential of inversion on source-vertical vectors at units.** For `ξ ∈ ker(ds_{1_x})`,
`d(inv)_{1_x} ξ = du_x (dt_{1_x} ξ) - ξ`, obtained by differentiating `g · g⁻¹ = 1_{t(g)}`. -/
theorem mfderiv_inverse_eq_of_mem_ker_source {x : C}
    {ξ : TangentSpace J (⟨x, x, 𝟙 x⟩ : Quiver.Total C)}
    (hξ : mfderiv J I Quiver.Total.left (⟨x, x, 𝟙 x⟩ : Quiver.Total C) ξ = 0) :
    mfderiv J J (inverseDiffeomorph I J C) (⟨x, x, 𝟙 x⟩ : Quiver.Total C) ξ =
      mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x
        (mfderiv J I Quiver.Total.right (⟨x, x, 𝟙 x⟩ : Quiver.Total C) ξ) - ξ := by
  let _ := composablePairsChartedSpace I J C
  have := isManifold_composablePairs I J C
  let KP := 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
  let e : Quiver.Total C := ⟨x, x, 𝟙 x⟩
  let e' : Quiver.Total C := inverseDiffeomorph I J C e
  let η : TangentSpace J e' := mfderiv J J (inverseDiffeomorph I J C) e ξ
  have hη : mfderiv J I Quiver.Total.right e' η = 0 :=
    (congrArg (· ξ) (mfderiv_target_comp_inverse I J C e)).trans hξ
  have hemb := isSmoothEmbedding_coe_composablePairs I J C
  have hfst := contMDiff_fst.comp hemb.contMDiff
  have hsnd := contMDiff_snd.comp hemb.contMDiff
  have hunit := contMDiff_unit (I := I) (J := J) (C := C)
  have hinv := (inverseDiffeomorph I J C).contMDiff
  have hmul := contMDiff_mul (I := I) (J := J) (C := C)
  let uInv : C → Quiver.Total C := fun y ↦ inverseDiffeomorph I J C ⟨y, y, 𝟙 y⟩
  have huInv : ContMDiff I J ∞ uInv := hinv.comp hunit
  let σR : Quiver.Total C → {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} :=
    fun g ↦ ⟨(g, uInv g.left), rfl⟩
  have hσR : ContMDiff J KP ∞ σR :=
    hemb.contMDiff_iff_comp.mpr (contMDiff_id.prodMk (huInv.comp (contMDiff_source I J C)))
  let σL : Quiver.Total C → {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} :=
    fun h ↦ ⟨(⟨h.right, h.right, 𝟙 h.right⟩, h), rfl⟩
  have hσL : ContMDiff J KP ∞ σL :=
    hemb.contMDiff_iff_comp.mpr ((hunit.comp (contMDiff_target I J C)).prodMk contMDiff_id)
  let φ : Quiver.Total C → {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} :=
    fun g ↦ ⟨(g, inverseDiffeomorph I J C g), rfl⟩
  have hφ : ContMDiff J KP ∞ φ := hemb.contMDiff_iff_comp.mpr (contMDiff_id.prodMk hinv)
  let v₁ : TangentSpace KP (φ e) := mfderiv J KP σR e ξ
  let v₂ : TangentSpace KP (φ e) := mfderiv J KP σL e' η
  have hv₁f : mfderiv KP J (Prod.fst ∘ Subtype.val) (φ e) v₁ = ξ :=
    mfderiv_comp_id_eq hfst hσR rfl e ξ
  have hv₁s : mfderiv KP J (Prod.snd ∘ Subtype.val) (φ e) v₁ = 0 := by
    have h := (mfderiv_comp_eq (k := uInv ∘ Quiver.Total.left) hsnd hσR rfl e ξ).trans
      (mfderiv_comp_eq (k := uInv ∘ Quiver.Total.left) huInv (contMDiff_source I J C) rfl e ξ).symm
    rwa [hξ, map_zero] at h
  have hv₂f : mfderiv KP J (Prod.fst ∘ Subtype.val) (φ e) v₂ = 0 := by
    have h := (mfderiv_comp_eq (k := (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) ∘
        Quiver.Total.right) hfst hσL rfl e' η).trans
      (mfderiv_comp_eq (k := (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) ∘ Quiver.Total.right)
        hunit (contMDiff_target I J C) rfl e' η).symm
    rwa [hη, map_zero] at h
  have hv₂s : mfderiv KP J (Prod.snd ∘ Subtype.val) (φ e) v₂ = η :=
    mfderiv_comp_id_eq hsnd hσL rfl e' η
  have hv_eq : mfderiv J KP φ e ξ = v₁ + v₂ := by
    refine ext_mfderiv_composablePairs I J C ?_ ?_
    · rw [map_add, hv₁f, hv₂f, add_zero]
      exact mfderiv_comp_id_eq hfst hφ rfl e ξ
    · rw [map_add, hv₁s, hv₂s, zero_add]
      exact mfderiv_comp_eq (k := inverseDiffeomorph I J C) hsnd hφ rfl e ξ
  have hv₁m : mfderiv KP J (fun q : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} ↦
      q.1.2.comp q.1.1 q.2.symm) (φ e) v₁ = ξ :=
    mfderiv_comp_id_eq hmul hσR (by funext g; simp [σR, uInv, inverseDiffeomorph_apply]) e ξ
  have hv₂m : mfderiv KP J (fun q : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} ↦
      q.1.2.comp q.1.1 q.2.symm) (φ e) v₂ = η :=
    mfderiv_comp_id_eq hmul hσL (funext fun h ↦ Quiver.Total.comp_id h rfl) e' η
  have hcancel : (fun q : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} ↦
      q.1.2.comp q.1.1 q.2.symm) ∘ φ =
      (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) ∘ Quiver.Total.right :=
    funext fun g ↦ Quiver.Total.inv_self_comp g rfl
  have key := (mfderiv_comp_eq hmul hφ hcancel e ξ).trans
    (mfderiv_comp_eq (k := (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) ∘ Quiver.Total.right)
      hunit (contMDiff_target I J C) rfl e ξ).symm
  rw [hv_eq, map_add, hv₁m, hv₂m] at key
  exact eq_sub_of_add_eq' key

end IsLieGroupoid

end TauCeti

section SmoothFamilies

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  {C : Type*} [Category C] [IsGroupoid C] [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
  [IsManifold J ∞ (Quiver.Total C)] [TauCeti.IsLieGroupoid I J C]
  {E'' H'' M : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {K : ModelWithCorners ℝ E'' H''} [TopologicalSpace M] [ChartedSpace H'' M]

include I in
/-- Smooth families `g` and `h` of arrows with `s(g z) = t(h z)` have smooth geometric product
`z ↦ g(z) h(z) = h(z) ≫ g(z)`. -/
theorem ContMDiff.quiverTotalMul {g h : M → Quiver.Total C}
    (hg : ContMDiff K J ∞ g) (hh : ContMDiff K J ∞ h) (heq : ∀ z, (g z).left = (h z).right) :
    ContMDiff K J ∞ fun z ↦ (h z).comp (g z) (heq z).symm := by
  let _ := TauCeti.IsLieGroupoid.composablePairsChartedSpace I J C
  have hpair : ContMDiff K _ ∞ (fun z ↦ (⟨(g z, h z), heq z⟩ :
      {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right})) :=
    (TauCeti.IsLieGroupoid.isSmoothEmbedding_coe_composablePairs I J C).contMDiff_iff_comp.mpr
      (hg.prodMk hh)
  exact (TauCeti.IsLieGroupoid.contMDiff_mul (I := I) (J := J) (C := C)).comp hpair

include I in
/-- Smooth families `a` and `b` of arrows with `t(a z) = s(b z)` have smooth categorical composite
`z ↦ a(z) ≫ b(z)`. -/
theorem ContMDiff.quiverTotalComp {a b : M → Quiver.Total C}
    (ha : ContMDiff K J ∞ a) (hb : ContMDiff K J ∞ b) (heq : ∀ z, (a z).right = (b z).left) :
    ContMDiff K J ∞ fun z ↦ (a z).comp (b z) (heq z) :=
  (hb.quiverTotalMul (I := I) ha fun z ↦ (heq z).symm).congr fun _ ↦
    Quiver.Total.comp_congr rfl rfl _ _

end SmoothFamilies
