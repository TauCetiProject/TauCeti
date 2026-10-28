/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.GradedContraction
public import TauCeti.RepresentationTheory.Tensor.Induction.Diagonal
public import TauCeti.RepresentationTheory.Tensor.Induction.Smooth
import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.CoboundaryShift

/-!
# Tensor induction of the total coinduced resolution

Let `U` be a compact open finite-index subgroup of a topological group `G`, and let `A` be a
smooth discrete `U`-representation.  The shifted coinduced resolution of `A` has a smooth
discrete total object, so it can itself be tensor-induced from `U` to `G`.  This file names that
object and its augmentation from the tensor induction of `A`.

On a pure tensor, the augmentation applies the ordinary coinduced-resolution augmentation in
every coset coordinate, and the construction is natural in `A`.  Compatibility with changing the
transversal is the naturality of `TauCeti.smoothTensorInducedChangeTransversalIso`, applied to
the components of the augmentation.

When every element of `A` is its own additive inverse, the tensor-induced total resolution is a
contracted complex, on which Evens' multiplicative transfer is computed.  It is graded by total
degree, and its differential is the slot sum of the total differential, which applies it in one
coset factor at a time; it commutes with the action of `G` because the slot sum needs no signs
and so commutes with permuting the factors.  The tensor power of the contraction of the total
resolution by evaluation at `1`, with the slot homotopy for an order on the cosets, contracts it
onto the tensor induction of `A` (`TauCeti.smoothTensorInducedGradedResolutionContraction`).

For a `U`-invariant cocycle `z` of degree `n` of the total resolution of `A`, the diagonal tensor
`z ⊗ ⋯ ⊗ z`, with one factor for each of the `l` cosets, is a `G`-invariant cocycle of degree
`l * n`. Its class `TauCeti.smoothTensorInducedDiagonalClass` in `H^{l n}(G, Ind⊗ A)` is the norm
of `z` in the sense of Evens; it does not depend on the order on the cosets used to contract the
resolution.  It is invariant under chain endomorphisms of the total resolution over the identity
of `A`, since their tensor inductions are chain maps over the identity of `Ind⊗ A`. The norm is not
additive, but over a coefficient ring in which `2` generates a maximal ideal, such as `ℤ` for
trivial `𝔽₂` coefficients, such an endomorphism moves a nonzero cocycle `z` to `z + d w` for any
invariant `w`, so cohomologous cocycles have the same norm.

## Main definitions

* `TauCeti.smoothTensorInducedGradedResolutionFunctor`: tensor induction of the total shifted
  coinduced resolution, functorially in the coefficients.
* `TauCeti.smoothTensorInducedGradedResolutionAugmentationApp`: the tensor-induced augmentation
  of a single coefficient object.
* `TauCeti.smoothTensorInducedGradedResolutionAugmentation`: the natural tensor-induced
  augmentation.
* `TauCeti.smoothTensorInducedGradedResolutionPiece` and
  `TauCeti.smoothTensorInducedGradedResolutionDifferential`: the total-degree grading and the
  slot-sum differential of the tensor-induced total resolution.
* `TauCeti.smoothTensorInducedGradedResolutionContraction`: its contraction onto the tensor
  induction of the coefficients, in characteristic two.
* `TauCeti.smoothTensorInducedDiagonalClass`: the class in `H^{l n}(G, Ind⊗ A)` of the diagonal
  tensor of a `U`-invariant cocycle of degree `n`.

## Main results

* `TauCeti.smoothTensorInducedGradedResolutionDifferential_sq`: in characteristic two the
  differential squares to zero.
* `TauCeti.slotSum_smoothTensorInducedGradedResolutionHomotopy_add`: the contraction identity.
* `TauCeti.smoothTensorInducedDiagonalClass_eq`: the class of the diagonal tensor does not depend
  on the order on the cosets: it equals the class computed through the contraction for any order.
* `TauCeti.smoothTensorInducedDiagonalClass_eq_of_hom_apply_eq`: the norm is invariant under
  chain endomorphisms of the total resolution over the identity of the coefficients.
* `TauCeti.smoothTensorInducedDiagonalClass_eq_of_sub_eq_d`: cohomologous cocycles have the same
  norm, when `2` generates a maximal ideal of the coefficient ring.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Transactions of the American Mathematical Society 108 (1963), Sections 2--5.
-/

public section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace TauCeti

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : Subgroup G) (hU : IsOpen (U : Set G)) (s : U.LeftTransversal) [U.FiniteIndex]
  [CompactSpace U]

/-- Tensor induction from `U` to `G` of the total shifted coinduced resolution, functorially in
the smooth discrete coefficient object. -/
@[expose] noncomputable def smoothTensorInducedGradedResolutionFunctor :
    SmoothDiscreteTopRep.{u, v, max v w} R U ⥤
      SmoothDiscreteTopRep.{u, v, max u v w} R G :=
  smoothGradedResolutionFunctor ⋙ smoothTensorInductionFunctor R G U hU s

/-- The object map of the tensor-induced total resolution tensor-induces the total resolution of
the coefficient object.

This is not a simp lemma: rewriting the objects would take the pure-tensor evaluation lemma
`smoothTensorInducedGradedResolutionAugmentationApp_apply_tprod` out of simp-normal form. -/
theorem smoothTensorInducedGradedResolutionFunctor_obj
    (A : SmoothDiscreteTopRep.{u, v, max v w} R U) :
    (smoothTensorInducedGradedResolutionFunctor U hU s).obj A =
      (smoothTensorInductionFunctor R G U hU s).obj (smoothGradedResolutionFunctor.obj A) :=
  rfl

/-- The morphism map of the tensor-induced total resolution tensor-induces the induced map of
total resolutions. -/
@[simp]
theorem smoothTensorInducedGradedResolutionFunctor_map
    {A B : SmoothDiscreteTopRep.{u, v, max v w} R U} (f : A ⟶ B) :
    (smoothTensorInducedGradedResolutionFunctor U hU s).map f =
      (smoothTensorInductionFunctor R G U hU s).map (smoothGradedResolutionFunctor.map f) :=
  rfl

/-- The action of `G` on the tensor-induced total resolution is tensor induction of the action of
`U` on the total resolution. -/
theorem smoothTensorInducedGradedResolutionFunctor_obj_ρ_apply
    (A : SmoothDiscreteTopRep.{u, v, max v w} R U) (g : G)
    (x : ((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).obj.V) :
    ((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).obj.ρ g x =
      U.tensorInducedRepresentation s
        ((ofSmoothDiscrete R U).obj (smoothGradedResolutionFunctor.obj A)).ρ g x :=
  -- `toSmoothDiscrete` keeps the action of the discrete tensor induction.
  DiscreteRep.tensorInduced_ρ_apply U hU s _ g x

/-- Tensor induction of the coefficient augmentation into the total shifted coinduced
resolution.

The source is written in the simp-normal form produced by `smoothTensorInductionFunctor_obj`, so
that the pure-tensor computation rule below can be a simp lemma. -/
noncomputable def smoothTensorInducedGradedResolutionAugmentationApp
    (A : SmoothDiscreteTopRep.{u, v, max v w} R U) :
    (toSmoothDiscrete R G).obj
        (DiscreteRep.tensorInduced U hU s ((ofSmoothDiscrete R U).obj A)) ⟶
      (smoothTensorInducedGradedResolutionFunctor U hU s).obj A :=
  (smoothTensorInductionFunctor R G U hU s).map (smoothGradedResolutionAugmentationApp A)

/-- On a pure tensor, the tensor-induced augmentation applies the coinduced-resolution
augmentation in every coset coordinate. -/
@[simp]
theorem smoothTensorInducedGradedResolutionAugmentationApp_apply_tprod
    (A : SmoothDiscreteTopRep.{u, v, max v w} R U) (x : G ⧸ U → A.obj.V) :
    (smoothTensorInducedGradedResolutionAugmentationApp U hU s A).hom.hom
        (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R fun i ↦ A.obj.gradedResolutionAugmentation (x i) :=
  -- The discrete functor is sandwiched between `ofSmoothDiscrete` and `toSmoothDiscrete`, whose
  -- round trips on maps are the identity by definition because `discreteRepEquivSmoothTopRep`
  -- has identity unit and counit components.
  (Representation.IntertwiningMap.tensorInduced_apply_tprod
    ((ofSmoothDiscrete R U).map (smoothGradedResolutionAugmentationApp A)) s x).trans <|
      congrArg (PiTensorProduct.tprod R) <| funext fun i ↦
        smoothGradedResolutionAugmentationApp_hom_apply A (x i)

/-- The tensor-induced coefficient augmentations, as a natural transformation into the
tensor-induced total resolution: the right whiskering of `smoothGradedResolutionAugmentation` by
smooth tensor induction. -/
noncomputable def smoothTensorInducedGradedResolutionAugmentation :
    smoothTensorInductionFunctor R G U hU s ⟶
      smoothTensorInducedGradedResolutionFunctor U hU s :=
  Functor.whiskerRight smoothGradedResolutionAugmentation
    (smoothTensorInductionFunctor R G U hU s)

/-- The component of the tensor-induced augmentation is the named tensor-induced augmentation. -/
@[simp]
theorem smoothTensorInducedGradedResolutionAugmentation_app
    (A : SmoothDiscreteTopRep.{u, v, max v w} R U) :
    (smoothTensorInducedGradedResolutionAugmentation U hU s).app A =
      smoothTensorInducedGradedResolutionAugmentationApp U hU s A := by
  rw [smoothTensorInducedGradedResolutionAugmentation, Functor.whiskerRight_app,
    smoothGradedResolutionAugmentation_app, smoothTensorInducedGradedResolutionAugmentationApp]

/-- The tensor-induced augmentation applies the coinduced-resolution augmentation in every coset
factor.

This is not a simp lemma, so that `smoothTensorInducedGradedResolutionAugmentationApp_apply_tprod`
still evaluates the augmentation on pure tensors. -/
theorem smoothTensorInducedGradedResolutionAugmentationApp_hom_apply
    (A : SmoothDiscreteTopRep.{u, v, max v w} R U) (x : ⨂[R] _ : G ⧸ U, A.obj.V) :
    (smoothTensorInducedGradedResolutionAugmentationApp U hU s A).hom.hom x =
      PiTensorProduct.map (fun _ ↦ A.obj.gradedResolutionAugmentation) x := by
  have hf : ((ofSmoothDiscrete R U).map (smoothGradedResolutionAugmentationApp A)).toLinearMap =
      A.obj.gradedResolutionAugmentation :=
    (ofSmoothDiscrete_map_toLinearMap _ _ _).trans
      (LinearMap.ext (smoothGradedResolutionAugmentationApp_hom_apply A))
  -- The bundled augmentation is tensor induction of the augmentation, through the dictionary
  -- functors, whose round trips on maps are the identity by definition.
  exact (LinearMap.congr_fun (Representation.IntertwiningMap.tensorInduced_toLinearMap
      ((ofSmoothDiscrete R U).map (smoothGradedResolutionAugmentationApp A)) s) x).trans
    (congrArg (fun φ ↦ PiTensorProduct.map (fun _ : G ⧸ U ↦ φ) x) hf)

/-! ### The contracted tensor-induced resolution -/

section Contraction

variable (A : SmoothDiscreteTopRep.{u, v, max v w} R U)

variable [Fintype (G ⧸ U)]

/-- The **total-degree grading** of the tensor-induced total resolution: a pure tensor of
homogeneous factors has the sum of their degrees. -/
noncomputable abbrev smoothTensorInducedGradedResolutionPiece :
    ℤ → Submodule R ((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).obj.V :=
  PiTensorProduct.totalDegreePiece (G ⧸ U) A.obj.gradedResolutionPiece

/-- The action of `G` on the tensor-induced total resolution preserves the total degree. -/
theorem smoothTensorInducedGradedResolutionPiece_ρ_mem (n : ℤ) (g : G)
    (x : ((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).obj.V)
    (hx : x ∈ smoothTensorInducedGradedResolutionPiece U hU s A n) :
    ((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).obj.ρ g x ∈
      smoothTensorInducedGradedResolutionPiece U hU s A n := by
  let B := (ofSmoothDiscrete R U).obj ((smoothGradedResolutionFunctor (R := R)).obj A)
  have hB (u : U) :
      TauCeti.LinearMap.IsHomogeneous (B.ρ u) A.obj.gradedResolutionPiece
        A.obj.gradedResolutionPiece 0 :=
    TauCeti.LinearMap.isHomogeneous_def.2 fun p y hy ↦
      (congrArg₂ (· ∈ A.obj.gradedResolutionPiece ·)
        ((ofSmoothDiscrete_obj_ρ_apply R U _ u y).trans
          (smoothGradedResolutionFunctor_obj_obj_ρ_apply A u y)) (add_zero p)).mpr
        (A.obj.gradedResolutionTopRep_ρ_mem p u y hy)
  have h := (B.ρ.isHomogeneous_wreathTensor hB (U.monomialHom s g)).map_mem hx
  rw [add_zero] at h
  rw [smoothTensorInducedGradedResolutionFunctor_obj_ρ_apply]
  exact (congrArg (· ∈ smoothTensorInducedGradedResolutionPiece U hU s A n)
    (Subgroup.tensorInducedRepresentation_apply U s B.ρ g x)).mpr h

/-- The **differential of the tensor-induced total resolution**: the slot sum of the total
differential, which applies it in one coset factor at a time. It is a complex in characteristic
two (`TauCeti.smoothTensorInducedGradedResolutionDifferential_sq`). -/
noncomputable def smoothTensorInducedGradedResolutionDifferential :
    (smoothTensorInducedGradedResolutionFunctor U hU s).obj A ⟶
      (smoothTensorInducedGradedResolutionFunctor U hU s).obj A :=
  letI := Classical.decEq (G ⧸ U)
  (toSmoothDiscrete R G).map
    (((ofSmoothDiscrete R U).map (smoothGradedResolutionDifferential A)).tensorInducedSlotSum s :
      DiscreteRep.tensorInduced U hU s _ ⟶ DiscreteRep.tensorInduced U hU s _)

/-- The differential of the tensor-induced total resolution is the slot sum of the total
differential. -/
@[simp]
theorem smoothTensorInducedGradedResolutionDifferential_apply [DecidableEq (G ⧸ U)]
    (z : ((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).obj.V) :
    (smoothTensorInducedGradedResolutionDifferential U hU s A).hom.hom z =
      PiTensorProduct.slotSum (G ⧸ U) A.obj.gradedResolutionDifferential z := by
  obtain rfl : ‹DecidableEq (G ⧸ U)› = Classical.decEq _ := Subsingleton.elim _ _
  let := Classical.decEq (G ⧸ U)
  have hf : ((ofSmoothDiscrete R U).map (smoothGradedResolutionDifferential A)).toLinearMap =
      A.obj.gradedResolutionDifferential :=
    (ofSmoothDiscrete_map_toLinearMap _ _ _).trans
      (LinearMap.ext (smoothGradedResolutionDifferential_hom_apply A))
  exact (toSmoothDiscrete_map_hom_hom_apply R G _ z).trans <|
    (LinearMap.congr_fun (Representation.IntertwiningMap.tensorInducedSlotSum_toLinearMap _ s)
      z).trans (congrArg (fun φ ↦ PiTensorProduct.slotSum (G ⧸ U) φ z) hf)

/-- The differential of the tensor-induced total resolution raises the total degree by one. -/
theorem isHomogeneous_smoothTensorInducedGradedResolutionDifferential :
    LinearMap.IsHomogeneous
      (smoothTensorInducedGradedResolutionDifferential U hU s A).hom.hom.toLinearMap
      (smoothTensorInducedGradedResolutionPiece U hU s A)
      (smoothTensorInducedGradedResolutionPiece U hU s A) 1 := by
  classical
  have h := PiTensorProduct.isHomogeneous_slotSum (ι := G ⧸ U)
    A.obj.isHomogeneous_gradedResolutionDifferential
  exact LinearMap.isHomogeneous_def.2 fun n x hx ↦
    (congrArg (· ∈ smoothTensorInducedGradedResolutionPiece U hU s A (n + 1))
      (smoothTensorInducedGradedResolutionDifferential_apply U hU s A x)).mpr (h.map_mem hx)

/-- **The tensor-induced total resolution is a complex in characteristic two**: if every
coefficient is its own additive inverse, its differential squares to zero. Applying the total
differential in two distinct coset factors gives the same term in either order, and these terms
cancel in pairs. -/
theorem smoothTensorInducedGradedResolutionDifferential_sq (hA : ∀ a : A.obj.V, a + a = 0) :
    (smoothTensorInducedGradedResolutionDifferential U hU s A).hom ≫
      (smoothTensorInducedGradedResolutionDifferential U hU s A).hom = 0 := by
  classical
  ext z
  have h := LinearMap.congr_fun (PiTensorProduct.slotSum_comp_slotSum (ι := G ⧸ U) (R := R)
    (A.obj.gradedResolutionModule_add_self_eq_zero hA) (f := A.obj.gradedResolutionDifferential)
    (LinearMap.ext A.obj.gradedResolutionDifferential_sq)) z
  exact (smoothTensorInducedGradedResolutionDifferential_apply U hU s A _).trans <|
    (congrArg (PiTensorProduct.slotSum (G ⧸ U) A.obj.gradedResolutionDifferential)
      (smoothTensorInducedGradedResolutionDifferential_apply U hU s A z)).trans h

/-- The projection of the tensor-induced total resolution onto the tensor induction of the
coefficients: the projection of the total resolution, evaluation at `1` in degree zero, in every
coset factor. It is not equivariant. -/
noncomputable def smoothTensorInducedGradedResolutionProjection :
    (⨂[R] _ : G ⧸ U, A.obj.gradedResolutionModule) →ₗ[R] ⨂[R] _ : G ⧸ U, A.obj.V :=
  PiTensorProduct.map fun _ ↦ A.obj.gradedResolutionProjection

omit [DiscreteTopology R] [U.FiniteIndex] [CompactSpace U] [Fintype (G ⧸ U)] in
/-- On a pure tensor, the projection applies the projection of the total resolution in every
coset factor. -/
@[simp]
theorem smoothTensorInducedGradedResolutionProjection_tprod
    (m : G ⧸ U → A.obj.gradedResolutionModule) :
    smoothTensorInducedGradedResolutionProjection U A (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun i ↦ A.obj.gradedResolutionProjection (m i) :=
  PiTensorProduct.map_tprod _ _

omit [DiscreteTopology R] [U.FiniteIndex] [CompactSpace U] [Fintype (G ⧸ U)] in
/-- The projection retracts the tensor-induced augmentation. -/
theorem smoothTensorInducedGradedResolutionProjection_augmentation (x : ⨂[R] _ : G ⧸ U, A.obj.V) :
    smoothTensorInducedGradedResolutionProjection U A
      (PiTensorProduct.map (fun _ ↦ A.obj.gradedResolutionAugmentation) x) = x := by
  have h : A.obj.gradedResolutionProjection ∘ₗ A.obj.gradedResolutionAugmentation =
      LinearMap.id :=
    LinearMap.ext A.obj.gradedResolutionProjection_augmentation
  rw [smoothTensorInducedGradedResolutionProjection, ← LinearMap.comp_apply,
    ← PiTensorProduct.map_comp, h, PiTensorProduct.map_id, LinearMap.id_apply]

/-- The tensor-induced augmentation lands in total degree zero. -/
theorem smoothTensorInducedGradedResolutionAugmentationApp_mem
    (x : ((toSmoothDiscrete R G).obj
      (DiscreteRep.tensorInduced U hU s ((ofSmoothDiscrete R U).obj A))).obj.V) :
    (smoothTensorInducedGradedResolutionAugmentationApp U hU s A).hom.hom x ∈
      smoothTensorInducedGradedResolutionPiece U hU s A 0 :=
  (congrArg (· ∈ smoothTensorInducedGradedResolutionPiece U hU s A 0)
    (smoothTensorInducedGradedResolutionAugmentationApp_hom_apply U hU s A x)).mpr
      (PiTensorProduct.map_mem_totalDegreePiece_zero
        (fun _ ↦ A.obj.gradedResolutionAugmentation_mem) x)

variable [LinearOrder (G ⧸ U)]

/-- The contracting homotopy of the tensor-induced total resolution, for an order on the cosets:
the slot homotopy applying the projection followed by the augmentation in the factors before a
slot, the contracting homotopy of the total resolution at the slot, and the identity after it.
It lowers the total degree by one and is not equivariant. -/
noncomputable def smoothTensorInducedGradedResolutionHomotopy :
    Module.End R (⨂[R] _ : G ⧸ U, A.obj.gradedResolutionModule) :=
  PiTensorProduct.slotHomotopy (G ⧸ U)
    (A.obj.gradedResolutionAugmentation ∘ₗ A.obj.gradedResolutionProjection)
    A.obj.gradedResolutionHomotopy

omit [DiscreteTopology R] [U.FiniteIndex] [CompactSpace U] in
/-- The contracting homotopy of the tensor-induced total resolution is the slot homotopy of the
projection followed by the augmentation, and of the contracting homotopy of the total
resolution. -/
theorem smoothTensorInducedGradedResolutionHomotopy_def :
    smoothTensorInducedGradedResolutionHomotopy U A =
      PiTensorProduct.slotHomotopy (G ⧸ U)
        (A.obj.gradedResolutionAugmentation ∘ₗ A.obj.gradedResolutionProjection)
        A.obj.gradedResolutionHomotopy :=
  (rfl)

omit [DiscreteTopology R] [U.FiniteIndex] [CompactSpace U] in
/-- The contracting homotopy of the tensor-induced total resolution lowers the total degree by
one. -/
theorem isHomogeneous_smoothTensorInducedGradedResolutionHomotopy :
    LinearMap.IsHomogeneous (smoothTensorInducedGradedResolutionHomotopy U A)
      (PiTensorProduct.totalDegreePiece (G ⧸ U) A.obj.gradedResolutionPiece)
      (PiTensorProduct.totalDegreePiece (G ⧸ U) A.obj.gradedResolutionPiece) (-1) := by
  refine PiTensorProduct.isHomogeneous_slotHomotopy ?_
    A.obj.isHomogeneous_gradedResolutionHomotopy
  rw [LinearMap.isHomogeneous_def]
  intro p v hv
  rw [add_zero]
  rcases eq_or_ne p 0 with rfl | hp
  · exact A.obj.gradedResolutionAugmentation_mem _
  · rw [LinearMap.comp_apply, A.obj.gradedResolutionProjection_eq_zero_of_mem hp hv, map_zero]
    exact zero_mem _

omit [DiscreteTopology R] [U.FiniteIndex] [CompactSpace U] in
/-- **The contraction identity** of the tensor-induced total resolution in characteristic two:
`d ∘ h + h ∘ d = 1 - ι ∘ π` for the slot sum `d` of the total differential, the contracting
homotopy `h`, the tensor-induced augmentation `ι` and the projection `π`. -/
theorem slotSum_smoothTensorInducedGradedResolutionHomotopy_add (hA : ∀ a : A.obj.V, a + a = 0)
    (v : ⨂[R] _ : G ⧸ U, A.obj.gradedResolutionModule) :
    PiTensorProduct.slotSum (G ⧸ U) A.obj.gradedResolutionDifferential
          (smoothTensorInducedGradedResolutionHomotopy U A v) +
        smoothTensorInducedGradedResolutionHomotopy U A
          (PiTensorProduct.slotSum (G ⧸ U) A.obj.gradedResolutionDifferential v) =
      v - PiTensorProduct.map (fun _ ↦ A.obj.gradedResolutionAugmentation)
        (smoothTensorInducedGradedResolutionProjection U A v) := by
  rw [smoothTensorInducedGradedResolutionProjection,
    ← LinearMap.comp_apply (PiTensorProduct.map fun _ ↦ A.obj.gradedResolutionAugmentation),
    ← PiTensorProduct.map_comp, smoothTensorInducedGradedResolutionHomotopy_def]
  exact LinearMap.congr_fun (PiTensorProduct.slotSum_comp_slotHomotopy_add
    (A.obj.gradedResolutionModule_add_self_eq_zero hA)
    (LinearMap.ext fun x ↦ by
      simp only [LinearMap.comp_apply, TopRep.gradedResolutionDifferential_augmentation,
        TopRep.gradedResolutionProjection_differential, map_zero])
    (LinearMap.ext fun x ↦ by
      simpa using A.obj.gradedResolutionDifferential_gradedResolutionHomotopy_add x)) v

/-- **The contraction of the tensor-induced total resolution** onto the tensor induction of the
coefficients, in characteristic two and for an order on the cosets: the tensor-induced
augmentation, the projection `smoothTensorInducedGradedResolutionProjection` and the slot
homotopy `smoothTensorInducedGradedResolutionHomotopy`. Through it an invariant cocycle of the
tensor-induced resolution has a class in the continuous cohomology of the tensor induction. -/
noncomputable def smoothTensorInducedGradedResolutionContraction
    (hA : ∀ a : A.obj.V, a + a = 0) :
    TopRep.ResolutionContraction.{u, v, max u w}
      ((toSmoothDiscrete R G).obj
        (DiscreteRep.tensorInduced U hU s ((ofSmoothDiscrete R U).obj A))).obj
      (((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).obj.gradedCochainComplex
        (smoothTensorInducedGradedResolutionPiece U hU s A)
        (smoothTensorInducedGradedResolutionPiece_ρ_mem U hU s A)
        (smoothTensorInducedGradedResolutionDifferential U hU s A).hom
        (isHomogeneous_smoothTensorInducedGradedResolutionDifferential U hU s A)
        (smoothTensorInducedGradedResolutionDifferential_sq U hU s A hA)) :=
  TopRep.ResolutionContraction.ofGraded.{u, v, max u w} _
    (smoothTensorInducedGradedResolutionAugmentationApp U hU s A).hom
    (smoothTensorInducedGradedResolutionAugmentationApp_mem U hU s A)
    (smoothTensorInducedGradedResolutionProjection U A)
    (smoothTensorInducedGradedResolutionHomotopy U A)
    (isHomogeneous_smoothTensorInducedGradedResolutionHomotopy U A)
    (fun x ↦ (congrArg (smoothTensorInducedGradedResolutionProjection U A)
      (smoothTensorInducedGradedResolutionAugmentationApp_hom_apply U hU s A x)).trans
        (smoothTensorInducedGradedResolutionProjection_augmentation U A x))
    (fun n _ hv ↦ PiTensorProduct.map_eq_zero_of_mem_totalDegreePiece_of_pos
      (fun _ _ hp _ hv ↦ A.obj.gradedResolutionProjection_eq_zero_of_mem hp.ne' hv)
      (Int.natCast_pos.2 n.succ_pos) hv)
    (fun _ hv ↦ PiTensorProduct.slotHomotopy_eq_zero_of_mem_totalDegreePiece_zero
      (fun _ hp ↦ A.obj.gradedResolutionPiece_of_neg hp)
      (fun _ hv ↦ A.obj.gradedResolutionHomotopy_eq_zero_of_mem_zero hv) hv)
    (fun v ↦ by
      rw [smoothTensorInducedGradedResolutionDifferential_apply,
        smoothTensorInducedGradedResolutionDifferential_apply]
      exact (slotSum_smoothTensorInducedGradedResolutionHomotopy_add U A hA v).trans
        (congrArg (v - ·) (smoothTensorInducedGradedResolutionAugmentationApp_hom_apply U hU s A
          (smoothTensorInducedGradedResolutionProjection U A v)).symm))
    (IsSmoothDiscrete.continuous_conj
      ((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).property
      ((smoothTensorInductionFunctor R G U hU s).obj A).property _)
    (IsSmoothDiscrete.continuous_conj
      ((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).property
      ((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).property _)

/-- The augmentation of the contraction of the tensor-induced total resolution is the
tensor-induced augmentation; in particular it does not depend on the order on the cosets. -/
theorem smoothTensorInducedGradedResolutionContraction_ι (hA : ∀ a : A.obj.V, a + a = 0) :
    (smoothTensorInducedGradedResolutionContraction U hU s A hA).ι =
      ((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).obj.gradedCochainComplexLift
        (smoothTensorInducedGradedResolutionPiece U hU s A)
        (smoothTensorInducedGradedResolutionPiece_ρ_mem U hU s A)
        (smoothTensorInducedGradedResolutionDifferential U hU s A).hom
        (isHomogeneous_smoothTensorInducedGradedResolutionDifferential U hU s A)
        (smoothTensorInducedGradedResolutionDifferential_sq U hU s A hA) 0
        (smoothTensorInducedGradedResolutionAugmentationApp U hU s A).hom
        (smoothTensorInducedGradedResolutionAugmentationApp_mem U hU s A) :=
  TopRep.ResolutionContraction.ofGraded_ι ..

/-- The augmentation of the contraction of the tensor-induced total resolution applies the
coinduced-resolution augmentation in every coset factor. -/
@[simp]
theorem smoothTensorInducedGradedResolutionContraction_ι_apply (hA : ∀ a : A.obj.V, a + a = 0)
    (x : ((toSmoothDiscrete R G).obj
      (DiscreteRep.tensorInduced U hU s ((ofSmoothDiscrete R U).obj A))).obj.V) :
    ((smoothTensorInducedGradedResolutionContraction U hU s A hA).ι.hom x).1 =
      PiTensorProduct.map (fun _ ↦ A.obj.gradedResolutionAugmentation) x := by
  rw [smoothTensorInducedGradedResolutionContraction_ι]
  exact (TopRep.gradedCochainComplexLift_apply _ _ _ _ _ _ 0 _ _ x).trans
    (smoothTensorInducedGradedResolutionAugmentationApp_hom_apply U hU s A x)

/-- The retraction of the contraction of the tensor-induced total resolution is
`TauCeti.smoothTensorInducedGradedResolutionProjection`. -/
@[simp]
theorem smoothTensorInducedGradedResolutionContraction_proj_apply
    (hA : ∀ a : A.obj.V, a + a = 0)
    (v : ((((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).obj.gradedCochainComplex
      (smoothTensorInducedGradedResolutionPiece U hU s A)
      (smoothTensorInducedGradedResolutionPiece_ρ_mem U hU s A)
      (smoothTensorInducedGradedResolutionDifferential U hU s A).hom
      (isHomogeneous_smoothTensorInducedGradedResolutionDifferential U hU s A)
      (smoothTensorInducedGradedResolutionDifferential_sq U hU s A hA)).X 0).V) :
    (smoothTensorInducedGradedResolutionContraction U hU s A hA).proj v =
      smoothTensorInducedGradedResolutionProjection U A v.1 :=
  TopRep.ResolutionContraction.ofGraded_proj_apply ..

/-- The contracting homotopy of the contraction of the tensor-induced total resolution is
`TauCeti.smoothTensorInducedGradedResolutionHomotopy`. -/
@[simp]
theorem smoothTensorInducedGradedResolutionContraction_hom_apply
    (hA : ∀ a : A.obj.V, a + a = 0) (n : ℕ)
    (v : ((((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).obj.gradedCochainComplex
      (smoothTensorInducedGradedResolutionPiece U hU s A)
      (smoothTensorInducedGradedResolutionPiece_ρ_mem U hU s A)
      (smoothTensorInducedGradedResolutionDifferential U hU s A).hom
      (isHomogeneous_smoothTensorInducedGradedResolutionDifferential U hU s A)
      (smoothTensorInducedGradedResolutionDifferential_sq U hU s A hA)).X (n + 1)).V) :
    ((smoothTensorInducedGradedResolutionContraction U hU s A hA).hom n v).1 =
      smoothTensorInducedGradedResolutionHomotopy U A v.1 :=
  TopRep.ResolutionContraction.ofGraded_hom_apply ..

omit [LinearOrder (G ⧸ U)]

/-- The diagonal tensor `z ⊗ ⋯ ⊗ z` of a homogeneous element of degree `n` has total degree
`l * n`, for `l` the number of cosets. -/
theorem tprod_const_mem_smoothTensorInducedGradedResolutionPiece {n : ℕ}
    {z : A.obj.gradedResolutionModule} (hz : z ∈ A.obj.gradedResolutionPiece n) :
    PiTensorProduct.tprod R (fun _ : G ⧸ U ↦ z) ∈
      smoothTensorInducedGradedResolutionPiece U hU s A (Fintype.card (G ⧸ U) * n : ℕ) := by
  have h := PiTensorProduct.tprod_mem_totalDegreePiece (ι := G ⧸ U) (R := R)
    (ℳ := A.obj.gradedResolutionPiece) (p := fun _ ↦ (n : ℤ)) (m := fun _ ↦ z) fun _ ↦ hz
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  exact_mod_cast h

omit [Fintype (G ⧸ U)] in
/-- The diagonal tensor `z ⊗ ⋯ ⊗ z` of a `U`-invariant element of the total resolution is
`G`-invariant. -/
theorem smoothTensorInducedGradedResolutionFunctor_obj_ρ_tprod_const
    {z : A.obj.gradedResolutionModule} (hinv : ∀ u, A.obj.gradedResolutionTopRep.ρ u z = z)
    (g : G) :
    ((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).obj.ρ g
        (PiTensorProduct.tprod R (fun _ : G ⧸ U ↦ z)) =
      PiTensorProduct.tprod R (fun _ : G ⧸ U ↦ z) := by
  let B := (ofSmoothDiscrete R U).obj ((smoothGradedResolutionFunctor (R := R)).obj A)
  have hB (u : U) : B.ρ u z = z :=
    (ofSmoothDiscrete_obj_ρ_apply R U (smoothGradedResolutionFunctor.obj A) u z).trans
      ((smoothGradedResolutionFunctor_obj_obj_ρ_apply A u z).trans (hinv u))
  have h := (B.ρ.tensorInducedDiagonal s ⟨z, hB⟩).property g
  rw [Representation.coe_tensorInducedDiagonal] at h
  exact (smoothTensorInducedGradedResolutionFunctor_obj_ρ_apply U hU s A g _).trans h

/-- The diagonal tensor `z ⊗ ⋯ ⊗ z` of a cocycle is a cocycle: each term of the slot sum
applies the differential to a factor. -/
theorem smoothTensorInducedGradedResolutionDifferential_tprod_const_eq_zero
    {z : A.obj.gradedResolutionModule} (hdz : A.obj.gradedResolutionDifferential z = 0) :
    (smoothTensorInducedGradedResolutionDifferential U hU s A).hom.hom
      (PiTensorProduct.tprod R (fun _ : G ⧸ U ↦ z)) = 0 := by
  classical
  refine (smoothTensorInducedGradedResolutionDifferential_apply U hU s A _).trans <|
    (PiTensorProduct.slotSum_tprod _ _).trans (Finset.sum_eq_zero fun i _ ↦ ?_)
  exact (PiTensorProduct.tprod R).map_coord_zero i (by rw [Function.update_self, hdz])

/-- **The Evens norm of a cocycle**: for a homogeneous cocycle `z` of degree `n` of the total
coinduced resolution of `A`, fixed by `U`, the class in `H^{l n}(G, Ind⊗ A)` of its diagonal
tensor `z ⊗ ⋯ ⊗ z`, one factor for each of the `l` cosets of `U`. Here `A` has characteristic two,
so that the tensor-induced resolution is a complex, and the class is computed through
`TauCeti.smoothTensorInducedGradedResolutionContraction` for some order on the cosets; by
`TauCeti.smoothTensorInducedDiagonalClass_eq` it does not depend on that order. -/
noncomputable def smoothTensorInducedDiagonalClass (hA : ∀ a : A.obj.V, a + a = 0) {n : ℕ}
    (z : A.obj.gradedResolutionModule) (hz : z ∈ A.obj.gradedResolutionPiece n)
    (hinv : ∀ u, A.obj.gradedResolutionTopRep.ρ u z = z)
    (hdz : A.obj.gradedResolutionDifferential z = 0) :
    continuousCohomology.{u, v, max u w} (Fintype.card (G ⧸ U) * n)
      ((toSmoothDiscrete R G).obj
        (DiscreteRep.tensorInduced U hU s ((ofSmoothDiscrete R U).obj A))).obj :=
  letI : LinearOrder (G ⧸ U) := LinearOrder.lift' _ (Fintype.equivFin (G ⧸ U)).injective
  TopRep.ResolutionContraction.gradedCohomologyClass.{u, v, max u w}
    (smoothTensorInducedGradedResolutionContraction U hU s A hA) _
    (tprod_const_mem_smoothTensorInducedGradedResolutionPiece U hU s A hz)
    (smoothTensorInducedGradedResolutionFunctor_obj_ρ_tprod_const U hU s A hinv)
    (smoothTensorInducedGradedResolutionDifferential_tprod_const_eq_zero U hU s A hdz)

/-- **The norm of a cocycle does not depend on the order on the cosets**: it is the class of the
diagonal tensor through the contraction of the tensor-induced resolution for any order. -/
theorem smoothTensorInducedDiagonalClass_eq [LinearOrder (G ⧸ U)]
    (hA : ∀ a : A.obj.V, a + a = 0) {n : ℕ} (z : A.obj.gradedResolutionModule)
    (hz : z ∈ A.obj.gradedResolutionPiece n) (hinv : ∀ u, A.obj.gradedResolutionTopRep.ρ u z = z)
    (hdz : A.obj.gradedResolutionDifferential z = 0) :
    smoothTensorInducedDiagonalClass U hU s A hA z hz hinv hdz =
      TopRep.ResolutionContraction.gradedCohomologyClass.{u, v, max u w}
        (smoothTensorInducedGradedResolutionContraction U hU s A hA) _
        (tprod_const_mem_smoothTensorInducedGradedResolutionPiece U hU s A hz)
        (smoothTensorInducedGradedResolutionFunctor_obj_ρ_tprod_const U hU s A hinv)
        (smoothTensorInducedGradedResolutionDifferential_tprod_const_eq_zero U hU s A hdz) := by
  have : LocallyCompactSpace G :=
    (isCompact_iff_compactSpace.2 ‹CompactSpace U›).locallyCompactSpace_of_mem_nhds_of_group
      (hU.mem_nhds U.one_mem)
  unfold smoothTensorInducedDiagonalClass
  apply TopRep.ResolutionContraction.gradedCohomologyClass_eq_of_ι_eq
  rw [smoothTensorInducedGradedResolutionContraction_ι,
    smoothTensorInducedGradedResolutionContraction_ι]

section Endomorphism

variable (Φ : A.obj.gradedResolutionTopRep ⟶ A.obj.gradedResolutionTopRep)

/-- The tensor induction of an endomorphism of the total resolution of `A`. -/
private noncomputable def tensorInducedEndo :
    ((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).obj ⟶
      ((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).obj :=
  ((smoothTensorInductionFunctor R G U hU s).map
    (ObjectProperty.homMk Φ : (smoothGradedResolutionFunctor (R := R)).obj A ⟶
      smoothGradedResolutionFunctor.obj A)).hom

omit [Fintype (G ⧸ U)] in
private theorem tensorInducedEndo_apply (x : ⨂[R] _ : G ⧸ U, A.obj.gradedResolutionModule) :
    (tensorInducedEndo U hU s A Φ).hom x =
      PiTensorProduct.map (fun _ : G ⧸ U ↦
        (Φ.hom.toLinearMap : Module.End R A.obj.gradedResolutionModule)) x :=
  smoothTensorInductionFunctor_map_hom_hom_apply R G U hU s
    (ObjectProperty.homMk Φ : (smoothGradedResolutionFunctor (R := R)).obj A ⟶
      smoothGradedResolutionFunctor.obj A) x

private theorem isHomogeneous_tensorInducedEndo
    (hΦ : LinearMap.IsHomogeneous Φ.hom.toLinearMap A.obj.gradedResolutionPiece
      A.obj.gradedResolutionPiece 0) :
    LinearMap.IsHomogeneous (tensorInducedEndo U hU s A Φ).hom.toLinearMap
      (smoothTensorInducedGradedResolutionPiece U hU s A)
      (smoothTensorInducedGradedResolutionPiece U hU s A) 0 := by
  have hΦ' : LinearMap.IsHomogeneous
      (Φ.hom.toLinearMap : Module.End R A.obj.gradedResolutionModule)
      A.obj.gradedResolutionPiece A.obj.gradedResolutionPiece 0 := hΦ
  have h := PiTensorProduct.isHomogeneous_map (ι := G ⧸ U) fun _ ↦ hΦ'
  rw [Finset.sum_const_zero] at h
  exact LinearMap.isHomogeneous_def.2 fun p x hx ↦
    (congrArg (· ∈ smoothTensorInducedGradedResolutionPiece U hU s A (p + 0))
      (tensorInducedEndo_apply U hU s A Φ x)).mpr (h.map_mem hx)

private theorem tensorInducedEndo_comm
    (hΦd : A.obj.gradedResolutionTopRepDifferential ≫ Φ =
      Φ ≫ A.obj.gradedResolutionTopRepDifferential) :
    (smoothTensorInducedGradedResolutionDifferential U hU s A).hom ≫
        tensorInducedEndo U hU s A Φ =
      tensorInducedEndo U hU s A Φ ≫
        (smoothTensorInducedGradedResolutionDifferential U hU s A).hom := by
  classical
  let Φ' : Module.End R A.obj.gradedResolutionModule := Φ.hom.toLinearMap
  have hΦd' : A.obj.gradedResolutionDifferential ∘ₗ Φ' = Φ' ∘ₗ A.obj.gradedResolutionDifferential :=
    LinearMap.ext fun v ↦ by
      rw [LinearMap.comp_apply, LinearMap.comp_apply,
        ← TopRep.gradedResolutionTopRepDifferential_apply,
        ← TopRep.gradedResolutionTopRepDifferential_apply]
      -- Composition of morphisms of `TopRep` evaluates by definition (`TopRep.comp_apply`).
      exact (congrArg (fun f ↦ f.hom v) hΦd).symm
  -- Both differentials are slot sums, and the slot sum is natural in factorwise maps.
  have key (x : ((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).obj.V) :
      (tensorInducedEndo U hU s A Φ).hom
          ((smoothTensorInducedGradedResolutionDifferential U hU s A).hom.hom x) =
        (smoothTensorInducedGradedResolutionDifferential U hU s A).hom.hom
          ((tensorInducedEndo U hU s A Φ).hom x) :=
    (congrArg (tensorInducedEndo U hU s A Φ).hom
      (smoothTensorInducedGradedResolutionDifferential_apply U hU s A x)).trans <|
        (tensorInducedEndo_apply U hU s A Φ _).trans <|
          (LinearMap.congr_fun (PiTensorProduct.slotSum_comp_map
            (fun _ : G ⧸ U ↦ Φ') fun _ ↦ hΦd') x).symm.trans <|
              (congrArg (PiTensorProduct.slotSum (G ⧸ U) A.obj.gradedResolutionDifferential)
                (tensorInducedEndo_apply U hU s A Φ x).symm).trans
                  (smoothTensorInducedGradedResolutionDifferential_apply U hU s A
                    ((tensorInducedEndo U hU s A Φ).hom x)).symm
  apply TopRep.hom_ext
  apply ContIntertwiningMap.ext
  apply ContinuousLinearMap.ext
  exact key

omit [Fintype (G ⧸ U)] in
private theorem tensorInducedEndo_augmentation
    (hΦι : ∀ x, Φ.hom (A.obj.gradedResolutionAugmentation x) = A.obj.gradedResolutionAugmentation x)
    (x : ⨂[R] _ : G ⧸ U, A.obj.V) :
    (tensorInducedEndo U hU s A Φ).hom
        (PiTensorProduct.map (fun _ ↦ A.obj.gradedResolutionAugmentation) x) =
      PiTensorProduct.map (fun _ ↦ A.obj.gradedResolutionAugmentation) x := by
  have hΦι' : (Φ.hom.toLinearMap : Module.End R A.obj.gradedResolutionModule) ∘ₗ
      A.obj.gradedResolutionAugmentation = A.obj.gradedResolutionAugmentation :=
    LinearMap.ext hΦι
  rw [tensorInducedEndo_apply]
  exact (LinearMap.congr_fun (PiTensorProduct.map_comp
    (fun _ : G ⧸ U ↦ (Φ.hom.toLinearMap : Module.End R A.obj.gradedResolutionModule))
      fun _ : G ⧸ U ↦ A.obj.gradedResolutionAugmentation) x).symm.trans
        (congrArg (fun φ ↦ PiTensorProduct.map (fun _ : G ⧸ U ↦ φ) x) hΦι')

end Endomorphism

/-- **The norm of a cocycle is invariant under chain endomorphisms over the identity.** Let `Φ` be
an endomorphism of the total resolution of `A` of degree zero, commuting with the differential and
fixing the augmentation. Then a `U`-invariant cocycle `z` and its image `Φ z` have the same norm:
the tensor induction of `Φ` carries the diagonal tensor of `z` to that of `Φ z` and is a chain map
over the identity of the tensor-induced coefficients. -/
theorem smoothTensorInducedDiagonalClass_eq_of_hom_apply_eq (hA : ∀ a : A.obj.V, a + a = 0)
    {n : ℕ} {z z' : A.obj.gradedResolutionModule} (hz : z ∈ A.obj.gradedResolutionPiece n)
    (hz' : z' ∈ A.obj.gradedResolutionPiece n) (hinv : ∀ u, A.obj.gradedResolutionTopRep.ρ u z = z)
    (hinv' : ∀ u, A.obj.gradedResolutionTopRep.ρ u z' = z')
    (hdz : A.obj.gradedResolutionDifferential z = 0)
    (hdz' : A.obj.gradedResolutionDifferential z' = 0)
    (Φ : A.obj.gradedResolutionTopRep ⟶ A.obj.gradedResolutionTopRep)
    (hΦd : A.obj.gradedResolutionTopRepDifferential ≫ Φ =
      Φ ≫ A.obj.gradedResolutionTopRepDifferential)
    (hΦι : ∀ x, Φ.hom (A.obj.gradedResolutionAugmentation x) = A.obj.gradedResolutionAugmentation x)
    (hΦ : LinearMap.IsHomogeneous Φ.hom.toLinearMap A.obj.gradedResolutionPiece
      A.obj.gradedResolutionPiece 0)
    (hΦz : Φ.hom z = z') :
    smoothTensorInducedDiagonalClass.{u, v, w} U hU s A hA z' hz' hinv' hdz' =
      smoothTensorInducedDiagonalClass.{u, v, w} U hU s A hA z hz hinv hdz := by
  let : LinearOrder (G ⧸ U) := LinearOrder.lift' _ (Fintype.equivFin (G ⧸ U)).injective
  have : LocallyCompactSpace G :=
    (isCompact_iff_compactSpace.2 ‹CompactSpace U›).locallyCompactSpace_of_mem_nhds_of_group
      (hU.mem_nhds U.one_mem)
  rw [smoothTensorInducedDiagonalClass_eq, smoothTensorInducedDiagonalClass_eq]
  refine Eq.trans ?_
    ((smoothTensorInducedGradedResolutionContraction U hU s A hA).gradedCohomologyClass_map _
      (tensorInducedEndo U hU s A Φ) (isHomogeneous_tensorInducedEndo U hU s A Φ hΦ)
      (tensorInducedEndo_comm U hU s A Φ hΦd) (fun x ↦ by
        rw [smoothTensorInducedGradedResolutionContraction_ι_apply]
        exact tensorInducedEndo_augmentation U hU s A Φ hΦι x)
      (tprod_const_mem_smoothTensorInducedGradedResolutionPiece U hU s A hz)
      (smoothTensorInducedGradedResolutionFunctor_obj_ρ_tprod_const U hU s A hinv)
      (smoothTensorInducedGradedResolutionDifferential_tprod_const_eq_zero U hU s A hdz))
  congr 1
  rw [tensorInducedEndo_apply]
  exact ((PiTensorProduct.map_tprod _ _).trans
    (congrArg (PiTensorProduct.tprod R) (funext fun _ ↦ hΦz))).symm

/-- **Cohomologous cocycles have the same norm.** Let `R` be a commutative ring in which `2`
generates a maximal ideal, such as `ℤ`, so that `A`, whose elements are their own additive
inverses, is a vector space over the field `R ⧸ (2)`. If two `U`-invariant cocycles `z` and `z'` of
the total resolution of `A` differ by the differential of a `U`-invariant element, their diagonal
tensors have the same class in `H^{l (n + 1)}(G, Ind⊗ A)`. So the norm of a cocycle depends only
on its class.

Although the norm is not additive, the coboundary can be moved by a chain endomorphism of the total
resolution over the identity of `A`
(`TopRep.exists_gradedResolutionTopRep_hom_apply_eq_add_of_add_self_eq_zero`), under which the norm
is invariant (`TauCeti.smoothTensorInducedDiagonalClass_eq_of_hom_apply_eq`). -/
theorem smoothTensorInducedDiagonalClass_eq_of_sub_eq_d [(Ideal.span {(2 : R)}).IsMaximal]
    (hA : ∀ a : A.obj.V, a + a = 0) {n : ℕ} {z z' : A.obj.gradedResolutionModule}
    (hz : z ∈ A.obj.gradedResolutionPiece (n + 1 : ℕ))
    (hz' : z' ∈ A.obj.gradedResolutionPiece (n + 1 : ℕ))
    (hinv : ∀ u, A.obj.gradedResolutionTopRep.ρ u z = z)
    (hinv' : ∀ u, A.obj.gradedResolutionTopRep.ρ u z' = z')
    (hdz : A.obj.gradedResolutionDifferential z = 0)
    (hdz' : A.obj.gradedResolutionDifferential z' = 0) {y : A.obj.gradedResolutionModule}
    (hy : y ∈ A.obj.gradedResolutionPiece n) (hyinv : ∀ u, A.obj.gradedResolutionTopRep.ρ u y = y)
    (hzy : z - z' = A.obj.gradedResolutionDifferential y) :
    smoothTensorInducedDiagonalClass.{u, v, w} U hU s A hA z hz hinv hdz =
      smoothTensorInducedDiagonalClass.{u, v, w} U hU s A hA z' hz' hinv' hdz' := by
  by_cases hz0 : z = 0
  · by_cases hz'0 : z' = 0
    · subst hz0 hz'0
      rfl
    -- Move `z'` to `z' + d y = z`.
    obtain ⟨Φ, hΦd, hΦι, hΦ, hΦz⟩ :=
      TopRep.exists_gradedResolutionTopRep_hom_apply_eq_add_of_add_self_eq_zero A.property hA hz'
        hinv' hz'0 hy hyinv
    exact smoothTensorInducedDiagonalClass_eq_of_hom_apply_eq U hU s A hA hz' hz hinv' hinv hdz'
      hdz Φ hΦd hΦι hΦ (by rw [hΦz, ← hzy, add_sub_cancel])
  -- Move `z` to `z + d (-y) = z'`.
  obtain ⟨Φ, hΦd, hΦι, hΦ, hΦz⟩ :=
    TopRep.exists_gradedResolutionTopRep_hom_apply_eq_add_of_add_self_eq_zero A.property hA hz
      hinv hz0 (neg_mem hy) fun u ↦ (map_neg (A.obj.gradedResolutionTopRep.ρ u) y).trans
        (congrArg Neg.neg (hyinv u))
  exact (smoothTensorInducedDiagonalClass_eq_of_hom_apply_eq U hU s A hA hz hz' hinv hinv' hdz
    hdz' Φ hΦd hΦι hΦ (by rw [hΦz, map_neg, ← hzy, ← sub_eq_add_neg, sub_sub_cancel])).symm

end Contraction

end TauCeti
