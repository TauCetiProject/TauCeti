/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Tensor.Induction.Basic
import TauCeti.LinearAlgebra.PiTensorProduct.ZMod
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete.Basic
public import TauCeti.Topology.Algebra.Group.WreathProduct.Monomial

/-!
# Tensor induction of discrete continuous representations

For an open finite-index subgroup `U ≤ G`, tensor induction of a discrete continuous
`U`-module is again a discrete continuous `G`-module. The tensor power is given the discrete
topology, not a topology inferred from an algebraic tensor product. Continuity follows because
a pure tensor involves finitely many continuous coordinate actions; sums of pure tensors then
exhaust the tensor power.

`TauCeti.DiscreteRep.tensorInductionFunctor` is the continuous-coefficient version of
`Subgroup.tensorInductionFunctor`. Composing it with `TauCeti.toSmoothDiscrete` supplies
coefficients for Mathlib's continuous cohomology. In particular this makes the tensor induction
used in the general Evens norm available on discrete coefficients, rather than only in `Rep`.
The scalar ring is discrete; this includes both `ℤ` and `ZMod 2`. No compactness of `G` is needed:
openness and finite index are separate hypotheses.

## References

* L. Evens, "A generalization of the transfer map in the cohomology of groups",
  *Transactions of the American Mathematical Society* 108 (1963), §§2–5.
-/

public section

open CategoryTheory
open scoped TensorProduct

universe u v w x

namespace Representation

variable {R : Type u} {D : Type v} {M : Type w} {ι : Type x}
  [CommSemiring R] [Group D] [TopologicalSpace D]
  [AddCommMonoid M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  [Finite ι] [TopologicalSpace ι] [DiscreteTopology ι]
  [TopologicalSpace (⨂[R] _ : ι, M)] [DiscreteTopology (⨂[R] _ : ι, M)]

/-- A wreath tensor representation has continuous orbit maps on its discrete tensor power if
its base representation has a continuous action and there are finitely many tensor factors. -/
theorem continuous_wreathTensor_apply (ρ : Representation R D M)
    (hρ : Continuous fun p : D × M ↦ ρ p.1 p.2) (z : ⨂[R] _ : ι, M) :
    Continuous fun a : TauCeti.WreathProduct D ι ↦ ρ.wreathTensor ι a z := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    have hc : Continuous (fun a : TauCeti.WreathProduct D ι ↦
        fun i ↦ ρ (a.left i) (m (a.right.symm i))) := by
      apply continuous_pi
      intro i
      exact hρ.comp ((TauCeti.WreathProduct.continuous_left i).prodMk
        (continuous_of_discreteTopology.comp (TauCeti.WreathProduct.continuous_right_inv i)))
    have ht : Continuous (PiTensorProduct.tprod R : (ι → M) → (⨂[R] _ : ι, M)) :=
      continuous_of_discreteTopology
    simpa only [map_smul, wreathTensor_apply_tprod, Function.comp_def] using
      (continuous_of_discreteTopology (f := fun t : ⨂[R] _ : ι, M ↦ r • t)).comp (ht.comp hc)
  | add z z' hz hz' =>
    exact (hz.add hz').congr fun a ↦ (map_add (ρ.wreathTensor ι a) z z').symm

end Representation

namespace TauCeti.DiscreteRep

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  (U : Subgroup G) (hU : IsOpen (U : Set G)) (s : U.LeftTransversal) [U.FiniteIndex]

/-- Tensor induction on discrete continuous modules. The underlying tensor power has the
discrete topology and the action is the existing algebraic tensor-induced representation.

The body is exposed so that the carrier and its module and action instances can be used in
formulas on pure tensors. -/
@[expose] noncomputable def tensorInduced (A : DiscreteRep.{u, v, w} R U) :
    DiscreteRep.{u, v, max u v w} R G := by
  letI : TopologicalSpace (⨂[R] _ : G ⧸ U, A.V) := ⊥
  letI : DiscreteTopology (⨂[R] _ : G ⧸ U, A.V) := ⟨rfl⟩
  let ρ := U.tensorInducedRepresentation s A.ρ
  letI : DistribMulAction G (⨂[R] _ : G ⧸ U, A.V) := .compHom _ ρ
  letI : SMulCommClass G R (⨂[R] _ : G ⧸ U, A.V) :=
    ⟨fun g r z ↦ (ρ g).map_smul r z⟩
  letI : ContinuousSMul R (⨂[R] _ : G ⧸ U, A.V) := ⟨continuous_of_discreteTopology⟩
  letI : ContinuousSMul G (⨂[R] _ : G ⧸ U, A.V) := by
    refine ⟨continuous_prod_of_discrete_right.mpr fun z ↦ ?_⟩
    have : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU
    have : Finite (G ⧸ U) := inferInstance
    have hc := (Representation.continuous_wreathTensor_apply A.ρ
      (by simpa only [Representation.ofDistribMulAction_apply_apply] using
        (continuous_smul : Continuous fun p : U × A.V ↦ p.1 • p.2)) z).comp
      (U.continuous_monomialHom hU s)
    exact hc.congr fun g ↦ (U.tensorInducedRepresentation_apply s A.ρ g z).symm
  exact { V := ⨂[R] _ : G ⧸ U, A.V }

/-- The underlying module of discrete tensor induction is the tensor power over the cosets. -/
@[simp] theorem tensorInduced_V (A : DiscreteRep.{u, v, w} R U) :
    (tensorInduced U hU s A).V = (⨂[R] _ : G ⧸ U, A.V) := (rfl)

/-- Discrete tensor induction uses the algebraic tensor-induced action. -/
theorem tensorInduced_ρ_apply (A : DiscreteRep.{u, v, w} R U) (g : G)
    (z : ⨂[R] _ : G ⧸ U, A.V) :
    (tensorInduced U hU s A).ρ g z = U.tensorInducedRepresentation s A.ρ g z := (rfl)

/-- On a pure tensor, the coordinate at a coset is acted on by its transversal word and the
coordinates are translated by `g⁻¹`. -/
@[simp] theorem tensorInduced_ρ_apply_tprod (A : DiscreteRep.{u, v, w} R U) (g : G)
    (m : G ⧸ U → A.V) :
    (tensorInduced U hU s A).ρ g (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun i ↦ (U.monomialHom s g).left i • m (g⁻¹ • i) :=
  U.tensorInducedRepresentation_apply_tprod s A.ρ g m

/-- A morphism of discrete modules induces a morphism of tensor-induced modules by applying it
in each factor. -/
noncomputable def tensorInducedMap {A B : DiscreteRep.{u, v, w} R U} (f : A ⟶ B) :
    tensorInduced U hU s A ⟶ tensorInduced U hU s B :=
  f.tensorInduced s

/-- The underlying linear map of a discrete tensor-induced morphism is the tensor of the
original linear map. -/
@[simp] theorem tensorInducedMap_toLinearMap {A B : DiscreteRep.{u, v, w} R U} (f : A ⟶ B) :
    (tensorInducedMap U hU s f).toLinearMap = PiTensorProduct.map fun _ ↦ f.toLinearMap :=
  Representation.IntertwiningMap.tensorInduced_toLinearMap f s

/-- The tensor-induced morphism acts factorwise on pure tensors. -/
@[simp] theorem tensorInducedMap_apply_tprod {A B : DiscreteRep.{u, v, w} R U} (f : A ⟶ B)
    (m : G ⧸ U → A.V) :
    (tensorInducedMap U hU s f).toLinearMap (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun i ↦ f.toLinearMap (m i) := by
  rw [tensorInducedMap_toLinearMap]
  exact PiTensorProduct.map_tprod _ _

/-- Tensor induction preserves the identity morphism. -/
@[simp] theorem tensorInducedMap_id (A : DiscreteRep.{u, v, w} R U) :
    tensorInducedMap U hU s (𝟙 A) = 𝟙 (tensorInduced U hU s A) := by
  apply Representation.IntertwiningMap.ext
  rw [tensorInducedMap_toLinearMap, DiscreteRep.id_toLinearMap, DiscreteRep.id_toLinearMap]
  exact PiTensorProduct.map_id

/-- Tensor induction preserves composition of morphisms. -/
@[simp] theorem tensorInducedMap_comp {A B C : DiscreteRep.{u, v, w} R U}
    (f : A ⟶ B) (g : B ⟶ C) :
    tensorInducedMap U hU s (f ≫ g) = tensorInducedMap U hU s f ≫ tensorInducedMap U hU s g := by
  apply Representation.IntertwiningMap.ext
  simp only [tensorInducedMap_toLinearMap, DiscreteRep.comp_toLinearMap]
  exact PiTensorProduct.map_comp _ _

/-- Tensor induction for discrete continuous representations along an open finite-index
subgroup. Composing with `toSmoothDiscrete` gives smooth discrete coefficients for continuous
cohomology. The object map is exposed so the morphism formula can be stated without
transports between the opaque functor's objects and the named tensor-induced objects. -/
@[expose] noncomputable def tensorInductionFunctor :
    DiscreteRep.{u, v, w} R U ⥤ DiscreteRep.{u, v, max u v w} R G where
  obj A := tensorInduced U hU s A
  map f := tensorInducedMap U hU s f
  map_id A := tensorInducedMap_id U hU s A
  map_comp f g := tensorInducedMap_comp U hU s f g

/-- The tensor induction functor has the named tensor-induced object map. -/
@[simp] theorem tensorInductionFunctor_obj (A : DiscreteRep.{u, v, w} R U) :
    (tensorInductionFunctor U hU s).obj A = tensorInduced U hU s A := (rfl)

/-- The tensor induction functor has the factorwise tensor-induced morphism map. -/
@[simp] theorem tensorInductionFunctor_map {A B : DiscreteRep.{u, v, w} R U} (f : A ⟶ B) :
    (tensorInductionFunctor U hU s).map f = tensorInducedMap U hU s f := (rfl)

end TauCeti.DiscreteRep

namespace TauCeti

/-- Tensor induction of the trivial lifted `𝔽₂` module has a nonzero invariant pure tensor:
the tensor with every factor equal to `1`. Its image under multiplication of the factors is `1`.
This computes a non-degenerate discrete continuous coefficient example. -/
example {G : Type v} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (s : U.LeftTransversal) [U.FiniteIndex] :
    ∃ A : DiscreteRep.{0, v, v} ℤ U, ∃ z : (DiscreteRep.tensorInduced U hU s A).V,
      z ≠ 0 ∧ ∀ g : G, (DiscreteRep.tensorInduced U hU s A).ρ g z = z := by
  let M := ULift.{v} (ZMod 2)
  let : DistribMulAction U M := .compHom M (Representation.trivial ℤ U M)
  have : SMulCommClass U ℤ M :=
    ⟨fun g r m ↦ (Representation.trivial ℤ U M g).map_smul r m⟩
  have : ContinuousSMul U M := ⟨continuous_snd.congr fun p ↦
    (Representation.trivial_apply ℤ p.1 p.2).symm⟩
  let A : DiscreteRep.{0, v, v} ℤ U := { V := M }
  let z := PiTensorProduct.tprod ℤ (fun _ : G ⧸ U ↦ (1 : M))
  have : Fintype (G ⧸ U) := Fintype.ofFinite _
  refine ⟨A, z, ?_, fun g ↦ ?_⟩
  · intro hz
    let e : (⨂[ℤ] _ : G ⧸ U, M) ≃ₗ[ℤ] M := PiTensorProduct.uliftZModEquiv 2
    -- State zero in the tensor carrier, rather than in the bundled object's opaque projection.
    have hz0 : z = (0 : ⨂[ℤ] _ : G ⧸ U, M) := hz
    have hz' : e z = 0 := (congrArg e hz0).trans e.map_zero
    have hez : e z = (1 : M) := by
      apply ULift.ext
      simp [e, z, M]
    exact one_ne_zero (congrArg ULift.down (hez.symm.trans hz'))
  · rw [DiscreteRep.tensorInduced_ρ_apply_tprod]
    congr 1

end TauCeti
