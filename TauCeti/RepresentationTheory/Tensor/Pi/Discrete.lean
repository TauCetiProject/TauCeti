/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete.Basic
public import TauCeti.RepresentationTheory.Tensor.Pi.Basic

/-!
# Tensor products of finite families of discrete representations

The tensor product `⨂[R] i, A i` of a finite family of discrete `G`-modules with continuous
`G`-action, with `G` acting in every factor (`Representation.piTensorProduct`), is again such a
module once it is given the discrete topology. Continuity holds on a pure tensor because it
involves finitely many continuous orbit maps, and sums of pure tensors exhaust the tensor
product. The topology is the discrete one by fiat, not a topology inferred from the algebraic
tensor product. Finiteness of the index type is what makes the action continuous.

The construction is functorial in the family: a family of morphisms acts factorwise. Composing
with `TauCeti.toSmoothDiscrete` gives smooth discrete coefficients for continuous cohomology. This
is the object on which the restriction of a tensor-induced discrete module to a subgroup splits
over double cosets.

## Main definitions

* `TauCeti.DiscreteRep.piTensorProduct`: the tensor product of a finite family of discrete
  representations.
* `TauCeti.DiscreteRep.piTensorProductFunctor`: the same construction as a functor on families.
-/

public section

open CategoryTheory
open scoped TensorProduct

universe u v w x

namespace TauCeti.DiscreteRep

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Monoid G] [TopologicalSpace G] {ι : Type x} [Finite ι]

/-- The tensor product of a finite family of discrete continuous representations. The underlying
tensor product has the discrete topology and `G` acts in every factor.

The body is exposed so that the carrier and its module and action instances can be used in
formulas on pure tensors. -/
@[expose] noncomputable def piTensorProduct (A : ι → DiscreteRep.{u, v, w} R G) :
    DiscreteRep.{u, v, max u w x} R G := by
  letI : TopologicalSpace (⨂[R] i, (A i).V) := ⊥
  letI : DiscreteTopology (⨂[R] i, (A i).V) := ⟨rfl⟩
  let ρ := Representation.piTensorProduct fun i ↦ (A i).ρ
  letI : DistribMulAction G (⨂[R] i, (A i).V) := .compHom _ ρ
  letI : SMulCommClass G R (⨂[R] i, (A i).V) := ⟨fun g r z ↦ (ρ g).map_smul r z⟩
  letI : ContinuousSMul R (⨂[R] i, (A i).V) := ⟨continuous_of_discreteTopology⟩
  letI : ContinuousSMul G (⨂[R] i, (A i).V) := by
    refine ⟨continuous_prod_of_discrete_right.mpr fun z ↦ ?_⟩
    -- The orbit map of the `compHom` action is the orbit map of `ρ`.
    change Continuous fun g : G ↦ ρ g z
    induction z using PiTensorProduct.induction_on with
    | smul_tprod r m =>
      have hc : Continuous fun g : G ↦ fun i ↦ g • m i :=
        continuous_pi fun i ↦ continuous_id.smul continuous_const
      simpa only [map_smul, ρ, Representation.piTensorProduct_apply_tprod,
        Representation.ofDistribMulAction_apply_apply, Function.comp_def] using
        (continuous_of_discreteTopology (f := fun t : ⨂[R] i, (A i).V ↦ r • t)).comp
          ((continuous_of_discreteTopology (f := PiTensorProduct.tprod R)).comp hc)
    | add z z' hz hz' =>
      exact (hz.add hz').congr fun g ↦ (map_add (ρ g) z z').symm
  exact { V := ⨂[R] i, (A i).V }

/-- The underlying module of the tensor product is the tensor product of the underlying
modules. -/
@[simp] theorem piTensorProduct_V (A : ι → DiscreteRep.{u, v, w} R G) :
    (piTensorProduct A).V = ⨂[R] i, (A i).V := (rfl)

/-- The tensor product of discrete representations carries the factorwise representation. -/
theorem piTensorProduct_ρ_apply (A : ι → DiscreteRep.{u, v, w} R G) (g : G)
    (z : ⨂[R] i, (A i).V) :
    (piTensorProduct A).ρ g z = Representation.piTensorProduct (fun i ↦ (A i).ρ) g z := (rfl)

/-- On a pure tensor, every factor is acted on in its own discrete representation. -/
@[simp] theorem piTensorProduct_ρ_apply_tprod (A : ι → DiscreteRep.{u, v, w} R G) (g : G)
    (m : ∀ i, (A i).V) :
    (piTensorProduct A).ρ g (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun i ↦ g • m i :=
  Representation.piTensorProduct_apply_tprod _ g m

variable (R G ι) in
/-- The tensor product of finite families of discrete continuous representations, as a functor
on families. A family of morphisms acts factorwise. The object map is exposed so the morphism
formula can be stated without transports between the functor's objects and the named tensor
products. -/
@[expose] noncomputable def piTensorProductFunctor :
    (ι → DiscreteRep.{u, v, w} R G) ⥤ DiscreteRep.{u, v, max u w x} R G where
  obj A := piTensorProduct A
  -- The action of `piTensorProduct A` is definitionally the factorwise representation, so the
  -- tensor product of the intertwining maps is a morphism of the named objects.
  map f := Representation.IntertwiningMap.piTensorProduct f
  map_id _ := Representation.IntertwiningMap.piTensorProduct_id
  map_comp f g := Representation.IntertwiningMap.piTensorProduct_comp g f

/-- The tensor product functor has the named tensor-product object map. -/
@[simp] theorem piTensorProductFunctor_obj (A : ι → DiscreteRep.{u, v, w} R G) :
    (piTensorProductFunctor R G ι).obj A = piTensorProduct A := (rfl)

/-- The tensor product functor applies a family of morphisms factorwise. -/
@[simp] theorem piTensorProductFunctor_map {A B : ι → DiscreteRep.{u, v, w} R G}
    (f : A ⟶ B) :
    (piTensorProductFunctor R G ι).map f = Representation.IntertwiningMap.piTensorProduct f :=
  (rfl)

/-- The tensor product functor applies the underlying linear maps of a family of morphisms in
the corresponding tensor factors. -/
theorem piTensorProductFunctor_map_toLinearMap {A B : ι → DiscreteRep.{u, v, w} R G}
    (f : A ⟶ B) :
    ((piTensorProductFunctor R G ι).map f).toLinearMap =
      PiTensorProduct.map fun i ↦ (f i).toLinearMap :=
  Representation.IntertwiningMap.piTensorProduct_toLinearMap f

end TauCeti.DiscreteRep
