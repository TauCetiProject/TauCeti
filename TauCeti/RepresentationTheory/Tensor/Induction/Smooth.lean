/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Tensor.Induction.Discrete

/-!
# Tensor induction of smooth discrete representations

Tensor induction along an open finite-index subgroup acts on smooth discrete representations by
passing through the equivalent category of discrete continuous representations, where the tensor
power has the discrete topology and continuity of the induced action is available.

## Main definitions

* `TauCeti.smoothTensorInductionFunctor`: tensor induction on smooth discrete coefficients.

## References

* L. Evens, "A generalization of the transfer map in the cohomology of groups",
  *Transactions of the American Mathematical Society* 108 (1963), §§2–5.
-/

public section

open CategoryTheory

universe u v w

namespace TauCeti

variable (R : Type u) [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : Subgroup G) (hU : IsOpen (U : Set G)) (s : U.LeftTransversal) [U.FiniteIndex]

/-- Tensor induction on smooth discrete representations along an open finite-index subgroup.

The functor passes through the equivalent category of discrete continuous representations, where
the tensor power has the discrete topology and continuity of the induced action is available.
The body is exposed so that the morphism formula `smoothTensorInductionFunctor_map` can be stated
without transports between the functor's objects and the named tensor-induced objects. -/
@[expose] noncomputable def smoothTensorInductionFunctor :
    SmoothDiscreteTopRep.{u, v, w} R U ⥤
      SmoothDiscreteTopRep.{u, v, max u v w} R G :=
  ofSmoothDiscrete R U ⋙
    DiscreteRep.tensorInductionFunctor U hU s ⋙
      toSmoothDiscrete R G

/-- The object map of smooth tensor induction is discrete tensor induction of the coefficient
module underlying the smooth representation. -/
@[simp]
theorem smoothTensorInductionFunctor_obj (A : SmoothDiscreteTopRep.{u, v, w} R U) :
    (smoothTensorInductionFunctor R G U hU s).obj A =
      (toSmoothDiscrete R G).obj
        (DiscreteRep.tensorInduced U hU s ((ofSmoothDiscrete R U).obj A)) :=
  rfl

/-- The morphism map of smooth tensor induction applies discrete tensor induction to the
underlying equivariant linear map, then returns through the smooth-discrete dictionary. -/
@[simp]
theorem smoothTensorInductionFunctor_map {A B : SmoothDiscreteTopRep.{u, v, w} R U}
    (f : A ⟶ B) :
    (smoothTensorInductionFunctor R G U hU s).map f =
      (toSmoothDiscrete R G).map
        ((DiscreteRep.tensorInductionFunctor U hU s).map ((ofSmoothDiscrete R U).map f)) :=
  rfl

end TauCeti
