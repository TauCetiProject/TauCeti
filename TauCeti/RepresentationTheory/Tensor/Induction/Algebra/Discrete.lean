/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Tensor.Induction.Algebra.Multiplication
public import TauCeti.RepresentationTheory.Tensor.Induction.ChangeTransversal.Discrete

/-!
# Tensor-induced discrete `G`-algebras and smooth multiplication

For an open finite-index subgroup `U ≤ G` and a discrete `U`-algebra `A` with continuous `U`-action,
giving `Subgroup.TensorInduced U s R A` the discrete topology makes it a discrete topological
`R`-algebra with continuous `G`-action (`Subgroup.TensorInduced.continuousSMul_of_isOpen`).

When `A` is a discrete commutative `G`-ring (or `R`-algebra over a discrete commutative ring `R`)
with continuous `G`-action, Evens' twisted multiplication `a₁ ⊗ ⋯ ⊗ a_l ↦ t₁ a₁ ⋯ t_l a_l` gives
morphisms in `TauCeti.DiscreteRep R G` and `TauCeti.SmoothDiscreteTopRep R G`. These morphisms
commute with the change-of-transversal comparison `TauCeti.smoothTensorInducedChangeTransversalIso`
and carry the tensor-induced multiplication pairing `TauCeti.TopPairing.smoothTensorInduced` to
multiplication in `A`.

## Main definitions

* `TauCeti.DiscreteRep.tensorInducedAlgebra`: `U.TensorInduced s R A` (given the discrete
  topology) as an object of `TauCeti.DiscreteRep R G`.
* `TauCeti.DiscreteRep.tensorInducedAlgebraIso`, `TauCeti.smoothTensorInducedAlgebraIso`:
  the canonical comparison with `TauCeti.DiscreteRep.tensorInduced` and its smooth counterpart.
* `TauCeti.DiscreteRep.tensorInducedMulHom`, `TauCeti.smoothTensorInducedMulHom`:
  Evens' twisted multiplication as morphisms in `DiscreteRep R G` and `SmoothDiscreteTopRep R G`.

## Main results

* `Subgroup.TensorInduced.continuousSMul_of_isOpen`, `OpenSubgroup.continuousSMul_tensorInduced`:
  continuity of the `G`-action on `U.TensorInduced s R A` when equipped with a discrete topology.
* `TauCeti.DiscreteRep.tensorInducedChangeTransversalIso_hom_comp_mulHom`,
  `TauCeti.smoothTensorInducedChangeTransversalIso_hom_comp_mulHom`: twisted multiplication
  commutes with changing the left transversal.
* `TauCeti.smoothTensorInducedMulHom_apply_smoothTensorInduced_bil`: twisted multiplication
  carries the tensor-induced multiplication pairing to multiplication in `A`.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Transactions of the American Mathematical Society **108** (1963), §5, p. 60.
-/

public section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace Subgroup.TensorInduced

section ContinuousAction

variable {G : Type v} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  {U : Subgroup G} {s : U.LeftTransversal} [U.FiniteIndex]
  {R : Type u} {A : Type w} [CommSemiring R] [Semiring A] [Algebra R A]
  [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (U.TensorInduced s R A)] [DiscreteTopology (U.TensorInduced s R A)]
  [MulSemiringAction U A] [SMulCommClass U R A] [ContinuousSMul U A]

/-- For an open finite-index subgroup `U ≤ G` and a discrete `U`-semiring `A` with continuous
`U`-action, the tensor-induced `G`-action on `U.TensorInduced s R A` (equipped with a discrete
topology) is continuous. -/
theorem continuousSMul_of_isOpen (hU : IsOpen (U : Set G)) :
    ContinuousSMul G (U.TensorInduced s R A) := by
  refine ⟨continuous_prod_of_discrete_right.mpr fun z ↦ ?_⟩
  let _ : TopologicalSpace (⨂[R] _ : G ⧸ U, A) := ⊥
  have : DiscreteTopology (⨂[R] _ : G ⧸ U, A) := ⟨rfl⟩
  have : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU
  have hc := (Representation.continuous_wreathTensor_apply
    (Representation.ofDistribMulAction R U A)
    (by simpa only [Representation.ofDistribMulAction_apply_apply] using
      (continuous_smul : Continuous fun p : U × A ↦ p.1 • p.2)) z.toTensor).comp
    (U.continuous_monomialHom hU s)
  have hof : Continuous (ofTensor : (⨂[R] _ : G ⧸ U, A) → U.TensorInduced s R A) :=
    continuous_of_discreteTopology
  refine (hof.comp hc).congr fun g ↦ congrArg ofTensor ?_
  exact ((U.tensorInducedRepresentation_apply s (Representation.ofDistribMulAction R U A)
    g z.toTensor).symm).trans
    (U.tensorInducedAlgAut_apply_eq_tensorInducedRepresentation s R A g z.toTensor).symm

end ContinuousAction

end Subgroup.TensorInduced

namespace OpenSubgroup

/-- For a finite-index open subgroup `U : OpenSubgroup G` and a discrete `U`-semiring `A` with
continuous `U`-action, the `G`-action on `U.toSubgroup.TensorInduced s R A` (equipped with a
discrete topology) is continuous. -/
theorem continuousSMul_tensorInduced {G : Type v} [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] (U : OpenSubgroup G) (s : U.toSubgroup.LeftTransversal)
    [U.toSubgroup.FiniteIndex] (R : Type u) (A : Type w) [CommSemiring R] [Semiring A]
    [Algebra R A] [TopologicalSpace A] [DiscreteTopology A]
    [TopologicalSpace (U.toSubgroup.TensorInduced s R A)]
    [DiscreteTopology (U.toSubgroup.TensorInduced s R A)]
    [MulSemiringAction U.toSubgroup A] [SMulCommClass U.toSubgroup R A]
    [ContinuousSMul U.toSubgroup A] :
    ContinuousSMul G (U.toSubgroup.TensorInduced s R A) :=
  Subgroup.TensorInduced.continuousSMul_of_isOpen U.isOpen'

end OpenSubgroup

namespace TauCeti

attribute [local instance] DiscreteTopology.instContinuousSMul

namespace DiscreteRep

section AlgebraIso

variable {G : Type v} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  (U : Subgroup G) (hU : IsOpen (U : Set G)) (s : U.LeftTransversal) [U.FiniteIndex]
  (R : Type u) [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  (A : Type w) [Ring A] [Algebra R A] [TopologicalSpace A] [DiscreteTopology A]
  [MulSemiringAction U A] [SMulCommClass U R A] [ContinuousSMul U A]

/-- The bundled tensor-induced `G`-ring `U.TensorInduced s R A` (equipped with the discrete
topology) as a discrete continuous `G`-representation. -/
@[expose] noncomputable def tensorInducedAlgebra :
    DiscreteRep.{u, v, max u v w} R G :=
  letI : TopologicalSpace (U.TensorInduced s R A) := ⊥
  letI : DiscreteTopology (U.TensorInduced s R A) := ⟨rfl⟩
  letI : ContinuousSMul R (U.TensorInduced s R A) := ⟨continuous_of_discreteTopology⟩
  letI : ContinuousSMul G (U.TensorInduced s R A) :=
    Subgroup.TensorInduced.continuousSMul_of_isOpen hU
  { V := U.TensorInduced s R A }

/-- The underlying carrier of `tensorInducedAlgebra` is `U.TensorInduced s R A`. -/
@[simp]
theorem tensorInducedAlgebra_V :
    (tensorInducedAlgebra U hU s R A).V = U.TensorInduced s R A := (rfl)

/-- The representation carried by `tensorInducedAlgebra` acts by the `G`-action on
`U.TensorInduced s R A`. -/
@[simp]
theorem tensorInducedAlgebra_ρ_apply (g : G) (z : U.TensorInduced s R A) :
    (tensorInducedAlgebra U hU s R A).ρ g z = g • z := (rfl)

/-- As an object of `DiscreteRep R G`, `U.TensorInduced s R A` is canonically isomorphic to
`DiscreteRep.tensorInduced U hU s` of `A`. -/
noncomputable def tensorInducedAlgebraIso :
    tensorInducedAlgebra U hU s R A ≅ tensorInduced U hU s { V := A } where
  hom := (Subgroup.TensorInduced.representationEquiv U s R A).toIntertwiningMap
  inv := (Subgroup.TensorInduced.representationEquiv U s R A).symm.toIntertwiningMap
  hom_inv_id := Representation.IntertwiningMap.ext <| LinearMap.ext <|
    (Subgroup.TensorInduced.representationEquiv U s R A).symm_apply_apply
  inv_hom_id := Representation.IntertwiningMap.ext <| LinearMap.ext <|
    (Subgroup.TensorInduced.representationEquiv U s R A).apply_symm_apply

/-- The forward map of `tensorInducedAlgebraIso` unwraps `toTensor`. -/
@[simp]
theorem tensorInducedAlgebraIso_hom_apply (z : U.TensorInduced s R A) :
    (tensorInducedAlgebraIso U hU s R A).hom.toLinearMap z = z.toTensor :=
  (Representation.IntertwiningMap.toLinearMap_apply _ _
    (Subgroup.TensorInduced.representationEquiv U s R A).toIntertwiningMap z).trans (by simp)

/-- The inverse map of `tensorInducedAlgebraIso` wraps a tensor via `ofTensor`. -/
@[simp]
theorem tensorInducedAlgebraIso_inv_apply (z : ⨂[R] _ : G ⧸ U, A) :
    (tensorInducedAlgebraIso U hU s R A).inv.toLinearMap z =
      Subgroup.TensorInduced.ofTensor z :=
  (Representation.IntertwiningMap.toLinearMap_apply _ _
    (Subgroup.TensorInduced.representationEquiv U s R A).symm.toIntertwiningMap z).trans (by simp)

end AlgebraIso

section Multiplication

variable {G : Type v} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  (U : Subgroup G) (hU : IsOpen (U : Set G)) (s : U.LeftTransversal) [U.FiniteIndex]
  (R : Type u) [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  (A : Type (max u v w)) [CommRing A] [Algebra R A] [TopologicalSpace A] [DiscreteTopology A]
  [MulSemiringAction G A] [SMulCommClass G R A] [ContinuousSMul G A]

/-- Evens' twisted multiplication as a morphism in `DiscreteRep R G` from the tensor induction of a
discrete commutative `G`-algebra `A` to `A`. -/
noncomputable def tensorInducedMulHom :
    tensorInduced U hU s ({ V := A } : DiscreteRep.{u, v, max u v w} R U) ⟶
      ({ V := A } : DiscreteRep.{u, v, max u v w} R G) :=
  letI : Fintype (G ⧸ U) := U.fintypeQuotientOfFiniteIndex
  U.tensorInducedMulIntertwiningMap s R A

/-- Pointwise evaluation of `tensorInducedMulHom` agrees with `Subgroup.tensorInducedMulAlgHom`. -/
theorem tensorInducedMulHom_apply [inst : Fintype (G ⧸ U)] (z : ⨂[R] _ : G ⧸ U, A) :
    (tensorInducedMulHom U hU s R A).toLinearMap z =
      U.tensorInducedMulAlgHom s R A z := by
  cases Subsingleton.elim inst U.fintypeQuotientOfFiniteIndex
  let _ : Fintype (G ⧸ U) := U.fintypeQuotientOfFiniteIndex
  rw [tensorInducedMulHom]
  exact (LinearMap.congr_fun (U.tensorInducedMulIntertwiningMap_toLinearMap s R A) z).trans
    (AlgHom.toLinearMap_apply _ z)

/-- On a pure tensor, `tensorInducedMulHom` applies each coset's transversal representative and
multiplies the resulting elements in `A`. -/
theorem tensorInducedMulHom_apply_tprod [Fintype (G ⧸ U)] (m : G ⧸ U → A) :
    (tensorInducedMulHom U hU s R A).toLinearMap (PiTensorProduct.tprod R m) =
      ∏ x : G ⧸ U, U.leftTransversalRep s x • m x :=
  (tensorInducedMulHom_apply U hU s R A (PiTensorProduct.tprod R m)).trans
    (U.tensorInducedMulAlgHom_tprod s R A m)

/-- `tensorInducedMulHom` sends `1` to `1`. -/
theorem tensorInducedMulHom_apply_one :
    (tensorInducedMulHom U hU s R A).toLinearMap (1 : ⨂[R] _ : G ⧸ U, A) = (1 : A) := by
  let _ : Fintype (G ⧸ U) := U.fintypeQuotientOfFiniteIndex
  exact (tensorInducedMulHom_apply U hU s R A 1).trans (map_one _)

/-- `tensorInducedMulHom` preserves tensor multiplication. -/
theorem tensorInducedMulHom_apply_mul (a b : ⨂[R] _ : G ⧸ U, A) :
    (tensorInducedMulHom U hU s R A).toLinearMap (a * b) =
      (((tensorInducedMulHom U hU s R A).toLinearMap a : A) *
        ((tensorInducedMulHom U hU s R A).toLinearMap b : A) : A) := by
  let _ : Fintype (G ⧸ U) := U.fintypeQuotientOfFiniteIndex
  exact (tensorInducedMulHom_apply U hU s R A (a * b)).trans
    ((map_mul _ a b).trans (congrArg₂ (· * ·)
      (tensorInducedMulHom_apply U hU s R A a).symm
      (tensorInducedMulHom_apply U hU s R A b).symm))

/-- Changing the left transversal commutes with `tensorInducedMulHom`. -/
@[reassoc (attr := simp)]
theorem tensorInducedChangeTransversalIso_hom_comp_mulHom (t : U.LeftTransversal) :
    (tensorInducedChangeTransversalIso U hU s t
        ({ V := A } : DiscreteRep.{u, v, max u v w} R U)).hom ≫
      tensorInducedMulHom U hU s R A =
      tensorInducedMulHom U hU t R A := by
  let _ : Fintype (G ⧸ U) := U.fintypeQuotientOfFiniteIndex
  refine Representation.IntertwiningMap.ext (LinearMap.ext fun z ↦ ?_)
  have hcomp := (LinearMap.congr_fun
    (DiscreteRep.comp_toLinearMap
      (tensorInducedChangeTransversalIso U hU s t
        ({ V := A } : DiscreteRep.{u, v, max u v w} R U)).hom
      (tensorInducedMulHom U hU s R A)) z).trans (LinearMap.comp_apply _ _ z)
  have hct : (tensorInducedChangeTransversalIso U hU s t
      ({ V := A } : DiscreteRep.{u, v, max u v w} R U)).hom.toLinearMap z =
      U.tensorInducedChangeTransversalAlgEquiv s t R A z :=
    (LinearMap.congr_fun (tensorInducedChangeTransversalIso_hom_toLinearMap U hU s t
      ({ V := A } : DiscreteRep.{u, v, max u v w} R U)) z).trans
      ((LinearEquiv.congr_fun (U.tensorInducedChangeTransversal_toLinearEquiv s t
        ({ V := A } : DiscreteRep.{u, v, max u v w} R U).ρ) z).trans
        (LinearEquiv.congr_fun
          (U.tensorInducedChangeTransversalAlgEquiv_toLinearEquiv s t R A).symm z))
  exact hcomp.trans <|
    (tensorInducedMulHom_apply U hU s R A _).trans <|
      (congrArg (U.tensorInducedMulAlgHom s R A) hct).trans <|
        (U.tensorInducedMulAlgHom_changeTransversal s R A t z).trans
          (tensorInducedMulHom_apply U hU t R A z).symm

end Multiplication

end DiscreteRep

section Smooth

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : Subgroup G) (hU : IsOpen (U : Set G)) (s : U.LeftTransversal) [U.FiniteIndex]
  (R : Type u) [CommRing R] [TopologicalSpace R] [DiscreteTopology R]

/-- Smooth counterpart of `DiscreteRep.tensorInducedAlgebraIso`: the smooth discrete object of
`U.TensorInduced s R A` is isomorphic to smooth tensor induction of `A`. -/
noncomputable def smoothTensorInducedAlgebraIso
    (A : Type w) [Ring A] [Algebra R A] [TopologicalSpace A] [DiscreteTopology A]
    [MulSemiringAction U A] [SMulCommClass U R A] [ContinuousSMul U A] :
    (toSmoothDiscrete R G).obj (DiscreteRep.tensorInducedAlgebra U hU s R A) ≅
      (toSmoothDiscrete R G).obj
        (DiscreteRep.tensorInduced U hU s ({ V := A } : DiscreteRep.{u, v, w} R U)) :=
  (toSmoothDiscrete R G).mapIso (DiscreteRep.tensorInducedAlgebraIso U hU s R A)

variable (A : Type (max u v w)) [CommRing A] [Algebra R A]
  [TopologicalSpace A] [DiscreteTopology A]
  [MulSemiringAction G A] [SMulCommClass G R A] [ContinuousSMul G A]

/-- **Evens' twisted multiplication on smooth discrete representations.**

The source is written in the simp-normal form of `smoothTensorInductionFunctor_obj` applied to
`(toSmoothDiscrete R U).obj { V := A }`, matching `smoothTensorInducedChangeTransversalIso` and
`TopPairing.smoothTensorInduced`. -/
noncomputable def smoothTensorInducedMulHom :
    (toSmoothDiscrete R G).obj
        (DiscreteRep.tensorInduced U hU s
          ((ofSmoothDiscrete R U).obj
            ((toSmoothDiscrete R U).obj ({ V := A } : DiscreteRep.{u, v, max u v w} R U)))) ⟶
      (toSmoothDiscrete R G).obj ({ V := A } : DiscreteRep.{u, v, max u v w} R G) :=
  (toSmoothDiscrete R G).map (DiscreteRep.tensorInducedMulHom U hU s R A)

/-- Pointwise evaluation of `smoothTensorInducedMulHom` agrees with
`Subgroup.tensorInducedMulAlgHom`, which is an `R`-algebra homomorphism on the tensor power. -/
theorem smoothTensorInducedMulHom_apply [Fintype (G ⧸ U)] (z : ⨂[R] _ : G ⧸ U, A) :
    ((smoothTensorInducedMulHom U hU s R A).hom.hom z : A) =
      U.tensorInducedMulAlgHom s R A z :=
  DiscreteRep.tensorInducedMulHom_apply U hU s R A z

/-- On a pure tensor, `smoothTensorInducedMulHom` applies each coset's transversal representative
and multiplies the results in `A`. -/
@[simp]
theorem smoothTensorInducedMulHom_apply_tprod [Fintype (G ⧸ U)] (m : G ⧸ U → A) :
    (smoothTensorInducedMulHom U hU s R A).hom.hom (PiTensorProduct.tprod R m) =
      ∏ x : G ⧸ U, U.leftTransversalRep s x • m x :=
  DiscreteRep.tensorInducedMulHom_apply_tprod U hU s R A m

/-- `smoothTensorInducedMulHom` sends `1` to `1`. -/
@[simp]
theorem smoothTensorInducedMulHom_apply_one :
    (smoothTensorInducedMulHom U hU s R A).hom.hom (1 : ⨂[R] _ : G ⧸ U, A) = (1 : A) :=
  DiscreteRep.tensorInducedMulHom_apply_one U hU s R A

/-- On a `G`-fixed element `a : A`, `smoothTensorInducedMulHom` sends the constant pure tensor
`⨂ₜ _, a` to `a ^ U.index`. -/
theorem smoothTensorInducedMulHom_apply_tprod_const_of_smul_eq {a : A}
    (ha : ∀ g : G, g • a = a) :
    (smoothTensorInducedMulHom U hU s R A).hom.hom (PiTensorProduct.tprod R fun _ : G ⧸ U ↦ a) =
      a ^ U.index := by
  let _ : Fintype (G ⧸ U) := U.fintypeQuotientOfFiniteIndex
  rw [smoothTensorInducedMulHom_apply_tprod]
  simp only [ha, Finset.prod_const, Finset.card_univ, Subgroup.index_eq_card,
    Nat.card_eq_fintype_card]
  rfl

/-- Changing the left transversal commutes with `smoothTensorInducedMulHom`. -/
@[reassoc (attr := simp)]
theorem smoothTensorInducedChangeTransversalIso_hom_comp_mulHom (t : U.LeftTransversal) :
    (smoothTensorInducedChangeTransversalIso U hU s t
        ((toSmoothDiscrete R U).obj ({ V := A } : DiscreteRep.{u, v, max u v w} R U))).hom ≫
      smoothTensorInducedMulHom U hU s R A =
      smoothTensorInducedMulHom U hU t R A := by
  -- `smoothTensorInducedChangeTransversalIso` is not exposed, so identify its forward map with
  -- `(toSmoothDiscrete R G).map` of the discrete comparison on pure tensors before transporting.
  have hhom :
      (smoothTensorInducedChangeTransversalIso U hU s t
          ((toSmoothDiscrete R U).obj ({ V := A } : DiscreteRep.{u, v, max u v w} R U))).hom =
        (toSmoothDiscrete R G).map
          (DiscreteRep.tensorInducedChangeTransversalIso U hU s t
            ({ V := A } : DiscreteRep.{u, v, max u v w} R U)).hom := by
    refine ObjectProperty.hom_ext _ (TopRep.hom_ext (DFunLike.ext _ _ (LinearMap.congr_fun
      (PiTensorProduct.ext (MultilinearMap.ext fun m ↦ ?_)))))
    exact (LinearMap.compMultilinearMap_apply _ _ m).trans <|
      (smoothTensorInducedChangeTransversalIso_hom_apply_tprod U hU s t _ m).trans <|
        (DiscreteRep.tensorInducedChangeTransversalIso_hom_apply_tprod U hU s t _ m).symm.trans <|
          (toSmoothDiscrete_map_hom_hom_apply R G _ _).symm.trans
            (LinearMap.compMultilinearMap_apply _ _ m).symm
  exact (congrArg (· ≫ smoothTensorInducedMulHom U hU s R A) hhom).trans <|
    ((toSmoothDiscrete R G).map_comp _ _).symm.trans <|
      congrArg (toSmoothDiscrete R G).map
        (DiscreteRep.tensorInducedChangeTransversalIso_hom_comp_mulHom U hU s R A t)

/-- `smoothTensorInducedMulHom` intertwines the tensor induction of a multiplicative `TopPairing` on
`U` with a multiplicative `TopPairing` on `G` (for instance `ofDiscreteModulePairing` of
`AddMonoidHom.mul` when `R = ℤ`). -/
theorem smoothTensorInducedMulHom_apply_smoothTensorInduced_bil
    (PU : TopPairing
      ((toSmoothDiscrete R U).obj ({ V := A } : DiscreteRep.{u, v, max u v w} R U)).obj
      ((toSmoothDiscrete R U).obj ({ V := A } : DiscreteRep.{u, v, max u v w} R U)).obj
      ((toSmoothDiscrete R U).obj ({ V := A } : DiscreteRep.{u, v, max u v w} R U)).obj)
    (PG : TopPairing
      ((toSmoothDiscrete R G).obj ({ V := A } : DiscreteRep.{u, v, max u v w} R G)).obj
      ((toSmoothDiscrete R G).obj ({ V := A } : DiscreteRep.{u, v, max u v w} R G)).obj
      ((toSmoothDiscrete R G).obj ({ V := A } : DiscreteRep.{u, v, max u v w} R G)).obj)
    (hPU : ∀ x y : A, PU.bil x y = x * y)
    (hPG : ∀ x y : A, PG.bil x y = x * y)
    (a b : ⨂[R] _ : G ⧸ U, A) :
    (smoothTensorInducedMulHom U hU s R A).hom.hom
        ((PU.smoothTensorInduced.{u, v, max u w} U hU s).bil a b) =
      PG.bil ((smoothTensorInducedMulHom U hU s R A).hom.hom a)
        ((smoothTensorInducedMulHom U hU s R A).hom.hom b) := by
  let _ : Fintype (G ⧸ U) := U.fintypeQuotientOfFiniteIndex
  have hbil : (PU.bil : A →ₗ[R] A →ₗ[R] A) = LinearMap.mul R A := LinearMap.ext₂ hPU
  have hab : ((PU.smoothTensorInduced.{u, v, max u w} U hU s).bil a b : ⨂[R] _ : G ⧸ U, A) =
      a * b :=
    (LinearMap.congr_fun
      (LinearMap.congr_fun (TopPairing.smoothTensorInduced_bil U hU s PU) a) b).trans <|
      (LinearMap.congr_fun (LinearMap.congr_fun
        (congrArg (PiTensorProduct.map₂ (R := R) (s := fun _ : G ⧸ U ↦ A)
          (t := fun _ : G ⧸ U ↦ A) (t' := fun _ : G ⧸ U ↦ A)) (funext fun _ ↦ hbil)) a) b).trans
        (PiTensorProduct.map₂_mul_apply a b)
  have hlhs : @Eq A
      ((smoothTensorInducedMulHom U hU s R A).hom.hom
        ((PU.smoothTensorInduced.{u, v, max u w} U hU s).bil a b))
      (U.tensorInducedMulAlgHom s R A (a * b)) :=
    (congrArg (fun z : ⨂[R] _ : G ⧸ U, A ↦
      ((smoothTensorInducedMulHom U hU s R A).hom.hom z : A)) hab).trans
      (smoothTensorInducedMulHom_apply U hU s R A (a * b))
  have hmain : @Eq A
      ((smoothTensorInducedMulHom U hU s R A).hom.hom
        ((PU.smoothTensorInduced.{u, v, max u w} U hU s).bil a b))
      (PG.bil ((smoothTensorInducedMulHom U hU s R A).hom.hom a)
        ((smoothTensorInducedMulHom U hU s R A).hom.hom b)) :=
    hlhs.trans <|
      (map_mul (U.tensorInducedMulAlgHom s R A) a b).trans <|
        (congrArg₂ (HMul.hMul (α := A) (β := A) (γ := A))
          (smoothTensorInducedMulHom_apply U hU s R A a).symm
          (smoothTensorInducedMulHom_apply U hU s R A b).symm).trans
          (hPG ((smoothTensorInducedMulHom U hU s R A).hom.hom a)
            ((smoothTensorInducedMulHom U hU s R A).hom.hom b)).symm
  exact hmain

end Smooth

end TauCeti
