/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Tensor.Induction.Ring.Basic
public import TauCeti.RepresentationTheory.Tensor.Induction.ChangeTransversal.Discrete

/-!
# Tensor induction of discrete continuous rings and its equivariant multiplication

For an open finite-index subgroup `U ≤ G` of a topological group and a discrete `U`-algebra `A`
with continuous `U`-action, the tensor power `⨂[R] _ : G ⧸ U, A` endowed with the discrete
topology has continuous `G`-action under `Subgroup.tensorInducedMulSemiringAction`. When `A` is a
discrete commutative `G`-algebra with continuous `G`-action, Evens's twisted multiplication
`Subgroup.tensorInducedMulAlgHom` lifts to a morphism of discrete continuous `G`-representations
`TauCeti.DiscreteRep.tensorInducedMulHom` and to a morphism of smooth discrete `G`-representations
`TauCeti.smoothTensorInducedMulHom`.

These morphisms commute with the change-of-transversal comparisons
`TauCeti.DiscreteRep.tensorInducedChangeTransversalIso` and
`TauCeti.smoothTensorInducedChangeTransversalIso`. Moreover, for continuous `U`- and
`G`-equivariant bilinear pairings `PU` and `PG` on `A` whose underlying maps are ring
multiplication (`∀ a b, PU.bil a b = a * b` and `∀ a b, PG.bil a b = a * b`, covering `R`-algebra
multiplication, `PG.res U.subtype`, and `TauCeti.ofDiscreteModulePairing AddMonoidHom.mul` over
`ℤ`),
`TauCeti.smoothTensorInducedMulHom` intertwines the tensor-induced pairing
`PU.smoothTensorInduced` with `PG`, providing the exact coefficient compatibility hypothesis
consumed by `TauCeti.TopPairing.cup_coeffMap`.

## Main definitions

* `TauCeti.DiscreteRep.tensorInducedMulHom`: Evens's twisted multiplication as a morphism in
  `TauCeti.DiscreteRep R G`.
* `TauCeti.smoothTensorInducedMulHom`: Evens's twisted multiplication as a morphism in
  `TauCeti.SmoothDiscreteTopRep R G`.

## Main results

* `TauCeti.WreathProduct.continuous_tensorAlgAut_apply`,
  `TauCeti.WreathProduct.instContinuousSMulPiTensorProduct`,
  `Subgroup.continuous_tensorInducedAlgAut_apply`, `Subgroup.tensorInducedContinuousSMul`:
  continuity of the wreath-product and tensor-induced algebra actions on discrete tensor powers.
* `TauCeti.DiscreteRep.tensorInducedChangeTransversalIso_hom_tensorInducedMulHom`,
  `TauCeti.smoothTensorInducedChangeTransversalIso_hom_smoothTensorInducedMulHom`:
  transversal independence of the discrete and smooth-discrete twisted multiplication morphisms.
* `TauCeti.TopPairing.smoothTensorInduced_bil_eq_mul`,
  `TauCeti.smoothTensorInducedMulHom_bil_of_eq_mul`: compatibility of the smooth tensor-induced
  multiplication pairing with factorwise tensor-power multiplication and Evens's twisted
  multiplication morphism.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Trans. Amer. Math. Soc. **108** (1963), §§2, 5–6.
-/

public section

open CategoryTheory
open scoped TensorProduct

universe u v w x

/-! ### Continuity of the wreath-product and tensor-induced algebra actions -/

namespace TauCeti.WreathProduct

variable {R : Type u} [CommSemiring R]
  {D : Type v} [Group D] [TopologicalSpace D]
  {A : Type w} [Semiring A] [Algebra R A] [TopologicalSpace A] [DiscreteTopology A]
  [MulSemiringAction D A] [SMulCommClass D R A] [ContinuousSMul D A]
  {ι : Type x} [Finite ι] [TopologicalSpace ι] [DiscreteTopology ι]
  [TopologicalSpace (⨂[R] _ : ι, A)] [DiscreteTopology (⨂[R] _ : ι, A)]

/-- For a discrete `D`-algebra `A` with continuous `D`-action and a finite discrete index type `ι`,
orbit maps of `TauCeti.WreathProduct.tensorAlgAut` on the discrete tensor power `⨂[R] _ : ι, A` are
continuous. -/
theorem continuous_tensorAlgAut_apply (z : ⨂[R] _ : ι, A) :
    Continuous fun w : WreathProduct D ι ↦ tensorAlgAut R D A ι w z := by
  have hρ : Continuous fun p : D × A ↦ Representation.ofDistribMulAction R D A p.1 p.2 := by
    simpa only [Representation.ofDistribMulAction_apply_apply] using
      (continuous_smul : Continuous fun p : D × A ↦ p.1 • p.2)
  simpa only [← tensorAlgAut_toLinearMap, AlgEquiv.toLinearMap_apply] using
    Representation.continuous_wreathTensor_apply (Representation.ofDistribMulAction R D A) hρ z

/-- For a discrete `D`-algebra `A` with continuous `D`-action and a finite discrete index type `ι`,
the wreath-product action on the discrete tensor power `⨂[R] _ : ι, A` is continuous. -/
instance instContinuousSMulPiTensorProduct :
    ContinuousSMul (WreathProduct D ι) (⨂[R] _ : ι, A) :=
  ⟨continuous_prod_of_discrete_right.mpr fun z ↦
    (continuous_tensorAlgAut_apply z).congr fun w ↦ (smul_piTensorProduct_def w z).symm⟩

end TauCeti.WreathProduct

namespace Subgroup

variable {G : Type v} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  (U : Subgroup G) [U.FiniteIndex]
  (R : Type u) [CommSemiring R]
  (A : Type w) [Semiring A] [Algebra R A] [TopologicalSpace A] [DiscreteTopology A]
  [MulSemiringAction U A] [SMulCommClass U R A] [ContinuousSMul U A]

/-- For an open finite-index subgroup `U ≤ G` and a discrete `U`-algebra `A` with continuous
`U`-action, orbit maps of `Subgroup.tensorInducedAlgAut` on the discrete tensor power
`⨂[R] _ : G ⧸ U, A` are continuous. -/
theorem continuous_tensorInducedAlgAut_apply (hU : IsOpen (U : Set G)) (s : U.LeftTransversal)
    [TopologicalSpace (⨂[R] _ : G ⧸ U, A)] [DiscreteTopology (⨂[R] _ : G ⧸ U, A)]
    (z : ⨂[R] _ : G ⧸ U, A) :
    Continuous fun g : G ↦ U.tensorInducedAlgAut R A s g z := by
  have : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU
  exact ((TauCeti.WreathProduct.continuous_tensorAlgAut_apply z).comp
    (U.continuous_monomialHom hU s)).congr fun g ↦
      (AlgEquiv.congr_fun (U.tensorInducedAlgAut_apply R A s g) z).symm

/-- On the discrete tensor power `⨂[R] _ : G ⧸ U, A`, the `G`-action
`Subgroup.tensorInducedMulSemiringAction` along an open finite-index subgroup `U ≤ G` is
continuous whenever `U` acts continuously on the discrete `U`-algebra `A`. -/
theorem tensorInducedContinuousSMul (hU : IsOpen (U : Set G)) (s : U.LeftTransversal)
    [TopologicalSpace (⨂[R] _ : G ⧸ U, A)] [DiscreteTopology (⨂[R] _ : G ⧸ U, A)] :
    @ContinuousSMul G (⨂[R] _ : G ⧸ U, A) (U.tensorInducedMulSemiringAction R A s).toSMul _ _ := by
  let := U.tensorInducedMulSemiringAction R A s
  exact ⟨continuous_prod_of_discrete_right.mpr fun z ↦
    (U.continuous_tensorInducedAlgAut_apply R A hU s z).congr fun g ↦
      (U.tensorInducedMulSemiringAction_smul R A s g z).symm⟩

end Subgroup

/-! ### Twisted multiplication on discrete continuous representations -/

namespace TauCeti

namespace DiscreteRep

section RingAction

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  (U : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex]
  (A : Type w) [Ring A] [Algebra R A] [TopologicalSpace A] [DiscreteTopology A]
  [MulSemiringAction U A] [SMulCommClass U R A] [ContinuousSMul R A] [ContinuousSMul U A]

/-- On the discrete `U`-representation `{ V := A }` of a discrete `U`-algebra `A`,
`TauCeti.DiscreteRep.tensorInduced` acts via `Subgroup.tensorInducedAlgAut`. -/
theorem tensorInduced_ρ_eq_tensorInducedAlgAut (s : U.LeftTransversal) (g : G)
    (z : ⨂[R] _ : G ⧸ U, A) :
    (tensorInduced U hU s ({ V := A } : DiscreteRep.{u, v, w} R U)).ρ g z =
      U.tensorInducedAlgAut R A s g z := by
  rw [tensorInduced_ρ_apply, ← U.tensorInducedAlgAut_toLinearMap R A s g,
    AlgEquiv.toLinearMap_apply]

end RingAction

section TwistedMultiplication

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  (U : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex]
  (A : Type (max u v w)) [CommRing A] [Algebra R A]
  [TopologicalSpace A] [DiscreteTopology A]
  [MulSemiringAction G A] [SMulCommClass G R A] [ContinuousSMul R A] [ContinuousSMul G A]

/-- Evens's twisted multiplication as a morphism in `TauCeti.DiscreteRep R G` from the
tensor-induced discrete representation of a discrete commutative `G`-algebra `A` to `A`. -/
noncomputable def tensorInducedMulHom (s : U.LeftTransversal) :
    tensorInduced U hU s ({ V := A } : DiscreteRep.{u, v, max u v w} R U) ⟶
      ({ V := A } : DiscreteRep.{u, v, max u v w} R G) :=
  letI : Fintype (G ⧸ U) := U.fintypeQuotientOfFiniteIndex
  U.tensorInducedMulIntertwiningMap R A s

/-- With any `Fintype (G ⧸ U)` instance in scope, the underlying linear map of
`TauCeti.DiscreteRep.tensorInducedMulHom` is `Subgroup.tensorInducedMulAlgHom`. -/
@[simp]
theorem tensorInducedMulHom_toLinearMap (s : U.LeftTransversal) [Fintype (G ⧸ U)] :
    (tensorInducedMulHom (R := R) U hU A s).toLinearMap =
      (U.tensorInducedMulAlgHom R A s).toLinearMap :=
  (@Subgroup.tensorInducedMulIntertwiningMap_toLinearMap G _ U R _ A _ _ _ _ s
    U.fintypeQuotientOfFiniteIndex).trans
    (congrArg AlgHom.toLinearMap
      (U.tensorInducedMulAlgHom_congr_fintype R A s U.fintypeQuotientOfFiniteIndex inferInstance))

/-- Evaluating `TauCeti.DiscreteRep.tensorInducedMulHom` on a tensor gives
`Subgroup.tensorInducedMulAlgHom`. -/
theorem tensorInducedMulHom_apply (s : U.LeftTransversal) [Fintype (G ⧸ U)]
    (z : ⨂[R] _ : G ⧸ U, A) :
    (tensorInducedMulHom (R := R) U hU A s).toLinearMap z =
      U.tensorInducedMulAlgHom R A s z :=
  LinearMap.congr_fun (tensorInducedMulHom_toLinearMap (R := R) U hU A s) z

/-- On a pure tensor, `TauCeti.DiscreteRep.tensorInducedMulHom` multiplies the factors twisted by
the chosen coset representatives. -/
theorem tensorInducedMulHom_apply_tprod (s : U.LeftTransversal) [Fintype (G ⧸ U)]
    (a : G ⧸ U → A) :
    (tensorInducedMulHom (R := R) U hU A s).toLinearMap (PiTensorProduct.tprod R a) =
      ∏ x, U.leftTransversalRep s x • a x :=
  (tensorInducedMulHom_apply (R := R) U hU A s (PiTensorProduct.tprod R a)).trans
    (U.tensorInducedMulAlgHom_tprod R A s a)

/-- `TauCeti.DiscreteRep.tensorInducedMulHom` commutes with
`TauCeti.DiscreteRep.tensorInducedChangeTransversalIso`. -/
@[reassoc (attr := simp)]
theorem tensorInducedChangeTransversalIso_hom_tensorInducedMulHom (s t : U.LeftTransversal) :
    (tensorInducedChangeTransversalIso U hU s t
        ({ V := A } : DiscreteRep.{u, v, max u v w} R U)).hom ≫
      tensorInducedMulHom (R := R) U hU A s =
      tensorInducedMulHom (R := R) U hU A t := by
  let : Fintype (G ⧸ U) := U.fintypeQuotientOfFiniteIndex
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  have hcomp :
      ((tensorInducedChangeTransversalIso U hU s t
          ({ V := A } : DiscreteRep.{u, v, max u v w} R U)).hom ≫
        tensorInducedMulHom (R := R) U hU A s).toLinearMap z =
      (tensorInducedMulHom (R := R) U hU A s).toLinearMap
        ((tensorInducedChangeTransversalIso U hU s t
            ({ V := A } : DiscreteRep.{u, v, max u v w} R U)).hom.toLinearMap z) :=
    LinearMap.congr_fun (DiscreteRep.comp_toLinearMap _ _) z
  have hct :
      (tensorInducedChangeTransversalIso U hU s t
          ({ V := A } : DiscreteRep.{u, v, max u v w} R U)).hom.toLinearMap z =
      U.tensorInducedChangeTransversalAlgEquiv R A s t z := by
    have hlin := LinearMap.congr_fun
      (tensorInducedChangeTransversalIso_hom_toLinearMap U hU s t
        ({ V := A } : DiscreteRep.{u, v, max u v w} R U)) z
    exact hlin.trans <| LinearEquiv.congr_fun
      ((U.tensorInducedChangeTransversal_toLinearEquiv s t
          (Representation.ofDistribMulAction R U A)).trans
        (U.tensorInducedChangeTransversalAlgEquiv_toLinearEquiv R A s t).symm) z
  exact hcomp.trans <|
    (congrArg (tensorInducedMulHom (R := R) U hU A s).toLinearMap hct).trans <|
    (tensorInducedMulHom_apply (R := R) U hU A s _).trans <|
    (U.tensorInducedMulAlgHom_changeTransversalAlgEquiv R A s t z).trans
      (tensorInducedMulHom_apply (R := R) U hU A t z).symm

end TwistedMultiplication

end DiscreteRep

/-! ### Twisted multiplication on smooth discrete representations and cup-product compatibility -/

section SmoothPairing

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex]
  {A : Type (max v w)} [Ring A] [Algebra R A]
  [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction U A] [SMulCommClass U R A] [ContinuousSMul R A] [ContinuousSMul U A]

/-- If `P` is a continuous `U`-equivariant bilinear pairing on `ofDiscreteModule R U A` whose
underlying map is multiplication in `A`, then the tensor-induced pairing `P.smoothTensorInduced`
has underlying bilinear map equal to multiplication in the tensor-power algebra
`⨂[R] _ : G ⧸ U, A`. -/
theorem TopPairing.smoothTensorInduced_bil_eq_mul
    (P : TopPairing (ofDiscreteModule R U A) (ofDiscreteModule R U A) (ofDiscreteModule R U A))
    (hP : ∀ a b : A, P.bil a b = a * b) (s : U.LeftTransversal)
    (z w : ⨂[R] _ : G ⧸ U, A) :
    (P.smoothTensorInduced.{u, v, w} U hU s
        (A := ⟨ofDiscreteModule R U A, ofDiscreteModule_isSmoothDiscrete R U A⟩)
        (B := ⟨ofDiscreteModule R U A, ofDiscreteModule_isSmoothDiscrete R U A⟩)
        (C := ⟨ofDiscreteModule R U A, ofDiscreteModule_isSmoothDiscrete R U A⟩)).bil z w =
      z * w := by
  have hbil : (P.bil : A →ₗ[R] A →ₗ[R] A) = LinearMap.mul R A :=
    LinearMap.ext₂ fun (a b : A) ↦
      (hP a b).trans (LinearMap.mul_apply' (R := R) (A := A) a b).symm
  have hmul :
      PiTensorProduct.map₂ (fun _ : G ⧸ U ↦ LinearMap.mul R A) =
        PiTensorProduct.mul (R := R) (A := fun _ : G ⧸ U ↦ A) :=
    PiTensorProduct.ext <| MultilinearMap.ext fun x ↦
      PiTensorProduct.ext <| MultilinearMap.ext fun y ↦ by
        simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map₂_tprod_tprod,
          PiTensorProduct.mul_tprod_tprod, LinearMap.mul_apply', Pi.mul_def]
  have hmap₂ :
      (P.smoothTensorInduced.{u, v, w} U hU s
          (A := ⟨ofDiscreteModule R U A, ofDiscreteModule_isSmoothDiscrete R U A⟩)
          (B := ⟨ofDiscreteModule R U A, ofDiscreteModule_isSmoothDiscrete R U A⟩)
          (C := ⟨ofDiscreteModule R U A, ofDiscreteModule_isSmoothDiscrete R U A⟩)).bil z w =
        PiTensorProduct.map₂ (fun _ : G ⧸ U ↦ (P.bil : A →ₗ[R] A →ₗ[R] A)) z w :=
    LinearMap.congr_fun (LinearMap.congr_fun
      (P.smoothTensorInduced_bil.{u, v, w} U hU s
        (A := ⟨ofDiscreteModule R U A, ofDiscreteModule_isSmoothDiscrete R U A⟩)
        (B := ⟨ofDiscreteModule R U A, ofDiscreteModule_isSmoothDiscrete R U A⟩)
        (C := ⟨ofDiscreteModule R U A, ofDiscreteModule_isSmoothDiscrete R U A⟩)) z) w
  have hmap₂' :
      PiTensorProduct.map₂ (fun _ : G ⧸ U ↦ (P.bil : A →ₗ[R] A →ₗ[R] A)) z w =
        PiTensorProduct.map₂ (fun _ : G ⧸ U ↦ LinearMap.mul R A) z w :=
    congrArg (fun f : A →ₗ[R] A →ₗ[R] A ↦ PiTensorProduct.map₂ (fun _ : G ⧸ U ↦ f) z w) hbil
  have hmul' : PiTensorProduct.map₂ (fun _ : G ⧸ U ↦ LinearMap.mul R A) z w = z * w :=
    (LinearMap.congr_fun (LinearMap.congr_fun hmul z) w).trans (PiTensorProduct.mul_def z w).symm
  exact hmap₂.trans (hmap₂'.trans hmul')

end SmoothPairing

section SmoothDiscrete

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex]
  (A : Type (max u v w)) [CommRing A] [Algebra R A]
  [TopologicalSpace A] [DiscreteTopology A]
  [MulSemiringAction G A] [SMulCommClass G R A] [ContinuousSMul R A] [ContinuousSMul G A]

/-- Evens's twisted multiplication as a morphism in `TauCeti.SmoothDiscreteTopRep R G` from the
smooth tensor induction of `⟨ofDiscreteModule R U A, ofDiscreteModule_isSmoothDiscrete R U A⟩`
(definitionally `smoothDiscreteResTopRep U ⟨ofDiscreteModule R G A, ...⟩`) to
`⟨ofDiscreteModule R G A, ofDiscreteModule_isSmoothDiscrete R G A⟩`.

The source is written in the simp-normal form produced by
`TauCeti.smoothTensorInductionFunctor_obj` so that evaluation and change-of-transversal lemmas
apply directly. -/
noncomputable def smoothTensorInducedMulHom (s : U.LeftTransversal) :
    (toSmoothDiscrete R G).obj
        (DiscreteRep.tensorInduced U hU s
          ((ofSmoothDiscrete R U).obj
            ⟨ofDiscreteModule R U A, ofDiscreteModule_isSmoothDiscrete R U A⟩)) ⟶
      ⟨ofDiscreteModule R G A, ofDiscreteModule_isSmoothDiscrete R G A⟩ :=
  (toSmoothDiscrete R G).map (DiscreteRep.tensorInducedMulHom (R := R) U hU A s)

/-- Evaluating `TauCeti.smoothTensorInducedMulHom` on any tensor gives
`Subgroup.tensorInducedMulAlgHom`. -/
@[simp]
theorem smoothTensorInducedMulHom_hom_hom_apply (s : U.LeftTransversal) [Fintype (G ⧸ U)]
    (z : ⨂[R] _ : G ⧸ U, A) :
    (smoothTensorInducedMulHom (R := R) U hU A s).hom.hom z =
      U.tensorInducedMulAlgHom R A s z :=
  DiscreteRep.tensorInducedMulHom_apply (R := R) U hU A s z

/-- On a pure tensor, `TauCeti.smoothTensorInducedMulHom` multiplies the factors after acting on
each factor by its chosen coset representative. -/
theorem smoothTensorInducedMulHom_hom_hom_apply_tprod (s : U.LeftTransversal) [Fintype (G ⧸ U)]
    (a : G ⧸ U → A) :
    (smoothTensorInducedMulHom (R := R) U hU A s).hom.hom (PiTensorProduct.tprod R a) =
      ∏ x, U.leftTransversalRep s x • a x :=
  DiscreteRep.tensorInducedMulHom_apply_tprod (R := R) U hU A s a

/-- `TauCeti.smoothTensorInducedMulHom` commutes with
`TauCeti.smoothTensorInducedChangeTransversalIso`. -/
@[reassoc (attr := simp)]
theorem smoothTensorInducedChangeTransversalIso_hom_smoothTensorInducedMulHom
    (s t : U.LeftTransversal) :
    (smoothTensorInducedChangeTransversalIso U hU s t
        ⟨ofDiscreteModule R U A, ofDiscreteModule_isSmoothDiscrete R U A⟩).hom ≫
      smoothTensorInducedMulHom (R := R) U hU A s =
      smoothTensorInducedMulHom (R := R) U hU A t := by
  have hiso :
      (smoothTensorInducedChangeTransversalIso U hU s t
          ⟨ofDiscreteModule R U A, ofDiscreteModule_isSmoothDiscrete R U A⟩).hom =
        (toSmoothDiscrete R G).map
          (DiscreteRep.tensorInducedChangeTransversalIso U hU s t
            ({ V := A } : DiscreteRep.{u, v, max u v w} R U)).hom := by
    apply ObjectProperty.hom_ext
    apply TopRep.hom_ext
    apply ContIntertwiningMap.toIntertwiningMap_injective
    apply Representation.IntertwiningMap.ext
    refine PiTensorProduct.ext (MultilinearMap.ext fun m ↦ ?_)
    exact (smoothTensorInducedChangeTransversalIso_hom_apply_tprod U hU s t
        ⟨ofDiscreteModule R U A, ofDiscreteModule_isSmoothDiscrete R U A⟩ m).trans
      (DiscreteRep.tensorInducedChangeTransversalIso_hom_apply_tprod U hU s t
        ({ V := A } : DiscreteRep.{u, v, max u v w} R U) m).symm
  exact (congrArg (· ≫ smoothTensorInducedMulHom (R := R) U hU A s) hiso).trans <|
    ((toSmoothDiscrete R G).map_comp
      (DiscreteRep.tensorInducedChangeTransversalIso U hU s t
        ({ V := A } : DiscreteRep.{u, v, max u v w} R U)).hom
      (DiscreteRep.tensorInducedMulHom (R := R) U hU A s)).symm.trans <|
    congrArg (toSmoothDiscrete R G).map
      (DiscreteRep.tensorInducedChangeTransversalIso_hom_tensorInducedMulHom U hU A s t)

section Pairing

variable {A}

/-- `TauCeti.smoothTensorInducedMulHom` intertwines the tensor-induced pairing
`PU.smoothTensorInduced` with `PG` whenever `PU.bil` and `PG.bil` are multiplication in `A`. -/
theorem smoothTensorInducedMulHom_bil_of_eq_mul
    (PU : TopPairing (ofDiscreteModule R U A) (ofDiscreteModule R U A) (ofDiscreteModule R U A))
    (hPU : ∀ a b : A, PU.bil a b = a * b)
    (PG : TopPairing (ofDiscreteModule R G A) (ofDiscreteModule R G A) (ofDiscreteModule R G A))
    (hPG : ∀ a b : A, PG.bil a b = a * b) (s : U.LeftTransversal)
    (z w : ⨂[R] _ : G ⧸ U, A) :
    (smoothTensorInducedMulHom (R := R) U hU A s).hom.hom
        ((PU.smoothTensorInduced.{u, v, max u v w} U hU s
            (A := ⟨ofDiscreteModule R U A, ofDiscreteModule_isSmoothDiscrete R U A⟩)
            (B := ⟨ofDiscreteModule R U A, ofDiscreteModule_isSmoothDiscrete R U A⟩)
            (C := ⟨ofDiscreteModule R U A, ofDiscreteModule_isSmoothDiscrete R U A⟩)).bil z w) =
      PG.bil ((smoothTensorInducedMulHom (R := R) U hU A s).hom.hom z)
        ((smoothTensorInducedMulHom (R := R) U hU A s).hom.hom w) := by
  let : Fintype (G ⧸ U) := U.fintypeQuotientOfFiniteIndex
  exact (congrArg (smoothTensorInducedMulHom (R := R) U hU A s).hom.hom
      (PU.smoothTensorInduced_bil_eq_mul (R := R) U hU hPU s z w)).trans <|
    (smoothTensorInducedMulHom_hom_hom_apply U hU A s (z * w)).trans <|
    (map_mul (U.tensorInducedMulAlgHom R A s) z w).trans <|
    (congrArg₂ ((· * ·) : A → A → A)
      (smoothTensorInducedMulHom_hom_hom_apply U hU A s z).symm
      (smoothTensorInducedMulHom_hom_hom_apply U hU A s w).symm).trans
      (hPG _ _).symm

end Pairing

end SmoothDiscrete

/-! ### Worked example on smooth discrete coefficients -/

/-- On the discrete commutative `G`-ring `ℤ` with trivial continuous action of `C₂` and `U = ⊥`,
`TauCeti.smoothTensorInducedMulHom` intertwines the tensor-induced multiplication pairing
`(ofDiscreteModulePairing AddMonoidHom.mul ...).smoothTensorInduced` on `U` with the ambient
multiplication pairing `ofDiscreteModulePairing AddMonoidHom.mul ...` on `G`, sending
`(2 ⊗ 3, 5 ⊗ 7)` to `6 * 35 = 210 ≠ 0`. -/
example :
    ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G) (_ : IsTopologicalGroup G)
      (U : Subgroup G) (hU : IsOpen (U : Set G)) (_ : U.FiniteIndex)
      (_ : MulSemiringAction G ℤ) (_ : SMulCommClass G ℤ ℤ) (_ : ContinuousSMul G ℤ)
      (PU : TopPairing (ofDiscreteModule ℤ U ℤ) (ofDiscreteModule ℤ U ℤ) (ofDiscreteModule ℤ U ℤ))
      (PG : TopPairing (ofDiscreteModule ℤ G ℤ) (ofDiscreteModule ℤ G ℤ) (ofDiscreteModule ℤ G ℤ))
      (s : U.LeftTransversal) (z w : ⨂[ℤ] _ : G ⧸ U, ℤ),
      @Eq ℤ
        ((smoothTensorInducedMulHom (R := ℤ) U hU ℤ s).hom.hom
          ((PU.smoothTensorInduced.{0, 0, 0} U hU s
              (A := ⟨ofDiscreteModule ℤ U ℤ, ofDiscreteModule_isSmoothDiscrete ℤ U ℤ⟩)
              (B := ⟨ofDiscreteModule ℤ U ℤ, ofDiscreteModule_isSmoothDiscrete ℤ U ℤ⟩)
              (C := ⟨ofDiscreteModule ℤ U ℤ, ofDiscreteModule_isSmoothDiscrete ℤ U ℤ⟩)).bil z w))
        (PG.bil ((smoothTensorInducedMulHom (R := ℤ) U hU ℤ s).hom.hom z)
          ((smoothTensorInducedMulHom (R := ℤ) U hU ℤ s).hom.hom w)) ∧
      @Eq ℤ
        (PG.bil ((smoothTensorInducedMulHom (R := ℤ) U hU ℤ s).hom.hom z)
          ((smoothTensorInducedMulHom (R := ℤ) U hU ℤ s).hom.hom w))
        210 ∧ (210 : ℤ) ≠ 0 := by
  let G := Multiplicative (ZMod 2)
  let : TopologicalSpace G := ⊥
  have : DiscreteTopology G := ⟨rfl⟩
  have : IsTopologicalGroup G := {}
  let U : Subgroup G := ⊥
  have hU : IsOpen (U : Set G) := isOpen_discrete _
  let : Fintype (G ⧸ U) := Fintype.ofEquiv G QuotientGroup.quotientBot.toEquiv.symm
  let : DecidableEq (G ⧸ U) := Equiv.decidableEq QuotientGroup.quotientBot.toEquiv
  have : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let : MulSemiringAction G ℤ := MulSemiringAction.compHom ℤ (1 : G →* (ℤ ≃+* ℤ))
  have htriv : ∀ (g : G) (n : ℤ), g • n = n := fun g n ↦ by simp [MulAction.compHom_smul_def]
  have htrivU : ∀ (u : U) (n : ℤ), u • n = n := fun u n ↦ by
    rw [Subgroup.smul_def]
    exact htriv u n
  have : SMulCommClass G ℤ ℤ := ⟨fun g m n ↦ by simp [htriv]⟩
  have : ContinuousSMul G ℤ := ⟨continuous_of_discreteTopology⟩
  let PU : TopPairing (ofDiscreteModule ℤ U ℤ) (ofDiscreteModule ℤ U ℤ) (ofDiscreteModule ℤ U ℤ) :=
    ofDiscreteModulePairing (AddMonoidHom.mul : ℤ →+ ℤ →+ ℤ) fun u m n ↦ by simp [htrivU]
  have hPU : ∀ a b : ℤ, PU.bil a b = a * b := fun a b ↦
    ofDiscreteModulePairing_bil_apply (AddMonoidHom.mul : ℤ →+ ℤ →+ ℤ) _ a b
  let PG : TopPairing (ofDiscreteModule ℤ G ℤ) (ofDiscreteModule ℤ G ℤ) (ofDiscreteModule ℤ G ℤ) :=
    ofDiscreteModulePairing (AddMonoidHom.mul : ℤ →+ ℤ →+ ℤ) fun g m n ↦ by simp [htriv]
  have hPG : ∀ a b : ℤ, PG.bil a b = a * b := fun a b ↦
    ofDiscreteModulePairing_bil_apply (AddMonoidHom.mul : ℤ →+ ℤ →+ ℤ) _ a b
  let s : U.LeftTransversal :=
    ⟨Set.range QuotientGroup.quotientBot,
      Subgroup.isComplement_range_left fun x ↦ QuotientGroup.induction_on x fun _ ↦ rfl⟩
  let z : ⨂[ℤ] _ : G ⧸ U, ℤ :=
    PiTensorProduct.tprod ℤ fun x ↦ if QuotientGroup.quotientBot x = 1 then 2 else 3
  let w : ⨂[ℤ] _ : G ⧸ U, ℤ :=
    PiTensorProduct.tprod ℤ fun x ↦ if QuotientGroup.quotientBot x = 1 then 5 else 7
  have hz : @Eq ℤ ((smoothTensorInducedMulHom (R := ℤ) U hU ℤ s).hom.hom z) 6 := by
    refine (smoothTensorInducedMulHom_hom_hom_apply U hU ℤ s z).trans ?_
    rw [U.tensorInducedMulAlgHom_eq_mulAlgHom_of_smul_eq_self ℤ ℤ s htriv,
      PiTensorProduct.mulAlgHom_tprod, ← Equiv.prod_comp QuotientGroup.quotientBot.symm.toEquiv]
    simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, MulEquiv.apply_symm_apply]
    exact (by decide : (∏ x : Multiplicative (ZMod 2), if x = 1 then (2 : ℤ) else 3) = 6)
  have hw : @Eq ℤ ((smoothTensorInducedMulHom (R := ℤ) U hU ℤ s).hom.hom w) 35 := by
    refine (smoothTensorInducedMulHom_hom_hom_apply U hU ℤ s w).trans ?_
    rw [U.tensorInducedMulAlgHom_eq_mulAlgHom_of_smul_eq_self ℤ ℤ s htriv,
      PiTensorProduct.mulAlgHom_tprod, ← Equiv.prod_comp QuotientGroup.quotientBot.symm.toEquiv]
    simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, MulEquiv.apply_symm_apply]
    exact (by decide : (∏ x : Multiplicative (ZMod 2), if x = 1 then (5 : ℤ) else 7) = 35)
  refine ⟨G, inferInstance, inferInstance, inferInstance, U, hU, inferInstance,
    inferInstance, inferInstance, inferInstance, PU, PG, s, z, w,
    smoothTensorInducedMulHom_bil_of_eq_mul (R := ℤ) U hU PU hPU PG hPG s z w, ?_, by decide⟩
  exact (hPG _ _).trans <| (congrArg₂ ((· * ·) : ℤ → ℤ → ℤ) hz hw).trans (by decide)

end TauCeti
