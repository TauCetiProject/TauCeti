/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Tensor.Induction.ChangeTransversal.Basic
public import TauCeti.RepresentationTheory.Tensor.Induction.TrivialF2

/-!
# Change of transversal for discrete tensor induction

Tensor induction of a discrete continuous representation is independent of the chosen left
transversal.  This file lifts the algebraic comparison
`Subgroup.tensorInducedChangeTransversal` to the categories of discrete and smooth discrete
representations.  The comparisons are natural in the coefficient representation.

For trivial `𝔽₂` coefficients, the comparison commutes with the canonical identification of
the tensor-induced coefficient object with the ambient trivial coefficient object.  Consequently,
changing the transversal does not change the coefficient identification used by the cochain-level
Evens norm.

## Main definitions

* `TauCeti.DiscreteRep.tensorInducedChangeTransversalIso`: the comparison on discrete continuous
  representations.
* `TauCeti.DiscreteRep.tensorInductionChangeTransversalNatIso`: the comparison as a natural
  isomorphism of tensor-induction functors.
* `TauCeti.smoothTensorInducedChangeTransversalIso`: the comparison on smooth discrete
  representations.
* `TauCeti.smoothTensorInductionChangeTransversalNatIso`: its functorial form.
* `TauCeti.smoothTensorInducedTrivialF2Iso_changeTransversal_apply_tprod`: compatibility with
  the canonical trivial-`𝔽₂` coefficient identification.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  *Transactions of the American Mathematical Society* 108 (1963), §§2–5.
-/

public section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace TauCeti

namespace DiscreteRep

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  (U : Subgroup G) (hU : IsOpen (U : Set G)) (s t : U.LeftTransversal) [U.FiniteIndex]

/-- Changing the transversal gives an isomorphism between the corresponding tensor-induced
discrete continuous representations. -/
noncomputable def tensorInducedChangeTransversalIso (A : DiscreteRep.{u, v, w} R U) :
    tensorInduced U hU t A ≅ tensorInduced U hU s A where
  hom := (U.tensorInducedChangeTransversal s t A.ρ).toIntertwiningMap
  inv := (U.tensorInducedChangeTransversal s t A.ρ).symm.toIntertwiningMap
  hom_inv_id := by
    apply Representation.IntertwiningMap.ext
    exact LinearMap.ext fun z ↦
      (U.tensorInducedChangeTransversal s t A.ρ).symm_apply_apply z
  inv_hom_id := by
    apply Representation.IntertwiningMap.ext
    exact LinearMap.ext fun z ↦
      (U.tensorInducedChangeTransversal s t A.ρ).apply_symm_apply z

/-- The forward map of the discrete comparison is the algebraic change-of-transversal map. -/
theorem tensorInducedChangeTransversalIso_hom_toLinearMap (A : DiscreteRep.{u, v, w} R U) :
    (tensorInducedChangeTransversalIso U hU s t A).hom.toLinearMap =
      (U.tensorInducedChangeTransversal s t A.ρ).toLinearEquiv.toLinearMap := by
  rw [tensorInducedChangeTransversalIso]

/-- On a pure tensor, the discrete comparison applies the difference of the two transversal
representatives in every coset coordinate. -/
@[simp]
theorem tensorInducedChangeTransversalIso_hom_apply_tprod
    (A : DiscreteRep.{u, v, w} R U) (m : G ⧸ U → A.V) :
    (tensorInducedChangeTransversalIso U hU s t A).hom.toLinearMap
        (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun x ↦
        A.ρ ((Subgroup.monomialChangeTransversal U s t).left x) (m x) :=
  U.tensorInducedChangeTransversal_apply_tprod s t A.ρ m

/-- The discrete change-of-transversal comparison is natural in the coefficient
representation. -/
@[reassoc]
theorem tensorInducedChangeTransversalIso_hom_naturality
    {A B : DiscreteRep.{u, v, w} R U} (f : A ⟶ B) :
    (tensorInductionFunctor U hU t).map f ≫
        (tensorInducedChangeTransversalIso U hU s t B).hom =
      (tensorInducedChangeTransversalIso U hU s t A).hom ≫
        (tensorInductionFunctor U hU s).map f := by
  apply Representation.IntertwiningMap.ext
  apply PiTensorProduct.ext
  ext m
  -- The extensionality goal is wrapped in `MultilinearMap.compMultilinearMap`, so the functor-map
  -- and comparison projection lemmas cannot rewrite it. Unfold those two wrappers to expose the
  -- algebraic intertwining maps on the pure tensor.
  change (U.tensorInducedChangeTransversal s t B.ρ)
      (f.tensorInduced t (PiTensorProduct.tprod R m)) =
    f.tensorInduced s
      (U.tensorInducedChangeTransversal s t A.ρ (PiTensorProduct.tprod R m))
  rw [Representation.IntertwiningMap.tensorInduced_apply_tprod,
    U.tensorInducedChangeTransversal_apply_tprod,
    U.tensorInducedChangeTransversal_apply_tprod,
    Representation.IntertwiningMap.tensorInduced_apply_tprod]
  congr 1
  funext x
  exact (f.isIntertwining _ _ _ _).symm

/-- Tensor induction on discrete continuous representations is naturally independent of the
chosen transversal. -/
noncomputable def tensorInductionChangeTransversalNatIso :
    tensorInductionFunctor (R := R) U hU t ≅ tensorInductionFunctor (R := R) U hU s :=
  NatIso.ofComponents
    (fun A : DiscreteRep.{u, v, w} R U ↦ tensorInducedChangeTransversalIso U hU s t A)
    (fun {A B} (f : A ⟶ B) ↦
      tensorInducedChangeTransversalIso_hom_naturality U hU s t f)

/-- The component of the natural change-of-transversal isomorphism is the named discrete
comparison. -/
@[simp]
theorem tensorInductionChangeTransversalNatIso_app
    (A : DiscreteRep.{u, v, w} R U) :
    (tensorInductionChangeTransversalNatIso (R := R) U hU s t).app A =
      tensorInducedChangeTransversalIso U hU s t A := by
  rw [tensorInductionChangeTransversalNatIso]
  exact NatIso.ofComponents.app _ _ A

end DiscreteRep

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : Subgroup G) (hU : IsOpen (U : Set G)) (s t : U.LeftTransversal) [U.FiniteIndex]

/-- Changing the transversal gives an isomorphism between the corresponding smooth tensor-induced
representations. -/
noncomputable def smoothTensorInducedChangeTransversalIso
    (A : SmoothDiscreteTopRep.{u, v, w} R U) :
    (smoothTensorInductionFunctor R G U hU t).obj A ≅
      (smoothTensorInductionFunctor R G U hU s).obj A :=
  (toSmoothDiscrete R G).mapIso
    (DiscreteRep.tensorInducedChangeTransversalIso U hU s t
      ((ofSmoothDiscrete R U).obj A))

/-- On a pure tensor, the smooth comparison applies the difference of the two transversal
representatives in every coset coordinate. -/
theorem smoothTensorInducedChangeTransversalIso_hom_apply_tprod
    (A : SmoothDiscreteTopRep.{u, v, w} R U) (m : G ⧸ U → A.obj.V) :
    (smoothTensorInducedChangeTransversalIso U hU s t A).hom.hom.hom
        (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun x ↦
        A.obj.ρ ((Subgroup.monomialChangeTransversal U s t).left x) (m x) :=
  DiscreteRep.tensorInducedChangeTransversalIso_hom_apply_tprod U hU s t
    ((ofSmoothDiscrete R U).obj A) m

/-- The smooth comparison sends the named pure tensor for trivial `𝔽₂` coefficients to the
corresponding named pure tensor for the new transversal. -/
theorem smoothTensorInducedChangeTransversalIso_hom_apply_trivialF2Tprod
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (s t : U.LeftTransversal) [U.FiniteIndex]
    (m : G ⧸ U → (DiscreteRep.trivialF2 U).V) :
    (smoothTensorInducedChangeTransversalIso U hU s t
        ⟨trivialF2 U, isSmoothDiscrete_trivialF2 U⟩).hom.hom.hom
        (smoothTensorInducedTrivialF2Tprod G U hU t m) =
      smoothTensorInducedTrivialF2Tprod G U hU s fun x ↦
        (DiscreteRep.trivialF2 U).ρ
          ((Subgroup.monomialChangeTransversal U s t).left x) (m x) := by
  rw [smoothTensorInducedTrivialF2Tprod_eq, smoothTensorInducedTrivialF2Tprod_eq]
  exact smoothTensorInducedChangeTransversalIso_hom_apply_tprod U hU s t _ m

/-- The smooth change-of-transversal comparison is natural in the coefficient representation. -/
@[reassoc]
theorem smoothTensorInducedChangeTransversalIso_hom_naturality
    {A B : SmoothDiscreteTopRep.{u, v, w} R U} (f : A ⟶ B) :
    (smoothTensorInductionFunctor R G U hU t).map f ≫
        (smoothTensorInducedChangeTransversalIso U hU s t B).hom =
      (smoothTensorInducedChangeTransversalIso U hU s t A).hom ≫
        (smoothTensorInductionFunctor R G U hU s).map f := by
  apply ObjectProperty.hom_ext
  apply TopRep.hom_ext
  apply ContIntertwiningMap.toIntertwiningMap_injective
  exact DiscreteRep.tensorInducedChangeTransversalIso_hom_naturality U hU s t
    ((ofSmoothDiscrete R U).map f)

/-- Smooth tensor induction is naturally independent of the chosen transversal. -/
noncomputable def smoothTensorInductionChangeTransversalNatIso :
    smoothTensorInductionFunctor R G U hU t ≅ smoothTensorInductionFunctor R G U hU s :=
  NatIso.ofComponents
    (fun A : SmoothDiscreteTopRep.{u, v, w} R U ↦
      smoothTensorInducedChangeTransversalIso U hU s t A)
    (fun {A B} (f : A ⟶ B) ↦
      smoothTensorInducedChangeTransversalIso_hom_naturality U hU s t f)

/-- The component of the smooth natural isomorphism is the named change-of-transversal
comparison. -/
@[simp]
theorem smoothTensorInductionChangeTransversalNatIso_app
    (A : SmoothDiscreteTopRep.{u, v, w} R U) :
    (smoothTensorInductionChangeTransversalNatIso U hU s t).app A =
      smoothTensorInducedChangeTransversalIso U hU s t A := by
  simp only [smoothTensorInductionChangeTransversalNatIso, NatIso.ofComponents.app]

/-- On pure tensors, changing the transversal does not change the canonical identification of
tensor-induced trivial `𝔽₂` coefficients with ambient trivial `𝔽₂` coefficients. -/
theorem smoothTensorInducedTrivialF2Iso_changeTransversal_apply_tprod
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (s t : U.LeftTransversal) [U.FiniteIndex]
    (m : G ⧸ U → (DiscreteRep.trivialF2 U).V) :
    trivialF2Equiv G
        ((smoothTensorInducedTrivialF2Iso G U hU s).hom.hom.hom
          ((smoothTensorInducedChangeTransversalIso U hU s t
              ⟨trivialF2 U, isSmoothDiscrete_trivialF2 U⟩).hom.hom.hom
            (smoothTensorInducedTrivialF2Tprod G U hU t m))) =
      trivialF2Equiv G
        ((smoothTensorInducedTrivialF2Iso G U hU t).hom.hom.hom
          (smoothTensorInducedTrivialF2Tprod G U hU t m)) := by
  rw [smoothTensorInducedChangeTransversalIso_hom_apply_trivialF2Tprod,
    smoothTensorInducedTrivialF2Iso_hom_apply_tprod,
    smoothTensorInducedTrivialF2Iso_hom_apply_tprod]
  congr 1
  funext x
  congr 1
  -- The action above comes from the discrete representation underlying `trivialF2`; its public
  -- computation lemma is stated for the smooth object, and rewriting cannot cross that opaque
  -- wrapper. Unfolding only the carrier projection aligns the two action expressions.
  change (trivialF2 U).ρ _ (m x) = m x
  exact trivialF2_ρ_apply_apply U _ _

end TauCeti
