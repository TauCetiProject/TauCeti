/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coset.Basic
public import TauCeti.RepresentationTheory.Tensor.Induction.Diagonal
public import TauCeti.RepresentationTheory.Tensor.Induction.Smooth
public import TauCeti.LinearAlgebra.PiTensorProduct.Assoc
import TauCeti.GroupTheory.Perm.WreathProduct.Transitivity

/-!
# Transitivity of tensor induction

For a subgroup tower `V ≤ U ≤ G`, tensor induction from `V` to `U` followed by tensor induction
from `U` to `G` is equivalent to tensor induction from `V` to `G` for the composite transversal.
The equivalence flattens the two tensor indices and relabels them by the tower's coset
coordinates. It is natural in the representation of `V`. The final section lifts this comparison
to discrete continuous representations and to smooth discrete representations.

Only `G ⧸ U` must be finite: its finiteness permits expansion of tensors of sums in the inner
tensor powers. No finiteness of `U ⧸ V`, topology, or characteristic assumption is needed.
This is the coefficient-level regrouping used in transitivity of the multiplicative transfer.

The discrete and smooth lifts additionally assume that both subgroup inclusions have finite
index and that the subgroups are open, exactly as required by their tensor-induction functors.

## Main definitions

* `Subgroup.tensorInducedTransitivity`: the algebraic intertwining equivalence.
* `TauCeti.DiscreteRep.tensorInducedTransitivityIso`: the comparison for discrete continuous
  representations.
* `TauCeti.smoothTensorInducedTransitivityIso`: the comparison for smooth discrete
  representations.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Transactions of the American Mathematical Society 108 (1963), §§2–3 and §6.1, pp. 60–61
  (the module identification preceding Proposition 1).
-/

public section

open scoped TensorProduct

namespace Subgroup

open TauCeti

universe u v w

variable {R : Type u} [CommSemiring R] {G : Type v} [Group G]
  {U V : Subgroup G} (hVU : V ≤ U) (s : U.LeftTransversal)
  [Finite (G ⧸ U)] {M : Type w} [AddCommMonoid M] [Module R M]

/-- Flatten the tensor powers of a subgroup tower and relabel their product index by the cosets
of the smaller subgroup, using the outer transversal. -/
noncomputable def tensorInducedTransitivityLinearEquiv :
    (⨂[R] _ : G ⧸ U, ⨂[R] _ : U ⧸ V.subgroupOf U, M) ≃ₗ[R]
      (⨂[R] _ : G ⧸ V, M) :=
  PiTensorProduct.prodEquiv.trans
    (PiTensorProduct.reindex R (fun _ ↦ M)
      (quotientEquivProdOfLE' hVU (leftTransversalRep U s) (leftTransversalRep_mk U s)).symm)

/-- On tensors of pure tensors, regrouping reads the two coordinates of each coset. -/
@[simp] theorem tensorInducedTransitivityLinearEquiv_tprod
    (m : (G ⧸ U) → (U ⧸ V.subgroupOf U) → M) :
    tensorInducedTransitivityLinearEquiv (R := R) hVU s (PiTensorProduct.tprod R
      fun a ↦ PiTensorProduct.tprod R (m a)) =
      PiTensorProduct.tprod R (fun q : G ⧸ V ↦
        m (quotientEquivProdOfLE' hVU (leftTransversalRep U s)
          (leftTransversalRep_mk U s) q).1
          (quotientEquivProdOfLE' hVU (leftTransversalRep U s)
            (leftTransversalRep_mk U s) q).2) := by
  simp [tensorInducedTransitivityLinearEquiv]

/-- The inverse linear regrouping expands a pure tensor according to the two coset indices. -/
@[simp] theorem tensorInducedTransitivityLinearEquiv_symm_tprod (m : G ⧸ V → M) :
    (tensorInducedTransitivityLinearEquiv (R := R) hVU s).symm
        (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R (fun a ↦ PiTensorProduct.tprod R (fun b ↦
        m ((quotientEquivProdOfLE' hVU (leftTransversalRep U s)
          (leftTransversalRep_mk U s)).symm (a, b)))) := by
  apply (tensorInducedTransitivityLinearEquiv hVU s).injective
  simp only [LinearEquiv.apply_symm_apply, tensorInducedTransitivityLinearEquiv_tprod,
    Equiv.symm_apply_apply, Prod.mk.eta]

/-- Tensor induction is transitive along a subgroup tower, with the composite transversal on
the direct induction. The representation of `V` is restricted to `V.subgroupOf U` through its
canonical equivalence with `V`. -/
noncomputable def tensorInducedTransitivity (t : (V.subgroupOf U).LeftTransversal)
    (ρ : Representation R V M) :
    (U.tensorInducedRepresentation s ((V.subgroupOf U).tensorInducedRepresentation t
      (ρ.comp (subgroupOfEquivOfLe hVU : V.subgroupOf U →* V)))).Equiv
      (V.tensorInducedRepresentation (compositeLeftTransversal hVU s t) ρ) :=
  Representation.Equiv.mk (tensorInducedTransitivityLinearEquiv hVU s) (fun g ↦ by
    apply PiTensorProduct.ext_sigma_tprod
    intro m
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      tensorInducedRepresentation_apply_tprod, tensorInducedTransitivityLinearEquiv_tprod]
    simp only [MonoidHom.comp_apply]
    congr 1
    funext q
    let e := quotientEquivProdOfLE' hVU (leftTransversalRep U s) (leftTransversalRep_mk U s)
    have hcoords := quotientEquivProdOfLE'_inv_smul_symm U (leftTransversalRep U s)
      hVU (leftTransversalRep_mk U s) (e q).1 (e q).2 g
    rw [Prod.mk.eta, e.symm_apply_apply] at hcoords
    have hword : (subgroupOfEquivOfLe hVU)
        (((V.subgroupOf U).monomialHom t ((U.monomialHom s g).left (e q).1)).left
          (e q).2) =
        (V.monomialHom (compositeLeftTransversal hVU s t) g).left q := by
      simpa [e] using (congrArg (fun a ↦ a.left q)
        (monomialHom_compositeLeftTransversal hVU s t g)).symm
    -- Identify the composed representation's group argument with the underlying subgroup
    -- equivalence, and write both coefficient indices using the same coset-coordinate map `e`.
    change ρ ((subgroupOfEquivOfLe hVU) _)
        (m (g⁻¹ • (e q).1) (((U.monomialHom s g).left (e q).1)⁻¹ • (e q).2)) =
      ρ ((V.monomialHom (compositeLeftTransversal hVU s t) g).left q)
        (m (e (g⁻¹ • q)).1 (e (g⁻¹ • q)).2)
    rw [hword]
    congr 1
    rw [monomialHom_left]
    exact congrArg (fun p ↦ m p.1 p.2) hcoords.symm)

/-- The transitivity equivalence is the flattening and coset-reindexing linear equivalence. -/
theorem tensorInducedTransitivity_toLinearEquiv (t : (V.subgroupOf U).LeftTransversal)
    (ρ : Representation R V M) :
    (tensorInducedTransitivity hVU s t ρ).toLinearEquiv =
      tensorInducedTransitivityLinearEquiv hVU s := by
  simp only [tensorInducedTransitivity, Representation.Equiv.toLinearEquiv_mk']

/-- The transitivity equivalence evaluates by the named linear regrouping. -/
theorem tensorInducedTransitivity_apply (t : (V.subgroupOf U).LeftTransversal)
    (ρ : Representation R V M)
    (z : ⨂[R] _ : G ⧸ U, ⨂[R] _ : U ⧸ V.subgroupOf U, M) :
    tensorInducedTransitivity hVU s t ρ z =
      tensorInducedTransitivityLinearEquiv hVU s z := by
  simp only [tensorInducedTransitivity, Representation.Equiv.mk_apply]

/-- The representation comparison flattens pure tensors using the tower's coset coordinates. -/
@[simp] theorem tensorInducedTransitivity_tprod (t : (V.subgroupOf U).LeftTransversal)
    (ρ : Representation R V M) (m : (G ⧸ U) → (U ⧸ V.subgroupOf U) → M) :
    tensorInducedTransitivity hVU s t ρ (PiTensorProduct.tprod R
      fun a ↦ PiTensorProduct.tprod R (m a)) =
      PiTensorProduct.tprod R (fun q : G ⧸ V ↦
        m (quotientEquivProdOfLE' hVU (leftTransversalRep U s)
          (leftTransversalRep_mk U s) q).1
          (quotientEquivProdOfLE' hVU (leftTransversalRep U s)
            (leftTransversalRep_mk U s) q).2) := by
  rw [tensorInducedTransitivity_apply, tensorInducedTransitivityLinearEquiv_tprod]

/-- The inverse comparison regroups a pure tensor according to the two coset indices. -/
@[simp] theorem tensorInducedTransitivity_symm_tprod (t : (V.subgroupOf U).LeftTransversal)
    (ρ : Representation R V M) (m : G ⧸ V → M) :
    (tensorInducedTransitivity hVU s t ρ).symm (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R (fun a ↦ PiTensorProduct.tprod R (fun b ↦
        m ((quotientEquivProdOfLE' hVU (leftTransversalRep U s)
          (leftTransversalRep_mk U s)).symm (a, b)))) := by
  apply (tensorInducedTransitivity hVU s t ρ).toLinearEquiv.injective
  simp only [Representation.Equiv.toLinearEquiv_apply,
    Representation.Equiv.coe_toIntertwiningMap, Representation.Equiv.apply_symm_apply,
    tensorInducedTransitivity_tprod, Equiv.symm_apply_apply, Prod.mk.eta]

/-- Regrouping is natural in an intertwining map: applying that map to each of the inner
factors and then regrouping equals applying the tensor-induced map after regrouping. -/
theorem tensorInducedTransitivity_naturality (t : (V.subgroupOf U).LeftTransversal)
    {N : Type*} [AddCommMonoid N] [Module R N]
    {ρ : Representation R V M} {τ : Representation R V N} (f : ρ.IntertwiningMap τ)
    (z : ⨂[R] _ : G ⧸ U, ⨂[R] _ : U ⧸ V.subgroupOf U, M) :
    let e := (subgroupOfEquivOfLe hVU : V.subgroupOf U →* V)
    let f' : Representation.IntertwiningMap (ρ.comp e) (τ.comp e) :=
      { toLinearMap := f.toLinearMap
        isIntertwining' := fun v ↦ f.isIntertwining' (e v) }
    tensorInducedTransitivity hVU s t τ (((f'.tensorInduced t).tensorInduced s) z) =
      f.tensorInduced (compositeLeftTransversal hVU s t)
        (tensorInducedTransitivity hVU s t ρ z) := by
  dsimp only
  have H : (tensorInducedTransitivityLinearEquiv (R := R) (M := N) hVU s).toLinearMap ∘ₗ
        PiTensorProduct.map (fun _ : G ⧸ U ↦
          PiTensorProduct.map (fun _ : U ⧸ V.subgroupOf U ↦ f.toLinearMap)) =
      PiTensorProduct.map (fun _ : G ⧸ V ↦ f.toLinearMap) ∘ₗ
        (tensorInducedTransitivityLinearEquiv hVU s).toLinearMap := by
    apply LinearMap.ext
    intro x
    simp only [tensorInducedTransitivityLinearEquiv, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.trans_apply, PiTensorProduct.prodEquiv_map]
    exact (PiTensorProduct.map_reindex
      (fun _ : (G ⧸ U) × (U ⧸ V.subgroupOf U) ↦ f.toLinearMap)
      (quotientEquivProdOfLE' hVU (leftTransversalRep U s)
        (leftTransversalRep_mk U s)).symm (PiTensorProduct.prodEquiv x)).symm
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    tensorInducedTransitivity_apply,
    Representation.IntertwiningMap.tensorInduced_toLinearMap,
    ← Representation.IntertwiningMap.toLinearMap_apply] using LinearMap.congr_fun H z

end Subgroup

namespace TauCeti

open CategoryTheory

universe u v w

namespace DiscreteRep

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {U V : Subgroup G} (hVU : V ≤ U)

/-- Transport a discrete representation of `V` to the canonically isomorphic subgroup
`V.subgroupOf U`. This is the coefficient identification used when tensor induction is iterated
along a subgroup tower. -/
@[expose] noncomputable def subgroupOfTransport (A : DiscreteRep.{u, v, w} R V) :
    DiscreteRep.{u, v, w} R (V.subgroupOf U) := by
  let e : V.subgroupOf U →* V := Subgroup.subgroupOfEquivOfLe hVU
  let ρ := A.ρ.comp e
  letI : DistribMulAction (V.subgroupOf U) A.V := .compHom A.V ρ
  letI : SMulCommClass (V.subgroupOf U) R A.V :=
    ⟨fun g r x ↦ (ρ g).map_smul r x⟩
  have he : Continuous (e : V.subgroupOf U → V) := by
    exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  letI : ContinuousSMul (V.subgroupOf U) A.V :=
    ⟨(continuous_smul.comp ((he.comp continuous_fst).prodMk continuous_snd)).congr
      fun _ ↦ rfl⟩
  exact { V := A.V }

omit [DiscreteTopology R] [IsTopologicalGroup G] in
/-- Transport to `V.subgroupOf U` does not change the coefficient module. -/
@[simp] theorem subgroupOfTransport_V (A : DiscreteRep.{u, v, w} R V) :
    (subgroupOfTransport hVU A).V = A.V := (rfl)

omit [DiscreteTopology R] [IsTopologicalGroup G] in
/-- The transported action is the original action through the canonical subgroup equivalence. -/
@[simp] theorem subgroupOfTransport_ρ_apply (A : DiscreteRep.{u, v, w} R V)
    (g : V.subgroupOf U) (x : A.V) :
    (subgroupOfTransport hVU A).ρ g x =
      A.ρ (Subgroup.subgroupOfEquivOfLe hVU g) x := (rfl)

/-- Transport of discrete representations across the canonical equivalence
`V.subgroupOf U ≃* V`. -/
@[expose] noncomputable def subgroupOfTransportFunctor :
    DiscreteRep.{u, v, w} R V ⥤ DiscreteRep.{u, v, w} R (V.subgroupOf U) where
  obj A := subgroupOfTransport hVU A
  map {_A _B} f :=
    { toLinearMap := f.toLinearMap
      isIntertwining' := fun g ↦ f.isIntertwining' (Subgroup.subgroupOfEquivOfLe hVU g) }
  map_id A := Representation.IntertwiningMap.ext (DiscreteRep.id_toLinearMap A)
  map_comp f g := Representation.IntertwiningMap.ext (DiscreteRep.comp_toLinearMap f g)

omit [DiscreteTopology R] [IsTopologicalGroup G] in
/-- The subgroup-transport functor keeps the underlying linear map of a morphism. -/
@[simp] theorem subgroupOfTransportFunctor_map_toLinearMap
    {A B : DiscreteRep.{u, v, w} R V}
    (f : A ⟶ B) :
    ((subgroupOfTransportFunctor hVU).map f).toLinearMap = f.toLinearMap := (rfl)

variable (s : U.LeftTransversal) (t : (V.subgroupOf U).LeftTransversal)
  (hU : IsOpen (U : Set G)) (hV : IsOpen (V : Set G))
  [U.FiniteIndex] [(V.subgroupOf U).FiniteIndex]

/-- Iterated tensor induction of a discrete continuous representation is isomorphic to direct
tensor induction along the composite transversal. -/
noncomputable def tensorInducedTransitivityIso (A : DiscreteRep.{u, v, w} R V) :
    letI : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
    tensorInduced U hU s
        (tensorInduced (V.subgroupOf U) (U.subgroupOf_isOpen V hV) t
          (subgroupOfTransport hVU A)) ≅
      tensorInduced V hV (Subgroup.compositeLeftTransversal hVU s t) A := by
  let _ : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
  exact
    { hom := (Subgroup.tensorInducedTransitivity hVU s t A.ρ).toIntertwiningMap
      inv := (Subgroup.tensorInducedTransitivity hVU s t A.ρ).symm.toIntertwiningMap
      hom_inv_id := Representation.IntertwiningMap.ext <| LinearMap.ext <|
        (Subgroup.tensorInducedTransitivity hVU s t A.ρ).symm_apply_apply
      inv_hom_id := Representation.IntertwiningMap.ext <| LinearMap.ext <|
        (Subgroup.tensorInducedTransitivity hVU s t A.ρ).apply_symm_apply }

/-- The forward map of discrete transitivity is the algebraic tensor-regrouping equivalence. -/
theorem tensorInducedTransitivityIso_hom_toLinearMap (A : DiscreteRep.{u, v, w} R V) :
    letI : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
    (tensorInducedTransitivityIso hVU s t hU hV A).hom.toLinearMap =
      (Subgroup.tensorInducedTransitivity hVU s t A.ρ).toLinearEquiv.toLinearMap := (rfl)

/-- On pure tensors, discrete transitivity flattens the two coset coordinates. -/
@[simp] theorem tensorInducedTransitivityIso_hom_apply_tprod
    (A : DiscreteRep.{u, v, w} R V)
    (m : (G ⧸ U) → (U ⧸ V.subgroupOf U) → A.V) :
    letI : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
    (tensorInducedTransitivityIso hVU s t hU hV A).hom.toLinearMap
        (PiTensorProduct.tprod R fun a ↦ PiTensorProduct.tprod R (m a)) =
      PiTensorProduct.tprod R (fun q : G ⧸ V ↦
        m (Subgroup.quotientEquivProdOfLE' hVU (Subgroup.leftTransversalRep U s)
          (Subgroup.leftTransversalRep_mk U s) q).1
          (Subgroup.quotientEquivProdOfLE' hVU (Subgroup.leftTransversalRep U s)
            (Subgroup.leftTransversalRep_mk U s) q).2) := by
  let _ : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
  exact Subgroup.tensorInducedTransitivity_tprod hVU s t A.ρ m

/-- The discrete tensor-induction transitivity comparison is natural in the coefficient
representation. -/
@[reassoc]
theorem tensorInducedTransitivityIso_hom_naturality
    {A B : DiscreteRep.{u, v, w} R V} (f : A ⟶ B) :
    letI : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
    (tensorInductionFunctor U hU s).map
          ((tensorInductionFunctor (V.subgroupOf U) (U.subgroupOf_isOpen V hV) t).map
            ((subgroupOfTransportFunctor hVU).map f)) ≫
        (tensorInducedTransitivityIso hVU s t hU hV B).hom =
      (tensorInducedTransitivityIso hVU s t hU hV A).hom ≫
        (tensorInductionFunctor V hV (Subgroup.compositeLeftTransversal hVU s t)).map f := by
  let _ : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
  apply Representation.IntertwiningMap.ext
  exact LinearMap.ext fun z ↦
    Subgroup.tensorInducedTransitivity_naturality hVU s t f z

end DiscreteRep

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {U V : Subgroup G} (hVU : V ≤ U)

/-- Transport smooth discrete coefficients from `V` to the canonically isomorphic subgroup
`V.subgroupOf U`. -/
@[expose] noncomputable def smoothSubgroupOfFunctor :
    SmoothDiscreteTopRep.{u, v, w} R V ⥤
      SmoothDiscreteTopRep.{u, v, w} R (V.subgroupOf U) :=
  ofSmoothDiscrete R V ⋙ DiscreteRep.subgroupOfTransportFunctor hVU ⋙
    toSmoothDiscrete R (V.subgroupOf U)

variable (s : U.LeftTransversal) (t : (V.subgroupOf U).LeftTransversal)
  (hU : IsOpen (U : Set G)) (hV : IsOpen (V : Set G))
  [U.FiniteIndex] [(V.subgroupOf U).FiniteIndex]

/-- Iterated smooth tensor induction is isomorphic to direct smooth tensor induction along the
composite transversal.

The objects are written in the simp-normal form produced by `smoothTensorInductionFunctor_obj`,
so that the pure-tensor computation rule below can be a simp lemma. -/
noncomputable def smoothTensorInducedTransitivityIso
    (A : SmoothDiscreteTopRep.{u, v, w} R V) :
    letI : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
    (toSmoothDiscrete R G).obj
        (DiscreteRep.tensorInduced U hU s
          ((ofSmoothDiscrete R U).obj
            ((toSmoothDiscrete R U).obj
              (DiscreteRep.tensorInduced (V.subgroupOf U) (U.subgroupOf_isOpen V hV) t
                ((ofSmoothDiscrete R (V.subgroupOf U)).obj
                  ((smoothSubgroupOfFunctor hVU).obj A)))))) ≅
      (toSmoothDiscrete R G).obj
        (DiscreteRep.tensorInduced V hV (Subgroup.compositeLeftTransversal hVU s t)
          ((ofSmoothDiscrete R V).obj A)) := by
  let _ : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
  exact (toSmoothDiscrete R G).mapIso
    (DiscreteRep.tensorInducedTransitivityIso hVU s t hU hV
      ((ofSmoothDiscrete R V).obj A))

/-- On pure tensors, smooth transitivity flattens the two coset coordinates. -/
@[simp] theorem smoothTensorInducedTransitivityIso_hom_apply_tprod
    (A : SmoothDiscreteTopRep.{u, v, w} R V)
    (m : (G ⧸ U) → (U ⧸ V.subgroupOf U) → A.obj.V) :
    letI : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
    (smoothTensorInducedTransitivityIso hVU s t hU hV A).hom.hom.hom
        (PiTensorProduct.tprod R fun a ↦ PiTensorProduct.tprod R (m a)) =
      PiTensorProduct.tprod R (fun q : G ⧸ V ↦
        m (Subgroup.quotientEquivProdOfLE' hVU (Subgroup.leftTransversalRep U s)
          (Subgroup.leftTransversalRep_mk U s) q).1
          (Subgroup.quotientEquivProdOfLE' hVU (Subgroup.leftTransversalRep U s)
            (Subgroup.leftTransversalRep_mk U s) q).2) := by
  let _ : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
  exact DiscreteRep.tensorInducedTransitivityIso_hom_apply_tprod hVU s t hU hV
    ((ofSmoothDiscrete R V).obj A) m

/-- The smooth tensor-induction transitivity comparison is natural in the coefficient
representation. -/
@[reassoc]
theorem smoothTensorInducedTransitivityIso_hom_naturality
    {A B : SmoothDiscreteTopRep.{u, v, w} R V} (f : A ⟶ B) :
    letI : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
    (smoothTensorInductionFunctor R G U hU s).map
          ((smoothTensorInductionFunctor R U (V.subgroupOf U)
            (U.subgroupOf_isOpen V hV) t).map ((smoothSubgroupOfFunctor hVU).map f)) ≫
        (smoothTensorInducedTransitivityIso hVU s t hU hV B).hom =
      (smoothTensorInducedTransitivityIso hVU s t hU hV A).hom ≫
        (smoothTensorInductionFunctor R G V hV
          (Subgroup.compositeLeftTransversal hVU s t)).map f := by
  let _ : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
  apply ObjectProperty.hom_ext
  apply TopRep.hom_ext
  apply ContIntertwiningMap.toIntertwiningMap_injective
  exact DiscreteRep.tensorInducedTransitivityIso_hom_naturality hVU s t hU hV
    ((ofSmoothDiscrete R V).map f)

end TauCeti

namespace Subgroup

open TauCeti

universe u v w

variable {R : Type u} [CommRing R] {G : Type v} [Group G]
  {U V : Subgroup G} (hVU : V ≤ U) (s : U.LeftTransversal)
  [Finite (G ⧸ U)] {M : Type w} [AddCommGroup M] [Module R M]

/-- Transitivity carries the iterated invariant diagonal to the direct invariant diagonal. -/
theorem tensorInducedTransitivity_tensorInducedDiagonal
    (t : (V.subgroupOf U).LeftTransversal) (ρ : Representation R V M) (x : ρ.invariants) :
    let τ : Representation R (V.subgroupOf U) M :=
      ρ.comp (subgroupOfEquivOfLe hVU : V.subgroupOf U →* V)
    let y : τ.invariants := ⟨x, fun v ↦ x.property ((subgroupOfEquivOfLe hVU) v)⟩
    tensorInducedTransitivity hVU s t ρ
        (((V.subgroupOf U).tensorInducedRepresentation t τ).tensorInducedDiagonal s
          (τ.tensorInducedDiagonal t y)) =
      (ρ.tensorInducedDiagonal (compositeLeftTransversal hVU s t) x :
        ⨂[R] _ : G ⧸ V, M) := by
  simp only [Representation.coe_tensorInducedDiagonal, tensorInducedTransitivity_tprod]

end Subgroup
