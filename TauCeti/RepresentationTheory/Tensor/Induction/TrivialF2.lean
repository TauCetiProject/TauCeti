/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialF2
import TauCeti.LinearAlgebra.PiTensorProduct.ZMod
public import TauCeti.RepresentationTheory.Tensor.Induction.Discrete

/-!
# Smooth tensor induction of trivial F₂ coefficients

Tensor induction along an open finite-index subgroup acts on smooth discrete representations by
passing through the equivalent category of discrete continuous representations. For the canonical
trivial `𝔽₂` coefficient object, the resulting tensor power is again the canonical trivial
coefficient object of the ambient group.

The isomorphism multiplies the tensor factors. It is the coefficient identification needed before
the cochain-level Evens norm can be read as a class in `TauCeti.cohomF2 G` rather than in the
cohomology of an abstract tensor-induced coefficient object.

## Main definitions

* `TauCeti.smoothTensorInductionFunctor`: tensor induction on smooth discrete coefficients.
* `TauCeti.smoothTensorInducedTrivialF2Iso`: tensor induction of trivial `𝔽₂` coefficients
  is the canonical trivial `𝔽₂` coefficient object.

## References

* L. Evens, "A generalization of the transfer map in the cohomology of groups",
  *Transactions of the American Mathematical Society* 108 (1963), §§2–5.
-/

public section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace TauCeti

section Functor

variable (R : Type u) [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : Subgroup G) (hU : IsOpen (U : Set G)) (s : U.LeftTransversal) [U.FiniteIndex]

/-- Tensor induction on smooth discrete representations along an open finite-index subgroup.

The functor passes through the equivalent category of discrete continuous representations, where
the tensor power has the discrete topology and continuity of the induced action is available. -/
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

end Functor

section TrivialF2

variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : Subgroup G) (hU : IsOpen (U : Set G)) (s : U.LeftTransversal)
  [U.FiniteIndex]

/-- The finite quotient indexing the tensor factors of tensor induction. -/
noncomputable local instance quotientFintype : Fintype (G ⧸ U) :=
  U.fintypeQuotientOfFiniteIndex

private noncomputable def tensorInducedTrivialF2DiscreteIso :
    DiscreteRep.tensorInduced U hU s
        ((ofSmoothDiscrete ℤ U).obj ⟨trivialF2 U, isSmoothDiscrete_trivialF2 U⟩) ≅
      (ofSmoothDiscrete ℤ G).obj ⟨trivialF2 G, isSmoothDiscrete_trivialF2 G⟩ := by
  let AU := (ofSmoothDiscrete ℤ U).obj
    ⟨trivialF2 U, isSmoothDiscrete_trivialF2 U⟩
  let AG := DiscreteRep.trivialF2 G
  let TI := DiscreteRep.tensorInduced U hU s AU
  change TI ≅ AG
  let _ : Module ℤ AU.V := AU.module
  let _ : Module ℤ AG.V := AG.module
  let cU := (trivialF2Equiv U).toIntLinearEquiv
    (modM := AU.module)
    (modM₂ := AddCommGroup.toIntModule (ZMod 2))
  let cG := (trivialF2Equiv G).toIntLinearEquiv
    (modM := AG.module)
    (modM₂ := AddCommGroup.toIntModule (ZMod 2))
  let e :=
    (@PiTensorProduct.congr (G ⧸ U) ℤ _ (fun _ ↦ AU.V)
      (fun _ ↦ AU.addCommGroup.toAddCommMonoid) (fun _ ↦ AU.module)
      (fun _ ↦ ZMod 2) (fun _ ↦ inferInstance) (fun _ ↦ AddCommGroup.toIntModule (ZMod 2))
      (fun _ ↦ cU)) ≪≫ₗ
      PiTensorProduct.zmodEquiv 2 ≪≫ₗ cG.symm
  let f : TI.V →ₗ[ℤ] AG.V :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := e.map_smul }
  let fInv : AG.V →ₗ[ℤ] TI.V :=
    { toFun := e.symm
      map_add' := e.symm.map_add
      map_smul' := e.symm.map_smul }
  let fe : TI.V ≃ₗ[ℤ] AG.V :=
    { toLinearMap := f
      invFun := fInv
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply }
  have hAU (u : U) (x : AU.V) : AU.ρ u x = x := by
    change (trivialF2 U).ρ u x = x
    exact trivialF2_ρ_apply_apply U u x
  have hAG (g : G) (x : AG.V) : AG.ρ g x = x := by
    change (trivialF2 G).ρ g x = x
    exact trivialF2_ρ_apply_apply G g x
  have hfe (g : G) (z : TI.V) : fe (TI.ρ g z) = AG.ρ g (fe z) := by
    change e (U.tensorInducedRepresentation s AU.ρ g z) = AG.ρ g (e z)
    induction z using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      rw [map_smul, e.map_smul, e.map_smul, (AG.ρ g).map_smul]
      congr 1
      rw [Subgroup.tensorInducedRepresentation_apply_tprod]
      simp only [e, LinearEquiv.trans_apply, PiTensorProduct.congr_tprod,
        PiTensorProduct.zmodEquiv_tprod]
      rw [hAG]
      congr 1
      simp_rw [hAU]
      exact Equiv.prod_comp (MulAction.toPerm g⁻¹) fun i ↦ cU (x i)
    | add z z' hz hz' =>
      rw [map_add, e.map_add, hz, hz', e.map_add, (AG.ρ g).map_add]
  let hom := fe.toLinearMap.intertwiningMap_of_isIntertwiningMap TI.ρ AG.ρ hfe
  let inv := fe.symm.toLinearMap.intertwiningMap_of_isIntertwiningMap AG.ρ TI.ρ
    fun g x ↦ by
      change fe.symm (g • x) = g • fe.symm x
      simpa only [MulActionHom.inverse_apply, LinearEquiv.coe_coe] using
        (MulActionHom.inverse (M := G) ⟨fe, hfe⟩ fe.symm fe.symm_apply_apply
          fe.apply_symm_apply).map_smul g x
  exact
    { hom := hom
      inv := inv
      hom_inv_id := Representation.IntertwiningMap.ext (LinearMap.ext fe.symm_apply_apply)
      inv_hom_id := Representation.IntertwiningMap.ext (LinearMap.ext fe.apply_symm_apply) }

/-- Smooth tensor induction of the canonical trivial `𝔽₂` coefficient object is
isomorphic to the canonical trivial `𝔽₂` coefficient object of the ambient group.

On carriers the forward map multiplies the tensor factors. -/
noncomputable def smoothTensorInducedTrivialF2Iso :
    (smoothTensorInductionFunctor ℤ G U hU s).obj
        ⟨trivialF2 U, isSmoothDiscrete_trivialF2 U⟩ ≅
      ⟨trivialF2 G, isSmoothDiscrete_trivialF2 G⟩ :=
  (toSmoothDiscrete ℤ G).mapIso (tensorInducedTrivialF2DiscreteIso G U hU s)

/-- The pure tensor in the smooth tensor induction of trivial `𝔽₂` coefficients. -/
noncomputable def smoothTensorInducedTrivialF2Tprod
    (x : G ⧸ U → (DiscreteRep.trivialF2 U).V) :
    (DiscreteRep.tensorInduced U hU s
      (DiscreteRep.trivialF2 U)).V := by
  let A := DiscreteRep.trivialF2 U
  letI : Module ℤ A.V := A.module
  exact cast (DiscreteRep.tensorInduced_V U hU s A).symm
    (PiTensorProduct.tprod ℤ x)

/-- On a pure tensor, the smooth trivial-`𝔽₂` tensor-induction isomorphism multiplies
the underlying `ZMod 2` values. -/
theorem smoothTensorInducedTrivialF2Iso_hom_apply_tprod
    (x : G ⧸ U → (DiscreteRep.trivialF2 U).V) :
    trivialF2Equiv G ((smoothTensorInducedTrivialF2Iso G U hU s).hom.hom.hom
        (smoothTensorInducedTrivialF2Tprod G U hU s x)) =
      ∏ i, trivialF2Equiv U (x i) := by
  rw [smoothTensorInducedTrivialF2Iso, Functor.mapIso_hom]
  change trivialF2Equiv G
    (((toSmoothDiscrete ℤ G).map
      (tensorInducedTrivialF2DiscreteIso G U hU s).hom).hom.hom
        (smoothTensorInducedTrivialF2Tprod G U hU s x)) = _
  rw [toSmoothDiscrete_map_hom_hom_apply]
  let AU := DiscreteRep.trivialF2 U
  let AG := DiscreteRep.trivialF2 G
  let _ : Module ℤ AU.V := AU.module
  let _ : Module ℤ AG.V := AG.module
  let cU := (trivialF2Equiv U).toIntLinearEquiv
    (modM := AU.module) (modM₂ := AddCommGroup.toIntModule (ZMod 2))
  let cG := (trivialF2Equiv G).toIntLinearEquiv
    (modM := AG.module) (modM₂ := AddCommGroup.toIntModule (ZMod 2))
  change trivialF2Equiv G
    (cG.symm (PiTensorProduct.zmodEquiv 2
      (PiTensorProduct.congr (fun _ ↦ cU) (PiTensorProduct.tprod ℤ x)))) = _
  simp only [PiTensorProduct.congr_tprod, PiTensorProduct.zmodEquiv_tprod]
  change trivialF2Equiv G
    ((trivialF2Equiv G).symm (∏ i, trivialF2Equiv U (x i))) = _
  exact (trivialF2Equiv G).apply_symm_apply _

end TrivialF2

end TauCeti
