/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialF2
import TauCeti.LinearAlgebra.PiTensorProduct.ZMod
public import TauCeti.RepresentationTheory.Tensor.Induction.Smooth

/-!
# Smooth tensor induction of trivial F₂ coefficients

Smooth tensor induction (`TauCeti.smoothTensorInductionFunctor`) of the canonical trivial `𝔽₂`
coefficient object is again the canonical trivial coefficient object of the ambient group.

The isomorphism multiplies the tensor factors. It is the coefficient identification needed before
the cochain-level Evens norm can be read as a class in `TauCeti.cohomF2 G` rather than in the
cohomology of an abstract tensor-induced coefficient object.

## Main definitions

* `TauCeti.smoothTensorInducedTrivialF2Iso`: tensor induction of trivial `𝔽₂` coefficients
  is the canonical trivial `𝔽₂` coefficient object.

## References

* L. Evens, "A generalization of the transfer map in the cohomology of groups",
  *Transactions of the American Mathematical Society* 108 (1963), §§2–5.
-/

public section

open CategoryTheory
open scoped TensorProduct

universe v

namespace TauCeti

variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : Subgroup G) (hU : IsOpen (U : Set G)) (s : U.LeftTransversal)
  [U.FiniteIndex]

/-- The finite quotient indexing the tensor factors of tensor induction. -/
noncomputable local instance quotientFintype : Fintype (G ⧸ U) :=
  U.fintypeQuotientOfFiniteIndex

/-- The pure tensor in the smooth tensor induction of trivial `𝔽₂` coefficients. -/
noncomputable def smoothTensorInducedTrivialF2Tprod
    (x : G ⧸ U → (DiscreteRep.trivialF2 U).V) :
    (DiscreteRep.tensorInduced U hU s
      (DiscreteRep.trivialF2 U)).V := by
  let A := DiscreteRep.trivialF2 U
  letI : Module ℤ A.V := A.module
  exact cast (DiscreteRep.tensorInduced_V U hU s A).symm
    (PiTensorProduct.tprod ℤ x)

/-- The coefficient calculation on the tensor power: read every tensor factor in `ZMod 2` and
multiply the factors. The factors carry the `ℤ`-module structure of the `DiscreteRep`, which is the
one the tensor induction is formed with. -/
private noncomputable def tensorInducedTrivialF2LinearEquiv :=
  @PiTensorProduct.congr (G ⧸ U) ℤ _ (fun _ ↦ (DiscreteRep.trivialF2 U).V) _
      (fun _ ↦ (DiscreteRep.trivialF2 U).module) (fun _ ↦ ZMod 2) _
      (fun _ ↦ AddCommGroup.toIntModule (ZMod 2))
      (fun _ ↦ (trivialF2Equiv U).toIntLinearEquiv
        (modM := (DiscreteRep.trivialF2 U).module)
        (modM₂ := AddCommGroup.toIntModule (ZMod 2))) ≪≫ₗ
    PiTensorProduct.zmodEquiv 2

private theorem tensorInducedTrivialF2LinearEquiv_tprod
    (x : G ⧸ U → (DiscreteRep.trivialF2 U).V) :
    tensorInducedTrivialF2LinearEquiv G U (smoothTensorInducedTrivialF2Tprod G U hU s x) =
      ∏ i, trivialF2Equiv U (x i) := by
  let _ : Module ℤ (DiscreteRep.trivialF2 U).V := (DiscreteRep.trivialF2 U).module
  -- `smoothTensorInducedTrivialF2Tprod` is a cast along the definitional equality
  -- `DiscreteRep.tensorInduced_V`.
  change tensorInducedTrivialF2LinearEquiv G U (PiTensorProduct.tprod ℤ x) = _
  simp only [tensorInducedTrivialF2LinearEquiv, LinearEquiv.trans_apply,
    PiTensorProduct.congr_tprod, PiTensorProduct.zmodEquiv_tprod]
  rfl

private theorem tensorInducedTrivialF2LinearEquiv_ρ (g : G)
    (z : (DiscreteRep.tensorInduced U hU s (DiscreteRep.trivialF2 U)).V) :
    tensorInducedTrivialF2LinearEquiv G U
        ((DiscreteRep.tensorInduced U hU s (DiscreteRep.trivialF2 U)).ρ g z) =
      tensorInducedTrivialF2LinearEquiv G U z := by
  let _ : Module ℤ (DiscreteRep.trivialF2 U).V := (DiscreteRep.trivialF2 U).module
  rw [show (DiscreteRep.tensorInduced U hU s (DiscreteRep.trivialF2 U)).ρ g z =
      U.tensorInducedRepresentation s (DiscreteRep.trivialF2 U).ρ g z from
    DiscreteRep.tensorInduced_ρ_apply U hU s _ g z]
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smul, LinearEquiv.map_smul, LinearEquiv.map_smul,
      Subgroup.tensorInducedRepresentation_apply_tprod]
    congr 1
    simp only [show ∀ (u : U) y, (DiscreteRep.trivialF2 U).ρ u y = y from
      trivialF2_ρ_apply_apply U]
    exact (tensorInducedTrivialF2LinearEquiv_tprod G U hU s _).trans
      ((Equiv.prod_comp (MulAction.toPerm g⁻¹) fun i ↦ trivialF2Equiv U (x i)).trans
        (tensorInducedTrivialF2LinearEquiv_tprod G U hU s x).symm)
  | add z z' hz hz' => rw [map_add, LinearEquiv.map_add, hz, hz', LinearEquiv.map_add]

/-- The carrier map of the coefficient identification, landing in the carrier of
`trivialF2 G`. -/
private noncomputable def tensorInducedTrivialF2AddEquiv :
    (DiscreteRep.tensorInduced U hU s (DiscreteRep.trivialF2 U)).V ≃+
      (DiscreteRep.trivialF2 G).V :=
  (tensorInducedTrivialF2LinearEquiv G U).toAddEquiv.trans (trivialF2Equiv G).symm

private theorem tensorInducedTrivialF2AddEquiv_ρ (g : G)
    (z : (DiscreteRep.tensorInduced U hU s (DiscreteRep.trivialF2 U)).V) :
    tensorInducedTrivialF2AddEquiv G U hU s
        ((DiscreteRep.tensorInduced U hU s (DiscreteRep.trivialF2 U)).ρ g z) =
      (DiscreteRep.trivialF2 G).ρ g (tensorInducedTrivialF2AddEquiv G U hU s z) := by
  rw [show ∀ y, (DiscreteRep.trivialF2 G).ρ g y = y from trivialF2_ρ_apply_apply G g]
  exact congrArg (trivialF2Equiv G).symm (tensorInducedTrivialF2LinearEquiv_ρ G U hU s g z)

private noncomputable def tensorInducedTrivialF2DiscreteIso :
    DiscreteRep.tensorInduced U hU s (DiscreteRep.trivialF2 U) ≅ DiscreteRep.trivialF2 G := by
  let TI := DiscreteRep.tensorInduced U hU s (DiscreteRep.trivialF2 U)
  let AG := DiscreteRep.trivialF2 G
  -- Instance search would pick `AddCommGroup.toIntModule`, which is not the module structure
  -- that `AG.ρ` is linear for.
  letI : Module ℤ AG.V := AG.module
  let fe := (tensorInducedTrivialF2AddEquiv G U hU s).toIntLinearEquiv
    (modM := TI.module) (modM₂ := AG.module)
  have hfe : ∀ g z, fe (TI.ρ g z) = AG.ρ g (fe z) := tensorInducedTrivialF2AddEquiv_ρ G U hU s
  exact
    { hom := fe.toLinearMap.intertwiningMap_of_isIntertwiningMap TI.ρ AG.ρ hfe
      inv := fe.symm.toLinearMap.intertwiningMap_of_isIntertwiningMap AG.ρ TI.ρ fun g x ↦
        fe.injective (by simp only [LinearEquiv.coe_coe, hfe, LinearEquiv.apply_symm_apply])
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

/-- On a pure tensor, the smooth trivial-`𝔽₂` tensor-induction isomorphism multiplies
the underlying `ZMod 2` values. -/
theorem smoothTensorInducedTrivialF2Iso_hom_apply_tprod
    (x : G ⧸ U → (DiscreteRep.trivialF2 U).V) :
    trivialF2Equiv G ((smoothTensorInducedTrivialF2Iso G U hU s).hom.hom.hom
        (smoothTensorInducedTrivialF2Tprod G U hU s x)) =
      ∏ i, trivialF2Equiv U (x i) := by
  rw [smoothTensorInducedTrivialF2Iso, Functor.mapIso_hom]
  exact ((trivialF2Equiv G).apply_symm_apply _).trans
    (tensorInducedTrivialF2LinearEquiv_tprod G U hU s x)

end TauCeti
