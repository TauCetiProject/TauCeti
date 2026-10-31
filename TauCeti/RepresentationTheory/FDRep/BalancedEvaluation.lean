/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Linear.BalancedEvaluation
public import TauCeti.RepresentationTheory.FDRep.Basic
public import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RepresentationTheory.Rep.Iso

/-!
# Isotypic reconstruction over the full commutant

If the group-algebra module of a finite representation `W` is semisimple and
isotypic of type `S`, evaluation identifies `Hom(S,W) ⊗_{End(S)} S` with `W`.
The coefficient ring is the actual categorical `End S`, acting on morphisms by
precomposition. It need not consist of scalars. In particular the construction
applies to simple representations over nonsplitting fields, with no assumption
on the order of the group.

The left endomorphism action on `S` is the explicit `FDRep.endModule`, obtained
from `Functor.endModule` for the composite forgetful functor to modules. The inverse and its
naturality are
characterized by evaluation, independently of the decomposition chosen in the proof.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985).
* Mathlib's `IsIsotypicOfType.linearEquiv_fun` supplies the finite decomposition.
-/

public section

namespace FDRep

open CategoryTheory TauCeti
open scoped MonoidAlgebra

universe u v

variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]

local notation "R" => forget₂ (FDRep k G) (Rep k G)
local notation "F" => (R) ⋙ (forget₂ (Rep k G) (ModuleCat k))

/-- The full equivariant endomorphism ring acts on the underlying representation.
The action is explicit; install it locally when forming balanced multiplicity tensors. -/
noncomputable abbrev endModule (S : FDRep k G) :
    Module (End S) ((R).obj S) := (F).endModule S

attribute [local instance] endModule

/-- Evaluation over the actual commutant is bijective on a semisimple isotypic
finite representation. No scalar-Schur or splitting-field assumption is required. -/
theorem balancedEvaluation_bijective (S W : FDRep k G)
    [IsSemisimpleModule k[G] (Representation.asModule W.ρ)]
    (h : IsIsotypicOfType k[G] (Representation.asModule W.ρ)
      (Representation.asModule S.ρ)) :
    Function.Bijective ((F).balancedEvaluation S W) := by
  classical
  let H := (forget₂ (FDRep k G) (Rep k G)) ⋙ Rep.toModuleMonoidAlgebra
  have : H.Additive := ⟨by intros; rfl⟩
  let : Module.Finite k[G] (Representation.asModule W.ρ) :=
    Module.Finite.of_restrictScalars_finite k _ _
  obtain ⟨n, ⟨e⟩⟩ := h.linearEquiv_fun
  -- Identify the forgotten actions before lifting the decomposition's maps through the
  -- fully faithful group-algebra functor. Its object carriers are bundled module synonyms.
  let e' : H.obj W ≃ₗ[k[G]] (Fin n → H.obj S) := by
    dsimp only [H, Functor.comp_obj, Rep.toModuleMonoidAlgebra]
    rw [FDRep.forget₂_ρ, FDRep.forget₂_ρ]
    exact e
  let i (j : Fin n) : S ⟶ W := H.preimage (X := S) (Y := W)
    (ConcreteCategory.ofHom (C := ModuleCat k[G])
      (e'.symm.toLinearMap.comp (LinearMap.single k[G] (fun _ : Fin n ↦ H.obj S) j)))
  let p (j : Fin n) : W ⟶ S := H.preimage (X := W) (Y := S)
    (ConcreteCategory.ofHom (C := ModuleCat k[G]) ((LinearMap.proj j).comp e'.toLinearMap))
  have hi (j : Fin n) : (H.map (i j)).hom =
      e'.symm.toLinearMap.comp (LinearMap.single k[G] (fun _ : Fin n ↦ H.obj S) j) :=
    congrArg ModuleCat.Hom.hom (H.map_preimage _)
  have hp (j : Fin n) : (H.map (p j)).hom =
      (LinearMap.proj j).comp e'.toLinearMap :=
    congrArg ModuleCat.Hom.hom (H.map_preimage _)
  have hid : (H.map (𝟙 W)).hom = LinearMap.id :=
    (congrArg ModuleCat.Hom.hom (H.map_id W)).trans (ModuleCat.hom_id)
  apply (F).balancedEvaluation_bijective_of_sum_id i p
  apply H.map_injective
  apply ModuleCat.hom_ext
  simp only [Functor.map_sum, Functor.map_comp, ModuleCat.hom_sum, ModuleCat.hom_comp,
    hi, hp, hid]
  ext x
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.proj_apply, LinearMap.single_apply, LinearMap.id_apply]
  rw [← map_sum, Finset.univ_sum_single, e'.symm_apply_apply]

/-- An isotypic finite representation is recovered from its right-commutant
multiplicity module by balanced evaluation. -/
noncomputable def isotypicBalancedEvaluationEquiv (S W : FDRep k G)
    [IsSemisimpleModule k[G] (Representation.asModule W.ρ)]
    (h : IsIsotypicOfType k[G] (Representation.asModule W.ρ)
      (Representation.asModule S.ρ)) :
    BalancedTensorProduct k (End S) (S ⟶ W) ((R).obj S) ≃ₗ[k] (R).obj W :=
  LinearEquiv.ofBijective ((F).balancedEvaluation S W) (S.balancedEvaluation_bijective W h)

/-- Reconstruction is the canonical evaluation map on arbitrary balanced tensors. -/
theorem isotypicBalancedEvaluationEquiv_apply (S W : FDRep k G)
    [IsSemisimpleModule k[G] (Representation.asModule W.ρ)]
    (h : IsIsotypicOfType k[G] (Representation.asModule W.ρ)
      (Representation.asModule S.ρ))
    (z : BalancedTensorProduct k (End S) (S ⟶ W) ((R).obj S)) :
    S.isotypicBalancedEvaluationEquiv W h z = (F).balancedEvaluation S W z := (rfl)

/-- A multiplicity morphism tensored with a vector evaluates to that morphism's value. -/
@[simp]
theorem isotypicBalancedEvaluationEquiv_tmul (S W : FDRep k G)
    [IsSemisimpleModule k[G] (Representation.asModule W.ρ)]
    (h : IsIsotypicOfType k[G] (Representation.asModule W.ρ)
      (Representation.asModule S.ρ)) (f : S ⟶ W) (x : (R).obj S) :
    S.isotypicBalancedEvaluationEquiv W h (BalancedTensorProduct.tmul k (End S) f x) =
      ((R).map f).hom x := by
  rw [isotypicBalancedEvaluationEquiv_apply]
  exact (F).balancedEvaluation_tmul S W f x

/-- The inverse reconstruction sends a morphism's value back to its pure tensor. -/
@[simp]
theorem isotypicBalancedEvaluationEquiv_symm_apply_map (S W : FDRep k G)
    [IsSemisimpleModule k[G] (Representation.asModule W.ρ)]
    (h : IsIsotypicOfType k[G] (Representation.asModule W.ρ)
      (Representation.asModule S.ρ)) (f : S ⟶ W) (x : (R).obj S) :
    (S.isotypicBalancedEvaluationEquiv W h).symm (((R).map f).hom x) =
      BalancedTensorProduct.tmul k (End S) f x := by
  apply (S.isotypicBalancedEvaluationEquiv W h).injective
  rw [LinearEquiv.apply_symm_apply, isotypicBalancedEvaluationEquiv_tmul]

/-- Inverse reconstruction is natural: an intertwiner acts by postcomposition on
the multiplicity factor and leaves the source vector unchanged. -/
theorem isotypicBalancedEvaluationEquiv_symm_naturality (S W U : FDRep k G)
    [IsSemisimpleModule k[G] (Representation.asModule W.ρ)]
    [IsSemisimpleModule k[G] (Representation.asModule U.ρ)]
    (hW : IsIsotypicOfType k[G] (Representation.asModule W.ρ)
      (Representation.asModule S.ρ))
    (hU : IsIsotypicOfType k[G] (Representation.asModule U.ρ)
      (Representation.asModule S.ρ)) (g : W ⟶ U) (y : (R).obj W) :
    BalancedTensorProduct.map (Linear.rightComp k S g) LinearMap.id
        (by intro a f; simp [End.smul_left]) (fun _ _ ↦ rfl)
        ((S.isotypicBalancedEvaluationEquiv W hW).symm y) =
      (S.isotypicBalancedEvaluationEquiv U hU).symm (((R).map g).hom y) := by
  apply (S.isotypicBalancedEvaluationEquiv U hU).injective
  rw [isotypicBalancedEvaluationEquiv_apply, Functor.balancedEvaluation_naturality,
    ← isotypicBalancedEvaluationEquiv_apply S W hW]
  simp

end FDRep
