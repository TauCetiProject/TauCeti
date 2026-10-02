/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule
public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.Levi
import TauCeti.Algebra.Coalgebra.Subcomodule.Coordinate

/-!
# The two minuscule subcomodules of the doubled E₆ carrier

The standard representation of the doubled minuscule carrier is the corestriction of the
standard `O(GL₅₄)`-comodule along its quotient coordinate morphism. It is faithful over every
commutative ring. Its two coordinate blocks `V(ϖ₁)` and `V(ϖ₆)` are complementary subcomodules:
the carrier preserves them scheme-theoretically, so this decomposition persists after arbitrary
base change.

The parameter `dual = false` selects the first block, and `dual = true` the contragredient block.
Membership means vanishing outside the selected block. These subcomodules are the constituents
whose simplicity over fields can be used to establish complete reducibility of the carrier's
standard representation.

The carrier has not been identified with the pinned simply connected group scheme of type `E₆`.
Transfer of these representations to that pinned group requires such an identification.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and II.1–2.
* R. W. Carter, *Simple Groups of Lie Type*, §12.2.
* The corestriction interface follows `TauCeti.Algebra.Lie.E6.Minuscule.StandardComodule`;
  the coordinate subcomodules follow `TauCeti.Algebra.Lie.D4.Tripled.StandardComodule`.
-/

public section

open Module

namespace TauCeti.E6DoubledMinuscule

universe u

variable (R : Type u) [CommRing R]

/-- The standard right comodule of the specialized doubled type-`E₆` minuscule carrier. -/
@[instance_reducible]
noncomputable def standardComodule :
    Comodule R (coordinateHopfAlgebra R) (Fin 54 → R) :=
  GeneralLinear.corestrictStandardComodule R 54 (coordinateMap R).hom

attribute [local instance] GeneralLinear.standardComodule standardComodule

/-- The standard representation of the doubled minuscule carrier is faithful over every
commutative ring. -/
theorem isFaithful_standardComodule :
    Comodule.IsFaithful (k := R) (H := coordinateHopfAlgebra R) (V := Fin 54 → R) :=
  GeneralLinear.isFaithful_corestrictStandardComodule R 54
    (coordinateMap R).hom (coordinateMap_surjective R)

/-- The minuscule (`dual = false`) or contragredient minuscule (`dual = true`) block as a
subcomodule of the standard carrier comodule. -/
noncomputable def summandSubcomodule (dual : Bool) :
    Subcomodule R (coordinateHopfAlgebra R) (Fin 54 → R) :=
  (Pi.basisFun R (Fin 54)).coordinateSpanSubcomodule
    {a | matrixSummand a = if dual then 1 else 0} <|
    ((Pi.basisFun R (Fin 54)).coordinateSpanIsStable_iff
      (C := coordinateHopfAlgebra R) _).2 <| by
    intro a ha b hb
    have hab : matrixSummand a ≠ matrixSummand b := fun h ↦ ha (h.trans hb)
    rw [Comodule.coefficientMatrix_corestrict, Matrix.map_apply,
      GeneralLinear.coefficientMatrix_basisFun, BialgHom.toCoalgHom_apply,
      GeneralLinear.genericMatrix_apply]
    exact coordinateMap_X_eq_zero R hab

/-- Each summand subcomodule is the span of the corresponding coordinate basis vectors. -/
@[simp]
theorem summandSubcomodule_toSubmodule (dual : Bool) :
    (summandSubcomodule R dual).toSubmodule =
      Submodule.span R ((Pi.basisFun R (Fin 54)) ''
        {a | matrixSummand a = if dual then 1 else 0}) :=
  Module.Basis.coordinateSpanSubcomodule_toSubmodule _ _ _

/-- Membership in a minuscule summand means vanishing outside its coordinate block. -/
@[simp]
theorem mem_summandSubcomodule (dual : Bool) (v : Fin 54 → R) :
    v ∈ summandSubcomodule R dual ↔
      ∀ a, matrixSummand a ≠ (if dual then 1 else 0) → v a = 0 := by
  classical
  rw [← Subcomodule.mem_toSubmodule, summandSubcomodule_toSubmodule,
    (Pi.basisFun R (Fin 54)).mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Pi.basisFun_repr,
    Set.mem_ofPred_eq]
  exact forall_congr' fun a ↦ not_imp_comm

/-- The two minuscule summands are complementary over every commutative ring. -/
theorem isCompl_summandSubcomodule :
    IsCompl (summandSubcomodule R false).toSubmodule
      (summandSubcomodule R true).toSubmodule := by
  classical
  have hset : {a : Fin 54 | matrixSummand a = 1} = {a | matrixSummand a = 0}ᶜ := by
    ext a
    obtain ⟨b, rfl⟩ := matrixIndexEquiv.surjective a
    cases b <;> simp
  rw [summandSubcomodule_toSubmodule, summandSubcomodule_toSubmodule]
  simp only [Bool.false_eq_true, ↓reduceIte, hset]
  exact (Pi.basisFun R (Fin 54)).linearIndependent.isCompl_span_image
    (Pi.basisFun R (Fin 54)).span_eq isCompl_compl

end TauCeti.E6DoubledMinuscule
