/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.SimpleBasis
public import TauCeti.RepresentationTheory.Symmetric.Modular.Three.CharTwo

/-!
# The simple-class basis for S₃ in characteristic two

The exact Grothendieck group of the group algebra of S₃ over any field of characteristic two
has the trivial and standard classes as an integral basis, indexed by `false` and `true`.
These independent coordinates are the composition multiplicities used to compute images of
induction. The basis specializes `TauCeti.simpleClassBasis` to the exhaustive classification
of irreducible S₃ representations.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part III, §14.
-/

public section

open scoped MonoidAlgebra

namespace TauCeti

universe u

variable (k : Type u) [Field k] [CharP k 2]

local instance instIsArtinianRingSymmetricThreeCharTwo : IsArtinianRing k[Equiv.Perm (Fin 3)] :=
  IsArtinianRing.of_finite k k[Equiv.Perm (Fin 3)]

omit [CharP k 2] in
private theorem trivial_standard_not_equiv :
    IsEmpty ((Representation.trivial k (Equiv.Perm (Fin 3)) k).asModule
      ≃ₗ[k[Equiv.Perm (Fin 3)]] (standardRepresentation k (Fin 3)).asModule) := by
  refine ⟨fun e ↦ ?_⟩
  have h := (Representation.equivOfAsModuleLinearEquiv e).toLinearEquiv.finrank_eq
  rw [Module.finrank_self, finrank_augmentationSubrepresentation, Fintype.card_fin] at h
  norm_num at h

local instance : Module.Finite k[Equiv.Perm (Fin 3)]
    (standardRepresentation k (Fin 3)).asModule :=
  Module.Finite.of_restrictScalars_finite k k[Equiv.Perm (Fin 3)] _

private noncomputable def simpleFamily (b : Bool) : FGModuleCat k[Equiv.Perm (Fin 3)] :=
  match b with
  | false => FGModuleCat.of k[Equiv.Perm (Fin 3)]
      (Representation.trivial k (Equiv.Perm (Fin 3)) k).asModule
  | true => FGModuleCat.of k[Equiv.Perm (Fin 3)] (standardRepresentation k (Fin 3)).asModule

private instance simpleFamily_isSimpleModule (b : Bool) :
    IsSimpleModule k[Equiv.Perm (Fin 3)] (simpleFamily k b) := by
  cases b
  · exact (_root_.Representation.irreducible_iff_isSimpleModule_asModule
      (Representation.trivial k (Equiv.Perm (Fin 3)) k)).mp inferInstance
  · exact (_root_.Representation.irreducible_iff_isSimpleModule_asModule
      (standardRepresentation k (Fin 3))).mp
        (isIrreducible_standardRepresentation_fin_three
          (CharP.cast_ne_zero_of_ne_of_prime k
            (by decide : Nat.Prime 3) (by decide : 2 ≠ 3)))

/-- The trivial and standard classes form an integral basis of the exact Grothendieck group
of S₃ in characteristic two. The index `false` denotes the trivial class and `true` the
standard class; the coordinates are their Jordan–Hölder multiplicities. -/
noncomputable def symmetricThreeCharTwoSimpleClassBasis :
    Module.Basis Bool ℤ (ExactK0 (finiteModulesExactStructure k[Equiv.Perm (Fin 3)])) := by
  let S := simpleFamily k
  have hnoniso : Pairwise fun b c ↦ IsEmpty ((S b : Type u) ≃ₗ[k[Equiv.Perm (Fin 3)]] S c) := by
    intro b c hbc
    cases b <;> cases c
    · exact (hbc rfl).elim
    · exact trivial_standard_not_equiv k
    · exact ⟨fun e ↦ (trivial_standard_not_equiv k).false e.symm⟩
    · exact (hbc rfl).elim
  have hexhaustive : IsExhaustiveSimpleFamily S := by
    apply isExhaustiveSimpleFamily_of_forall_isIrreducible
    intro V _ _ ρ hρ
    rcases hρ.nonempty_equiv_trivial_or_standard_perm_fin_three with h | h
    · obtain ⟨e⟩ := h
      have he := Representation.asModuleLinearEquivOfEquiv e
      exact ⟨false, ⟨he⟩⟩
    · obtain ⟨e⟩ := h
      have he := Representation.asModuleLinearEquivOfEquiv e
      exact ⟨true, ⟨he⟩⟩
  exact simpleClassBasis S hnoniso hexhaustive

/-- Each basis vector is the class of the corresponding simple representation. -/
@[simp]
theorem symmetricThreeCharTwoSimpleClassBasis_apply (b : Bool) :
    symmetricThreeCharTwoSimpleClassBasis k b = if b then
      ExactK0.of (FGModuleCat.of k[Equiv.Perm (Fin 3)]
        (standardRepresentation k (Fin 3)).asModule)
    else ExactK0.of (FGModuleCat.of k[Equiv.Perm (Fin 3)]
      (Representation.trivial k (Equiv.Perm (Fin 3)) k).asModule) := by
  unfold symmetricThreeCharTwoSimpleClassBasis
  -- Splitting the Boolean index reduces both the `simpleFamily` match and the `if`
  -- in the stated formula, so each branch is exactly `simpleClassBasis_apply`.
  cases b <;> exact simpleClassBasis_apply ..

/-- The two coordinates are the trivial and standard composition multiplicities,
extended additively to virtual classes. -/
@[simp]
theorem symmetricThreeCharTwoSimpleClassBasis_repr_apply
    (x : ExactK0 (finiteModulesExactStructure k[Equiv.Perm (Fin 3)])) (b : Bool) :
    (symmetricThreeCharTwoSimpleClassBasis k).repr x b = if b then
      jordanHolderCoordinate k[Equiv.Perm (Fin 3)] (standardRepresentation k (Fin 3)).asModule x
    else jordanHolderCoordinate k[Equiv.Perm (Fin 3)]
      (Representation.trivial k (Equiv.Perm (Fin 3)) k).asModule x := by
  unfold symmetricThreeCharTwoSimpleClassBasis
  -- Splitting the Boolean index reduces the `simpleFamily` match and the displayed `if`.
  cases b <;> exact simpleClassBasis_repr_apply ..

end TauCeti
