/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.SimpleBasis
public import TauCeti.RepresentationTheory.Symmetric.Modular.Three.Irreducible

/-!
# The simple-class basis for S₃ in characteristic three

The exact Grothendieck group of the group algebra of S₃ over a field of characteristic three
has a basis consisting of the trivial and sign classes, indexed by `false` and `true`.
Thus these classes are independent over ℤ, and every finite-dimensional representation is
determined in the Grothendieck group by its two composition multiplicities. The basis is the
specialization of `TauCeti.simpleClassBasis` to the classification of simple S₃ modules.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part III, §14.
-/

public section

namespace TauCeti

open scoped MonoidAlgebra

universe u

variable (k : Type u) [Field k] [CharP k 3]

local instance : IsArtinianRing k[Equiv.Perm (Fin 3)] :=
  IsArtinianRing.of_finite k k[Equiv.Perm (Fin 3)]

private theorem trivial_sign_not_equiv :
    IsEmpty ((Representation.ofLinearCharacter (1 : Equiv.Perm (Fin 3) →* kˣ)).asModule
      ≃ₗ[k[Equiv.Perm (Fin 3)]]
        (Representation.ofLinearCharacter (signLinearCharacter k (Fin 3))).asModule) := by
  refine ⟨fun e ↦ ?_⟩
  have h := Representation.char_iso (Representation.equivOfAsModuleLinearEquiv e)
  have hswap := congrFun h (Equiv.swap (0 : Fin 3) 1)
  have hne : (1 : k) ≠ -1 := by
    intro h
    have htwo : (2 : k) = 0 := by linear_combination h
    have hdvd := (CharP.cast_eq_zero_iff k 3 2).mp htwo
    norm_num at hdvd
  apply hne
  simpa only [Representation.char_ofLinearCharacter, MonoidHom.one_apply, Units.val_one,
    signLinearCharacter_swap (show (0 : Fin 3) ≠ 1 by decide), Units.val_neg] using hswap

/-- The trivial and sign classes form a basis of the exact Grothendieck group of S₃ over
any field of characteristic three. The index `false` denotes the trivial class and `true`
the sign class. Coordinates are the corresponding Jordan–Hölder multiplicities. -/
noncomputable def symmetricThreeCharThreeSimpleClassBasis :
    Module.Basis Bool ℤ (ExactK0 (finiteModulesExactStructure k[Equiv.Perm (Fin 3)])) := by
  let S (b : Bool) := FGModuleCat.of k[Equiv.Perm (Fin 3)]
    (Representation.ofLinearCharacter (if b then signLinearCharacter k (Fin 3) else 1)).asModule
  have hS (b : Bool) : IsSimpleModule k[Equiv.Perm (Fin 3)] (S b) := by
    dsimp only [S]
    infer_instance
  have hnoniso : Pairwise fun b c ↦ IsEmpty ((S b : Type u) ≃ₗ[k[Equiv.Perm (Fin 3)]] S c) := by
    intro b c hbc
    cases b <;> cases c
    · exact (hbc rfl).elim
    · exact trivial_sign_not_equiv k
    · exact ⟨fun e ↦ (trivial_sign_not_equiv k).false e.symm⟩
    · exact (hbc rfl).elim
  have hexhaustive : IsExhaustiveSimpleFamily S := by
    apply isExhaustiveSimpleFamily_of_forall_isIrreducible
    intro V _ _ ρ hρ
    rcases hρ.nonempty_equiv_trivial_or_sign_perm_fin_three with h | h
    · obtain ⟨e⟩ := h
      rw [← Representation.ofLinearCharacter_one] at e
      have he := Representation.asModuleLinearEquivOfEquiv e
      exact ⟨false, ⟨he⟩⟩
    · obtain ⟨e⟩ := h
      have he := Representation.asModuleLinearEquivOfEquiv e
      exact ⟨true, ⟨he⟩⟩
  exact simpleClassBasis S hnoniso hexhaustive

/-- Each basis vector is the class of its one-dimensional representation. -/
@[simp]
theorem symmetricThreeCharThreeSimpleClassBasis_apply (b : Bool) :
    symmetricThreeCharThreeSimpleClassBasis k b =
      ExactK0.of (FGModuleCat.of k[Equiv.Perm (Fin 3)]
        (Representation.ofLinearCharacter
          (if b then signLinearCharacter k (Fin 3) else 1)).asModule) := by
  apply simpleClassBasis_apply

/-- The coordinates in the trivial–sign basis are the corresponding composition
multiplicities, extended additively to virtual classes. -/
@[simp]
theorem symmetricThreeCharThreeSimpleClassBasis_repr_apply
    (x : ExactK0 (finiteModulesExactStructure k[Equiv.Perm (Fin 3)])) (b : Bool) :
    (symmetricThreeCharThreeSimpleClassBasis k).repr x b =
      jordanHolderCoordinate k[Equiv.Perm (Fin 3)]
        (Representation.ofLinearCharacter
          (if b then signLinearCharacter k (Fin 3) else 1)).asModule x := by
  apply simpleClassBasis_repr_apply

end TauCeti
