/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.SimpleBasis
public import TauCeti.RepresentationTheory.Symmetric.Modular.Three.Stabilizer
import TauCeti.RepresentationTheory.AsModule
import TauCeti.RepresentationTheory.OfModule
import TauCeti.GroupTheory.Perm.FinThree.Basic

/-!
# The simple-class basis of a point stabilizer in S₃

Over a field of characteristic different from two, the trivial and restricted sign classes
form an integral basis of the exact Grothendieck group of each point stabilizer in S₃.
Thus induction from a stabilizer is determined by its values on these two classes.
The coordinates are Jordan–Hölder multiplicities, so the basis applies to exact, rather
than only split, Grothendieck groups.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part III, §14.
-/

public section

namespace TauCeti

open scoped MonoidAlgebra

universe u

variable (k : Type u) [Field k] [NeZero (2 : k)] (a : Fin 3)

local instance : IsArtinianRing k[MulAction.stabilizer (Equiv.Perm (Fin 3)) a] :=
  IsArtinianRing.of_finite k k[MulAction.stabilizer (Equiv.Perm (Fin 3)) a]

/-- The trivial and restricted sign classes form a basis of the exact Grothendieck group
of a point stabilizer in S₃. The indices `false` and `true` denote these classes respectively.
This works over every field in which two is nonzero. -/
noncomputable def symmetricThreeStabilizerSimpleClassBasis :
    Module.Basis Bool ℤ
      (ExactK0 (finiteModulesExactStructure k[MulAction.stabilizer (Equiv.Perm (Fin 3)) a])) := by
  let H := MulAction.stabilizer (Equiv.Perm (Fin 3)) a
  let χ := (signLinearCharacter k (Fin 3)).comp H.subtype
  let S (b : Bool) := FGModuleCat.of k[H]
    (Representation.ofLinearCharacter (if b then χ else 1)).asModule
  have hS (b : Bool) : IsSimpleModule k[H] (S b) := by
    dsimp only [S]
    infer_instance
  have hnoniso : IsEmpty ((S false : Type u) ≃ₗ[k[H]] S true) := by
    refine ⟨fun e ↦ ?_⟩
    have e' : (Representation.ofLinearCharacter (1 : H →* kˣ)).asModule ≃ₗ[k[H]]
        (Representation.ofLinearCharacter χ).asModule := e
    let t : H := ⟨Equiv.swap (a + 1) (a + 2),
      (mem_stabilizer_perm_fin_three_iff a _).mpr (Or.inr rfl)⟩
    have hne : a + 1 ≠ a + 2 := (by decide : ∀ a : Fin 3, a + 1 ≠ a + 2) a
    have hχ : χ t = -1 := signLinearCharacter_swap hne
    have h := congrFun
      (Representation.char_iso (Representation.equivOfAsModuleLinearEquiv e')) t
    have hone : (1 : k) = -1 := by
      simpa only [Representation.char_ofLinearCharacter,
        MonoidHom.one_apply, Units.val_one, hχ, Units.val_neg] using h
    have htwo : (2 : k) = 0 := by linear_combination hone
    exact NeZero.ne (2 : k) htwo
  have hpair : Pairwise fun b c ↦ IsEmpty ((S b : Type u) ≃ₗ[k[H]] S c) := by
    intro b c hbc
    cases b <;> cases c
    · exact (hbc rfl).elim
    · exact hnoniso
    · exact ⟨fun e ↦ hnoniso.false e.symm⟩
    · exact (hbc rfl).elim
  have hexhaustive : IsExhaustiveSimpleFamily S := by
    rw [isExhaustiveSimpleFamily_iff]
    intro M hM
    let := hM
    let := Module.restrictScalars k k[H] M
    let := IsScalarTower.restrictScalars k k[H] M
    let ρ := Representation.ofModule' (k := k) (G := H) M
    have hρ : ρ.IsIrreducible := (Representation.isIrreducible_ofModule'_iff M).mpr hM
    rcases hρ.nonempty_equiv_trivial_or_sign_stabilizer_perm_fin_three with h | h
    · obtain ⟨e⟩ := h
      rw [← Representation.ofLinearCharacter_one] at e
      have he : Nonempty (M ≃ₗ[k[H]]
          (Representation.ofLinearCharacter (1 : H →* kˣ)).asModule) :=
        ⟨(Representation.ofModule'AsModuleEquiv M).symm.trans
          (Representation.asModuleLinearEquivOfEquiv e)⟩
      exact ⟨false, he⟩
    · obtain ⟨e⟩ := h
      have he : Nonempty (M ≃ₗ[k[H]] (Representation.ofLinearCharacter χ).asModule) :=
        ⟨(Representation.ofModule'AsModuleEquiv M).symm.trans
          (Representation.asModuleLinearEquivOfEquiv e)⟩
      exact ⟨true, he⟩
  exact simpleClassBasis S hpair hexhaustive

/-- Each basis vector is the class of its one-dimensional source representation. -/
@[simp]
theorem symmetricThreeStabilizerSimpleClassBasis_apply (b : Bool) :
    symmetricThreeStabilizerSimpleClassBasis k a b =
      ExactK0.of (FGModuleCat.of k[MulAction.stabilizer (Equiv.Perm (Fin 3)) a]
        (Representation.ofLinearCharacter
          (if b then (signLinearCharacter k (Fin 3)).comp
            (MulAction.stabilizer (Equiv.Perm (Fin 3)) a).subtype else 1)).asModule) := by
  apply simpleClassBasis_apply

/-- The basis coordinates are the trivial and restricted-sign composition multiplicities. -/
@[simp]
theorem symmetricThreeStabilizerSimpleClassBasis_repr_apply
    (x : ExactK0 (finiteModulesExactStructure k[MulAction.stabilizer (Equiv.Perm (Fin 3)) a]))
    (b : Bool) :
    (symmetricThreeStabilizerSimpleClassBasis k a).repr x b =
      jordanHolderCoordinate k[MulAction.stabilizer (Equiv.Perm (Fin 3)) a]
        (Representation.ofLinearCharacter
          (if b then (signLinearCharacter k (Fin 3)).comp
            (MulAction.stabilizer (Equiv.Perm (Fin 3)) a).subtype else 1)).asModule x := by
  apply simpleClassBasis_repr_apply

end TauCeti
