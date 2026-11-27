/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Pi
public import TauCeti.LinearAlgebra.RootSystem.DynkinType

/-!
# Base change preserves the Cartan type

The entrywise base change `TauCeti.rootPairingBaseChange` of a crystallographic dot-product root
pairing along an injective algebra map into a characteristic-zero domain keeps the support of a
base and every Cartan integer (`TauCeti.cartanMatrix_rootPairingBaseChangeBase`). So it keeps the
Cartan type of the base as well. This is how a Cartan type established on an integral pinned root
datum passes to its rational model, and on to any characteristic-zero domain.

The statement lives apart from `TauCeti.LinearAlgebra.RootSystem.BaseChange.Pi` so that the base
change construction does not depend on the enumeration of Dynkin types.

## Main results

* `TauCeti.HasCartanType.rootPairingBaseChange`: **base change preserves the Cartan type of a
  base.**
-/

public section

namespace TauCeti

section CommRing

variable {ι κ R : Type*} (S : Type*) [Fintype κ] [CommRing R] [CommRing S] [Algebra R S]
  [FaithfulSMul R S] [IsDomain S] [CharZero S]
  {P : RootPairing ι R (κ → R) (κ → R)} (hP : ∀ x y, P.toLinearMap x y = x ⬝ᵥ y)
  [P.IsCrystallographic] {b : P.Base} {t : DynkinType}

/-- **Base change preserves the Cartan type of a base.** The base change of a base has the same
support and the same Cartan integers (`TauCeti.cartanMatrix_rootPairingBaseChangeBase`), so the
relabelling exhibiting the type of `b` still works. -/
theorem HasCartanType.rootPairingBaseChange (h : HasCartanType P b t) :
    HasCartanType (rootPairingBaseChange S P hP) (rootPairingBaseChangeBase S P hP b) t := by
  obtain ⟨e, he⟩ := (hasCartanType_iff _ _).1 h
  refine (hasCartanType_iff _ _).2 ⟨(supportEquivRootPairingBaseChangeBase S P hP b).trans e,
    fun i j ↦ ?_⟩
  exact (cartanMatrix_rootPairingBaseChangeBase S P hP b i j).trans (he _ _)

end CommRing

section Field

variable {ι κ R : Type*} (S : Type*) [Fintype κ] [CommRing R] [Field S] [Algebra R S]
  [FaithfulSMul R S] {P : RootPairing ι R (κ → R) (κ → R)}
  (hP : ∀ x y, P.toLinearMap x y = x ⬝ᵥ y) [P.IsCrystallographic] {b : P.Base} {t : DynkinType}

/-- Base change of a dot-product root datum into a field is a root system when its base has
Cartan type `t` of rank `Fintype.card κ` and its coroots span the cocharacter lattice. -/
theorem HasCartanType.isRootSystem_rootPairingBaseChange (h : HasCartanType P b t)
    (hrank : t.rank = Fintype.card κ) (hcor : Submodule.span R (Set.range P.coroot) = ⊤) :
    (TauCeti.rootPairingBaseChange S P hP).IsRootSystem :=
  isRootSystem_rootPairingBaseChange_of_card_support S P hP b (h.card_support.trans hrank) hcor

end Field

end TauCeti
