/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Pi
public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Base
public import TauCeti.LinearAlgebra.RootSystem.DynkinType

/-!
# Base change preserves the Cartan type

Tensor-product base change along an injective flat ring map preserves and reflects the Cartan type
of a base (`TauCeti.hasCartanType_baseChange_iff`), without requiring standard coordinate lattices.

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
* `TauCeti.hasCartanType_baseChange_iff`: tensor-product base change preserves and reflects the
  Cartan type.
-/

public section

namespace TauCeti

section TensorProduct

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} [P.IsCrystallographic]
  (S : Type*) [CommRing S] [Algebra R S] [FaithfulSMul R S] [Module.Flat R S]
  [Module.Free R N] [Module.Finite R N] (b : P.Base) (t : DynkinType)

/-- Extension of a base along an injective flat ring map preserves and reflects its Cartan type. -/
@[simp]
theorem hasCartanType_baseChange_iff :
    HasCartanType (P.baseChange S) (b.baseChange S) t ↔ HasCartanType P b t := by
  rw [hasCartanType_iff, hasCartanType_iff]
  constructor
  · rintro ⟨e, he⟩
    refine ⟨(b.supportBaseChangeEquiv S).symm.trans e, fun i j ↦ ?_⟩
    simpa using he ((b.supportBaseChangeEquiv S).symm i) ((b.supportBaseChangeEquiv S).symm j)
  · rintro ⟨e, he⟩
    refine ⟨(b.supportBaseChangeEquiv S).trans e, fun i j ↦ ?_⟩
    simpa using he (b.supportBaseChangeEquiv S i) (b.supportBaseChangeEquiv S j)

end TensorProduct

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

end TauCeti
