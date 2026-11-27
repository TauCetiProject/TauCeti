/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMType.InfinitePlace
public import TauCeti.NumberTheory.NumberField.Cyclotomic.InfinitePlace

/-!
# Cyclotomic labels of CM type representatives

For a cyclotomic extension of an imaginary quadratic field, choose one base embedding
and a reference extension of it. The representative at a cyclotomic label `a` is the
reference embedding precomposed with the automorphism that raises roots of unity to `a`.
Multiplying the labels corresponds to composing these automorphisms on the right.

The labeling convention follows `New.Parameters.galOfPlace` and `New.Parameters.placeMulEquiv`
in `New/Reduction/Data/FieldsAndPlaces.lean` of lsernau/grh-lean, revision `72fead1`.
-/

public noncomputable section

open NumberField Polynomial IsCyclotomicExtension

namespace TauCeti.CMType

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [Subsingleton (InfinitePlace K)] {n : ℕ} [IsCyclotomicExtension {n} K L]

/-- Label the embeddings of an induced CM type by cyclotomic units, using `φ` as the
reference embedding with label one. -/
def equivUnitsZMod (Φ : CMType K) (φ : Φ.induced (algebraMap K L))
    (h : Irreducible (cyclotomic n K)) : Φ.induced (algebraMap K L) ≃ (ZMod n)ˣ :=
  letI : IsTotallyComplex K := nonempty_iff_isTotallyComplex.mp ⟨Φ⟩
  Φ.induced (algebraMap K L) |>.equivInfinitePlace.trans
    ((InfinitePlace.mk φ.val).equivUnitsZMod
      (IsTotallyComplex.isUnramifiedAtInfinitePlaces (k := K) (K := L) |>.isUnramified _) h)

/-- The labels on the induced CM type are the labels of the underlying infinite places. -/
theorem equivUnitsZMod_apply (Φ : CMType K) (φ ψ : Φ.induced (algebraMap K L))
    (h : Irreducible (cyclotomic n K)) (hφ : (InfinitePlace.mk φ.val).IsUnramified K) :
    Φ.equivUnitsZMod φ h ψ =
      (InfinitePlace.mk φ.val).equivUnitsZMod hφ h (InfinitePlace.mk ψ.val) :=
  (by simp only [equivUnitsZMod, Equiv.trans_apply, equivInfinitePlace_apply])

/-- The reference embedding has label one. -/
@[simp]
theorem equivUnitsZMod_self (Φ : CMType K) (φ : Φ.induced (algebraMap K L))
    (h : Irreducible (cyclotomic n K)) : Φ.equivUnitsZMod φ h φ = 1 := by
  simp [equivUnitsZMod]

variable [NeZero n]

/-- The embedding at label `a` is the reference embedding precomposed with the
cyclotomic automorphism of exponent `a`. -/
@[simp]
theorem coe_equivUnitsZMod_symm_apply (Φ : CMType K) (φ : Φ.induced (algebraMap K L))
    (h : Irreducible (cyclotomic n K)) (a : (ZMod n)ˣ) :
    ((Φ.equivUnitsZMod φ h).symm a).val = φ.val.comp ((autEquivPow L h).symm a) := by
  rw [equivUnitsZMod, Equiv.symm_trans_apply]
  apply (coe_equivInfinitePlace_symm_apply_eq_iff _ _ _).mpr
  refine ⟨mem_induced.mpr ?_, (InfinitePlace.equivUnitsZMod_symm_apply_mk ..).symm⟩
  have hcomp : (((autEquivPow L h).symm a : L ≃ₐ[K] L) : L →+* L).comp (algebraMap K L) =
      algebraMap K L := RingHom.ext ((autEquivPow L h).symm a).commutes
  rw [RingHom.comp_assoc, hcomp]
  exact mem_induced.mp φ.property

/-- Right multiplication of cyclotomic labels corresponds to precomposition of the
representative at the first label by the automorphism attached to the second. -/
theorem coe_equivUnitsZMod_symm_apply_mul (Φ : CMType K) (φ : Φ.induced (algebraMap K L))
    (h : Irreducible (cyclotomic n K)) (a b : (ZMod n)ˣ) :
    ((Φ.equivUnitsZMod φ h).symm (a * b)).val =
      ((Φ.equivUnitsZMod φ h).symm a).val.comp ((autEquivPow L h).symm b) := by
  simp only [coe_equivUnitsZMod_symm_apply, map_mul, AlgEquiv.aut_mul,
    AlgEquiv.toRingHom_trans, RingHom.comp_assoc]

end TauCeti.CMType
