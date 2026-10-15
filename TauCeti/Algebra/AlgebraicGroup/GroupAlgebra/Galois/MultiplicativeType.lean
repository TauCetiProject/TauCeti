/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Connected
public import TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.Galois.Torus
public import TauCeti.Algebra.MonoidAlgebra.Etale
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Etale.Descent
import TauCeti.Algebra.AlgebraicGroup.Connected.BaseChange

/-!
# Multiplicative-type groups from Galois descent

The group algebra descended from a finitely generated character group with finite Galois
action is of multiplicative type, including when the character group has torsion. For a finite
character group, its descended coordinate algebra has dimension equal to the group order.
It is étale exactly when that order is invertible in the base field, and in prime
characteristic `p` it is geometrically connected exactly when the character group is a `p`-group.

These properties do not depend on the Galois action. They follow by transporting the split
group-algebra criteria through the splitting equivalence and descending along the field
extension. No perfectness hypothesis is needed on the base field.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.GaloisDescent

universe u

variable {k L M : Type u} [Field k] [Field L] [Algebra k L] [AddCommGroup M]
variable [FiniteDimensional k L] [IsGalois k L]
variable (ρ : Representation ℤ (L ≃ₐ[k] L) M)

/-- Descent of a finitely generated Galois character group produces a group of
multiplicative type; torsion freeness is not required. -/
theorem multiplicativeTypeCommHopfAlgProperty_descendedCoordinateRing [Module.Finite ℤ M] :
    multiplicativeTypeCommHopfAlgProperty k (descendedCoordinateRing ρ) := by
  let _ : Algebra L (AlgebraicClosure k) :=
    (IsAlgClosed.lift (R := k) (S := L) (M := AlgebraicClosure k)).toAlgebra
  let _ : IsScalarTower k L (AlgebraicClosure k) :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      (IsAlgClosed.lift (R := k) (S := L) (M := AlgebraicClosure k)).commutes x |>.symm
  rw [multiplicativeTypeCommHopfAlgProperty_iff_exists_iso_coordinateRing]
  refine ⟨exponentGroup (M := M), ⟨?_⟩⟩
  exact ((DiagonalizableGroup.baseChangeCoordinateRingIso L (AlgebraicClosure k)
    (exponentGroup (M := M))).symm ≪≫
      (FiniteTypeCommHopfAlgCat.baseChangeFunctor (K := AlgebraicClosure k)).mapIso
        (descendedBaseChangeIso ρ).symm) ≪≫
    ObjectProperty.isoMk _
      (CommHopfAlgCat.baseChangeTowerIso k (AlgebraicClosure k) (descendedCoordinateRing ρ).obj)

variable [Finite M]

/-- A finite character group descends to a finite group scheme. -/
instance instModuleFiniteGroupAlgebraInvariants : Module.Finite k (groupAlgebraInvariants ρ) := by
  let _ : Module.Finite k (MonoidAlgebra L (Multiplicative M)) :=
    Module.Finite.trans L (MonoidAlgebra L (Multiplicative M))
  exact Module.Finite.of_injective (groupAlgebraInvariants ρ).val.toLinearMap Subtype.val_injective

/-- The order of the descended finite group scheme is the order of its character group. -/
theorem finrank_groupAlgebraInvariants :
    Module.finrank k (groupAlgebraInvariants ρ) = Nat.card M := by
  let _ := Fintype.ofFinite (Multiplicative M)
  calc
    Module.finrank k (groupAlgebraInvariants ρ) =
        Module.finrank L (L ⊗[k] groupAlgebraInvariants ρ) := Module.finrank_baseChange.symm
    _ = Module.finrank L (MonoidAlgebra L (Multiplicative M)) :=
      (groupAlgebraInvariantsBaseChangeBialgEquiv ρ).toAlgEquiv.toLinearEquiv.finrank_eq
    _ = Nat.card M := by
      rw [Module.finrank_eq_card_basis (MonoidAlgebra.basis (Multiplicative M) L),
        ← Nat.card_eq_fintype_card]
      exact Nat.card_congr Multiplicative.toAdd

/-- A finite descended group is étale exactly when its character-group order is invertible
in the base field. This criterion permits arbitrary Galois action on the character group. -/
theorem etale_groupAlgebraInvariants_iff_isUnit_card :
    Algebra.Etale k (groupAlgebraInvariants ρ) ↔ IsUnit (Nat.card M : k) := by
  have hcard : Nat.card (Multiplicative M) = Nat.card M := Nat.card_congr Multiplicative.toAdd
  constructor
  · intro h
    let _ := h
    have hsplit : Algebra.Etale L (MonoidAlgebra L (Multiplicative M)) :=
      Algebra.Etale.of_equiv (groupAlgebraInvariantsBaseChangeBialgEquiv ρ).toAlgEquiv
    have hunit := (MonoidAlgebra.etale_iff_isUnit_card (Multiplicative M) L).mp hsplit
    rwa [hcard, ← map_natCast (algebraMap k L), isUnit_map_iff] at hunit
  · intro h
    have hunit : IsUnit (Nat.card (Multiplicative M) : L) := by
      simpa only [hcard, map_natCast] using h.map (algebraMap k L)
    let _ := MonoidAlgebra.etale_of_isUnit_card L (Multiplicative M) hunit
    let _ : Algebra.Etale L (L ⊗[k] groupAlgebraInvariants ρ) :=
      Algebra.Etale.of_equiv (groupAlgebraInvariantsBaseChangeBialgEquiv ρ).symm.toAlgEquiv
    exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat L

/-- In prime characteristic, a finite descended group is geometrically connected exactly
when its character group is primary for that prime. -/
theorem geometricallyConnected_groupAlgebraInvariants_iff_isPGroup
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.of k (groupAlgebraInvariants ρ)) ↔ IsPGroup p (Multiplicative M) := by
  let _ : CharP L p := charP_of_injective_algebraMap (algebraMap k L).injective p
  rw [← geometricallyConnectedCommHopfAlgProperty.baseChange_iff k L]
  exact ((geometricallyConnectedCommHopfAlgProperty L).prop_iff_of_iso
    (CommHopfAlgCat.isoMk (groupAlgebraInvariantsBaseChangeBialgEquiv ρ))).trans
      (DiagonalizableGroup.geometricallyConnected_iff_isPGroup L p (Multiplicative M))

end TauCeti.GaloisDescent
