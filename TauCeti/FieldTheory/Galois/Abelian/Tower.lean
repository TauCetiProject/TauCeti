/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.Abelian.Basic
public import Mathlib.Order.RelSeries
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Order.Atoms.Finite
import Mathlib.Data.SetLike.Fintype
import TauCeti.FieldTheory.IntermediateField.Lift

/-!
# Prime-degree towers in abelian Galois extensions

A finite abelian Galois extension admits a finite tower of intermediate fields from the base to
the whole extension, with every successive extension of prime degree. Every field in the tower
is Galois over the base, so the corresponding fixing subgroups form a normal series with
prime-order quotients. Such towers supply the induction used in the Hasse--Arf theorem.

The tower uses Mathlib's `RelSeries` of covering relations on intermediate fields. The algebra
of each adjacent pair is the algebra induced by its inclusion.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter V, §7.
-/

public section
noncomputable section

namespace IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [Module.Finite K L] [IsAbelianGalois K L]

/-- A covering pair of intermediate fields in a finite abelian Galois extension has prime
relative degree. The algebra and tower instances retain the caller's chosen inclusion map. -/
theorem prime_finrank_of_covBy (E F : IntermediateField K L) (h : E ⋖ F)
    [aEF : Algebra E F] [IsScalarTower K E F] [IsScalarTower E F L] :
    (Module.finrank E F).Prime := by
  have : Module.Finite E F := Module.Finite.of_restrictScalars_finite K E F
  have : IsAbelianGalois E F := .tower_bot E F L
  -- A tower-compatible algebra between these subfields is their inclusion algebra. Identifying
  -- it explicitly lets the interval correspondences retain the caller's algebra instance.
  have hinst : aEF = (IntermediateField.inclusion h.le).toAlgebra := by
    apply Algebra.algebra_ext
    intro x
    apply (algebraMap F L).injective
    rw [← IsScalarTower.algebraMap_apply E F L]
    rfl
  subst aEF
  let : Algebra E F := (IntermediateField.inclusion h.le).toAlgebra
  have ha : IsAtom (IntermediateField.extendScalars h.le) :=
    ((IntermediateField.extendScalars.orderIso E).isAtom_iff ⟨F, h.le⟩).2
      ((covBy_iff_atom_Ici h.le).1 h)
  have : IsSimpleOrder (Set.Iic (IntermediateField.extendScalars h.le)) :=
    Set.isSimpleOrder_Iic_iff_isAtom.2 ha
  -- `extendScalars` retains the field carrier, with precisely the inclusion algebra above.
  have : IsSimpleOrder (IntermediateField E F) :=
    (IntermediateField.liftOrderIso (IntermediateField.extendScalars h.le)).isSimpleOrder
  have : IsSimpleOrder (Subgroup (Gal(F/E)))ᵒᵈ :=
    (IsGalois.intermediateFieldEquivSubgroup (F := E) (E := F)).symm.isSimpleOrder
  have : IsSimpleOrder (Subgroup (Gal(F/E))) :=
    isSimpleOrder_iff_isSimpleOrder_orderDual.2 inferInstance
  have : IsSimpleGroup (Gal(F/E)) := IsSimpleGroup.of_isSimpleOrder
  exact IsGalois.card_aut_eq_finrank E F ▸ Group.is_simple_iff_prime_card.1 inferInstance

end IntermediateField

namespace TauCeti

/-- A finite abelian Galois extension admits a bottom-to-top series of intermediate fields with
prime relative degree at every step. The successive algebras are induced by inclusion. Every
node is abelian Galois over the base, and every step is abelian Galois.
The trivial extension gives a series of length zero. -/
theorem exists_prime_finrank_intermediateField_series
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Module.Finite K L] [IsAbelianGalois K L] :
    ∃ s : RelSeries {(E, F) : IntermediateField K L × IntermediateField K L | E ⋖ F},
      s.head = ⊥ ∧ s.last = ⊤ ∧ ∀ i : Fin s.length,
        let : Algebra (s i.castSucc) (s i.succ) :=
          (IntermediateField.inclusion (s.step i).le).toAlgebra
        (Module.finrank (s i.castSucc) (s i.succ)).Prime ∧
          IsAbelianGalois (s i.castSucc) (s i.succ) := by
  have : Finite (IntermediateField K L) :=
    Finite.of_injective IsGalois.intermediateFieldEquivSubgroup
      IsGalois.intermediateFieldEquivSubgroup.injective
  obtain ⟨s, _, _, hhead, hlast⟩ :=
    LTSeries.exists_relSeries_covBy_and_head_eq_bot_and_last_eq_bot
      (RelSeries.singleton _ (⊥ : IntermediateField K L))
  refine ⟨s, hhead, hlast, fun i ↦ ?_⟩
  let : Algebra (s i.castSucc) (s i.succ) :=
    (IntermediateField.inclusion (s.step i).le).toAlgebra
  have : IsScalarTower K (s i.castSucc) (s i.succ) :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      (IntermediateField.inclusion (s.step i).le).commutes x |>.symm
  have : IsScalarTower (s i.castSucc) (s i.succ) L :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      (IntermediateField.coe_inclusion (s.step i).le x).symm
  exact ⟨IntermediateField.prime_finrank_of_covBy _ _ (s.step i),
    IsAbelianGalois.tower_bot (s i.castSucc) (s i.succ) L⟩

end TauCeti
