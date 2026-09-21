/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Passport.Class

/-!
# The passport of a connected permutation triple

Every connected permutation triple determines a passport: its monodromy subgroup is the reference
subgroup and its three full cycle partitions are the ordered partition data.  The resulting
passport is admissible and contains the original triple.

The reference subgroup depends on the numbering of the sheets.  Relabeling a triple therefore
conjugates its passport rather than fixing it literally.  The passport membership relation removes
this choice: a connected triple belongs to `passportOf t` exactly when its monodromy subgroup is
conjugate to that of `t` and its ordered cycle data agrees with that of `t`.

## Main declarations

* `TauCeti.ConnectedTriple.passportOf`: the passport determined by a connected triple.
* `TauCeti.ConnectedTriple.isAdmissible_passportOf`: this passport is admissible.
* `TauCeti.ConnectedTriple.hasPassport_passportOf`: the triple belongs to its passport.
* `TauCeti.ConnectedTriple.hasPassport_passportOf_iff`: the characteristic property of the
  passport of a triple.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.5.
-/

open Equiv MulAction

public section

namespace TauCeti

namespace ConnectedTriple

variable {n : ℕ}

/-! ## Construction and projections -/

/-- The passport determined by a connected permutation triple: its monodromy subgroup together
with its ordered full cycle partitions. -/
noncomputable def passportOf (t : ConnectedTriple n) : PassportSpec n where
  G := t.1.monodromyGroup
  lam0 := t.1.cycleData.1
  lam1 := t.1.cycleData.2.1
  laminf := t.1.cycleData.2.2

@[simp]
theorem passportOf_G (t : ConnectedTriple n) : t.passportOf.G = t.1.monodromyGroup :=
  (rfl)

@[simp]
theorem passportOf_lam0 (t : ConnectedTriple n) : t.passportOf.lam0 = t.1.cycleData.1 :=
  (rfl)

@[simp]
theorem passportOf_lam1 (t : ConnectedTriple n) : t.passportOf.lam1 = t.1.cycleData.2.1 :=
  (rfl)

@[simp]
theorem passportOf_laminf (t : ConnectedTriple n) : t.passportOf.laminf = t.1.cycleData.2.2 :=
  (rfl)

/-- Relabeling the sheets conjugates the reference subgroup of the attached passport and leaves
its ordered cycle data unchanged. -/
@[simp]
theorem passportOf_smul (tau : Perm (Fin n)) (t : ConnectedTriple n) :
    (tau • t).passportOf = t.passportOf.conjugate tau := by
  ext
  · simp [PermutationTriple.monodromyGroup_smul]
  · simp
  · simp
  · simp

/-! ## Admissibility and the characteristic property -/

/-- Every connected triple belongs to the passport it determines. -/
@[simp]
theorem hasPassport_passportOf (t : ConnectedTriple n) :
    PassportSpec.HasPassport t t.passportOf := by
  rw [PassportSpec.hasPassport_iff]
  have hconj : (MulAut.conj (1 : Perm (Fin n))).toMonoidHom = MonoidHom.id _ := by
    ext
    simp
  refine ⟨⟨1, ?_⟩, rfl, rfl, rfl⟩
  rw [hconj, Subgroup.map_id]
  exact (passportOf_G t).symm

/-- The passport determined by a connected triple is admissible. -/
@[simp]
theorem isAdmissible_passportOf (t : ConnectedTriple n) : t.passportOf.IsAdmissible :=
  PassportSpec.isAdmissible_of_hasPassport t.hasPassport_passportOf

/-- The admissible ordered passport attached to a connected triple. -/
noncomputable def orderedPassportOf (t : ConnectedTriple n) : OrderedPassport n :=
  ⟨t.passportOf, t.isAdmissible_passportOf⟩

@[simp] theorem coe_orderedPassportOf (t : ConnectedTriple n) :
    t.orderedPassportOf.1 = t.passportOf := (rfl)

/-- The indexed partition of the attached passport is the full partition of the component. -/
@[simp] theorem partition_passportOf (t : ConnectedTriple n) (i : Fin 3) :
    t.passportOf.partition i = (t.1.component i).partition.parts := by
  fin_cases i <;> simp

/-- A connected triple belongs to `passportOf t` exactly when its monodromy subgroup is conjugate
to that of `t` and its ordered full cycle data agrees with that of `t`. -/
theorem hasPassport_passportOf_iff (t t' : ConnectedTriple n) :
    PassportSpec.HasPassport t' t.passportOf ↔
      (∃ tau : Perm (Fin n),
        t'.1.monodromyGroup.map (MulAut.conj tau).toMonoidHom = t.1.monodromyGroup) ∧
        t'.1.cycleData = t.1.cycleData := by
  rw [PassportSpec.hasPassport_iff]
  constructor
  · rintro ⟨hG, h0, h1, hinf⟩
    refine ⟨hG, ?_⟩
    ext <;> simp_all
  · rintro ⟨hG, hdata⟩
    refine ⟨hG, ?_, ?_, ?_⟩
    · exact congrArg (fun data ↦ data.1) hdata
    · exact congrArg (fun data ↦ data.2.1) hdata
    · exact congrArg (fun data ↦ data.2.2) hdata

/-- A connected triple belongs to a passport exactly when that passport is obtained from the
triple's attached passport by conjugating its reference subgroup. -/
theorem hasPassport_iff_exists_conjugate_passportOf (t : ConnectedTriple n)
    (P : PassportSpec n) :
    PassportSpec.HasPassport t P ↔ ∃ tau : Perm (Fin n), t.passportOf.conjugate tau = P := by
  rw [PassportSpec.hasPassport_iff]
  constructor
  · rintro ⟨⟨tau, hG⟩, h0, h1, hinf⟩
    refine ⟨tau, PassportSpec.ext ?_ ?_ ?_ ?_⟩
    · simpa using hG
    · simpa using h0
    · simpa using h1
    · simpa using hinf
  · rintro ⟨tau, rfl⟩
    exact ⟨⟨tau, (PassportSpec.conjugate_G t.passportOf tau).symm⟩,
      (PassportSpec.conjugate_lam0 t.passportOf tau).symm,
      (PassportSpec.conjugate_lam1 t.passportOf tau).symm,
      (PassportSpec.conjugate_laminf t.passportOf tau).symm⟩

/-- The isomorphism class of a connected triple lies in the class set of its attached passport. -/
theorem mk_mem_classSet_passportOf (t : ConnectedTriple n) :
    ConnectedIsoClass.mk t ∈ t.passportOf.classSet := by
  rw [PassportSpec.mem_classSet, ConnectedIsoClass.hasPassport_mk]
  exact t.hasPassport_passportOf

/-- The passport attached to a connected triple has positive size. -/
theorem passportSize_passportOf_pos (t : ConnectedTriple n) : 0 < t.passportOf.passportSize :=
  (PassportSpec.passportSize_pos_iff t.passportOf).2 ⟨t, t.hasPassport_passportOf⟩

/-- Membership in the class set of `passportOf t` has the same characteristic description as
membership of a representative triple. -/
theorem mk_mem_classSet_passportOf_iff (t t' : ConnectedTriple n) :
    ConnectedIsoClass.mk t' ∈ t.passportOf.classSet ↔
      (∃ tau : Perm (Fin n),
        t'.1.monodromyGroup.map (MulAut.conj tau).toMonoidHom = t.1.monodromyGroup) ∧
        t'.1.cycleData = t.1.cycleData := by
  rw [PassportSpec.mem_classSet, ConnectedIsoClass.hasPassport_mk,
    hasPassport_passportOf_iff]

end ConnectedTriple

end TauCeti
