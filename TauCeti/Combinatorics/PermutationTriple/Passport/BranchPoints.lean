/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.BranchPoints
public import TauCeti.Combinatorics.PermutationTriple.Passport.OfTriple
public import TauCeti.Combinatorics.PermutationTriple.Examples
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Branch-point action on ordered passports

Permuting the branch points reorders the three cycle partitions and leaves the reference
monodromy subgroup unchanged. Reindexing is contravariant, so this is a right action of
`Perm (Fin 3)`, written as a left action of its opposite group. The action preserves
admissibility and agrees with the branch-point operations on connected triples.

`OrderedPassport` carries an admissible specification, including its reference subgroup.
Its branch-point orbit has at most six elements. It is a coarser invariant than the ordered
partitions: the torus passport changes under an exchange of branch points, while the
passport of the degree-one cyclic triple has a singleton orbit.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.5.
-/

open Equiv MulAction

public section

namespace TauCeti

namespace ConnectedTriple

variable {n : ℕ}

/-- Reorder the branch points of a connected triple. -/
def reindexBranchPoints (t : ConnectedTriple n) (ρ : Perm (Fin 3)) : ConnectedTriple n :=
  ⟨t.1.reindexBranchPoints ρ,
    (PermutationTriple.isConnected_reindexBranchPoints_iff t.1 ρ).2 t.2⟩

@[simp]
theorem coe_reindexBranchPoints (t : ConnectedTriple n) (ρ : Perm (Fin 3)) :
    (t.reindexBranchPoints ρ).1 = t.1.reindexBranchPoints ρ := (rfl)

end ConnectedTriple

namespace PassportSpec

variable {n : ℕ}

/-- Reorder the three partitions of a passport, retaining its reference subgroup. -/
def reindexBranchPoints (P : PassportSpec n) (ρ : Perm (Fin 3)) : PassportSpec n where
  G := P.G
  lam0 := P.partition (ρ 0)
  lam1 := P.partition (ρ 1)
  laminf := P.partition (ρ 2)

@[simp] theorem reindexBranchPoints_G (P : PassportSpec n) (ρ : Perm (Fin 3)) :
    (P.reindexBranchPoints ρ).G = P.G := (rfl)

@[simp] theorem reindexBranchPoints_lam0 (P : PassportSpec n) (ρ : Perm (Fin 3)) :
    (P.reindexBranchPoints ρ).lam0 = P.partition (ρ 0) := (rfl)

@[simp] theorem reindexBranchPoints_lam1 (P : PassportSpec n) (ρ : Perm (Fin 3)) :
    (P.reindexBranchPoints ρ).lam1 = P.partition (ρ 1) := (rfl)

@[simp] theorem reindexBranchPoints_laminf (P : PassportSpec n) (ρ : Perm (Fin 3)) :
    (P.reindexBranchPoints ρ).laminf = P.partition (ρ 2) := (rfl)

@[simp] theorem partition_reindexBranchPoints (P : PassportSpec n) (ρ : Perm (Fin 3))
    (i : Fin 3) : (P.reindexBranchPoints ρ).partition i = P.partition (ρ i) := by
  fin_cases i <;> simp

@[simp] theorem reindexBranchPoints_one (P : PassportSpec n) :
    P.reindexBranchPoints 1 = P := by
  apply ext_partition <;> simp

/-- Reindexing twice composes the permutations in the order of application. -/
theorem reindexBranchPoints_reindexBranchPoints (P : PassportSpec n) (ρ σ : Perm (Fin 3)) :
    (P.reindexBranchPoints ρ).reindexBranchPoints σ = P.reindexBranchPoints (ρ * σ) := by
  apply ext_partition <;> simp

/-- Reordering the branch points commutes with changing the reference subgroup by conjugacy. -/
@[simp] theorem reindexBranchPoints_conjugate (P : PassportSpec n) (ρ : Perm (Fin 3))
    (τ : Perm (Fin n)) :
    (P.conjugate τ).reindexBranchPoints ρ = (P.reindexBranchPoints ρ).conjugate τ := by
  have h (i : Fin 3) : (P.conjugate τ).partition i = P.partition i := by
    fin_cases i <;> simp
  ext <;> simp [reindexBranchPoints, h]

/-- Admissibility is invariant under reordering the branch points. -/
@[simp] theorem isAdmissible_reindexBranchPoints_iff (P : PassportSpec n) (ρ : Perm (Fin 3)) :
    (P.reindexBranchPoints ρ).IsAdmissible ↔ P.IsAdmissible := by
  simp only [isAdmissible_iff_partition, partition_reindexBranchPoints]
  exact and_congr_right fun _ => and_congr_right fun _ => (ρ.surjective.forall (p := fun i =>
    (P.partition i).sum = n ∧ ∀ j ∈ P.partition i, 0 < j)).symm

/-- The right action on passport specifications permutes their ordered partitions. -/
instance : MulAction (Perm (Fin 3))ᵐᵒᵖ (PassportSpec n) where
  smul ρ P := P.reindexBranchPoints ρ.unop
  one_smul := reindexBranchPoints_one
  mul_smul ρ σ P := (reindexBranchPoints_reindexBranchPoints P σ.unop ρ.unop).symm

@[simp] theorem smul_eq_reindexBranchPoints (P : PassportSpec n) (ρ : (Perm (Fin 3))ᵐᵒᵖ) :
    ρ • P = P.reindexBranchPoints ρ.unop := (rfl)

end PassportSpec

namespace OrderedPassport

variable {n : ℕ}

/-- The branch-point action restricts to admissible specifications. -/
instance : MulAction (Perm (Fin 3))ᵐᵒᵖ (OrderedPassport n) where
  smul ρ P := ⟨P.1.reindexBranchPoints ρ.unop,
    (P.1.isAdmissible_reindexBranchPoints_iff ρ.unop).2 P.2⟩
  one_smul P := Subtype.ext P.1.reindexBranchPoints_one
  mul_smul ρ σ P := Subtype.ext
    (P.1.reindexBranchPoints_reindexBranchPoints σ.unop ρ.unop).symm

@[simp] theorem coe_smul (ρ : (Perm (Fin 3))ᵐᵒᵖ) (P : OrderedPassport n) :
    (ρ • P).1 = ρ • P.1 := (rfl)

/-- A branch-point orbit contains at most six ordered passports. -/
theorem card_orbit_le_six (P : OrderedPassport n) :
    Nat.card (orbit (Perm (Fin 3))ᵐᵒᵖ P) ≤ 6 := by
  let := Fintype.ofEquiv (Perm (Fin 3)) MulOpposite.opEquiv
  have hcard := Fintype.card_congr (MulOpposite.opEquiv (α := Perm (Fin 3)))
  have h := Finite.card_range_le (fun ρ : (Perm (Fin 3))ᵐᵒᵖ => ρ • P)
  simpa [orbit, Nat.card_eq_fintype_card, ← hcard, Fintype.card_perm, Nat.factorial] using h

end OrderedPassport

namespace ConnectedTriple

variable {n : ℕ}

/-- Taking a passport commutes with all six branch-point operations. -/
@[simp] theorem passportOf_reindexBranchPoints (t : ConnectedTriple n) (ρ : Perm (Fin 3)) :
    (t.reindexBranchPoints ρ).passportOf = t.passportOf.reindexBranchPoints ρ := by
  apply PassportSpec.ext_partition
  · simp
  · intro i
    simp only [partition_passportOf, coe_reindexBranchPoints,
      PassportSpec.partition_reindexBranchPoints]
    exact congrArg Nat.Partition.parts
      (Equiv.Perm.partition_eq_of_isConj.mp (t.1.isConj_component_reindexBranchPoints ρ i))

/-- The refined ordered passport is equivariant for branch-point reindexing. -/
@[simp] theorem orderedPassportOf_reindexBranchPoints (t : ConnectedTriple n)
    (ρ : Perm (Fin 3)) :
    (t.reindexBranchPoints ρ).orderedPassportOf = MulOpposite.op ρ • t.orderedPassportOf := by
  apply Subtype.ext
  simp

end ConnectedTriple

namespace PassportSpec

variable {n : ℕ}

/-- Reordering a triple and its passport preserves passport membership, in both directions. -/
@[simp] theorem hasPassport_reindexBranchPoints_iff (t : ConnectedTriple n)
    (P : PassportSpec n) (ρ : Perm (Fin 3)) :
    HasPassport (t.reindexBranchPoints ρ) (P.reindexBranchPoints ρ) ↔ HasPassport t P := by
  simp only [ConnectedTriple.hasPassport_iff_exists_conjugate_passportOf,
    ConnectedTriple.passportOf_reindexBranchPoints, ← reindexBranchPoints_conjugate]
  apply exists_congr
  intro τ
  simpa only [smul_eq_reindexBranchPoints, MulOpposite.unop_op] using
    (smul_left_cancel_iff (MulOpposite.op ρ)
      (x := t.passportOf.conjugate τ) (y := P))

end PassportSpec

namespace PermutationTriple

/-- The degree-one cyclic triple has a singleton branch-point orbit of ordered passports. -/
theorem orbit_orderedPassportOf_cyclicTriple_one :
    orbit (Perm (Fin 3))ᵐᵒᵖ
        (ConnectedTriple.orderedPassportOf
          ⟨cyclicTriple 1, isConnected_cyclicTriple_iff.mpr (by decide)⟩) =
      {(ConnectedTriple.orderedPassportOf
          ⟨cyclicTriple 1, isConnected_cyclicTriple_iff.mpr (by decide)⟩)} := by
  let t : ConnectedTriple 1 :=
    ⟨cyclicTriple 1, isConnected_cyclicTriple_iff.mpr (by decide)⟩
  have hp (i : Fin 3) : t.passportOf.partition i = {1} := by
    fin_cases i <;>
      simp only [Fin.reduceFinMk, PassportSpec.partition_zero, PassportSpec.partition_one,
        PassportSpec.partition_two, ConnectedTriple.passportOf_lam0,
        ConnectedTriple.passportOf_lam1, ConnectedTriple.passportOf_laminf,
        t, cycleData_cyclicTriple (by decide : 1 ≠ 0), Multiset.replicate_one]
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨mem_orbit_self _, ?_⟩
  intro Q hQ
  obtain ⟨ρ, rfl⟩ := mem_orbit_iff.mp hQ
  apply Subtype.ext
  apply PassportSpec.ext_partition
  · rfl
  · intro i
    rw [OrderedPassport.coe_smul]
    simp only [ConnectedTriple.coe_orderedPassportOf,
      PassportSpec.smul_eq_reindexBranchPoints, PassportSpec.partition_reindexBranchPoints]
    exact (hp _).trans (hp _).symm

/-- Different ordered passports can have the same branch-point orbit: exchanging `1` and `∞`
changes the torus passport from `([4], [4], [2, 2])` to `([4], [2, 2], [4])`. -/
theorem exists_ne_mem_orbit_orderedPassportOf_torusTriple :
    ∃ Q ∈ orbit (Perm (Fin 3))ᵐᵒᵖ
      (ConnectedTriple.orderedPassportOf ⟨torusTriple, isConnected_torusTriple⟩),
      Q ≠ (ConnectedTriple.orderedPassportOf ⟨torusTriple, isConnected_torusTriple⟩) := by
  let t : ConnectedTriple 4 := ⟨torusTriple, isConnected_torusTriple⟩
  refine ⟨MulOpposite.op (swap (1 : Fin 3) 2) • t.orderedPassportOf, mem_orbit _ _, ?_⟩
  have h1 : t.orderedPassportOf.1.partition 1 = {4} := by
    simp only [ConnectedTriple.coe_orderedPassportOf, PassportSpec.partition_one,
      ConnectedTriple.passportOf_lam1, t, cycleData_torusTriple]
  have hswap :
      (MulOpposite.op (swap (1 : Fin 3) 2) • t.orderedPassportOf).1.partition 1 = {2, 2} := by
    simp only [OrderedPassport.coe_smul, ConnectedTriple.coe_orderedPassportOf,
      PassportSpec.smul_eq_reindexBranchPoints, MulOpposite.unop_op,
      PassportSpec.partition_reindexBranchPoints, swap_apply_left, PassportSpec.partition_two,
      ConnectedTriple.passportOf_laminf, t, cycleData_torusTriple]
  intro h
  have hp := congrArg (fun P : OrderedPassport 4 => P.1.partition 1) h
  have hc : ({2, 2} : Multiset ℕ) = {4} := hswap.symm.trans (hp.trans h1)
  have := congrArg Multiset.card hc
  norm_num at this

end PermutationTriple

end TauCeti
