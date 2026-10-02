/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Passport.BranchPoints
public import TauCeti.Combinatorics.PermutationTriple.Passport.Enumeration
public import TauCeti.Combinatorics.PermutationTriple.Examples
-- Kernel computation of cycle partitions needs the unexposed cycle-factor implementation.
import all Mathlib.GroupTheory.Perm.Cycle.Factors

/-!
# Examples of passports and their enumeration

The degree-one cyclic passport has a singleton branch-point orbit. The torus passport changes
under an exchange of branch points, witnessing that passing to the orbit is strictly coarser
than equality of ordered passports. The computed passport fibers in degrees one to three
have size one; the degree-three check uses the nonabelian symmetric monodromy group.
-/

open Equiv MulAction

public section

namespace TauCeti

/-- The degree-one passport has one class, computed with its whole symmetric group. -/
theorem card_passportClasses_one :
    (passportClasses (Finset.univ : Finset (Perm (Fin 1))) {1} {1} {1}).card = 1 := by
  decide

/-- The degree-two cyclic passport, ramified over `0` and `∞`, has one class. -/
theorem card_passportClasses_cyclic_two :
    (passportClasses (Finset.univ : Finset (Perm (Fin 2))) {2} {1, 1} {2}).card = 1 := by
  decide

/-- The degree-three passport with symmetric monodromy and ordered partitions
`([3], [2, 1], [2, 1])` has one class. -/
theorem card_passportClasses_symmetric_three :
    (passportClasses (Finset.univ : Finset (Perm (Fin 3))) {3} {2, 1} {2, 1}).card = 1 := by
  decide +kernel

namespace PermutationTriple

/-- The passport of the degree-three symmetric triple has size one. -/
theorem passportSize_passportOf_s3Triple :
    (ConnectedTriple.passportOf ⟨s3Triple, isConnected_s3Triple⟩).passportSize = 1 := by
  let t : ConnectedTriple 3 := ⟨s3Triple, isConnected_s3Triple⟩
  have hG : ((Finset.univ : Finset (Perm (Fin 3))) : Set (Perm (Fin 3))) = t.passportOf.G := by
    simp [ConnectedTriple.passportOf_G, t, monodromyGroup_s3Triple]
  rw [← card_passportClasses t.passportOf Finset.univ
    ⟨1, by simpa using hG⟩]
  simpa only [ConnectedTriple.passportOf_lam0, ConnectedTriple.passportOf_lam1,
    ConnectedTriple.passportOf_laminf, t, cycleData_s3Triple] using
    card_passportClasses_symmetric_three

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
  apply Set.Subsingleton.eq_singleton_of_mem _ (mem_orbit_self _)
  apply subsingleton_orbit_iff_mem_fixedPoints.mpr
  intro ρ
  apply Subtype.ext
  apply PassportSpec.ext_partition
  · simp only [OrderedPassport.coe_smul, PassportSpec.smul_eq_reindexBranchPoints,
      PassportSpec.reindexBranchPoints_G]
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
