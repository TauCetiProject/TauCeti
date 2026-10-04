/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Passport.BranchPoints
public import TauCeti.Combinatorics.PermutationTriple.Passport.Enumeration
public import TauCeti.Combinatorics.PermutationTriple.Passport.GeneratingCount
public import TauCeti.Combinatorics.PermutationTriple.Examples
-- Kernel computation of cycle partitions needs the unexposed cycle-factor implementation.
import all Mathlib.GroupTheory.Perm.Cycle.Factors

/-!
# Examples of passports and their enumeration

The degree-one cyclic passport has a singleton branch-point orbit. The torus passport changes
under an exchange of branch points, witnessing that passing to the orbit is strictly coarser
than equality of ordered passports. The computed passport fibers in degrees one to three
have size one; the degree-three check uses the nonabelian symmetric monodromy group. For that
passport, the generating count, centralizer order and normalizer order evaluate the normalizer
formula as `1 = 6 * 1 / 6`.
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

/-- For the degree-three symmetric passport, the normalizer formula reads
`1 = 6 * 1 / 6`: there are six generating triples of the prescribed cycle types, the
centralizer of the monodromy group is trivial, and its normalizer is the full symmetric group. -/
theorem passportSize_formula_s3Triple :
    let P := ConnectedTriple.passportOf ⟨s3Triple, isConnected_s3Triple⟩
    P.G.genCountType P.lam0 P.lam1 P.laminf = 6 ∧
      Nat.card (Subgroup.centralizer (P.G : Set (Perm (Fin 3)))) = 1 ∧
      Nat.card (Subgroup.normalizer (P.G : Set (Perm (Fin 3)))) = 6 ∧
      P.passportSize = 6 * 1 / 6 := by
  let t : ConnectedTriple 3 := ⟨s3Triple, isConnected_s3Triple⟩
  let P := t.passportOf
  have hPG : P.G = t.1.monodromyGroup := by simp [P]
  have hG : P.G = ⊤ := by simp [P, t]
  have htrans : MulAction.IsPretransitive P.G (Fin 3) := by
    rw [hPG]
    exact t.2.isPretransitive
  -- The monodromy group is all of `S₃`; its centralizer is the already-computed automorphism
  -- group of the triple, while its normalizer is all of `S₃` again.
  have hcentralizer :
      Nat.card (Subgroup.centralizer (P.G : Set (Perm (Fin 3)))) = 1 := by
    rw [hG, ← monodromyGroup_s3Triple,
      ← PermutationTriple.automorphismGroup_eq_centralizer_monodromyGroup,
      automorphismGroup_s3Triple, Subgroup.card_bot]
  have hnormalizer :
      Nat.card (Subgroup.normalizer (P.G : Set (Perm (Fin 3)))) = 6 := by
    have hnormal : P.G.Normal := hG.symm ▸ (inferInstance : (⊤ : Subgroup (Perm (Fin 3))).Normal)
    rw [@Subgroup.normalizer_eq_top _ _ P.G hnormal, Subgroup.card_top, Nat.card_perm, Nat.card_fin]
    norm_num
  have hpassport : P.passportSize = 1 := by
    simpa only [P, t] using passportSize_passportOf_s3Triple
  -- Compute the raw passport fiber independently of the normalizer formula.
  let F := passportTriples (Finset.univ : Finset (Perm (Fin 3))) P.lam0 P.lam1 P.laminf
  have hF : F.card = 6 := by
    simp only [F, P, ConnectedTriple.passportOf_lam0, ConnectedTriple.passportOf_lam1,
      ConnectedTriple.passportOf_laminf, t, cycleData_s3Triple]
    decide +kernel
  have hP : ∃ ρ, ((Finset.univ : Finset (Perm (Fin 3))) : Set (Perm (Fin 3))) =
      (P.conjugate ρ).G := by
    refine ⟨1, ?_⟩
    simp [hG, PassportSpec.conjugate_G]
  have hmem (s : ConnectedTriple 3) : s ∈ F ↔ P.IsGeneratingTriple s.1 := by
    rw [mem_passportTriples_iff_hasPassport P _ hP]
    constructor
    · intro hs
      apply PassportSpec.isGeneratingTriple_iff_monodromyGroup_eq_and_hasPassport.mpr
      refine ⟨?_, hs⟩
      obtain ⟨⟨τ, hτ⟩, -⟩ := (PassportSpec.hasPassport_iff s P).mp hs
      apply Subgroup.map_injective (f := (MulAut.conj τ).toMonoidHom)
        (MulAut.conj τ).injective
      rw [hτ, hG, Subgroup.map_top_of_surjective _ (MulAut.conj τ).surjective]
    · exact fun hs =>
        (PassportSpec.isGeneratingTriple_iff_monodromyGroup_eq_and_hasPassport.mp hs).2
  -- Since the reference group is `S₃`, passport membership already means equality with the
  -- reference monodromy group, giving a bijection with the generating triples used in Layer 3.4.
  let e : P.GeneratingTriple ≃ {s : ConnectedTriple 3 // s ∈ F} :=
    { toFun := fun g => ⟨g.toConnectedTriple (by decide) htrans,
        (hmem _).mpr (by
          simpa only [PassportSpec.GeneratingTriple.coe_toConnectedTriple] using g.2)⟩
      invFun := fun s => ⟨s.1.1, (hmem s.1).mp s.2⟩
      left_inv := fun g => by
        apply Subtype.ext
        simp only [PassportSpec.GeneratingTriple.coe_toConnectedTriple]
      right_inv := fun s => by
        apply Subtype.ext
        apply Subtype.ext
        simp only [PassportSpec.GeneratingTriple.coe_toConnectedTriple] }
  have hgeneratingTriple : Nat.card P.GeneratingTriple = 6 := by
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, hF]
  have hgen : P.G.genCountType P.lam0 P.lam1 P.laminf = 6 := by
    rw [← P.card_generatingTriples_eq_genCountType, ← P.card_generatingTriples]
    exact hgeneratingTriple
  have hformula : P.passportSize = 6 * 1 / 6 := by
    rw [P.passportSize_eq_genCountType_mul_card_centralizer_div_card_normalizer
      (by decide) htrans, hgen, hcentralizer, hnormalizer]
  simpa only [P, t] using ⟨hgen, hcentralizer, hnormalizer, hformula⟩

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
