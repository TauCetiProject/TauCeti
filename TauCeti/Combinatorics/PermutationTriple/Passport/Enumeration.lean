/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Passport.Class

/-!
# Executable passport fibers

A passport compares monodromy subgroups up to conjugacy in the symmetric group. A subgroup
itself has no decidable equality, so executable enumeration takes its elements as a finset.
`TauCeti.passportTriples` filters connected triples by that finset, up to conjugacy, and by
three ordered cycle partitions. `TauCeti.passportClasses` lists the resulting relabeling
orbits as finsets of connected triples, without choosing representatives.

Whenever the input finset presents a conjugate of the reference subgroup of a
`TauCeti.PassportSpec`, these computations give exactly its triples and classes. In particular,
`TauCeti.card_passportClasses` identifies the computed cardinality with
`TauCeti.PassportSpec.passportSize`.

The input need not be certified as a subgroup to run the computation. If it is not the element
set of a subgroup, the fiber is empty: no conjugate of a monodromy group can equal it.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.5.
-/

public section

namespace TauCeti

open Equiv

variable {n : ℕ}

/-- The connected triples with the specified ordered full cycle partitions and monodromy group
conjugate to the supplied finset of permutations. Fixed points occur as parts equal to one. -/
@[expose] def passportTriples (G : Finset (Perm (Fin n)))
    (lam0 lam1 laminf : Multiset ℕ) : Finset (ConnectedTriple n) :=
  Finset.univ.filter fun t =>
    (∃ τ : Perm (Fin n), t.1.monodromyFinset.image (MulAut.conj τ) = G) ∧
      t.1.σ0.partition.parts = lam0 ∧ t.1.σ1.partition.parts = lam1 ∧
        t.1.σinf.partition.parts = laminf

/-- Membership in the computed triple fiber is conjugacy of the monodromy finset together with
agreement of the ordered full cycle partitions. -/
@[simp] theorem mem_passportTriples {G : Finset (Perm (Fin n))}
    {lam0 lam1 laminf : Multiset ℕ} {t : ConnectedTriple n} :
    t ∈ passportTriples G lam0 lam1 laminf ↔
      (∃ τ : Perm (Fin n), t.1.monodromyFinset.image (MulAut.conj τ) = G) ∧
        t.1.σ0.partition.parts = lam0 ∧ t.1.σ1.partition.parts = lam1 ∧
          t.1.σinf.partition.parts = laminf := by
  simp [passportTriples]

/-- A finset presentation of any conjugate of the reference subgroup turns the computed
membership test into passport membership. -/
theorem mem_passportTriples_iff_hasPassport (P : PassportSpec n)
    (G : Finset (Perm (Fin n)))
    (hG : ∃ ρ, (G : Set (Perm (Fin n))) = (P.conjugate ρ).G)
    (t : ConnectedTriple n) :
    t ∈ passportTriples G P.lam0 P.lam1 P.laminf ↔ PassportSpec.HasPassport t P := by
  obtain ⟨ρ, hG⟩ := hG
  rw [← PassportSpec.hasPassport_conjugate_iff t P ρ,
    mem_passportTriples, PassportSpec.hasPassport_iff]
  simp only [PermutationTriple.cycleData_σ0, PermutationTriple.cycleData_σ1,
    PermutationTriple.cycleData_σinf, PassportSpec.conjugate_lam0,
    PassportSpec.conjugate_lam1, PassportSpec.conjugate_laminf]
  refine and_congr ?_ Iff.rfl
  apply exists_congr
  intro τ
  rw [← Finset.coe_inj, Finset.coe_image, PermutationTriple.coe_monodromyFinset, hG]
  simpa only [Subgroup.coe_map, MulEquiv.coe_toMonoidHom] using
    (SetLike.coe_injective.eq_iff (a := t.1.monodromyGroup.map (MulAut.conj τ).toMonoidHom)
      (b := (P.conjugate ρ).G))

open scoped Classical in
/-- The computed triple fiber is exactly the filter by the canonical passport predicate. -/
theorem passportTriples_eq_filter (P : PassportSpec n) (G : Finset (Perm (Fin n)))
    (hG : ∃ ρ, (G : Set (Perm (Fin n))) = (P.conjugate ρ).G) :
    passportTriples G P.lam0 P.lam1 P.laminf =
      Finset.univ.filter (fun t : ConnectedTriple n => PassportSpec.HasPassport t P) := by
  ext t
  simp [mem_passportTriples_iff_hasPassport P G hG]

/-- The passport classes specified by a monodromy finset and three ordered full cycle partitions,
as a finset of relabeling orbits. Each orbit is listed once, with all its connected triples. -/
@[expose] def passportClasses (G : Finset (Perm (Fin n)))
    (lam0 lam1 laminf : Multiset ℕ) : Finset (Finset (ConnectedTriple n)) :=
  (passportTriples G lam0 lam1 laminf).image fun t => (ConnectedIsoClass.mk t).orbitFinset

/-- The members of the computed class fiber are the relabeling orbits of triples in the
computed triple fiber. -/
@[simp] theorem mem_passportClasses {G : Finset (Perm (Fin n))}
    {lam0 lam1 laminf : Multiset ℕ} {s : Finset (ConnectedTriple n)} :
    s ∈ passportClasses G lam0 lam1 laminf ↔
      ∃ t ∈ passportTriples G lam0 lam1 laminf, (ConnectedIsoClass.mk t).orbitFinset = s := by
  simp [passportClasses]

/-- Every triple in the computed passport fiber lies in exactly one of its listed relabeling
orbits, for arbitrary input finsets and ordered cycle partitions. -/
theorem existsUnique_mem_passportClasses {G : Finset (Perm (Fin n))}
    {lam0 lam1 laminf : Multiset ℕ} (t : ConnectedTriple n)
    (ht : t ∈ passportTriples G lam0 lam1 laminf) :
    ∃! s, s ∈ passportClasses G lam0 lam1 laminf ∧ t ∈ s := by
  refine ⟨(ConnectedIsoClass.mk t).orbitFinset,
    ⟨mem_passportClasses.mpr ⟨t, ht, rfl⟩, ConnectedIsoClass.mem_orbitFinset.mpr rfl⟩,
    fun s ⟨hs, hts⟩ => ?_⟩
  obtain ⟨t', _, rfl⟩ := mem_passportClasses.mp hs
  rw [ConnectedIsoClass.mem_orbitFinset.mp hts]

/-- The computed class fiber consists exactly of the orbit finsets of the canonical passport
class set. This equality supplies both soundness and completeness of the enumeration. -/
theorem passportClasses_eq_image_classSet (P : PassportSpec n)
    (G : Finset (Perm (Fin n)))
    (hG : ∃ ρ, (G : Set (Perm (Fin n))) = (P.conjugate ρ).G) :
    passportClasses G P.lam0 P.lam1 P.laminf =
      P.classSet.image ConnectedIsoClass.orbitFinset := by
  classical
  ext s
  simp only [mem_passportClasses, Finset.mem_image, PassportSpec.mem_classSet]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨ConnectedIsoClass.mk t,
      (ConnectedIsoClass.hasPassport_mk t P).mpr
        ((mem_passportTriples_iff_hasPassport P G hG t).mp ht), rfl⟩
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨t, rfl⟩ := ConnectedIsoClass.mk_surjective c
    exact ⟨t, (mem_passportTriples_iff_hasPassport P G hG t).mpr
      ((ConnectedIsoClass.hasPassport_mk t P).mp hc), rfl⟩

/-- A relabeling orbit belongs to the computed fiber exactly when its class has the passport. -/
theorem orbitFinset_mem_passportClasses_iff (P : PassportSpec n)
    (G : Finset (Perm (Fin n)))
    (hG : ∃ ρ, (G : Set (Perm (Fin n))) = (P.conjugate ρ).G)
    (c : ConnectedIsoClass n) :
    c.orbitFinset ∈ passportClasses G P.lam0 P.lam1 P.laminf ↔ c.HasPassport P := by
  classical
  rw [passportClasses_eq_image_classSet P G hG]
  simp [ConnectedIsoClass.orbitFinset_injective.eq_iff]

/-- The union of the listed passport classes is exactly the computed triple fiber, for arbitrary
input finsets and ordered cycle partitions. -/
theorem biUnion_passportClasses (G : Finset (Perm (Fin n)))
    (lam0 lam1 laminf : Multiset ℕ) :
    (passportClasses G lam0 lam1 laminf).biUnion id =
      passportTriples G lam0 lam1 laminf := by
  classical
  have horbit (t' : ConnectedTriple n) (ht' : t' ∈ passportTriples G lam0 lam1 laminf) :
      (ConnectedIsoClass.mk t').orbitFinset =
        (passportTriples G lam0 lam1 laminf).filter
          (fun t => ConnectedIsoClass.mk t = ConnectedIsoClass.mk t') := by
    -- A member certifies the input finset as a conjugate subgroup, so the existing passport
    -- invariance applies without assuming that arbitrary inputs present a subgroup.
    obtain ⟨τ, hτ⟩ := (mem_passportTriples.mp ht').1
    let P : PassportSpec n :=
      ⟨t'.1.monodromyGroup.map (MulAut.conj τ).toMonoidHom, lam0, lam1, laminf⟩
    have hG : (G : Set (Perm (Fin n))) = P.G := by
      dsimp [P]
      rw [← hτ, Finset.coe_image, PermutationTriple.coe_monodromyFinset]
    have hG : ∃ ρ, (G : Set (Perm (Fin n))) = (P.conjugate ρ).G :=
      ⟨1, by simpa using hG⟩
    have hc := (ConnectedIsoClass.hasPassport_mk t' P).mpr
      ((mem_passportTriples_iff_hasPassport P G hG t').mp ht')
    ext t
    simp only [ConnectedIsoClass.mem_orbitFinset, Finset.mem_filter]
    constructor
    · intro ht
      rw [← ht] at hc
      exact ⟨(mem_passportTriples_iff_hasPassport P G hG t).mpr
        ((ConnectedIsoClass.hasPassport_mk t P).mp hc), ht⟩
    · exact fun ht => ht.2
  rw [passportClasses, Finset.image_biUnion]
  calc
    _ = (passportTriples G lam0 lam1 laminf).biUnion
        (fun t' => (passportTriples G lam0 lam1 laminf).filter
          (fun t => ConnectedIsoClass.mk t = ConnectedIsoClass.mk t')) :=
      Finset.biUnion_congr rfl horbit
    _ = passportTriples G lam0 lam1 laminf := by
      simpa only [Finset.image_biUnion] using
        Finset.image_biUnion_filter_eq (passportTriples G lam0 lam1 laminf)
          ConnectedIsoClass.mk

/-- The computed class fiber has cardinality equal to the passport size. -/
theorem card_passportClasses (P : PassportSpec n) (G : Finset (Perm (Fin n)))
    (hG : ∃ ρ, (G : Set (Perm (Fin n))) = (P.conjugate ρ).G) :
    (passportClasses G P.lam0 P.lam1 P.laminf).card = P.passportSize := by
  rw [passportClasses_eq_image_classSet P G hG,
    Finset.card_image_of_injective _ ConnectedIsoClass.orbitFinset_injective,
    PassportSpec.passportSize_def]

end TauCeti
