/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.CycleData
public import TauCeti.Algebra.Group.Subgroup.Map
public import TauCeti.GroupTheory.Perm.PermCongr

/-!
# Passports of permutation triples

A passport records the coarse invariants of a connected permutation triple: the conjugacy class
of its monodromy subgroup in the ambient symmetric group and the ordered full cycle partitions at
the three branch points.  This file introduces connected triples as a carrier, their relabeling
classes, passport specifications, and the membership relation between the two.

The cycle partitions include fixed points.  Admissibility therefore says that each partition has
positive parts summing to the degree.  The degree is also required to be nonzero: transitivity on
`Fin 0` is vacuous, but there is no connected degree-zero triple.

## Main definitions

* `TauCeti.ConnectedTriple`: a permutation triple together with connectedness.
* `TauCeti.ConnectedIsoClass`: connected triples modulo simultaneous relabeling.
* `TauCeti.PassportSpec`: a reference monodromy subgroup and three ordered cycle partitions.
* `TauCeti.PassportSpec.IsAdmissible`: well-formed passport data.
* `TauCeti.PassportSpec.HasPassport`: membership of a connected triple in a passport.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.5.
-/

open Equiv MulAction

public section

namespace TauCeti

/-! ## Connected triples and their isomorphism classes -/

/-- A connected permutation triple of degree `n`.

Connectedness is part of the carrier because passports are invariants of connected covers. -/
abbrev ConnectedTriple (n : ℕ) : Type :=
  {t : PermutationTriple n // t.IsConnected}

namespace ConnectedTriple

variable {n : ℕ}

/-- Relabeling a connected triple simultaneously conjugates its three permutations. -/
instance : MulAction (Perm (Fin n)) (ConnectedTriple n) where
  smul τ t := ⟨τ • t.1, (PermutationTriple.isConnected_smul_iff τ t.1).2 t.2⟩
  one_smul t := Subtype.ext (one_smul _ t.1)
  mul_smul τ υ t := Subtype.ext (mul_smul τ υ t.1)

noncomputable instance : Fintype (ConnectedTriple n) := Fintype.ofFinite _

instance : DecidableEq (ConnectedTriple n) := inferInstance

@[simp]
theorem coe_smul (τ : Perm (Fin n)) (t : ConnectedTriple n) :
    ((τ • t : ConnectedTriple n) : PermutationTriple n) = τ • (t : PermutationTriple n) :=
  (rfl)

end ConnectedTriple

/-- Isomorphism classes of connected permutation triples of degree `n`. -/
def ConnectedIsoClass (n : ℕ) : Type :=
  MulAction.orbitRel.Quotient (Perm (Fin n)) (ConnectedTriple n)

namespace ConnectedIsoClass

variable {n : ℕ}

/-- The isomorphism class of a connected triple. -/
def mk (t : ConnectedTriple n) : ConnectedIsoClass n :=
  Quotient.mk'' t

end ConnectedIsoClass

/-! ## Passport specifications -/

/-- A passport specification in degree `n`: a reference monodromy subgroup and the ordered full
cycle partitions at `0`, `1`, and `∞`.

The subgroup is compared only up to conjugacy in `Perm (Fin n)` by `HasPassport`. -/
@[ext]
structure PassportSpec (n : ℕ) where
  /-- A reference representative for the conjugacy class of the monodromy subgroup. -/
  G : Subgroup (Perm (Fin n))
  /-- The full cycle partition at `0`. -/
  lam0 : Multiset ℕ
  /-- The full cycle partition at `1`. -/
  lam1 : Multiset ℕ
  /-- The full cycle partition at `∞`. -/
  laminf : Multiset ℕ

namespace PassportSpec

variable {n : ℕ}

/-- A passport is admissible when its degree is nonzero, its reference subgroup is transitive,
and its three multisets are partitions of the degree into positive parts. -/
def IsAdmissible (P : PassportSpec n) : Prop :=
  n ≠ 0 ∧
    IsPretransitive P.G (Fin n) ∧
    (P.lam0.sum = n ∧ ∀ i ∈ P.lam0, 0 < i) ∧
    (P.lam1.sum = n ∧ ∀ i ∈ P.lam1, 0 < i) ∧
    (P.laminf.sum = n ∧ ∀ i ∈ P.laminf, 0 < i)

theorem IsAdmissible.ne_zero {P : PassportSpec n} (hP : P.IsAdmissible) : n ≠ 0 := hP.1

theorem IsAdmissible.isPretransitive {P : PassportSpec n} (hP : P.IsAdmissible) :
    IsPretransitive P.G (Fin n) := hP.2.1

theorem IsAdmissible.sum_lam0 {P : PassportSpec n} (hP : P.IsAdmissible) :
    P.lam0.sum = n := hP.2.2.1.1

theorem IsAdmissible.sum_lam1 {P : PassportSpec n} (hP : P.IsAdmissible) :
    P.lam1.sum = n := hP.2.2.2.1.1

theorem IsAdmissible.sum_laminf {P : PassportSpec n} (hP : P.IsAdmissible) :
    P.laminf.sum = n := hP.2.2.2.2.1

theorem IsAdmissible.pos_of_mem_lam0 {P : PassportSpec n} (hP : P.IsAdmissible)
    {i : ℕ} (hi : i ∈ P.lam0) : 0 < i := hP.2.2.1.2 i hi

theorem IsAdmissible.pos_of_mem_lam1 {P : PassportSpec n} (hP : P.IsAdmissible)
    {i : ℕ} (hi : i ∈ P.lam1) : 0 < i := hP.2.2.2.1.2 i hi

theorem IsAdmissible.pos_of_mem_laminf {P : PassportSpec n} (hP : P.IsAdmissible)
    {i : ℕ} (hi : i ∈ P.laminf) : 0 < i := hP.2.2.2.2.2 i hi

/-- A connected triple has passport `P` when its monodromy subgroup is conjugate to `P.G` and
its ordered full cycle partitions are those specified by `P`. -/
def HasPassport (t : ConnectedTriple n) (P : PassportSpec n) : Prop :=
  (∃ τ : Perm (Fin n),
      (t.1.monodromyGroup).map (MulAut.conj τ).toMonoidHom = P.G) ∧
    t.1.cycleData.1 = P.lam0 ∧
    t.1.cycleData.2.1 = P.lam1 ∧
    t.1.cycleData.2.2 = P.laminf

/-- Relabeling a connected triple does not change its passport membership. -/
@[simp]
theorem hasPassport_smul_iff (τ : Perm (Fin n)) (t : ConnectedTriple n)
    (P : PassportSpec n) : HasPassport (τ • t) P ↔ HasPassport t P := by
  constructor
  · rintro ⟨⟨ρ, hρ⟩, h0, h1, hinf⟩
    refine ⟨⟨ρ * τ, ?_⟩, ?_, ?_, ?_⟩
    · rw [ConnectedTriple.coe_smul, PermutationTriple.monodromyGroup_smul,
        Subgroup.map_conj_map_conj] at hρ
      exact hρ
    · simpa using h0
    · simpa using h1
    · simpa using hinf
  · rintro ⟨⟨ρ, hρ⟩, h0, h1, hinf⟩
    refine ⟨⟨ρ * τ⁻¹, ?_⟩, ?_, ?_, ?_⟩
    · rw [ConnectedTriple.coe_smul, PermutationTriple.monodromyGroup_smul,
        Subgroup.map_conj_map_conj]
      simpa [mul_assoc] using hρ
    · simpa using h0
    · simpa using h1
    · simpa using hinf

/-- Isomorphic connected triples have exactly the same passport memberships. -/
theorem hasPassport_iff_of_equivalent {t t' : ConnectedTriple n}
    (h : MulAction.orbitRel (Perm (Fin n)) (ConnectedTriple n) t t') (P : PassportSpec n) :
    HasPassport t P ↔ HasPassport t' P := by
  obtain ⟨τ, rfl⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
  exact hasPassport_smul_iff τ t' P

/-- Replace the reference subgroup of a passport by a conjugate representative. -/
def conjugate (P : PassportSpec n) (τ : Perm (Fin n)) : PassportSpec n where
  G := P.G.map (MulAut.conj τ).toMonoidHom
  lam0 := P.lam0
  lam1 := P.lam1
  laminf := P.laminf

@[simp] theorem conjugate_G (P : PassportSpec n) (τ : Perm (Fin n)) :
    (P.conjugate τ).G = P.G.map (MulAut.conj τ).toMonoidHom := (rfl)

@[simp] theorem conjugate_lam0 (P : PassportSpec n) (τ : Perm (Fin n)) :
    (P.conjugate τ).lam0 = P.lam0 := (rfl)

@[simp] theorem conjugate_lam1 (P : PassportSpec n) (τ : Perm (Fin n)) :
    (P.conjugate τ).lam1 = P.lam1 := (rfl)

@[simp] theorem conjugate_laminf (P : PassportSpec n) (τ : Perm (Fin n)) :
    (P.conjugate τ).laminf = P.laminf := (rfl)

/-- Conjugating the reference subgroup preserves admissibility. -/
@[simp]
theorem isAdmissible_conjugate_iff (P : PassportSpec n) (τ : Perm (Fin n)) :
    (P.conjugate τ).IsAdmissible ↔ P.IsAdmissible := by
  constructor
  · rintro ⟨hn, hG, h0, h1, hinf⟩
    refine ⟨hn, ?_, h0, h1, hinf⟩
    rw [conjugate_G, Equiv.conj_eq_permCongrHom,
      Equiv.isPretransitive_map_permCongrHom_iff] at hG
    exact hG
  · rintro ⟨hn, hG, h0, h1, hinf⟩
    refine ⟨hn, ?_, h0, h1, hinf⟩
    rw [conjugate_G, Equiv.conj_eq_permCongrHom,
      Equiv.isPretransitive_map_permCongrHom_iff]
    exact hG

/-- Passport membership depends on the reference subgroup only through its conjugacy class. -/
@[simp]
theorem hasPassport_conjugate_iff (t : ConnectedTriple n) (P : PassportSpec n)
    (τ : Perm (Fin n)) : HasPassport t (P.conjugate τ) ↔ HasPassport t P := by
  constructor
  · rintro ⟨⟨ρ, hρ⟩, h0, h1, hinf⟩
    refine ⟨⟨τ⁻¹ * ρ, ?_⟩, h0, h1, hinf⟩
    refine Subgroup.map_injective (f := (MulAut.conj τ).toMonoidHom)
      (MulAut.conj τ).injective ?_
    rw [Subgroup.map_conj_map_conj]
    simpa [mul_assoc] using hρ
  · rintro ⟨⟨ρ, hρ⟩, h0, h1, hinf⟩
    refine ⟨⟨τ * ρ, ?_⟩, h0, h1, hinf⟩
    calc
      t.1.monodromyGroup.map (MulAut.conj (τ * ρ)).toMonoidHom =
          (t.1.monodromyGroup.map (MulAut.conj ρ).toMonoidHom).map
            (MulAut.conj τ).toMonoidHom := by
        rw [Subgroup.map_conj_map_conj]
      _ = P.G.map (MulAut.conj τ).toMonoidHom := congrArg _ hρ
      _ = (P.conjugate τ).G := rfl

/-- Any passport containing a connected triple is admissible. -/
theorem isAdmissible_of_hasPassport {t : ConnectedTriple n} {P : PassportSpec n}
    (htP : HasPassport t P) : P.IsAdmissible := by
  rcases htP with ⟨⟨τ, hG⟩, h0, h1, hinf⟩
  refine ⟨t.2.ne_zero, ?_, ?_, ?_, ?_⟩
  · rw [← hG, Equiv.conj_eq_permCongrHom, Equiv.isPretransitive_map_permCongrHom_iff]
    exact t.2.isPretransitive
  · refine ⟨?_, fun _ hi ↦ ?_⟩
    · rw [← h0]
      simpa using congrArg (fun data ↦ data.1) t.1.sum_cycleData
    · rw [← h0, PermutationTriple.cycleData_σ0] at hi
      exact t.1.σ0.partition.parts_pos hi
  · refine ⟨?_, fun _ hi ↦ ?_⟩
    · rw [← h1]
      simpa using congrArg (fun data ↦ data.2.1) t.1.sum_cycleData
    · rw [← h1, PermutationTriple.cycleData_σ1] at hi
      exact t.1.σ1.partition.parts_pos hi
  · refine ⟨?_, fun _ hi ↦ ?_⟩
    · rw [← hinf]
      simpa using congrArg (fun data ↦ data.2.2) t.1.sum_cycleData
    · rw [← hinf, PermutationTriple.cycleData_σinf] at hi
      exact t.1.σinf.partition.parts_pos hi

end PassportSpec

end TauCeti
