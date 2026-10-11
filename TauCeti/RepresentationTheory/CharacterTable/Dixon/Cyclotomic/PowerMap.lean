/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Cyclotomic.Reduction
public import TauCeti.RepresentationTheory.CharacterTable.Cyclotomic.PowerMap
public import TauCeti.RingTheory.Cyclotomic.Power
public import TauCeti.Algebra.Group.Conj

/-!
# Power-map alignment of cyclotomic character-table residues

For a certified exact table, a coprime power substitution on an entry is the same as powering its
column representative, provided that representative has `e`-th power one. This holds
for ordinary and central characters because coprime powers preserve class sizes. Hence every
conjugate residue of a row is determined by one modular row, without searching permutations of the
rows across embeddings.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, §12.4.
* J. D. Dixon, *High speed computation of group characters* (1967), 446--450.
-/

public section

namespace TauCeti.ClassData.IsCyclotomicCharacterTableSpec

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
  {d : ClassData G} {e : ℕ} [NeZero e]
  {omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) (Cyclotomic e)}
  {degree : Fin d.numClasses → ℕ}

/-- Coprime substitution on the ordinary entries of a certified table powers its class
representative when its `e`-th power is one. -/
theorem powRingHom_table (h : d.IsCyclotomicCharacterTableSpec e omega table degree)
    {n : ℕ} (hn : e.Coprime n) (i k : Fin d.numClasses) (hg : d.rep k ^ e = 1) :
    Cyclotomic.powRingHom hn (table i k) = table i (d.index (d.rep k ^ n)) := by
  obtain ⟨j, hj⟩ := h.isCharacterTableSpec.exists_eq_characterTable
    (finCongr d.numClasses_eq_card_conjClasses i)
  let ρ := irreducibleRepresentation ℂ (G := G) j
  have hentry (g : G) : Cyclotomic.complexEmbedding (table i (d.index g)) =
      ρ.character g := by
    have hv := hj (d.classOf (d.index g))
    rw [d.complexTableOfCyclotomic_apply_classOf, d.classOf_index, characterTable_apply] at hv
    simpa [ρ] using hv
  apply Cyclotomic.complexEmbedding_injective
  have hx : Cyclotomic.complexEmbedding (table i k) = ρ.character (d.rep k) := by
    simpa using hentry (d.rep k)
  have hpow := ρ.map_cyclotomic_character_eq_character_pow (n := n)
    hg hx
    (Cyclotomic.complexEmbedding.comp (Cyclotomic.powRingHom hn)) (by simp)
  exact hpow.trans (hentry (d.rep k ^ n)).symm

/-- Coprime substitution on the central entries of a certified table powers its class
representative when its `e`-th power is one. -/
theorem powRingHom_omega (h : d.IsCyclotomicCharacterTableSpec e omega table degree)
    {n : ℕ} (hn : e.Coprime n) (i k : Fin d.numClasses) (hg : d.rep k ^ e = 1) :
    Cyclotomic.powRingHom hn (omega i k) = omega i (d.index (d.rep k ^ n)) := by
  have hcard : (d.classFinset (d.index (d.rep k ^ n))).card = (d.classFinset k).card := by
    rw [d.card_classFinset, d.classOf_index, d.card_classFinset, d.classOf_eq_mk]
    exact ConjClasses.card_carrier_mk_pow _
      (hn.of_dvd_left (orderOf_dvd_of_pow_eq_one hg))
  have hconv := congrArg (Cyclotomic.powRingHom hn) (h.degree_mul_central i k)
  simp only [map_mul, map_natCast, h.powRingHom_table hn i k hg] at hconv
  have heq : (degree i : Cyclotomic e) * Cyclotomic.powRingHom hn (omega i k) =
      (degree i : Cyclotomic e) * omega i (d.index (d.rep k ^ n)) := by
    rw [hconv, h.degree_mul_central, hcard]
  apply Cyclotomic.complexEmbedding_injective
  have hmap := congrArg Cyclotomic.complexEmbedding heq
  simp only [map_mul, map_natCast] at hmap
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (h.degree_pos i).ne' : (degree i : ℂ) ≠ 0) hmap

/-- Every conjugate residue of a certified central entry is obtained by powering its column
representative in its reduction at one primitive root, when that representative has `e`-th power
one. -/
theorem conjugateResidues_omega (h : d.IsCyclotomicCharacterTableSpec e omega table degree)
    {p : ℕ} [Fact p.Prime] {α : ZMod p}
    (hα : IsPrimitiveRoot α e) (i k : Fin d.numClasses) (j : Fin e.totient)
    (hg : d.rep k ^ e = 1) :
    Cyclotomic.conjugateResidues α (omega i k) j =
      Cyclotomic.reduce p α (omega i (d.index (d.rep k ^ Cyclotomic.primitiveExponent e j))) := by
  rw [Cyclotomic.conjugateResidues_apply, Cyclotomic.conjugateRoot_def,
    ← Cyclotomic.reduce_powRingHom (Cyclotomic.coprime_primitiveExponent e j) hα,
    h.powRingHom_omega (Cyclotomic.coprime_primitiveExponent e j) i k hg]

end TauCeti.ClassData.IsCyclotomicCharacterTableSpec
