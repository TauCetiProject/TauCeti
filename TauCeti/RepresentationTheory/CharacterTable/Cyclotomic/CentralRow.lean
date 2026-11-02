/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Conj.CoprimePow
public import TauCeti.RepresentationTheory.CharacterTable.Cyclotomic
public import TauCeti.RepresentationTheory.CharacterTable.Cyclotomic.PowerMap
public import TauCeti.RepresentationTheory.CharacterTable.Recovery
public import TauCeti.RingTheory.Cyclotomic.Lift
public import TauCeti.RingTheory.Cyclotomic.Power

/-!
# The class-power and degree identities of a central character row

A row `Ω = (C ↦ ωᵪ(K_C))` of the central character table takes its values in the cyclotomic field
of the group exponent `e`. This file records two identities that constrain such a row without
reference to the ordinary character table.

**The class-power Galois identity.** For `b` coprime to `e`, write `σ_b` for the automorphism
`ζ ↦ ζ ^ b`. Then `Ω(C ^ b) = σ_b (Ω(C))`, where `C ^ b` is the class permutation
`ConjClasses.powEquiv`. Indeed `Ω(C) = |C| χ(g) / χ(1)`, the numbers `|C|` and `χ(1)` are fixed by
`σ_b`, the size `|C ^ b|` equals `|C|`, and `σ_b (χ(g)) = χ(g ^ b)`. The identity holds on exact
cyclotomic integers, on their reductions at the conjugate roots, and in any field embedded in `ℂ`
containing a primitive `e`-th root of unity.

**The degree identity.** With `n = |G|` and `s_C = |C|`, the sum
`T = ∑_C (n / s_C) Ω(C) Ω(C⁻¹)` equals `(n / χ(1)) ^ 2`, where each quotient `n / s_C` is exact. It
is Dixon's degree formula `TauCeti.Representation.finrank_sq_mul_classRowNorm_eq_card` with the
denominators of the class sizes cleared. The equation `m ^ 2 * T = n ^ 2` has the degree as its only
natural-number solution, so the row determines the degree.

## Main statements

* `TauCeti.complexEmbedding_powRingHom_centralCharacterTable`: the power substitution on an exact
  representative of a central entry represents the entry at the powered class.
* `TauCeti.powRingHom_centralRow` and `TauCeti.conjugateResidues_centralRow`: the same identity for
  an exact row, and for its reductions at the conjugate roots.
* `TauCeti.exists_centralRow_classPower`: a central row descends to any field embedded in `ℂ`
  containing a primitive `e`-th root of unity, where it satisfies the class-power identity.
* `TauCeti.characterDegree_sq_mul_sum_centralCharacterTable_eq_card_sq`: the division-free degree
  identity.
* `TauCeti.sum_centralRow_eq_card_div_sq`: the degree identity for a descended row.
* `TauCeti.natCast_sq_mul_sum_centralRow_eq_iff`: the degree is the unique solution.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, §12.4.
* W. Fulton, J. Harris, *Representation Theory*, Theorem 2.12.
* J. D. Dixon, *High speed computation of group characters* (1967).
-/

public section

open Module

namespace TauCeti

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

section ClassPower

variable {e n : ℕ} [NeZero e]

/-- The power substitution on an exact representative of a central-character entry represents the
entry at the powered class, provided the `e`-th power of the class representative is one. -/
theorem complexEmbedding_powRingHom_centralCharacterTable (hn : e.Coprime n)
    (i : Fin (Nat.card (ConjClasses G))) {g : G} (hg : g ^ e = 1) {y : Cyclotomic e}
    (hy : Cyclotomic.complexEmbedding y = centralCharacterTable ℂ G i (ConjClasses.mk g)) :
    Cyclotomic.complexEmbedding (Cyclotomic.powRingHom hn y) =
      centralCharacterTable ℂ G i (ConjClasses.mk (g ^ n)) := by
  let ρ := irreducibleRepresentation ℂ (G := G) i
  have hχ (h : G) : ρ.character h = characterTable ℂ G i (ConjClasses.mk h) := by
    simp [ρ, character_irreducibleRepresentation]
  -- An exact value of the character at `g` and its image under the power substitution.
  obtain ⟨x, hx⟩ : ∃ x : Cyclotomic e, Cyclotomic.complexEmbedding x = ρ.character g :=
    Cyclotomic.mem_range_complexEmbedding_iff.mpr
      (Representation.char_mem_adjoin_of_isPrimitiveRoot ρ
        Cyclotomic.isPrimitiveRoot_complexRoot hg)
  have hpow : Cyclotomic.complexEmbedding (Cyclotomic.powRingHom hn x) = ρ.character (g ^ n) :=
    ρ.map_cyclotomic_character_eq_character_pow hg hx
      (Cyclotomic.complexEmbedding.comp (Cyclotomic.powRingHom hn)) (by simp)
  -- The division-free relation between the two tables holds in the exact ring.
  have hexact : y * (characterDegree ℂ i : Cyclotomic e) =
      (Nat.card (ConjClasses.mk g).carrier : Cyclotomic e) * x := by
    apply Cyclotomic.complexEmbedding_injective
    simp only [map_mul, map_natCast, hy, hx, hχ]
    exact centralCharacterTable_mul_characterDegree i _
  have hsize := ConjClasses.card_carrier_mk_pow g
    (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hg) hn)
  have hd : (characterDegree ℂ i : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (characterDegree_pos ℂ i).ne'
  apply mul_right_cancel₀ hd
  rw [centralCharacterTable_mul_characterDegree, ← hχ, ← hpow, hsize]
  simpa only [map_mul, map_natCast] using
    congrArg (fun z ↦ Cyclotomic.complexEmbedding (Cyclotomic.powRingHom hn z)) hexact

variable (he : e = Monoid.exponent G) {i : Fin (Nat.card (ConjClasses G))}
  {y : ConjClasses G → Cyclotomic e}

include he

/-- **The class-power identity on an exact central row.** The power substitution `ζ ↦ ζ ^ n` sends
the exact entry at `C` to the exact entry at `C ^ n`. -/
theorem powRingHom_centralRow (hn : e.Coprime n)
    (hy : ∀ C, Cyclotomic.complexEmbedding (y C) = centralCharacterTable ℂ G i C)
    (C : ConjClasses G) : Cyclotomic.powRingHom hn (y C) = y (C ^ n) := by
  obtain ⟨g, rfl⟩ := C.exists_rep
  apply Cyclotomic.complexEmbedding_injective
  rw [ConjClasses.mk_pow, hy, complexEmbedding_powRingHom_centralCharacterTable hn i
    (he ▸ Monoid.pow_exponent_eq_one g) (hy _)]

/-- **The class-power identity on reductions.** The reduction of an exact central entry at a
conjugate root is the reduction at the original root of the entry at the powered class. -/
theorem conjugateResidues_centralRow {p : ℕ} {α : ZMod p}
    (hα : (Polynomial.cyclotomic e ℤ).eval₂ (Int.castRingHom (ZMod p)) α = 0)
    (hy : ∀ C, Cyclotomic.complexEmbedding (y C) = centralCharacterTable ℂ G i C)
    (C : ConjClasses G) (j : Fin e.totient) :
    Cyclotomic.conjugateResidues α (y C) j =
      Cyclotomic.reduce p α (y (C ^ Cyclotomic.primitiveExponent e j)) := by
  rw [Cyclotomic.conjugateResidues_apply, Cyclotomic.conjugateRoot_def,
    ← Cyclotomic.reduce_powRingHom (Cyclotomic.coprime_primitiveExponent e j) hα,
    powRingHom_centralRow he _ hy]

/-- **The descended class-power identity.** A row of the central character table descends to any
field `K` embedded in `ℂ` containing a primitive `e`-th root of unity `ζ`, and an endomorphism of
`K` taking `ζ` to `ζ ^ b` carries the value on `C` to the value on `C ^ b`. Coprimality of `b` and
`e` is not assumed, since it follows from `ζ ^ b` being the image of a primitive root. -/
theorem exists_centralRow_classPower {K : Type*} [Field K] [Algebra K ℂ] {ζ : K}
    (hζ : IsPrimitiveRoot ζ e) (i : Fin (Nat.card (ConjClasses G))) :
    ∃ w : ConjClasses G → K, (∀ C, algebraMap K ℂ (w C) = centralCharacterTable ℂ G i C) ∧
      ∀ (σ : K →+* K) (b : ℕ), σ ζ = ζ ^ b → ∀ C, w (C ^ b) = σ (w C) := by
  obtain ⟨f, hf, hσf⟩ := Cyclotomic.exists_ringHom_comp_eq_complexEmbedding (algebraMap K ℂ) hζ
  choose y hy using centralCharacterTable_mem_range_complexEmbedding e he i
  refine ⟨fun C ↦ f (y C), fun C ↦ ?_, fun σ b hσ C ↦ ?_⟩
  · rw [← hy C, ← hf, RingHom.comp_apply]
  · have hprim : IsPrimitiveRoot (ζ ^ b) e := hσ ▸ hζ.map_of_injective σ.injective
    have hb : e.Coprime b := ((hζ.pow_iff_coprime (NeZero.pos e) b).mp hprim).symm
    beta_reduce
    rw [← powRingHom_centralRow he hb hy, ← RingHom.comp_apply, ← hσf σ hb hσ,
      RingHom.comp_apply]

end ClassPower

section Degree

/-- **The division-free degree identity.** Over any algebraically closed field in which `|G|` is
invertible, `χ(1) ^ 2 * ∑_C (|G| / |C|) Ω(C) Ω(C⁻¹) = |G| ^ 2`, the quotients being exact natural
number divisions. -/
theorem characterDegree_sq_mul_sum_centralCharacterTable_eq_card_sq {k : Type*} [Field k]
    [IsAlgClosed k] [Invertible (Nat.card G : k)] (i : Fin (Nat.card (ConjClasses G))) :
    (characterDegree k i : k) ^ 2 * ∑ C : ConjClasses G,
        ((Nat.card G / Nat.card C.carrier : ℕ) : k) * centralCharacterTable k G i C *
          centralCharacterTable k G i C⁻¹ =
      (Nat.card G : k) ^ 2 := by
  have hG : (Nat.card G : k) ≠ 0 := Invertible.ne_zero _
  have hrow : centralCharacterTable k G i =
      classSumRow (Representation.centralCharacter (irreducibleRepresentation k i)) := by
    funext C
    rw [centralCharacterTable_apply, classSumRow_apply]
  have hsum : ∑ C : ConjClasses G,
      ((Nat.card G / Nat.card C.carrier : ℕ) : k) * centralCharacterTable k G i C *
        centralCharacterTable k G i C⁻¹ =
      (Nat.card G : k) * classRowNorm (centralCharacterTable k G i) := by
    rw [classRowNorm_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun C _ ↦ ?_
    rw [Nat.cast_div (ConjClasses.card_carrier_dvd_card C)
      (ConjClasses.card_carrier_cast_ne_zero C hG)]
    ring
  have hrec := Representation.finrank_sq_mul_classRowNorm_eq_card
    (irreducibleRepresentation k (G := G) i)
  rw [← hrow, finrank_fin_fun] at hrec
  rw [hsum, mul_left_comm, hrec, sq]

variable {K : Type*} [Field K] [Algebra K ℂ] {i : Fin (Nat.card (ConjClasses G))}
  {w : ConjClasses G → K}

/-- **The degree identity for a descended row.** In a field `K` embedded in `ℂ`, a row descending a
row of the central character table satisfies
`∑_C (|G| / |C|) w(C) w(C⁻¹) = (|G| / χ(1)) ^ 2`. -/
theorem sum_centralRow_eq_card_div_sq
    (hw : ∀ C, algebraMap K ℂ (w C) = centralCharacterTable ℂ G i C) :
    ∑ C : ConjClasses G, ((Nat.card G / Nat.card C.carrier : ℕ) : K) * w C * w C⁻¹ =
      ((Nat.card G : K) / (characterDegree ℂ i : K)) ^ 2 := by
  have hd : (characterDegree ℂ i : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (characterDegree_pos ℂ i).ne'
  apply (algebraMap K ℂ).injective
  simp only [map_sum, map_mul, map_natCast, map_pow, map_div₀, hw]
  rw [div_pow, eq_div_iff (pow_ne_zero 2 hd), mul_comm]
  exact characterDegree_sq_mul_sum_centralCharacterTable_eq_card_sq i

/-- **The row determines the degree.** The degree `χ(1)` is the unique natural number `m` with
`m ^ 2 * ∑_C (|G| / |C|) w(C) w(C⁻¹) = |G| ^ 2`. -/
theorem natCast_sq_mul_sum_centralRow_eq_iff
    (hw : ∀ C, algebraMap K ℂ (w C) = centralCharacterTable ℂ G i C) (m : ℕ) :
    (m : K) ^ 2 *
        ∑ C : ConjClasses G, ((Nat.card G / Nat.card C.carrier : ℕ) : K) * w C * w C⁻¹ =
      (Nat.card G : K) ^ 2 ↔ m = characterDegree ℂ i := by
  have : CharZero K := (algebraMap K ℂ).charZero
  have hG : (Nat.card G : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hd : (characterDegree ℂ i : K) ≠ 0 := Nat.cast_ne_zero.mpr (characterDegree_pos ℂ i).ne'
  rw [sum_centralRow_eq_card_div_sq hw, div_pow, mul_div_assoc', div_eq_iff (pow_ne_zero 2 hd),
    mul_comm, mul_right_inj' (pow_ne_zero 2 hG)]
  constructor
  · intro h
    exact (Nat.pow_left_injective (n := 2) (by norm_num)) (by exact_mod_cast h)
  · rintro rfl
    rfl

end Degree

end TauCeti
