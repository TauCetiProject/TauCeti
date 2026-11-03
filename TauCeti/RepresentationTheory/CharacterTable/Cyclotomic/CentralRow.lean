/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Conj
public import TauCeti.RepresentationTheory.CharacterTable.Cyclotomic
public import TauCeti.RepresentationTheory.CharacterTable.Cyclotomic.PowerMap
public import TauCeti.RingTheory.Cyclotomic.Lift
public import TauCeti.RingTheory.Cyclotomic.Power

/-!
# The class-power identity of a central character row

A row `Ω = (C ↦ ωᵪ(K_C))` of the central character table takes its values in the cyclotomic field
of any multiple `e` of the group exponent. This file records the class-power Galois identity, which
constrains such a row without reference to the ordinary character table. For `b` coprime to `e`,
write `σ_b` for the automorphism `ζ ↦ ζ ^ b`. Then `Ω(C ^ b) = σ_b (Ω(C))`, where `C ^ b` is the
class permutation `ConjClasses.powEquiv`. Indeed `Ω(C) = |C| χ(g) / χ(1)`, the numbers `|C|` and
`χ(1)` are fixed by `σ_b`, the size `|C ^ b|` equals `|C|`, and `σ_b (χ(g)) = χ(g ^ b)`. The
identity holds on exact cyclotomic integers, on their reductions at the conjugate roots, and in any
field embedded in `ℂ` containing a primitive `e`-th root of unity.

## Main statements

* `TauCeti.complexEmbedding_powRingHom_centralCharacterTable`: the power substitution on an exact
  representative of a central entry represents the entry at the powered class.
* `TauCeti.powRingHom_centralRow` and `TauCeti.conjugateResidues_centralRow`: the same identity for
  an exact row, and for its reductions at the conjugate roots.
* `TauCeti.exists_centralRow_classPower`: a central row descends to any field embedded in `ℂ`
  containing a primitive `e`-th root of unity, where it satisfies the class-power identity.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, §12.4.
-/

public section

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

variable (he : Monoid.exponent G ∣ e) {i : Fin (Nat.card (ConjClasses G))}
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
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp he g) (hy _)]

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

end TauCeti
