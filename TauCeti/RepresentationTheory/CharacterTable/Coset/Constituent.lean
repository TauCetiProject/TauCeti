/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.VirtualCharacter
import Mathlib.GroupTheory.IndexNormal
import TauCeti.GroupTheory.PGroup.FixedPointSum
import TauCeti.RepresentationTheory.CharacterTable.Automorphism.Quotient
import TauCeti.RepresentationTheory.CharacterTable.Coset.Pairing
import TauCeti.RepresentationTheory.CharacterTable.Coset.Orthogonality
import TauCeti.RepresentationTheory.CharacterTable.CyclicExtension

/-!
# Detecting constituents by pairing on a prime-index coset

Modulo a prime index, the pairing of two invariant virtual characters on a normal subgroup
only sees the stable irreducible characters. If an ambient virtual character is a scalar
multiple of an irreducible extension on the generator coset, then the orthogonality of
inequivalent extensions forces all other stable coefficients to vanish modulo the index.
A nondivisible pairing on the subgroup therefore detects the constituent of that extension.

The constituent conclusion is the character form of the vanishing statement for representations
with no shared constituent in Levent Alpöge's Lean formalization
<https://github.com/leanprover-community/riemann-hypothesis>,
`GlobalTheory.Shin.kills_of_norm_one_of_pairing_prime` in the split prime-index case.
-/

public section

namespace TauCeti

open ClassFunction

variable {k G : Type*} [Field k] [IsAlgClosed k] [CharZero k] [Group G]
  {N : Subgroup G} [N.Normal] [Fintype N]

/-- In prime index, if the products of the coefficients of two invariant virtual characters at
all stable irreducibles are divisible by the index, so is their pairing. The other products
occur in orbits of size equal to the index. -/
theorem exists_index_dvd_characterPairing_of_dvd_stable_coefficients (hp : N.index.Prime)
    {f y : ClassFunction k N} (hf : f.val ∈ virtualCharacters k N)
    (hy : y.val ∈ virtualCharacters k N)
    (hF : ∀ (g : G) (n : N), f.val (MulAut.conjNormal g n) = f.val n)
    (hY : ∀ (g : G) (n : N), y.val (MulAut.conjNormal g n) = y.val n)
    (hd : ∀ θ : ClassFunction k N, θ.val ∈ irreducibleCharacters k N →
      (∀ (g : G) (n : N), θ.val (MulAut.conjNormal g n) = θ.val n) →
      ∃ m : ℤ, (N.index : ℤ) ∣ m ∧ characterPairing f θ * characterPairing y θ = m) :
    ∃ m : ℤ, (N.index : ℤ) ∣ m ∧ characterPairing f y = m := by
  classical
  let : Fact N.index.Prime := ⟨hp⟩
  let : Invertible (Nat.card N : k) := invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let e := finEquivIrreducibleCharacters k N
  let : Fintype (irreducibleCharacters k N) := Fintype.ofFinite _
  have hχ (θ : irreducibleCharacters k N) :=
    irreducibleCharacters_subset_virtualCharacters θ.property
  let χ (θ : irreducibleCharacters k N) : ClassFunction k N :=
    ⟨θ, virtualCharacters_le_classFunction (hχ θ)⟩
  choose a ha using fun θ ↦ exists_characterPairing_eq_intCast (f₂ := χ θ) hf (hχ θ)
  choose b hb using fun θ ↦ exists_characterPairing_eq_intCast (f₂ := χ θ) hy (hχ θ)
  let w (θ : irreducibleCharacters k N) : ℤ := a θ * b θ
  have hweight (θ : irreducibleCharacters k N) :
      (w θ : k) = characterPairing f (χ θ) * characterPairing y (χ θ) := by
    simp only [w, Int.cast_mul, ha, hb]
  have hpair : characterPairing f y = ((∑ θ, w θ : ℤ) : k) := by
    rw [← e.sum_comp w, Int.cast_sum]
    nth_rewrite 1 [← sum_characterPairing_smul_ofCharacter (irreducibleRepresentation k)
      (pairwise_isEmpty_equiv_irreducibleRepresentation k) (by simp) f]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have heq : χ (e i) = ofCharacter (irreducibleRepresentation k i) :=
      Subtype.ext (funext fun n ↦ (congrFun (coe_finEquivIrreducibleCharacters_apply k i) n).trans
        (by rw [ofCharacter_apply, character_irreducibleRepresentation]))
    rw [hweight, heq, characterPairing_symm f, characterPairing_symm y]
  have hcoeff (v : ClassFunction k N)
      (hv : ∀ (g : G) (n : N), v.val (MulAut.conjNormal g n) = v.val n)
      (q : G ⧸ N) (θ : irreducibleCharacters k N) :
      characterPairing v (χ (q • θ)) = characterPairing v (χ θ) := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
    let l := MulAut.conjNormal (H := N) g⁻¹
    have h₁ : comap (l : N →* N) v = v :=
      Subtype.ext (funext fun n ↦ (comap_apply _ _ _).trans (hv g⁻¹ n))
    have h₂ : comap (l : N →* N) (χ θ) = χ ((g : G ⧸ N) • θ) :=
      Subtype.ext (funext fun n ↦ by
        simp only [comap_apply, χ, quotient_smul_irreducibleCharacters_apply, ← map_inv]
        rfl)
    simpa only [QuotientGroup.mk'_apply, h₁, h₂] using characterPairing_comap_mulEquiv l v (χ θ)
  refine ⟨∑ θ, w θ, ?_, hpair⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sum]
  have hpq : IsPGroup N.index (G ⧸ N) := IsPGroup.of_card (n := 1) (by rw [pow_one, Subgroup.index])
  have hw (q : G ⧸ N) (θ : irreducibleCharacters k N) : w (q • θ) = w θ :=
    Int.cast_injective (by rw [hweight, hweight, hcoeff f hF, hcoeff y hY])
  rw [hpq.sum_eq_sum_fixedPoints (fun θ ↦ (w θ : ZMod N.index)) (fun q θ ↦ by rw [hw])]
  refine Finset.sum_eq_zero fun θ hθ ↦ ?_
  obtain ⟨m, hm, heq⟩ := hd (χ θ) θ.property
    (mem_fixedPoints_quotient_irreducibleCharacters_iff.mp (Finset.mem_filter.mp hθ).2)
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (Int.cast_injective ((hweight θ).trans heq) ▸ hm)

/-- Suppose `X` agrees on `xN` with a scalar multiple of a character `χ` whose restriction is
irreducible. If the pairing of `X|ₙ` with an `x`-stable virtual character `Y` is not divisible by
the prime index, the pairing of `χ|ₙ` with `Y` is nonzero. In particular, when `Y` is a character,
`χ|ₙ` is a constituent of `Y`. -/
theorem characterPairing_ne_zero_of_index_not_dvd_of_eq_on_coset (hp : N.index.Prime)
    {x : G} {X : ClassFunction k G} (hX : X.val ∈ virtualCharacters k G)
    (Z : FDRep k G) (hZ : Z.character ∘ N.subtype ∈ irreducibleCharacters k N)
    {b : k} (hcoset : ∀ n : N, X.val (x * n) = b * Z.character (x * n))
    {Y : ClassFunction k N} (hY : Y.val ∈ virtualCharacters k N)
    (hYx : ∀ n : N, Y.val (MulAut.conjNormal x n) = Y.val n)
    {m : ℤ} (hm : characterPairing (comap N.subtype X) Y = m) (hnd : ¬ (N.index : ℤ) ∣ m) :
    characterPairing (comap N.subtype (ofFDRep Z)) Y ≠ 0 := by
  let χN := comap N.subtype (ofFDRep Z)
  intro hzero
  -- If `x` lies in `N`, the two restrictions are already proportional on `N` itself.
  have hx : x ∉ N := by
    intro hx
    have hEq : comap N.subtype X = b • χN := by
      apply Subtype.ext
      funext n
      simpa only [χN, comap_apply, ofFDRep_apply, Subgroup.subtype_apply, Submodule.coe_smul,
        Pi.smul_apply, smul_eq_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk,
        ← mul_assoc, mul_inv_cancel, one_mul] using hcoset ((⟨x, hx⟩ : N)⁻¹ * n)
    rw [hEq, map_smul, LinearMap.smul_apply, hzero, smul_zero] at hm
    exact hnd (Int.cast_eq_zero.mp hm.symm ▸ dvd_zero _)
  obtain ⟨d, hd, hpair⟩ := exists_index_dvd_characterPairing_of_dvd_stable_coefficients hp
    (comap_mem_virtualCharacters N.subtype hX) hY (comap_subtype_apply_conjNormal X)
    (apply_conjNormal_eq_of_isCoatom Y (N.isCoatom_of_index_prime hp) hx hYx) (by
      intro θ hθ hθinv
      by_cases heq : θ = χN
      · subst θ
        exact ⟨0, dvd_zero _, by rw [characterPairing_symm Y, hzero, mul_zero, Int.cast_zero]⟩
      obtain ⟨ψ, hψ, hψres⟩ := exists_irreducibleCharacter_extension_of_index_prime hp hx hθ
        (funext (hθinv x))
      obtain ⟨_, ρψ, _, rfl⟩ := mem_irreducibleCharacters_iff.mp hψ
      have hψN : (fun n : N ↦ ρψ.character n) = θ.val := hψres
      have hχN : χN.val = fun n : N ↦ Representation.character Z.ρ n := by
        funext n
        simp only [χN, comap_apply, ofFDRep_apply, Subgroup.subtype_apply,
          ← FDRep.character_ρ]
      have horth := Representation.sum_character_mul_mul_character_mul_inv_eq_zero Z.ρ ρψ N hZ
        (hψN.symm ▸ hθ) (fun h ↦ heq (Subtype.ext (hψN.symm.trans (hχN.trans h).symm))) x
      have hcos : ∑ n : N, X.val (x * n) * ρψ.character (x * n)⁻¹ = 0 := by
        simp only [hcoset, ← FDRep.character_ρ Z, mul_assoc, ← Finset.mul_sum, horth, mul_zero]
      obtain ⟨a, ha, ha'⟩ := index_dvd_pairing_of_coset_pairing_eq_zero hp hX
        (irreducibleCharacters_subset_virtualCharacters (character_mem_irreducibleCharacters ρψ))
        x hcos
      obtain ⟨c, hc⟩ := exists_characterPairing_eq_intCast hY
        (irreducibleCharacters_subset_virtualCharacters hθ)
      refine ⟨a * c, dvd_mul_of_dvd_left ha _, ?_⟩
      rw [Int.cast_mul, hc, characterPairing_apply (comap N.subtype X), ← hψres]
      simp only [comap_apply, Function.comp_apply, Subgroup.subtype_apply, ha'])
  exact hnd (Int.cast_injective (hm.symm.trans hpair) ▸ hd)

end TauCeti
