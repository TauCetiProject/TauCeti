/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.CoefficientAction
public import TauCeti.RepresentationTheory.CharacterTable.Galois
import TauCeti.RepresentationTheory.Induction.Cyclotomic.SplittingField

/-!
# Cyclotomic Galois actions on characters

If `K` contains a primitive `n`-th root of unity and the exponent of the finite group `G` divides
`n`, Brauer splitting identifies the virtual-character lattice over an algebraically closed
extension `L` with the lattice over `K`. Transporting coefficient automorphisms along this
identification gives the Galois action on virtual characters over `L`. Its value formula is
`(σ · χ)(g) = χ(g ^ j)`, with `j` the cyclotomic exponent `autToPow` of `σ`.

The action permutes the irreducible characters, preserving their degrees. In particular it applies
to `K = ℚ(ζ_e) ⊆ ℂ`, `L = ℂ`, and the group exponent `e`.
No extension of an automorphism of `K` to the whole field `L` is chosen.

The lattice identification is `TauCeti.virtualCharacters_eq_map_of_isPrimitiveRoot`, and
irreducibility is detected by `TauCeti.mem_irreducibleCharacters_of_characterPairing_self_eq_one`.

## References

* J.-P. Serre, *Linear Representations of Finite Groups* (1977), §§12.3–12.4.
* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Chapter 9.
-/

public section

open Module

namespace IsPrimitiveRoot

open TauCeti

universe u

variable {K L G : Type u} [Field K] [Field L] [Algebra K L] [CharZero K]
  [Group G] [Finite G] [IsAlgClosed L]
  {n : ℕ} [NeZero n] {ζ : K}

/-- Scalar extension from a field containing the requisite roots of unity identifies the entire
virtual-character lattice with the lattice over an algebraically closed extension. -/
noncomputable def cyclotomicVirtualCharacterEquiv (hζ : IsPrimitiveRoot ζ n)
    (hG : Monoid.exponent G ∣ n) : virtualCharacters K G ≃+ virtualCharacters L G := by
  let f : virtualCharacters K G →+ virtualCharacters L G :=
    { toFun χ := ⟨algebraMap K L ∘ χ.1, (algebraMap K L).comp_mem_virtualCharacters χ.2⟩
      map_zero' := by ext g; simp
      map_add' χ ψ := by ext g; simp }
  refine AddEquiv.ofBijective f ⟨?_, ?_⟩
  · intro χ ψ h
    apply Subtype.ext
    funext g
    exact (algebraMap K L).injective (congrArg (fun χ => χ.1 g) h)
  · intro χ
    have hχ := χ.2
    simp only [virtualCharacters_eq_map_of_isPrimitiveRoot hζ hG] at hχ
    obtain ⟨ψ, hψ, hψχ⟩ := AddSubgroup.mem_map.mp hχ
    exact ⟨⟨ψ, hψ⟩, Subtype.ext hψχ⟩

/-- The scalar-extension equivalence is the coefficient embedding on every value. -/
@[simp]
theorem cyclotomicVirtualCharacterEquiv_apply (hζ : IsPrimitiveRoot ζ n)
    (hG : Monoid.exponent G ∣ n) (χ : virtualCharacters K G) (g : G) :
    (cyclotomicVirtualCharacterEquiv (L := L) hζ hG χ).1 g = algebraMap K L (χ.1 g) :=
by
  unfold cyclotomicVirtualCharacterEquiv
  rfl

variable [Algebra ℚ K]

/-- The Galois action on the virtual-character lattice, transported from the splitting field. -/
noncomputable def cyclotomicVirtualCharacterAction (hζ : IsPrimitiveRoot ζ n)
    (hG : Monoid.exponent G ∣ n) :
    Gal(K/ℚ) →* Multiplicative (AddAut (virtualCharacters L G)) where
  toFun σ := Multiplicative.ofAdd
    ((cyclotomicVirtualCharacterEquiv hζ hG).symm.trans
      (σ.toRingEquiv.virtualCharacterEquiv.trans (cyclotomicVirtualCharacterEquiv hζ hG)))
  map_one' := by
    apply congrArg Multiplicative.ofAdd
    ext χ g
    simp only [AddEquiv.trans_apply, RingEquiv.virtualCharacterEquiv_apply,
      cyclotomicVirtualCharacterEquiv_apply]
    exact congrArg (fun χ => χ.1 g)
      ((cyclotomicVirtualCharacterEquiv (L := L) hζ hG).apply_symm_apply χ)
  map_mul' σ τ := by
    apply congrArg Multiplicative.ofAdd
    ext χ g
    simp

/-- On scalar-extended virtual characters the action is the coefficient automorphism in the
splitting field. -/
theorem cyclotomicVirtualCharacterAction_equiv_apply (hζ : IsPrimitiveRoot ζ n)
    (hG : Monoid.exponent G ∣ n) (σ : Gal(K/ℚ)) (χ : virtualCharacters K G) (g : G) :
    (Multiplicative.toAdd (cyclotomicVirtualCharacterAction (L := L) hζ hG σ)
      (cyclotomicVirtualCharacterEquiv hζ hG χ)).1 g = algebraMap K L (σ (χ.1 g)) := by
  simp [cyclotomicVirtualCharacterAction]

/-- The cyclotomic Galois action on every virtual character is the power map on group elements. -/
@[simp]
theorem cyclotomicVirtualCharacterAction_apply (hζ : IsPrimitiveRoot ζ n)
    (hG : Monoid.exponent G ∣ n) (σ : Gal(K/ℚ)) (χ : virtualCharacters L G) (g : G) :
    (Multiplicative.toAdd (cyclotomicVirtualCharacterAction hζ hG σ) χ).1 g =
      χ.1 (g ^ (hζ.autToPow ℚ σ : ZMod n).val) := by
  obtain ⟨ψ, rfl⟩ := (cyclotomicVirtualCharacterEquiv (L := L) hζ hG).surjective χ
  rw [cyclotomicVirtualCharacterAction_equiv_apply, cyclotomicVirtualCharacterEquiv_apply]
  apply congrArg (algebraMap K L)
  obtain ⟨A, B, hψ⟩ := exists_eq_character_sub_character ψ.2
  rw [hψ, Pi.sub_apply, Pi.sub_apply, map_sub]
  have hg : g ^ n = 1 := by
    obtain ⟨m, rfl⟩ := hG
    rw [pow_mul, Monoid.pow_exponent_eq_one, one_pow]
  have hpower := (hζ.autToPow_spec ℚ σ).symm
  congr 1
  · exact Representation.map_character_eq_character_pow_of_isPrimitiveRoot A.ρ hζ
      (Nat.cast_ne_zero.mpr (NeZero.ne n)) hg σ.toAlgHom.toRingHom hpower
  · exact Representation.map_character_eq_character_pow_of_isPrimitiveRoot B.ρ hζ
      (Nat.cast_ne_zero.mpr (NeZero.ne n)) hg σ.toAlgHom.toRingHom hpower

/-- The cyclotomic Galois action preserves irreducible characters. -/
theorem cyclotomicVirtualCharacterAction_mem_irreducibleCharacters
    (hζ : IsPrimitiveRoot ζ n) (hG : Monoid.exponent G ∣ n) (σ : Gal(K/ℚ))
    (χ : virtualCharacters L G) (hχ : χ.1 ∈ irreducibleCharacters L G) :
    (Multiplicative.toAdd (cyclotomicVirtualCharacterAction hζ hG σ) χ).1 ∈
      irreducibleCharacters L G := by
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  let : Fintype G := Fintype.ofFinite G
  let : Invertible (Nat.card G : K) := invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card G : L) := invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨ψ, rfl⟩ := (cyclotomicVirtualCharacterEquiv (L := L) hζ hG).surjective χ
  let F : ClassFunction K G := ⟨ψ.1, virtualCharacters_le_classFunction ψ.2⟩
  obtain ⟨d, ρ, hρ, hρχ⟩ := mem_irreducibleCharacters_iff.mp hχ
  have := hρ
  have hF : ClassFunction.map (algebraMap K L) F = ClassFunction.ofCharacter ρ := by
    ext g
    simpa only [ClassFunction.map_apply, ClassFunction.ofCharacter_apply,
      cyclotomicVirtualCharacterEquiv_apply] using (congrFun hρχ g).symm
  have hnorm : ClassFunction.characterPairing F F = 1 := by
    apply (algebraMap K L).injective
    rw [← ClassFunction.characterPairing_map, hF]
    simp
  have haction :
      (ClassFunction.map (algebraMap K L) (ClassFunction.map σ.toAlgHom.toRingHom F)).1 =
      (Multiplicative.toAdd (cyclotomicVirtualCharacterAction hζ hG σ)
        (cyclotomicVirtualCharacterEquiv hζ hG ψ)).1 := by
    funext g
    simp only [ClassFunction.map_apply, cyclotomicVirtualCharacterAction_equiv_apply]
    rfl
  rw [← haction]
  refine mem_irreducibleCharacters_of_characterPairing_self_eq_one ?_ ?_ (n := d) ?_
  · rw [haction]
    exact (Multiplicative.toAdd (cyclotomicVirtualCharacterAction hζ hG σ)
      (cyclotomicVirtualCharacterEquiv hζ hG ψ)).2
  · rw [ClassFunction.characterPairing_map, ClassFunction.characterPairing_map, hnorm]
    simp
  · have h1 := congrFun hρχ 1
    rw [Representation.char_one] at h1
    have hdeg : F.1 1 = d := by
      apply (algebraMap K L).injective
      simpa [F] using h1.symm
    rw [ClassFunction.map_apply, ClassFunction.map_apply, hdeg]
    simp

/-- The Galois group acts on the actual irreducible characters, independently of a
choice of row enumeration for a character table. -/
noncomputable def cyclotomicIrreducibleCharacterAction (hζ : IsPrimitiveRoot ζ n)
    (hG : Monoid.exponent G ∣ n) : Gal(K/ℚ) →* Equiv.Perm (irreducibleCharacters L G) := by
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  let : Invertible (Nat.card G : L) := invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let ι : irreducibleCharacters L G → virtualCharacters L G := fun χ =>
    ⟨χ.1, by
      rw [virtualCharacters_eq_closure_irreducibleCharacters]
      exact AddSubgroup.subset_closure χ.2⟩
  let f (σ : Gal(K/ℚ)) (χ : irreducibleCharacters L G) : irreducibleCharacters L G :=
    ⟨(Multiplicative.toAdd (cyclotomicVirtualCharacterAction hζ hG σ) (ι χ)).1,
      cyclotomicVirtualCharacterAction_mem_irreducibleCharacters hζ hG σ (ι χ) χ.2⟩
  have hinj (σ : Gal(K/ℚ)) : Function.Injective (f σ) := by
    intro χ ψ h
    have hv := (Multiplicative.toAdd (cyclotomicVirtualCharacterAction hζ hG σ)).injective
      (Subtype.ext (by simpa only [f] using congrArg Subtype.val h))
    exact Subtype.ext (by simpa only [ι] using congrArg Subtype.val hv)
  refine
    { toFun σ := Equiv.ofBijective (f σ) ⟨hinj σ, Finite.surjective_of_injective (hinj σ)⟩
      map_one' := ?_
      map_mul' := ?_ }
  · ext χ g
    simp only [Equiv.ofBijective_apply, f, MonoidHom.map_one]
    rfl
  · intro σ τ
    ext χ g
    simp [f, ι, cyclotomicVirtualCharacterAction]

/-- The permutation of irreducible characters has the cyclotomic power-map value formula. -/
@[simp]
theorem cyclotomicIrreducibleCharacterAction_apply (hζ : IsPrimitiveRoot ζ n)
    (hG : Monoid.exponent G ∣ n) (σ : Gal(K/ℚ)) (χ : irreducibleCharacters L G) (g : G) :
    (cyclotomicIrreducibleCharacterAction hζ hG σ χ).1 g =
      χ.1 (g ^ (hζ.autToPow ℚ σ : ZMod n).val) := by
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  let : Invertible (Nat.card G : L) := invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact cyclotomicVirtualCharacterAction_apply hζ hG σ
    ⟨χ.1, by
      rw [virtualCharacters_eq_closure_irreducibleCharacters]
      exact AddSubgroup.subset_closure χ.2⟩ g

end IsPrimitiveRoot
