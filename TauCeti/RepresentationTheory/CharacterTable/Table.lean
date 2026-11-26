/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Completeness
public import TauCeti.RepresentationTheory.CharacterTable.Degree.Basic
-- `FDRep.character_mem_irreducibleCharacters` is stated for a simple object of `FDRep k G`.
public import TauCeti.RepresentationTheory.Simple.Basic
import TauCeti.SetTheory.Cardinal.Finite
import TauCeti.RepresentationTheory.FDRep.Basic
-- Non-public: irreducibility transports along an equivariant linear equivalence, used to move an
-- irreducible representation onto a coordinate space.
import TauCeti.RepresentationTheory.Irreducible
-- Non-public: a linear character is the character of its line `Representation.ofLinearCharacter`.
import TauCeti.RepresentationTheory.LinearCharacter.Basic

/-!
# The character table of a finite group

Let `G` be a finite group and `k` an algebraically closed field in which `|G|` is invertible. The
characters of the irreducible representations of `G` over `k` form a finite set
`TauCeti.irreducibleCharacters k G` of functions `G → k`, of size the number of conjugacy classes of
`G`: they are linearly independent, they span the class functions, and every irreducible
representation is equivalent to one that occurs in the complete family produced by the Wedderburn
decomposition of `k[G]`.

Choosing an enumeration of that set by `Fin r`, `r = |ConjClasses G|`, turns the irreducible
characters into the rows of a **square matrix**, the character table
`TauCeti.characterTable k G : Matrix (Fin r) (ConjClasses G) k`, whose `(i, C)` entry is the value
of the `i`-th irreducible character on the class `C`. Its columns are labelled by the actual
conjugacy classes of `G`; only the rows depend on the enumeration, and any two enumerations differ
by a permutation of them.

The two orthogonality relations become statements about the table: its rows are orthonormal for the
character pairing, and its columns are orthogonal with the class sizes as weights. Over `ℂ` both
take their familiar Hermitian form, because inversion conjugates character values
(`Representation.conj_char`).

## Main definitions

* `TauCeti.irreducibleCharacters`: the set of irreducible characters of `G` over `k`.
* `TauCeti.irreducibleCharacter`: the `i`-th irreducible character, for an enumeration of that set
  by `Fin (Nat.card (ConjClasses G))`, together with `TauCeti.irreducibleRepresentation`, an
  irreducible representation affording it, and `TauCeti.characterDegree`, its degree.
* `TauCeti.irreducibleCharactersOver`: the irreducible characters `Irr(G | θ)` of `G` lying over a
  function `θ` on a subgroup `N`.
* `TauCeti.characterTable`: the character table of `G`.
* `TauCeti.basisIrreducibleCharacter`: its rows, as a basis of the class functions, so that
  `TauCeti.linearIndependent_irreducibleCharacter` holds in `G → k`.

## Main results

* `TauCeti.card_irreducibleCharacters`: **`G` has as many irreducible characters as conjugacy
  classes**, so the table is square; `TauCeti.character_mem_irreducibleCharacters` is the statement
  that no irreducible character is missing from it, and `MonoidHom.coe_mem_irreducibleCharacters`
  puts every linear character `G →* kˣ` in it.
* `TauCeti.characterTable_apply`: the entries of the table are the irreducible character values.
* `TauCeti.card_inv_mul_sum_characterTable_mul_characterTable_inv` and
  `TauCeti.card_inv_mul_sum_characterTable_mul_conj`: **first (row) orthogonality**, over `k` and in
  its Hermitian form over `ℂ`; `TauCeti.card_inv_mul_sum_card_conjClass_mul_characterTable_mul_conj`
  is the latter summed one column at a time, the form in which `TauCeti.IsCharacterTableSpec` asks
  for it;
  `TauCeti.characterPairing_ofCharacter_irreducibleRepresentation_orthonormal` is the same relation
  phrased as orthonormality for the character pairing, and
  `TauCeti.sum_mul_inv_of_mem_irreducibleCharacters` is the same relation for the set of
  irreducible characters, free of the enumeration and of division.
* `TauCeti.one_mem_irreducibleCharacters`: the trivial character is irreducible;
  `TauCeti.exists_irreducibleCharacter_eq_one`: it is a row of the table, and every other row is
  nonconstant
  (`TauCeti.exists_irreducibleCharacter_ne_characterDegree`).
* `TauCeti.card_conjClass_mul_sum_characterTable_mul_characterTable_inv` and
  `TauCeti.sum_characterTable_mul_conj`: **second (column) orthogonality**, over `k` and in its
  Hermitian form over `ℂ`.
* `TauCeti.irreducibleCharacter_apply_mem_of_forall_pow_eq_one_mem`: the entries lie in every
  subring containing the `|G|`-th roots of unity.
* `TauCeti.characterTable_one`: the identity-class column of the table lists the degrees, which are
  positive (`TauCeti.characterDegree_pos`) and have squares summing to `|G|`
  (`TauCeti.sum_characterDegree_sq_eq_card`); in characteristic zero they moreover divide `|G|`
  (`TauCeti.characterDegree_dvd_card`). For a commutative group every degree is one
  (`TauCeti.apply_one_eq_one_of_mem_irreducibleCharacters_of_isMulCommutative`).
* `TauCeti.mem_irreducibleCharactersOver_of_restrict_eq`: an irreducible character restricting to
  an irreducible character `θ` of a finite subgroup lies over `θ`.

## Implementation notes

`TauCeti.irreducibleCharacters` is defined by the representations on the coordinate spaces
`Fin n → k`, the shape in which the Wedderburn blocks of `k[G]` produce them; this also keeps the
set free of a universe parameter beyond those of `k` and `G`. Nothing is lost:
`TauCeti.character_mem_irreducibleCharacters` puts the character of an irreducible representation on
*any* finite-dimensional space in the set, since it is equivalent to one of the coordinate ones.

The rows are indexed by `Fin (Nat.card (ConjClasses G))` rather than by a bare `Fin r`, so that the
squareness of the table is visible in its type.

Everything holds over any algebraically closed field in which `|G|` is invertible except the
Hermitian refinements, which are stated over `ℂ`, and the divisibility of the degrees by `|G|`,
which additionally assumes `CharZero k`. So the table is defined over such a `k`, and
`TauCeti.characterTable ℂ G` is the classical complex character table.

## References

See I. M. Isaacs, *Character Theory of Finite Groups* (1976), Chapter 2, or J.-P. Serre, *Linear
Representations of Finite Groups* (1977), Section 2.5.
-/

public section

namespace TauCeti

open Module

universe u v w

section Set

variable (k : Type u) (G : Type v) [Field k] [Group G]

/-- **The irreducible characters of `G` over `k`**: the set of characters of the irreducible
representations of `G` on the coordinate spaces `Fin n → k`.

Restricting to coordinate spaces costs nothing: by `TauCeti.character_mem_irreducibleCharacters` the
character of an irreducible representation on any finite-dimensional space belongs to this set. -/
def irreducibleCharacters : Set (G → k) :=
  {f | ∃ (n : ℕ) (ρ : Representation k G (Fin n → k)), ρ.IsIrreducible ∧ ρ.character = f}

variable {k G}

/-- Membership in `TauCeti.irreducibleCharacters` unfolded. This is deliberately not `@[simp]`:
unfolding membership to the existential would put the left-hand side of the `@[simp]` lemma
`TauCeti.irreducibleCharacter_mem` out of simp normal form, and simp cannot discharge the
existential it produces. -/
theorem mem_irreducibleCharacters_iff {f : G → k} :
    f ∈ irreducibleCharacters k G ↔
      ∃ (n : ℕ) (ρ : Representation k G (Fin n → k)), ρ.IsIrreducible ∧ ρ.character = f :=
  Iff.rfl

/-- **The character of an irreducible representation is an irreducible character**: the character
of an irreducible representation on an arbitrary finite-dimensional space lies in
`TauCeti.irreducibleCharacters`, because a basis transports it to an equivalent representation on a
coordinate space. -/
@[simp]
theorem character_mem_irreducibleCharacters {V : Type w} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (σ : Representation k G V) [σ.IsIrreducible] :
    σ.character ∈ irreducibleCharacters k G := by
  let e : V ≃ₗ[k] (Fin (finrank k V) → k) := (Module.finBasis k V).equivFun
  -- the representation `σ` transported along `e`
  let ρ : Representation k G (Fin (finrank k V) → k) :=
    { toFun g := e.conj (σ g)
      map_one' := by simp [Module.End.one_eq_id, LinearEquiv.conj_id]
      map_mul' g h := by simp [Module.End.mul_eq_comp, LinearEquiv.conj_comp] }
  have he : ∀ g v, e (σ g v) = ρ g (e v) := fun g v => by
    simp [ρ, LinearEquiv.conj_apply_apply]
  exact ⟨_, ρ, Representation.isIrreducible_of_linearEquiv e he ‹_›,
    (_root_.Representation.char_iso (Representation.Equiv.mk e fun g => LinearMap.ext (he g))).symm⟩

/-- **The character of a simple object of `FDRep k G` is an irreducible character**, the bundled
form of `TauCeti.character_mem_irreducibleCharacters`. -/
@[simp]
theorem _root_.FDRep.character_mem_irreducibleCharacters (X : FDRep k G)
    [CategoryTheory.Simple X] : X.character ∈ irreducibleCharacters k G :=
  have := FDRep.isIrreducible_of_simple X
  TauCeti.character_mem_irreducibleCharacters X.ρ

/-- **A linear character is an irreducible character**: `g ↦ χ g`, read in `k`, is the character
of the line `Representation.ofLinearCharacter χ`. -/
@[simp]
theorem _root_.MonoidHom.coe_mem_irreducibleCharacters (χ : G →* kˣ) :
    (fun g => (χ g : k)) ∈ irreducibleCharacters k G := by
  rw [← funext (Representation.char_ofLinearCharacter χ)]
  exact character_mem_irreducibleCharacters _

/-- **The trivial character is irreducible**: the constant function `1` is the character of the
trivial one-dimensional representation. -/
theorem one_mem_irreducibleCharacters : (fun _ : G => (1 : k)) ∈ irreducibleCharacters k G := by
  have h : (Representation.trivial k G k).character = fun _ => 1 :=
    funext fun _ => by rw [Representation.char_trivial, Module.finrank_self, Nat.cast_one]
  exact h ▸ character_mem_irreducibleCharacters _

/-- An irreducible character does not vanish at the identity, where its value is its degree. -/
theorem apply_one_ne_zero_of_mem_irreducibleCharacters [CharZero k] {f : G → k}
    (hf : f ∈ irreducibleCharacters k G) : f 1 ≠ 0 := by
  obtain ⟨n, ρ, hρ, rfl⟩ := mem_irreducibleCharacters_iff.mp hf
  rw [Representation.char_one]
  exact hρ.natCast_finrank_ne_zero

/-- **An irreducible character of a commutative group is linear**: its value at the identity, its
degree, is one. -/
theorem apply_one_eq_one_of_mem_irreducibleCharacters_of_isMulCommutative [IsAlgClosed k]
    [IsMulCommutative G] {f : G → k} (hf : f ∈ irreducibleCharacters k G) : f 1 = 1 := by
  obtain ⟨n, ρ, hρ, rfl⟩ := mem_irreducibleCharacters_iff.mp hf
  rw [Representation.char_one, Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative ρ,
    Nat.cast_one]

variable [IsAlgClosed k] [Invertible (Nat.card G : k)]

variable (k G)

/-- **The irreducible characters of `G` correspond to its conjugacy classes.** A complete family of
pairwise inequivalent irreducible representations is indexed by `ConjClasses G`, its characters are
distinct because they are linearly independent, and every irreducible character is one of them. -/
theorem nonempty_equiv_conjClasses_irreducibleCharacters :
    Nonempty (ConjClasses G ≃ irreducibleCharacters k G) := by
  have : NeZero (Nat.card G : k) := ⟨Invertible.ne_zero _⟩
  have := finite_of_natCast_card_ne_zero (Invertible.ne_zero (Nat.card G : k))
  obtain ⟨d, ρ, hirr, hind, -⟩ := exists_irreducible_family_conjClasses k G
  have := hirr
  have hmem : ∀ C, (ρ C).character ∈ irreducibleCharacters k G := fun C => ⟨d C, ρ C, hirr C, rfl⟩
  refine ⟨Equiv.ofBijective (fun C => ⟨(ρ C).character, hmem C⟩) ⟨fun C D hCD => ?_, ?_⟩⟩
  · refine (ClassFunction.linearIndependent_ofCharacter ρ hind).injective (Subtype.ext ?_)
    exact funext fun g => by
      simpa using congrFun (congrArg Subtype.val hCD) g
  · rintro ⟨-, n, σ, hσ, rfl⟩
    have := hσ
    obtain ⟨C, ⟨e⟩⟩ := ClassFunction.exists_nonempty_equiv ρ hind rfl σ
    exact ⟨C, Subtype.ext (_root_.Representation.char_iso e).symm⟩

instance : Finite (irreducibleCharacters k G) :=
  have := finite_of_natCast_card_ne_zero (Invertible.ne_zero (Nat.card G : k))
  Finite.of_equiv _ (nonempty_equiv_conjClasses_irreducibleCharacters k G).some

/-- **A group with invertible order has as many irreducible characters as conjugacy classes.** -/
theorem card_irreducibleCharacters :
    Nat.card (irreducibleCharacters k G) = Nat.card (ConjClasses G) :=
  (Nat.card_congr (nonempty_equiv_conjClasses_irreducibleCharacters k G).some).symm

end Set

section Enumeration

variable (k : Type u) (G : Type v) [Field k] [Group G] [IsAlgClosed k] [Invertible (Nat.card G : k)]

/-- An enumeration of the irreducible characters of `G` by `Fin (Nat.card (ConjClasses G))`, chosen
once and for all; it indexes the rows of the character table. -/
noncomputable def finEquivIrreducibleCharacters :
    Fin (Nat.card (ConjClasses G)) ≃ irreducibleCharacters k G :=
  (finCongr (card_irreducibleCharacters k G).symm).trans (Finite.equivFin _).symm

variable {G}

/-- The `i`-th irreducible character of `G`. -/
noncomputable def irreducibleCharacter (i : Fin (Nat.card (ConjClasses G))) : G → k :=
  finEquivIrreducibleCharacters k G i

/-- The `i`-th member of the chosen enumeration is the `i`-th irreducible character. -/
@[simp]
theorem coe_finEquivIrreducibleCharacters_apply (i : Fin (Nat.card (ConjClasses G))) :
    (finEquivIrreducibleCharacters k G i : G → k) = irreducibleCharacter k i :=
  (rfl)

/-- Every enumerated character is an irreducible character. -/
@[simp]
theorem irreducibleCharacter_mem (i : Fin (Nat.card (ConjClasses G))) :
    irreducibleCharacter k i ∈ irreducibleCharacters k G :=
  (finEquivIrreducibleCharacters k G i).property

/-- Distinct rows of the character table are distinct characters. -/
theorem irreducibleCharacter_injective :
    Function.Injective (irreducibleCharacter (G := G) k) :=
  Subtype.val_injective.comp (finEquivIrreducibleCharacters k G).injective

/-- **Every irreducible character is enumerated.** -/
theorem exists_irreducibleCharacter_eq {f : G → k} (hf : f ∈ irreducibleCharacters k G) :
    ∃ i, irreducibleCharacter k i = f :=
  ⟨(finEquivIrreducibleCharacters k G).symm ⟨f, hf⟩,
    congrArg Subtype.val ((finEquivIrreducibleCharacters k G).apply_symm_apply ⟨f, hf⟩)⟩

variable {k} in
/-- The enumerated irreducible characters exhaust the irreducible characters. -/
theorem range_irreducibleCharacter :
    Set.range (irreducibleCharacter (G := G) k) = irreducibleCharacters k G := by
  ext f
  exact ⟨by rintro ⟨i, rfl⟩; exact irreducibleCharacter_mem k i,
    fun hf => exists_irreducibleCharacter_eq k hf⟩

variable (G) in
/-- **The trivial character is a row of the character table**: some enumerated irreducible
character of `G` is the constant function `1`, the character of the trivial one-dimensional
representation. -/
theorem exists_irreducibleCharacter_eq_one :
    ∃ i, irreducibleCharacter k i = fun _ : G => (1 : k) :=
  exists_irreducibleCharacter_eq k one_mem_irreducibleCharacters

/-- **The degree of the `i`-th irreducible character**, the dimension of a representation affording
it. -/
noncomputable def characterDegree (i : Fin (Nat.card (ConjClasses G))) : ℕ :=
  (irreducibleCharacter_mem k i).choose

/-- An irreducible representation affording the `i`-th irreducible character. -/
noncomputable def irreducibleRepresentation (i : Fin (Nat.card (ConjClasses G))) :
    Representation k G (Fin (characterDegree k i) → k) :=
  (irreducibleCharacter_mem k i).choose_spec.choose

instance (i : Fin (Nat.card (ConjClasses G))) :
    (irreducibleRepresentation k i).IsIrreducible :=
  (irreducibleCharacter_mem k i).choose_spec.choose_spec.1

@[simp]
theorem character_irreducibleRepresentation (i : Fin (Nat.card (ConjClasses G))) :
    (irreducibleRepresentation k i).character = irreducibleCharacter k i :=
  (irreducibleCharacter_mem k i).choose_spec.choose_spec.2

/-- The representations affording the rows of the character table are pairwise inequivalent, their
characters being distinct. -/
theorem pairwise_isEmpty_equiv_irreducibleRepresentation :
    Pairwise fun i j : Fin (Nat.card (ConjClasses G)) =>
      IsEmpty ((irreducibleRepresentation k i).Equiv (irreducibleRepresentation k j)) :=
  fun i j hij =>
  ⟨fun e => hij (irreducibleCharacter_injective k (by
    rw [← character_irreducibleRepresentation k i, ← character_irreducibleRepresentation k j]
    exact _root_.Representation.char_iso e))⟩

/-- **An irreducible character takes its degree as its value at the identity.** -/
@[simp]
theorem irreducibleCharacter_one (i : Fin (Nat.card (ConjClasses G))) :
    irreducibleCharacter k i 1 = (characterDegree k i : k) := by
  rw [← character_irreducibleRepresentation k i, _root_.Representation.char_one]
  simp

/-- **The values of the irreducible characters lie in every subring of `k` containing the
`|G|`-th roots of unity**, each value being a sum of such roots. -/
theorem irreducibleCharacter_apply_mem_of_forall_pow_eq_one_mem {A : Subring k}
    (hA : ∀ x : k, x ^ Nat.card G = 1 → x ∈ A) (i : Fin (Nat.card (ConjClasses G))) (g : G) :
    irreducibleCharacter k i g ∈ A := by
  rw [← character_irreducibleRepresentation k i]
  exact Representation.char_mem_of_forall_pow_eq_one_mem _ (IsAlgClosed.splits _)
    (pow_card_eq_one' (x := g)) hA

/-- **The degree of an irreducible character is positive**: an irreducible representation is
nonzero, so the space affording the character has positive dimension. -/
theorem characterDegree_pos (i : Fin (Nat.card (ConjClasses G))) :
    0 < characterDegree k i := by
  simpa using Representation.IsIrreducible.finrank_pos
    (inferInstance : (irreducibleRepresentation k i).IsIrreducible)

/-- **The sum of the squares of the degrees is the order of the group**, as an identity of natural
numbers. The representations affording the enumerated characters are pairwise inequivalent
irreducibles, and there are as many of them as `G` has conjugacy classes, so they are the blocks of
a Wedderburn presentation of `k[G]` up to a relabelling of the blocks; the squares of the block
dimensions add up to the dimension `|G|` of `k[G]`. -/
theorem sum_characterDegree_sq_eq_card :
    ∑ i : Fin (Nat.card (ConjClasses G)), characterDegree k i ^ 2 = Nat.card G := by
  have := finite_of_natCast_card_ne_zero (Invertible.ne_zero (Nat.card G : k))
  simpa using sum_finrank_sq_eq_card (irreducibleRepresentation k)
    (pairwise_isEmpty_equiv_irreducibleRepresentation k) (by simp)

/-- **The degree of an irreducible character divides the order of the group.** -/
theorem characterDegree_dvd_card [CharZero k] (i : Fin (Nat.card (ConjClasses G))) :
    characterDegree k i ∣ Nat.card G := by
  simpa using (irreducibleRepresentation k i).finrank_dvd_card

end Enumeration

section Subsingleton

variable {k : Type u} [Field k]

/-- A group with one element has the trivial character as its only irreducible character, over any
field: every subspace is invariant, so an irreducible representation is a line. -/
@[simp]
theorem irreducibleCharacters_of_subsingleton {G : Type v} [Group G] [Subsingleton G] :
    irreducibleCharacters k G = {fun _ => 1} := by
  ext f
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · obtain ⟨n, ρ, hρ, rfl⟩ := mem_irreducibleCharacters_iff.mp hf
    have := hρ.nontrivial
    obtain ⟨v, hv⟩ := exists_ne (0 : Fin n → k)
    -- every vector is invariant, so the irreducible `ρ` is a line
    have hne : ρ.invariants ≠ ⊥ := (Submodule.ne_bot_iff _).2
      ⟨v, fun g => by rw [Subsingleton.elim g 1, map_one]; rfl, hv⟩
    have h1 := hρ.finrank_eq_one_of_invariants_ne_bot hne
    refine Set.mem_singleton_iff.mpr (funext fun g => ?_)
    rw [Subsingleton.elim g 1, Representation.char_one, h1, Nat.cast_one]
  · exact Set.mem_singleton_iff.mp hf ▸ one_mem_irreducibleCharacters

end Subsingleton

section Over

variable (k : Type u) {G : Type v} [Field k] [Group G]

/-- **The irreducible characters of `G` lying over `θ`**, `Irr(G | θ)`: for a function `θ` on a
subgroup `N`, the irreducible characters `ψ` of `G` with `∑ᶠ n ∈ N, ψ n θ n⁻¹ ≠ 0`. Over an
algebraically closed field of characteristic zero and for an irreducible character `θ` of a finite
`N`, the sum is `|N|` times the multiplicity of `θ` in the restriction of `ψ` to `N`, so these are
the irreducible characters whose restriction contains `θ`. -/
def irreducibleCharactersOver (N : Subgroup G) (θ : N → k) : Set (G → k) :=
  {ψ | ψ ∈ irreducibleCharacters k G ∧ ∑ᶠ n : N, ψ n * θ n⁻¹ ≠ 0}

variable {k}

/-- Membership in `TauCeti.irreducibleCharactersOver`, in the defining form with a `finsum` over
`N`, which needs no `Fintype N` instance. -/
theorem mem_irreducibleCharactersOver {N : Subgroup G} {θ : N → k} {ψ : G → k} :
    ψ ∈ irreducibleCharactersOver k N θ ↔
      ψ ∈ irreducibleCharacters k G ∧ ∑ᶠ n : N, ψ n * θ n⁻¹ ≠ 0 :=
  Iff.rfl

/-- Membership in `TauCeti.irreducibleCharactersOver`, with the defining sum over the finite
subgroup `N` written as a `Finset` sum. -/
@[simp]
theorem mem_irreducibleCharactersOver_iff_sum {N : Subgroup G} [Fintype N] {θ : N → k} {ψ : G → k} :
    ψ ∈ irreducibleCharactersOver k N θ ↔
      ψ ∈ irreducibleCharacters k G ∧ ∑ n : N, ψ n * θ n⁻¹ ≠ 0 := by
  rw [mem_irreducibleCharactersOver, finsum_eq_sum_of_fintype]

/-- The irreducible characters lying over `θ` are irreducible characters. -/
theorem irreducibleCharactersOver_subset {N : Subgroup G} (θ : N → k) :
    irreducibleCharactersOver k N θ ⊆ irreducibleCharacters k G :=
  fun _ hψ => hψ.1

/-- Over the trivial subgroup, every irreducible character lies over any function that does not
vanish at the identity. -/
theorem irreducibleCharactersOver_bot [CharZero k] {θ : (⊥ : Subgroup G) → k} (hθ : θ 1 ≠ 0) :
    irreducibleCharactersOver k ⊥ θ = irreducibleCharacters k G := by
  refine (irreducibleCharactersOver_subset θ).antisymm fun ψ h => ⟨h, ?_⟩
  rw [finsum_unique, Unique.default_eq 1]
  simpa using mul_ne_zero (apply_one_ne_zero_of_mem_irreducibleCharacters h) hθ

end Over

section Table

variable (k : Type u) (G : Type v) [Field k] [Group G] [IsAlgClosed k] [Invertible (Nat.card G : k)]

/-- **The character table of `G`**: the square matrix whose `(i, C)` entry is the value of the
`i`-th irreducible character of `G` on the conjugacy class `C`.

The rows are indexed by the chosen enumeration `TauCeti.finEquivIrreducibleCharacters` of the
irreducible characters and the columns by the conjugacy classes themselves, so the table is labelled
on its columns and determined up to a permutation of its rows. -/
noncomputable def characterTable :
    Matrix (Fin (Nat.card (ConjClasses G))) (ConjClasses G) k := fun i =>
  ClassFunction.toConjClasses (ClassFunction.ofCharacter (irreducibleRepresentation k i))

variable {k G}

/-- **The entries of the character table are the values of the irreducible characters**: the entry
in row `i` and the column of the class of `g` is the `i`-th irreducible character at `g`. -/
@[simp]
theorem characterTable_apply (i : Fin (Nat.card (ConjClasses G))) (g : G) :
    characterTable k G i (ConjClasses.mk g) = irreducibleCharacter k i g := by
  rw [characterTable, ClassFunction.toConjClasses_mk, ClassFunction.ofCharacter_apply,
    character_irreducibleRepresentation]

/-- The identity-class column of the character table lists the degrees of the irreducible
characters.

This is not a `simp` lemma: `TauCeti.characterTable_apply` already rewrites the left-hand side to
`TauCeti.irreducibleCharacter k i 1`, which `TauCeti.irreducibleCharacter_one` then evaluates. -/
theorem characterTable_one (i : Fin (Nat.card (ConjClasses G))) :
    characterTable k G i (ConjClasses.mk 1) = (characterDegree k i : k) := by
  rw [characterTable_apply, irreducibleCharacter_one]

variable (k G)

/-- **The rows of the character table are a basis of the class functions.** There are as many of
them as `G` has conjugacy classes, which is the dimension of the space of class functions, and they
are linearly independent. -/
noncomputable def basisIrreducibleCharacter :
    Module.Basis (Fin (Nat.card (ConjClasses G))) k (ClassFunction k G) :=
  have := finite_of_natCast_card_ne_zero (Invertible.ne_zero (Nat.card G : k))
  ClassFunction.basisOfIrreducibleCharacters (irreducibleRepresentation k)
    (pairwise_isEmpty_equiv_irreducibleRepresentation k) (by simp)

variable {k G}

@[simp]
theorem basisIrreducibleCharacter_apply (i : Fin (Nat.card (ConjClasses G))) (g : G) :
    (basisIrreducibleCharacter k G i).val g = irreducibleCharacter k i g := by
  have := finite_of_natCast_card_ne_zero (Invertible.ne_zero (Nat.card G : k))
  rw [basisIrreducibleCharacter, ClassFunction.basisOfIrreducibleCharacters_apply,
    ClassFunction.ofCharacter_apply, character_irreducibleRepresentation]

/-- **The irreducible characters are linearly independent** as functions `G → k`: they are the
basis `TauCeti.basisIrreducibleCharacter` of the class functions, read in the ambient space. -/
theorem linearIndependent_irreducibleCharacter :
    LinearIndependent k (irreducibleCharacter (G := G) k) := by
  have h : irreducibleCharacter (G := G) k =
      (ClassFunction k G).subtype ∘ basisIrreducibleCharacter k G := by
    ext i g
    simp
  rw [h]
  exact (basisIrreducibleCharacter k G).linearIndependent.map' _ (Submodule.ker_subtype _)

end Table

section RowOrthogonality

variable {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)]

/-- **The rows of the character table are orthonormal**, read as class functions: the character
pairing of the representations affording the `i`-th and `j`-th irreducible characters is `1` when
`i = j` and `0` otherwise. This is the orthonormality of the irreducible characters
(`TauCeti.ClassFunction.characterPairing_ofCharacter_self` and
`TauCeti.ClassFunction.characterPairing_ofCharacter_eq_zero`) transported along the enumeration. -/
@[simp]
theorem characterPairing_ofCharacter_irreducibleRepresentation_orthonormal
    (i j : Fin (Nat.card (ConjClasses G))) :
    ClassFunction.characterPairing (ClassFunction.ofCharacter (irreducibleRepresentation k i))
        (ClassFunction.ofCharacter (irreducibleRepresentation k j)) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl]
    exact ClassFunction.characterPairing_ofCharacter_self _
  · rw [ite_eq_right hij]
    exact ClassFunction.characterPairing_ofCharacter_eq_zero _ _
      (pairwise_isEmpty_equiv_irreducibleRepresentation k (Ne.symm hij))

/-- **First (row) orthogonality on the character table**: distinct rows pair to `0` and each row
pairs to `1` with itself. -/
theorem card_inv_mul_sum_characterTable_mul_characterTable_inv
    (i j : Fin (Nat.card (ConjClasses G))) :
    (Nat.card G : k)⁻¹ * ∑ g : G, characterTable k G i (ConjClasses.mk g) *
        characterTable k G j (ConjClasses.mk g⁻¹) = if i = j then 1 else 0 := by
  have hchar : ∀ (l : Fin (Nat.card (ConjClasses G))) (g : G),
      characterTable k G l (ConjClasses.mk g) =
        (irreducibleRepresentation k l).character g := by simp
  simp only [hchar, ← ClassFunction.characterPairing_ofCharacter]
  exact characterPairing_ofCharacter_irreducibleRepresentation_orthonormal i j

end RowOrthogonality

section Orthonormal

variable {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- Distinct irreducible characters are orthogonal: `∑ g, β(g) β'(g⁻¹) = 0`. The field need not be
algebraically closed, and `|G|` may be zero in it. When `|G|` is nonzero in `k`, `β` and `β'` are
the characters of inequivalent irreducible representations, which pair to `0` by Schur's lemma
(`TauCeti.ClassFunction.characterPairing_ofCharacter_eq_zero`); otherwise every such sum vanishes
(`Representation.sum_character_mul_character_inv_eq_zero_of_natCard_eq_zero`). -/
theorem sum_mul_inv_eq_zero_of_mem_irreducibleCharacters {β β' : G → k}
    (hβ : β ∈ irreducibleCharacters k G) (hβ' : β' ∈ irreducibleCharacters k G) (h : β ≠ β') :
    ∑ g, β g * β' g⁻¹ = 0 := by
  obtain ⟨_, ρ, hρ, rfl⟩ := mem_irreducibleCharacters_iff.mp hβ
  obtain ⟨_, ρ', hρ', rfl⟩ := mem_irreducibleCharacters_iff.mp hβ'
  by_cases hG : (Nat.card G : k) = 0
  · exact ρ.sum_character_mul_character_inv_eq_zero_of_natCard_eq_zero ρ' hG
  have : NeZero (Nat.card G : k) := ⟨hG⟩
  have key := ClassFunction.characterPairing_ofCharacter_eq_zero ρ ρ'
    ⟨fun e => h (Representation.char_iso e).symm⟩
  rw [ClassFunction.characterPairing_ofCharacter] at key
  exact (mul_eq_zero.mp key).resolve_left (inv_ne_zero hG)

/-- **Row orthogonality for the set of irreducible characters**, in a form free of division: over
an algebraically closed field, the sum `∑ g, β(g) β'(g⁻¹)` is `|G|` when `β = β'` and `0`
otherwise. When `|G|` is zero in `k` both values are `0`. -/
theorem sum_mul_inv_of_mem_irreducibleCharacters [DecidableEq (G → k)] {β β' : G → k}
    (hβ : β ∈ irreducibleCharacters k G) (hβ' : β' ∈ irreducibleCharacters k G) :
    ∑ g, β g * β' g⁻¹ = if β = β' then (Nat.card G : k) else 0 := by
  obtain ⟨n, ρ, hρ, rfl⟩ := mem_irreducibleCharacters_iff.mp hβ
  by_cases hG : (Nat.card G : k) = 0
  · obtain ⟨_, ρ', -, rfl⟩ := mem_irreducibleCharacters_iff.mp hβ'
    rw [hG, ite_self]
    exact ρ.sum_character_mul_character_inv_eq_zero_of_natCard_eq_zero ρ' hG
  let : Invertible (Nat.card G : k) := invertibleOfNonzero hG
  split_ifs with h
  · rw [← h]
    have key := Representation.char_orthonormal ρ ρ
    rw [ite_eq_left ⟨Representation.Equiv.refl ρ⟩] at key
    field_simp at key
    simpa using key
  · exact sum_mul_inv_eq_zero_of_mem_irreducibleCharacters hβ hβ' h

/-- Over an algebraically closed field, an irreducible character has unnormalized self-pairing
`∑ g, β(g) β(g⁻¹) = |G|` (which is `0` when `|G|` is zero in `k`). -/
theorem sum_mul_inv_self_of_mem_irreducibleCharacters {β : G → k}
    (hβ : β ∈ irreducibleCharacters k G) : ∑ g, β g * β g⁻¹ = Nat.card G := by
  classical
  simpa using sum_mul_inv_of_mem_irreducibleCharacters hβ hβ

end Orthonormal

section Restriction

variable {k : Type u} {G : Type v} [Field k] [Group G] [IsAlgClosed k]

/-- An irreducible character of `G` whose restriction to a finite subgroup `N` is an irreducible
character `θ` of `N` lies over `θ`. Only `|N| ≠ 0` in `k` is needed. -/
theorem mem_irreducibleCharactersOver_of_restrict_eq {N : Subgroup G} [Finite N]
    [NeZero (Nat.card N : k)] {θ : N → k}
    {ψ : G → k} (hψ : ψ ∈ irreducibleCharacters k G) (hθ : θ ∈ irreducibleCharacters k N)
    (h : ∀ n : N, ψ n = θ n) : ψ ∈ irreducibleCharactersOver k N θ := by
  have := Fintype.ofFinite N
  refine mem_irreducibleCharactersOver_iff_sum.mpr ⟨hψ, ?_⟩
  simp only [h, sum_mul_inv_self_of_mem_irreducibleCharacters hθ]
  exact NeZero.ne _

end Restriction

section Nonconstant

variable {k : Type u} {G : Type v} [Field k] [Group G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)]

/-- **A nontrivial irreducible character is not constant.** Over an algebraically closed field in
which `|G|` is invertible, if `i₀` indexes the trivial character, the constant function `1`, and
`i ≠ i₀`, then the `i`-th irreducible character takes somewhere a value other than its degree,
which is its value `χᵢ(1)` at the identity (`TauCeti.irreducibleCharacter_one`).
`TauCeti.exists_irreducibleCharacter_eq_one` supplies such an index `i₀`. -/
theorem exists_irreducibleCharacter_ne_characterDegree {i₀ i : Fin (Nat.card (ConjClasses G))}
    (hi₀ : irreducibleCharacter k i₀ = fun _ : G => (1 : k)) (hne : i ≠ i₀) :
    ∃ g : G, irreducibleCharacter k i g ≠ characterDegree k i := by
  by_contra! htriv
  -- `χᵢ = χᵢ(1) • χᵢ₀` would be a linear relation between distinct irreducible characters
  exact hne <| linearIndependent_irreducibleCharacter.eq_of_smul_apply_eq_smul_apply 1
    (characterDegree k i : k) i i₀ one_ne_zero (by ext g; simp [hi₀, htriv g])

end Nonconstant

section ColumnOrthogonality

variable {k : Type u} {G : Type v} [Field k] [Group G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)]

open scoped Classical in
/-- **Second (column) orthogonality on the character table**, in a form free of division: the
columns at `g` and at `h`, weighted by the size of the class of `g`, sum to `|G|` when `g` and `h`
are conjugate and to `0` otherwise. -/
theorem card_conjClass_mul_sum_characterTable_mul_characterTable_inv (g h : G) :
    (Nat.card (ConjClasses.mk g).carrier : k) *
        ∑ i : Fin (Nat.card (ConjClasses G)),
          characterTable k G i (ConjClasses.mk g) * characterTable k G i (ConjClasses.mk h⁻¹) =
      if IsConj g h then (Nat.card G : k) else 0 := by
  have := finite_of_natCast_card_ne_zero (Invertible.ne_zero (Nat.card G : k))
  let _ : Fintype G := Fintype.ofFinite G
  simpa using ClassFunction.card_conjClass_mul_sum_char_mul_char_inv
    (fun i : Fin (Nat.card (ConjClasses G)) => irreducibleRepresentation k i)
    (pairwise_isEmpty_equiv_irreducibleRepresentation k) (by simp) g h

open scoped Classical in
/-- **Second (column) orthogonality on the character table**, in its quotient form. -/
theorem sum_characterTable_mul_characterTable_inv (g h : G) :
    ∑ i : Fin (Nat.card (ConjClasses G)),
        characterTable k G i (ConjClasses.mk g) * characterTable k G i (ConjClasses.mk h⁻¹) =
      if IsConj g h then (Nat.card G : k) / Nat.card (ConjClasses.mk g).carrier else 0 := by
  have := finite_of_natCast_card_ne_zero (Invertible.ne_zero (Nat.card G : k))
  let _ : Fintype G := Fintype.ofFinite G
  simpa using ClassFunction.sum_char_mul_char_inv
    (fun i : Fin (Nat.card (ConjClasses G)) => irreducibleRepresentation k i)
    (pairwise_isEmpty_equiv_irreducibleRepresentation k) (by simp) g h

/-- **Second (column) orthogonality at a class and its inverse**, indexed by the conjugacy classes
themselves: the column at `C` against the column at `C⁻¹`, weighted by the class size `|C|`,
is `|G|`.

This is `TauCeti.card_conjClass_mul_sum_characterTable_mul_characterTable_inv` at a pair of
conjugate elements, restated without a choice of representative. -/
theorem card_carrier_mul_sum_characterTable_mul_characterTable_inv (C : ConjClasses G) :
    (Nat.card C.carrier : k) *
        ∑ i : Fin (Nat.card (ConjClasses G)),
          characterTable k G i C * characterTable k G i C⁻¹ = (Nat.card G : k) := by
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
  rw [ConjClasses.inv_mk]
  exact (card_conjClass_mul_sum_characterTable_mul_characterTable_inv g g).trans
    (ite_eq_left (IsConj.refl g))

/-- **Second (column) orthogonality at two distinct classes**, indexed by the conjugacy classes
themselves: for `C ≠ D` the column at `C` pairs with the column at `D⁻¹` to `0`.

The weight `|C|` of
`TauCeti.card_carrier_mul_sum_characterTable_mul_characterTable_inv` cancels here, being nonzero
in `k`: it divides the invertible `|G|`. -/
theorem sum_characterTable_mul_characterTable_inv_of_ne {C D : ConjClasses G} (h : C ≠ D) :
    ∑ i : Fin (Nat.card (ConjClasses G)),
        characterTable k G i C * characterTable k G i D⁻¹ = 0 := by
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
  obtain ⟨x, rfl⟩ := ConjClasses.exists_rep D
  have hconj : ¬ IsConj g x := fun hc => h (ConjClasses.mk_eq_mk_iff_isConj.2 hc)
  have hzero := (card_conjClass_mul_sum_characterTable_mul_characterTable_inv (k := k) g x).trans
    (ite_eq_right hconj)
  rw [ConjClasses.inv_mk]
  exact (mul_eq_zero.1 hzero).resolve_left
    (ConjClasses.card_carrier_cast_ne_zero _ (Invertible.ne_zero (Nat.card G : k)))

end ColumnOrthogonality

section Complex

variable {G : Type v} [Group G] [Invertible (Nat.card G : ℂ)]

/-- **Complex conjugation of an irreducible character value inverts the group element.** -/
@[simp]
theorem conj_irreducibleCharacter (i : Fin (Nat.card (ConjClasses G))) (g : G) :
    (starRingEnd ℂ) (irreducibleCharacter ℂ i g) = irreducibleCharacter ℂ i g⁻¹ := by
  have := finite_of_natCast_card_ne_zero (Invertible.ne_zero (Nat.card G : ℂ))
  rw [← character_irreducibleRepresentation ℂ i]
  exact Representation.conj_char _ g

/-- Complex conjugation of a character-table entry inverts the class.

This is not a `simp` lemma: `TauCeti.characterTable_apply` already rewrites the left-hand side to
`(starRingEnd ℂ) (TauCeti.irreducibleCharacter ℂ i g)`, which `TauCeti.conj_irreducibleCharacter`
then normalizes. -/
theorem conj_characterTable_apply (i : Fin (Nat.card (ConjClasses G))) (g : G) :
    (starRingEnd ℂ) (characterTable ℂ G i (ConjClasses.mk g)) =
      characterTable ℂ G i (ConjClasses.mk g⁻¹) := by
  rw [characterTable_apply, characterTable_apply, conj_irreducibleCharacter]

/-- **Complex conjugation of a character-table entry inverts the class**, in the class-indexed
form: `TauCeti.conj_characterTable_apply` is the same statement about a representative. -/
@[simp]
theorem conj_characterTable (i : Fin (Nat.card (ConjClasses G))) (C : ConjClasses G) :
    (starRingEnd ℂ) (characterTable ℂ G i C) = characterTable ℂ G i C⁻¹ := by
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
  rw [ConjClasses.inv_mk, conj_characterTable_apply]

/-- **First (row) orthogonality over `ℂ`**, in its Hermitian form: the rows of the complex character
table are orthonormal for the Hermitian inner product on class functions. -/
theorem card_inv_mul_sum_characterTable_mul_conj [Fintype G]
    (i j : Fin (Nat.card (ConjClasses G))) :
    (Nat.card G : ℂ)⁻¹ * ∑ g : G, characterTable ℂ G i (ConjClasses.mk g) *
        (starRingEnd ℂ) (characterTable ℂ G j (ConjClasses.mk g)) = if i = j then 1 else 0 := by
  simp only [conj_characterTable_apply]
  exact card_inv_mul_sum_characterTable_mul_characterTable_inv i j

/-- **First (row) orthogonality over `ℂ`, summed one column at a time**: the Hermitian pairing of
two rows of the complex character table, collected over the conjugacy classes with the class sizes
as weights. This is the shape in which `TauCeti.IsCharacterTableSpec` asks for row orthonormality;
`TauCeti.card_inv_mul_sum_characterTable_mul_conj` is the same statement summed over the group.

The enumeration of the conjugacy classes is an explicit `Fintype` argument rather than a classical
one, so that the statement is about whichever enumeration the caller has in hand; a caller with
`[DecidableEq G]` has one, and a classical instance would not be defeq to it. -/
theorem card_inv_mul_sum_card_conjClass_mul_characterTable_mul_conj [Fintype (ConjClasses G)]
    (i j : Fin (Nat.card (ConjClasses G))) :
    (Nat.card G : ℂ)⁻¹ * ∑ C : ConjClasses G, (Nat.card C.carrier : ℂ) *
        characterTable ℂ G i C * (starRingEnd ℂ) (characterTable ℂ G j C) =
      if i = j then 1 else 0 := by
  have := finite_of_natCast_card_ne_zero (Invertible.ne_zero (Nat.card G : ℂ))
  let _ : Fintype G := Fintype.ofFinite G
  rw [← card_inv_mul_sum_characterTable_mul_conj i j]
  congr 1
  have hsum := ClassFunction.sum_eq_sum_conjClasses (ClassFunction.ofConjClasses
    (fun C => characterTable ℂ G i C * (starRingEnd ℂ) (characterTable ℂ G j C)))
  have hval : ∀ C : ConjClasses G, ClassFunction.toConjClasses (ClassFunction.ofConjClasses
      (fun C => characterTable ℂ G i C * (starRingEnd ℂ) (characterTable ℂ G j C))) C =
      characterTable ℂ G i C * (starRingEnd ℂ) (characterTable ℂ G j C) := by
    rintro C
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
    rw [ClassFunction.toConjClasses_mk, ClassFunction.ofConjClasses_apply]
  simp only [ClassFunction.ofConjClasses_apply, hval] at hsum
  rw [hsum]
  exact Finset.sum_congr rfl fun C _ => mul_assoc _ _ _

open scoped Classical in
/-- **Second (column) orthogonality over `ℂ`**, in its Hermitian form: two columns of the complex
character table are orthogonal unless they are the same class, in which case they pair to
`|G| / |C|`. -/
theorem sum_characterTable_mul_conj (C C' : ConjClasses G) :
    ∑ i : Fin (Nat.card (ConjClasses G)),
        characterTable ℂ G i C * (starRingEnd ℂ) (characterTable ℂ G i C') =
      if C = C' then (Nat.card G : ℂ) / Nat.card C.carrier else 0 := by
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
  obtain ⟨h, rfl⟩ := ConjClasses.exists_rep C'
  simp only [conj_characterTable_apply]
  rw [sum_characterTable_mul_characterTable_inv]
  exact if_congr ConjClasses.mk_eq_mk_iff_isConj.symm rfl rfl

end Complex

end TauCeti
