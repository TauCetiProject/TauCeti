/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import TauCeti.Algebra.Group.Conj
public import TauCeti.RepresentationTheory.CharacterTable.Table
import TauCeti.LinearAlgebra.Trace.Basic
import TauCeti.RepresentationTheory.CharacterTable.Determined
import TauCeti.RepresentationTheory.Irreducible
import TauCeti.RepresentationTheory.Subrepresentation

/-!
# Automorphisms of a group acting on its irreducible characters

An automorphism `σ` of a group `G` permutes the irreducible characters of `G`, by
`(σ • χ)(g) = χ(σ⁻¹ g)`, and it permutes the conjugacy classes of `G`, by mapping representatives
(`TauCeti.instMulActionMulAutConjClasses`). This file proves **Brauer's permutation lemma**: over
an algebraically closed field of characteristic zero, for a finite group `G`, the two permutations
have the same number of fixed points.

A noncyclic group of automorphisms can fix different numbers of characters and of classes, but
Burnside's lemma turns the lemma into an equality of orbit counts for every group of automorphisms.
For a cyclic group acting on `G`, a character, respectively a class, is invariant exactly when it
is fixed by a generator, so there are as many invariant characters as invariant classes. These
counts are the input from character theory to the study of coprime actions on characters, where
the invariant classes are compared with the classes of the fixed-point subgroup.

## Main definitions and results

* `MonoidHom.comp_mem_irreducibleCharacters` and `MulEquiv.comp_mem_irreducibleCharacters_iff`:
  precomposing with a surjective homomorphism, respectively an isomorphism, preserves irreducible
  characters.
* `Representation.isIrreducible_of_character_comp_mem_irreducibleCharacters`: over a field of
  characteristic zero, a representation whose restriction to a finite group has an irreducible
  character is irreducible.
* `TauCeti.instMulActionMulAutIrreducibleCharacters`: the action of `MulAut G` on the irreducible
  characters, computed by `MulAut.smul_irreducibleCharacters_apply`; its fixed points are described
  by `TauCeti.mem_fixedBy_irreducibleCharacters_iff`.
* `TauCeti.natCard_fixedBy_irreducibleCharacters_eq_natCard_fixedBy_conjClasses`: **Brauer's
  permutation lemma**, an automorphism fixes as many irreducible characters as conjugacy classes.
* `TauCeti.natCard_orbits_irreducibleCharacters_eq_natCard_orbits_conjClasses`: a group of
  automorphisms has as many orbits on the irreducible characters as on the conjugacy classes.
* `TauCeti.natCard_invariant_irreducibleCharacters_eq_natCard_invariant_conjClasses_of_isCyclic`:
  for a cyclic group acting on `G` by automorphisms, there are as many invariant irreducible
  characters as invariant conjugacy classes.

## Implementation notes

The permutation lemma is proved with a trace rather than with the character table. The linear map
`f ↦ f ∘ σ⁻¹` on class functions sends the basis of irreducible characters to itself, permuted by
`σ`, and likewise the basis of class indicators; by
`LinearMap.trace_eq_natCard_of_apply_basis_eq` its trace counts the fixed points of either
permutation, and characteristic zero turns the equality in `k` into one of natural numbers.

## References

* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Theorem 6.32 and Corollary 6.33.
* G. Glauberman, *Correspondences of characters for relatively prime operator groups*, Canad. J.
  Math. **20** (1968), 1465–1488, proof of Theorem 3.
-/

public section

namespace TauCeti

universe u v w

variable {k : Type u} [Field k] {G : Type v} [Group G]

/-- **Inflation along a surjection preserves irreducible characters.** If `χ` is an irreducible
character of `G` and `f : H →* G` is surjective, then `χ ∘ f` is an irreducible character of `H`,
the character of the composite representation. -/
theorem _root_.MonoidHom.comp_mem_irreducibleCharacters {H : Type w} [Group H] (f : H →* G)
    (hf : Function.Surjective f) {χ : G → k} (hχ : χ ∈ irreducibleCharacters k G) :
    χ ∘ f ∈ irreducibleCharacters k H := by
  obtain ⟨n, ρ, hρ, rfl⟩ := mem_irreducibleCharacters_iff.1 hχ
  exact mem_irreducibleCharacters_iff.2
    ⟨n, ρ.comp f, (f.isIrreducible_comp_surjective_iff hf ρ).2 hρ, rfl⟩

/-- **Precomposing with an isomorphism preserves irreducible characters**, in both directions. -/
@[simp]
theorem _root_.MulEquiv.comp_mem_irreducibleCharacters_iff {H : Type w} [Group H] (e : H ≃* G)
    {χ : G → k} : χ ∘ e ∈ irreducibleCharacters k H ↔ χ ∈ irreducibleCharacters k G := by
  refine ⟨fun h ↦ ?_, (e : H →* G).comp_mem_irreducibleCharacters e.surjective⟩
  simpa [Function.comp_assoc] using
    e.symm.toMonoidHom.comp_mem_irreducibleCharacters e.symm.surjective h

/-- A finite-dimensional representation of `G` over a field of characteristic zero whose
restriction along `f : H →* G`, for a finite group `H`, has an irreducible character is
irreducible. -/
theorem _root_.Representation.isIrreducible_of_character_comp_mem_irreducibleCharacters
    [CharZero k] {H : Type w} [Group H] [Finite H] {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k G V) (f : H →* G)
    (h : ρ.character ∘ f ∈ irreducibleCharacters k H) : ρ.IsIrreducible := by
  obtain ⟨m, ρ₀, hρ₀, hc⟩ := mem_irreducibleCharacters_iff.1 h
  obtain ⟨E⟩ := Representation.nonempty_equiv_of_character_eq ρ₀ (ρ.comp f) hc
  have := E.isIrreducible hρ₀
  exact Representation.IsIrreducible.of_comp f

/-- **Automorphisms permute the irreducible characters**: an automorphism `σ` sends `χ` to
`g ↦ χ (σ⁻¹ g)`, the character of the representation precomposed with `σ⁻¹`. The inverse makes this
a left action, the same convention as `arrowAction`. -/
instance instMulActionMulAutIrreducibleCharacters :
    MulAction (MulAut G) (irreducibleCharacters k G) where
  smul σ χ := ⟨fun g ↦ (χ : G → k) (σ⁻¹ g),
    (σ⁻¹ : MulAut G).comp_mem_irreducibleCharacters_iff.2 χ.property⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The action of an automorphism on irreducible characters, evaluated at a group element. -/
@[simp]
theorem _root_.MulAut.smul_irreducibleCharacters_apply (σ : MulAut G)
    (χ : irreducibleCharacters k G) (g : G) :
    ((σ • χ : irreducibleCharacters k G) : G → k) g = (χ : G → k) (σ⁻¹ g) :=
  (rfl)

open MulAction

/-- An automorphism `σ` fixes an irreducible character exactly when the character is constant
along `σ`. -/
theorem mem_fixedBy_irreducibleCharacters_iff (σ : MulAut G) (χ : irreducibleCharacters k G) :
    χ ∈ fixedBy (irreducibleCharacters k G) σ ↔ (χ : G → k) ∘ σ = χ := by
  rw [mem_fixedBy, eq_comm, ← inv_smul_eq_iff, Subtype.ext_iff, funext_iff, funext_iff]
  simp

section PermutationLemma

variable [IsAlgClosed k] [CharZero k] [Finite G]

/-- **Brauer's permutation lemma.** Over an algebraically closed field of characteristic zero, an
automorphism `σ` of a finite group fixes as many irreducible characters as conjugacy classes. A
character `χ` is fixed exactly when `χ ∘ σ = χ` (`TauCeti.mem_fixedBy_irreducibleCharacters_iff`),
and a class `K` exactly when `σ` maps it onto itself. -/
theorem natCard_fixedBy_irreducibleCharacters_eq_natCard_fixedBy_conjClasses (σ : MulAut G) :
    Nat.card (fixedBy (irreducibleCharacters k G) σ) = Nat.card (fixedBy (ConjClasses G) σ) := by
  classical
  have : Invertible (Nat.card G : k) := invertibleOfNonzero (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  -- The linear map `f ↦ f ∘ σ⁻¹` on class functions, read in two bases.
  let T := ClassFunction.comap (k := k) (σ⁻¹ : MulAut G).toMonoidHom
  -- In the basis of irreducible characters, it permutes the basis vectors by `χ ↦ σ • χ`.
  let b₁ := (basisIrreducibleCharacter k G).reindex (finEquivIrreducibleCharacters k G)
  have hb₁ (χ : irreducibleCharacters k G) (g : G) : (b₁ χ).val g = (χ : G → k) g := by
    rw [Module.Basis.reindex_apply, basisIrreducibleCharacter_apply,
      ← coe_finEquivIrreducibleCharacters_apply, Equiv.apply_symm_apply]
  have h₁ (χ : irreducibleCharacters k G) : T (b₁ χ) = b₁ (σ • χ) := by
    ext g
    simp [T, hb₁]
  -- In the basis of class indicators, it permutes the basis vectors by `K ↦ σ • K`.
  let b₂ := (Pi.basisFun k (ConjClasses G)).map ClassFunction.equivConjClasses.symm
  have h₂ (K : ConjClasses G) : T (b₂ K) = b₂ (σ • K) := by
    ext g
    simp only [T, b₂, Module.Basis.map_apply, Pi.basisFun_apply, ClassFunction.comap_apply,
      ClassFunction.equivConjClasses_symm_apply, ClassFunction.ofConjClasses_apply,
      MulEquiv.coe_toMonoidHom, ← MulAut.smul_conjClasses_mk, Pi.single_apply, inv_smul_eq_iff]
  have h := (LinearMap.trace_eq_natCard_of_apply_basis_eq b₁ h₁).symm.trans
    (LinearMap.trace_eq_natCard_of_apply_basis_eq b₂ h₂)
  exact Nat.cast_injective h

/-- **A group of automorphisms has as many orbits on the irreducible characters as on the conjugacy
classes**, over an algebraically closed field of characteristic zero. This follows from Brauer's
permutation lemma by Burnside's lemma. -/
theorem natCard_orbits_irreducibleCharacters_eq_natCard_orbits_conjClasses
    (A : Subgroup (MulAut G)) :
    Nat.card (orbitRel.Quotient A (irreducibleCharacters k G)) =
      Nat.card (orbitRel.Quotient A (ConjClasses G)) := by
  classical
  have : Fintype A := Fintype.ofFinite A
  have : Fintype (irreducibleCharacters k G) := Fintype.ofFinite _
  have : Fintype (ConjClasses G) := Fintype.ofFinite _
  have h₁ := sum_card_fixedBy_eq_card_orbits_mul_card_group A (irreducibleCharacters k G)
  have h₂ := sum_card_fixedBy_eq_card_orbits_mul_card_group A (ConjClasses G)
  -- An element of `A` fixes as many characters as classes, acting as an automorphism.
  have hsum : ∑ a : A, Fintype.card (fixedBy (irreducibleCharacters k G) a) =
      ∑ a : A, Fintype.card (fixedBy (ConjClasses G) a) := by
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
    -- Unfold `fixedBy` so that `Subgroup.smul_def` exposes the action of `a` as an automorphism.
    simp only [fixedBy, Subgroup.smul_def]
    exact natCard_fixedBy_irreducibleCharacters_eq_natCard_fixedBy_conjClasses (k := k)
      (a : MulAut G)
  rw [hsum, h₂] at h₁
  simp only [Fintype.card_eq_nat_card] at h₁
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h₁.symm

/-- **A cyclic group acting on `G` by automorphisms has as many invariant irreducible characters as
invariant conjugacy classes**, over an algebraically closed field of characteristic zero. A
character, respectively a class, is invariant under the group exactly when it is fixed by a
generator, so this is Brauer's permutation lemma for the automorphism that generator induces. The
cyclic group need not be finite. -/
theorem natCard_invariant_irreducibleCharacters_eq_natCard_invariant_conjClasses_of_isCyclic
    {A : Type*} [Group A] [IsCyclic A] [MulDistribMulAction A G] :
    Nat.card {χ : irreducibleCharacters k G //
        ∀ (a : A) (g : G), (χ : G → k) (a • g) = (χ : G → k) g} =
      Nat.card {K : ConjClasses G // ∀ a : A, MulDistribMulAction.toMulAut A G a • K = K} := by
  obtain ⟨a₀, ha₀⟩ := IsCyclic.exists_generator (α := A)
  let φ := MulDistribMulAction.toMulAut A G
  -- A subgroup of `MulAut G` contains the image of `A` once it contains that of the generator.
  have hgen (S : Subgroup (MulAut G)) : (∀ a, φ a ∈ S) ↔ φ a₀ ∈ S :=
    ⟨fun h ↦ h a₀, fun h a ↦
      Subgroup.mem_comap.1 (Subgroup.zpowers_le.2 (Subgroup.mem_comap.2 h) (ha₀ a))⟩
  -- So both sides are the points fixed by the automorphism `φ a₀`, applying `hgen` to stabilizers.
  have hχ (χ : irreducibleCharacters k G) :
      (∀ (a : A) (g : G), (χ : G → k) (a • g) = (χ : G → k) g) ↔ χ ∈ fixedBy _ (φ a₀) := by
    have h := hgen (stabilizer (MulAut G) χ)
    simp only [mem_stabilizer_iff, ← mem_fixedBy, mem_fixedBy_irreducibleCharacters_iff,
      funext_iff] at h
    rw [mem_fixedBy_irreducibleCharacters_iff, funext_iff, ← h]
    simp [φ]
  have hK (K : ConjClasses G) : (∀ a : A, φ a • K = K) ↔ K ∈ fixedBy _ (φ a₀) := by
    simpa only [mem_stabilizer_iff, mem_fixedBy] using hgen (stabilizer (MulAut G) K)
  rw [Nat.card_congr (Equiv.subtypeEquivRight hχ), Nat.card_congr (Equiv.subtypeEquivRight hK)]
  exact natCard_fixedBy_irreducibleCharacters_eq_natCard_fixedBy_conjClasses (φ a₀)

end PermutationLemma

end TauCeti
