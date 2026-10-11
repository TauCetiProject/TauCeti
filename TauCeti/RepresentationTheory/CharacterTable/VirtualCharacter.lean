/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Span.IntegralDescent
public import TauCeti.RepresentationTheory.CharacterTable.Table
public import TauCeti.RepresentationTheory.FDRep
import Mathlib.RepresentationTheory.Maschke
import TauCeti.RepresentationTheory.Intertwining
import TauCeti.RepresentationTheory.Irreducible

/-!
# The virtual-character lattice

The characters of the finite-dimensional representations of a monoid `G` over a field `k` are
closed under addition, the character of a direct sum being the sum of the characters, but in
general not under negation: over `ℂ` a character takes the positive value `dim V` at `1`. The
additive subgroup of `G → k` they generate, `TauCeti.virtualCharacters k G`, is the
**virtual-character lattice**: its elements are the *virtual characters* of `G`, the differences of
genuine characters.

It is an additive subgroup rather than a subring, but it is closed under the pointwise product
(`TauCeti.mul_mem_virtualCharacters`), because the pointwise product of two characters is the
character of the tensor product, and it contains the constant function `1`, the character of the
trivial representation.

Over an algebraically closed field in which `|G|` is invertible, and for `G` a finite group, the
lattice is pinned down completely: it is the `ℤ`-span of the finitely many irreducible characters
(`TauCeti.virtualCharacters_eq_closure_irreducibleCharacters`), which are a basis of the class
functions. Every character is even a `ℕ`-combination of them, because its coefficient against `χᵢ`
is the dimension of an intertwiner space. Consequently the character pairing takes *integer* values
on the lattice: pairing two integer combinations of the irreducible characters gives the dot
product of their integer coefficients. That integrality is what makes the classical norm-`1` test
work — a virtual character of norm `1` is, up to sign, an irreducible character.

Over a field of characteristic zero that is not algebraically closed the irreducible characters
need not be orthonormal, but the norm-`1` test survives in the form that realizes representations
over a smaller field: writing a virtual character as `χ_A - χ_B` and cancelling the summands that
`A` and `B` share, a virtual character of norm `1` and natural degree is the character of a simple
representation whose endomorphisms are the scalars
(`TauCeti.exists_simple_character_eq_of_characterPairing_self_eq_one`). This is how an irreducible
complex character that is an integer combination of characters of representations over a subfield
`K` of `ℂ` is seen to be the character of a representation over `K`.

## Main definitions

* `TauCeti.virtualCharacters`: the virtual-character lattice of `G` over `k`.

## Main results

* `TauCeti.mem_virtualCharacters_iff_exists_eq_character_sub_character`: the virtual characters
  are exactly the differences of two characters, with `TauCeti.exists_eq_character_sub_character`
  its forward direction.
* `TauCeti.mul_mem_virtualCharacters` and `TauCeti.one_mem_virtualCharacters`: the lattice is
  closed under the pointwise product and contains the constant `1`.
* `TauCeti.comp_mem_virtualCharacters`: pulling back along a monoid homomorphism preserves virtual
  characters.
* `TauCeti.virtualCharacters_le_classFunction`: a virtual character is a class function, and
  `TauCeti.conj_apply_of_mem_virtualCharacters`: over `ℂ` inverting the argument conjugates the
  value, `conj (f g) = f g⁻¹`.
* `TauCeti.character_eq_sum_nsmul_irreducibleCharacter`: **a character is the sum of the
  irreducible characters weighted by their multiplicities**, and
  `TauCeti.virtualCharacters_eq_closure_irreducibleCharacters`: **the lattice is the `ℤ`-span of
  the irreducible characters**, with `TauCeti.mem_virtualCharacters_iff` its elementwise form.
* `TauCeti.mem_of_mem_span_of_mem_virtualCharacters`: **a virtual character that is a
  `ℤ[ζ]`-combination of elements of a subgroup of the lattice is an integer combination of them**,
  and more generally for any subring of `k` retracting additively onto `ℤ`.
* `TauCeti.characterPairing_eq_intCast_sum` and `TauCeti.exists_characterPairing_eq_intCast`: **the
  character pairing is integer-valued on the lattice**, computed by the dot product of the integer
  coefficients.
* `TauCeti.exists_eq_irreducibleCharacter_or_neg`: **a virtual character of norm `1` is `±` an
  irreducible character**, and `TauCeti.mem_irreducibleCharacters_of_characterPairing_self_eq_one`
  fixes the sign when its degree is a natural number.
* `TauCeti.exists_simple_character_eq_of_characterPairing_self_eq_one`: **over any field of
  characteristic zero, a virtual character of norm `1` and natural degree is the character of a
  simple representation whose endomorphisms are the scalars**.
* `TauCeti.natCard_nsmul_mem_span_irreducibleCharacters`: **`|G|` times a class function with
  values in a subring `A` containing the character values is an `A`-combination of the irreducible
  characters**.

## Implementation notes

The lattice is generated by the characters of the bundled representations `FDRep k G`, which makes
closure under the pointwise product immediate from `FDRep.char_tensor`. The set
`TauCeti.irreducibleCharacters`, by contrast, is cut out by representations on the coordinate
spaces `Fin n → k`; `FDRep.of` mediates between the two, and nothing is lost, since the character
of an irreducible representation on an arbitrary finite-dimensional space already lies in
`TauCeti.irreducibleCharacters`.

Following the roadmap, the lattice is an `AddSubgroup (G → k)` and not a `Subring (G → k)`: the
additive structure is what the integrality arguments downstream use, and closure under the pointwise
product is recorded as the lemma `TauCeti.mul_mem_virtualCharacters` rather than built into the
interface. The coefficients in `TauCeti.mem_virtualCharacters_iff` are genuine integers, the scalars
`(c i : k)` appearing only because the ambient module is a `k`-module; they are determined by the
element only in characteristic zero, since in positive characteristic the cast `ℤ → k` is not
injective.

## References

This is the virtual-character-lattice item of Layer 3 of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md)
and the `virtualCharacters` target of Layer 6 of the
[induction and restriction roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md).
See I. M. Isaacs, *Character Theory of Finite Groups* (1976), Chapter 2 and Lemma 4.7, or
J.-P. Serre, *Linear Representations of Finite Groups* (1977), Sections 2.5 and 9. The norm-`1`
test over an arbitrary field of characteristic zero is the argument of Serre, Section 12.3
(realizability over cyclotomic fields), and of Isaacs, Chapter 10.
-/

public section

namespace TauCeti

open Module CategoryTheory.MonoidalCategory

universe u v w

section Defs

variable {k : Type u} {G : Type v} [Field k] [Monoid G]

variable (k G)

/-- **The virtual-character lattice** of `G` over `k`: the additive subgroup of `G → k` generated
by the characters of the finite-dimensional representations of `G`.

Its elements, the *virtual characters*, are the differences of genuine characters: characters are
closed under addition, so an integer combination of them is a difference of two of them. -/
def virtualCharacters : AddSubgroup (G → k) :=
  AddSubgroup.closure (Set.range (FDRep.character : FDRep k G → G → k))

variable {k G}

/-- **A character is a virtual character.** -/
@[simp]
theorem character_mem_virtualCharacters (V : FDRep k G) :
    V.character ∈ virtualCharacters k G :=
  AddSubgroup.subset_closure ⟨V, rfl⟩

/-- **The generation principle for the virtual-character lattice**: an additive subgroup of `G → k`
containing every character contains every virtual character. -/
theorem virtualCharacters_le {H : AddSubgroup (G → k)} (h : ∀ V : FDRep k G, V.character ∈ H) :
    virtualCharacters k G ≤ H := by
  rw [virtualCharacters, AddSubgroup.closure_le]
  rintro - ⟨V, rfl⟩
  exact h V

open CategoryTheory.Limits in
/-- **A virtual character is a difference of two characters**: the characters are closed under
addition, the character of a direct sum being the sum of the characters, so an integer combination
of characters is the character of one representation minus that of another. -/
theorem exists_eq_character_sub_character {f : G → k} (hf : f ∈ virtualCharacters k G) :
    ∃ A B : FDRep k G, f = A.character - B.character := by
  induction hf using AddSubgroup.closure_induction with
  | mem f hf =>
    obtain ⟨V, rfl⟩ := hf
    exact ⟨V ⊞ V, V, by rw [FDRep.char_biprod, add_sub_cancel_right]⟩
  | zero => exact ⟨𝟙_ (FDRep k G), 𝟙_ (FDRep k G), (sub_self _).symm⟩
  | add f g _ _ hf hg =>
    obtain ⟨A, B, rfl⟩ := hf
    obtain ⟨C, D, rfl⟩ := hg
    exact ⟨A ⊞ C, B ⊞ D, by rw [FDRep.char_biprod, FDRep.char_biprod]; abel⟩
  | neg f _ hf =>
    obtain ⟨A, B, rfl⟩ := hf
    exact ⟨B, A, (neg_sub _ _)⟩

/-- **A function `G → k` is a virtual character exactly when it is a difference of two
characters.** This holds over any field and for any monoid `G`, unlike the description
`TauCeti.mem_virtualCharacters_iff` as an integer combination of irreducible characters. -/
theorem mem_virtualCharacters_iff_exists_eq_character_sub_character {f : G → k} :
    f ∈ virtualCharacters k G ↔ ∃ A B : FDRep k G, f = A.character - B.character :=
  ⟨exists_eq_character_sub_character, by
    rintro ⟨A, B, rfl⟩
    exact sub_mem (character_mem_virtualCharacters A) (character_mem_virtualCharacters B)⟩

/-- **The virtual-character lattice is closed under the pointwise product.** The product of two
characters is the character of the tensor product, and multiplication by a fixed function is
additive, so the property propagates through the additive generation of the lattice.

The lattice is nevertheless kept as an `AddSubgroup`: multiplicativity is recorded by this lemma
rather than by bundling the carrier as a `Subring (G → k)`, the additive interface being the one
the roadmap prescribes. -/
theorem mul_mem_virtualCharacters {f g : G → k} (hf : f ∈ virtualCharacters k G)
    (hg : g ∈ virtualCharacters k G) : f * g ∈ virtualCharacters k G := by
  rw [virtualCharacters] at hf hg ⊢
  induction hf, hg using AddSubgroup.closure_induction₂ with
  | mem x y hx hy =>
    obtain ⟨V, rfl⟩ := hx
    obtain ⟨W, rfl⟩ := hy
    rw [← FDRep.char_tensor]
    exact AddSubgroup.subset_closure ⟨V ⊗ W, rfl⟩
  | zero_left x _ => simp
  | zero_right x _ => simp
  | add_left x y z hx hy hz ihx ihy => rw [add_mul]; exact AddSubgroup.add_mem _ ihx ihy
  | add_right y z x hy hz hx ihy ihz => rw [mul_add]; exact AddSubgroup.add_mem _ ihy ihz
  | neg_left x y hx hy ih => rw [neg_mul]; exact AddSubgroup.neg_mem _ ih
  | neg_right x y hx hy ih => rw [mul_neg]; exact AddSubgroup.neg_mem _ ih

/-- **The constant function `1` is a virtual character**, being the character of the trivial
one-dimensional representation. -/
@[simp]
theorem one_mem_virtualCharacters : (1 : G → k) ∈ virtualCharacters k G := by
  have h : (FDRep.of (Representation.trivial k G k)).character = 1 :=
    funext fun g => FDRep.character_of_trivial g
  exact h ▸ character_mem_virtualCharacters _

/-- **Pulling back along a monoid homomorphism preserves virtual characters.** The pullback
`f ∘ φ` of a character along `φ : H →* G` is the character of the representation restricted along
`φ`, Mathlib's `Action.res`, and pullback is additive, so the property propagates through the
additive generation of the lattice. Restriction to a subgroup and inflation from a quotient are
the two instances. -/
theorem comp_mem_virtualCharacters {H : Type w} [Monoid H] (φ : H →* G) {f : G → k}
    (hf : f ∈ virtualCharacters k G) : f ∘ φ ∈ virtualCharacters k H := by
  rw [virtualCharacters] at hf ⊢
  induction hf using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨V, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨(Action.res (FGModuleCat k) φ).obj V, ?_⟩
    funext h
    exact V.character_actionRes φ h
  | zero => rw [Pi.zero_comp]; exact AddSubgroup.zero_mem _
  | neg x _ ih => rw [Pi.neg_comp]; exact AddSubgroup.neg_mem _ ih
  | add x y _ _ ihx ihy => rw [Pi.add_comp]; exact AddSubgroup.add_mem _ ihx ihy

/-- **Pulling back along a monoid homomorphism preserves `A`-combinations of virtual characters**,
for any subring `A` of `k`: pullback is `A`-linear and, by `TauCeti.comp_mem_virtualCharacters`,
carries virtual characters to virtual characters. -/
theorem comp_mem_span_virtualCharacters (A : Subring k) {H : Type w} [Monoid H] (φ : H →* G)
    {f : G → k} (hf : f ∈ Submodule.span A (virtualCharacters k G : Set (G → k))) :
    f ∘ φ ∈ Submodule.span A (virtualCharacters k H : Set (H → k)) :=
  (Submodule.map_span_le (LinearMap.funLeft A k φ) _ _).2
    (fun _ hg => Submodule.subset_span (comp_mem_virtualCharacters φ hg))
    (Submodule.mem_map_of_mem hf)

end Defs

section ClassFunctions

variable {k : Type u} {G : Type v} [Field k] [Group G]

/-- **The virtual-character lattice is contained in the class functions**: a virtual character is
constant on conjugacy classes, being an integer combination of characters, each of which is.

Applied to a hypothesis `hf : f ∈ virtualCharacters k G` this gives `f ∈ ClassFunction k G`. -/
theorem virtualCharacters_le_classFunction :
    virtualCharacters k G ≤ (ClassFunction k G).toAddSubgroup :=
  virtualCharacters_le fun V => by
    have h : (ClassFunction.ofCharacter V.ρ : G → k) = V.character :=
      funext fun g => ClassFunction.ofCharacter_apply V.ρ g
    exact h ▸ (ClassFunction.ofCharacter V.ρ).2

end ClassFunctions

section Complex

variable {G : Type v} [Group G] [Finite G]

/-- **Over `ℂ`, inverting the argument conjugates the value of a virtual character** of a finite
group: `conj (f g) = f g⁻¹`. This holds for genuine characters (`FDRep.conj_char`), and
both sides are additive in `f`.

This is not a `simp` lemma: `TauCeti.character_mem_virtualCharacters` and
`TauCeti.irreducibleCharacter_mem_virtualCharacters` discharge its hypothesis, so as a conditional
`simp` lemma it fires on the characters themselves and makes the more specific
`FDRep.conj_char` and `TauCeti.conj_irreducibleCharacter` redundant, which the `simpNF`
linter rejects. -/
theorem conj_apply_of_mem_virtualCharacters {f : G → ℂ} (hf : f ∈ virtualCharacters ℂ G) (g : G) :
    (starRingEnd ℂ) (f g) = f g⁻¹ := by
  have key : ∀ x ∈ AddSubgroup.closure (Set.range (FDRep.character : FDRep ℂ G → G → ℂ)),
      (starRingEnd ℂ) (x g) = x g⁻¹ := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨V, rfl⟩ := hx
      exact FDRep.conj_char V g
    | zero => simp
    | neg x _ ih => simp [ih]
    | add x y _ _ ihx ihy => simp [ihx, ihy]
  exact key f hf

end Complex

section Irreducible

variable {k : Type u} {G : Type v} [Field k] [Group G]

/-- Every irreducible character is the character of a bundled representation, hence generates the
virtual-character lattice. -/
theorem irreducibleCharacters_subset_range :
    irreducibleCharacters k G ⊆ Set.range (FDRep.character : FDRep k G → G → k) := by
  intro f hf
  obtain ⟨n, ρ, -, rfl⟩ := mem_irreducibleCharacters_iff.mp hf
  exact ⟨FDRep.of ρ, rfl⟩

end Irreducible

section Lattice

variable {k : Type u} {G : Type v} [Field k] [Group G] [Finite G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)]

/-- **A character is the sum of the irreducible characters weighted by their multiplicities.** The
coefficient of `χᵢ` in the expansion of `χ_V` in the basis of irreducible characters is the pairing
`⟨χᵢ, χ_V⟩`, which is the dimension of the space of intertwiners `V → Vᵢ`, so the coefficients are
natural numbers: the multiplicities with which the irreducibles occur in `V`. -/
theorem character_eq_sum_nsmul_irreducibleCharacter (V : FDRep k G) :
    V.character = ∑ i, finrank k (Representation.IntertwiningMap V.ρ
      (irreducibleRepresentation k i)) • irreducibleCharacter k i := by
  let _ : Fintype G := Fintype.ofFinite G
  funext y
  have hy := ClassFunction.apply_eq_sum_characterPairing_mul_character
    (irreducibleRepresentation k) (pairwise_isEmpty_equiv_irreducibleRepresentation k)
    (by simp) (ClassFunction.ofFDRep V) y
  rw [ClassFunction.ofFDRep_apply, ClassFunction.ofFDRep_eq_ofCharacter] at hy
  rw [hy, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ClassFunction.characterPairing_ofCharacter_eq_finrank (irreducibleRepresentation k i) V.ρ,
    Pi.smul_apply, nsmul_eq_mul, character_irreducibleRepresentation]

/-- **Every character lies in the `ℤ`-span of the irreducible characters**, its multiplicities
being natural numbers. -/
theorem character_mem_closure_irreducibleCharacters (V : FDRep k G) :
    V.character ∈ AddSubgroup.closure (irreducibleCharacters k G) := by
  rw [character_eq_sum_nsmul_irreducibleCharacter V]
  exact AddSubgroup.sum_mem _ fun i _ =>
    AddSubgroup.nsmul_mem _ (AddSubgroup.subset_closure (irreducibleCharacter_mem k i)) _

/-- **The virtual-character lattice is the `ℤ`-span of the irreducible characters.** One inclusion
is that every character expands over the irreducible characters with natural-number coefficients;
the other is that an irreducible character is a character. -/
theorem virtualCharacters_eq_closure_irreducibleCharacters :
    virtualCharacters k G = AddSubgroup.closure (irreducibleCharacters k G) :=
  le_antisymm (virtualCharacters_le character_mem_closure_irreducibleCharacters)
    ((AddSubgroup.closure_le _).mpr fun _ hf =>
      AddSubgroup.subset_closure (irreducibleCharacters_subset_range hf))

/-- **An irreducible character is a virtual character.** -/
@[simp]
theorem irreducibleCharacter_mem_virtualCharacters (i : Fin (Nat.card (ConjClasses G))) :
    irreducibleCharacter k i ∈ virtualCharacters k G := by
  rw [virtualCharacters_eq_closure_irreducibleCharacters]
  exact AddSubgroup.subset_closure (irreducibleCharacter_mem k i)

/-- The enumerated irreducible characters exhaust the irreducible characters. -/
theorem range_irreducibleCharacter :
    Set.range (irreducibleCharacter (G := G) k) = irreducibleCharacters k G := by
  ext f
  exact ⟨by rintro ⟨i, rfl⟩; exact irreducibleCharacter_mem k i,
    fun hf => exists_irreducibleCharacter_eq k hf⟩

/-- **A function `G → k` is a virtual character exactly when it is an integer combination of the
irreducible characters.**

The coefficients `c` are genuine integers, but they are pinned down by `f` only in characteristic
zero: what the irreducible characters determine are the scalars `(c i : k)`, and in positive
characteristic the cast `ℤ → k` is not injective. -/
theorem mem_virtualCharacters_iff {f : G → k} :
    f ∈ virtualCharacters k G ↔
      ∃ c : Fin (Nat.card (ConjClasses G)) → ℤ,
        f = ∑ i, (c i : k) • irreducibleCharacter k i := by
  have hspan : ∀ x : G → k, x ∈ AddSubgroup.closure (irreducibleCharacters k G) ↔
      x ∈ Submodule.span ℤ (Set.range (irreducibleCharacter (G := G) k)) := by
    intro x
    rw [range_irreducibleCharacter, ← AddSubgroup.toIntSubmodule_closure]
    exact Iff.rfl
  rw [virtualCharacters_eq_closure_irreducibleCharacters, hspan,
    Submodule.mem_span_range_iff_exists_fun]
  refine exists_congr fun c => ?_
  have heq : (∑ i, (c i : k) • irreducibleCharacter k i) =
      ∑ i, c i • irreducibleCharacter k i :=
    Finset.sum_congr rfl fun i _ => Int.cast_smul_eq_zsmul k (c i) _
  rw [heq, eq_comm]

/-- **Virtual characters descend from `A`-coefficients to integer coefficients.** Let `A` be a
subring of `k` admitting an additive map `t : A → ℤ` with `t 1 = 1`, such as `ℤ[ζ]` for a root of
unity `ζ` in characteristic zero (`PowerBasis.exists_linearMap_apply_one`). If `V` is an additive
subgroup of the virtual characters, then a virtual character that is an `A`-linear combination of
elements of `V` already lies in `V`: `Submodule.span A V ∩ R(G) = V`. -/
theorem mem_of_mem_span_of_mem_virtualCharacters (A : Subring k) (t : A →+ ℤ) (ht : t 1 = 1)
    {V : AddSubgroup (G → k)} (hV : V ≤ virtualCharacters k G) {f : G → k}
    (hf : f ∈ virtualCharacters k G) (hfA : f ∈ Submodule.span A (V : Set (G → k))) :
    f ∈ V := by
  have h := virtualCharacters_eq_closure_irreducibleCharacters (k := k) (G := G)
  rw [← range_irreducibleCharacter] at h
  rw [h] at hV hf
  exact mem_of_mem_span_of_mem_closure
    ((linearIndependent_irreducibleCharacter (k := k)).restrict_scalars' A) t ht hV hf hfA

/-- Reading an integer combination of irreducible characters back inside
`TauCeti.ClassFunction`. -/
private theorem eq_sum_smul_ofCharacter {f : ClassFunction k G}
    {c : Fin (Nat.card (ConjClasses G)) → ℤ}
    (hc : (f : G → k) = ∑ i, (c i : k) • irreducibleCharacter k i) :
    f = ∑ i, (c i : k) • ClassFunction.ofCharacter (irreducibleRepresentation k i) := by
  refine Subtype.ext ?_
  rw [hc, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [SetLike.val_smul]
  congr 1
  funext y
  rw [ClassFunction.ofCharacter_apply, character_irreducibleRepresentation]

end Lattice

section Subring

variable {k : Type u} {G : Type v} [Field k] [Group G] [Finite G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)]

/-- **A class function with values in a subring `A` is, once multiplied by `|G|`, an
`A`-combination of the irreducible characters**, provided `A` contains the values of the
irreducible characters: the coefficient of `χᵢ` in `|G| • f` is the group sum `∑ g, χᵢ(g) f(g⁻¹)`.

This is the expansion of a class function in the basis of irreducible characters with the
division by `|G|` in the character pairing cleared, so that only the ring operations of `A` are
needed. It is the integrality input of Brauer's induction theorem. -/
theorem natCard_nsmul_mem_span_irreducibleCharacters (A : Subring k) {f : G → k}
    (hf : f ∈ ClassFunction k G) (hfA : ∀ g, f g ∈ A)
    (hA : ∀ (i : Fin (Nat.card (ConjClasses G))) (g : G), irreducibleCharacter k i g ∈ A) :
    Nat.card G • f ∈ Submodule.span A (irreducibleCharacters k G) := by
  let _ : Fintype G := Fintype.ofFinite G
  have hexp : Nat.card G • f =
      ∑ i, (∑ g, irreducibleCharacter k i g * f g⁻¹) • irreducibleCharacter k i := by
    funext y
    have hy := ClassFunction.apply_eq_sum_characterPairing_mul_character
      (irreducibleRepresentation k) (pairwise_isEmpty_equiv_irreducibleRepresentation k)
      (by simp) ⟨f, hf⟩ y
    simp only [ClassFunction.characterPairing_apply, ClassFunction.ofCharacter_apply,
      character_irreducibleRepresentation] at hy
    rw [Pi.smul_apply, Finset.sum_apply, nsmul_eq_mul, hy, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_assoc, mul_inv_cancel_left₀ (Invertible.ne_zero _)]
  rw [hexp]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hc : ∑ g, irreducibleCharacter k i g * f g⁻¹ ∈ A :=
    A.sum_mem fun g _ => A.mul_mem (hA i g) (hfA g⁻¹)
  rw [← Subring.smul_def (⟨_, hc⟩ : A)]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (irreducibleCharacter_mem k i))

end Subring

section Pairing

variable {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)]

/-- **The character pairing of two virtual characters is the dot product of their integer
coefficients.** The irreducible characters are orthonormal, so pairing two integer combinations of
them multiplies the coefficients termwise. -/
theorem characterPairing_eq_intCast_sum {f₁ f₂ : ClassFunction k G}
    {c d : Fin (Nat.card (ConjClasses G)) → ℤ}
    (h₁ : (f₁ : G → k) = ∑ i, (c i : k) • irreducibleCharacter k i)
    (h₂ : (f₂ : G → k) = ∑ i, (d i : k) • irreducibleCharacter k i) :
    ClassFunction.characterPairing f₁ f₂ = ((∑ i, c i * d i : ℤ) : k) := by
  classical
  rw [eq_sum_smul_ofCharacter h₁, eq_sum_smul_ofCharacter h₂]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    characterPairing_ofCharacter_irreducibleRepresentation_orthonormal, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  push_cast
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **The character pairing is integer-valued on the virtual-character lattice.** -/
theorem exists_characterPairing_eq_intCast {f₁ f₂ : ClassFunction k G}
    (h₁ : (f₁ : G → k) ∈ virtualCharacters k G) (h₂ : (f₂ : G → k) ∈ virtualCharacters k G) :
    ∃ n : ℤ, ClassFunction.characterPairing f₁ f₂ = (n : k) := by
  obtain ⟨c, hc⟩ := mem_virtualCharacters_iff.mp h₁
  obtain ⟨d, hd⟩ := mem_virtualCharacters_iff.mp h₂
  exact ⟨∑ i, c i * d i, characterPairing_eq_intCast_sum hc hd⟩

end Pairing

section Norm

variable {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G] [IsAlgClosed k] [CharZero k]
  [Invertible (Nat.card G : k)]

/-- **A virtual character of norm `1` is `±` an irreducible character.** Writing the virtual
character as `∑ᵢ cᵢ χᵢ` with integer coefficients, its norm is `∑ᵢ cᵢ²`; a sum of squares of
integers is `1` only when a single coefficient is `±1` and the rest vanish.

This is the norm-`1` classification of virtual characters: the conclusion is genuinely a sign
ambiguity, since `-χᵢ` also has norm `1` and is not itself an irreducible character. It specializes
to the usual irreducibility test only for a genuine character, where the coefficients are
non-negative and so the negative case cannot occur. It is the tool behind the
exceptional-character arguments of Frobenius's theorem. -/
theorem exists_eq_irreducibleCharacter_or_neg {f : ClassFunction k G}
    (hf : (f : G → k) ∈ virtualCharacters k G)
    (hnorm : ClassFunction.characterPairing f f = 1) :
    ∃ i, (f : G → k) = irreducibleCharacter k i ∨
      (f : G → k) = -irreducibleCharacter k i := by
  classical
  obtain ⟨c, hc⟩ := mem_virtualCharacters_iff.mp hf
  have hcast := characterPairing_eq_intCast_sum hc hc
  rw [hnorm] at hcast
  have hsum : ∑ i, c i * c i = 1 :=
    Int.cast_injective (α := k) (by rw [← hcast, Int.cast_one])
  have hnn : ∀ i ∈ (Finset.univ : Finset (Fin (Nat.card (ConjClasses G)))), 0 ≤ c i * c i :=
    fun i _ => mul_self_nonneg _
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, c i₀ ≠ 0 := by
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    rw [Finset.sum_congr rfl fun i _ => by rw [hcon i, mul_zero], Finset.sum_const_zero] at hsum
    exact zero_ne_one hsum
  have hpos : 0 < c i₀ * c i₀ := lt_of_le_of_ne (mul_self_nonneg _) (Ne.symm (mul_ne_zero hi₀ hi₀))
  have hge : 1 ≤ c i₀ * c i₀ := by simpa using Int.lt_iff_add_one_le.mp hpos
  have hle : c i₀ * c i₀ ≤ 1 := hsum ▸ Finset.single_le_sum hnn (Finset.mem_univ i₀)
  have hone : c i₀ * c i₀ = 1 := le_antisymm hle hge
  have hadd := Finset.sum_erase_add Finset.univ (fun i => c i * c i) (Finset.mem_univ i₀)
  have hzero : ∑ i ∈ Finset.univ.erase i₀, c i * c i = 0 := by omega
  have hrest : ∀ i ∈ Finset.univ.erase i₀, c i = 0 := fun i hi =>
    mul_self_eq_zero.mp
      ((Finset.sum_eq_zero_iff_of_nonneg fun j _ => hnn j (Finset.mem_univ j)).mp hzero i hi)
  have hval : (f : G → k) = (c i₀ : k) • irreducibleCharacter k i₀ := by
    rw [hc, ← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i₀),
      Finset.sum_eq_zero fun i hi => by rw [hrest i hi]; simp, zero_add]
  refine ⟨i₀, ?_⟩
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hone with h | h
  · exact Or.inl (by rw [hval, h]; simp)
  · exact Or.inr (by rw [hval, h]; simp)

/-- **A virtual character of norm `1` whose degree is a natural number is an irreducible
character.** By `TauCeti.exists_eq_irreducibleCharacter_or_neg` it is `±χ`, and `-χ` is excluded:
its degree `-χ(1)` is negative, so it is not the image of a natural number. -/
theorem mem_irreducibleCharacters_of_characterPairing_self_eq_one {f : ClassFunction k G}
    (hf : (f : G → k) ∈ virtualCharacters k G)
    (hnorm : ClassFunction.characterPairing f f = 1) {n : ℕ} (hn : (f : G → k) 1 = n) :
    (f : G → k) ∈ irreducibleCharacters k G := by
  obtain ⟨i, hi | hi⟩ := exists_eq_irreducibleCharacter_or_neg hf hnorm
  · exact hi ▸ irreducibleCharacter_mem k i
  · -- the negative alternative would force a sum of a positive and a natural number to vanish
    exfalso
    rw [hi, Pi.neg_apply, irreducibleCharacter_one] at hn
    have hsum : ((characterDegree k i + n : ℕ) : k) = 0 := by
      push_cast
      linear_combination -hn
    have := characterDegree_pos k i
    rw [Nat.cast_eq_zero] at hsum
    omega

end Norm

section NormCharZero

open Module

variable {k : Type u} {G : Type v} [Field k] [Group G]

/-- The cancellation step of `TauCeti.exists_simple_character_eq_of_characterPairing_self_eq_one`:
a nonzero intertwiner `σ → ρ` between semisimple representations exhibits a common summand, the
image of a complement of its kernel, and cancelling it from `χ_ρ - χ_σ` leaves the difference of
the characters of a complement of that image in `ρ` and of the kernel. -/
private theorem exists_char_sub_eq_of_ne_zero {V W : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    {ρ : Representation k G V} {σ : Representation k G W} [ρ.IsSemisimpleRepresentation]
    [σ.IsSemisimpleRepresentation] {φ : σ.IntertwiningMap ρ} (hφ : φ ≠ 0) :
    ∃ (ρ' : Subrepresentation ρ) (σ' : Subrepresentation σ),
      finrank k ρ'.toSubmodule < finrank k V ∧
        ρ.character - σ.character =
          ρ'.toRepresentation.character - σ'.toRepresentation.character := by
  obtain ⟨C, hC⟩ := exists_isCompl φ.ker
  have hC' := Subrepresentation.isCompl_toSubmodule.mpr hC
  -- `φ` restricted to the complement `C` of its kernel is injective
  let ψ := φ.comp C.subtype
  have hψ : Function.Injective ψ := by
    intro x y hxy
    have hker : (x : W) - y ∈ φ.ker.toSubmodule := by
      simp only [Representation.IntertwiningMap.ker_toSubmodule, LinearMap.mem_ker,
        Representation.IntertwiningMap.coe_toLinearMap, map_sub]
      exact sub_eq_zero.mpr (by simpa [ψ] using hxy)
    exact Subtype.ext (sub_eq_zero.mp (Submodule.disjoint_def.mp hC'.disjoint _ hker
      (C.toSubmodule.sub_mem x.2 y.2)))
  obtain ⟨ρ', hρ'⟩ := exists_isCompl ψ.range
  refine ⟨ρ', φ.ker, ?_, ?_⟩
  · -- the image of `ψ` is nonzero, since otherwise `C` is zero and `φ` vanishes
    have hpos : 0 < finrank k ψ.range.toSubmodule := by
      refine Nat.pos_of_ne_zero fun h0 => hφ ?_
      have hrange := Submodule.finrank_eq_zero.mp h0
      have hCbot : C.toSubmodule = ⊥ := Submodule.eq_bot_iff _ |>.mpr fun v hv =>
        congrArg Subtype.val (hψ (a₂ := 0) (by
          simpa using (Submodule.eq_bot_iff _).mp hrange (ψ ⟨v, hv⟩) ⟨⟨v, hv⟩, rfl⟩))
      have hktop : φ.ker.toSubmodule = ⊤ := eq_top_of_isCompl_bot (hCbot ▸ hC')
      refine Representation.IntertwiningMap.ext (LinearMap.ext fun v => ?_)
      have hv : v ∈ φ.ker.toSubmodule := hktop ▸ Submodule.mem_top
      simpa using hv
    have := Submodule.finrank_add_eq_of_isCompl
      (Subrepresentation.isCompl_toSubmodule.mpr hρ')
    omega
  · rw [← Subrepresentation.char_add_eq_of_isCompl hC,
      ← Subrepresentation.char_add_eq_of_isCompl hρ',
      Representation.char_iso (ψ.equivOfRange hψ (P := ψ.range) rfl)]
    abel

open _root_.Representation in
/-- **A virtual character of norm `1` and natural degree is the character of an absolutely
irreducible representation, over any field of characteristic zero.** If `f` is an integer
combination of characters of representations of `G` over `k`, with `⟨f, f⟩ = 1` and `f 1` a
natural number, then `f` is the character of a simple object `V` of `FDRep k G` whose equivariant
endomorphisms are the scalars.

Over an algebraically closed field this is
`TauCeti.mem_irreducibleCharacters_of_characterPairing_self_eq_one`. Over a general field the
irreducible characters need not be orthonormal (the rotation representation of `ℤ/3` on `ℝ²` is
irreducible of norm `2`), so instead `f = χ_A - χ_B` is reduced by cancelling common summands of
`A` and `B` until no nonzero intertwiner `B → A` is left; then `⟨f, f⟩ = dim End(A) + dim End(B)`
forces one of `A`, `B` to be zero and the other to have one-dimensional endomorphism algebra, and
the degree rules out `A = 0`.

This is the step that turns a character identity over a subfield `k` of `ℂ` into the realizability
over `k` of an irreducible complex representation. -/
theorem exists_simple_character_eq_of_characterPairing_self_eq_one [Fintype G] [CharZero k]
    {f : ClassFunction k G} (hf : (f : G → k) ∈ virtualCharacters k G)
    (hnorm : ClassFunction.characterPairing f f = 1) {n : ℕ} (hn : (f : G → k) 1 = n) :
    ∃ V : FDRep k G, CategoryTheory.Simple V ∧ finrank k (V ⟶ V) = 1 ∧ V.character = f := by
  have : NeZero (Nat.card G : k) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  let _ : Invertible (Nat.card G : k) := invertibleOfNonzero (NeZero.ne _)
  obtain ⟨A, B, hAB⟩ := exists_eq_character_sub_character hf
  induction hA : finrank k A using Nat.strong_induction_on generalizing A B with
  | _ m ih =>
  by_cases hφ : ∃ φ : IntertwiningMap B.ρ A.ρ, φ ≠ 0
  · -- cancel a common summand of `A` and `B`, lowering the dimension of `A`
    obtain ⟨φ, hφ⟩ := hφ
    obtain ⟨ρ', σ', hlt, heq⟩ := exists_char_sub_eq_of_ne_zero hφ
    refine ih _ (hA ▸ hlt) (FDRep.of ρ'.toRepresentation) (FDRep.of σ'.toRepresentation) ?_ rfl
    rw [hAB, FDRep.character_of, FDRep.character_of, ← heq]
    funext g
    rw [Pi.sub_apply, Pi.sub_apply, FDRep.character_ρ, FDRep.character_ρ]
  -- no intertwiner `B → A` is left, so `⟨f, f⟩ = dim End(A) + dim End(B)`
  push Not at hφ
  have : Subsingleton (IntertwiningMap B.ρ A.ρ) := ⟨fun φ ψ => (hφ φ).trans (hφ ψ).symm⟩
  have hf' : f = ClassFunction.ofCharacter A.ρ - ClassFunction.ofCharacter B.ρ :=
    Subtype.ext (funext fun g => by simp [hAB, ClassFunction.ofCharacter_apply, FDRep.character_ρ])
  rw [hf', ClassFunction.characterPairing_ofCharacter_sub_self] at hnorm
  have hsum : finrank k (IntertwiningMap A.ρ A.ρ) + finrank k (IntertwiningMap B.ρ B.ρ) = 1 := by
    exact_mod_cast hnorm
  rcases Nat.add_eq_one_iff.mp hsum with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · -- `A = 0` would make the degree `f 1 = -dim B` negative
    have := (isIrreducible_of_finrank_intertwiningMap_self_eq_one hb).nontrivial
    rw [hAB, Pi.sub_apply, FDRep.character_eq_zero_of_finrank_intertwiningMap_eq_zero A ha,
      Pi.zero_apply, zero_sub, FDRep.char_one] at hn
    have hd : finrank k B + n = 0 := by
      exact_mod_cast (by linear_combination -hn : (finrank k B : k) + n = 0)
    exact absurd (finrank_pos (R := k) (M := B)) (by omega)
  · -- `B = 0`, and `A` is semisimple with one-dimensional endomorphism algebra
    have := isIrreducible_of_finrank_intertwiningMap_self_eq_one ha
    refine ⟨A, inferInstance, ?_, ?_⟩
    · have hEnd := ClassFunction.characterPairing_ofFDRep_eq_finrank A A
      rw [ClassFunction.ofFDRep_eq_ofCharacter,
        ClassFunction.characterPairing_ofCharacter_eq_finrank, ha] at hEnd
      exact_mod_cast hEnd.symm
    · rw [hAB, FDRep.character_eq_zero_of_finrank_intertwiningMap_eq_zero B hb, sub_zero]

end NormCharZero

end TauCeti
