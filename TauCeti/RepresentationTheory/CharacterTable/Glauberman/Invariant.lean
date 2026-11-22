/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SemidirectProduct
public import TauCeti.RepresentationTheory.CharacterTable.Automorphism
public import TauCeti.RepresentationTheory.Induction.Inertia
import TauCeti.RepresentationTheory.CharacterTable.Determined

/-!
# Invariant irreducible characters under an action by automorphisms

Let a group `S` act on a group `Γ` by automorphisms (`MulDistribMulAction S Γ`). Then `S` acts on
the functions `Γ → k` by `(s · χ)(g) = χ(s⁻¹ • g)`, the convention of Mathlib's `arrowAction`, and
this action permutes the irreducible characters: it is the action of `MulAut Γ` on
`TauCeti.irreducibleCharacters k Γ` of `TauCeti.instMulActionMulAutIrreducibleCharacters`, pulled
back along `MulDistribMulAction.toMulAut S Γ`. Its fixed set is the set `Irr_S(Γ)` of
**invariant irreducible characters**, `TauCeti.invariantIrreducibleCharacters k S Γ`: the
irreducible characters `χ` with `χ(s • g) = χ(g)` for all `s` and `g`.

These are the characters studied by Glauberman's correspondence for a coprime action, which
matches `Irr_S(Γ)` with the irreducible characters of the fixed-point subgroup
`FixedPoints.subgroup S Γ`. Invariance has two representation-theoretic readings, used to extend
an invariant character from `Γ` to `Γ ⋊ S`:

* a representation `ρ` affording `χ` is equivalent to each of its twists `g ↦ ρ (s • g)`;
* in the semidirect product `Γ ⋊ S`, where `Γ` is the kernel of the projection onto `S`, the
  inertia group of a representation of `Γ` affording `χ` is everything.

## Main definitions and results

* `TauCeti.invariantIrreducibleCharacters`: the invariant irreducible characters `Irr_S(Γ)`.
* `TauCeti.coe_mem_invariantIrreducibleCharacters_iff`: `Irr_S(Γ)` is the fixed set of the action
  of `S` on the irreducible characters through `MulAut Γ`.
* `TauCeti.invariantIrreducibleCharacters_range_toMulAut` and
  `FixedPoints.subgroup_range_toMulAut`: both `Irr_S(Γ)` and `C_Γ(S)` only depend on the image of
  `S` in `MulAut Γ`, so the kernel of the action can be divided out.
* `Representation.character_mem_invariantIrreducibleCharacters_iff`: over a field of
  characteristic zero and for finite `Γ`, the character of an irreducible representation `ρ` is
  invariant exactly when `ρ` is equivalent to each of its twists by elements of `S`.
* `TauCeti.inertia_eq_top_iff_forall_character_smul_eq`: for a representation `A` of the kernel
  of `Γ ⋊ S → S`, its inertia group is the whole semidirect product exactly when its character,
  read on `Γ`, is `S`-invariant.

## References

* G. Glauberman, *Correspondences of characters for relatively prime operator groups*, Canad. J.
  Math. **20** (1968), 1465–1488, §1.
* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Chapter 13.
-/

public section

open MulAction SemidirectProduct

universe u v w

namespace TauCeti

section Definition

variable (k : Type u) (S : Type v) (Γ : Type w) [Field k] [Group S] [Group Γ]
  [MulDistribMulAction S Γ]

/-- The **invariant irreducible characters** `Irr_S(Γ)` for a group `S` acting on `Γ` by
automorphisms: the irreducible characters `χ` of `Γ` over `k` with `χ(s • g) = χ(g)` for all
`s : S` and `g : Γ`. They are the fixed points of the action `(s · χ)(g) = χ(s⁻¹ • g)` of `S` on
the irreducible characters (`TauCeti.coe_mem_invariantIrreducibleCharacters_iff`). -/
def invariantIrreducibleCharacters : Set (Γ → k) :=
  {χ | χ ∈ irreducibleCharacters k Γ ∧ ∀ (s : S) (g : Γ), χ (s • g) = χ g}

end Definition

variable {k : Type u} {S : Type v} {Γ : Type w} [Field k] [Group S] [Group Γ]
  [MulDistribMulAction S Γ]

/-- Membership in `TauCeti.invariantIrreducibleCharacters` unfolded. -/
theorem mem_invariantIrreducibleCharacters_iff {χ : Γ → k} :
    χ ∈ invariantIrreducibleCharacters k S Γ ↔
      χ ∈ irreducibleCharacters k Γ ∧ ∀ (s : S) (g : Γ), χ (s • g) = χ g :=
  Iff.rfl

/-- An invariant irreducible character is an irreducible character. -/
theorem invariantIrreducibleCharacters_subset_irreducibleCharacters :
    invariantIrreducibleCharacters k S Γ ⊆ irreducibleCharacters k Γ :=
  fun _ hχ ↦ hχ.1

/-- **The invariant irreducible characters are the fixed points** of the action of `S` on the
irreducible characters through `MulDistribMulAction.toMulAut S Γ`, under which `s` sends `χ` to
`g ↦ χ(s⁻¹ • g)`. -/
theorem coe_mem_invariantIrreducibleCharacters_iff (χ : irreducibleCharacters k Γ) :
    (χ : Γ → k) ∈ invariantIrreducibleCharacters k S Γ ↔
      ∀ s : S, MulDistribMulAction.toMulAut S Γ s • χ = χ := by
  simp only [mem_invariantIrreducibleCharacters_iff, χ.property, true_and]
  refine forall_congr' fun s ↦ ?_
  rw [← mem_fixedBy, mem_fixedBy_irreducibleCharacters_iff, funext_iff]
  simp

/-- **Only the image of `S` in `MulAut Γ` matters** for the invariant irreducible characters: they
are the same for `S` and for the range of `MulDistribMulAction.toMulAut S Γ`, which is the quotient
of `S` by the kernel of its action. -/
@[simp]
theorem invariantIrreducibleCharacters_range_toMulAut :
    invariantIrreducibleCharacters k (MulDistribMulAction.toMulAut S Γ).range Γ =
      invariantIrreducibleCharacters k S Γ := by
  ext χ
  simp [mem_invariantIrreducibleCharacters_iff, Subgroup.smul_def]

section Twist

variable [CharZero k] [Finite Γ] {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- **Invariance as equivalence with the twists.** Over a field of characteristic zero and for a
finite group `Γ`, the character of an irreducible representation `ρ` of `Γ` is an invariant
irreducible character exactly when `ρ` is equivalent to its twist `g ↦ ρ (s • g)` for every
`s : S`: the character of the twist is `g ↦ χ(s • g)`, and representations are determined by
their characters. -/
theorem _root_.Representation.character_mem_invariantIrreducibleCharacters_iff
    (ρ : Representation k Γ V) [ρ.IsIrreducible] :
    ρ.character ∈ invariantIrreducibleCharacters k S Γ ↔
      ∀ s : S, Nonempty (ρ.Equiv (ρ.comp (MulDistribMulAction.toMonoidHom Γ s))) := by
  simp only [mem_invariantIrreducibleCharacters_iff, character_mem_irreducibleCharacters,
    true_and]
  refine forall_congr' fun s ↦ ⟨fun h ↦ ?_, fun ⟨e⟩ g ↦ ?_⟩
  · exact ρ.nonempty_equiv_of_character_eq _ (funext fun g ↦ (h g).symm)
  · exact (congrFun (Representation.char_iso e) g).symm

end Twist

section Inertia

/-- The inclusion of `Γ` into the kernel of the projection `Γ ⋊ S → S`. -/
private abbrev inlKer : Γ →* (rightHom : Γ ⋊[MulDistribMulAction.toMulAut S Γ] S →* S).ker :=
  inl.codRestrict _ fun g ↦ MonoidHom.mem_ker.2 (rightHom_inl g)

private theorem inlKer_surjective : Function.Surjective (inlKer (S := S) (Γ := Γ)) := by
  rintro ⟨x, hx⟩
  refine ⟨x.left, Subtype.ext ?_⟩
  rw [MonoidHom.mem_ker, rightHom_eq_right] at hx
  simpa [hx] using inl_left_mul_inr_right x

/-- Conjugating by `inr s` acts on the copy of `Γ` in `Γ ⋊ S` as `s⁻¹`. -/
private theorem inv_inr_mul_inl_mul_inr (s : S) (g : Γ) :
    (inr s)⁻¹ * (inl g : Γ ⋊[MulDistribMulAction.toMulAut S Γ] S) * inr s = inl (s⁻¹ • g) := by
  simp [← map_inv, ← inl_aut_inv]

variable [CharZero k] [Finite Γ]

/-- **Invariance as full inertia in the semidirect product.** In `Γ ⋊ S`, the copy of `Γ` is the
kernel of the projection onto `S`. For a finite group `Γ` and a field of characteristic zero, a
representation `A` of that kernel has the whole semidirect product as its inertia group exactly
when its character `χ`, read on `Γ`, satisfies `χ(s • g) = χ(g)` for all `s` and `g`. -/
theorem inertia_eq_top_iff_forall_character_smul_eq
    (A : FDRep k (rightHom : Γ ⋊[MulDistribMulAction.toMulAut S Γ] S →* S).ker) :
    inertia A = ⊤ ↔ ∀ (s : S) (g : Γ),
      A.character ⟨inl (s • g), MonoidHom.mem_ker.2 (rightHom_inl _)⟩ =
        A.character ⟨inl g, MonoidHom.mem_ker.2 (rightHom_inl _)⟩ := by
  have : Finite (rightHom : Γ ⋊[MulDistribMulAction.toMulAut S Γ] S →* S).ker :=
    Finite.of_surjective _ inlKer_surjective
  -- `inr s` lies in the inertia group exactly when the character is invariant under `s⁻¹`.
  have hinr (s : S) : inr s ∈ inertia A ↔ ∀ g : Γ, A.character (inlKer (s⁻¹ • g)) =
      A.character (inlKer g) := by
    rw [mem_inertia_iff_forall_character_eq, inlKer_surjective.forall]
    simp only [MonoidHom.codRestrict_apply, inv_inr_mul_inl_mul_inr]
  refine ⟨fun h s g ↦ by simpa using (hinr s⁻¹).1 (h ▸ Subgroup.mem_top _) g, fun h ↦ ?_⟩
  -- Every element is `inl x.left * inr x.right`, and the inertia group contains the kernel.
  refine eq_top_iff.2 fun x _ ↦ inl_left_mul_inr_right x ▸ mul_mem (le_inertia A ?_)
    ((hinr _).2 fun g ↦ h _ g)
  exact MonoidHom.mem_ker.2 (rightHom_inl _)

/-- **An invariant irreducible character has full inertia in the semidirect product.** For a
simple representation `A` of the copy of `Γ` in `Γ ⋊ S`, its character read on `Γ` is an invariant
irreducible character exactly when its inertia group is the whole semidirect product. -/
theorem mem_invariantIrreducibleCharacters_iff_inertia_eq_top
    (A : FDRep k (rightHom : Γ ⋊[MulDistribMulAction.toMulAut S Γ] S →* S).ker)
    [CategoryTheory.Simple A] :
    (fun g : Γ ↦ A.character ⟨inl g, MonoidHom.mem_ker.2 (rightHom_inl g)⟩) ∈
        invariantIrreducibleCharacters k S Γ ↔ inertia A = ⊤ := by
  have := FDRep.isIrreducible_of_simple A
  rw [inertia_eq_top_iff_forall_character_smul_eq, mem_invariantIrreducibleCharacters_iff]
  exact and_iff_right (inlKer.comp_mem_irreducibleCharacters inlKer_surjective
    (character_mem_irreducibleCharacters A.ρ))

end Inertia

end TauCeti

/-- **Only the image of `S` in `MulAut Γ` matters** for the fixed-point subgroup: `C_Γ(S)` is the
fixed-point subgroup of the range of `MulDistribMulAction.toMulAut S Γ`. -/
@[simp]
theorem FixedPoints.subgroup_range_toMulAut (S : Type v) (Γ : Type w) [Group S] [Group Γ]
    [MulDistribMulAction S Γ] :
    FixedPoints.subgroup (MulDistribMulAction.toMulAut S Γ).range Γ = FixedPoints.subgroup S Γ := by
  ext g
  simp [FixedPoints.mem_subgroup, Subgroup.smul_def]
