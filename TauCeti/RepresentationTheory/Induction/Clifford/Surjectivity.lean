/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.RepresentationTheory.Induction.Clifford.Injectivity` is imported publicly: it
-- re-exports `TauCeti.inertia`, `TauCeti.le_inertia`, `FDRep.LiesOver`, `TauCeti.indFDRep` and
-- `TauCeti.resFDRep`, all of which occur in the statement below, together with
-- `FDRep.simple_indFDRep_of_inertia`, the irreducibility of the induced representation that the
-- proof uses to upgrade a nonzero intertwiner to an isomorphism.
public import TauCeti.RepresentationTheory.Induction.Clifford.Injectivity
-- Non-public: the enumeration `TauCeti.irreducibleRepresentation` of the irreducible
-- representations of the inertia group, and the expansion of a class function in the basis of
-- irreducible characters, are used only inside the proof.
import TauCeti.RepresentationTheory.CharacterTable.Table
-- Non-public: `TauCeti.finrank_hom_indFDRep`, Frobenius reciprocity as an identity of intertwining
-- dimensions, is the engine of the proof and occurs in no statement.
import TauCeti.RepresentationTheory.Induction.FrobeniusReciprocity

/-!
# Surjectivity in the Clifford correspondence

Let `N` be a normal subgroup of a finite group `G`, let `V` be an irreducible representation of
`N` over an algebraically closed field of characteristic zero, and let `T = inertia V` be its
inertia group.  `TauCeti/RepresentationTheory/Induction/Clifford/Correspondence.lean` shows that
induction from `T` carries an irreducible representation **lying over `V`** to an irreducible
representation of `G`, and `Injectivity.lean` shows that it does so injectively on isomorphism
classes.  This file proves that it is also **surjective**: every irreducible representation of `G`
lying over `V` is induced from an irreducible representation of `T` lying over `V`.  With the two
earlier halves this completes the Clifford correspondence `Irr(T ∣ V) ≃ Irr(G ∣ V)`, which reduces
the classification of the irreducible representations of `G` lying over `V` to the same
classification for the inertia group, a group in which `V` is stable under conjugation.

## Main statements

* `FDRep.exists_simple_liesOver_inertia_nonempty_iso_indFDRep`: **surjectivity in the Clifford
  correspondence**.  An irreducible representation of `G` lying over `V` is induced from an
  irreducible representation of the inertia group lying over `V`.  The inducing representation is
  unique up to isomorphism by `FDRep.nonempty_iso_of_liesOver_inertia_of_nonempty_iso_indFDRep`.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, AMS Chelsea (1976), Theorem 6.11.
* C. W. Curtis and I. Reiner, *Methods of Representation Theory, Vol. I*, Wiley (1981), §11.
-/

public section

open CategoryTheory

universe u

namespace FDRep

open TauCeti

section Restriction

variable {k G : Type u} [Field k] [Group G] {N : Subgroup G} [N.Normal]

/-- The restriction to `N` of a representation of the inertia group of `V`, along the inclusion
`N ≤ inertia V`.  This is the shape in which `FDRep.LiesOver` reads the restriction of a
representation of the inertia group; it is not a `TauCeti.resFDRep`, the inclusion of `N` into
`inertia V` not being the inclusion of a subgroup of `N`. -/
private noncomputable abbrev resInertia (V : FDRep k N) (U : FDRep k (inertia V)) : FDRep k N :=
  (Action.res (FGModuleCat k) (Subgroup.inclusion (le_inertia V))).obj U

/-- The character of a restriction to `N` is the character of the original representation, read at
the image of the argument in the inertia group. -/
private theorem character_resInertia (V : FDRep k N) (U : FDRep k (inertia V)) (n : N) :
    (resInertia V U).character n = U.character (Subgroup.inclusion (le_inertia V) n) :=
  rfl

end Restriction

section Surjectivity

variable {k G : Type u} [Field k] [Group G] [Finite G] [IsAlgClosed k] [CharZero k]
  {N : Subgroup G} [N.Normal]

/-- **Surjectivity in the Clifford correspondence.**  Let `N` be a normal subgroup of a finite
group `G` and let `V` be an irreducible representation of `N` over an algebraically closed field of
characteristic zero.  Every irreducible representation `W` of `G` lying over `V` is induced from an
irreducible representation of `inertia V` lying over `V`. -/
theorem exists_simple_liesOver_inertia_nonempty_iso_indFDRep
    (V : FDRep k N) [Simple V] (W : FDRep k G) [Simple W]
    (hW : W.LiesOver N.subtype V) :
    ∃ (U : FDRep k (inertia V)) (_ : Simple U),
      U.LiesOver (Subgroup.inclusion (le_inertia V)) V ∧ Nonempty (indFDRep U ≅ W) := by
  -- The proof is a character count, not a decomposition of the restriction.  Expanding the class
  -- function of `Res_T W` in the orthonormal basis of irreducible characters of `T = inertia V`
  -- gives `χ_W(t) = ∑ᵢ aᵢ · χ_{Uᵢ}(t)` with `aᵢ = dim Hom_T(Uᵢ, Res_T W)`; algebraic closedness is
  -- what makes that basis orthonormal, so that the multiplicities `aᵢ` are the pairings.
  -- Restricting the identity to `N` and pairing it with the character of `V` turns it into the
  -- identity of natural numbers `dim Hom_N(V, Res_N W) = ∑ᵢ aᵢ · dim Hom_N(V, Res_N Uᵢ)`, whose
  -- left-hand side is nonzero because `W` lies over `V`.  Some `Uᵢ` therefore lies over `V` and
  -- admits a nonzero intertwiner into `Res_T W`; Frobenius reciprocity
  -- (`TauCeti.finrank_hom_indFDRep`) moves that intertwiner to `Hom_G(Ind Uᵢ, W)`, and Schur's
  -- lemma makes it an isomorphism, `Ind Uᵢ` being irreducible by
  -- `FDRep.simple_indFDRep_of_inertia`.
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype N := Fintype.ofFinite N
  let _ : Fintype (inertia V) := Fintype.ofFinite _
  let _ : Invertible (Nat.card N : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let _ : Invertible (Nat.card (inertia V) : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- The irreducible representations of the inertia group, as objects of `FDRep`.
  let U : Fin (Nat.card (ConjClasses (inertia V))) → FDRep k (inertia V) := fun i =>
    FDRep.of (irreducibleRepresentation k i)
  have hsimple : ∀ i, Simple (U i) := by
    intro i
    let _ : Representation.IsIrreducible (U i).ρ := by
      dsimp only [U, FDRep.of_ρ']
      infer_instance
    exact FDRep.simple_of_isIrreducible (U i)
  have hU : ∀ i, ClassFunction.ofCharacter (irreducibleRepresentation k i) =
      ClassFunction.ofFDRep (U i) := fun i => (ClassFunction.ofFDRep_eq_ofCharacter (U i)).symm
  -- The multiplicity of `U i` in the restriction of `W` to the inertia group, and the
  -- multiplicity of `V` in the restriction of `U i` to `N`.
  let a : Fin (Nat.card (ConjClasses (inertia V))) → ℕ := fun i =>
    Module.finrank k (U i ⟶ resFDRep (inertia V) W)
  let b : Fin (Nat.card (ConjClasses (inertia V))) → ℕ := fun i =>
    Module.finrank k (V ⟶ resInertia V (U i))
  -- The coefficients in the expansion of the restricted character are the multiplicities.
  have hcoeff : ∀ i, ClassFunction.characterPairing
      (ClassFunction.ofCharacter (irreducibleRepresentation k i))
      (ClassFunction.ofFDRep (resFDRep (inertia V) W)) = (a i : k) := by
    intro i
    rw [hU i, ClassFunction.characterPairing_symm,
      ClassFunction.characterPairing_ofFDRep_eq_finrank]
  -- Expand the character of `Res_T W` in the basis of irreducible characters of `T`.
  have hexp : ∀ t : (inertia V), W.character (t : G) = ∑ i, (a i : k) * (U i).character t := by
    intro t
    have hval := ClassFunction.apply_eq_sum_characterPairing_mul_character
      (irreducibleRepresentation (k := k) (G := (inertia V : Subgroup G)))
      (pairwise_isEmpty_equiv_irreducibleRepresentation k) (by simp)
      (ClassFunction.ofFDRep (resFDRep (inertia V) W)) t
    rw [ClassFunction.ofFDRep_apply, character_resFDRep] at hval
    refine hval.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [hcoeff i, ← ClassFunction.ofCharacter_apply (irreducibleRepresentation k i) t, hU i,
      ClassFunction.ofFDRep_apply]
  -- Pair the expansion, restricted to `N`, with the character of `V`.
  have hpair : (Module.finrank k (V ⟶ resFDRep N W) : k) = ∑ i, (a i : k) * (b i : k) := by
    have h1 : ClassFunction.characterPairing (ClassFunction.ofFDRep (resFDRep N W))
        (ClassFunction.ofFDRep V) = (Module.finrank k (V ⟶ resFDRep N W) : k) :=
      ClassFunction.characterPairing_ofFDRep_eq_finrank _ _
    have h2 : ∀ i, ClassFunction.characterPairing
        (ClassFunction.ofFDRep (resInertia V (U i)))
        (ClassFunction.ofFDRep V) = (b i : k) :=
      fun i => ClassFunction.characterPairing_ofFDRep_eq_finrank _ _
    have hchar : ∀ n : N,
        (resFDRep N W).character n = ∑ i, (a i : k) * (resInertia V (U i)).character n := by
      intro n
      have h := hexp (Subgroup.inclusion (le_inertia V) n)
      rw [Subgroup.coe_inclusion] at h
      rw [character_resFDRep]
      refine h.trans (Finset.sum_congr rfl fun i _ => ?_)
      rw [character_resInertia]
    rw [← h1, ClassFunction.characterPairing_ofFDRep]
    calc (Nat.card N : k)⁻¹ * ∑ n : N, (resFDRep N W).character n * V.character (n⁻¹)
        = (Nat.card N : k)⁻¹ * ∑ n : N, ∑ i, (a i : k) *
            ((resInertia V (U i)).character n * V.character (n⁻¹)) := by
          congr 1
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [hchar n, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i, (a i : k) * ((Nat.card N : k)⁻¹ * ∑ n : N,
            (resInertia V (U i)).character n * V.character (n⁻¹)) := by
          rw [Finset.sum_comm, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.mul_sum]
          ring
      _ = ∑ i, (a i : k) * (b i : k) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← ClassFunction.characterPairing_ofFDRep, h2 i]
  -- Read the identity back in the natural numbers, where the left-hand side is nonzero.
  have hnat : Module.finrank k (V ⟶ resFDRep N W) = ∑ i, a i * b i := by
    have hcast : ((Module.finrank k (V ⟶ resFDRep N W) : ℕ) : k) = ((∑ i, a i * b i : ℕ) : k) := by
      rw [hpair]
      push_cast
      ring
    exact_mod_cast hcast
  have hne : Module.finrank k (V ⟶ resFDRep N W) ≠ 0 := by
    obtain ⟨f, hf⟩ := liesOver_iff.mp hW
    intro hzero
    let _ := Module.finrank_zero_iff.mp hzero
    exact hf (Subsingleton.elim f 0)
  rw [hnat] at hne
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have ha : a i ≠ 0 := fun h => hi (by rw [h, Nat.zero_mul])
  have hb : b i ≠ 0 := fun h => hi (by rw [h, Nat.mul_zero])
  -- The `i`-th irreducible of the inertia group lies over `V`.
  have hliesover : (U i).LiesOver (Subgroup.inclusion (le_inertia V)) V := by
    have hnt : Nontrivial (V ⟶ resInertia V (U i)) := by
      rw [← not_subsingleton_iff_nontrivial]
      intro hsub
      exact hb Module.finrank_zero_of_subsingleton
    exact liesOver_iff.mpr (exists_ne 0)
  let _ : Simple (U i) := hsimple i
  let _ : Simple (indFDRep (U i)) := simple_indFDRep_of_inertia V (U i) hliesover
  refine ⟨U i, hsimple i, hliesover, ?_⟩
  by_contra hiso
  have hzero := CategoryTheory.finrank_hom_simple_simple_eq_zero_of_not_iso k
    (X := indFDRep (U i)) (Y := W) fun e => hiso ⟨e⟩
  rw [finrank_hom_indFDRep] at hzero
  exact ha hzero

end Surjectivity

end FDRep
