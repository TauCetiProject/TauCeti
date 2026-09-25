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
-- Non-public: `FDRep.finrank_hom_eq_sum_of_character_eq`, which reads multiplicities off an
-- identity of characters, is used only inside the proof.
import TauCeti.RepresentationTheory.CharacterTable.Determined
-- Non-public: the enumeration `TauCeti.irreducibleRepresentation` of the irreducible
-- representations of the inertia group, and the expansion
-- `TauCeti.character_eq_sum_nsmul_irreducibleCharacter` of a character over them, are used only
-- inside the proof.
import TauCeti.RepresentationTheory.CharacterTable.VirtualCharacter
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

/-- **Hom-space dimensions through the inertia group.**  Write `Uᵢ` for the irreducible
representations of `T = inertia V`.  Then `dim Hom_N(V, Res_N W) = ∑ᵢ aᵢ · bᵢ`, where
`aᵢ = dim Hom_T(Uᵢ, Res_T W)` is the multiplicity of `Uᵢ` in `Res_T W` and
`bᵢ = dim Hom_N(V, Res_N Uᵢ)`.  When `V` is simple these dimensions are multiplicities. -/
private theorem finrank_hom_resFDRep_eq_sum (V : FDRep k N) (W : FDRep k G)
    [Invertible (Nat.card (inertia V) : k)] : Module.finrank k (V ⟶ resFDRep N W) =
      ∑ i, Module.finrank k (FDRep.of (irreducibleRepresentation k i) ⟶ resFDRep (inertia V) W) *
        Module.finrank k (V ⟶ resInertia V (FDRep.of (irreducibleRepresentation k i))) := by
  let _ : Fintype (inertia V) := Fintype.ofFinite _
  -- Restricted to `N`, the expansion of the character of `Res_T W` in the irreducible characters
  -- of `T` is an expansion of the character of `Res_N W`: read `χ_{Res_N W}` at `n` as
  -- `χ_{Res_T W}` at the image `t` of `n` in `T`, and expand the latter.
  refine finrank_hom_eq_sum_of_character_eq V <| funext fun n => ?_
  rw [show (resFDRep N W).character n =
        (resFDRep (inertia V) W).character (Subgroup.inclusion (le_inertia V) n) from rfl,
    character_eq_sum_nsmul_irreducibleCharacter, Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- The character of `Res_N Uᵢ` at `n` is `χᵢ(t)`, and the coefficient `dim Hom_T(Res_T W, Uᵢ)`
  -- is `dim Hom_T(Uᵢ, Res_T W)`: both are the pairing of `χᵢ` and `χ_{Res_T W}`, in the two orders.
  rw [Pi.smul_apply, Pi.smul_apply, character_resInertia, nsmul_eq_mul, nsmul_eq_mul,
    ← character_irreducibleRepresentation,
    ← ClassFunction.characterPairing_ofCharacter_eq_finrank,
    ← ClassFunction.characterPairing_ofFDRep_eq_finrank, ClassFunction.characterPairing_symm,
    ClassFunction.ofFDRep_eq_ofCharacter, ClassFunction.ofFDRep_eq_ofCharacter (FDRep.of _),
    FDRep.of_ρ']
  -- The one definitional step left, `χ_ρ(t) = χ_{FDRep.of ρ}(t)`, unfolds `FDRep.of` and no
  -- restriction wrapper: neither Mathlib nor Tau Ceti states the character of `FDRep.of ρ`.
  rfl

/-- An irreducible representation `U` of `inertia V` lying over `V` induces to `W` as soon as it
occurs in the restriction of the irreducible representation `W` to `inertia V`. -/
private theorem nonempty_iso_indFDRep_of_finrank_hom_ne_zero (V : FDRep k N) [Simple V]
    (W : FDRep k G) [Simple W] (U : FDRep k (inertia V)) [Simple U]
    (hU : U.LiesOver (Subgroup.inclusion (le_inertia V)) V)
    (hne : Module.finrank k (U ⟶ resFDRep (inertia V) W) ≠ 0) : Nonempty (indFDRep U ≅ W) := by
  have := simple_indFDRep_of_inertia V U hU
  -- Frobenius reciprocity moves the nonzero multiplicity to `Hom_G(Ind U, W)`, and Schur's lemma
  -- makes a nonzero intertwiner between the irreducibles `Ind U` and `W` an isomorphism.
  rw [← finrank_hom_indFDRep] at hne
  by_contra hiso
  exact hne <| finrank_hom_simple_simple_eq_zero_of_not_iso k fun e => hiso ⟨e⟩

/-- **Surjectivity in the Clifford correspondence.**  Let `N` be a normal subgroup of a finite
group `G` and let `V` be an irreducible representation of `N` over an algebraically closed field of
characteristic zero.  Every irreducible representation `W` of `G` lying over `V` is induced from an
irreducible representation of `inertia V` lying over `V`. -/
theorem exists_simple_liesOver_inertia_nonempty_iso_indFDRep
    (V : FDRep k N) [Simple V] (W : FDRep k G) [Simple W]
    (hW : W.LiesOver N.subtype V) :
    ∃ (U : FDRep k (inertia V)) (_ : Simple U),
      U.LiesOver (Subgroup.inclusion (le_inertia V)) V ∧ Nonempty (indFDRep U ≅ W) := by
  -- The proof is a character count, not a decomposition of the restriction.  The multiplicity of
  -- `V` in `Res_N W` is nonzero because `W` lies over `V`, and by `finrank_hom_resFDRep_eq_sum` it
  -- is `∑ᵢ aᵢ · bᵢ`.  Some irreducible `Uᵢ` of `T = inertia V` therefore lies over `V` and occurs
  -- in `Res_T W`, so it induces to `W`.
  let _ : Invertible (Nat.card (inertia V) : k) := invertibleOfNonzero (NeZero.ne _)
  obtain ⟨f, hf⟩ := liesOver_iff.mp hW
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero <|
    (finrank_hom_resFDRep_eq_sum V W).symm.trans_ne fun h =>
      hf <| @Subsingleton.elim _ (Module.finrank_zero_iff.mp h) f 0
  obtain ⟨ha, hb⟩ := mul_ne_zero_iff.mp hi
  let U : FDRep k (inertia V) := FDRep.of (irreducibleRepresentation k i)
  have : Representation.IsIrreducible U.ρ := by
    dsimp only [U, FDRep.of_ρ']
    infer_instance
  -- `U` lies over `V`, the multiplicity of `V` in `Res_N U` being nonzero.
  have hliesover : U.LiesOver (Subgroup.inclusion (le_inertia V)) V :=
    have := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hb)
    liesOver_iff.mpr (exists_ne 0)
  exact ⟨U, inferInstance, hliesover,
    nonempty_iso_indFDRep_of_finrank_hom_ne_zero V W U hliesover ha⟩

end Surjectivity

end FDRep
