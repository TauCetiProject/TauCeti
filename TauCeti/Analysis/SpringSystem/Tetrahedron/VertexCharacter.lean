/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpringSystem.Tetrahedron.Character
public import TauCeti.GroupTheory.Perm.PointStabilizer
import TauCeti.RepresentationTheory.CharacterTable.Determined
import TauCeti.RepresentationTheory.Induction.Permutation

/-!
# The tetrahedron displacement character on a vertex stabilizer

Label the complement of a vertex `i` in increasing order, using `Fin.permStabilizerEquiv`.
The displacement representation restricted to this copy of `S₃` has character `(12, 2, 0)`
on the identity, transpositions and three-cycles. It decomposes as three trivial lines,
one sign line and four standard two-dimensional representations.

The resulting equivalence is obtained from character recognition over `ℝ`; it does not choose
individual modes within the multiplicity spaces. In particular the multiplicity of the trivial
representation is three, in agreement with the breathing, translation and vibration seeds.

## References

* A. Knutson, *Group theory in physics: an example*, tetrahedron handout for Math 261
  (Cornell, 2001), pp. 3–5.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, §2.3.
-/

public section

namespace TauCeti

open Equiv

/-- The displacement representation restricted to the stabilizer of `i`, with the remaining
three vertices labelled in increasing order. -/
noncomputable def tetrahedronVertexRestriction (i : Fin 4) :
    Representation ℝ (Perm (Fin 3)) (Fin 4 × Fin 3 → ℝ) :=
  tetrahedronDisplacementRep.comp
    ((MulAction.stabilizer (Perm (Fin 4)) i).subtype.comp i.permStabilizerEquiv.toMonoidHom)

/-- The restricted action is the original displacement action of the permutation fixing `i`. -/
@[simp]
theorem tetrahedronVertexRestriction_apply (i : Fin 4) (σ : Perm (Fin 3))
    (u : Fin 4 × Fin 3 → ℝ) :
    tetrahedronVertexRestriction i σ u =
      tetrahedronDisplacementRep (i.permStabilizerEquiv σ) u := (rfl)

/-- If a permutation of the other three vertices fixes `f` of them, the displacement character
is `(f + 1) f`: the distinguished vertex supplies one additional fixed point. -/
theorem char_tetrahedronVertexRestriction (i : Fin 4) (σ : Perm (Fin 3)) :
    (tetrahedronVertexRestriction i).character σ =
      ((Nat.card {j : Fin 3 // σ j = j} : ℝ) + 1) * Nat.card {j : Fin 3 // σ j = j} := by
  classical
  have hcycle : (i.permStabilizerEquiv σ : Perm (Fin 4)).cycleType = σ.cycleType := by
    rw [Fin.coe_permStabilizerEquiv]
    exact Perm.cycleType_extendDomain _
  have h4 := (i.permStabilizerEquiv σ : Perm (Fin 4)).card_fixedPoints
  have h3 := σ.card_fixedPoints
  have hle := σ.sum_cycleType_le
  rw [← Nat.card_eq_fintype_card] at h4 h3
  simp only [Fintype.card_fin] at h4 h3 hle
  rw [hcycle] at h4
  dsimp only [Function.fixedPoints, Function.IsFixedPt, Set.coe_ofPred] at h4 h3
  have hc : Nat.card {j : Fin 4 // (i.permStabilizerEquiv σ : Perm (Fin 4)) j = j} =
      Nat.card {j : Fin 3 // σ j = j} + 1 := by
    rw [h4, h3]
    omega
  -- The character of restriction is the trace of the same operator.
  have h := char_tetrahedronDisplacementRep (i.permStabilizerEquiv σ)
  rw [hc, Nat.cast_add, Nat.cast_one] at h
  simpa only [Representation.character, tetrahedronVertexRestriction, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype, add_sub_cancel_right] using h

/-- On a vertex stabilizer, the character is `3 · 1 + sgn + 4 · χ_std`. -/
theorem char_tetrahedronVertexRestriction_eq (i : Fin 4) (σ : Perm (Fin 3)) :
    (tetrahedronVertexRestriction i).character σ =
      3 + (Representation.ofLinearCharacter (signLinearCharacter ℝ (Fin 3))).character σ +
        4 * (standardRepresentation ℝ (Fin 3)).character σ := by
  rw [char_tetrahedronVertexRestriction, Representation.char_ofLinearCharacter,
    coe_signLinearCharacter_apply, char_standardRepresentation, char_ofMulAction]
  simp only [Perm.smul_def, Nat.card_eq_fintype_card]
  have h : ∀ τ : Perm (Fin 3),
      ((Fintype.card {j : Fin 3 // τ j = j} : ℤ) + 1) *
          Fintype.card {j : Fin 3 // τ j = j} =
        3 + (τ.sign : ℤ) + 4 * ((Fintype.card {j : Fin 3 // τ j = j} : ℤ) - 1) := by
    decide
  exact_mod_cast h σ

/-- A transposition in a vertex stabilizer has displacement character two. -/
@[simp]
theorem char_tetrahedronVertexRestriction_swap (i : Fin 4) {a b : Fin 3} (hab : a ≠ b) :
    (tetrahedronVertexRestriction i).character (swap a b) = 2 := by
  rw [char_tetrahedronVertexRestriction]
  have hc : Nat.card {j : Fin 3 // swap a b j = j} = 1 := by
    rw [Nat.card_eq_fintype_card]
    fin_cases a <;> fin_cases b <;> first | exact (hab rfl).elim | decide
  rw [hc]
  norm_num

/-- A three-cycle in a vertex stabilizer has displacement character zero. -/
@[simp]
theorem char_tetrahedronVertexRestriction_finRotate (i : Fin 4) :
    (tetrahedronVertexRestriction i).character (finRotate 3) = 0 := by
  rw [char_tetrahedronVertexRestriction]
  have hc : Nat.card {j : Fin 3 // finRotate 3 j = j} = 0 := by
    rw [Nat.card_eq_fintype_card]
    decide
  norm_num [hc]

/-- The restriction to any vertex stabilizer is `1³ ⊕ sgn ⊕ std⁴` as a real representation.
Character recognition gives existence of an equivalence, without choosing bases of multiplicity
spaces or asserting that every equivariant operator is scalar on those spaces. -/
theorem nonempty_equiv_tetrahedronVertexRestriction (i : Fin 4) :
    Nonempty (((Representation.trivial ℝ (Perm (Fin 3)) (Fin 3 → ℝ)).prod
      ((Representation.ofLinearCharacter (signLinearCharacter ℝ (Fin 3))).prod
        ((standardRepresentation ℝ (Fin 3)).prod
          ((standardRepresentation ℝ (Fin 3)).prod
            ((standardRepresentation ℝ (Fin 3)).prod
              (standardRepresentation ℝ (Fin 3))))))).Equiv
      (tetrahedronVertexRestriction i)) := by
  apply Representation.nonempty_equiv_of_character_eq
  funext σ
  simp only [Representation.char_prod, Representation.char_trivial,
    Module.finrank_pi, Fintype.card_fin, Nat.cast_ofNat]
  rw [char_tetrahedronVertexRestriction_eq]
  ring

end TauCeti
