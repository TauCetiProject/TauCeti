/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Inertia
import TauCeti.RepresentationTheory.Induction.Clifford.Basic

/-!
# Constituents with full inertia

Let `A` be a normal subgroup of `G` acting on an irreducible representation `W` of `G` through
pairwise commuting operators, over an algebraically closed field.  By Schur's lemma, `A` acts on
each irreducible constituent `σ` of the restriction `Res_A W` through scalars.  If the inertia
group of `σ` is all of `G`, those scalars are invariant under conjugation, and `A` acts on all of
`W` through them: the operators of `A` are central among those of `G`.

This is the dichotomy behind the induction step in the proof that nilpotent groups are M-groups:
either a constituent of a commutative normal subgroup has proper inertia group, and Clifford
theory induces `W` from it, or that subgroup acts centrally.

## Main statements

* `FDRep.commute_of_inertia_eq_top`: if the inertia group of an irreducible constituent of the
  restriction of `W` to a normal subgroup `A` acting through commuting operators is all of `G`,
  then the operators of `A` commute with those of `G`.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 6.
-/

public section

open CategoryTheory

universe u

namespace FDRep

open TauCeti

variable {k G : Type u} [Field k] [Group G]

/-- **A constituent with full inertia forces central action.**  Let `A` be a normal subgroup
acting on an irreducible `W` through commuting operators, and let `σ` be an irreducible constituent
of the restriction.  Schur's lemma makes `A` act on `σ` through scalars; if the inertia group of `σ`
is all of `G`, those scalars are invariant under conjugation, so `A` acts on all of `W` through them
(`Representation.apply_eq_smul_of_ne_bot`), and its operators commute with those of `G`. -/
theorem commute_of_inertia_eq_top [IsAlgClosed k] (W : FDRep k G) [Simple W]
    {A : Subgroup G} [A.Normal] (hA : ∀ a b : A, Commute (W.ρ a) (W.ρ b))
    {σ : Subrepresentation (W.ρ.comp A.subtype)} (hσ : IsAtom σ)
    (hT : inertia (FDRep.of σ.toRepresentation) = ⊤) (a : A) (g : G) :
    Commute (W.ρ a) (W.ρ g) := by
  have hW := FDRep.isIrreducible_of_simple W
  let V : FDRep k A := FDRep.of σ.toRepresentation
  have hV : Representation.IsIrreducible V.ρ :=
    Representation.isIrreducible_toRepresentation_of_isAtom hσ
  have : Nontrivial V := hV.nontrivial
  -- `V.ρ b` acts on `σ` as `W.ρ b`, so `hA` says the operators of `V` commute.
  choose c hc using fun b : A => hV.exists_forall_apply_eq_smul (V.ρ b) fun b' w =>
    Subtype.ext (congrArg (fun f : Module.End k W => f w) (hA b b').eq)
  have hcσ (b : A) (w : W) (hw : w ∈ σ) : W.ρ b w = c b • w :=
    congrArg Subtype.val (hc b ⟨w, hw⟩)
  -- An isomorphism `{}^h V ≅ V` carries the scalar of `b` to that of its conjugate.
  have hconj (h : G) (b : A) : c (MulAut.conjNormal h b) = c b := by
    obtain ⟨e, he⟩ := mem_inertia_iff_exists_linearEquiv.mp (hT ▸ Subgroup.mem_top h)
    obtain ⟨w, hw⟩ := exists_ne (0 : V)
    have heb := he b w
    rw [hc, hc, map_smul] at heb
    exact (smul_left_injective k ((map_ne_zero_iff e e.injective).mpr hw) heb).symm
  have hscalar := Representation.apply_eq_smul_of_ne_bot W.ρ hσ.1 c hcσ hconj a
  exact LinearMap.ext fun w => by simp [hscalar]

end FDRep
