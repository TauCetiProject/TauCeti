/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Character
public import TauCeti.RepresentationTheory.LinearCharacter
public import Mathlib.GroupTheory.Nilpotent
import TauCeti.GroupTheory.Nilpotent
import TauCeti.RepresentationTheory.CharacterTable.Determined
import TauCeti.RepresentationTheory.Induction.Clifford.Basic
import TauCeti.RepresentationTheory.Induction.Clifford.Surjectivity

/-!
# Irreducible representations of nilpotent groups are monomial

Over an algebraically closed field of characteristic zero, every irreducible representation of a
finite nilpotent group `G` is induced from a one-dimensional representation of a subgroup: there
are a subgroup `H` and a linear character `χ : H →* kˣ` with

`W ≅ Ind_H^G χ`, equivalently `χ_W = Ind_H^G χ`.

In the classical language, finite nilpotent groups are *M-groups*.  The elementary groups of
Brauer's induction theorem are nilpotent (`TauCeti.IsElementary.isNilpotent`), so their irreducible
characters are induced from linear characters, whose values are roots of unity; this is how
Brauer's theorem is sharpened to a statement about fields of definition.

## The argument

The proof is by induction on `|G|`.  Let `W` be irreducible.

* If the operators `W.ρ g` commute pairwise, Schur's lemma makes each of them a scalar, `W` is a
  line, and its character is a linear character of `G = ⊤`.
* Otherwise let `K` be the kernel of `W` and `Z = upperCentralSeriesStep K` the elements acting
  centrally.  As `G` is nilpotent and `Z ≠ ⊤`, some `x` lies one step above `Z` but not in `Z`
  (`TauCeti.lt_upperCentralSeriesStep`), and the normal closure `A` of `x` acts through pairwise
  commuting operators (`TauCeti.commutator_normalClosure_singleton_le`).
* Choose an irreducible constituent `V` of `Res_A W`.  Schur's lemma makes `A` act on `V` by
  scalars.  If the inertia group of `V` were all of `G`, those scalars would be invariant under
  conjugation and `A` would act on all of `W` by them
  (`Representation.apply_eq_smul_of_ne_bot`); then `x` would act centrally, that is
  `x ∈ Z`.  So the inertia group `T` is proper.
* By the Clifford correspondence (`FDRep.exists_simple_liesOver_inertia_nonempty_iso_indFDRep`)
  `W ≅ Ind_T^G U` for an irreducible `U` of `T`, and `T` is nilpotent and smaller, so
  `χ_U = Ind_L^T χ` by induction.  Transitivity of induction
  (`TauCeti.indClassFun_indClassFun_subgroupOf`) finishes.

## Main statements

* `FDRep.exists_character_eq_indClassFun_of_isNilpotent`: the character of an irreducible
  representation of a finite nilpotent group is induced from a linear character of a subgroup.
* `FDRep.exists_nonempty_iso_indFDRep_ofLinearCharacter_of_isNilpotent`: the representation
  itself is induced from a one-dimensional representation of a subgroup.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), §8.5.
* I. M. Isaacs, *Character Theory of Finite Groups*, AMS Chelsea (1976), Chapter 6.
-/

public section

open CategoryTheory
open scoped commutatorElement

universe u

namespace FDRep

open TauCeti

variable {k G : Type u} [Field k] [Group G]

/-- **A representation whose operators commute is a linear character.**  Over an algebraically
closed field, if the operators of an irreducible representation `W` commute pairwise, Schur's lemma
makes each a scalar, so `W` is a line and its character is the linear character of those scalars,
here read as induced from `⊤`. -/
private theorem exists_character_eq_indClassFun_top [IsAlgClosed k] (W : FDRep k G) [Simple W]
    (hcomm : ∀ g h : G, Commute (W.ρ g) (W.ρ h)) :
    ∃ χ : (⊤ : Subgroup G) →* kˣ, W.character = indClassFun ⊤ fun h => (χ h : k) := by
  have hW := FDRep.isIrreducible_of_simple W
  have : Nontrivial W := hW.nontrivial
  choose c hc using fun g => hW.exists_forall_apply_eq_smul (W.ρ g) fun h v => by
    rw [← Module.End.mul_apply, (hcomm g h).eq, Module.End.mul_apply]
  obtain ⟨v, hv⟩ := exists_ne (0 : W)
  have hmul (g h : G) : c (g * h) = c g * c h := by
    refine smul_left_injective k hv ?_
    dsimp only
    rw [← hc, map_mul, Module.End.mul_apply, hc h, map_smul, hc g, smul_smul, mul_comm]
  have hone : c 1 = 1 := smul_left_injective k hv (by simp [← hc])
  -- The line through `v` is stable, hence everything: `W` is one-dimensional.
  let line : Subrepresentation W.ρ :=
    ⟨k ∙ v, fun g w hw => by
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [map_smul, hc, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)⟩
  have hline : line = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top line).resolve_left fun h => hv <| by
    have hmem : v ∈ line.toSubmodule := Submodule.mem_span_singleton_self v
    rw [h] at hmem
    exact hmem
  have hfin : Module.finrank k W = 1 :=
    (finrank_eq_one_iff_of_nonzero v hv).mpr (congrArg Subrepresentation.toSubmodule hline)
  let χ : G →* k := { toFun := c, map_one' := hone, map_mul' := hmul }
  refine ⟨χ.toHomUnits.comp (⊤ : Subgroup G).subtype, funext fun g => ?_⟩
  rw [indClassFun_top (ClassFunction.comp_monoidHom_mem _ Units.val)]
  have hρ : W.ρ g = c g • LinearMap.id := LinearMap.ext (hc g)
  simp [χ, character, hρ, hfin]

/-- **A constituent with full inertia forces central action.**  Let `A` be a normal subgroup
acting on an irreducible `W` through commuting operators, and let `σ` be an irreducible constituent
of the restriction.  Schur's lemma makes `A` act on `σ` through scalars; if the inertia group of `σ`
is all of `G`, those scalars are invariant under conjugation, so `A` acts on all of `W` through them
(`Representation.apply_eq_smul_of_ne_bot`), and its operators commute with those of `G`. -/
private theorem commute_of_inertia_eq_top [IsAlgClosed k] (W : FDRep k G) [Simple W]
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

/-- **The character of an irreducible representation of a finite nilpotent group is monomial.**
Over an algebraically closed field of characteristic zero, for every irreducible representation
`W` of a finite nilpotent group `G` there are a subgroup `H` and a linear character `χ` of `H`
with `χ_W = Ind_H^G χ`. -/
theorem exists_character_eq_indClassFun_of_isNilpotent [IsAlgClosed k] [CharZero k] [Finite G]
    [Group.IsNilpotent G] (W : FDRep k G) [Simple W] :
    ∃ (H : Subgroup G) (χ : H →* kˣ), W.character = indClassFun H fun h => (χ h : k) := by
  obtain ⟨n, hn⟩ : ∃ n, Nat.card G = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing G with
  | _ n ih =>
  by_cases hcomm : ∀ g h : G, Commute (W.ρ g) (W.ρ h)
  · obtain ⟨χ, hχ⟩ := exists_character_eq_indClassFun_top W hcomm
    exact ⟨⊤, χ, hχ⟩
  have hW := FDRep.isIrreducible_of_simple W
  have : Nontrivial W := hW.nontrivial
  -- `Z`, the elements acting centrally, is proper; `x` lies one step above it.
  have hZ : Subgroup.upperCentralSeriesStep W.ρ.ker ≠ ⊤ := fun h =>
    hcomm fun g h' => W.ρ.commutatorElement_mem_ker_iff.mp <|
      (Subgroup.mem_upperCentralSeriesStep _ g).mp (h ▸ Subgroup.mem_top g) h'
  obtain ⟨x, hx, hxZ⟩ := IsConcreteLE.exists_of_lt (lt_upperCentralSeriesStep hZ)
  -- The normal closure `A` of `x` acts through commuting operators.
  let A := Subgroup.normalClosure ({x} : Set G)
  have hA (a b : A) : Commute (W.ρ a) (W.ρ b) :=
    W.ρ.commutatorElement_mem_ker_iff.mp <|
      commutator_normalClosure_singleton_le hx (Subgroup.commutator_mem_commutator a.2 b.2)
  obtain ⟨σ, hσ⟩ := Representation.exists_isAtom (W.ρ.comp A.subtype)
  let V : FDRep k A := FDRep.of σ.toRepresentation
  have hV : Representation.IsIrreducible V.ρ :=
    Representation.isIrreducible_toRepresentation_of_isAtom hσ
  have : Simple V := FDRep.simple_of_isIrreducible V
  -- The inertia group of `V` is proper, as otherwise `x` would act centrally.
  have hT : inertia V ≠ ⊤ := fun hT => hxZ fun g => W.ρ.commutatorElement_mem_ker_iff.mpr <|
    commute_of_inertia_eq_top W hA hσ hT ⟨x, Subgroup.subset_normalClosure rfl⟩ g
  -- Clifford: `W` is induced from an irreducible representation of the inertia group.
  obtain ⟨U, hU, -, ⟨e⟩⟩ := exists_simple_liesOver_inertia_nonempty_iso_indFDRep V W
    (liesOver_of_ne_bot W A.subtype hσ.1)
  have hcard : Nat.card (inertia V) < n :=
    hn ▸ (Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hT)).trans_eq Subgroup.card_top
  obtain ⟨L₀, χ, hχ⟩ := ih _ hcard U rfl
  obtain ⟨L, hLT, rfl⟩ : ∃ L ≤ inertia V, L.subgroupOf (inertia V) = L₀ :=
    ⟨L₀.map (inertia V).subtype, Subgroup.map_subtype_le L₀,
      Subgroup.comap_map_eq_self_of_injective (inertia V).subtype_injective L₀⟩
  refine ⟨L, χ.comp (Subgroup.subgroupOfEquivOfLe hLT).symm.toMonoidHom, ?_⟩
  rw [← char_iso e, ← indClassFun_ofFDRep_character, hχ,
    ← indClassFun_indClassFun_subgroupOf hLT (ClassFunction.comp_monoidHom_mem _ Units.val)]
  simp

/-- **Finite nilpotent groups are M-groups.**  Over an algebraically closed field of
characteristic zero, every irreducible representation of a finite nilpotent group is induced from
a one-dimensional representation of a subgroup. -/
theorem exists_nonempty_iso_indFDRep_ofLinearCharacter_of_isNilpotent [IsAlgClosed k] [CharZero k]
    [Finite G] [Group.IsNilpotent G] (W : FDRep k G) [Simple W] :
    ∃ (H : Subgroup G) (χ : H →* kˣ), Nonempty (W ≅ indFDRep (ofLinearCharacter χ)) := by
  obtain ⟨H, χ, hχ⟩ := exists_character_eq_indClassFun_of_isNilpotent W
  refine ⟨H, χ, nonempty_iso_of_character_eq _ _ ?_⟩
  rw [hχ, ← indClassFun_ofFDRep_character]
  exact congrArg (indClassFun H) (funext fun h => (char_ofLinearCharacter χ h).symm)

end FDRep
