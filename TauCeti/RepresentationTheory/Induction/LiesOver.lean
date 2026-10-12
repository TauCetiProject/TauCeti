/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.FiniteDimensional.Unit

/-!
# Representations lying over a constituent

Given a homomorphism `φ : N →* H`, an `H`-representation `U` *lies over* an
`N`-representation `V` when there is a nonzero intertwiner from `V` to the restriction of `U`
along `φ`.  For simple `V` in the semisimple setting, this says that `V` occurs as a constituent
of the restriction.

The predicate is invariant under isomorphism of either representation, and the main result says
that it is preserved by induction from a finite-index subgroup: if `A` lies over `V` along
`φ : N →* S`, then `Ind_S^G A` lies over `V` along `N → S → G`.  The witness is the composite of
the given intertwiner with the unit `FDRep.indFDRepUnit`, which is injective.

## Main definitions

* `FDRep.LiesOver`: occurrence in a restriction, expressed by a nonzero intertwiner.

## Main statements

* `FDRep.liesOver_iff`: the characterisation by nonzero intertwiners.
* `FDRep.LiesOver.of_iso_left`, `FDRep.LiesOver.of_iso_right`: transport across isomorphisms.
* `FDRep.liesOver_res_self`: a nontrivial representation lies over its own restriction.
* `FDRep.LiesOver.of_res_iso`: transport across isomorphisms of restrictions.
* `FDRep.liesOver_of_ne_bot`: a representation lies over each nonzero subrepresentation of its
  restriction.
* `FDRep.LiesOver.indFDRep`: induction preserves lying over along the composite homomorphism.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Theorem 6.11.
* C. W. Curtis and I. Reiner, *Methods of Representation Theory, Vol. I*, §11.
-/

public section

open CategoryTheory

universe u v w

namespace FDRep

open TauCeti

section Defs

variable {k : Type u} {N : Type v} {H : Type w} [Field k] [Group N] [Group H]

/-- An `H`-representation lies over an `N`-representation along `φ : N →* H` when the
smaller representation admits a nonzero intertwiner into the restriction of the larger one. -/
def LiesOver (U : FDRep k H) (φ : N →* H) (V : FDRep k N) : Prop :=
  ∃ f : V ⟶ (Action.res (FGModuleCat k) φ).obj U, f ≠ 0

variable {U : FDRep k H} {φ : N →* H} {V : FDRep k N}

/-- `U` lies over `V` along `φ` exactly when some intertwiner `V ⟶ Res_φ U` is nonzero. -/
theorem liesOver_iff :
    U.LiesOver φ V ↔ ∃ f : V ⟶ (Action.res (FGModuleCat k) φ).obj U, f ≠ 0 :=
  Iff.rfl

/-- A nontrivial representation lies over its own restriction along any homomorphism. -/
theorem liesOver_res_self (U : FDRep k H) (φ : N →* H) [Nontrivial U] :
    U.LiesOver φ ((Action.res (FGModuleCat k) φ).obj U) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : U)
  refine ⟨𝟙 _, fun h => hx ?_⟩
  exact ConcreteCategory.congr_hom h x

/-- Lying over transfers along an isomorphism of the restricted larger representations. -/
theorem LiesOver.of_res_iso {U' : FDRep k H} (h : U.LiesOver φ V)
    (e : (Action.res (FGModuleCat k) φ).obj U ≅
      (Action.res (FGModuleCat k) φ).obj U') : U'.LiesOver φ V := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f ≫ e.hom, fun hzero => hf ?_⟩
  exact (cancel_mono e.hom).mp (hzero.trans Limits.zero_comp.symm)

/-- Lying over is invariant under isomorphism of the larger representation. -/
theorem LiesOver.of_iso_left {U' : FDRep k H} (h : U.LiesOver φ V) (e : U ≅ U') :
    U'.LiesOver φ V :=
  h.of_res_iso ((Action.res (FGModuleCat k) φ).mapIso e)

/-- Lying over is invariant under isomorphism of the smaller representation. -/
theorem LiesOver.of_iso_right {V' : FDRep k N} (h : U.LiesOver φ V) (e : V ≅ V') :
    U.LiesOver φ V' := by
  obtain ⟨f, hf⟩ := h
  refine ⟨e.inv ≫ f, ?_⟩
  intro hzero
  exact hf ((cancel_epi e.inv).mp (hzero.trans Limits.comp_zero.symm))

/-- **A representation lies over each of its nonzero subrepresentations.**  If `σ` is a nonzero
subrepresentation of the restriction of `U` along `φ`, then `U` lies over `σ` regarded as a
representation, the witness being the inclusion of `σ`. -/
theorem liesOver_of_ne_bot (U : FDRep k H) (φ : N →* H) {σ : Subrepresentation (U.ρ.comp φ)}
    (hσ : σ ≠ ⊥) : U.LiesOver φ (FDRep.of σ.toRepresentation) := by
  -- Both forgetful images carry the actions `σ.toRepresentation` and `U.ρ.comp φ` by definition,
  -- so the inclusion of `σ` intertwines them on the nose.
  let i : _root_.Representation.IntertwiningMap
      ((forget₂ (FDRep k N) (Rep k N)).obj (FDRep.of σ.toRepresentation)).ρ
      ((forget₂ (FDRep k N) (Rep k N)).obj ((Action.res (FGModuleCat k) φ).obj U)).ρ :=
    ⟨σ.toSubmodule.subtype, fun _ => rfl⟩
  refine ⟨FDRep.forget₂HomLinearEquiv _ _ (Rep.ofHom i), fun h => hσ ?_⟩
  refine Subrepresentation.toSubmodule_injective <| (Submodule.eq_bot_iff _).mpr fun v hv => ?_
  -- Evaluating `h` at `⟨v, hv⟩` gives `v = 0`: the morphism is the inclusion of `σ`, and neither
  -- `Rep.ofHom` nor `FDRep.forget₂HomLinearEquiv` changes the underlying function.
  exact ConcreteCategory.congr_hom h ⟨v, hv⟩

end Defs

section Induction

variable {k G : Type u} {N : Type v} [Field k] [Group G] [Group N]

/-- **Induction preserves lying over.** If `A` lies over `V` along `φ : N →* S`, then
`Ind_S^G A` lies over `V` along the composite `N → S → G`. -/
theorem LiesOver.indFDRep {S : Subgroup G} [S.FiniteIndex] {A : FDRep k S}
    {φ : N →* S} {V : FDRep k N} (h : A.LiesOver φ V) :
    (indFDRep A).LiesOver (S.subtype.comp φ) V := by
  obtain ⟨f, hf⟩ := h
  let η := (Action.res (FGModuleCat k) φ).map (indFDRepUnit A)
  refine ⟨f ≫ η, fun hzero => hf ?_⟩
  apply Action.Hom.ext
  ext v
  have hv := ConcreteCategory.congr_hom hzero v
  -- Restriction does not change the underlying linear map, but its carrier wrapper is opaque.
  change indFDRepUnit A (f v) = 0 at hv
  have hmapzero : indFDRepUnit A (0 : A) = 0 :=
    (indFDRepUnit A).hom.hom.hom.map_zero
  exact indFDRepUnit_injective A (hv.trans hmapzero.symm)

end Induction

end FDRep
