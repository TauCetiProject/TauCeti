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

* `FDRep.liesOver_iff`, `FDRep.liesOver_of_ne_zero`, `FDRep.LiesOver.exists_ne_zero`: the
  characterisation by nonzero intertwiners.
* `FDRep.LiesOver.of_iso_left`, `FDRep.LiesOver.of_iso_right`: transport across isomorphisms.
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

/-- A nonzero intertwiner `V ⟶ Res_φ U` witnesses that `U` lies over `V`. -/
theorem liesOver_of_ne_zero {f : V ⟶ (Action.res (FGModuleCat k) φ).obj U} (hf : f ≠ 0) :
    U.LiesOver φ V :=
  ⟨f, hf⟩

/-- If `U` lies over `V` along `φ`, some intertwiner `V ⟶ Res_φ U` is nonzero. -/
theorem LiesOver.exists_ne_zero (h : U.LiesOver φ V) :
    ∃ f : V ⟶ (Action.res (FGModuleCat k) φ).obj U, f ≠ 0 :=
  h

/-- Lying over is invariant under isomorphism of the larger representation. -/
theorem LiesOver.of_iso_left {U' : FDRep k H} (e : U ≅ U') (h : U.LiesOver φ V) :
    U'.LiesOver φ V := by
  obtain ⟨f, hf⟩ := h.exists_ne_zero
  refine liesOver_of_ne_zero (f := f ≫ ((Action.res (FGModuleCat k) φ).mapIso e).hom) ?_
  intro hzero
  exact hf ((cancel_mono ((Action.res (FGModuleCat k) φ).mapIso e).hom).mp
    (hzero.trans Limits.zero_comp.symm))

/-- Lying over is invariant under isomorphism of the smaller representation. -/
theorem LiesOver.of_iso_right {V' : FDRep k N} (e : V ≅ V') (h : U.LiesOver φ V) :
    U.LiesOver φ V' := by
  obtain ⟨f, hf⟩ := h.exists_ne_zero
  refine liesOver_of_ne_zero (f := e.inv ≫ f) ?_
  intro hzero
  exact hf ((cancel_epi e.inv).mp (hzero.trans Limits.comp_zero.symm))

end Defs

section Induction

variable {k G : Type u} {N : Type v} [Field k] [Group G] [Group N]

/-- **Induction preserves lying over.** If `A` lies over `V` along `φ : N →* S`, then
`Ind_S^G A` lies over `V` along the composite `N → S → G`. -/
theorem LiesOver.indFDRep {S : Subgroup G} [S.FiniteIndex] {A : FDRep k S}
    {φ : N →* S} {V : FDRep k N} (h : A.LiesOver φ V) :
    (indFDRep A).LiesOver (S.subtype.comp φ) V := by
  obtain ⟨f, hf⟩ := h.exists_ne_zero
  let η := (Action.res (FGModuleCat k) φ).map (indFDRepUnit A)
  refine liesOver_of_ne_zero (f := f ≫ η) fun hzero => hf ?_
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
