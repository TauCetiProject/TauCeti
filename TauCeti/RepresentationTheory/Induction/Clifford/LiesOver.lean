/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.FiniteDimensional.Unit
public import TauCeti.RepresentationTheory.Induction.Inertia

/-!
# Representations lying over a constituent

Given a homomorphism `φ : N →* H`, an `H`-representation `U` *lies over* an
`N`-representation `V` when there is a nonzero intertwiner from `V` to the restriction of `U`
along `φ`.  For simple `V` in the semisimple setting, this says that `V` occurs as a constituent
of the restriction.

The main result says that this property is preserved by induction from a finite-index subgroup.
For a normal subgroup `N` and its inertia group `inertia V`, this supplies the forward map in the
Clifford correspondence: inducing a representation of `inertia V` lying over `V` gives a
representation of the ambient group that still lies over `V`.

## Main definitions

* `FDRep.LiesOver`: occurrence in a restriction, expressed by a nonzero intertwiner.

## Main statements

* `FDRep.LiesOver.indFDRep`: induction preserves lying over along the composite homomorphism.
* `FDRep.liesOver_indFDRep_of_inertia`: the inertia-group specialization.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Theorem 6.11.
* C. W. Curtis and I. Reiner, *Methods of Representation Theory, Vol. I*, §11.
-/

public section

open CategoryTheory

universe u

namespace FDRep

open TauCeti

variable {k N H G : Type u} [Field k] [Group N] [Group H] [Group G]

/-- An `H`-representation lies over an `N`-representation along `φ : N →* H` when the
smaller representation admits a nonzero intertwiner into the restriction of the larger one.

The body is exposed so that downstream modules can destructure and build `LiesOver` directly. -/
@[expose] def LiesOver (U : FDRep k H) (φ : N →* H) (V : FDRep k N) : Prop :=
  ∃ f : V ⟶ (Action.res (FGModuleCat k) φ).obj U, f ≠ 0

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
  have hv' : f v = 0 := indFDRepUnit_injective A (hv.trans hmapzero.symm)
  exact hv'

section Inertia

variable {N : Subgroup G} [N.Normal]

/-- Inducing from the inertia group preserves occurrence of the chosen normal-subgroup
constituent.  This is the "lies over" half of the forward map in the Clifford correspondence. -/
theorem liesOver_indFDRep_of_inertia (V : FDRep k N) [(inertia V).FiniteIndex]
    (U : FDRep k (inertia V))
    (h : U.LiesOver (Subgroup.inclusion (le_inertia V)) V) :
    (indFDRep U).LiesOver N.subtype V := by
  have hInd := h.indFDRep
  have hcomp : (inertia V).subtype.comp (Subgroup.inclusion (le_inertia V)) = N.subtype := by
    ext
    rfl
  rw [hcomp] at hInd
  exact hInd

end Inertia

end FDRep
