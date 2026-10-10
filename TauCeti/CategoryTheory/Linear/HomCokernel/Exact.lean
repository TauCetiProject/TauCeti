/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Linear.HomCokernel.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Exact.Basic

/-!
# The cocycle condition in a Hom cokernel

For an exact sequence `L → X → K → 0` and a morphism `i : K → P`,
precomposition embeds the cokernel of `Hom(P,Y) → Hom(K,Y)` in the cokernel of
`Hom(P,Y) → Hom(X,Y)`. Its image is precisely the kernel of restriction to `L`.
Thus passing from relations `X` to their image `K` imposes a cocycle condition on
the Hom cokernel. This allows arbitrary projective presentations to compute Ext¹,
including presentations whose relation map is not a monomorphism.

A morphism `X → Y` vanishing on `L` descends uniquely to `K`, as expressed by
Mathlib's `ShortComplex.Exact.desc`.
-/

public section

namespace TauCeti.HomCokernel

open CategoryTheory

universe u v t

variable (R : Type t) [Ring R] {C : Type u} [Category.{v} C] [Abelian C]
  [Linear R C] {S : ShortComplex C} {P Y : C}

/-- The Hom-cokernel sequence associated to an exact sequence ending in an epimorphism
is exact: a class restricting to zero comes from the cokernel on the quotient object. -/
theorem exact_precomp_restrict (hS : S.Exact) [Epi S.g] (i : S.X₃ ⟶ P) :
    Function.Exact (precomp R i S.g (Y := Y))
      (restrict R (S.g ≫ i) S.f (by simp)) := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ g =>
    constructor
    · intro hg
      have hfg : S.f ≫ g = 0 := by simpa using hg
      exact ⟨Submodule.Quotient.mk (hS.desc g hfg), by simp⟩
    · rintro ⟨y, hy⟩
      rw [← hy]
      induction y using Submodule.Quotient.induction_on with
      | _ a => simp [← Category.assoc]

/-- Replacing a relation object by its quotient identifies the resulting Hom cokernel
with the kernel of the cocycle restriction map. -/
noncomputable def equivKerRestrict (hS : S.Exact) [Epi S.g] (i : S.X₃ ⟶ P) :
    HomCokernel R i Y ≃ₗ[R]
      LinearMap.ker (restrict R (S.g ≫ i) S.f (Y := Y) (by simp)) :=
  LinearEquiv.ofBijective
    ((precomp R i S.g).codRestrict _ fun x ↦
      (exact_precomp_restrict R hS i).apply_apply_eq_zero x)
    ⟨fun _ _ h ↦ precomp_injective R i S.g (congrArg Subtype.val h), fun x ↦ by
      obtain ⟨y, hy⟩ := (exact_precomp_restrict R hS i x.val).mp x.property
      exact ⟨y, Subtype.ext hy⟩⟩

/-- The kernel comparison has precomposition as its underlying map. -/
@[simp]
theorem equivKerRestrict_apply (hS : S.Exact) [Epi S.g] (i : S.X₃ ⟶ P)
    (x : HomCokernel R i Y) :
    (equivKerRestrict R hS i x).val = precomp R i S.g x := (rfl)

/-- The inverse kernel comparison recovers a class from its precomposition. -/
@[simp]
theorem equivKerRestrict_symm_precomp (hS : S.Exact) [Epi S.g] (i : S.X₃ ⟶ P)
    (x : HomCokernel R i Y)
    (hx : restrict R (S.g ≫ i) S.f (by simp) (precomp R i S.g x) = 0) :
    (equivKerRestrict R hS i).symm ⟨precomp R i S.g x, hx⟩ = x :=
  (equivKerRestrict R hS i).symm_apply_apply x

end TauCeti.HomCokernel
