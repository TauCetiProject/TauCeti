/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Groupoid.ActionCategory.Basic
public import TauCeti.GroupTheory.TwistedConjugacy.Basic

/-!
# The twisted conjugacy groupoid

An arrow from `b` to `c` retains a conjugator `g` satisfying `c = g b σ(g)⁻¹`.
The automorphisms of `b` are its twisted centralizer, and isomorphism classes are
the elements of the twisted conjugacy quotient. The identification of automorphisms with
the stabilizer is `CategoryTheory.ActionCategory.stabilizerMulEquivAut`, and
`TwistedConj.mem_stabilizer_iff` gives its defining equation.
-/

public section

open CategoryTheory

namespace TauCeti.TwistedConj

variable {G : Type*} [Group G] {σ : G →* G}

/-- The action groupoid for twisted conjugation. The label of a composite `f ≫ g`
is the label of `g` multiplied on the left of the label of `f`. -/
abbrev Groupoid (σ : G →* G) := ActionCategory G (TwistedConj σ)

/-- The object of the twisted conjugacy groupoid given by a representative. -/
abbrev obj (σ : G →* G) (b : G) : Groupoid σ :=
  ActionCategory.objEquiv G (TwistedConj σ) ⟨b⟩

/-- The arrows between two representatives are the actual twisted conjugators. -/
def homEquiv (b c : G) :
    (obj σ b ⟶ obj σ c) ≃ {g : G // c = g * b * (σ g)⁻¹} where
  toFun f := ⟨f.hom, ((congrArg TwistedConj.val (ActionCategory.hom_smul f)).symm.trans
    (val_smul f.hom ⟨b⟩))⟩
  invFun g := Functor.Elements.homMk g.val (TwistedConj.ext
    ((val_smul g.val ⟨b⟩).trans g.property.symm))
  left_inv _ := Functor.Elements.hom_ext rfl
  right_inv _ := rfl

@[simp]
theorem homEquiv_apply_val {b c : G} (f : obj σ b ⟶ obj σ c) :
    (homEquiv b c f).val = f.hom := (rfl)

@[simp]
theorem homEquiv_symm_apply_hom {b c : G} (g : {g : G // c = g * b * (σ g)⁻¹}) :
    ((homEquiv b c).symm g).hom = g.val := (rfl)

/-- Two representatives have a conjugator arrow precisely when their classes agree. -/
theorem nonempty_hom_iff {b c : G} :
    Nonempty (obj σ b ⟶ obj σ c) ↔ Classes.mk σ b = Classes.mk σ c :=
  (homEquiv b c).nonempty_congr.trans
    (nonempty_subtype.trans Classes.mk_eq_mk_iff.symm)

end TauCeti.TwistedConj
