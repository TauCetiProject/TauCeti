/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Abelian.Subobject
public import TauCeti.CategoryTheory.Projective.Cover
public import TauCeti.Order.Superfluous

import TauCeti.CategoryTheory.Subobject.Image

/-!
# Essential epimorphisms in abelian categories

An epimorphism in an abelian category is essential exactly when its kernel is superfluous in the
subobject lattice of its source. This allows one to verify essentiality of a projective cover
by computing the kernel, and applies to epimorphisms with any source.

The module case is Wisbauer, *Foundations of Module and Ring Theory* (1991), §19.2, p. 159.
-/

public section

open CategoryTheory Limits

namespace TauCeti

variable {C : Type*} [Category* C] [Abelian C] {P M : C}

/-- An epimorphism in an abelian category is essential exactly when its kernel subobject is
superfluous. -/
theorem isEssentialEpi_iff_isSuperfluous_kernelSubobject (p : P ⟶ M) [Epi p] :
    IsEssentialEpi p ↔ IsSuperfluous (kernelSubobject p) := by
  constructor
  · intro hp
    refine isSuperfluous_iff.mpr fun S hS ↦ ?_
    have h : Epi (S.arrow ≫ p) :=
      (epi_comp_iff_kernelSubobject_sup_imageSubobject_eq_top S.arrow p).2
        (by simpa only [imageSubobject_mono, Subobject.mk_arrow] using hS)
    simpa only [Subobject.epi_iff_mk_eq_top, Subobject.mk_arrow] using hp.epi_of_epi_comp S.arrow h
  · intro hker
    refine ⟨inferInstance, fun g hg ↦ ?_⟩
    exact (imageSubobject_eq_top_iff_epi g).1 (hker.eq_top_of_sup_eq_top
      ((epi_comp_iff_kernelSubobject_sup_imageSubobject_eq_top g p).1 hg))

end TauCeti
