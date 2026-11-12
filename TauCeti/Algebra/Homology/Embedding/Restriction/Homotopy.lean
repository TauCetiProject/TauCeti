/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.Boundary
public import Mathlib.Algebra.Homology.Embedding.Restriction
public import Mathlib.Algebra.Homology.Homotopy

/-!
# Restricting homotopies along an embedding of complex shapes

Mathlib restricts complexes and their morphisms along an embedding of complex shapes
`e : c.Embedding c'` (`HomologicalComplex.restriction`, `HomologicalComplex.restrictionMap`).
A homotopy `φ ≃ ψ` does not restrict along an arbitrary embedding, since the homotopy relation in
a degree `e.f i` involves the neighbours `c'.prev (e.f i)` and `c'.next (e.f i)`, which need not
lie in the image of `e.f`. When `e` satisfies both `IsTruncGE` and `IsTruncLE`, these
neighbours are `e.f (c.prev i)` and `e.f (c.next i)`, and restricting the components of the
homotopy gives a homotopy between the restricted morphisms. This applies in particular to the
embeddings that reindex a complex by a bijection of its degrees.

## Main definitions

* `Homotopy.restriction`: restrict a homotopy along an embedding of complex shapes.
* `HomotopyEquiv.restriction`: restrict a homotopy equivalence along an embedding of complex
  shapes.
-/

public section

open CategoryTheory

variable {C ι ι' : Type*} [Category* C] [Preadditive C]
  {c : ComplexShape ι} {c' : ComplexShape ι'}

namespace Homotopy

open HomologicalComplex

variable {K L : HomologicalComplex C c'} {φ ψ : K ⟶ L}

/-- Restricting the components of a homotopy along an embedding of complex shapes satisfying
`IsTruncGE` and `IsTruncLE` gives a homotopy between the restricted morphisms. -/
def restriction (h : Homotopy φ ψ) (e : c.Embedding c') [e.IsTruncGE] [e.IsTruncLE] :
    Homotopy (restrictionMap φ e) (restrictionMap ψ e) where
  hom i j := h.hom (e.f i) (e.f j)
  zero i j hij := h.zero _ _ (by rwa [e.rel_iff])
  comm i := by
    have hi := h.comm (e.f i)
    simp only [dNext, prevD, AddMonoidHom.mk'_apply] at hi ⊢
    rw [e.next_f rfl, e.prev_f rfl] at hi
    exact hi

/-- The components of a restricted homotopy are the components of the homotopy in the image
degrees. -/
@[simp] theorem restriction_hom (h : Homotopy φ ψ) (e : c.Embedding c') [e.IsTruncGE]
    [e.IsTruncLE] (i j : ι) : (h.restriction e).hom i j = h.hom (e.f i) (e.f j) :=
  (rfl)

end Homotopy

namespace HomotopyEquiv

open HomologicalComplex

variable {K L : HomologicalComplex C c'}

/-- Restricting both complexes along an embedding of complex shapes satisfying `IsTruncGE` and
`IsTruncLE` preserves a homotopy equivalence. -/
def restriction (h : HomotopyEquiv K L) (e : c.Embedding c') [e.IsTruncGE] [e.IsTruncLE] :
    HomotopyEquiv (K.restriction e) (L.restriction e) where
  hom := restrictionMap h.hom e
  inv := restrictionMap h.inv e
  homotopyHomInvId := by
    simpa only [restrictionMap_comp, restrictionMap_id] using h.homotopyHomInvId.restriction e
  homotopyInvHomId := by
    simpa only [restrictionMap_comp, restrictionMap_id] using h.homotopyInvHomId.restriction e

/-- The forward map of a restricted homotopy equivalence is the restriction of the forward
map. -/
@[simp] theorem restriction_hom (h : HomotopyEquiv K L) (e : c.Embedding c') [e.IsTruncGE]
    [e.IsTruncLE] : (h.restriction e).hom = restrictionMap h.hom e :=
  (rfl)

/-- The inverse map of a restricted homotopy equivalence is the restriction of the inverse
map. -/
@[simp] theorem restriction_inv (h : HomotopyEquiv K L) (e : c.Embedding c') [e.IsTruncGE]
    [e.IsTruncLE] : (h.restriction e).inv = restrictionMap h.inv e :=
  (rfl)

end HomotopyEquiv
