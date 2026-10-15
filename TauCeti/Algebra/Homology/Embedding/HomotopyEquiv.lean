/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-!
# Extending homotopy equivalences by zero

An embedding of complex shapes extends complexes and their morphisms by zero.  Mathlib proves
that this construction also extends homotopies.  This file packages those results into the
corresponding operation on homotopy equivalences.

## Main definition

* `HomotopyEquiv.extend`: extend a homotopy equivalence along an embedding of complex shapes.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomotopyEquiv

open HomologicalComplex

variable {C ι ι' : Type*} [Category* C] [HasZeroObject C] [Preadditive C]
  {c : ComplexShape ι} {c' : ComplexShape ι'}
  {K L : HomologicalComplex C c}

/-- Extending both complexes by zero along an embedding of complex shapes preserves a homotopy
equivalence. -/
@[expose] noncomputable def extend (h : HomotopyEquiv K L) (e : c.Embedding c') [e.IsRelIff] :
    HomotopyEquiv (K.extend e) (L.extend e) where
  hom := extendMap h.hom e
  inv := extendMap h.inv e
  homotopyHomInvId := by
    simpa only [extendMap_comp, extendMap_id] using h.homotopyHomInvId.extend e
  homotopyInvHomId := by
    simpa only [extendMap_comp, extendMap_id] using h.homotopyInvHomId.extend e

/-- The forward map of an extended homotopy equivalence is the extension of the forward map. -/
@[simp] theorem extend_hom (h : HomotopyEquiv K L) (e : c.Embedding c') [e.IsRelIff] :
    (h.extend e).hom = extendMap h.hom e :=
  rfl

/-- The inverse map of an extended homotopy equivalence is the extension of the inverse map. -/
@[simp] theorem extend_inv (h : HomotopyEquiv K L) (e : c.Embedding c') [e.IsRelIff] :
    (h.extend e).inv = extendMap h.inv e :=
  rfl

end HomotopyEquiv
