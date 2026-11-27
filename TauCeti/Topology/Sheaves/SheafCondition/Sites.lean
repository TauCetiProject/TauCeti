/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Sheaves on the empty open subspace

Mathlib's `TopCat.Sheaf.isTerminalOfEqEmpty` says that the sections of a sheaf over an empty open
form a terminal object. On the subspace `⊥` every open is empty, so when the coefficient category
has zero morphisms every sheaf on it is a zero object.

## Main results

* `TopologicalSpace.Opens.isZero_sheaf_bot`: every sheaf on the empty open subspace is zero.
-/

public section

open CategoryTheory Limits

universe u uA vA

namespace TopologicalSpace.Opens

variable {X : TopCat.{u}} {A : Type uA} [Category.{vA} A]

/-- Every sheaf on the empty subspace is zero when the coefficient category has zero morphisms. -/
lemma isZero_sheaf_bot [HasZeroMorphisms A]
    (F : (TopCat.of (⊥ : Opens X)).Sheaf A) : IsZero F := by
  apply (IsZero.iff_id_eq_zero F).2
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext T
  have hT : T.unop = ⊥ := by
    apply Opens.ext
    ext x
    exact False.elim x.property
  exact (F.isTerminalOfEqEmpty hT).hom_ext _ _

end TopologicalSpace.Opens
