/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Hom
public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Balanced.Basic
import TauCeti.LinearAlgebra.RootSystem.HomInvariance.Basic

/-!
# Naturality of the root-span projection under morphisms

This file records that morphisms and automorphisms of balanced root pairings commute with
`RootPairing.rootSpanProj`.

## Main results

* `RootPairing.Hom.coe_rootSpanProj_weightMap` and `RootPairing.coe_rootSpanProj_smul`:
  morphisms and automorphisms of balanced root pairings commute with `rootSpanProj`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
* M. Demazure, A. Grothendieck (eds.), *Schémas en groupes III* (SGA 3), Exposé XXI, §1.
-/

public section

namespace RootPairing

section Hom

variable {ι ι₂ R M N M₂ N₂ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂}

/-- **Morphisms of balanced root pairings commute with `rootSpanProj`.** -/
theorem Hom.coe_rootSpanProj_weightMap [P.IsBalanced] [Q.IsBalanced] (f : P.Hom Q) (x : M) :
    (Q.rootSpanProj (f.weightMap x) : M₂) = f.weightMap (P.rootSpanProj x : M) := by
  refine congrArg Subtype.val ((Q.rootSpanProj_eq_iff (y :=
    ⟨f.weightMap (P.rootSpanProj x : M),
      f.weightMap_mem_rootSpan (P.rootSpanProj x).property⟩)).mpr ?_)
  rw [← map_sub, mem_corootKer]
  intro j
  obtain ⟨i, rfl⟩ := f.indexEquiv.surjective j
  rw [f.coroot'_weightMap]
  exact mem_corootKer.mp (P.sub_coe_rootSpanProj_mem_corootKer x) i

/-- Automorphisms of a balanced root pairing commute with `rootSpanProj`. -/
@[simp]
theorem coe_rootSpanProj_smul [P.IsBalanced] (g : P.Aut) (x : M) :
    (P.rootSpanProj (g • x) : M) = g • (P.rootSpanProj x : M) :=
  g.toHom.coe_rootSpanProj_weightMap x

end Hom

end RootPairing
