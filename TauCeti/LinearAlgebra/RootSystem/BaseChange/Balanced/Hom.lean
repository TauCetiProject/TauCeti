/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Hom
public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Balanced.Basic
import TauCeti.LinearAlgebra.RootSystem.HomInvariance

/-!
# Equivariance of the root-span projection under equivalences

This file records that equivalences and automorphisms of balanced root pairings commute with
`RootPairing.rootSpanProj`.

## Main results

* `RootPairing.Equiv.coe_rootSpanProj_weightMap` and `RootPairing.coe_rootSpanProj_smul`:
  equivalences and automorphisms of balanced root pairings commute with `rootSpanProj`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
* M. Demazure, A. Grothendieck (eds.), *Schémas en groupes III* (SGA 3), Exposé XXI, §1.
-/

public section

namespace RootPairing

section Equiv

variable {ι ι₂ R M N M₂ N₂ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂}

/-- **Equivalences of balanced root pairings commute with `rootSpanProj`.** -/
theorem Equiv.coe_rootSpanProj_weightMap [P.IsBalanced] [Q.IsBalanced] (e : P.Equiv Q) (x : M) :
    (Q.rootSpanProj (e.weightMap x) : M₂) = e.weightMap (P.rootSpanProj x : M) := by
  have hmem : e.weightMap (P.rootSpanProj x : M) ∈ Q.rootSpan R :=
    e.toHom.weightMap_mem_rootSpan (P.rootSpanProj x).property
  have hker : e.weightMap x - e.weightMap (P.rootSpanProj x : M) ∈ Q.corootKer := by
    rw [← map_sub, e.weightMap_mem_corootKer_iff]
    exact P.sub_coe_rootSpanProj_mem_corootKer x
  have hzero : Q.rootSpanProj (e.weightMap x - e.weightMap (P.rootSpanProj x : M)) = 0 :=
    Q.rootSpanProj_eq_zero_iff.mpr hker
  rw [map_sub, Q.rootSpanProj_apply_of_mem hmem, sub_eq_zero] at hzero
  exact congrArg Subtype.val hzero

/-- Automorphisms of a balanced root pairing commute with `rootSpanProj`. -/
@[simp]
theorem coe_rootSpanProj_smul [P.IsBalanced] (g : P.Aut) (x : M) :
    (P.rootSpanProj (g • x) : M) = g • (P.rootSpanProj x : M) :=
  g.coe_rootSpanProj_weightMap x

end Equiv

end RootPairing
