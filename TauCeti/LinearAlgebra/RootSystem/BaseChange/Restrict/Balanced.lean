/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Balanced.Basic
public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Restrict.Chamber
public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Restrict.Hom
import TauCeti.LinearAlgebra.RootSystem.BaseChange.Balanced.Chamber
import TauCeti.LinearAlgebra.RootSystem.BaseChange.Balanced.Hom

/-!
# Root-span projection compatibility with scalar restriction

For a balanced root pairing `P` over a field `L`, the same-field restriction `P.restrictScalars' L`
acts on `P.rootSpan L`. This file records how the root-span projection `P.rootSpanProj` from
`TauCeti.LinearAlgebra.RootSystem.BaseChange.Balanced.Basic` intertwines reflections and
automorphisms of `P` with those of `P.restrictScalars' L`.

## Main results

* `RootPairing.rootSpanProj_reflection`: `P.rootSpanProj` intertwines reflections of `P` with
  reflections of `P.restrictScalars' L`.
* `RootPairing.restrictScalars'_self_smul_rootSpanProj`: `P.rootSpanProj` intertwines the action
  of `P.Aut` with that of `(P.restrictScalars' L).Aut`.
* `RootPairing.Equiv.weightMap_restrictScalars'_rootSpanProj`: `P.rootSpanProj` intertwines an
  equivalence of root pairings with its restriction to the spans of the roots.
* `RootPairing.rootSpanProj_mem_dominantChamber_iff`: `P.rootSpanProj` preserves dominance.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
* M. Demazure, A. Grothendieck (eds.), *Schémas en groupes III* (SGA 3), Exposé XXI, §§1, 6.
-/

public section

namespace RootPairing

variable {ι L M N : Type*} [Field L] [AddCommGroup M] [AddCommGroup N] [Module L M] [Module L N]
  (P : RootPairing ι L M N) [P.IsBalanced]

/-- Projecting onto the root span intertwines each ambient reflection with the corresponding
reflection of `P.restrictScalars' L`. -/
@[simp]
theorem rootSpanProj_reflection (i : ι) (x : M) :
    P.rootSpanProj (P.reflection i x) = (P.restrictScalars' L).reflection i (P.rootSpanProj x) := by
  ext
  rw [coe_rootSpanProj_reflection, coe_restrictScalars'_reflection_apply]

/-- Projecting onto the `L`-span of the roots intertwines the action of `P.Aut` on `M` with the
action of `(P.restrictScalars' L).Aut` on `P.rootSpan L`. -/
@[simp]
theorem restrictScalars'_self_smul_rootSpanProj (g : P.Aut) (x : M) :
    g.restrictScalars' L • P.rootSpanProj x = P.rootSpanProj (g • x) := by
  ext
  rw [coe_restrictScalars'_smul, coe_rootSpanProj_smul]

/-- **The projection onto the span of the roots is equivariant**: the restriction of an equivalence
of root pairings to the spans of the roots intertwines the two projections. -/
theorem Equiv.weightMap_restrictScalars'_rootSpanProj {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂]
    [AddCommGroup N₂] [Module L M₂] [Module L N₂] {Q : RootPairing ι₂ L M₂ N₂} [Q.IsBalanced]
    (e : P.Equiv Q) (x : M) :
    (e.restrictScalars' L).weightMap (P.rootSpanProj x) = Q.rootSpanProj (e.weightMap x) :=
  Subtype.ext <| by
    rw [Equiv.toHom_restrictScalars', Hom.coe_weightMap_restrictScalars']
    exact (e.toHom.coe_rootSpanProj_weightMap x).symm

/-- The projection of a vector onto the span of the roots is dominant for `b.restrictScalars' L`
exactly when the vector is dominant for `b`. -/
theorem rootSpanProj_mem_dominantChamber_iff [Preorder L] (b : P.Base) {x : M} :
    P.rootSpanProj x ∈ dominantChamber (P.restrictScalars' L) (b.restrictScalars' L) ↔
      x ∈ dominantChamber P b := by
  rw [mem_dominantChamber_restrictScalars'_self_iff, coe_rootSpanProj_mem_dominantChamber_iff]

end RootPairing
