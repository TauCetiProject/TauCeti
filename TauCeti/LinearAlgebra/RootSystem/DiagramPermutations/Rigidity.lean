/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations.NonSimplyLaced
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classification
import TauCeti.LinearAlgebra.RootSystem.Weyl.Automorphism

/-!
# Based automorphisms of nonsimply-laced irreducible root systems

An irreducible finite reduced crystallographic root system with a multiple edge has
no nontrivial based automorphism. The classification reduces this to rigidity of the
oriented numbered Cartan matrices of `Bₙ`, `Cₙ`, `F₄`, and `G₂`. A length exchange is
not a counterexample: it transposes rather than preserves the Cartan matrix.

`RootPairing.Base.eq_one_of_forall_mem_support_of_not_isSimplyLaced` identifies the
automorphism itself;
`RootPairing.Base.indexEquiv_eq_self_of_not_isSimplyLaced` fixes every root index,
not just the simple indices. They apply over any characteristic-zero domain with
the native root-system hypotheses; no choice of real coordinates is involved.
This is the nonsimply-laced branch in reducing finite diagram folding to simply-laced
components and cycles of components.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. VI, §4 and plates II–III, VIII–IX.
-/

public section

namespace RootPairing.Base

open TauCeti

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N}
  [Finite ι] [IsDomain R] [CharZero R] [P.IsReduced]
  [P.IsCrystallographic] [P.IsIrreducible]

/-- A based automorphism of a finite irreducible reduced crystallographic root pairing over a
characteristic-zero domain with a non-simply-laced Cartan matrix is the identity.
The based condition requires only that simple indices map to simple indices. -/
theorem eq_one_of_forall_mem_support_of_not_isSimplyLaced (b : P.Base) {σ : P.Aut}
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsl : ¬ b.cartanMatrix.IsSimplyLaced) : σ = 1 := by
  classical
  have : Nonempty ι := by
    by_contra h
    have := not_nonempty_iff.mp h
    exact hsl fun j ↦ isEmptyElim j.1
  obtain ⟨t, ⟨ht, hb⟩, -⟩ := existsUnique_dynkinType b
  have hrigid := DynkinType.diagramSymmetry_eq_bot_of_not_isSimplyLaced
    (fun hc ↦ hsl ((hb.isSimplyLaced_iff_of_valid ht).mpr hc))
  have hmem : σ ∈ P.weylGroup := by rw [hb.weylGroup_eq_top hrigid]; trivial
  have hone := eq_one_of_forall_mem_support_mem_posRoots P b (w := ⟨σ, hmem⟩) fun i hi ↦ by
    rw [RootPairing.weylGroupToPerm_apply]
    exact support_subset_posRoots P b (hσ i hi)
  exact congrArg (fun w : P.weylGroup ↦ (w : P.Aut)) hone

/-- A based automorphism of a finite irreducible reduced crystallographic root pairing over a
characteristic-zero domain with a non-simply-laced Cartan matrix fixes every root index. -/
theorem indexEquiv_eq_self_of_not_isSimplyLaced (b : P.Base) (σ : P.Aut)
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsl : ¬ b.cartanMatrix.IsSimplyLaced) (i : ι) : σ.indexEquiv i = i := by
  simp [b.eq_one_of_forall_mem_support_of_not_isSimplyLaced hσ hsl]

end RootPairing.Base
