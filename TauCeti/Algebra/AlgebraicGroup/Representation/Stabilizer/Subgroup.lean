/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.Stabilizer.BaseChange
public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive

/-!
# Subrepresentations under closed subgroups

Let `M` be a representation of an affine group `G = Spec H` over a field `k`. A subspace `W ≤ M`
is a subrepresentation exactly when its stabilizer Hopf ideal is `⊥`
(`Submodule.stabilizerHopfIdeal_eq_bot_iff`). For the closed subgroup cut out by a Hopf ideal
`I`, the subspaces stable under the subgroup are therefore those whose stabilizer Hopf ideal lies
below `I`. So `M`, as a representation of the subgroup, is completely reducible exactly when every
such subspace has a complement of the same kind
(`TauCeti.Comodule.isCompletelyReducible_corestrict_mkQuotient_iff`). This is the form in which
the semisimplicity of a representation is checked through the stabilizers of subspaces, as for
the Mumford–Tate group of a polarizable Hodge structure.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 4 and 10.
-/

public section

namespace TauCeti.Comodule

variable {k : Type*} [Field k] {H : _root_.CommHopfAlgCat k} {M : Type*} [AddCommGroup M]
  [Module k M] [Comodule k H M]

/-- **Complete reducibility under a closed subgroup.** Regard a representation `M` of `G` as a
representation of the closed subgroup cut out by a Hopf ideal `I`. It is completely reducible
exactly when every subspace stable under the subgroup (its stabilizer Hopf ideal lies below `I`)
has a complement stable under the subgroup. -/
theorem isCompletelyReducible_corestrict_mkQuotient_iff (I : HopfIdeal k H) :
    letI := Comodule.Corestrict (M := M) (_root_.CommHopfAlgCat.mkQuotient H I).hom.toCoalgHom
    IsCompletelyReducible k (_root_.CommHopfAlgCat.quotient H I) M ↔
      ∀ W : Submodule k M, W.stabilizerHopfIdeal H ≤ I →
        ∃ W' : Submodule k M, IsCompl W W' ∧ W'.stabilizerHopfIdeal H ≤ I := by
  let _ := Comodule.Corestrict (M := M) (_root_.CommHopfAlgCat.mkQuotient H I).hom.toCoalgHom
  have key (W : Submodule k M) :
      W.stabilizerHopfIdeal (_root_.CommHopfAlgCat.quotient H I) = ⊥ ↔
        W.stabilizerHopfIdeal H ≤ I := by
    rw [Submodule.stabilizerHopfIdeal_corestrict_eq_bot_iff, ← HopfIdeal.toIdeal_le_toIdeal]
    exact Iff.of_eq (congrArg _ (_root_.CommHopfAlgCat.mkQuotient_ker H I))
  constructor
  · intro h W hW
    obtain ⟨Q, hQ⟩ := h.exists_isCompl
      (Subcomodule.ofSubmodule W ((Submodule.stabilizerHopfIdeal_eq_bot_iff W).mp
        ((key W).mpr hW)))
    refine ⟨Q.toSubmodule, hQ, (key _).mp ?_⟩
    exact (Submodule.stabilizerHopfIdeal_eq_bot_iff _).mpr fun m hm ↦ Q.coact_mem hm
  · intro h
    refine IsCompletelyReducible.of_exists_isCompl fun W ↦ ?_
    obtain ⟨W', hW', hW'I⟩ := h W.toSubmodule ((key _).mp
      ((Submodule.stabilizerHopfIdeal_eq_bot_iff _).mpr fun m hm ↦ W.coact_mem hm))
    exact ⟨Subcomodule.ofSubmodule W' ((Submodule.stabilizerHopfIdeal_eq_bot_iff W').mp
      ((key W').mpr hW'I)), hW'⟩

end TauCeti.Comodule
