/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive
public import TauCeti.Algebra.Coalgebra.Comodule.Weight.Space
import TauCeti.Algebra.Coalgebra.Subcomodule.Lattice

/-!
# Weight spaces in completely reducible comodules

If every nonzero subcomodule of a completely reducible comodule contains a weight vector,
then the weight spaces span the comodule. Indeed, a complement of their sum cannot contain
a nonzero weight vector. Together with Lie--Kolchin, this turns complete reducibility of
representations of connected solvable groups into diagonalizability.

The complement argument follows
`TauCeti.Comodule.fixedSubcomodule_eq_top_of_isCompletelyReducible_of_forall_exists_fixed`,
with the sum of all weight spaces replacing the fixed subcomodule.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.12 and §16.a.
-/

public section

namespace TauCeti.Comodule

universe u v w

variable {k : Type u} {C : Type v} {M : Type w}
variable [CommSemiring k] [AddCommMonoid C] [Module k C] [Coalgebra k C]
variable [Module.Flat k C] [AddCommMonoid M] [Module k M] [Comodule k C M]

/-- A completely reducible comodule is spanned by its group-like weight spaces if every
nonzero subcomodule contains a nonzero weight vector. No finite-dimensionality is required. -/
theorem iSup_groupLikeWeightSpace_eq_top_of_isCompletelyReducible
    (hcr : IsCompletelyReducible k C M)
    (hweight : ∀ N : Subcomodule k C M, N ≠ ⊥ → HasNonzeroWeightVector k C N) :
    ⨆ g : GroupLike k C, _root_.GroupLike.weightSpace (M := M) g = ⊤ := by
  let W : Subcomodule k C M := ⨆ g : GroupLike k C,
    _root_.GroupLike.weightSubcomodule (M := M) g
  have hW : W.toSubmodule = ⨆ g : GroupLike k C,
      _root_.GroupLike.weightSpace (M := M) g := by
    simp [W, Subcomodule.iSup_toSubmodule]
  obtain ⟨Q, hQ⟩ := hcr.exists_isCompl W
  have hQbot : Q = ⊥ := by
    by_contra hne
    obtain ⟨g, hg⟩ := hasNonzeroWeightVector_iff_exists_groupLikeWeightSpace_ne_bot.mp
      (hweight Q hne)
    obtain ⟨q, hq, hq0⟩ := (_root_.GroupLike.weightSpace (M := Q) g).ne_bot_iff.mp hg
    have hqW : (q : M) ∈ W.toSubmodule := by
      rw [hW]
      apply Submodule.mem_iSup_of_mem g
      simpa only [Subcomodule.subtype_apply] using
        (Subcomodule.subtype Q).map_mem_groupLikeWeightSpace hq
    have hzero : (q : M) = 0 := by
      have hmem : (q : M) ∈ W.toSubmodule ⊓ Q.toSubmodule := ⟨hqW, q.property⟩
      simpa [hQ.inf_eq_bot] using hmem
    exact hq0 (Subtype.ext hzero)
  have hsup := hQ.sup_eq_top
  simpa [hQbot, hW] using hsup

end TauCeti.Comodule
