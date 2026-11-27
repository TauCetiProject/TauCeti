/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.RepresentationTheory.Invariants
import TauCeti.RepresentationTheory.GaloisDescent.FiniteIndex

/-!
# Invariant vectors span a semilinear representation

Let a finite group `G` act faithfully on a field `L` by ring automorphisms, for instance the
automorphism group of `L` over a commutative ring `k` when that group is finite. Every
semilinear representation of `G` on an `L`-vector space is spanned over `L` by its invariant
vectors. No finite-dimensionality of the vector space is required. This is the surjectivity
step in Galois descent, applied in particular to the coordinate algebra of a split torus with a
Galois action on its character lattice.

The result has no characteristic restriction and does not require the order of `G` to be
invertible in `L`.

It is the case `U = ⊥`, `j = id` of `TauCeti.GaloisDescent.mem_span_invariants_of_finiteIndex`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Appendix A.64 (Galois descent).
-/

public section

namespace TauCeti.GaloisDescent

variable {k G L V : Type*} [CommRing k] [Group G] [Field L]
variable [MulSemiringAction G L] [FaithfulSMul G L] [Finite G]
variable [AddCommGroup V] [Module k V] [Module L V]

/-- Invariant vectors of a semilinear representation of a finite group `G` acting faithfully on
the field `L` span the representation over `L`. This applies to the automorphism group of any
extension `L / k` for which that group is finite; the extension need not be Galois. -/
theorem span_invariants_eq_top
    {ρ : Representation k G V}
    (hsemi : ∀ (g : G) (a : L) (v : V), ρ g (a • v) = (g • a) • ρ g v) :
    Submodule.span L (ρ.invariants : Set V) = ⊤ :=
  -- The case `U = ⊥`, `j = id`: faithfulness says that only `1` fixes all of `L`.
  eq_top_iff.mpr fun _ _ ↦ mem_span_invariants_of_finiteIndex (MonoidHom.id G) ⊥
    (fun g hg ↦ Subgroup.mem_bot.mpr <| eq_of_smul_eq_smul fun a ↦ by
      rw [one_smul]
      exact (mem_fixingSubgroup_iff G).mp hg a fun m ↦ by
        rw [Subgroup.smul_def, Subgroup.mem_bot.mp m.property, one_smul]) hsemi
    (fun g hg ↦ by simp_all)

end TauCeti.GaloisDescent
