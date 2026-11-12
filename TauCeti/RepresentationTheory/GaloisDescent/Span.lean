/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.Basis.VectorSpace

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
    Submodule.span L (ρ.invariants : Set V) = ⊤ := by
  classical
  let := Fintype.ofFinite G
  by_contra hspan
  obtain ⟨f, hf, hker⟩ :=
    (Submodule.span L (ρ.invariants : Set V)).exists_le_ker_of_lt_top
      (lt_top_iff_ne_top.mpr hspan)
  apply hf
  ext v
  have horbit (a : L) : ∑ g : G, ρ g (a • v) ∈ ρ.invariants := by
    rw [Representation.mem_invariants]
    intro h
    simpa only [Representation.norm, LinearMap.sum_apply] using ρ.self_norm_apply h (a • v)
  -- Dedekind's independence of the characters `a ↦ g • a` of `L`, for `g ∈ G`.
  have hli := (linearIndependent_monoidHom L L).comp
    (fun g : G ↦ (MulSemiringAction.toRingHom G L g : L →* L))
    fun g h hgh ↦ eq_of_smul_eq_smul fun a ↦ DFunLike.congr_fun hgh a
  have hsum : ∑ g : G, f (ρ g v) • ⇑(MulSemiringAction.toRingHom G L g : L →* L) = 0 := by
    ext a
    have hz := LinearMap.mem_ker.mp (hker (Submodule.subset_span (horbit a)))
    simpa [hsemi, mul_comm] using hz
  simpa using Fintype.linearIndependent_iff.mp hli _ hsum 1

end TauCeti.GaloisDescent
