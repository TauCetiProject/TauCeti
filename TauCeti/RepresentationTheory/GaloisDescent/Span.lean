/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Invariant vectors span a semilinear representation

For a field `L` over a commutative ring `k` with finite automorphism group, every semilinear
representation is spanned over `L` by its invariant vectors. No finite-dimensionality of the
vector space is required. This is the surjectivity step in Galois descent, applied in particular
to the coordinate algebra of a split torus with a Galois action on its character lattice.

The result has no characteristic restriction and does not require the order of the
automorphism group to be invertible in `L`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Appendix A.64 (Galois descent).
-/

public section

namespace TauCeti.GaloisDescent

variable {k L V : Type*} [CommRing k] [Field L] [Algebra k L]
variable [AddCommGroup V] [Module k V] [Module L V]
variable [Finite (L ≃ₐ[k] L)]

/-- Invariant vectors of a semilinear action span the vector space over the coefficient field.
Only finiteness of the automorphism group is needed; the extension need not be Galois. -/
theorem span_invariants_eq_top
    {ρ : Representation k (L ≃ₐ[k] L) V}
    (hsemi : ∀ (σ : L ≃ₐ[k] L) (a : L) (v : V),
      ρ σ (a • v) = σ a • ρ σ v) :
    Submodule.span L (ρ.invariants : Set V) = ⊤ := by
  classical
  let := Fintype.ofFinite (L ≃ₐ[k] L)
  by_contra hspan
  obtain ⟨f, hf, hker⟩ :=
    (Submodule.span L (ρ.invariants : Set V)).exists_le_ker_of_lt_top
      (lt_top_iff_ne_top.mpr hspan)
  apply hf
  ext v
  have horbit (a : L) : ∑ σ : L ≃ₐ[k] L, ρ σ (a • v) ∈ ρ.invariants := by
    rw [Representation.mem_invariants]
    intro τ
    simpa only [Representation.norm, LinearMap.sum_apply] using
      ρ.self_norm_apply τ (a • v)
  have hsum : ∑ σ : L ≃ₐ[k] L, f (ρ σ v) • σ.toAlgHom.toLinearMap = 0 := by
    ext a
    have hz := hker (Submodule.subset_span (horbit a))
    have hz' : f (∑ σ : L ≃ₐ[k] L, ρ σ (a • v)) = 0 := hz
    simpa only [map_sum, hsemi, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      AlgHom.toLinearMap_apply, AlgEquiv.coe_toAlgHom, smul_eq_mul, mul_comm,
      LinearMap.zero_apply] using hz'
  have hli := (linearIndependent_algHom_toLinearMap k L L).comp
    (fun σ : L ≃ₐ[k] L ↦ σ.toAlgHom) AlgEquiv.coe_toAlgHom_injective
  have hz := (Fintype.linearIndependent_iff.mp hli _ hsum) (1 : L ≃ₐ[k] L)
  simpa using hz

end TauCeti.GaloisDescent
