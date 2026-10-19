/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.Irreducible
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Regularity
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Dimension drop for proper closed subgroups

A proper closed subgroup of a reduced geometrically connected affine group of finite type
has strictly smaller dimension. In coordinate rings, a nonzero Hopf ideal `I` satisfies
`dim (H ⧸ I) + 1 ≤ dim H`. The subgroup may be disconnected or non-smooth. Reducedness of
the ambient group matters: a proper infinitesimal subgroup can have the same dimension.

For smooth ambient groups and smooth closed subgroups, group dimension equals Lie dimension,
so the dimension drop is an inequality of natural numbers. This provides a measure for
induction through proper smooth closed subgroups, including reduced identity components of
closed subgroups. The connectedness assumption is only on the ambient group, and no
perfectness assumption on the field is needed.

The proof uses irreducibility of geometrically connected affine groups and Mathlib's
`ringKrullDim_succ_le_of_surjective`: a nonzero function in the defining ideal is a
non-zero-divisor in the ambient coordinate domain.

## References

* A. Borel, *Linear Algebraic Groups*, §11.1 (induction on dimension for Borel conjugacy).
* J. S. Milne, *Algebraic Groups* (2017), §§1 and 2 (connected groups and dimension).
-/

public section

namespace TauCeti.HopfIdeal

universe u v

variable {k : Type u} [Field k] {H : CommHopfAlgCat.{v} k}
  [Algebra.FiniteType k H]

/-- A proper closed subgroup of a reduced geometrically connected affine group has
dimension at least one less than the ambient group. The subgroup need not be smooth or
connected. -/
theorem ringKrullDim_quotient_add_one_le (I : HopfIdeal k H) [IsReduced H]
    (hH : geometricallyConnectedCommHopfAlgProperty k H) (hI : I ≠ ⊥) :
    ringKrullDim (H ⧸ I.toIdeal) + 1 ≤ ringKrullDim H := by
  have : IrreducibleSpace (PrimeSpectrum H) := hH.irreducibleSpace k H
  have : (⊥ : Ideal H).IsPrime := by
    simpa using (PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp
      (inferInstance : IrreducibleSpace (PrimeSpectrum H)))
  let _ := IsDomain.of_bot_isPrime H
  have hI' : I.toIdeal ≠ ⊥ := by
    intro h
    apply hI
    apply le_antisymm _ bot_le
    rw [← toIdeal_le_toIdeal, bot_toIdeal, h]
  obtain ⟨x, hx, hx0⟩ := I.toIdeal.ne_bot_iff.mp hI'
  exact ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk I.toIdeal)
    Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_iff_ne_zero.mpr hx0)
    (Ideal.Quotient.eq_zero_iff_mem.mpr hx)

/-- A proper smooth closed subgroup of a smooth geometrically connected affine group has
strictly smaller Lie dimension. The closed subgroup may be disconnected, and the base
field may be imperfect. -/
theorem finrank_quotientLie_lt (I : HopfIdeal k H)
    [Algebra.Smooth k H] [Algebra.Smooth k (H ⧸ I.toIdeal)]
    (hH : geometricallyConnectedCommHopfAlgProperty k H) (hI : I ≠ ⊥) :
    Module.finrank k
        (Derivation k (H ⧸ I.toIdeal) (Bialgebra.CounitAlgebra k (H ⧸ I.toIdeal) k)) <
      Module.finrank k (Derivation k H (Bialgebra.CounitAlgebra k H k)) := by
  let _ : IsReduced H := isReduced_of_smooth k H
  have hdim := I.ringKrullDim_quotient_add_one_le hH hI
  rw [← HopfAlgebra.smooth_iff_finrank_lie_eq_ringKrullDim.mp
    (inferInstance : Algebra.Smooth k H),
    ← HopfAlgebra.smooth_iff_finrank_lie_eq_ringKrullDim.mp
      (inferInstance : Algebra.Smooth k (H ⧸ I.toIdeal))] at hdim
  exact Nat.lt_of_succ_le (by exact_mod_cast hdim)

end TauCeti.HopfIdeal
