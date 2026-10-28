/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Normalizer.Connected

/-!
# Normal diagonalizable subgroups are central

A normal diagonalizable closed subgroup of a reduced connected affine group of finite type
over an algebraically closed field is central. The diagonalizable subgroup need not be reduced:
the conclusion concerns its full scheme structure, including infinitesimal subgroups.

The normalizer acts through a finite group of character automorphisms. Conjugation coefficients
are regular functions on the ambient group, so connectedness makes them constant. Specializing
at the identity makes the restricted conjugation trivial. Point separation is used only on the
reduced ambient coordinate ring, never on the diagonalizable subgroup.

## References

* J. S. Milne, *Algebraic Groups* (2017), Corollary 12.38.

The central input is
`BialgHom.centralizerHopfIdeal_le_ker_of_forall_mapDomain_mem_normalizerPoints`:
the identity morphism factors through the normalizer when the diagonalizable subgroup is normal.
-/

public section

open TauCeti WithConv

namespace BialgHom

noncomputable section

variable {k H X : Type*} [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X]

variable [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H]
  [ConnectedSpace (PrimeSpectrum H)]

/-- A normal diagonalizable closed subgroup of a reduced connected finite-type affine group
over an algebraically closed field is central as a subgroup scheme. No smoothness or
reducedness of the diagonalizable subgroup is assumed. -/
theorem isCentral_kerOfSurjective_of_isNormal
    (π : H →ₐc[k] MonoidAlgebra k X) (hπ : Function.Surjective π)
    (hN : (HopfIdeal.kerOfSurjective π hπ).IsNormal) :
    (HopfIdeal.kerOfSurjective π hπ).IsCentral := by
  rw [← centralizerHopfIdeal_eq_bot_iff_isCentral π hπ]
  have hker := centralizerHopfIdeal_le_ker_of_forall_mapDomain_mem_normalizerPoints
    π hπ (BialgHom.id k H) fun g ↦ ?_
  · rw [eq_bot_iff]
    intro x hx
    exact HopfIdeal.mem_bot.mpr (hker (HopfIdeal.mem_toIdeal.mpr hx))
  · rw [mapDomain_id, MonoidHom.id_apply, mem_normalizerPoints]
    apply le_antisymm
    · have h := hN.le_conjugate g⁻¹
      exact (HopfIdeal.conjugate_mono g h).trans_eq
        (HopfIdeal.conjugate_conjugate_inv _ g)
    · exact hN.le_conjugate g

end

end BialgHom
