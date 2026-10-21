/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Borel.Subgroup
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Reduction
public import TauCeti.RingTheory.TensorProduct.Reduced
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Borel subgroups and reduction

Over a perfect field the nilradical of a commutative Hopf algebra is a Hopf ideal.
Every Borel candidate is smooth, hence reduced, so it factors through the reduction.
Consequently a finite-type affine group and its reduction have the same Borel subgroups
over an algebraically closed field. Combined with the identity-component comparison,
this passes Borel subgroups to a reduced connected ambient group.

The proof uses `HopfIdeal.reduction_le_of_isReduced_quotient` and the surjective-coordinate
comparison in `Borel.Subgroup`.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §11.4.
* J. S. Milne, *Algebraic Groups* (2017), §17.a.
-/

public section

namespace TauCeti.HopfIdeal

universe u v

variable {k : Type u} [Field k] [PerfectField k]
variable {H : FiniteTypeCommHopfAlgCat.{u, v} k}

/-- A closed subgroup of the reduction is Borel there exactly when it is Borel in the
original affine group. The statement also applies to nonreduced ambient groups. -/
theorem isBorelOverAlgClosed_comap_reduction_iff
    (J : HopfIdeal k (FiniteTypeCommHopfAlgCat.quotient H (reduction k H))) :
    IsBorelOverAlgClosed k H
      (J.comapOfSurjective (Bialgebra.Quotient.mkBialgHom (reduction k H).toIdeal)
        (Bialgebra.Quotient.mkBialgHom_surjective _)) ↔
      IsBorelOverAlgClosed k (FiniteTypeCommHopfAlgCat.quotient H (reduction k H)) J := by
  apply isBorelOverAlgClosed_comapOfSurjective_iff
    (FiniteTypeCommHopfAlgCat.mkQuotient H (reduction k H))
  intro I hI
  let _ : Algebra.Smooth k (FiniteTypeCommHopfAlgCat.quotient H I) :=
    (smoothCommHopfAlgProperty_iff _).mp hI.smooth
  let _ : IsReduced (H ⧸ I.toIdeal) := isReduced_of_smooth k _
  apply (toIdeal_le_toIdeal).mp
  exact (kerOfSurjective_toIdeal _ _).le.trans
    ((FiniteTypeCommHopfAlgCat.mkQuotient_ker _ _).le.trans
      ((toIdeal_le_toIdeal).mpr (reduction_le_of_isReduced_quotient k H I)))

end TauCeti.HopfIdeal
