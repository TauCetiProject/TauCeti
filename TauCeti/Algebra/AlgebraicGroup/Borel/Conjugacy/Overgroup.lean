/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Borel.Conjugation
import TauCeti.Algebra.AlgebraicGroup.Borel.Conjugacy.Existence
import TauCeti.Algebra.AlgebraicGroup.Borel.Subgroup

/-!
# Borel conjugacy inside a closed overgroup

Over an algebraically closed field, two Borel subgroups of a finite-type affine group
contained in the same closed subgroup are conjugate by a rational point of that subgroup.
Consequently, a conjugator between two closed subgroups containing a chosen Borel can be
multiplied on the left by a point of the target subgroup so as to normalize the chosen Borel,
without changing the conjugate of the source subgroup.

This is the reduction from conjugacy of subgroups containing a Borel to its normalizer. All
conjugation equalities are equalities of Hopf ideals, hence of subgroup schemes, not just of
rational-point subgroups. Neither the ambient group nor the overgroup needs to be connected,
smooth, or reduced.

The construction uses `IsBorelOverAlgClosed.map_of_le` to restrict the ambient group,
`IsBorelOverAlgClosed.exists_conjugate_eq` for conjugacy there, and
`HopfIdeal.conjugate_comapOfSurjective` to transport the equality back to the ambient group.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 17.9(b), and the Borel-conjugacy argument
  in the proof of Theorem 21.91.
-/

public section

namespace TauCeti.HopfIdeal

universe u

variable {k : Type u} [Field k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} {B C P Q : HopfIdeal k H}

/-- Two ambient Borel subgroups contained in a closed subgroup are conjugate by a rational
point of that closed subgroup. In Hopf ideal order, `Q ≤ B` means that the subgroup defined
by `Q` contains the subgroup defined by `B`. No reducedness of `Q` is required. -/
theorem IsBorelOverAlgClosed.exists_mem_quotientPointsSubgroup_conjugate_eq
    (hB : IsBorelOverAlgClosed k H B) (hC : IsBorelOverAlgClosed k H C)
    (hQB : Q ≤ B) (hQC : Q ≤ C) :
    ∃ q ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj Q (CommAlgCat.of k k),
      B.conjugate q = C := by
  let π := Bialgebra.Quotient.mkBialgHom (R := k) Q.toIdeal
  obtain ⟨q, hq⟩ := (hB.map_of_le hQB).exists_conjugate_eq (hC.map_of_le hQC)
  refine ⟨CommHopfAlgCat.quotientPointsHom H.obj Q (CommAlgCat.of k k) q,
    CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup
      H.obj Q (CommAlgCat.of k k) q, ?_⟩
  have h := congrArg
    (fun I : HopfIdeal k (FiniteTypeCommHopfAlgCat.quotient H Q) ↦
      I.comapOfSurjective π (CommHopfAlgCat.mkQuotient_surjective H.obj Q)) hq
  rw [← conjugate_comapOfSurjective,
    comapOfSurjective_map_mkBialgHom hQB,
    comapOfSurjective_map_mkBialgHom hQC] at h
  rw [CommHopfAlgCat.quotientPointsHom_apply H.obj Q (CommAlgCat.of k k) q]
  exact h

/-- A conjugator between closed subgroups containing the same Borel can be adjusted by a
point of the target subgroup to normalize that Borel. The adjusted point is `q * g`, not
`g * q`: the convention is that `I.conjugate g` cuts out `g I g⁻¹`. The target subgroup is
unchanged by this adjustment, including when it is nonreduced. -/
theorem IsBorelOverAlgClosed.exists_mem_quotientPointsSubgroup_conjugate_mul_eq
    (hB : IsBorelOverAlgClosed k H B) (hPB : P ≤ B) (hQB : Q ≤ B)
    (g : WithConv (H →ₐ[k] k)) (hg : P.conjugate g = Q) :
    ∃ q ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj Q (CommAlgCat.of k k),
      B.conjugate (q * g) = B ∧ P.conjugate (q * g) = Q := by
  have hQBg : Q ≤ B.conjugate g := hg ▸ conjugate_mono g hPB
  obtain ⟨q, hq, hBq⟩ := (hB.conjugate g).exists_mem_quotientPointsSubgroup_conjugate_eq
    hB hQBg hQB
  refine ⟨q, hq, ?_, ?_⟩
  · simpa only [conjugate_mul] using hBq
  · rw [conjugate_mul, hg]
    exact conjugate_eq_self_of_mem_quotientPointsSubgroup Q hq

end TauCeti.HopfIdeal
