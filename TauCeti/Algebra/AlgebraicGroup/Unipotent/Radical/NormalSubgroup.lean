/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Isomorphism
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.RationalPoint
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Unipotent radicals of normal closed subgroups

Over an algebraically closed field, the unipotent radical of a normal closed subgroup of a
reduced finite-type affine group is normal in the ambient group. Consequently it lies in the
ambient unipotent radical. In particular, triviality of the ambient radical implies triviality
of the subgroup's radical, without any smoothness or connectedness assumption on that subgroup.

Conjugation restricts to an automorphism of the normal subgroup, and isomorphism invariance of
the unipotent radical makes its radical stable under that automorphism. Reducedness of the
ambient group and smoothness of the radical allow rational-point stability to detect
scheme-theoretic normality. The argument uses the quotient-isomorphism interface in
`TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic` and the radical invariance in
`TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Isomorphism`.

## References

* A. Borel, *Linear Algebraic Groups*, §11.21.
* J. S. Milne, *Algebraic Groups* (2017), §§6.45–6.46 and 19.
-/

public section

open CategoryTheory

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

noncomputable section

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (H : FiniteTypeCommHopfAlgCat.{u, u} k) [IsReduced H]
variable (I : HopfIdeal k H)

/-- The unipotent radical of a normal closed subgroup of a reduced finite-type affine group
over an algebraically closed field is normal in the ambient group. -/
theorem isNormal_comapOfSurjective_unipotentRadicalDefiningIdeal (hI : I.IsNormal) :
    ((unipotentRadicalDefiningIdeal (quotient H I)).comapOfSurjective
      (CommHopfAlgCat.mkQuotient H.obj I).hom
      (CommHopfAlgCat.mkQuotient_surjective H.obj I)).IsNormal := by
  let N := quotient H I
  let q := CommHopfAlgCat.mkQuotient H.obj I
  let R := unipotentRadicalDefiningIdeal N
  let J := R.comapOfSurjective q.hom (CommHopfAlgCat.mkQuotient_surjective H.obj I)
  -- The ambient presentation of the radical inherits smoothness from the subgroup presentation.
  let eJ := CommHopfAlgCat.Hom.quotientIsoOfSurjective q
    (CommHopfAlgCat.mkQuotient_surjective H.obj I) R
  have hsm : smoothCommHopfAlgProperty k (CommHopfAlgCat.quotient H.obj J) :=
    (smoothCommHopfAlgProperty k).prop_of_iso eJ.symm
      ((smoothCommHopfAlgProperty_iff _).mpr
        ((smoothUnipotentCommHopfAlgProperty_iff k (unipotentRadical N)).mp
          (smoothUnipotent_unipotentRadical N)).1)
  let _ : Algebra.Smooth k (CommHopfAlgCat.quotient H.obj J) :=
    (smoothCommHopfAlgProperty_iff _).mp hsm
  let _ : IsReduced (CommHopfAlgCat.quotient H.obj J) := isReduced_of_smooth k _
  apply HopfIdeal.isNormal_of_forall_le_conjugate
  intro g x hx
  -- Restrict ambient conjugation to the normal subgroup, then use invariance of its radical.
  let e := _root_.CommHopfAlgCat.isoMk (HopfAlgebra.pointConjugationBialgEquiv g)
  have hstable : I.comapOfSurjective e.hom.hom
      (ConcreteCategory.bijective_of_isIso e.hom).2 = I := by
    have hconj : I.conjugate g = I := by
      apply le_antisymm
      · have hle := HopfIdeal.conjugate_mono g (hI.le_conjugate g⁻¹)
        simpa using hle
      · exact hI.le_conjugate g
    exact (HopfIdeal.conjugate_eq_comapOfSurjective I g).symm.trans hconj
  let eN : N ≅ N := ObjectProperty.isoMk _
    (CommHopfAlgCat.quotientIsoOfComapEq e I hstable)
  have hR := comapOfSurjective_unipotentRadicalDefiningIdeal eN
  have hpres : toBialgHom eN.hom (q.hom x) ∈ R := by
    have hmem : q.hom x ∈ R.comapOfSurjective (toBialgHom eN.hom)
        (ConcreteCategory.bijective_of_isIso eN.hom).2 := by
      rw [hR]
      exact HopfIdeal.mem_comapOfSurjective.mp hx
    exact HopfIdeal.mem_comapOfSurjective.mp hmem
  have hcomm := congrArg (fun f ↦ f.hom x)
    (CommHopfAlgCat.mkQuotient_comp_quotientIsoOfComapEq_hom e I hstable)
  rw [CommHopfAlgCat.comp_apply, CommHopfAlgCat.comp_apply] at hcomm
  rw [HopfIdeal.mem_conjugate, HopfIdeal.mem_comapOfSurjective]
  -- The quotient automorphism is induced by point conjugation; its public commuting equation
  -- identifies the underlying bialgebra map without unfolding either quotient construction.
  have hc : e.hom.hom x = HopfAlgebra.pointConjugationAlgHom g x :=
    DFunLike.congr_fun (HopfAlgebra.pointConjugationBialgEquiv_toAlgHom g) x
  rw [← hc, ← hcomm]
  exact hpres

/-- The unipotent radical of a normal closed subgroup lies in the ambient unipotent radical.
The inclusion is reversed on defining Hopf ideals. -/
theorem unipotentRadicalDefiningIdeal_le_comapOfSurjective_quotient (hI : I.IsNormal) :
    unipotentRadicalDefiningIdeal H ≤
      (unipotentRadicalDefiningIdeal (quotient H I)).comapOfSurjective
        (CommHopfAlgCat.mkQuotient H.obj I).hom
        (CommHopfAlgCat.mkQuotient_surjective H.obj I) := by
  let N := quotient H I
  let q := CommHopfAlgCat.mkQuotient H.obj I
  let R := unipotentRadicalDefiningIdeal N
  let J := R.comapOfSurjective q.hom (CommHopfAlgCat.mkQuotient_surjective H.obj I)
  let eJ : quotient H J ≅ unipotentRadical N :=
    ObjectProperty.isoMk (finiteTypeCommHopfAlgProperty k)
      (CommHopfAlgCat.Hom.quotientIsoOfSurjective q
        (CommHopfAlgCat.mkQuotient_surjective H.obj I) R)
  apply unipotentRadicalDefiningIdeal_le
  refine .mk (isNormal_comapOfSurjective_unipotentRadicalDefiningIdeal H I hI) ?_ ?_
  · exact (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso
      ((forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k)
        (_root_.CommHopfAlgCat.{u} k)).mapIso eJ.symm)
      (geometricallyConnected_unipotentRadical N)
  · exact (smoothUnipotentCommHopfAlgProperty k).prop_of_iso eJ.symm
      (smoothUnipotent_unipotentRadical N)

/-- A normal closed subgroup of a reduced finite-type affine group with trivial unipotent
radical also has trivial unipotent radical, over an algebraically closed field. -/
theorem unipotentRadicalDefiningIdeal_quotient_eq_augmentation_of_isNormal (hI : I.IsNormal)
    (hH : unipotentRadicalDefiningIdeal H = HopfIdeal.augmentation k H) :
    unipotentRadicalDefiningIdeal (quotient H I) = HopfIdeal.augmentation k (quotient H I) := by
  apply le_antisymm (HopfIdeal.le_augmentation k _ _)
  rw [← HopfIdeal.comapOfSurjective_le_comapOfSurjective_iff
    (CommHopfAlgCat.mkQuotient H.obj I).hom
    (CommHopfAlgCat.mkQuotient_surjective H.obj I), HopfIdeal.comapOfSurjective_augmentation]
  rw [← hH]
  exact unipotentRadicalDefiningIdeal_le_comapOfSurjective_quotient H I hI

end

end TauCeti.FiniteTypeCommHopfAlgCat
