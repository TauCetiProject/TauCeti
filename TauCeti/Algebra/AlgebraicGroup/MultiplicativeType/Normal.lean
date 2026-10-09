/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Normal
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Basic
public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.Center.BaseChange
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.BaseChange
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced

/-!
# Normal subgroups of multiplicative type are central

A normal closed subgroup of multiplicative type in a geometrically reduced, geometrically
connected finite-type affine group is central. In particular, this applies to a normal torus
in a smooth geometrically connected affine group. The ground field may be imperfect, and the
subgroup may be nonreduced. These statements concern the scheme-theoretic center.

After extension to an algebraic closure the subgroup is diagonalizable, so
`BialgHom.isCentral_kerOfSurjective_of_isNormal` applies. Formation of the center commutes with
field extension, and faithful flatness reflects subgroup containment.

This centrality is the structural input needed once the solvable radical of a reductive group
has been identified as a torus, in order to construct the semisimple central quotient.

## References

* J. S. Milne, *Algebraic Groups* (2017), Corollary 12.38.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.HopfIdeal

universe u

noncomputable section

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- A normal subgroup of multiplicative type in a geometrically reduced and geometrically
connected affine group of finite type is central, over any field. The subgroup need not be
smooth or connected, so the conclusion includes infinitesimal subgroups of multiplicative type.
-/
theorem IsNormal.isCentral_of_multiplicativeType
    {I : HopfIdeal k H} (hI : I.IsNormal) [Algebra.IsGeometricallyReduced k H]
    (hH : geometricallyConnectedCommHopfAlgProperty k H.obj)
    (hM : multiplicativeTypeCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient H I)) :
    I.IsCentral := by
  let K := AlgebraicClosure k
  let H' := FiniteTypeCommHopfAlgCat.baseChange (K := K) H
  let I' := CommHopfAlgCat.baseChangeHopfIdeal (K := K) I
  let _ : ConnectedSpace (PrimeSpectrum H') := hH.connectedSpace_algebraicClosureBaseChange
  let _ : IsReduced H' := inferInstanceAs (IsReduced (K ⊗[k] H))
  obtain ⟨M, ⟨e⟩⟩ :=
    (multiplicativeTypeCommHopfAlgProperty_iff_exists_iso_coordinateRing k _).mp hM
  let q := CommHopfAlgCat.quotientBaseChangeIso (K := K) I
  let f : H'.obj ⟶ (DiagonalizableGroup.coordinateRing K M).obj :=
    CommHopfAlgCat.mkQuotient H'.obj I' ≫ q.hom ≫ e.inv.hom
  let π : H' →ₐc[K] MonoidAlgebra K M := f.hom
  have hπ : Function.Surjective π :=
    (ConcreteCategory.bijective_of_isIso e.inv.hom).2.comp
      ((ConcreteCategory.bijective_of_isIso q.hom).2.comp
        (CommHopfAlgCat.mkQuotient_surjective H'.obj I'))
  have hker : kerOfSurjective π hπ = I' := by
    apply HopfIdeal.ext
    intro x
    rw [mem_kerOfSurjective, ← CommHopfAlgCat.mkQuotient_eq_zero_iff H'.obj I' x]
    simp only [π, f, _root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply,
      map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso e.inv.hom).1,
      map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso q.hom).1]
  have hcentral : I'.IsCentral := by
    rw [← hker]
    apply BialgHom.isCentral_kerOfSurjective_of_isNormal
    rw [hker]
    exact CommHopfAlgCat.isNormal_baseChangeHopfIdeal hI
  exact (CommHopfAlgCat.isCentral_baseChangeHopfIdeal_iff (K := K) I).mp hcentral

end

end TauCeti.HopfIdeal
