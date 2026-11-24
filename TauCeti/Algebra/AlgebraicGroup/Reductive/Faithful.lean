/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.Faithful.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive
import TauCeti.Algebra.AlgebraicGroup.Representation.Faithful.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Faithful
import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive.Ascent.CharZero

/-!
# A faithful completely reducible representation makes a group reductive

Over a field `k` of characteristic zero, a geometrically connected affine group of finite type
which has a faithful completely reducible finite-dimensional representation is reductive.

Smoothness is Cartier's theorem. After extension to an algebraic closure the representation stays
faithful, and in characteristic zero it stays completely reducible
(`TauCeti.Comodule.IsCompletelyReducible.baseChange`). A normal smooth unipotent subgroup of the
geometric fibre then acts trivially on every simple summand, and faithfulness makes it trivial
(`TauCeti.HopfIdeal.eq_augmentation_of_isNormal_of_smoothUnipotent_of_isFaithful`).

Characteristic zero is needed. For a purely inseparable extension `k'/k` of degree `p`, the Weil
restriction of `𝔾_m` from `k'` to `k` acts faithfully and irreducibly on `k'` by multiplication,
but it is not reductive: its geometric fibre has a nontrivial unipotent radical. The hypothesis
enters through Cartier's theorem and through the ascent of complete reducibility. Geometric
connectedness is needed because reductive groups are connected by definition here: the constant
group `ℤ/2ℤ` acting on `k` by a sign is faithful and completely reducible but not reductive.

## Main results

* `TauCeti.reductiveCommHopfAlgProperty_of_isFaithful_of_isCompletelyReducible`: a geometrically
  connected affine group of finite type over a field of characteristic zero with a faithful
  completely reducible representation is reductive.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§4.a, 19.b and 22.
* J. S. Milne, *Shimura varieties and moduli*, proof of Corollary 6.5.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u

/-- **A faithful completely reducible representation makes a connected group reductive.** Over a
field of characteristic zero, a geometrically connected affine group of finite type with a
faithful completely reducible representation is reductive. -/
theorem reductiveCommHopfAlgProperty_of_isFaithful_of_isCompletelyReducible
    {k : Type u} [Field k] [CharZero k] (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hconnected : geometricallyConnectedCommHopfAlgProperty k H.obj)
    {M : Type u} [AddCommGroup M] [Module k M] [Comodule k H M]
    (hM : Comodule.IsFaithful (k := k) (H := H) (V := M))
    (hcr : Comodule.IsCompletelyReducible k H M) :
    reductiveCommHopfAlgProperty k H := by
  let K := AlgebraicClosure k
  have hsmooth : Algebra.Smooth k H :=
    (smoothCommHopfAlgProperty_iff _).mp (smoothCommHopfAlgProperty_of_charZero k H.obj)
  let _ : IsReduced (K ⊗[k] H) := isReduced_of_smooth K (K ⊗[k] H)
  let _ := Comodule.baseChange (R := k) (H := H) (M := M) K
  refine reductiveCommHopfAlgProperty_of_geometricFiber_iso k H _ hsmooth hconnected
    (CategoryTheory.Iso.refl _) fun I hI hU ↦ ?_
  exact HopfIdeal.eq_augmentation_of_isNormal_of_smoothUnipotent_of_isFaithful K
    (FiniteTypeCommHopfAlgCat.baseChange (K := K) H) (K ⊗[k] M)
    (hcr.baseChange K) (hM.baseChange (K := K)) I hI hU

end TauCeti
