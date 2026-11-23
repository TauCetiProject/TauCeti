/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.GroupScheme
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.LinearlyReductive
public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Construction
import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Coordinate
import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Points
import TauCeti.Algebra.AlgebraicGroup.LinearlyReductive.FiniteIndex
import TauCeti.Algebra.AlgebraicGroup.LinearlyReductive.FiniteSubgroup
import TauCeti.Algebra.AlgebraicGroup.Reductive.CompleteReducibility
import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Embedding
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.NormalSubgroup
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Linear reductivity and the identity component

In characteristic zero, a finite-type affine group `G` over a field `k` — not assumed connected —
is linearly reductive if and only if its geometric identity component (the identity component after
base change to `AlgebraicClosure k`) is reductive. Equivalently, every rational representation of
`G` (finite- or infinite-dimensional) is completely reducible as soon as that geometric identity
component is reductive.

Several ingredients hold in arbitrary characteristic over an algebraically closed field `k`:

* If `G` is reduced, `G⁰` is linearly reductive, and `|π₀(G)|` is invertible in `k`, then `G` is
  linearly reductive (`linearlyReductiveCommHopfAlgProperty.of_identityComponent`), by finite-index
  Maschke averaging (`linearlyReductiveCommHopfAlgProperty.of_quotient_finiteIndex`).
* Conversely, if `G` is linearly reductive, then `|π₀(G)|` is invertible in `k` (without assuming
  reducedness), by descending linear reductivity to the finite constant component group `π₀(G)`
  along its injective coordinate morphism.
* If `G` is reduced and linearly reductive, its unipotent radical is trivial without any
  connectedness assumption, and hence its normal identity component `G⁰` is reductive.

In characteristic zero, Cartier's theorem supplies reducedness, the finite component count is
automatically nonzero in `k`, and reductivity of the connected group `G⁰` coincides with its linear
reductivity. Combining both directions over `AlgebraicClosure k` and descending linear reductivity
along `k ↪ AlgebraicClosure k` yields the full characteristic-zero equivalence.

## Main declarations

* `TauCeti.linearlyReductiveCommHopfAlgProperty.of_identityComponent`: over an algebraically closed
  field, a reduced finite-type group is linearly reductive if its identity component is linearly
  reductive and the number of connected components is invertible in `k`.
* `TauCeti.linearlyReductiveCommHopfAlgProperty.natCast_card_connectedComponents_ne_zero`: over an
  algebraically closed field, a linearly reductive finite-type group has component count invertible
  in `k`.
* `TauCeti.linearlyReductiveCommHopfAlgProperty.unipotentRadicalDefiningIdeal_eq_augmentation`:
  over an algebraically closed field, a reduced linearly reductive finite-type group has trivial
  unipotent radical.
* `TauCeti.linearlyReductiveCommHopfAlgProperty.reductive_identityComponent`: over an algebraically
  closed field, the identity component of a reduced linearly reductive finite-type group is
  reductive.
* `TauCeti.linearlyReductiveCommHopfAlgProperty_iff_reductive_identityComponent_of_isAlgClosed`:
  the equivalence over an algebraically closed field of characteristic zero.
* `TauCeti.linearlyReductiveCommHopfAlgProperty_iff_reductive_identityComponent`: **over any field
  of characteristic zero, a finite-type affine group is linearly reductive if and only if its
  geometric identity component is reductive.**
* `TauCeti.Comodule.isCompletelyReducible_of_reductive_identityComponent`: complete reducibility of
  arbitrary comodules over such a group.

## References

* J. S. Milne, *Algebraic Groups* (2017), Corollary 22.43.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
-/

public section

namespace TauCeti

open CategoryTheory WithConv

universe u w

section AlgClosed

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- Over an algebraically closed field, a reduced finite-type affine group is linearly reductive
whenever its identity component is linearly reductive and the number of connected components is
invertible in `k`. -/
theorem linearlyReductiveCommHopfAlgProperty.of_identityComponent [IsReduced H]
    (hcard : (Nat.card (ConnectedComponents (PrimeSpectrum H)) : k) ≠ 0)
    (h0 : linearlyReductiveCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.identityComponent H).obj) :
    linearlyReductiveCommHopfAlgProperty k H.obj := by
  let I := HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)
  let N := CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)
  let eker :
      (HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) ⧸
          (FiniteTypeCommHopfAlgCat.rationalComponentMap H).ker) ≃*
        ConnectedComponents (PrimeSpectrum H) :=
    QuotientGroup.quotientKerEquivOfSurjective
      (FiniteTypeCommHopfAlgCat.rationalComponentMap H)
      (FiniteTypeCommHopfAlgCat.rationalComponentMap_surjective H)
  have hker : (FiniteTypeCommHopfAlgCat.rationalComponentMap H).ker = N :=
    FiniteTypeCommHopfAlgCat.rationalComponentMap_ker H
  have _ : N.Normal := hker ▸ MonoidHom.normal_ker _
  have hindex : (N.index : k) ≠ 0 := by
    rw [Subgroup.index_eq_card,
      Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hker.symm).toEquiv.trans eker.toEquiv)]
    exact hcard
  exact linearlyReductiveCommHopfAlgProperty.of_quotient_finiteIndex I hindex h0

/-- Over an algebraically closed field, the number of connected components of a linearly reductive
finite-type affine group is invertible in `k`. No reducedness assumption is required. -/
theorem linearlyReductiveCommHopfAlgProperty.natCast_card_connectedComponents_ne_zero
    (hH : linearlyReductiveCommHopfAlgProperty k H.obj) :
    (Nat.card (ConnectedComponents (PrimeSpectrum H)) : k) ≠ 0 := by
  have hcomp :
      linearlyReductiveCommHopfAlgProperty k
        (CommHopfAlgCat.of k
          (ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H)))) :=
    hH.of_injective (FiniteTypeCommHopfAlgCat.componentCoordinateHom H)
      (FiniteTypeCommHopfAlgCat.componentCoordinateHom_injective H)
  let e := ConstantGroup.pointsMulEquiv k (ConnectedComponents (PrimeSpectrum H))
  have _ : Finite
      (WithConv (ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H)) →ₐ[k] k)) :=
    Finite.of_equiv _ e.toEquiv
  have htop := HopfAlgebra.natCast_card_ne_zero_of_isLinearlyReductive
    ((linearlyReductiveCommHopfAlgProperty_iff _ _).mp hcomp) ⊤
  have hcard :
      Nat.card (⊤ : Subgroup (WithConv
        (ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H)) →ₐ[k] k))) =
      Nat.card (ConnectedComponents (PrimeSpectrum H)) :=
    (Nat.card_congr (Equiv.Set.univ _)).trans (Nat.card_congr e.symm.toEquiv)
  rwa [hcard] at htop

/-- Over an algebraically closed field, a reduced linearly reductive finite-type affine group has
trivial unipotent radical. Connectedness is not required. -/
theorem linearlyReductiveCommHopfAlgProperty.unipotentRadicalDefiningIdeal_eq_augmentation
    [IsReduced H] (hH : linearlyReductiveCommHopfAlgProperty k H.obj) :
    FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H =
      HopfIdeal.augmentation k H := by
  have hu := (smoothUnipotentCommHopfAlgProperty_iff k _).mp
    (FiniteTypeCommHopfAlgCat.smoothUnipotent_unipotentRadical H)
  let _ : Algebra.Smooth k (FiniteTypeCommHopfAlgCat.unipotentRadical H) := hu.1
  let _ : IsReduced (FiniteTypeCommHopfAlgCat.unipotentRadical H) := isReduced_of_smooth k _
  exact HopfIdeal.eq_augmentation_of_isNormal_of_forall_isUnipotentPoint_of_isLinearlyReductive
    (FiniteTypeCommHopfAlgCat.isNormal_unipotentRadicalDefiningIdeal H)
    (geometricallyUnipotentPointsCommHopfAlgProperty.forall_isUnipotentPoint
      ((geometricallyUnipotentPointsCommHopfAlgProperty_iff _ _).mpr hu.2))
    ((linearlyReductiveCommHopfAlgProperty_iff k H.obj).mp hH)

/-- Over an algebraically closed field, the identity component of a reduced linearly reductive
finite-type affine group is reductive, in every characteristic. -/
theorem linearlyReductiveCommHopfAlgProperty.reductive_identityComponent
    [IsReduced H] (hH : linearlyReductiveCommHopfAlgProperty k H.obj) :
    reductiveCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.identityComponent H) := by
  rw [reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_eq_augmentation]
  refine ⟨(smoothCommHopfAlgProperty_iff _).mp
      (smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced k _),
    FiniteTypeCommHopfAlgCat.geometricallyConnected_identityComponent H, ?_⟩
  exact FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_quotient_eq_augmentation_of_isNormal
    H _ (FiniteTypeCommHopfAlgCat.isNormal_identityComponentHopfIdeal H)
    hH.unipotentRadicalDefiningIdeal_eq_augmentation

end AlgClosed

section CharZeroAlgClosed

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]

/-- Over an algebraically closed field of characteristic zero, a finite-type affine group is
linearly reductive if and only if its identity component is reductive. -/
theorem linearlyReductiveCommHopfAlgProperty_iff_reductive_identityComponent_of_isAlgClosed
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    linearlyReductiveCommHopfAlgProperty k H.obj ↔
      reductiveCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.identityComponent H) := by
  let _ : IsReduced H := HopfAlgebra.isReduced_of_charZero k H
  refine ⟨fun hH ↦ hH.reductive_identityComponent, fun h0 ↦ ?_⟩
  exact linearlyReductiveCommHopfAlgProperty.of_identityComponent
    (Nat.cast_ne_zero.mpr Nat.card_pos.ne') h0.linearlyReductive

end CharZeroAlgClosed

section CharZero

variable {k : Type u} [Field k] [CharZero k]

/-- **Linear reductivity via the identity component in characteristic zero.** Over any field of
characteristic zero, a finite-type affine group (not assumed connected) is linearly reductive if
and only if its geometric identity component is reductive. -/
theorem linearlyReductiveCommHopfAlgProperty_iff_reductive_identityComponent
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    linearlyReductiveCommHopfAlgProperty k H.obj ↔
      reductiveCommHopfAlgProperty (AlgebraicClosure k)
        (FiniteTypeCommHopfAlgCat.identityComponent
          (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H)) := by
  rw [← linearlyReductiveCommHopfAlgProperty_baseChange_iff (AlgebraicClosure k) H.obj]
  exact linearlyReductiveCommHopfAlgProperty_iff_reductive_identityComponent_of_isAlgClosed
    (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H)

/-- Every rational representation of a finite-type affine group in characteristic zero whose
geometric identity component is reductive is completely reducible over the original field, without
any connectedness or finite-dimensionality assumption. -/
theorem Comodule.isCompletelyReducible_of_reductive_identityComponent
    {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    (h0 : reductiveCommHopfAlgProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.identityComponent
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H)))
    {M : Type w} [AddCommMonoid M] [Module k M] [Comodule k H M] :
    Comodule.IsCompletelyReducible k H M :=
  ((linearlyReductiveCommHopfAlgProperty_iff k H.obj).mp
    ((linearlyReductiveCommHopfAlgProperty_iff_reductive_identityComponent H).mpr
      h0)).isCompletelyReducible

end CharZero

end TauCeti
