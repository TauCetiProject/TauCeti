/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Connected
public import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Irreducible
import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.LowRank
import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Torus
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Faithful
import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.BaseChange
import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Smooth

/-!
# Reductivity of the special orthogonal groups

Let `SOₙ` be the special orthogonal group of the standard symmetric form over a field of
characteristic different from two. In dimension at least three, every normal smooth unipotent
closed subgroup of `SOₙ` is trivial. Equivalently, its unipotent radical is trivial.

The standard representation supplies the decisive input. It is faithful in every dimension and
simple in dimension at least three, hence completely reducible. The general normal-invariants
theorem then forces a normal smooth unipotent subgroup to act trivially, and faithfulness
identifies its defining Hopf ideal with the augmentation ideal.

Smoothness is already known away from characteristic two, and so is geometric connectedness, so
reductivity follows in dimension at least three. Together with the dimension-zero and
dimension-one cases, where the group is special linear, and the dimension-two case, where it is a
torus, this makes every standard special orthogonal group reductive away from characteristic two.

## Main declarations

* `TauCeti.SpecialOrthogonal.eq_augmentation_of_isNormal_of_smoothUnipotent_of_three_le`:
  every normal smooth unipotent closed subgroup of `SOₙ` is trivial when `3 ≤ n`.
* `TauCeti.SpecialOrthogonal.unipotentRadicalDefiningIdeal_eq_augmentation_of_three_le`:
  the unipotent radical of `SOₙ` is trivial when `3 ≤ n`.
* `TauCeti.SpecialOrthogonal.reductiveCommHopfAlgProperty_iff_geometricallyConnected_of_three_le`:
  in these dimensions and characteristics, `SOₙ` is reductive exactly when it is geometrically
  connected.
* `TauCeti.SpecialOrthogonal.reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra`: `SOₙ`
  is reductive in every dimension, over every field of characteristic different from two.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§ 4.a, 19.b, and 21.
* T. A. Springer, *Linear Algebraic Groups*, §§ 2.2, 2.4, and Chapter 8.
* Formal proof architecture: `TauCeti.Algebra.AlgebraicGroup.Symplectic.Reductive`.
-/

public section

open CategoryTheory

namespace TauCeti.SpecialOrthogonal

universe u

noncomputable section

open HopfIdeal

/-- The coordinate Hopf algebra and the underlying object of its finite-type package are
canonically identical. -/
private noncomputable def coordinateHopfAlgebraFiniteTypeObjIso
    (R : Type u) [CommRing R] (n : Nat) :
    coordinateHopfAlgebra R n ≅ (finiteTypeCoordinateHopfAlgebra R n).obj :=
  eqToIso (finiteTypeCoordinateHopfAlgebra_obj R n).symm

/-- **Every normal smooth unipotent closed subgroup of `SOₙ` is trivial in dimension at least
three**, over an algebraically closed field of characteristic different from two.

The conclusion is contravariant: the defining Hopf ideal of the subgroup is the augmentation
ideal of the special-orthogonal coordinate algebra. -/
theorem eq_augmentation_of_isNormal_of_smoothUnipotent_of_three_le
    (k : Type u) [Field k] [IsAlgClosed k] [NeZero (2 : k)] (n : Nat) (hn : 3 ≤ n)
    (I : HopfIdeal k (finiteTypeCoordinateHopfAlgebra k n)) (hI : I.IsNormal)
    (hU : smoothUnipotentCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient (finiteTypeCoordinateHopfAlgebra k n) I)) :
    I = HopfIdeal.augmentation k (finiteTypeCoordinateHopfAlgebra k n) := by
  let _ : Invertible (2 : k) := invertibleOfNonzero (NeZero.ne _)
  let e := coordinateHopfAlgebraFiniteTypeObjIso k n
  let H : FiniteTypeCommHopfAlgCat k :=
    ⟨coordinateHopfAlgebra k n, by
      rw [← finiteTypeCoordinateHopfAlgebra_obj]
      exact (finiteTypeCoordinateHopfAlgebra k n).property⟩
  let _ : IsReduced H := by
    -- `H` packages this coordinate algebra with its finite-type proof, so its carrier is
    -- definitionally the coordinate algebra on which smoothness supplies reducedness.
    change IsReduced (coordinateHopfAlgebra k n)
    exact isReduced_of_smooth_of_field k _
  let _ : Comodule k (coordinateHopfAlgebra k n) (Fin n → k) := standardComodule k n
  exact HopfIdeal.eq_augmentation_of_isNormal_of_smoothUnipotent_of_isFaithful_of_iso
    k H (Fin n → k) (finiteTypeCoordinateHopfAlgebra k n) e
      (isCompletelyReducible_standardComodule_of_three_le k n hn)
      (isFaithful_standardComodule k n) I hI hU

/-- **The unipotent radical of `SOₙ` is trivial in dimension at least three** over an
algebraically closed field of characteristic different from two. -/
theorem unipotentRadicalDefiningIdeal_eq_augmentation_of_three_le
    (k : Type u) [Field k] [IsAlgClosed k] [NeZero (2 : k)] (n : Nat) (hn : 3 ≤ n) :
    FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal
        (finiteTypeCoordinateHopfAlgebra k n) =
      HopfIdeal.augmentation k (finiteTypeCoordinateHopfAlgebra k n) := by
  rw [FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_eq_augmentation_iff]
  intro I hI
  exact eq_augmentation_of_isNormal_of_smoothUnipotent_of_three_le
    k n hn I hI.isNormal hI.smoothUnipotent

/-- **In dimension at least three and characteristic different from two, `SOₙ` is reductive
if and only if it is geometrically connected.**

Smoothness and triviality of every normal smooth unipotent subgroup of the geometric fibre are
automatic under these hypotheses, so geometric connectedness is the only remaining condition. -/
theorem reductiveCommHopfAlgProperty_iff_geometricallyConnected_of_three_le
    (k : Type u) [Field k] [NeZero (2 : k)] (n : Nat) (hn : 3 ≤ n) :
    reductiveCommHopfAlgProperty k (finiteTypeCoordinateHopfAlgebra k n) ↔
      geometricallyConnectedCommHopfAlgProperty k (coordinateHopfAlgebra k n) := by
  constructor
  · intro h
    rw [← finiteTypeCoordinateHopfAlgebra_obj]
    exact h.geometricallyConnected
  · intro hconnected
    let _ : Invertible (2 : k) := invertibleOfNonzero (NeZero.ne _)
    have htwo : (2 : AlgebraicClosure k) ≠ 0 := by
      simpa only [map_ofNat] using
        (map_ne_zero (algebraMap k (AlgebraicClosure k))).2 (NeZero.ne (2 : k))
    let _ : NeZero (2 : AlgebraicClosure k) := ⟨htwo⟩
    let e := coordinateHopfAlgebraFiniteTypeObjIso k n
    apply reductiveCommHopfAlgProperty_of_geometricFiber_iso k _
      (finiteTypeCoordinateHopfAlgebra (AlgebraicClosure k) n)
      ((smoothCommHopfAlgProperty_iff _).mp <|
        (smoothCommHopfAlgProperty k).prop_of_iso e
          ((smoothCommHopfAlgProperty_iff _).mpr inferInstance))
      ((geometricallyConnectedCommHopfAlgProperty k).prop_of_iso e hconnected)
      (finiteTypeCoordinateHopfAlgebraBaseChangeIso k (AlgebraicClosure k) n)
    intro I hI hU
    exact eq_augmentation_of_isNormal_of_smoothUnipotent_of_three_le
      (AlgebraicClosure k) n hn I hI hU

/-- **`SOₙ` is reductive in dimension at least three**, over every field of characteristic
different from two. -/
theorem reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra_of_three_le
    (k : Type u) [Field k] [NeZero (2 : k)] (n : Nat) (hn : 3 ≤ n) :
    reductiveCommHopfAlgProperty k (finiteTypeCoordinateHopfAlgebra k n) :=
  (reductiveCommHopfAlgProperty_iff_geometricallyConnected_of_three_le k n hn).mpr
    (geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra k n)

/-- **Every standard special orthogonal group is reductive**, over every field of characteristic
different from two.

The dimension-zero and dimension-one groups are special linear, the dimension-two group is a
torus, and from dimension three on the standard representation is simple, which makes the
unipotent radical trivial. -/
theorem reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra
    (k : Type u) [Field k] [NeZero (2 : k)] (n : Nat) :
    reductiveCommHopfAlgProperty k (finiteTypeCoordinateHopfAlgebra k n) :=
  match n with
  | 0 => reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra_zero k
  | 1 => reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra_one k
  | 2 => reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra_two k
  | (m + 3) =>
    reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra_of_three_le k (m + 3)
      (by omega)

end

end TauCeti.SpecialOrthogonal
