/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Symplectic.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Basic
import TauCeti.Algebra.AlgebraicGroup.Representation.Normal.Scalar
import TauCeti.Algebra.AlgebraicGroup.Symplectic.Reductive
import TauCeti.Algebra.AlgebraicGroup.Symplectic.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Symplectic.Smooth
import TauCeti.Algebra.AlgebraicGroup.Symplectic.Connected
import TauCeti.Algebra.AlgebraicGroup.Representation.ClosedSubgroup
import TauCeti.RingTheory.FiniteType.FiniteRange
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# The symplectic group is semisimple

The standard symplectic group `Sp₂ₘ` is semisimple over every field, in every rank and in every
characteristic, including characteristic two. A connected smooth normal solvable subgroup acts
by scalars on the simple standard representation. Preservation of the alternating form restricts
those scalars to square roots of one. A regular function with finite image on a reduced
connected affine scheme is constant, so the subgroup acts trivially. Faithfulness of the standard
representation identifies its defining ideal with the augmentation ideal.

The argument is `HopfIdeal.eq_augmentation_of_isFaithful_of_isNormal_of_isSolvable_of_pow_eq_one`
applied to the standard symplectic comodule, as in
`TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Semisimple` with the determinant replaced by the
alternating form. Reducedness of the subgroup is needed: this does not assert triviality of the
nonreduced connected central subgroup scheme `μ₂` in characteristic two. The rank-zero case,
where the carrier of the standard representation is a singleton, is handled separately.

## Main declarations

* `TauCeti.Symplectic.eq_augmentation_of_isNormal_of_isSolvable`: a connected reduced normal
  solvable closed subgroup of `Sp₂ₘ` over an algebraically closed field is trivial.
* `TauCeti.Symplectic.semisimpleCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra`:
  **`Sp₂ₘ` is semisimple over every field.**

## References

* J. S. Milne, *Algebraic Groups* (2017), §§19.b, 21, and 24.6.
* J. E. Humphreys, *Linear Algebraic Groups*, §§19 and 27.
* T. A. Springer, *Linear Algebraic Groups*, §§2.2, 2.4, and Chapter 8.
-/

public section

namespace TauCeti.Symplectic

open CategoryTheory

universe u

noncomputable section

attribute [local instance] standardComodule

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Every connected reduced normal solvable closed subgroup of `Sp₂ₘ` over an algebraically
closed field is trivial. Reducedness may be supplied by smoothness, but is the only subgroup
regularity needed here. -/
theorem eq_augmentation_of_isNormal_of_isSolvable
    (m : ℕ) (I : HopfIdeal k (coordinateHopfAlgebra k m)) (hI : I.IsNormal)
    [IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k m) I)]
    [ConnectedSpace (PrimeSpectrum (CommHopfAlgCat.quotient (coordinateHopfAlgebra k m) I))]
    [Group.IsSolvable (WithConv
      (CommHopfAlgCat.quotient (coordinateHopfAlgebra k m) I →ₐ[k] k))] :
    I = HopfIdeal.augmentation k (coordinateHopfAlgebra k m) := by
  cases m with
  | zero =>
    let _ : Subsingleton (Fin (0 + 0) → k) := ⟨fun f g ↦ funext fun i ↦ Fin.elim0 i⟩
    exact Comodule.eq_augmentation_of_isFaithful_of_subsingleton (M := Fin (0 + 0) → k) I
      (isFaithful_standardComodule k 0)
  | succ n =>
    let H := coordinateHopfAlgebra k (n + 1)
    let _ : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
    let _ : NeZero (n + 1 + (n + 1)) := ⟨by omega⟩
    let _ : IsReduced H := isReduced_of_smooth k H
    let _ : ConnectedSpace (PrimeSpectrum H) :=
      geometricallyConnectedCommHopfAlgProperty.connectedSpace k H
        (geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra k (n + 1))
    -- The alternating form confines the scalars to square roots of one.
    exact HopfIdeal.eq_augmentation_of_isFaithful_of_isNormal_of_isSolvable_of_pow_eq_one
      (V := Fin (n + 1 + (n + 1)) → k) I hI (isFaithful_standardComodule k (n + 1)) two_pos
      fun g c hc ↦ scalar_sq_eq_one_of_basePointsRepresentation_eq_smul k (n + 1)
        (Nat.succ_ne_zero n) _ c hc

/-- **The symplectic group is semisimple over every field and in every rank.** -/
theorem semisimpleCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra
    (k : Type u) [Field k] (m : ℕ) :
    semisimpleCommHopfAlgProperty k (finiteTypeCoordinateHopfAlgebra k m) := by
  have hred := reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra k m
  let K := AlgebraicClosure k
  let B := FiniteTypeCommHopfAlgCat.baseChange (K := K) (finiteTypeCoordinateHopfAlgebra k m)
  let G := coordinateHopfAlgebra K m
  let e : B.obj ≅ G :=
    (forget₂ (FiniteTypeCommHopfAlgCat K) (_root_.CommHopfAlgCat K)).mapIso
      (finiteTypeCoordinateHopfAlgebraBaseChangeIso k K m) ≪≫
        eqToIso (finiteTypeCoordinateHopfAlgebra_obj K m)
  apply semisimpleCommHopfAlgProperty_of_geometricFiber_iso k _ G
    hred.smooth hred.geometricallyConnected e
  intro I hnormal hconnected hsmooth hsolvable
  let _ : Algebra.Smooth K (CommHopfAlgCat.quotient G I) := hsmooth
  let _ : IsReduced (CommHopfAlgCat.quotient G I) := isReduced_of_smooth K _
  let _ : ConnectedSpace (PrimeSpectrum (CommHopfAlgCat.quotient G I)) :=
    geometricallyConnectedCommHopfAlgProperty.connectedSpace K _ hconnected
  let _ : Group.IsSolvable
      (WithConv (CommHopfAlgCat.quotient G I →ₐ[K] AlgebraicClosure K)) :=
    (geometricallySolvablePointsCommHopfAlgProperty_iff K _).mp hsolvable
  let φ : K →ₐ[K] AlgebraicClosure K := Algebra.ofId K (AlgebraicClosure K)
  let _ : Group.IsSolvable (WithConv (CommHopfAlgCat.quotient G I →ₐ[K] K)) :=
    Group.isSolvable_of_isSolvable_injective (AlgHom.mapValue_injective φ.injective)
  exact eq_augmentation_of_isNormal_of_isSolvable m I hnormal

end

end TauCeti.Symplectic
