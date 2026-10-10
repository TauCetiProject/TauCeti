/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Basic
import TauCeti.Algebra.AlgebraicGroup.Representation.Normal.Scalar
import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.BaseChange
import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Connected
import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Irreducible
import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Reductive
import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Smooth
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# The special orthogonal group is semisimple in dimension at least three

Let `SOₙ` be the special orthogonal group of the standard symmetric form over a field of
characteristic different from two. In dimension at least three it is semisimple. A connected
reduced normal solvable subgroup acts by scalars on the standard representation, which is simple
in these dimensions. Preservation of the symmetric form restricts those scalars to square roots
of one. A regular function with finite image on a reduced connected affine scheme is constant,
so the subgroup acts trivially. Faithfulness of the standard representation identifies its
defining ideal with the augmentation ideal.

The argument is `HopfIdeal.eq_augmentation_of_isFaithful_of_isNormal_of_isSolvable_of_pow_eq_one`
applied to the standard special orthogonal comodule, as in
`TauCeti.Algebra.AlgebraicGroup.Symplectic.Semisimple` with the alternating form replaced by the
symmetric form. The dimension bound is necessary: `SO₂` is a torus, hence not semisimple. The
characteristic restriction is the one under which `SOₙ` is known to be smooth and geometrically
connected.

## Main declarations

* `eq_augmentation_of_isNormal_of_isSolvable_of_three_le`: a connected reduced normal solvable
  closed subgroup of `SOₙ` over an algebraically closed field of characteristic different from
  two is trivial when `3 ≤ n`.
* `semisimpleCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra_of_three_le`:
  **`SOₙ` is semisimple when `3 ≤ n`**, over every field of characteristic different from two.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§19.b and 21, and Chapter 24.
* J. E. Humphreys, *Linear Algebraic Groups*, §§19 and 27.
* T. A. Springer, *Linear Algebraic Groups*, §§2.2, 2.4, and Chapter 8.
-/

public section

namespace TauCeti.SpecialOrthogonal

open CategoryTheory

universe u

noncomputable section

attribute [local instance] standardComodule

variable {k : Type u} [Field k] [IsAlgClosed k] [NeZero (2 : k)]

/-- Every connected reduced normal solvable closed subgroup of `SOₙ`, `3 ≤ n`, over an
algebraically closed field of characteristic different from two is trivial. Reducedness may be
supplied by smoothness, but is the only subgroup regularity needed here. -/
theorem eq_augmentation_of_isNormal_of_isSolvable_of_three_le
    (n : ℕ) (hn : 3 ≤ n) (I : HopfIdeal k (coordinateHopfAlgebra k n)) (hI : I.IsNormal)
    [IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) I)]
    [ConnectedSpace (PrimeSpectrum (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) I))]
    [Group.IsSolvable (WithConv
      (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) I →ₐ[k] k))] :
    I = HopfIdeal.augmentation k (coordinateHopfAlgebra k n) := by
  let H := coordinateHopfAlgebra k n
  let _ : Invertible (2 : k) := invertibleOfNonzero (NeZero.ne _)
  let _ : IsReduced H := isReduced_of_smooth k H
  let _ : ConnectedSpace (PrimeSpectrum H) :=
    geometricallyConnectedCommHopfAlgProperty.connectedSpace k H
      (geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra k n)
  let _ : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let _ : IsSimpleOrder (Subcomodule k H (Fin n → k)) :=
    isSimpleOrder_subcomodule_of_three_le k n hn
  -- The symmetric form confines the scalars to square roots of one.
  exact HopfIdeal.eq_augmentation_of_isFaithful_of_isNormal_of_isSolvable_of_pow_eq_one
    (V := Fin n → k) I hI (isFaithful_standardComodule k n) two_pos
    fun g c hc ↦ scalar_sq_eq_one_of_basePointsRepresentation_eq_smul k n (by omega) _ c hc

/-- **The special orthogonal group is semisimple in dimension at least three**, over every field
of characteristic different from two. -/
theorem semisimpleCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra_of_three_le
    (k : Type u) [Field k] [NeZero (2 : k)] (n : ℕ) (hn : 3 ≤ n) :
    semisimpleCommHopfAlgProperty k (finiteTypeCoordinateHopfAlgebra k n) := by
  have hred := reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra k n
  let K := AlgebraicClosure k
  have htwo : (2 : K) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap k K)).2 (NeZero.ne (2 : k))
  let _ : NeZero (2 : K) := ⟨htwo⟩
  let B := FiniteTypeCommHopfAlgCat.baseChange (K := K) (finiteTypeCoordinateHopfAlgebra k n)
  let G := coordinateHopfAlgebra K n
  let e : B.obj ≅ G :=
    (forget₂ (FiniteTypeCommHopfAlgCat K) (_root_.CommHopfAlgCat K)).mapIso
      (finiteTypeCoordinateHopfAlgebraBaseChangeIso k K n) ≪≫
        eqToIso (finiteTypeCoordinateHopfAlgebra_obj K n)
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
  exact eq_augmentation_of_isNormal_of_isSolvable_of_three_le n hn I hnormal

end

end TauCeti.SpecialOrthogonal
