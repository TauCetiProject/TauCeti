/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Center
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Construction
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Isomorphism
import TauCeti.Algebra.AlgebraicGroup.Center.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Center.Isomorphism
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.SmoothConnected
import TauCeti.Algebra.AlgebraicGroup.Representation.Normal.Scalar
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.SmoothConnected
import TauCeti.Algebra.AlgebraicGroup.Smooth.GeometricallyReduced
import TauCeti.RingTheory.FiniteType.PointSeparation

/-!
# The solvable radical of the general linear group

The solvable radical of `GLₙ` is its scalar center. A connected reduced normal solvable
closed subgroup acts by scalars on the simple standard representation. Point separation
then promotes scalar action on rational points to containment in the scheme-theoretic
center. In positive rank the center is the multiplicative group, hence smooth, connected,
and solvable, so the universal property of the radical gives equality.

The distinction between a subgroup scheme and its rational points matters here: reducedness
is used explicitly in point separation, and no assertion is made about nonreduced solvable
normal subgroup schemes.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 6 and 19.
* J. E. Humphreys, *Linear Algebraic Groups*, §§19 and 27.

The representation-theoretic input is `HopfIdeal.exists_basePointsRepresentation_eq_smul`;
the scalar center is represented by `GeneralLinear.centerCoordinateLaurentIso`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear

universe u

noncomputable section

attribute [local instance] standardComodule

variable {k : Type u} [Field k]

section AlgebraicallyClosed

variable [IsAlgClosed k]

/-- A connected reduced normal solvable closed subgroup of `GLₙ` over an algebraically
closed field is contained in its scheme-theoretic center, in every rank and characteristic. -/
theorem centerDefiningIdeal_le_of_isNormal_of_isSolvable
    (n : ℕ) (I : HopfIdeal k (coordinateHopfAlgebra k n)) (hI : I.IsNormal)
    [IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) I)]
    [ConnectedSpace (PrimeSpectrum (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) I))]
    [Group.IsSolvable (WithConv
      (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) I →ₐ[k] k))] :
    CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n) ≤ I := by
  let H := coordinateHopfAlgebra k n
  let Q := CommHopfAlgCat.quotient H I
  let q := (CommHopfAlgCat.mkQuotient H I).hom
  let _ : IsReduced H := isReduced_of_smooth k H
  let _ : ConnectedSpace (PrimeSpectrum H) :=
    geometricallyConnectedCommHopfAlgProperty.connectedSpace k H
      (geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra k n)
  -- Lie–Kolchin and normality make the standard action scalar on rational subgroup points.
  have hcentral (f : Q →ₐ[k] k) :
      AlgHom.mapDomain q (toConv f) ∈
        CommHopfAlgCat.centerPointsSubgroup H (CommAlgCat.of k k) := by
    have hmatrix : pointsMulEquiv n (AlgHom.mapDomain q (toConv f)) ∈
        Subgroup.center (Matrix.GeneralLinearGroup (Fin n) k) := by
      cases n with
      | zero =>
        have h : pointsMulEquiv 0 (AlgHom.mapDomain q (toConv f)) = 1 :=
          Matrix.GeneralLinearGroup.ext fun i ↦ i.elim0
        rw [h]
        exact Subgroup.one_mem _
      | succ m =>
        let _ : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
        obtain ⟨c, hc⟩ := HopfIdeal.exists_basePointsRepresentation_eq_smul
          (V := Fin (m + 1) → k) I hI (toConv f)
        have hm : pointsMulEquiv (m + 1) (AlgHom.mapDomain q (toConv f)) =
            Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) c := by
          apply Units.ext
          apply Matrix.mulVec_injective
          funext w
          have hv := LinearMap.congr_fun hc w
          rw [basePointsRepresentation_eq_mulVec] at hv
          ext i
          simpa [pointsMulEquiv_apply, Matrix.mulVec_diagonal, q] using congrFun hv i
        rw [hm, Matrix.GeneralLinearGroup.center_eq_range_scalar]
        exact ⟨c, rfl⟩
    rw [← map_centerPointsSubgroup_pointsMulEquiv_eq_center n (CommAlgCat.of k k)] at hmatrix
    obtain ⟨g, hg, heq⟩ := hmatrix
    exact (pointsMulEquiv n).injective heq ▸ hg
  -- Reducedness upgrades rational-point containment to containment of closed subgroup schemes.
  intro x hx
  apply (CommHopfAlgCat.mkQuotient_eq_zero_iff H I x).mp
  apply eq_of_forall_algHom_apply_eq (k := k) (K := k)
  intro f
  have h := (CommHopfAlgCat.mem_quotientPointsSubgroup_iff H
    (CommHopfAlgCat.centerDefiningIdeal H) (CommAlgCat.of k k) _).mp (hcentral f) x hx
  simpa [AlgHom.mapDomain_apply, q] using h

end AlgebraicallyClosed

/-- The center of `GLₙ` is a solvable-radical candidate over any field, including rank zero. -/
theorem isSolvableRadicalCandidate_centerDefiningIdeal
    (n : ℕ) :
    HopfIdeal.IsSolvableRadicalCandidate (finiteTypeCoordinateHopfAlgebra k n)
      (CommHopfAlgCat.centerDefiningIdeal (finiteTypeCoordinateHopfAlgebra k n).obj) := by
  by_cases hn : n = 0
  · subst n
    have he : CommHopfAlgCat.centerDefiningIdeal (finiteTypeCoordinateHopfAlgebra k 0).obj =
        HopfIdeal.augmentation k (finiteTypeCoordinateHopfAlgebra k 0) := by
      apply (CommHopfAlgCat.centerDefiningIdeal_eq_augmentation_iff_forall_isCentralPoint_eq_one
        (finiteTypeCoordinateHopfAlgebra k 0).obj).mpr
      intro A g _
      let e := (AlgHom.mapDomainMulEquiv (A := A)
        (_root_.CommHopfAlgCat.ofIso
          (eqToIso (finiteTypeCoordinateHopfAlgebra_obj k 0)).symm)).trans
          (pointsMulEquiv (R := k) (A := A) 0)
      apply e.injective
      rw [map_one]
      exact Matrix.GeneralLinearGroup.ext fun i ↦ i.elim0
    rw [he]
    exact HopfIdeal.isSolvableRadicalCandidate_augmentation _
  let H := finiteTypeCoordinateHopfAlgebra k n
  let I := CommHopfAlgCat.centerDefiningIdeal H.obj
  let G := FGCommGrpCat.of (Multiplicative ℤ)
  let e : CommHopfAlgCat.quotient H.obj I ≅ (DiagonalizableGroup.coordinateRing k G).obj :=
    CommHopfAlgCat.centerCoordinateIso (eqToIso (finiteTypeCoordinateHopfAlgebra_obj k n)) ≪≫
      centerCoordinateLaurentIso n (Nat.pos_of_ne_zero hn) ≪≫
      _root_.CommHopfAlgCat.isoMk (AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ)
  have hc := (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso e.symm
    (DiagonalizableGroup.geometricallyConnected_coordinateRing k G)
  have hr := (geometricallyReducedCommHopfAlgProperty k).prop_of_iso e.symm
    (DiagonalizableGroup.geometricallyReduced_coordinateRing k G)
  let _ : Coalgebra.IsCocomm k (FiniteTypeCommHopfAlgCat.quotient H I) :=
    (CommHopfAlgCat.isCentral_centerDefiningIdeal H.obj).isCocomm_quotient
  exact HopfIdeal.IsSolvableRadicalCandidate.mk
    (CommHopfAlgCat.isCentral_centerDefiningIdeal H.obj).isNormal hc
    ((smoothCommHopfAlgProperty_iff _).mp
      (smoothCommHopfAlgProperty_of_geometricallyReduced k _ hr))
    (geometricallySolvablePointsCommHopfAlgProperty_of_isCocomm k _)

/-- Every connected normal smooth geometrically solvable closed subgroup of `GLₙ` is
contained in the scalar center. This holds over arbitrary, possibly imperfect, fields. -/
theorem centerDefiningIdeal_le_of_isSolvableRadicalCandidate
    (n : ℕ) (I : HopfIdeal k (finiteTypeCoordinateHopfAlgebra k n))
    (hI : HopfIdeal.IsSolvableRadicalCandidate (finiteTypeCoordinateHopfAlgebra k n) I) :
    CommHopfAlgCat.centerDefiningIdeal (finiteTypeCoordinateHopfAlgebra k n).obj ≤ I := by
  -- Work over an algebraic closure, then reflect the ideal containment by faithful flatness.
  let K := AlgebraicClosure k
  let H := finiteTypeCoordinateHopfAlgebra k n
  let B := FiniteTypeCommHopfAlgCat.baseChange (K := K) H
  -- Present the geometric fibre with the coordinate model used by the scalar-action theorem.
  let G : FiniteTypeCommHopfAlgCat K :=
    ⟨coordinateHopfAlgebra K n, inferInstanceAs (Algebra.FiniteType K (coordinateHopfAlgebra K n))⟩
  let e : G ≅ B := (finiteTypeCommHopfAlgProperty K).isoMk
    (eqToIso (finiteTypeCoordinateHopfAlgebra_obj K n).symm) ≪≫
      (finiteTypeCoordinateHopfAlgebraBaseChangeIso k K n).symm
  let J := (CommHopfAlgCat.baseChangeHopfIdeal (K := K) I).comapOfSurjective
    (FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
    (ConcreteCategory.bijective_of_isIso e.hom).2
  have hJ : HopfIdeal.IsSolvableRadicalCandidate G J := hI.baseChange.comapOfIso e
  let _ : Algebra.Smooth K (CommHopfAlgCat.quotient G.obj J) := hJ.smooth
  let _ : IsReduced (CommHopfAlgCat.quotient G.obj J) := isReduced_of_smooth K _
  let _ : ConnectedSpace (PrimeSpectrum (CommHopfAlgCat.quotient G.obj J)) :=
    geometricallyConnectedCommHopfAlgProperty.connectedSpace K _ hJ.geometricallyConnected
  let _ : Group.IsSolvable
      (WithConv (CommHopfAlgCat.quotient G.obj J →ₐ[K] AlgebraicClosure K)) :=
    (geometricallySolvablePointsCommHopfAlgProperty_iff K _).mp hJ.geometricallySolvable
  let χ : K →ₐ[K] AlgebraicClosure K := Algebra.ofId K (AlgebraicClosure K)
  let _ : Group.IsSolvable (WithConv (CommHopfAlgCat.quotient G.obj J →ₐ[K] K)) :=
    Group.isSolvable_of_isSolvable_injective (AlgHom.mapValue_injective χ.injective)
  have hle := centerDefiningIdeal_le_of_isNormal_of_isSolvable n J hJ.isNormal
  apply (CommHopfAlgCat.baseChangeHopfIdeal_le_iff (K := K) (algebraMap k K).injective).mp
  rw [CommHopfAlgCat.baseChangeHopfIdeal_centerDefiningIdeal]
  let e₀ : G.obj ≅ B.obj :=
    (forget₂ (FiniteTypeCommHopfAlgCat K) (_root_.CommHopfAlgCat K)).mapIso e
  intro x hx
  obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso e₀.hom).2 x
  have hy : y ∈ CommHopfAlgCat.centerDefiningIdeal G.obj := by
    rw [← CommHopfAlgCat.comapOfSurjective_centerDefiningIdeal e₀]
    exact HopfIdeal.mem_comapOfSurjective.mpr hx
  exact HopfIdeal.mem_comapOfSurjective.mp (hle hy)

/-- **The solvable radical of `GLₙ` is its center**, over every field, in every rank,
and in every characteristic. The equality is between their defining Hopf ideals. -/
@[simp]
theorem solvableRadicalDefiningIdeal_eq_centerDefiningIdeal (n : ℕ) :
    FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal (finiteTypeCoordinateHopfAlgebra k n) =
      CommHopfAlgCat.centerDefiningIdeal (finiteTypeCoordinateHopfAlgebra k n).obj := by
  apply le_antisymm
  · exact FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal_le _ _
      (isSolvableRadicalCandidate_centerDefiningIdeal n)
  · exact centerDefiningIdeal_le_of_isSolvableRadicalCandidate n _
      (FiniteTypeCommHopfAlgCat.isSolvableRadicalCandidate_solvableRadicalDefiningIdeal _)

end

end TauCeti.GeneralLinear
