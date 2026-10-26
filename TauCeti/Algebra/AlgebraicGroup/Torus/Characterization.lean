/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.EssentialImage
public import TauCeti.Algebra.AlgebraicGroup.Torus.SmoothConnected
import Mathlib.LinearAlgebra.FreeModule.PID
import TauCeti.Algebra.AlgebraicGroup.Connected.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.Connected.BaseChange
import TauCeti.Algebra.AlgebraicGroup.GeometricallyReduced.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
import TauCeti.Algebra.MonoidAlgebra.Torsion

/-!
# Characterization of tori among groups of multiplicative type

A finite-type group of multiplicative type is a torus exactly when it is geometrically connected
and geometrically reduced. After passing to an algebraic closure, its coordinate ring is a group
algebra. Reducedness and connectedness force the character group to be torsion-free, while finite
generation then identifies it with a finite-rank free abelian group.

## Main declarations

* `TauCeti.splitTorusCommHopfAlgProperty_coordinateRing`: the coordinate Hopf algebra of a
  finitely generated torsion-free commutative group is a split torus.
* `TauCeti.splitTorusCommHopfAlgProperty.groupLikeSpanned`: every split torus is diagonalizable.
* `iff_multiplicativeType_and_geometricallyConnected_and_geometricallyReduced`: a finite-type
  commutative Hopf algebra over a field is a torus exactly when it is of multiplicative type,
  geometrically connected, and geometrically reduced.
* `TauCeti.torusCommHopfAlgProperty.of_groupLikeSetSpan_eq_top`: over an algebraically closed
  field, a reduced connected diagonalizable group is a torus.

## References

* J. S. Milne, *Algebraic Groups* (2017), Definitions 12.14 and 12.17.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

private theorem exists_mulEquiv_finsupp_int
    (G : Type u) [CommGroup G] [Group.FG G] [IsMulTorsionFree G] :
    ∃ n : ℕ, Nonempty (G ≃* Multiplicative (Fin n →₀ ℤ)) := by
  have : HasUniqueRoots G :=
    ⟨fun _ hn _ _ h ↦ eq_of_pow_eq_pow_of_commute hn (Commute.all _ _) h⟩
  let _ : Module.Finite ℤ (Additive G) :=
    Module.Finite.iff_addGroup_fg.mpr (inferInstance : AddGroup.FG (Additive G))
  let _ : Module.IsTorsionFree ℤ (Additive G) := inferInstance
  let _ : Module.Free ℤ (Additive G) := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis ℤ (Additive G)
  let _ : Finite (Module.Free.ChooseBasisIndex ℤ (Additive G)) :=
    Module.Finite.finite_basis b
  let eι := Finite.equivFin (Module.Free.ChooseBasisIndex ℤ (Additive G))
  let e : Additive G ≃+ (Fin (Nat.card (Module.Free.ChooseBasisIndex ℤ (Additive G))) →₀ ℤ) :=
    b.repr.toAddEquiv.trans (Finsupp.domCongr eι)
  exact ⟨_, ⟨AddEquiv.toMultiplicative e⟩⟩

/-- **The coordinate Hopf algebra of a finitely generated torsion-free commutative group is a
split torus.** Such a `G` is free of some finite rank `n`, which is then the rank of the split
torus. -/
theorem splitTorusCommHopfAlgProperty_coordinateRing (K : Type u) [CommRing K]
    (G : FGCommGrpCat.{u}) [IsMulTorsionFree G] :
    splitTorusCommHopfAlgProperty K (DiagonalizableGroup.coordinateRing K G) := by
  rw [splitTorusCommHopfAlgProperty_iff]
  obtain ⟨n, ⟨e⟩⟩ := exists_mulEquiv_finsupp_int G
  exact ⟨n, ⟨ObjectProperty.isoMk _ <| _root_.CommHopfAlgCat.isoMk
    (MonoidAlgebra.domCongrBialgEquiv K K
      ((AddEquiv.toMultiplicative (Finsupp.domCongr Equiv.ulift)).trans e.symm))⟩⟩

/-- **Every split torus is diagonalizable:** its coordinate Hopf algebra is spanned by its
group-like elements. -/
@[grind →]
theorem splitTorusCommHopfAlgProperty.groupLikeSpanned
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : splitTorusCommHopfAlgProperty k H) :
    DiagonalizableGroup.groupLikeSpannedProperty k H := by
  obtain ⟨n, ⟨e⟩⟩ := (splitTorusCommHopfAlgProperty_iff k H).mp hH
  exact (DiagonalizableGroup.groupLikeSpannedProperty k).prop_of_iso e
    ((DiagonalizableGroup.groupLikeSpannedProperty_iff k _).mpr
      (MonoidAlgebra.groupLikeSetSpan_eq_top (R := k) _))

namespace torusCommHopfAlgProperty

/-- **A finite-type commutative Hopf algebra over a field is a torus if and only if it is a
group of multiplicative type, geometrically connected, and geometrically reduced.** -/
theorem iff_multiplicativeType_and_geometricallyConnected_and_geometricallyReduced
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    torusCommHopfAlgProperty k H ↔
      multiplicativeTypeCommHopfAlgProperty k H ∧
      geometricallyConnectedCommHopfAlgProperty k H.obj ∧
      geometricallyReducedCommHopfAlgProperty k H.obj := by
  constructor
  · intro hH
    exact ⟨hH.multiplicativeType, hH.geometricallyConnected, hH.geometricallyReduced⟩
  · rintro ⟨hmt, hconnected, hreduced⟩
    rw [multiplicativeTypeCommHopfAlgProperty_iff_exists_iso_coordinateRing] at hmt
    obtain ⟨G, ⟨i⟩⟩ := hmt
    let i' := (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k))
      (CommHopfAlgCat.{u} (AlgebraicClosure k))).mapIso i
    have hconnected' : geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)
        (DiagonalizableGroup.coordinateRing (AlgebraicClosure k) G).obj :=
      (geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)).prop_of_iso i'.symm
        (geometricallyConnectedCommHopfAlgProperty.baseChange
          k (AlgebraicClosure k) H.obj hconnected)
    have hreduced' : geometricallyReducedCommHopfAlgProperty (AlgebraicClosure k)
        (DiagonalizableGroup.coordinateRing (AlgebraicClosure k) G).obj :=
      (geometricallyReducedCommHopfAlgProperty (AlgebraicClosure k)).prop_of_iso i'.symm
        (geometricallyReducedCommHopfAlgProperty.baseChange (AlgebraicClosure k) hreduced)
    -- The coordinate ring of a diagonalizable group *is* the group algebra, so the two properties
    -- transfer to it without an intervening isomorphism.
    let _ : ConnectedSpace
        (PrimeSpectrum (MonoidAlgebra (AlgebraicClosure k) G)) :=
      hconnected'.connectedSpace (AlgebraicClosure k)
        (_root_.CommHopfAlgCat.of (AlgebraicClosure k)
          (MonoidAlgebra (AlgebraicClosure k) G))
    let _ : IsReduced (MonoidAlgebra (AlgebraicClosure k) G) := hreduced'.isReduced
    let _ : IsMulTorsionFree G :=
      isMulTorsionFree_of_isReduced_monoidAlgebra_of_connectedSpace
        (AlgebraicClosure k) G
    obtain ⟨n, ⟨j⟩⟩ :=
      (splitTorusCommHopfAlgProperty_iff (AlgebraicClosure k) _).1
        (splitTorusCommHopfAlgProperty_coordinateRing (AlgebraicClosure k) G)
    rw [torusCommHopfAlgProperty_iff]
    exact ⟨n, ⟨j ≪≫ i⟩⟩

/-- **A reduced connected diagonalizable group over an algebraically closed field is a torus.**
Diagonalizability is expressed by the group-like elements spanning the coordinate Hopf
algebra. -/
theorem of_groupLikeSetSpan_eq_top {k : Type u} [Field k] [IsAlgClosed k]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) [IsReduced H] [ConnectedSpace (PrimeSpectrum H)]
    (hH : Subcoalgebra.groupLikeSetSpan (R := k) (C := H) Set.univ = ⊤) :
    torusCommHopfAlgProperty k H := by
  rw [← DiagonalizableGroup.groupLikeSpannedProperty_iff,
    ← DiagonalizableGroup.essImage_coordinateRingFunctor] at hH
  obtain ⟨G, ⟨i⟩⟩ := hH
  exact (iff_multiplicativeType_and_geometricallyConnected_and_geometricallyReduced k H).mpr
    ⟨(multiplicativeTypeCommHopfAlgProperty k).prop_of_iso i
      (DiagonalizableGroup.multiplicativeType_coordinateRing k G),
    (geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k H.obj).mpr inferInstance,
    (geometricallyReducedCommHopfAlgProperty_iff_isReduced_of_isAlgClosed k H.obj).mpr
      inferInstance⟩

end torusCommHopfAlgProperty

end TauCeti
