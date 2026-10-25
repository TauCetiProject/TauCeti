/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.DiagonalTorus.Basic
public import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal
import TauCeti.Algebra.AlgebraicGroup.Torus.SmoothConnected
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation
import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.InnerAut

/-!
# Maximality of the projective diagonal torus

The rank-`r` diagonal torus in `PGL_{r+1}` is a split maximal torus over every field.
In fact, no reduced commutative closed subgroup properly contains it. This gives the
maximality needed to use the normalized diagonal torus in the root datum of `PGL`.

Over an algebraically closed extension, every matrix-algebra automorphism is inner.
Commuting with the projective diagonal torus forces its conjugating matrix to be diagonal.
Dividing its entries by its last entry puts it in the normalized projective torus.
Reduced finite-type point separation then recovers the defining ideal. No restriction on
the characteristic, including characteristics dividing `r + 1`, is necessary.

The kernel-quotient presentation follows the general-linear diagonal torus in
`GeneralLinear.DiagonalTorus.Maximal`. The point calculation uses
`Matrix.GeneralLinearGroup.isDiag_of_commute_innerAut_diagGL` and Skolem–Noether
(`Matrix.GeneralLinearGroup.innerAut_surjective`).

## References

* J. S. Milne, *Algebraic Groups* (2017), §§12 and 21.1.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §16.1.
-/

public section

open CategoryTheory Matrix WithConv

namespace TauCeti.ProjectiveGeneralLinear

universe u w

noncomputable section

variable (r : ℕ) (R : Type u) [CommRing R]

/-- The Hopf ideal cutting out the normalized diagonal torus in `PGL_{r+1}`. -/
def diagonalTorusDefiningIdeal : HopfIdeal R (coordinateHopfAlgebra (r + 1) R) :=
  HopfIdeal.kerOfSurjective (diagonalTorusCoordinateMap r R).hom
    (diagonalTorusCoordinateMap_surjective r R)

/-- A coordinate function vanishes on the projective diagonal torus exactly when
restriction to the split-torus coordinates kills it. -/
@[simp]
theorem mem_diagonalTorusDefiningIdeal (x : coordinateHopfAlgebra (r + 1) R) :
    x ∈ diagonalTorusDefiningIdeal r R ↔ (diagonalTorusCoordinateMap r R).hom x = 0 := by
  rw [diagonalTorusDefiningIdeal, HopfIdeal.mem_kerOfSurjective]

/-- The quotient by the diagonal-torus ideal is the standard rank-`r` Laurent Hopf algebra. -/
def diagonalTorusCoordinateIso :
    FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.of R (coordinateHopfAlgebra (r + 1) R))
        (diagonalTorusDefiningIdeal r R) ≅
      DiagonalizableGroup.coordinateRing R
        (SplitTorus.characterGroup (ULift.{u} (Fin r))) :=
  ObjectProperty.isoMk _ <|
    CommHopfAlgCat.Hom.quotientKerOfSurjectiveIso (diagonalTorusCoordinateMap r R)
      (diagonalTorusCoordinateMap_surjective r R)

/-- The quotient presentation agrees with the original diagonal-torus restriction map. -/
@[simp]
theorem mkQuotient_comp_diagonalTorusCoordinateIso_hom :
    FiniteTypeCommHopfAlgCat.mkQuotient
        (FiniteTypeCommHopfAlgCat.of R (coordinateHopfAlgebra (r + 1) R))
        (diagonalTorusDefiningIdeal r R) ≫ (diagonalTorusCoordinateIso r R).hom =
      ObjectProperty.homMk (diagonalTorusCoordinateMap r R) :=
  ObjectProperty.hom_ext _ (CommHopfAlgCat.Hom.mkQuotient_comp_quotientKerOfSurjectiveIso_hom _ _)

/-- The projective diagonal-torus quotient is a split torus of rank `r`. -/
theorem splitTorusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal :
    splitTorusCommHopfAlgProperty R
      (FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.of R (coordinateHopfAlgebra (r + 1) R))
        (diagonalTorusDefiningIdeal r R)) := by
  rw [splitTorusCommHopfAlgProperty_iff]
  exact ⟨r, ⟨(diagonalTorusCoordinateIso r R).symm⟩⟩

/-- Points of the projective diagonal torus are precisely the image of its split-torus
parametrization, over every commutative value algebra. -/
theorem quotientPointsSubgroup_diagonalTorusDefiningIdeal (A : CommAlgCat.{w} R) :
    CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra (r + 1) R)
        (diagonalTorusDefiningIdeal r R) A =
      ((CommHopfAlgCat.Hom.mapPointsFunctor (diagonalTorusCoordinateMap r R)).app A).hom.range :=
  HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range_mapPointsFunctor _ _ A

/-- On algebra-valued points, membership in the projective diagonal torus is conjugation
by a diagonal matrix with last entry one. This includes nonreduced value algebras. -/
@[simp↓]
theorem mem_quotientPointsSubgroup_diagonalTorusDefiningIdeal_iff
    (A : CommAlgCat.{w} R)
    (q : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra (r + 1) R) A) :
    q ∈ CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra (r + 1) R)
        (diagonalTorusDefiningIdeal r R) A ↔
      ∃ s : ULift.{u} (Fin r) → Aˣ, pointsMulEquiv (r + 1) R A q =
        Matrix.GeneralLinearGroup.innerAut (diagGL (Fin.lastCases 1 (fun i ↦ s (ULift.up i)))) := by
  rw [quotientPointsSubgroup_diagonalTorusDefiningIdeal]
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨SplitTorus.pointsMulEquiv p,
      pointsMulEquiv_mapPointsFunctor_diagonalTorusCoordinateMap r R A p⟩
  · rintro ⟨s, hs⟩
    refine ⟨SplitTorus.pointsMulEquiv.symm s, (pointsMulEquiv (r + 1) R A).injective ?_⟩
    rw [pointsMulEquiv_mapPointsFunctor_diagonalTorusCoordinateMap, MulEquiv.apply_symm_apply, hs]

variable (k : Type u) [Field k]

/-- The diagonal torus of the projective general linear group is a torus over every field. -/
theorem torusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal :
    torusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.of k (coordinateHopfAlgebra (r + 1) k))
        (diagonalTorusDefiningIdeal r k)) :=
  (splitTorusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal r k).torus k _

/-- No reduced commutative closed subgroup properly contains the diagonal torus of
`PGL_{r+1}`, over any field. -/
theorem eq_diagonalTorusDefiningIdeal_of_le_of_isCocomm
    (I : HopfIdeal k (coordinateHopfAlgebra (r + 1) k))
    [IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra (r + 1) k) I)]
    [Coalgebra.IsCocomm k (CommHopfAlgCat.quotient (coordinateHopfAlgebra (r + 1) k) I)]
    (hI : I ≤ diagonalTorusDefiningIdeal r k) : I = diagonalTorusDefiningIdeal r k := by
  apply le_antisymm hI
  apply HopfIdeal.le_of_quotientPointsSubgroup_le (K := AlgebraicClosure k)
  intro q hq
  let A := CommAlgCat.of k (AlgebraicClosure k)
  let f := pointsMulEquiv (r + 1) k A q
  obtain ⟨g, hg⟩ := Matrix.GeneralLinearGroup.innerAut_surjective (AlgebraicClosure k) f
  have hcomm (d : Fin (r + 1) → (AlgebraicClosure k)ˣ) :
      Commute f (Matrix.GeneralLinearGroup.innerAut (diagGL d)) := by
    let p := (CommHopfAlgCat.Hom.mapPointsFunctor (diagonalTorusCoordinateMap r k)).app A
      (SplitTorus.pointsMulEquiv.symm (fun i : ULift.{u} (Fin r) ↦
        d i.down.castSucc / d (Fin.last r)))
    have hp : p ∈ CommHopfAlgCat.quotientPointsSubgroup
        (coordinateHopfAlgebra (r + 1) k) (diagonalTorusDefiningIdeal r k) A := by
      rw [quotientPointsSubgroup_diagonalTorusDefiningIdeal]
      exact ⟨_, rfl⟩
    have hpI := CommHopfAlgCat.quotientPointsSubgroup_le_of_le _ hI A hp
    have hc := (CommHopfAlgCat.instIsMulCommutativeQuotientPointsSubgroup
      (coordinateHopfAlgebra (r + 1) k) I A).is_comm.comm ⟨q, hq⟩ ⟨p, hpI⟩
    have hqp : Commute q p := congrArg Subtype.val hc
    have hc' : Commute f (pointsMulEquiv (r + 1) k A p) :=
      hqp.map (pointsMulEquiv (r + 1) k A)
    have hpn : pointsMulEquiv (r + 1) k A p =
        Matrix.GeneralLinearGroup.innerAut
          (diagGL (Fin.lastCases 1 (fun i ↦ d i.castSucc / d (Fin.last r)))) := by
      dsimp only [p]
      rw [pointsMulEquiv_mapPointsFunctor_diagonalTorusCoordinateMap, MulEquiv.apply_symm_apply]
    rwa [hpn, ← Matrix.GeneralLinearGroup.innerAut_diagGL_normalize] at hc'
  have hdiag : (g : Matrix (Fin (r + 1)) (Fin (r + 1)) (AlgebraicClosure k)).IsDiag :=
    g.isDiag_of_commute_innerAut_diagGL (fun d ↦ hg ▸ hcomm d)
  obtain ⟨d, hd⟩ := TauCeti.mem_diagonalTorus_iff_exists_diagGL.mp
    (TauCeti.mem_diagonalTorus_iff.mpr hdiag)
  apply (mem_quotientPointsSubgroup_diagonalTorusDefiningIdeal_iff r k A q).mpr
  refine ⟨fun i ↦ d i.down.castSucc / d (Fin.last r), ?_⟩
  exact hg.symm.trans ((congrArg Matrix.GeneralLinearGroup.innerAut hd).symm.trans
    (Matrix.GeneralLinearGroup.innerAut_diagGL_normalize r d))

/-- The normalized rank-`r` diagonal torus is a maximal torus in `PGL_{r+1}` over every field. -/
@[grind =>]
theorem isMaximalTorus_diagonalTorusDefiningIdeal :
    HopfIdeal.IsMaximalTorus k (coordinateHopfAlgebra (r + 1) k)
      (diagonalTorusDefiningIdeal r k) := by
  rw [HopfIdeal.isMaximalTorus_iff]
  refine ⟨torusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal r k, ?_⟩
  intro I hI hle
  let _ : IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra (r + 1) k) I) :=
    hI.geometricallyReduced.isReduced
  let _ : Coalgebra.IsCocomm k (CommHopfAlgCat.quotient (coordinateHopfAlgebra (r + 1) k) I) :=
    hI.isCocomm k _
  exact (eq_diagonalTorusDefiningIdeal_of_le_of_isCocomm r k I hle).ge

end

end TauCeti.ProjectiveGeneralLinear
