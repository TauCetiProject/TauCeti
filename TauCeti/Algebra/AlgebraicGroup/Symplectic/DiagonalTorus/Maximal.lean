/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.DiagonalTorus.ClosedImmersion
public import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation
import TauCeti.Algebra.AlgebraicGroup.Torus.SmoothConnected
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Diagonal.Centralizer

/-!
# Maximality of the diagonal torus in the symplectic group

Over any field, the paired diagonal torus of `Sp₂ₘ` is a maximal torus. Over an algebraically
closed field it is more: no reduced commutative closed subgroup scheme properly contains it. That
is stronger than maximality among tori, because a competing subgroup here need not be a torus, or
even connected.

The defining Hopf ideal and its split-torus quotient are the ones already attached to the
diagonal torus in `TauCeti.Algebra.AlgebraicGroup.Symplectic.DiagonalTorus.ClosedImmersion`.

## Main declarations

* `TauCeti.Symplectic.quotientPointsSubgroup_diagonalTorusDefiningIdeal`: the points cut out by
  the diagonal-torus ideal are the range of the diagonal-torus point morphism.
* `TauCeti.Symplectic.eq_diagonalTorusDefiningIdeal_of_le_of_isCocomm`: over an algebraically
  closed field, no larger reduced commutative closed subgroup contains the diagonal torus.
* `TauCeti.Symplectic.isMaximalTorus_diagonalTorusDefiningIdeal`: **the diagonal torus of `Sp₂ₘ`
  is a maximal torus**, over every field.

## References

* J. S. Milne, *Algebraic Groups* (2017), §17 and §23.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §16.1 and §26.3.
* The Hopf-ideal organization, the point-subgroup comparison and the base-change descent of
  maximality follow the formal template in
  `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.Maximal`.
* The matrix centralizer input is
  `TauCeti.GLSymplecticFin.centralizer_diagonalTorus`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.Symplectic

universe u

noncomputable section

section CommRing

variable (R : Type u) [CommRing R] (m : ℕ)

private theorem diagonalTorusDefiningIdeal_eq_ker :
    diagonalTorusDefiningIdeal R m =
      HopfIdeal.kerOfSurjective (diagonalTorusCoordinateMap (R := R) (m := m)).hom
        (diagonalTorusCoordinateMap_surjective (R := R) (m := m)) := by
  ext x
  rw [mem_diagonalTorusDefiningIdeal, HopfIdeal.mem_kerOfSurjective]

/-- The points cut out by `diagonalTorusDefiningIdeal` are exactly the diagonal-torus points. -/
theorem quotientPointsSubgroup_diagonalTorusDefiningIdeal (A : CommAlgCat.{u} R) :
    CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R m)
        (diagonalTorusDefiningIdeal R m) A =
      ((CommHopfAlgCat.mapPointsFunctor
        (diagonalTorusCoordinateMap (R := R) (m := m))).app A).hom.range := by
  rw [diagonalTorusDefiningIdeal_eq_ker,
    HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range]
  apply congrArg MonoidHom.range
  apply MonoidHom.ext
  intro q
  rw [AlgHom.mapDomain_apply]
  exact (CommHopfAlgCat.mapPointsFunctor_app_apply
    (diagonalTorusCoordinateMap (R := R) (m := m)) A q).symm

end CommRing

variable (k : Type u) [Field k] (m : ℕ)

private theorem mkQuotient_comp_diagonalTorusCoordinateIso_hom_commHopfAlgCat :
    CommHopfAlgCat.mkQuotient (coordinateHopfAlgebra k m) (diagonalTorusDefiningIdeal k m) ≫
        ((forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k)
          (_root_.CommHopfAlgCat.{u} k)).mapIso (diagonalTorusCoordinateIso k m)).hom =
      diagonalTorusCoordinateMap (R := k) (m := m) := by
  have h := congrArg
    (fun f ↦ (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k)
      (_root_.CommHopfAlgCat.{u} k)).map f)
    (mkQuotient_comp_diagonalTorusCoordinateIso_hom k m)
  rw [Functor.map_comp] at h
  -- A morphism in an `ObjectProperty.FullSubcategory` is definitionally its underlying
  -- morphism, so applying the forgetful functor changes only the wrapper. There is no
  -- propositional rewrite lemma for this reducible coercion.
  change CommHopfAlgCat.mkQuotient (coordinateHopfAlgebra k m)
      (diagonalTorusDefiningIdeal k m) ≫
        ((forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k)
          (_root_.CommHopfAlgCat.{u} k)).mapIso (diagonalTorusCoordinateIso k m)).hom =
      diagonalTorusCoordinateMap (R := k) (m := m) at h
  exact h

/-- The base-change isomorphism of symplectic coordinate Hopf algebras carries the base-changed
diagonal-torus ideal onto the diagonal-torus ideal over the extended base. -/
private theorem map_baseChangeHopfIdeal_diagonalTorusDefiningIdeal
    (K : Type u) [Field K] [Algebra k K] :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (diagonalTorusDefiningIdeal k m)).map
        (coordinateHopfAlgebraBaseChangeIso k K m).hom.hom =
      diagonalTorusDefiningIdeal K m := by
  let H := coordinateHopfAlgebra k m
  let D := diagonalTorusDefiningIdeal k m
  let e := coordinateHopfAlgebraBaseChangeIso k K m
  let q := (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k)
    (_root_.CommHopfAlgCat.{u} k)).mapIso (diagonalTorusCoordinateIso k m)
  let t := DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso k K
    (SplitTorus.characterGroup (ULift.{u} (Fin m)))
  let r := CommHopfAlgCat.baseChangeMap (K := K) q.hom ≫ t.hom
  have he : Function.Bijective e.hom.hom := ConcreteCategory.bijective_of_isIso e.hom
  have hq : CommHopfAlgCat.mkQuotient H D ≫ q.hom =
      diagonalTorusCoordinateMap (R := k) (m := m) :=
    mkQuotient_comp_diagonalTorusCoordinateIso_hom_commHopfAlgCat k m
  have hqK :
      CommHopfAlgCat.baseChangeMap (K := K) (CommHopfAlgCat.mkQuotient H D) ≫
          CommHopfAlgCat.baseChangeMap (K := K) q.hom =
        CommHopfAlgCat.baseChangeMap (K := K)
          (diagonalTorusCoordinateMap (R := k) (m := m)) := by
    rw [← (CommHopfAlgCat.baseChangeFunctor (K := K)).map_comp]
    exact congrArg (CommHopfAlgCat.baseChangeMap (K := K)) hq
  have hdiag := diagonalTorusCoordinateMap_baseChange (m := m) k K
  -- The local names `e` and `t` abbreviate exactly the isomorphisms appearing in that statement;
  -- exposing them is a definitional conversion, with no propositional equality to rewrite.
  change e.inv ≫
      CommHopfAlgCat.baseChangeMap (K := K)
        (diagonalTorusCoordinateMap (R := k) (m := m)) ≫ t.hom =
    diagonalTorusCoordinateMap (R := K) (m := m) at hdiag
  have hcomm :
      CommHopfAlgCat.baseChangeMap (K := K) (CommHopfAlgCat.mkQuotient H D) ≫ r =
        e.hom ≫ diagonalTorusCoordinateMap (R := K) (m := m) := by
    dsimp only [r]
    rw [← Category.assoc, hqK, ← hdiag]
    simp
  have hr : Function.Injective r.hom := by
    dsimp only [r]
    exact (ConcreteCategory.bijective_of_isIso
      ((CommHopfAlgCat.baseChangeFunctor (K := K)).mapIso q ≪≫ t).hom).1
  have hzero (y : CommHopfAlgCat.baseChange (K := K) H) :
      (CommHopfAlgCat.baseChangeMap (K := K)
          (CommHopfAlgCat.mkQuotient H D)).hom y = 0 ↔
        (diagonalTorusCoordinateMap (R := K) (m := m)).hom (e.hom.hom y) = 0 := by
    have hy := congrArg (fun f ↦ f.hom y) hcomm
    simp only [_root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply] at hy
    rw [← hy]
    exact ⟨fun hy0 ↦ by rw [hy0, map_zero], fun hy0 ↦ hr (by simpa using hy0)⟩
  ext x
  rw [HopfIdeal.mem_map_iff_of_surjective he.2, mem_diagonalTorusDefiningIdeal]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hzero y).mp ((CommHopfAlgCat.mem_baseChangeHopfIdeal_iff D y).mp hy)
  · intro hx
    refine ⟨e.inv.hom x, ?_, _root_.CommHopfAlgCat.hom_inv_apply e x⟩
    rw [CommHopfAlgCat.mem_baseChangeHopfIdeal_iff]
    apply (hzero _).mpr
    rwa [_root_.CommHopfAlgCat.hom_inv_apply]

private theorem isReduced_quotient_diagonalTorusDefiningIdeal :
    IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k m)
      (diagonalTorusDefiningIdeal k m)) := by
  rw [diagonalTorusDefiningIdeal_eq_ker]
  let f := (diagonalTorusCoordinateMap (R := k) (m := m)).hom
  let hf : Function.Surjective f := diagonalTorusCoordinateMap_surjective (R := k) (m := m)
  let e := HopfIdeal.kerLiftBialgEquiv f hf
  exact isReduced_of_injective e.toAlgEquiv.toRingEquiv.toRingHom e.injective

/-- A rational point of the split torus, read through the symplectic point equivalence, is the
paired diagonal matrix of its coordinates. -/
private theorem pointsMulEquiv_diagonalTorusPoints_symm (t : Fin m → kˣ) :
    pointsMulEquiv (R := k) (A := k) m
        (diagonalTorusPoints
          ((SplitTorus.pointsMulEquiv (R := k) (A := k)).symm
            (fun i : ULift.{u} (Fin m) ↦ t i.down))) =
      GLSymplecticFin.diagonal t := by
  rw [pointsMulEquiv_diagonalTorusPoints]
  congr 1
  funext i
  rw [GeneralLinear.diagonalTorusCoordinates_apply]
  exact congrFun
    ((SplitTorus.pointsMulEquiv (R := k) (A := k)).apply_symm_apply
      (fun j : ULift.{u} (Fin m) ↦ t j.down)) (ULift.up i)

variable [IsAlgClosed k]

/-- **The diagonal torus of `Sp₂ₘ` is maximal among reduced commutative closed subgroup schemes
over an algebraically closed field.**

If `I` cuts out a reduced commutative closed subgroup containing the diagonal torus, then `I` is
the diagonal-torus defining ideal. Containment is written contravariantly as
`I ≤ diagonalTorusDefiningIdeal k m`; commutativity is the cocommutativity of the quotient
coordinate Hopf algebra. -/
theorem eq_diagonalTorusDefiningIdeal_of_le_of_isCocomm
    (I : HopfIdeal k (coordinateHopfAlgebra k m))
    [IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k m) I)]
    [Coalgebra.IsCocomm k (CommHopfAlgCat.quotient (coordinateHopfAlgebra k m) I)]
    (hI : I ≤ diagonalTorusDefiningIdeal k m) :
    I = diagonalTorusDefiningIdeal k m := by
  let H := coordinateHopfAlgebra k m
  let D := diagonalTorusDefiningIdeal k m
  let A := CommAlgCat.of k k
  let GI := CommHopfAlgCat.quotientPointsSubgroup H I A
  let GD := CommHopfAlgCat.quotientPointsSubgroup H D A
  let e := pointsMulEquiv (R := k) (A := k) m
  let P : Subgroup (GLSymplecticFin m k) := GI.map e.toMonoidHom
  let _ : IsMulCommutative GI :=
    CommHopfAlgCat.instIsMulCommutativeQuotientPointsSubgroup
      (coordinateHopfAlgebra k m) I (CommAlgCat.of k k)
  let _ : IsMulCommutative P := Subgroup.map_isMulCommutative GI e.toMonoidHom
  have hDG : GD ≤ GI :=
    CommHopfAlgCat.quotientPointsSubgroup_le_of_le H hI A
  have hdiagonalP : GLSymplecticFin.diagonalTorus k m ≤ P := by
    intro g hg
    obtain ⟨t, rfl⟩ := GLSymplecticFin.mem_diagonalTorus_iff_exists_diagonal.mp hg
    let s : ULift.{u} (Fin m) → kˣ := fun i ↦ t i.down
    let q : WithConv
        (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin m) →₀ ℤ)) →ₐ[k] k) :=
      (SplitTorus.pointsMulEquiv (R := k) (A := k)).symm s
    let d := diagonalTorusPoints (R := k) (m := m) (A := k) q
    have hdD : d ∈ GD := by
      dsimp only [GD, D]
      rw [quotientPointsSubgroup_diagonalTorusDefiningIdeal]
      exact ⟨q, mapPointsFunctor_diagonalTorusCoordinateMap_app A q⟩
    refine ⟨d, hDG hdD, ?_⟩
    -- Unfold the `e.toMonoidHom` coercion introduced by `Subgroup.map` to the coercion of `e`.
    change e d = GLSymplecticFin.diagonal t
    simpa only [e, d, q, s] using pointsMulEquiv_diagonalTorusPoints_symm k m t
  have hP : P = GLSymplecticFin.diagonalTorus k m :=
    GLSymplecticFin.eq_diagonalTorus_of_le_of_isMulCommutative_of_infinite P hdiagonalP
  have hpoints : GI = GD := by
    refine le_antisymm (fun g hg ↦ ?_) hDG
    have hegD : e g ∈ GLSymplecticFin.diagonalTorus k m := hP ▸ ⟨g, hg, rfl⟩
    obtain ⟨t, ht⟩ := GLSymplecticFin.mem_diagonalTorus_iff_exists_diagonal.mp hegD
    let s : ULift.{u} (Fin m) → kˣ := fun i ↦ t i.down
    let q : WithConv
        (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin m) →₀ ℤ)) →ₐ[k] k) :=
      (SplitTorus.pointsMulEquiv (R := k) (A := k)).symm s
    have hdiag : e (diagonalTorusPoints (R := k) (m := m) (A := k) q) =
        GLSymplecticFin.diagonal t := by
      simpa only [e, q, s] using pointsMulEquiv_diagonalTorusPoints_symm k m t
    dsimp only [GD, D]
    rw [quotientPointsSubgroup_diagonalTorusDefiningIdeal]
    refine ⟨q, e.injective ?_⟩
    rw [mapPointsFunctor_diagonalTorusCoordinateMap_app]
    exact hdiag.trans ht
  let _ : IsReduced (CommHopfAlgCat.quotient H D) :=
    isReduced_quotient_diagonalTorusDefiningIdeal k m
  exact HopfIdeal.eq_of_quotientPointsSubgroup_eq hpoints

/-- The diagonal torus of `Sp₂ₘ` is a maximal torus over an algebraically closed field. -/
private theorem isMaximalTorus_diagonalTorusDefiningIdeal_of_isAlgClosed :
    HopfIdeal.IsMaximalTorus k (coordinateHopfAlgebra k m)
      (diagonalTorusDefiningIdeal k m) := by
  rw [HopfIdeal.isMaximalTorus_iff]
  refine ⟨torusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal k m, ?_⟩
  intro I hI hID
  let _ : IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k m) I) :=
    hI.geometricallyReduced.isReduced
  let _ : Coalgebra.IsCocomm k (CommHopfAlgCat.quotient (coordinateHopfAlgebra k m) I) :=
    hI.isCocomm k _
  have hEq := eq_diagonalTorusDefiningIdeal_of_le_of_isCocomm k m I hID
  subst I
  exact le_rfl

omit [IsAlgClosed k] in
/-- **The diagonal torus of `Sp₂ₘ` is a maximal torus over every field.** -/
@[grind =>]
theorem isMaximalTorus_diagonalTorusDefiningIdeal :
    HopfIdeal.IsMaximalTorus k (coordinateHopfAlgebra k m)
      (diagonalTorusDefiningIdeal k m) := by
  -- Maximality is checked after base change to an algebraic closure, where the stronger
  -- pointwise maximality theorem applies, and descended along the faithfully flat extension.
  rw [HopfIdeal.isMaximalTorus_iff]
  refine ⟨torusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal k m, ?_⟩
  intro I hI hID
  let K := AlgebraicClosure k
  let H := coordinateHopfAlgebra k m
  let HK := coordinateHopfAlgebra K m
  let Hft : FiniteTypeCommHopfAlgCat k :=
    ⟨H, (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
  let HKft : FiniteTypeCommHopfAlgCat K :=
    ⟨HK, (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
  let e := coordinateHopfAlgebraBaseChangeIso k K m
  let IK := (CommHopfAlgCat.baseChangeHopfIdeal (K := K) I).map e.hom.hom
  have hmapI :
      (CommHopfAlgCat.baseChangeHopfIdeal (K := K) I).map e.hom.hom = IK := rfl
  let qIso : FiniteTypeCommHopfAlgCat.baseChange (K := K)
        (FiniteTypeCommHopfAlgCat.quotient Hft I) ≅
      FiniteTypeCommHopfAlgCat.quotient HKft IK :=
    ObjectProperty.isoMk _
      (CommHopfAlgCat.quotientBaseChangeIsoOfMapEq I IK e hmapI)
  have hsplit : splitTorusCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.baseChange (K := K)
        (FiniteTypeCommHopfAlgCat.quotient Hft I)) := by
    rw [splitTorusCommHopfAlgProperty_iff]
    rw [torusCommHopfAlgProperty_iff] at hI
    simpa only [Hft] using hI
  have hIK : torusCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.quotient HKft IK) :=
    ((splitTorusCommHopfAlgProperty K).prop_of_iso qIso hsplit).torus K _
  have hIKD : IK ≤ diagonalTorusDefiningIdeal K m := by
    rw [← map_baseChangeHopfIdeal_diagonalTorusDefiningIdeal k m K]
    exact HopfIdeal.map_mono e.hom.hom (CommHopfAlgCat.baseChangeHopfIdeal_mono hID)
  have hmaxK := isMaximalTorus_diagonalTorusDefiningIdeal_of_isAlgClosed K m
  rw [HopfIdeal.isMaximalTorus_iff] at hmaxK
  have hDIK : diagonalTorusDefiningIdeal K m ≤ IK := hmaxK.2 IK hIK hIKD
  have he : Function.Bijective e.hom.hom := ConcreteCategory.bijective_of_isIso e.hom
  have hbase :
      CommHopfAlgCat.baseChangeHopfIdeal (K := K) (diagonalTorusDefiningIdeal k m) ≤
        CommHopfAlgCat.baseChangeHopfIdeal (K := K) I := by
    have hcomap := HopfIdeal.comapOfSurjective_mono e.hom.hom he.2 hDIK
    rw [← map_baseChangeHopfIdeal_diagonalTorusDefiningIdeal k m K,
      HopfIdeal.comapOfSurjective_map_of_bijective _ _ he,
      HopfIdeal.comapOfSurjective_map_of_bijective _ _ he] at hcomap
    exact hcomap
  exact (CommHopfAlgCat.baseChangeHopfIdeal_le_iff
    (algebraMap k K).injective).mp hbase

end

end TauCeti.Symplectic
