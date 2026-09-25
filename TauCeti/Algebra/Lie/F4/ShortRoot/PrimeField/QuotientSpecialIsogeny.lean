/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Represented.Carrier.RootPinning
public import TauCeti.Algebra.Lie.F4.ShortRoot.Represented.Carrier.TorusPinning
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.CommonKernel.Endomorphism
public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Frobenius

/-!
# The F4 carrier endomorphism from the represented quotient

The middle quotient of the represented adjoint flag defines a morphism from the prime-field
carrier to `GL₂₆`. Its pinned root and torus equations show that it maps the generating subgroup
schemes back into the carrier. The common-kernel universal property therefore factors it through
the carrier's coordinate Hopf algebra.

`quotientIsogeny_comp_self` proves the Frobenius square as an equality of coordinate morphisms.
`specialIsogenyHom` and `specialIsogenyHom_comp_self` expose the corresponding group-scheme
endomorphism and its square.
`specialIsogeny` transports this construction to the existing matrix-valued carrier points, with
its numbered root action and Frobenius square. These supply the special endomorphism selected by
the Ree F4 and Tits branches in L2 of `TauCetiRoadmap/CFSGStatement/README.md`.

The carrier is explicit; no identification with the pinned simply connected F4 group scheme,
or finiteness or simplicity theorem for its fixed-point candidates, is asserted here.
-/

public section

open CategoryTheory
open TauCeti.DynkinType

namespace TauCeti.F4ShortRoot.PrimeField

noncomputable section

local notation "𝔽₂" => ZMod 2
local notation "H₂₆" => GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26
local notation "J" => CommHopfAlgCat.commonKernelHopfIdeal generator
local notation "Q" => CommHopfAlgCat.quotient H₂₆ J

/-- The coordinate morphism of the represented middle quotient of the F4 carrier. -/
def quotientCoordinateMap : H₂₆ ⟶ Q :=
  CommHopfAlgCat.ofHom f4ShortRootQuotientCoordinateBialgHom

@[simp] theorem hom_quotientCoordinateMap :
    quotientCoordinateMap.hom = f4ShortRootQuotientCoordinateBialgHom := by
  exact CommHopfAlgCat.hom_ofHom _

private theorem commonKernelLift_comp_quotient (j : (Fin 4 ⊕ Fin 4) ⊕ Unit) :
    (CommHopfAlgCat.commonKernelLift generator j).hom.toAlgHom.comp
        (CommHopfAlgCat.mkQuotient H₂₆ J).hom.toAlgHom = (generator j).hom.toAlgHom :=
  congrArg (fun f => f.hom.toAlgHom)
    (CommHopfAlgCat.mkQuotient_comp_commonKernelLift generator j)

private theorem root_generator_point (k : Fin 4 ⊕ Fin 4) :
    ∃ u : Multiplicative (generatorCodomain (.inl k)),
      GeneralLinear.pointsMulEquiv 26
          (WithConv.toConv (generator (.inl k)).hom.toAlgHom) =
        F4ShortRoot.rootSubgroupPoints k (generatorCodomain (.inl k)) u := by
  let q : HopfAlgebra.points (H := AdditiveGroup.coordinateHopfAlgebra 𝔽₂)
      (CommAlgCat.of 𝔽₂ (generatorCodomain (.inl k))) :=
    WithConv.toConv (AlgHom.id 𝔽₂ _)
  refine ⟨AdditiveGroup.gaPointsMulEquiv q, ?_⟩
  have h := (coe_rootSubgroupPoints_gaPointsMulEquiv k _ q).symm.trans
    (coe_rootSubgroupPoints k _ _)
  change GeneralLinear.pointsMulEquiv 26
    (WithConv.toConv ((AlgHom.id 𝔽₂ _).comp (generator (.inl k)).hom.toAlgHom)) = _ at h
  simpa only [AlgHom.id_comp] using h

private theorem coe_weightTorusPoints_eq (A : Type) [CommRing A] [Algebra 𝔽₂ A]
    (s : Fin 4 → Aˣ) :
    (weightTorusPoints A s : GL (Fin 26) A) = f4ShortRootWeightTorusGL s := by
  rw [coe_weightTorusPoints, F4ShortRoot.coe_weightTorusPoints,
    UniversalEnvelopingAlgebra.kostantTorusMatrix_apply]

private theorem torus_generator_point :
    ∃ s : Fin 4 → (generatorCodomain (.inr ()))ˣ,
      GeneralLinear.pointsMulEquiv 26
          (WithConv.toConv (generator (.inr ())).hom.toAlgHom) = f4ShortRootWeightTorusGL s := by
  let q : HopfAlgebra.points (H := generatorCodomain (.inr ()))
      (CommAlgCat.of 𝔽₂ (generatorCodomain (.inr ()))) :=
    WithConv.toConv (AlgHom.id 𝔽₂ _)
  refine ⟨SplitTorus.pointsMulEquiv q, ?_⟩
  have h := (coe_weightTorusPoints_pointsMulEquiv _ q).symm.trans
    (coe_weightTorusPoints_eq _ _)
  change GeneralLinear.pointsMulEquiv 26
    (WithConv.toConv ((AlgHom.id 𝔽₂ _).comp (generator (.inr ())).hom.toAlgHom)) = _ at h
  simpa only [AlgHom.id_comp] using h

private theorem ideal_le_ker_of_point_eq
    {A : Type} [CommRing A] [Algebra 𝔽₂ A]
    (f : H₂₆ →ₐ[𝔽₂] A) (p : points A)
    (hp : GeneralLinear.pointsMulEquiv 26 (WithConv.toConv f) = (p : GL (Fin 26) A)) :
    (J).toIdeal ≤ RingHom.ker f.toRingHom := by
  have hmem := (mem_points_iff A p).mp p.property
  rw [← hp, MulEquiv.symm_apply_apply, WithConv.ofConv_toConv] at hmem
  intro x hx
  apply RingHom.mem_ker.mpr
  apply hmem x
  rw [definingIdeal_def]
  exact hx

/-- The represented quotient coordinate morphism kills the carrier ideal because its
universal root and torus points belong to the carrier. -/
theorem commonKernelHopfIdeal_le_ker_quotientCoordinateMap :
    (J).toIdeal ≤ RingHom.ker quotientCoordinateMap.hom.toAlgHom.toRingHom := by
  apply CommHopfAlgCat.commonKernelHopfIdeal_toIdeal_le_ker_of_comp_commonKernelLift generator
  intro j
  let g := (CommHopfAlgCat.commonKernelLift generator j).hom.toAlgHom
  rcases j with k | ⟨⟩
  · obtain ⟨u, hu⟩ := root_generator_point k
    have hg : GeneralLinear.pointsMulEquiv 26
        (WithConv.toConv (g.comp (CommHopfAlgCat.mkQuotient H₂₆ J).hom.toAlgHom)) =
        F4ShortRoot.rootSubgroupPoints k (generatorCodomain (.inl k)) u := by
      rw [commonKernelLift_comp_quotient]
      exact hu
    have hpin := pointsMulEquiv_f4ShortRootQuotientCoordinateBialgHom_root g k u hg
    have hp := hpin.trans (coe_rootSubgroupPoints (isogenyReverse k) _
      (Multiplicative.ofAdd (Multiplicative.toAdd u ^ isogenyExponent k))).symm
    simpa only [CommHopfAlgCat.hom_comp, hom_quotientCoordinateMap,
      BialgHom.comp_toAlgHom] using ideal_le_ker_of_point_eq _ _ hp
  · obtain ⟨s, hs⟩ := torus_generator_point
    have hg : GeneralLinear.pointsMulEquiv 26
        (WithConv.toConv (g.comp (CommHopfAlgCat.mkQuotient H₂₆ J).hom.toAlgHom)) =
        f4ShortRootWeightTorusGL s := by
      rw [commonKernelLift_comp_quotient]
      exact hs
    have hpin := pointsMulEquiv_f4ShortRootQuotientCoordinateBialgHom_torus g s hg
    have hp := hpin.trans (coe_weightTorusPoints_eq _ (f4SpecialIsogenyTorusMap s)).symm
    simpa only [CommHopfAlgCat.hom_comp, hom_quotientCoordinateMap,
      BialgHom.comp_toAlgHom] using ideal_le_ker_of_point_eq _ _ hp

/-- The endomorphism of the F4 coordinate Hopf algebra induced by its represented quotient. -/
def quotientIsogeny : Q ⟶ Q :=
  CommHopfAlgCat.liftQuotient J quotientCoordinateMap
    commonKernelHopfIdeal_le_ker_quotientCoordinateMap

/-- Pulling the quotient endomorphism back to the ambient coordinate algebra recovers the
matrix coefficient morphism of the represented quotient. -/
@[simp] theorem mkQuotient_comp_quotientIsogeny :
    CommHopfAlgCat.mkQuotient H₂₆ J ≫ quotientIsogeny = quotientCoordinateMap := by
  exact CommHopfAlgCat.mkQuotient_comp_liftQuotient J quotientCoordinateMap
    commonKernelHopfIdeal_le_ker_quotientCoordinateMap

private theorem quotientIsogeny_point_comp
    {A : Type} [CommRing A] [Algebra 𝔽₂ A] (g : Q →ₐ[𝔽₂] A) :
    (g.comp quotientIsogeny.hom.toAlgHom).comp
        (CommHopfAlgCat.mkQuotient H₂₆ J).hom.toAlgHom =
      g.comp f4ShortRootQuotientCoordinateBialgHom.toAlgHom := by
  have h := congrArg (fun f => g.comp f.hom.toAlgHom) mkQuotient_comp_quotientIsogeny
  simpa only [CommHopfAlgCat.hom_comp, BialgHom.comp_toAlgHom,
    hom_quotientCoordinateMap, AlgHom.comp_assoc] using h

/-- The induced coordinate endomorphism has the prescribed action on every root point. -/
theorem quotientIsogeny_root
    {A : Type} [CommRing A] [Algebra 𝔽₂ A] (g : Q →ₐ[𝔽₂] A)
    (k : Fin 4 ⊕ Fin 4) (u : Multiplicative A)
    (hg : GeneralLinear.pointsMulEquiv 26
        (WithConv.toConv (g.comp (CommHopfAlgCat.mkQuotient H₂₆ J).hom.toAlgHom)) =
      F4ShortRoot.rootSubgroupPoints k A u) :
    GeneralLinear.pointsMulEquiv 26
        (WithConv.toConv ((g.comp quotientIsogeny.hom.toAlgHom).comp
          (CommHopfAlgCat.mkQuotient H₂₆ J).hom.toAlgHom)) =
      F4ShortRoot.rootSubgroupPoints (isogenyReverse k) A
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ isogenyExponent k)) := by
  rw [quotientIsogeny_point_comp]
  exact pointsMulEquiv_f4ShortRootQuotientCoordinateBialgHom_root g k u hg

/-- The induced coordinate endomorphism has the prescribed action on every weight-torus point. -/
theorem quotientIsogeny_torus
    {A : Type} [CommRing A] [Algebra 𝔽₂ A] (g : Q →ₐ[𝔽₂] A)
    (s : Fin 4 → Aˣ)
    (hg : GeneralLinear.pointsMulEquiv 26
        (WithConv.toConv (g.comp (CommHopfAlgCat.mkQuotient H₂₆ J).hom.toAlgHom)) =
      f4ShortRootWeightTorusGL s) :
    GeneralLinear.pointsMulEquiv 26
        (WithConv.toConv ((g.comp quotientIsogeny.hom.toAlgHom).comp
          (CommHopfAlgCat.mkQuotient H₂₆ J).hom.toAlgHom)) =
      f4ShortRootWeightTorusGL (f4SpecialIsogenyTorusMap s) := by
  rw [quotientIsogeny_point_comp]
  exact pointsMulEquiv_f4ShortRootQuotientCoordinateBialgHom_torus g s hg

private theorem quotientIsogeny_square_root
    {A : Type} [CommRing A] [Algebra 𝔽₂ A] (g : Q →ₐ[𝔽₂] A)
    (k : Fin 4 ⊕ Fin 4) (u : Multiplicative A)
    (hg : GeneralLinear.pointsMulEquiv 26
        (WithConv.toConv (g.comp (CommHopfAlgCat.mkQuotient H₂₆ J).hom.toAlgHom)) =
      F4ShortRoot.rootSubgroupPoints k A u) :
    GeneralLinear.pointsMulEquiv 26
        (WithConv.toConv (((g.comp quotientIsogeny.hom.toAlgHom).comp
          quotientIsogeny.hom.toAlgHom).comp
            (CommHopfAlgCat.mkQuotient H₂₆ J).hom.toAlgHom)) =
      F4ShortRoot.rootSubgroupPoints k A (Multiplicative.ofAdd (Multiplicative.toAdd u ^ 2)) := by
  have h₁ := quotientIsogeny_root g k u hg
  have h₂ := quotientIsogeny_root (g.comp quotientIsogeny.hom.toAlgHom)
    (isogenyReverse k) (Multiplicative.ofAdd (Multiplicative.toAdd u ^ isogenyExponent k)) h₁
  simpa only [toAdd_ofAdd, ← pow_mul,
    isogenyExponent_mul_isogenyExponent, isogenyReverse_isogenyReverse] using h₂

private theorem quotientIsogeny_square_torus
    {A : Type} [CommRing A] [Algebra 𝔽₂ A] (g : Q →ₐ[𝔽₂] A)
    (s : Fin 4 → Aˣ)
    (hg : GeneralLinear.pointsMulEquiv 26
        (WithConv.toConv (g.comp (CommHopfAlgCat.mkQuotient H₂₆ J).hom.toAlgHom)) =
      f4ShortRootWeightTorusGL s) :
    GeneralLinear.pointsMulEquiv 26
        (WithConv.toConv (((g.comp quotientIsogeny.hom.toAlgHom).comp
          quotientIsogeny.hom.toAlgHom).comp
            (CommHopfAlgCat.mkQuotient H₂₆ J).hom.toAlgHom)) =
      f4ShortRootWeightTorusGL (fun i => s i ^ 2) := by
  have h₁ := quotientIsogeny_torus g s hg
  have h₂ := quotientIsogeny_torus (g.comp quotientIsogeny.hom.toAlgHom)
    (f4SpecialIsogenyTorusMap s) h₁
  simpa only [f4SpecialIsogenyTorusMap_apply_apply] using h₂

private theorem points_frobeniusBialgHom
    {A : Type} [CommRing A] [Algebra 𝔽₂ A] (g : Q →ₐ[𝔽₂] A) :
    GeneralLinear.pointsMulEquiv 26
        (WithConv.toConv ((g.comp (frobeniusBialgHom 𝔽₂ Q).toAlgHom).comp
          (CommHopfAlgCat.mkQuotient H₂₆ J).hom.toAlgHom)) =
      Matrix.GeneralLinearGroup.map (FiniteField.frobeniusAlgHom 𝔽₂ A).toRingHom
        (GeneralLinear.pointsMulEquiv 26
          (WithConv.toConv (g.comp (CommHopfAlgCat.mkQuotient H₂₆ J).hom.toAlgHom))) := by
  have h : (g.comp (frobeniusBialgHom 𝔽₂ Q).toAlgHom).comp
      (CommHopfAlgCat.mkQuotient H₂₆ J).hom.toAlgHom =
      (FiniteField.frobeniusAlgHom 𝔽₂ A).comp
        (g.comp (CommHopfAlgCat.mkQuotient H₂₆ J).hom.toAlgHom) := by
    ext x
    simp only [AlgHom.comp_apply, BialgHom.coe_toAlgHom,
      frobeniusBialgHom_apply, FiniteField.coe_frobeniusAlgHom, map_pow]
  rw [h]
  exact GeneralLinear.pointsMulEquiv_mapValue 26 (FiniteField.frobeniusAlgHom 𝔽₂ A) _

private theorem map_frobenius_root
    {A : Type} [CommRing A] [Algebra 𝔽₂ A]
    (k : Fin 4 ⊕ Fin 4) (u : Multiplicative A) :
    Matrix.GeneralLinearGroup.map (FiniteField.frobeniusAlgHom 𝔽₂ A).toRingHom
        (F4ShortRoot.rootSubgroupPoints k A u : GL (Fin 26) A) =
      (F4ShortRoot.rootSubgroupPoints k A
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ 2)) : GL (Fin 26) A) := by
  have h := congrArg (fun p : points A => (p : GL (Fin 26) A))
    (frobenius_rootSubgroupPoints 1 A k u)
  simpa only [coe_frobenius, pow_one, coe_rootSubgroupPoints,
    AlgHom.toRingHom_eq_coe] using h

private theorem map_frobenius_torus
    {A : Type} [CommRing A] [Algebra 𝔽₂ A] (s : Fin 4 → Aˣ) :
    Matrix.GeneralLinearGroup.map (FiniteField.frobeniusAlgHom 𝔽₂ A).toRingHom
        (f4ShortRootWeightTorusGL s) =
      f4ShortRootWeightTorusGL (fun i => s i ^ 2) := by
  have h := congrArg (fun p : points A => (p : GL (Fin 26) A))
    (frobenius_weightTorusPoints 1 A s)
  have hs : s ^ 2 = (fun i => s i ^ 2) := by ext i; rfl
  simpa only [coe_frobenius, pow_one, coe_weightTorusPoints_eq, hs,
    AlgHom.toRingHom_eq_coe] using h

/-- The represented quotient endomorphism squares to Frobenius as a morphism of coordinate
Hopf algebras. Equality is tested on the universal generators, over their coordinate algebras. -/
@[simp] theorem quotientIsogeny_comp_self :
    quotientIsogeny ≫ quotientIsogeny = CommHopfAlgCat.ofHom (frobeniusBialgHom 𝔽₂ Q) := by
  apply CommHopfAlgCat.commonKernelLift_hom_ext generator
  intro j
  apply CommHopfAlgCat.mkQuotient_hom_ext
  let g := (CommHopfAlgCat.commonKernelLift generator j).hom.toAlgHom
  have hpoints : GeneralLinear.pointsMulEquiv 26
      (WithConv.toConv (((g.comp quotientIsogeny.hom.toAlgHom).comp
        quotientIsogeny.hom.toAlgHom).comp
          (CommHopfAlgCat.mkQuotient H₂₆ J).hom.toAlgHom)) =
      GeneralLinear.pointsMulEquiv 26
        (WithConv.toConv ((g.comp (frobeniusBialgHom 𝔽₂ Q).toAlgHom).comp
          (CommHopfAlgCat.mkQuotient H₂₆ J).hom.toAlgHom)) := by
    rcases j with k | ⟨⟩
    · obtain ⟨u, hu⟩ := root_generator_point k
      have hg : GeneralLinear.pointsMulEquiv 26
          (WithConv.toConv (g.comp (CommHopfAlgCat.mkQuotient H₂₆ J).hom.toAlgHom)) =
          F4ShortRoot.rootSubgroupPoints k (generatorCodomain (.inl k)) u := by
        rw [commonKernelLift_comp_quotient]
        exact hu
      rw [quotientIsogeny_square_root g k u hg, points_frobeniusBialgHom, hg,
        map_frobenius_root]
    · obtain ⟨s, hs⟩ := torus_generator_point
      have hg : GeneralLinear.pointsMulEquiv 26
          (WithConv.toConv (g.comp (CommHopfAlgCat.mkQuotient H₂₆ J).hom.toAlgHom)) =
          f4ShortRootWeightTorusGL s := by
        rw [commonKernelLift_comp_quotient]
        exact hs
      rw [quotientIsogeny_square_torus g s hg, points_frobeniusBialgHom, hg,
        map_frobenius_torus]
  have halg := congrArg WithConv.ofConv ((GeneralLinear.pointsMulEquiv 26).injective hpoints)
  ext x
  exact DFunLike.congr_fun halg x

/-- The exceptional endomorphism of the explicit F4 carrier group scheme, represented by
`quotientIsogeny` on its coordinate Hopf algebra. -/
def specialIsogenyHom : groupScheme ⟶ groupScheme :=
  eqToHom (GeneralLinear.generatedGroupScheme_def 26 generator) ≫
    (AlgebraicGeometry.hopfSpec (CommRingCat.of 𝔽₂)).map quotientIsogeny.op ≫
      eqToHom (GeneralLinear.generatedGroupScheme_def 26 generator).symm

/-- The exceptional carrier morphism is the spectrum of the quotient isogeny. -/
theorem specialIsogenyHom_eq_map_quotientIsogeny :
    specialIsogenyHom =
      eqToHom (GeneralLinear.generatedGroupScheme_def 26 generator) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of 𝔽₂)).map quotientIsogeny.op ≫
          eqToHom (GeneralLinear.generatedGroupScheme_def 26 generator).symm := by
  rfl

/-- The exceptional endomorphism squares to Frobenius as a morphism of group schemes. -/
@[simp] theorem specialIsogenyHom_comp_self :
    specialIsogenyHom ≫ specialIsogenyHom = frobeniusHom := by
  rw [specialIsogenyHom_eq_map_quotientIsogeny, frobeniusHom_eq_map_frobeniusCoordinateMap]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  congr 1
  rw [← Category.assoc]
  congr 1
  rw [← Functor.map_comp, ← op_comp, quotientIsogeny_comp_self, frobeniusCoordinateMap_def]

/-- The characteristic-two special endomorphism of the matrix-valued F4 carrier. It is induced
by the represented quotient, with exponent one on long roots and two on short roots. -/
noncomputable def specialIsogeny (A : Type) [CommRing A] [Algebra 𝔽₂ A] :
    points A →* points A :=
  (coordinatePointsEquiv A).toMonoidHom.comp
    (((CommHopfAlgCat.mapPointsFunctor quotientIsogeny).app (CommAlgCat.of 𝔽₂ A)).hom.comp
      (coordinatePointsEquiv A).symm.toMonoidHom)

/-- The special endomorphism is precomposition by its coordinate morphism. -/
theorem specialIsogeny_coordinatePointsEquiv (A : Type) [CommRing A] [Algebra 𝔽₂ A]
    (q : HopfAlgebra.points (H := Q) (CommAlgCat.of 𝔽₂ A)) :
    specialIsogeny A (coordinatePointsEquiv A q) =
      coordinatePointsEquiv A (WithConv.toConv (q.ofConv.comp quotientIsogeny.hom.toAlgHom)) := by
  change coordinatePointsEquiv A
    ((CommHopfAlgCat.mapPointsFunctor quotientIsogeny).app (CommAlgCat.of 𝔽₂ A)
      ((coordinatePointsEquiv A).symm (coordinatePointsEquiv A q))) = _
  rw [MulEquiv.symm_apply_apply, CommHopfAlgCat.mapPointsFunctor_app_apply]

/-- The special endomorphism exchanges each signed simple root with its reversed root,
using the pinned long/short exponent convention. -/
theorem specialIsogeny_rootSubgroupPoints (A : Type) [CommRing A] [Algebra 𝔽₂ A]
    (k : Fin 4 ⊕ Fin 4) (u : Multiplicative A) :
    specialIsogeny A (rootSubgroupPoints k A u) =
      rootSubgroupPoints (isogenyReverse k) A
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ isogenyExponent k)) := by
  let q := (coordinatePointsEquiv A).symm (rootSubgroupPoints k A u)
  have hq : coordinatePointsEquiv A q = rootSubgroupPoints k A u :=
    (coordinatePointsEquiv A).apply_symm_apply _
  apply Subtype.ext
  rw [← hq, specialIsogeny_coordinatePointsEquiv, coe_coordinatePointsEquiv]
  rw [WithConv.ofConv_toConv, coe_rootSubgroupPoints]
  apply quotientIsogeny_root
  rw [← coe_coordinatePointsEquiv, hq, coe_rootSubgroupPoints]

/-- Squaring the special endomorphism gives the prime-field Frobenius on all carrier points. -/
@[simp] theorem specialIsogeny_specialIsogeny (A : Type) [CommRing A] [Algebra 𝔽₂ A]
    (g : points A) : specialIsogeny A (specialIsogeny A g) = frobenius 1 A g := by
  obtain ⟨q, rfl⟩ := (coordinatePointsEquiv A).surjective g
  apply Subtype.ext
  rw [specialIsogeny_coordinatePointsEquiv, specialIsogeny_coordinatePointsEquiv,
    coe_coordinatePointsEquiv, coe_frobenius, coe_coordinatePointsEquiv]
  have hs := congrArg (fun f => f.hom.toAlgHom) quotientIsogeny_comp_self
  simp only [CommHopfAlgCat.hom_comp, BialgHom.comp_toAlgHom,
    CommHopfAlgCat.hom_ofHom] at hs
  change GeneralLinear.pointsMulEquiv 26
    (WithConv.toConv (((q.ofConv.comp quotientIsogeny.hom.toAlgHom).comp
      quotientIsogeny.hom.toAlgHom).comp (CommHopfAlgCat.mkQuotient H₂₆ J).hom.toAlgHom)) = _
  have hcomp : (q.ofConv.comp quotientIsogeny.hom.toAlgHom).comp
      quotientIsogeny.hom.toAlgHom = q.ofConv.comp (frobeniusBialgHom 𝔽₂ Q).toAlgHom :=
    (AlgHom.comp_assoc ..).trans (congrArg (q.ofConv.comp ·) hs)
  rw [hcomp]
  simpa only [pow_one, AlgHom.toRingHom_eq_coe] using points_frobeniusBialgHom q.ofConv

end

end TauCeti.F4ShortRoot.PrimeField
