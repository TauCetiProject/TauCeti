/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Represented.Flag.PrimeField
public import TauCeti.Algebra.AlgebraicGroup.Representation.GeneratedFlag
public import TauCeti.Algebra.Coalgebra.Subcomodule.Coordinate
public import TauCeti.Algebra.Coalgebra.Subcomodule.Comap
public import TauCeti.Algebra.Coalgebra.Subcomodule.Quotient
public import TauCeti.Algebra.Coalgebra.Subcomodule.Transport
public import TauCeti.Algebra.Module.Submodule.Quotient

/-!
# The represented flag as a comodule of the prime-field F4 carrier

The adjoint cotangent comodule of `GL₂₆` corestricts to the generated prime-field carrier.
The root and torus generator calculations make its adapted `2, 1, 0` flag into actual
subcomodules of that carrier.  The middle subquotient retains the prescribed `Fin 26` basis.
-/

public section

namespace TauCeti.DynkinType

open CategoryTheory
open TauCeti.F4ShortRoot

noncomputable section

local notation "𝔽₂" => ZMod 2
local notation "H₂₆" => GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26

/-- The coordinate Hopf algebra of the generated prime-field short-root F4 carrier. -/
abbrev f4ShortRootCarrierCoordinateHopfAlgebra :=
  CommHopfAlgCat.quotient H₂₆
    (CommHopfAlgCat.commonKernelHopfIdeal F4ShortRoot.PrimeField.generator)

/-- The ambient adjoint cotangent comodule used before corestricting to the F4 carrier. -/
local instance f4ShortRootAmbientCotangentComodule :
    Comodule 𝔽₂ H₂₆ f4ShortRootCotangentDual :=
  Derivation.adjointComodule (R := 𝔽₂) (H := H₂₆)

/-- The adjoint cotangent comodule of `GL₂₆`, corestricted to the generated carrier. -/
noncomputable instance f4ShortRootCarrierCotangentComodule :
    Comodule 𝔽₂ f4ShortRootCarrierCoordinateHopfAlgebra f4ShortRootCotangentDual :=
  Comodule.Corestrict
    (CommHopfAlgCat.mkQuotient H₂₆
      (CommHopfAlgCat.commonKernelHopfIdeal F4ShortRoot.PrimeField.generator)).hom.toCoalgHom

/-- Every member of the generating family acts block triangularly on the adapted flag. -/
theorem f4ShortRootPrimeField_generator_blockTriangular :
    ∀ j : (Fin 4 ⊕ Fin 4) ⊕ Unit, ((Comodule.coefficientMatrix
      (C := H₂₆) f4ShortRootCotangentFlagBasis).map
        (F4ShortRoot.PrimeField.generator j).hom).BlockTriangular
      (OrderDual.toDual ∘ f4ShortRootCotangentFlagWeight)
  | .inl k => f4ShortRootPrimeField_root_blockTriangular k
  | .inr _ => f4ShortRootPrimeField_weightTorus_blockTriangular

/-- The coefficient matrix of the cotangent representation corestricted to the generated carrier
is block triangular for the adapted `2, 1, 0` weights. -/
theorem f4ShortRootCarrier_coefficientMatrix_blockTriangular :
    (Comodule.coefficientMatrix
      (C := f4ShortRootCarrierCoordinateHopfAlgebra)
      f4ShortRootCotangentFlagBasis).BlockTriangular
        (OrderDual.toDual ∘ f4ShortRootCotangentFlagWeight) := by
  exact Comodule.coefficientMatrix_commonKernelQuotient_blockTriangular
    F4ShortRoot.PrimeField.generator f4ShortRootCotangentFlagBasis
      f4ShortRootCotangentFlagWeight f4ShortRootPrimeField_generator_blockTriangular

/-- The ideal step of the adapted cotangent flag as a carrier subcomodule. -/
@[expose] noncomputable def f4ShortRootCarrierCotangentIdeal :
    Subcomodule 𝔽₂ f4ShortRootCarrierCoordinateHopfAlgebra f4ShortRootCotangentDual :=
  f4ShortRootCotangentFlagBasis.weightCoordinateSpanSubcomodule
    f4ShortRootCotangentFlagWeight 2 f4ShortRootCarrier_coefficientMatrix_blockTriangular

/-- The represented-range step of the adapted cotangent flag as a carrier subcomodule. -/
@[expose] noncomputable def f4ShortRootCarrierCotangentRange :
    Subcomodule 𝔽₂ f4ShortRootCarrierCoordinateHopfAlgebra f4ShortRootCotangentDual :=
  f4ShortRootCotangentFlagBasis.weightCoordinateSpanSubcomodule
    f4ShortRootCotangentFlagWeight 1 f4ShortRootCarrier_coefficientMatrix_blockTriangular

private noncomputable local instance : AddCommGroup f4ShortRootRepresentedIdeal :=
  Module.addCommMonoidToAddCommGroup 𝔽₂

@[simp] theorem f4ShortRootCarrierCotangentIdeal_toSubmodule_span :
    f4ShortRootCarrierCotangentIdeal.toSubmodule =
      Submodule.span 𝔽₂
        (f4ShortRootCotangentFlagBasis ''
          {i | (2 : ℤ) ≤ f4ShortRootCotangentFlagWeight i}) := by
  exact Module.Basis.weightCoordinateSpanSubcomodule_toSubmodule
    f4ShortRootCotangentFlagBasis f4ShortRootCotangentFlagWeight 2
      f4ShortRootCarrier_coefficientMatrix_blockTriangular

@[simp] theorem f4ShortRootCarrierCotangentRange_toSubmodule_span :
    f4ShortRootCarrierCotangentRange.toSubmodule =
      Submodule.span 𝔽₂
        (f4ShortRootCotangentFlagBasis ''
          {i | (1 : ℤ) ≤ f4ShortRootCotangentFlagWeight i}) := by
  exact Module.Basis.weightCoordinateSpanSubcomodule_toSubmodule
    f4ShortRootCotangentFlagBasis f4ShortRootCotangentFlagWeight 1
      f4ShortRootCarrier_coefficientMatrix_blockTriangular

private theorem f4ShortRootCotangentFlagIdeal_weightSet :
    {i | (2 : ℤ) ≤ f4ShortRootCotangentFlagWeight i} =
      Set.range (fun i : Fin f4ShortRootRepresentedIdealRank =>
        Fin.castAdd f4ShortRootRepresentedComplementRank (Fin.castAdd 26 i)) := by
  ext i
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · intro hi
    have him : i.val < f4ShortRootRepresentedIdealRank := by
      by_contra hnot
      by_cases hr : i.val < f4ShortRootRepresentedIdealRank + 26
      · have hw := f4ShortRootCotangentFlagWeight_of_quotient i hnot hr
        omega
      · have hw := f4ShortRootCotangentFlagWeight_of_complement i hr
        omega
    exact ⟨⟨i.val, him⟩, Fin.ext rfl⟩
  · rintro ⟨j, rfl⟩
    simp

private theorem f4ShortRootCotangentFlagRange_weightSet :
    {i | (1 : ℤ) ≤ f4ShortRootCotangentFlagWeight i} =
      Set.range (fun i : Fin (f4ShortRootRepresentedIdealRank + 26) =>
        Fin.castAdd f4ShortRootRepresentedComplementRank i) := by
  ext i
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · intro hi
    have him : i.val < f4ShortRootRepresentedIdealRank + 26 := by
      by_contra hnot
      have hw := f4ShortRootCotangentFlagWeight_of_complement i hnot
      omega
    exact ⟨⟨i.val, him⟩, Fin.ext rfl⟩
  · rintro ⟨j, rfl⟩
    by_cases hj : (j : ℕ) < f4ShortRootRepresentedIdealRank
    · rw [f4ShortRootCotangentFlagWeight_of_ideal _ hj]
      omega
    · rw [f4ShortRootCotangentFlagWeight_of_quotient _ hj j.isLt]

private theorem map_submodule_eq_span_basis
    {R V W ι : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    [AddCommMonoid W] [Module R W]
    (p : Submodule R V) (b : Module.Basis ι R p) (f : V →ₗ[R] W) :
    p.map f = Submodule.span R (Set.range fun i => f (b i : V)) := by
  have h := congrArg (Submodule.map (f.comp p.subtype)) b.span_eq
  rw [Submodule.map_span, Submodule.map_top, LinearMap.range_comp,
    Submodule.range_subtype] at h
  simpa only [← Set.range_comp, Function.comp_def, LinearMap.comp_apply,
    Submodule.subtype_apply] using h.symm

/-- The image of the represented ideal inside the ambient endomorphism space. -/
noncomputable abbrev f4ShortRootRepresentedIdealAmbient :
    Submodule 𝔽₂ (Module.End 𝔽₂ f4ShortRootLieIdeal) :=
  Submodule.span 𝔽₂ <| Set.range fun i : Fin f4ShortRootRepresentedIdealRank =>
    f4ShortRootRepresentedRange.subtype (f4ShortRootRepresentedIdealBasis i)

/-- The ideal step of the carrier cotangent flag is exactly the image of the represented ideal
under the endomorphism-to-cotangent equivalence. -/
private theorem f4ShortRootCarrierCotangentIdeal_toSubmodule :
    f4ShortRootCarrierCotangentIdeal.toSubmodule =
      f4ShortRootRepresentedIdealAmbient.map
        f4ShortRootEndEquivCotangentDual.toLinearMap := by
  let w := fun i : Fin f4ShortRootRepresentedIdealRank =>
    f4ShortRootEndEquivCotangentDual
      (f4ShortRootRepresentedRange.subtype (f4ShortRootRepresentedIdealBasis i))
  have hset : f4ShortRootCotangentFlagBasis ''
      {i | (2 : ℤ) ≤ f4ShortRootCotangentFlagWeight i} = Set.range w :=
    (congrArg (Set.image f4ShortRootCotangentFlagBasis)
      f4ShortRootCotangentFlagIdeal_weightSet).trans
      ((Set.range_comp _ _).symm.trans
        (congrArg Set.range (funext f4ShortRootCotangentFlagBasis_ideal)))
  have hmap : f4ShortRootRepresentedIdealAmbient.map
      f4ShortRootEndEquivCotangentDual.toLinearMap = Submodule.span 𝔽₂ (Set.range w) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  exact f4ShortRootCarrierCotangentIdeal_toSubmodule_span.trans
    ((congrArg (Submodule.span 𝔽₂) hset).trans hmap.symm)

/-- The range step of the carrier cotangent flag is exactly the image of the represented adjoint
range under the endomorphism-to-cotangent equivalence. -/
private theorem f4ShortRootCarrierCotangentRange_toSubmodule :
    f4ShortRootCarrierCotangentRange.toSubmodule =
      f4ShortRootRepresentedRange.map f4ShortRootEndEquivCotangentDual.toLinearMap := by
  let w := fun i : Fin (f4ShortRootRepresentedIdealRank + 26) =>
    f4ShortRootEndEquivCotangentDual (f4ShortRootRepresentedRangeBasis i)
  have hset : f4ShortRootCotangentFlagBasis ''
      {i | (1 : ℤ) ≤ f4ShortRootCotangentFlagWeight i} = Set.range w :=
    (congrArg (Set.image f4ShortRootCotangentFlagBasis)
      f4ShortRootCotangentFlagRange_weightSet).trans
      ((Set.range_comp _ _).symm.trans
        (congrArg Set.range (funext f4ShortRootCotangentFlagBasis_range)))
  exact f4ShortRootCarrierCotangentRange_toSubmodule_span.trans
    ((congrArg (Submodule.span 𝔽₂) hset).trans
      (map_submodule_eq_span_basis f4ShortRootRepresentedRange
        f4ShortRootRepresentedRangeBasis f4ShortRootEndEquivCotangentDual.toLinearMap).symm)

private theorem f4ShortRootRepresentedIdealAmbient_eq_map :
    f4ShortRootRepresentedIdealAmbient =
      f4ShortRootRepresentedIdeal.map f4ShortRootRepresentedRange.subtype := by
  exact (map_submodule_eq_span_basis f4ShortRootRepresentedIdeal
    f4ShortRootRepresentedIdealBasis f4ShortRootRepresentedRange.subtype).symm

/-- The represented-ideal step, regarded as a subcomodule of the represented-range step. -/
noncomputable def f4ShortRootCarrierIdealInRange :
    Subcomodule 𝔽₂ f4ShortRootCarrierCoordinateHopfAlgebra
      f4ShortRootCarrierCotangentRange :=
  f4ShortRootCarrierCotangentIdeal.comap f4ShortRootCarrierCotangentRange.subtype

/-- The carrier range inherits additive inverses from its module structure over `𝔽₂`. -/
noncomputable instance f4ShortRootCarrierCotangentRangeAddCommGroup :
    AddCommGroup f4ShortRootCarrierCotangentRange :=
  inferInstanceAs (AddCommGroup f4ShortRootCarrierCotangentRange.toSubmodule)

private noncomputable def f4ShortRootCarrierRangeEquivToSubmodule :
    f4ShortRootCarrierCotangentRange ≃ₗ[𝔽₂]
      f4ShortRootCarrierCotangentRange.toSubmodule where
  toFun x := ⟨x, x.property⟩
  invFun x := ⟨x, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The middle subquotient of the represented carrier flag. -/
abbrev f4ShortRootCarrierMiddle :=
  (↥f4ShortRootCarrierCotangentRange ⧸
    (f4ShortRootCarrierIdealInRange.toSubmodule :
      Submodule 𝔽₂ f4ShortRootCarrierCotangentRange))

private noncomputable def subquotientEquivOfEq
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (A B A' B' : Submodule R M) (hA : A = A') (hB : B = B') :
    (↥B ⧸ Submodule.comap B.subtype A) ≃ₗ[R]
      (↥B' ⧸ Submodule.comap B'.subtype A') := by
  subst A'
  subst B'
  exact LinearEquiv.refl R _

private theorem subquotientEquivOfEq_symm_mk
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (A B A' B' : Submodule R M) (hA : A = A') (hB : B = B') (x : B') :
    (subquotientEquivOfEq A B A' B' hA hB).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (show B from ⟨x, by rw [hB]; exact x.property⟩) := by
  subst A'
  subst B'
  rfl

private theorem quotEquivOfEq_symm_mk
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (A A' : Submodule R M) (hA : A = A') (x : M) :
    (Submodule.quotEquivOfEq A A' hA).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := by
  subst A'
  rfl

/-- The middle carrier subquotient is the modular quotient `L / I`, through its represented
realization `M / J`. -/
noncomputable def f4ShortRootCarrierMiddleEquivQuotient :
    f4ShortRootCarrierMiddle ≃ₗ[𝔽₂]
      (f4ModularChevalleyLieAlgebra ⧸ f4ShortRootSubspace) := by
  let e := f4ShortRootEndEquivCotangentDual
  let A := f4ShortRootRepresentedIdealAmbient
  let B := f4ShortRootRepresentedRange
  have hA : f4ShortRootCarrierCotangentIdeal.toSubmodule = A.map e.toLinearMap :=
    f4ShortRootCarrierCotangentIdeal_toSubmodule
  have hB : f4ShortRootCarrierCotangentRange.toSubmodule = B.map e.toLinearMap :=
    f4ShortRootCarrierCotangentRange_toSubmodule
  have htrace : Submodule.comap B.subtype A = f4ShortRootRepresentedIdeal := by
    rw [show A = f4ShortRootRepresentedIdeal.map B.subtype from
      f4ShortRootRepresentedIdealAmbient_eq_map]
    exact Submodule.comap_map_eq_of_injective B.injective_subtype _
  let eEq := subquotientEquivOfEq
    f4ShortRootCarrierCotangentIdeal.toSubmodule
    f4ShortRootCarrierCotangentRange.toSubmodule
    (A.map e.toLinearMap) (B.map e.toLinearMap) hA hB
  let eMap := TauCeti.mapSubquotientEquivOfInjective e.toLinearMap e.injective A B
  let eTrace := Submodule.quotEquivOfEq (R := 𝔽₂) (M := ↥B)
    (Submodule.comap B.subtype A) f4ShortRootRepresentedIdeal htrace
  let eCarrier := f4ShortRootCarrierRangeEquivToSubmodule
  have hcarrierTrace : f4ShortRootCarrierIdealInRange.toSubmodule.map
      eCarrier.toLinearMap =
      Submodule.comap f4ShortRootCarrierCotangentRange.toSubmodule.subtype
        f4ShortRootCarrierCotangentIdeal.toSubmodule := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      have hx' : (x : f4ShortRootCotangentDual) ∈ f4ShortRootCarrierCotangentIdeal :=
        by simpa only [TauCeti.Subcomodule.subtype_apply] using
          (TauCeti.Subcomodule.mem_comap.mp
            (TauCeti.Subcomodule.mem_toSubmodule.mp hx))
      have hxy' : (x : f4ShortRootCotangentDual) = y := congrArg Subtype.val hxy
      change (y : f4ShortRootCotangentDual) ∈ f4ShortRootCarrierCotangentIdeal
      rwa [← hxy']
    · intro hy
      let x : f4ShortRootCarrierCotangentRange := ⟨y, y.property⟩
      have hx : x ∈ f4ShortRootCarrierIdealInRange := by
        rw [f4ShortRootCarrierIdealInRange, TauCeti.Subcomodule.mem_comap,
          TauCeti.Subcomodule.subtype_apply]
        exact hy
      exact ⟨x, TauCeti.Subcomodule.mem_toSubmodule.mpr hx, rfl⟩
  let eCarrierQuot := Submodule.Quotient.equiv
    (R := 𝔽₂) (R₂ := 𝔽₂) (σ₁₂ := RingHom.id 𝔽₂)
    (M := f4ShortRootCarrierCotangentRange)
    (N := f4ShortRootCarrierCotangentRange.toSubmodule)
    f4ShortRootCarrierIdealInRange.toSubmodule
    (Submodule.comap f4ShortRootCarrierCotangentRange.toSubmodule.subtype
      f4ShortRootCarrierCotangentIdeal.toSubmodule)
    eCarrier hcarrierTrace
  exact eCarrierQuot.trans
    (eEq.trans (eMap.trans (eTrace.trans f4ShortRootQuotientEquivRepresentedRange.symm)))

/-- Transport the carrier subquotient comodule to the modular quotient `L / I`. -/
noncomputable instance f4ShortRootQuotientCarrierComodule :
    Comodule 𝔽₂ f4ShortRootCarrierCoordinateHopfAlgebra
      (f4ModularChevalleyLieAlgebra ⧸ f4ShortRootSubspace) :=
  Comodule.Transport f4ShortRootCarrierMiddleEquivQuotient

private noncomputable def f4ShortRootCarrierRepresentedAmbientMap :
    f4ModularChevalleyLieAlgebra →ₗ[𝔽₂] f4ShortRootCotangentDual :=
  f4ShortRootEndEquivCotangentDual.toLinearMap.comp
    (f4ShortRootAdjoint : f4ModularChevalleyLieAlgebra →ₗ[𝔽₂]
      Module.End 𝔽₂ f4ShortRootLieIdeal)

private noncomputable def f4ShortRootCarrierRepresentedToSubmodule :
    f4ModularChevalleyLieAlgebra →ₗ[𝔽₂]
      f4ShortRootCarrierCotangentRange.toSubmodule :=
  f4ShortRootCarrierRepresentedAmbientMap.codRestrict
    f4ShortRootCarrierCotangentRange.toSubmodule fun X => by
      rw [f4ShortRootCarrierCotangentRange_toSubmodule]
      exact ⟨f4ShortRootAdjoint X, ⟨X, rfl⟩, rfl⟩

/-- The represented adjoint image, regarded as a vector in the carrier-stable cotangent range. -/
noncomputable def f4ShortRootCarrierRepresentedMap :
    f4ModularChevalleyLieAlgebra →ₗ[𝔽₂] f4ShortRootCarrierCotangentRange :=
  f4ShortRootCarrierRangeEquivToSubmodule.symm.toLinearMap.comp
    f4ShortRootCarrierRepresentedToSubmodule

@[simp] theorem f4ShortRootCarrierRepresentedMap_apply
    (X : f4ModularChevalleyLieAlgebra) :
    (f4ShortRootCarrierRepresentedMap X : f4ShortRootCotangentDual) =
      f4ShortRootEndEquivCotangentDual (f4ShortRootAdjoint X) :=
  by exact rfl

/-- Project the carrier-stable represented range onto its transported modular quotient. -/
noncomputable def f4ShortRootCarrierQuotientProjection :
    Comodule.Hom 𝔽₂ f4ShortRootCarrierCoordinateHopfAlgebra
      f4ShortRootCarrierCotangentRange
      (f4ModularChevalleyLieAlgebra ⧸ f4ShortRootSubspace) :=
  (Comodule.transportToHom f4ShortRootCarrierMiddleEquivQuotient).comp
    f4ShortRootCarrierIdealInRange.mkQ

@[simp] theorem f4ShortRootCarrierMiddleEquivQuotient_symm_mk
    (X : f4ModularChevalleyLieAlgebra) :
    f4ShortRootCarrierMiddleEquivQuotient.symm (Submodule.Quotient.mk X) =
      Submodule.Quotient.mk (f4ShortRootCarrierRepresentedMap X) := by
  simp [f4ShortRootCarrierMiddleEquivQuotient, quotEquivOfEq_symm_mk,
    subquotientEquivOfEq_symm_mk,
    f4ShortRootCarrierRepresentedMap, f4ShortRootCarrierRepresentedToSubmodule,
    f4ShortRootCarrierRepresentedAmbientMap]
  congr 2

/-- Projecting a represented adjoint vector to the carrier middle block is its modular quotient
class. -/
@[simp] theorem f4ShortRootCarrierQuotientProjection_representedMap
    (X : f4ModularChevalleyLieAlgebra) :
    f4ShortRootCarrierQuotientProjection (f4ShortRootCarrierRepresentedMap X) =
      Submodule.Quotient.mk X := by
  rw [f4ShortRootCarrierQuotientProjection]
  change f4ShortRootCarrierMiddleEquivQuotient
    (Submodule.Quotient.mk (f4ShortRootCarrierRepresentedMap X)) = _
  rw [← f4ShortRootCarrierMiddleEquivQuotient_symm_mk X,
    LinearEquiv.apply_symm_apply]

/-- The represented adjoint map followed by the carrier quotient projection remains the ordinary
quotient map after arbitrary scalar extension. -/
theorem f4ShortRootCarrierQuotientProjection_baseChange_comp_representedMap
    {A : Type*} [CommSemiring A] [Algebra 𝔽₂ A] :
    f4ShortRootCarrierQuotientProjection.toLinearMap.baseChange A ∘ₗ
        f4ShortRootCarrierRepresentedMap.baseChange A =
      (f4ShortRootSubspace : Submodule 𝔽₂ f4ModularChevalleyLieAlgebra).mkQ.baseChange A := by
  have hbase : f4ShortRootCarrierQuotientProjection.toLinearMap ∘ₗ
      f4ShortRootCarrierRepresentedMap =
        (f4ShortRootSubspace : Submodule 𝔽₂ f4ModularChevalleyLieAlgebra).mkQ := by
    apply LinearMap.ext
    intro X
    exact f4ShortRootCarrierQuotientProjection_representedMap X
  rw [← LinearMap.baseChange_comp, hbase]

/-- The coordinate morphism of the 26-dimensional represented carrier subquotient. -/
@[expose] noncomputable def f4ShortRootQuotientCoordinateBialgHom :
    GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26 →ₐc[𝔽₂]
      f4ShortRootCarrierCoordinateHopfAlgebra :=
  Comodule.coordinateBialgHom f4ShortRootQuotientBasis

end

end TauCeti.DynkinType
