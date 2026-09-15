/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Generated.Endomorphism
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Generated.Preserves
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.GroupLikeMatrix
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.CommonKernel.Endomorphism
public import TauCeti.Algebra.CharP.Frobenius.Bialgebra
public import TauCeti.Algebra.CharP.PrimeFieldAlgebra
public import TauCeti.Algebra.Lie.F4.ShortRoot.CarrierSpecialIsogeny
public import TauCeti.Algebra.Lie.F4.ShortRoot.IsogenyMultiplicative
public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Carrier

/-!
# The special isogeny of the short-root type-F4 carrier over the prime field

`TauCeti.F4ShortRoot.specialIsogenyMatrix` is the matrix formula realizing the special isogeny `τ`
of type `F₄` in characteristic two: the `(p, q)` entry of `τ g` is the `p`th short-root quotient
coordinate of the conjugate `g Bq g⁻¹` of the `q`th representing matrix. This file makes it an
endomorphism of the short-root type-`F₄` carrier over `𝔽₂` and proves that it squares to the
carrier's Frobenius.

The formula is multiplicative on matrices preserving the invariant symmetric multiplication of
the twenty-six-dimensional module. Preserving that multiplication is a closed condition on `GL₂₆`
cut out by a Hopf ideal, so the carrier satisfies it as soon as its generators do, which they do.
Applied to the carrier's own generic matrix, multiplicativity makes the matrix of the formula
grouplike, so it is the image of the generic matrix under a morphism `ψ` of commutative Hopf
algebras out of the coordinate algebra of `GL₂₆`: a homomorphism from the carrier to `GL₂₆`.

Because the defining ideal of the carrier over `𝔽₂` is the largest Hopf ideal killed by the
generators, `ψ` maps the carrier into itself once each generator goes to a generator, and the
pinning and torus equations say exactly that. The resulting endomorphism of the carrier's points
is the matrix formula, and comparing `ψ ∘ ψ` with the squaring map of the coordinate algebra on
the generators gives the square relation on every point.

The carrier is not identified with the pinned simply connected group scheme of type `F₄`, and
constructions made here transfer to that group scheme only along such an identification.

## Main definitions

* `TauCeti.F4ShortRoot.PrimeField.coordinateMap`: the coordinate morphism of the special isogeny,
  with `TauCeti.F4ShortRoot.PrimeField.frobeniusCoordinateMap` the one of the Frobenius.
* `TauCeti.F4ShortRoot.PrimeField.specialIsogeny`: the special isogeny as an endomorphism of the
  carrier's points in characteristic two.

## Main results

* `TauCeti.F4ShortRoot.PrimeField.preservesMultiplication_of_mem_points`: **every point of the
  carrier preserves the invariant symmetric multiplication.**
* `TauCeti.F4ShortRoot.PrimeField.specialIsogenyMatrix_mul_of_mem_points` and
  `TauCeti.F4ShortRoot.PrimeField.commonKernelHopfIdeal_toIdeal_le_ker_coordinateMap`: **the
  matrix formula is multiplicative on the carrier's points and maps the carrier into itself.**
* `TauCeti.F4ShortRoot.PrimeField.coe_specialIsogeny`,
  `TauCeti.F4ShortRoot.PrimeField.specialIsogeny_rootSubgroupPoints` and
  `TauCeti.F4ShortRoot.PrimeField.specialIsogeny_weightTorusPoints`: the matrix of the special
  isogeny and **its pinning and torus equations.**
* `TauCeti.F4ShortRoot.PrimeField.specialIsogeny_specialIsogeny`: **the square relation**, that
  the special isogeny composed with itself is the carrier's Frobenius at exponent one.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* R. W. Carter, *Simple Groups of Lie Type*, §§12.3 and 13.4.
* J. Tits, *Algebraic and abstract simple groups*, Ann. of Math. **80** (1964), for the groups
  the odd powers of `τ` cut out.
-/

public section

open CategoryTheory Matrix WithConv
open scoped TensorProduct

namespace TauCeti.F4ShortRoot

open TauCeti.DynkinType
open TauCeti.UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

universe v

namespace PrimeField

variable {A : Type v} [CommRing A] [Algebra (ZMod 2) A]

/-! ### The reduced structure matrices of the invariant multiplication -/

/-- The reduced structure matrices of the invariant symmetric multiplication of the
twenty-six-dimensional module of type `F₄` over `𝔽₂`. -/
private noncomputable def multiplicationOperatorPrime :
    Fin 26 → Matrix (Fin 26) (Fin 26) (ZMod 2) :=
  fun a => (multiplicationOperator a).map (Int.cast : ℤ → ZMod 2)

private theorem map_algebraMap_multiplicationOperatorPrime {S : Type*} [CommRing S]
    [Algebra (ZMod 2) S] (a : Fin 26) :
    (multiplicationOperatorPrime a).map (algebraMap (ZMod 2) S) =
      (multiplicationOperator a).map (Int.cast : ℤ → S) := by
  rw [multiplicationOperatorPrime, Matrix.map_map]
  exact congrArg _ (funext fun z => map_intCast (algebraMap (ZMod 2) S) z)

/-- Preserving the invariant symmetric multiplication of type `F₄` is preserving the constant
multiplication over `𝔽₂` whose structure matrices are the reduced multiplication operators. -/
private theorem preserves_multiplicationOperatorPrime_iff {S : Type*} [CommRing S]
    [Algebra (ZMod 2) S] (g : Matrix (Fin 26) (Fin 26) S) :
    ConstantMultiplication.Preserves (ZMod 2) 26 multiplicationOperatorPrime g ↔
      PreservesMultiplication g := by
  rw [ConstantMultiplication.preserves_def, preservesMultiplication_def]
  simp only [ConstantMultiplication.imageStructureMatrix_def,
    map_algebraMap_multiplicationOperatorPrime, multiplicationBy_def]

/-- Preserving the invariant symmetric multiplication is stable under a morphism of value
algebras. -/
private theorem preservesMultiplication_map {S T : Type*} [CommRing S] [CommRing T]
    [Algebra (ZMod 2) S] [Algebra (ZMod 2) T] (f : S →ₐ[ZMod 2] T)
    {M : Matrix (Fin 26) (Fin 26) S} (h : PreservesMultiplication M) :
    PreservesMultiplication (M.map f) := by
  rw [← preserves_multiplicationOperatorPrime_iff] at h ⊢
  exact ConstantMultiplication.Preserves.map (ZMod 2) 26 multiplicationOperatorPrime h f

/-! ### Invertible matrices out of the coordinate algebra of `GL₂₆` -/

/-- A morphism out of the coordinate algebra of `GL₂₆` over `𝔽₂`, read as an invertible matrix. -/
private noncomputable def unitOfAlgHom {S : Type*} [CommRing S] [Algebra (ZMod 2) S]
    (ψ : TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26 →ₐ[ZMod 2] S) :
    _root_.Matrix.GeneralLinearGroup (Fin 26) S :=
  TauCeti.GeneralLinear.pointToGeneralLinear 26 (toConv ψ)

private theorem coe_unitOfAlgHom {S : Type*} [CommRing S] [Algebra (ZMod 2) S]
    (ψ : TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26 →ₐ[ZMod 2] S) :
    ((unitOfAlgHom ψ : _root_.Matrix.GeneralLinearGroup (Fin 26) S) :
        Matrix (Fin 26) (Fin 26) S) =
      (TauCeti.GeneralLinear.genericMatrix (ZMod 2) 26).map ψ :=
  (TauCeti.GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear 26 ψ).symm

private theorem coe_map_generalLinearGroup {S T : Type*} [CommRing S] [CommRing T]
    [Algebra (ZMod 2) S] [Algebra (ZMod 2) T] (f : S →ₐ[ZMod 2] T)
    (g : _root_.Matrix.GeneralLinearGroup (Fin 26) S) :
    ((_root_.Matrix.GeneralLinearGroup.map (f : S →+* T) g :
        _root_.Matrix.GeneralLinearGroup (Fin 26) T) : Matrix (Fin 26) (Fin 26) T) =
      ((g : _root_.Matrix.GeneralLinearGroup (Fin 26) S) :
        Matrix (Fin 26) (Fin 26) S).map f := by
  ext a b
  rw [Matrix.map_apply, _root_.Matrix.GeneralLinearGroup.map_apply]
  rfl

/-- The matrix formula commutes with entrywise application of a morphism of `𝔽₂`-algebras. -/
private theorem specialIsogenyMatrix_map_algHom {S T : Type*} [CommRing S] [CommRing T]
    [Algebra (ZMod 2) S] [Algebra (ZMod 2) T] (f : S →ₐ[ZMod 2] T)
    (g : _root_.Matrix.GeneralLinearGroup (Fin 26) S) :
    specialIsogenyMatrix (_root_.Matrix.GeneralLinearGroup.map (f : S →+* T) g) =
      (specialIsogenyMatrix g).map f :=
  specialIsogenyMatrix_map (f : S →+* T) g

private theorem unitOfAlgHom_comp {S T : Type*} [CommRing S] [CommRing T] [Algebra (ZMod 2) S]
    [Algebra (ZMod 2) T] (ψ : TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26 →ₐ[ZMod 2] S)
    (χ : S →ₐ[ZMod 2] T) :
    unitOfAlgHom (χ.comp ψ) =
      _root_.Matrix.GeneralLinearGroup.map (χ : S →+* T) (unitOfAlgHom ψ) := by
  apply Units.ext
  rw [coe_unitOfAlgHom, coe_map_generalLinearGroup, coe_unitOfAlgHom, Matrix.map_map]
  rfl

/-- The matrix formula transported along a morphism of value algebras. -/
private theorem specialIsogenyMatrix_unitOfAlgHom_comp {S T : Type*} [CommRing S] [CommRing T]
    [Algebra (ZMod 2) S] [Algebra (ZMod 2) T]
    (ψ : TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26 →ₐ[ZMod 2] S)
    (χ : S →ₐ[ZMod 2] T) :
    specialIsogenyMatrix (unitOfAlgHom (χ.comp ψ)) =
      (specialIsogenyMatrix (unitOfAlgHom ψ)).map χ := by
  rw [unitOfAlgHom_comp, specialIsogenyMatrix_map_algHom]

/-! ### The generic matrices of the generators -/

/-- The generic matrix of a generating coordinate morphism, as an invertible matrix. -/
private noncomputable def generatorUnit (j : (Fin 4 ⊕ Fin 4) ⊕ Unit) :
    _root_.Matrix.GeneralLinearGroup (Fin 26) (generatorCodomain j) :=
  unitOfAlgHom (generator j).hom.toAlgHom

private theorem coe_generatorUnit (j : (Fin 4 ⊕ Fin 4) ⊕ Unit) :
    ((generatorUnit j : _root_.Matrix.GeneralLinearGroup (Fin 26) (generatorCodomain j)) :
        Matrix (Fin 26) (Fin 26) (generatorCodomain j)) =
      (TauCeti.GeneralLinear.genericMatrix (ZMod 2) 26).map (generator j).hom.toAlgHom :=
  coe_unitOfAlgHom _

/-- The generic matrix of a reduced root-subgroup coordinate map is a numbered simple-root point
of the integral carrier, over the additive coordinate algebra of `𝔾ₐ` over `𝔽₂`. -/
private theorem exists_generatorUnit_inl (k : Fin 4 ⊕ Fin 4) :
    ∃ u : Multiplicative (AdditiveGroup.coordinateHopfAlgebra (ZMod 2)),
      generatorUnit (.inl k) =
        (_root_.TauCeti.F4ShortRoot.rootSubgroupPoints k
          (AdditiveGroup.coordinateHopfAlgebra (ZMod 2)) u :
          _root_.Matrix.GeneralLinearGroup (Fin 26)
            (AdditiveGroup.coordinateHopfAlgebra (ZMod 2))) := by
  set B : CommAlgCat (ZMod 2) :=
    CommAlgCat.of (ZMod 2) (AdditiveGroup.coordinateHopfAlgebra (ZMod 2)) with hB
  set q : HopfAlgebra.points (R := ZMod 2)
      (H := AdditiveGroup.coordinateHopfAlgebra (ZMod 2)) B :=
    toConv (AlgHom.id (ZMod 2) (AdditiveGroup.coordinateHopfAlgebra (ZMod 2))) with hq
  have hid : (CommHopfAlgCat.mapPointsFunctor (generator (.inl k))).app B q =
      toConv (generator (.inl k)).hom.toAlgHom := by
    rw [CommHopfAlgCat.mapPointsFunctor_app_apply]
    exact congrArg toConv (AlgHom.ext fun x => rfl)
  refine ⟨AdditiveGroup.gaPointsMulEquiv (R := ZMod 2) q, Units.ext ?_⟩
  rw [coe_generatorUnit, ← coe_rootSubgroupPoints, coe_rootSubgroupPoints_gaPointsMulEquiv, hid,
    TauCeti.GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear,
    TauCeti.GeneralLinear.pointsMulEquiv_apply]

/-- The generic matrix of the reduced weight-torus coordinate map is a weight-torus point of the
integral carrier, over the coordinate algebra of the split torus over `𝔽₂`. -/
private theorem exists_generatorUnit_inr :
    ∃ s : Fin 4 → ((DiagonalizableGroup.coordinateRing (ZMod 2)
      (SplitTorus.characterGroup (Fin 4))).obj)ˣ,
      generatorUnit (.inr ()) =
        (_root_.TauCeti.F4ShortRoot.weightTorusPoints
          ((DiagonalizableGroup.coordinateRing (ZMod 2)
            (SplitTorus.characterGroup (Fin 4))).obj) s :
          _root_.Matrix.GeneralLinearGroup (Fin 26)
            ((DiagonalizableGroup.coordinateRing (ZMod 2)
              (SplitTorus.characterGroup (Fin 4))).obj)) := by
  set B : CommAlgCat (ZMod 2) :=
    CommAlgCat.of (ZMod 2) ((DiagonalizableGroup.coordinateRing (ZMod 2)
      (SplitTorus.characterGroup (Fin 4))).obj) with hB
  set q : HopfAlgebra.points (R := ZMod 2)
      (H := (DiagonalizableGroup.coordinateRing (ZMod 2)
        (SplitTorus.characterGroup (Fin 4))).obj) B :=
    toConv (AlgHom.id (ZMod 2) ((DiagonalizableGroup.coordinateRing (ZMod 2)
      (SplitTorus.characterGroup (Fin 4))).obj)) with hq
  have hid : (CommHopfAlgCat.mapPointsFunctor (generator (.inr ()))).app B q =
      toConv (generator (.inr ())).hom.toAlgHom := by
    rw [CommHopfAlgCat.mapPointsFunctor_app_apply]
    exact congrArg toConv (AlgHom.ext fun x => rfl)
  refine ⟨SplitTorus.pointsMulEquiv q, Units.ext ?_⟩
  rw [coe_generatorUnit, ← coe_weightTorusPoints, coe_weightTorusPoints_pointsMulEquiv, hid,
    TauCeti.GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear,
    TauCeti.GeneralLinear.pointsMulEquiv_apply]

/-! ### The invariant multiplication on the carrier's points -/

/-- Every generating coordinate morphism has a generic matrix preserving the invariant
multiplication. -/
private theorem preservesMultiplication_coe_generatorUnit (j : (Fin 4 ⊕ Fin 4) ⊕ Unit) :
    PreservesMultiplication
      ((generatorUnit j : _root_.Matrix.GeneralLinearGroup (Fin 26) (generatorCodomain j)) :
        Matrix (Fin 26) (Fin 26) (generatorCodomain j)) := by
  rcases j with k | ⟨⟩
  · obtain ⟨u, hu⟩ := exists_generatorUnit_inl k
    rw [hu, _root_.TauCeti.F4ShortRoot.coe_rootSubgroupPoints_eq_rootElementMatrix]
    exact preservesMultiplication_rootElementMatrix k _
  · obtain ⟨s, hs⟩ := exists_generatorUnit_inr
    rw [hs, _root_.TauCeti.F4ShortRoot.coe_weightTorusPoints_eq_diagonal]
    exact preservesMultiplication_weightTorusMatrix s

/-- **Every point of the short-root type-`F₄` carrier over `𝔽₂` preserves the invariant symmetric
multiplication of the twenty-six-dimensional module.** -/
theorem preservesMultiplication_of_mem_points
    {g : _root_.Matrix.GeneralLinearGroup (Fin 26) A} (hg : g ∈ points A) :
    PreservesMultiplication ((g : _root_.Matrix.GeneralLinearGroup (Fin 26) A) :
      Matrix (Fin 26) (Fin 26) A) := by
  rw [← preserves_multiplicationOperatorPrime_iff]
  refine TauCeti.GeneralLinear.preserves_of_mem_generatedPointsSubgroup 26 generator
    multiplicationOperatorPrime (fun j => ?_) A (points_def A ▸ hg)
  rw [preserves_multiplicationOperatorPrime_iff, ← coe_generatorUnit]
  exact preservesMultiplication_coe_generatorUnit j

/-! ### The coordinate morphism of the special isogeny -/

/-- The coordinate Hopf algebra of the short-root type-`F₄` carrier over `𝔽₂`. -/
noncomputable abbrev carrierAlgebra : CommHopfAlgCat (ZMod 2) :=
  CommHopfAlgCat.quotient (TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26)
    (CommHopfAlgCat.commonKernelHopfIdeal generator)

/-- The quotient morphism onto the coordinate Hopf algebra of the carrier over `𝔽₂`. -/
noncomputable abbrev carrierQuotient :
    TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26 ⟶ carrierAlgebra :=
  CommHopfAlgCat.mkQuotient (TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26)
    (CommHopfAlgCat.commonKernelHopfIdeal generator)

/-- The coordinate Hopf algebra of the carrier over `𝔽₂` has characteristic two. -/
private theorem charP_carrierAlgebra : CharP carrierAlgebra 2 :=
  TauCeti.charP_of_bialgebra 2 carrierAlgebra

attribute [local instance] charP_carrierAlgebra

/-- The tensor square of the coordinate Hopf algebra of the carrier over `𝔽₂` has characteristic
two. -/
private theorem charP_tensorSquare_carrierAlgebra :
    CharP (carrierAlgebra ⊗[ZMod 2] carrierAlgebra) 2 :=
  TauCeti.charP_tensorSquare_of_bialgebra 2 carrierAlgebra

attribute [local instance] charP_tensorSquare_carrierAlgebra

/-- The generic matrix of the short-root type-`F₄` carrier over `𝔽₂`: the image of the generic
matrix of `GL₂₆` in the carrier's coordinate Hopf algebra, as an invertible matrix. It is the
matrix of the universal point of the carrier. -/
noncomputable def carrierGenericUnit :
    _root_.Matrix.GeneralLinearGroup (Fin 26) carrierAlgebra :=
  unitOfAlgHom carrierQuotient.hom.toAlgHom

/-- The matrix of the universal point is the generic matrix of the carrier. -/
theorem coe_carrierGenericUnit :
    ((carrierGenericUnit : _root_.Matrix.GeneralLinearGroup (Fin 26) carrierAlgebra) :
        Matrix (Fin 26) (Fin 26) carrierAlgebra) =
      (TauCeti.GeneralLinear.genericMatrix (ZMod 2) 26).map carrierQuotient.hom.toAlgHom :=
  coe_unitOfAlgHom _

/-- **The universal point of the carrier over `𝔽₂` is one of its points.** -/
private theorem carrierGenericUnit_mem_points :
    carrierGenericUnit ∈ points carrierAlgebra := by
  rw [points_def, TauCeti.GeneralLinear.mem_generatedPointsSubgroup_iff]
  intro x hx
  rw [carrierGenericUnit, unitOfAlgHom, ← TauCeti.GeneralLinear.pointsMulEquiv_apply,
    MulEquiv.symm_apply_apply, WithConv.ofConv_toConv]
  have hker : x ∈ RingHom.ker (CommHopfAlgCat.mkQuotient
      (TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26)
      (CommHopfAlgCat.commonKernelHopfIdeal generator)).hom.toAlgHom.toRingHom := by
    rw [CommHopfAlgCat.mkQuotient_ker]
    exact hx
  rw [RingHom.mem_ker] at hker
  exact hker

/-- The carrier's generic matrix preserves the invariant multiplication. -/
private theorem preservesMultiplication_carrierGenericUnit :
    PreservesMultiplication
      ((carrierGenericUnit : _root_.Matrix.GeneralLinearGroup (Fin 26) carrierAlgebra) :
        Matrix (Fin 26) (Fin 26) carrierAlgebra) :=
  preservesMultiplication_of_mem_points carrierGenericUnit_mem_points

/-- The matrix formula at the carrier's generic matrix satisfies the comultiplication condition:
the carrier's generic matrix is grouplike, and the formula is multiplicative on the two tensor
inclusions of a matrix preserving the invariant multiplication. -/
private theorem comul_specialIsogenyMatrix_carrierGenericUnit :
    (specialIsogenyMatrix carrierGenericUnit).map
        (Bialgebra.comulAlgHom (ZMod 2) carrierAlgebra) =
      (specialIsogenyMatrix carrierGenericUnit).map
          (Algebra.TensorProduct.includeLeft (R := ZMod 2) (S := ZMod 2)) *
        (specialIsogenyMatrix carrierGenericUnit).map
          (Algebra.TensorProduct.includeRight (R := ZMod 2)) := by
  have hXm : ((carrierGenericUnit :
          _root_.Matrix.GeneralLinearGroup (Fin 26) carrierAlgebra) :
        Matrix (Fin 26) (Fin 26) carrierAlgebra).map
          (Bialgebra.comulAlgHom (ZMod 2) carrierAlgebra) =
      ((carrierGenericUnit : _root_.Matrix.GeneralLinearGroup (Fin 26) carrierAlgebra) :
          Matrix (Fin 26) (Fin 26) carrierAlgebra).map
            (Algebra.TensorProduct.includeLeft (R := ZMod 2) (S := ZMod 2)) *
        ((carrierGenericUnit : _root_.Matrix.GeneralLinearGroup (Fin 26) carrierAlgebra) :
          Matrix (Fin 26) (Fin 26) carrierAlgebra).map
            (Algebra.TensorProduct.includeRight (R := ZMod 2)) := by
    simpa only [coe_carrierGenericUnit, BialgHom.coe_toAlgHom] using
      TauCeti.GeneralLinear.map_genericMatrix_map_comul carrierQuotient.hom
  set iL : carrierAlgebra →ₐ[ZMod 2] carrierAlgebra ⊗[ZMod 2] carrierAlgebra :=
    Algebra.TensorProduct.includeLeft with hiL
  set iR : carrierAlgebra →ₐ[ZMod 2] carrierAlgebra ⊗[ZMod 2] carrierAlgebra :=
    Algebra.TensorProduct.includeRight with hiR
  have hX : _root_.Matrix.GeneralLinearGroup.map
        ((Bialgebra.comulAlgHom (ZMod 2) carrierAlgebra :
            carrierAlgebra →ₐ[ZMod 2] carrierAlgebra ⊗[ZMod 2] carrierAlgebra) :
          carrierAlgebra →+* carrierAlgebra ⊗[ZMod 2] carrierAlgebra) carrierGenericUnit =
      _root_.Matrix.GeneralLinearGroup.map (iL : carrierAlgebra →+* _) carrierGenericUnit *
        _root_.Matrix.GeneralLinearGroup.map (iR : carrierAlgebra →+* _) carrierGenericUnit := by
    apply Units.ext
    rw [Units.val_mul, coe_map_generalLinearGroup, coe_map_generalLinearGroup,
      coe_map_generalLinearGroup]
    exact hXm
  have hL : PreservesMultiplication
      ((_root_.Matrix.GeneralLinearGroup.map (iL : carrierAlgebra →+* _) carrierGenericUnit :
          _root_.Matrix.GeneralLinearGroup (Fin 26) (carrierAlgebra ⊗[ZMod 2] carrierAlgebra)) :
        Matrix (Fin 26) (Fin 26) (carrierAlgebra ⊗[ZMod 2] carrierAlgebra)) := by
    rw [coe_map_generalLinearGroup]
    exact preservesMultiplication_map iL preservesMultiplication_carrierGenericUnit
  have hR : PreservesMultiplication
      ((_root_.Matrix.GeneralLinearGroup.map (iR : carrierAlgebra →+* _) carrierGenericUnit :
          _root_.Matrix.GeneralLinearGroup (Fin 26) (carrierAlgebra ⊗[ZMod 2] carrierAlgebra)) :
        Matrix (Fin 26) (Fin 26) (carrierAlgebra ⊗[ZMod 2] carrierAlgebra)) := by
    rw [coe_map_generalLinearGroup]
    exact preservesMultiplication_map iR preservesMultiplication_carrierGenericUnit
  rw [← specialIsogenyMatrix_map_algHom, ← specialIsogenyMatrix_map_algHom,
    ← specialIsogenyMatrix_map_algHom, hX, specialIsogenyMatrix_mul hL hR]

/-- The matrix formula at the carrier's generic matrix satisfies the counit condition. -/
private theorem counit_specialIsogenyMatrix_carrierGenericUnit :
    (specialIsogenyMatrix carrierGenericUnit).map
      (Bialgebra.counitAlgHom (ZMod 2) carrierAlgebra) = 1 := by
  have hXm : ((carrierGenericUnit :
          _root_.Matrix.GeneralLinearGroup (Fin 26) carrierAlgebra) :
        Matrix (Fin 26) (Fin 26) carrierAlgebra).map
          (Bialgebra.counitAlgHom (ZMod 2) carrierAlgebra) = 1 := by
    simpa only [coe_carrierGenericUnit, BialgHom.coe_toAlgHom] using
      TauCeti.GeneralLinear.map_genericMatrix_map_counit carrierQuotient.hom
  have hX : _root_.Matrix.GeneralLinearGroup.map
        ((Bialgebra.counitAlgHom (ZMod 2) carrierAlgebra : carrierAlgebra →ₐ[ZMod 2] ZMod 2) :
          carrierAlgebra →+* ZMod 2) carrierGenericUnit = 1 := by
    apply Units.ext
    rw [coe_map_generalLinearGroup, Units.val_one]
    exact hXm
  rw [← specialIsogenyMatrix_map_algHom, hX, specialIsogenyMatrix_one]

/-- **The coordinate morphism of the special isogeny of the carrier over `𝔽₂`**: the morphism out
of the coordinate Hopf algebra of `GL₂₆` carrying the generic matrix to the matrix formula at the
carrier's generic matrix. -/
noncomputable def coordinateMap :
    TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26 ⟶ carrierAlgebra :=
  CommHopfAlgCat.ofHom (TauCeti.GeneralLinear.coordinateBialgHomOfGroupLike (ZMod 2) 26
    (specialIsogenyMatrix carrierGenericUnit) comul_specialIsogenyMatrix_carrierGenericUnit
    counit_specialIsogenyMatrix_carrierGenericUnit)

/-- **The generic matrix of the special isogeny's coordinate morphism is the matrix formula at the
carrier's generic matrix.**

This is not a `simp` lemma: the simplifier rewrites the bialgebra-morphism coercion on the left,
so the left-hand side is not in normal form. -/
theorem map_genericMatrix_coordinateMap :
    (TauCeti.GeneralLinear.genericMatrix (ZMod 2) 26).map coordinateMap.hom.toAlgHom =
      specialIsogenyMatrix carrierGenericUnit := by
  rw [coordinateMap]
  simpa only [CommHopfAlgCat.hom_ofHom, BialgHom.coe_toAlgHom] using
    TauCeti.GeneralLinear.map_genericMatrix_coordinateBialgHomOfGroupLike (ZMod 2) 26
      (specialIsogenyMatrix carrierGenericUnit) comul_specialIsogenyMatrix_carrierGenericUnit
      counit_specialIsogenyMatrix_carrierGenericUnit

/-! ### The generator equations -/

/-- Transporting the generic matrix along a composite is transporting it twice. -/
private theorem map_genericMatrix_comp {K L : CommHopfAlgCat (ZMod 2)}
    (chi : TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26 ⟶ K) (chi' : K ⟶ L) :
    (TauCeti.GeneralLinear.genericMatrix (ZMod 2) 26).map (chi ≫ chi').hom.toAlgHom =
      ((TauCeti.GeneralLinear.genericMatrix (ZMod 2) 26).map chi.hom.toAlgHom).map
        chi'.hom.toAlgHom := by
  rw [Matrix.map_map]
  exact congrArg _ (funext fun x => CommHopfAlgCat.comp_apply chi chi' x)

/-- **The special isogeny's coordinate morphism followed by a factored generator is the matrix
formula at that generator's generic matrix.** -/
private theorem map_genericMatrix_coordinateMap_comp_commonKernelLift
    (j : (Fin 4 ⊕ Fin 4) ⊕ Unit) :
    (TauCeti.GeneralLinear.genericMatrix (ZMod 2) 26).map
        (coordinateMap ≫ CommHopfAlgCat.commonKernelLift generator j).hom.toAlgHom =
      specialIsogenyMatrix (generatorUnit j) := by
  have hgen : generatorUnit j =
      _root_.Matrix.GeneralLinearGroup.map
        ((CommHopfAlgCat.commonKernelLift generator j).hom.toAlgHom :
          carrierAlgebra →+* generatorCodomain j) carrierGenericUnit := by
    apply Units.ext
    rw [coe_generatorUnit, coe_map_generalLinearGroup, coe_carrierGenericUnit,
      ← map_genericMatrix_comp, CommHopfAlgCat.mkQuotient_comp_commonKernelLift]
  rw [map_genericMatrix_comp, map_genericMatrix_coordinateMap, hgen,
    specialIsogenyMatrix_map_algHom]

/-- A coordinate morphism out of `O(GL₂₆/𝔽₂)` whose generic matrix is the matrix of a point of the
carrier over `𝔽₂` is killed by the carrier's defining Hopf ideal. -/
private theorem toIdeal_le_ker_of_map_genericMatrix_eq {K : CommHopfAlgCat (ZMod 2)}
    (chi : TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26 ⟶ K) (g : points K)
    (h : (TauCeti.GeneralLinear.genericMatrix (ZMod 2) 26).map chi.hom.toAlgHom =
      ((g : _root_.Matrix.GeneralLinearGroup (Fin 26) K) : Matrix (Fin 26) (Fin 26) K)) :
    (CommHopfAlgCat.commonKernelHopfIdeal generator).toIdeal ≤
      RingHom.ker chi.hom.toAlgHom.toRingHom := by
  apply TauCeti.GeneralLinear.toIdeal_le_ker_of_pointToGeneralLinear_mem_hopfIdealPointsSubgroup
  have hg : TauCeti.GeneralLinear.pointToGeneralLinear 26 (toConv chi.hom.toAlgHom) =
      (g : _root_.Matrix.GeneralLinearGroup (Fin 26) K) := by
    apply Units.ext
    rw [← TauCeti.GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear, h]
  rw [hg]
  have hle : points K ≤ TauCeti.GeneralLinear.hopfIdealPointsSubgroup 26
      (CommHopfAlgCat.commonKernelHopfIdeal generator) K :=
    le_of_eq ((points_eq_hopfIdealPointsSubgroup K).trans
      (congrArg (fun I => TauCeti.GeneralLinear.hopfIdealPointsSubgroup 26 I
        (K : Type)) definingIdeal_def))
  exact hle g.2

/-- **The special isogeny's coordinate morphism is killed by the carrier's defining Hopf ideal**:
it carries every numbered simple root subgroup to a numbered simple root subgroup and the weight
torus to the weight torus, so it maps the carrier into itself. -/
theorem commonKernelHopfIdeal_toIdeal_le_ker_coordinateMap :
    (CommHopfAlgCat.commonKernelHopfIdeal generator).toIdeal ≤
      RingHom.ker coordinateMap.hom.toAlgHom.toRingHom := by
  refine CommHopfAlgCat.commonKernelHopfIdeal_toIdeal_le_ker_of_comp_commonKernelLift generator
    coordinateMap fun j => ?_
  let : CharP (generatorCodomain j) 2 := TauCeti.charP_of_bialgebra 2 (generatorCodomain j)
  rcases j with k | ⟨⟩
  · obtain ⟨u, hu⟩ := exists_generatorUnit_inl k
    refine toIdeal_le_ker_of_map_genericMatrix_eq _
      (rootSubgroupPoints (isogenyReverse k)
        (AdditiveGroup.coordinateHopfAlgebra (ZMod 2))
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ isogenyExponent k))) ?_
    rw [map_genericMatrix_coordinateMap_comp_commonKernelLift, hu, coe_rootSubgroupPoints]
    exact specialIsogenyMatrix_rootSubgroupPoints k u
  · obtain ⟨s, hs⟩ := exists_generatorUnit_inr
    refine toIdeal_le_ker_of_map_genericMatrix_eq _
      (weightTorusPoints ((DiagonalizableGroup.coordinateRing (ZMod 2)
        (SplitTorus.characterGroup (Fin 4))).obj) (isogenyTorusMap s)) ?_
    rw [map_genericMatrix_coordinateMap_comp_commonKernelLift, hs, coe_weightTorusPoints]
    exact specialIsogenyMatrix_weightTorusPoints s

/-! ### The endomorphism of the carrier's points -/

/-- The generic matrix transported along the point of an invertible matrix is that matrix. -/
private theorem map_ofConv_genericMatrix (h : _root_.Matrix.GeneralLinearGroup (Fin 26) A) :
    (TauCeti.GeneralLinear.genericMatrix (ZMod 2) 26).map
        ((TauCeti.GeneralLinear.pointsMulEquiv (R := ZMod 2) 26).symm h).ofConv =
      (h : Matrix (Fin 26) (Fin 26) A) := by
  rw [TauCeti.GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear,
    ← TauCeti.GeneralLinear.pointsMulEquiv_apply, WithConv.toConv_ofConv,
    MulEquiv.apply_symm_apply]

/-- **The endomorphism of points restricted from the special isogeny's coordinate morphism is the
matrix formula.** -/
private theorem coe_generatedPointsEndomorphism
    (g : TauCeti.GeneralLinear.generatedPointsSubgroup 26 generator A) :
    ((TauCeti.GeneralLinear.generatedPointsEndomorphism 26 coordinateMap
          commonKernelHopfIdeal_toIdeal_le_ker_coordinateMap A g :
        _root_.Matrix.GeneralLinearGroup (Fin 26) A) : Matrix (Fin 26) (Fin 26) A) =
      specialIsogenyMatrix (g : _root_.Matrix.GeneralLinearGroup (Fin 26) A) := by
  ext a b
  have hunit : unitOfAlgHom
      ((carrierQuotient.hom.toAlgHom).comp
        (AlgHom.id (ZMod 2) (TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26))) =
      carrierGenericUnit := by
    rw [AlgHom.comp_id, carrierGenericUnit]
  have hxy : (CommHopfAlgCat.mkQuotient (TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26)
        (CommHopfAlgCat.commonKernelHopfIdeal generator)).hom
        (specialIsogenyMatrix
          (unitOfAlgHom (AlgHom.id (ZMod 2)
            (TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26))) a b) =
      coordinateMap.hom (TauCeti.GeneralLinear.genericMatrix (ZMod 2) 26 a b) := by
    have hl := congrFun (congrFun (specialIsogenyMatrix_unitOfAlgHom_comp
      (AlgHom.id (ZMod 2) (TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26))
      carrierQuotient.hom.toAlgHom) a) b
    have hr := congrFun (congrFun map_genericMatrix_coordinateMap a) b
    rw [hunit] at hl
    simp only [Matrix.map_apply, BialgHom.coe_toAlgHom] at hl hr ⊢
    rw [hr, hl]
  have key := TauCeti.GeneralLinear.ofConv_pointsMulEquiv_symm_generatedPointsEndomorphism 26
    coordinateMap commonKernelHopfIdeal_toIdeal_le_ker_coordinateMap A g
    (TauCeti.GeneralLinear.genericMatrix (ZMod 2) 26 a b)
    (specialIsogenyMatrix
      (unitOfAlgHom (AlgHom.id (ZMod 2)
        (TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26))) a b) hxy
  have hL : ((TauCeti.GeneralLinear.pointsMulEquiv (R := ZMod 2) 26).symm
        (TauCeti.GeneralLinear.generatedPointsEndomorphism 26 coordinateMap
          commonKernelHopfIdeal_toIdeal_le_ker_coordinateMap A g :
          _root_.Matrix.GeneralLinearGroup (Fin 26) A)).ofConv
        (TauCeti.GeneralLinear.genericMatrix (ZMod 2) 26 a b) =
      ((TauCeti.GeneralLinear.generatedPointsEndomorphism 26 coordinateMap
          commonKernelHopfIdeal_toIdeal_le_ker_coordinateMap A g :
        _root_.Matrix.GeneralLinearGroup (Fin 26) A) : Matrix (Fin 26) (Fin 26) A) a b := by
    rw [← map_ofConv_genericMatrix, Matrix.map_apply]
  have hgu : unitOfAlgHom
      ((((TauCeti.GeneralLinear.pointsMulEquiv (R := ZMod 2) 26).symm
          (g : _root_.Matrix.GeneralLinearGroup (Fin 26) A)).ofConv).comp
        (AlgHom.id (ZMod 2) (TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26))) =
      (g : _root_.Matrix.GeneralLinearGroup (Fin 26) A) := by
    apply Units.ext
    rw [AlgHom.comp_id, coe_unitOfAlgHom, map_ofConv_genericMatrix]
  have hR : (((TauCeti.GeneralLinear.pointsMulEquiv (R := ZMod 2) 26).symm
        (g : _root_.Matrix.GeneralLinearGroup (Fin 26) A)).ofConv)
        (specialIsogenyMatrix
          (unitOfAlgHom (AlgHom.id (ZMod 2)
            (TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26))) a b) =
      specialIsogenyMatrix (g : _root_.Matrix.GeneralLinearGroup (Fin 26) A) a b := by
    have hc := congrFun (congrFun (specialIsogenyMatrix_unitOfAlgHom_comp
      (AlgHom.id (ZMod 2) (TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26))
      (((TauCeti.GeneralLinear.pointsMulEquiv (R := ZMod 2) 26).symm
        (g : _root_.Matrix.GeneralLinearGroup (Fin 26) A)).ofConv)) a) b
    rw [hgu, Matrix.map_apply] at hc
    rw [← hc]
  rw [hL, hR] at key
  exact key

/-! ### The special isogeny -/

/-- **The special isogeny is multiplicative on the points of the carrier over `𝔽₂`** in
characteristic two. -/
theorem specialIsogenyMatrix_mul_of_mem_points [CharP A 2]
    {g h : _root_.Matrix.GeneralLinearGroup (Fin 26) A} (hg : g ∈ points A)
    (hh : h ∈ points A) :
    specialIsogenyMatrix (g * h) = specialIsogenyMatrix g * specialIsogenyMatrix h :=
  specialIsogenyMatrix_mul (preservesMultiplication_of_mem_points hg)
    (preservesMultiplication_of_mem_points hh)

variable (A) in
private theorem specialIsogenyMatrix_mul_specialIsogenyMatrix_inv [CharP A 2] (g : points A) :
    specialIsogenyMatrix (g : _root_.Matrix.GeneralLinearGroup (Fin 26) A) *
        specialIsogenyMatrix ((g⁻¹ : points A) :
          _root_.Matrix.GeneralLinearGroup (Fin 26) A) = 1 := by
  rw [← specialIsogenyMatrix_mul_of_mem_points g.2 (g⁻¹ : points A).2, ← Subgroup.coe_mul,
    mul_inv_cancel, Subgroup.coe_one, specialIsogenyMatrix_one]

variable (A) in
private theorem specialIsogenyMatrix_inv_mul_specialIsogenyMatrix [CharP A 2] (g : points A) :
    specialIsogenyMatrix ((g⁻¹ : points A) : _root_.Matrix.GeneralLinearGroup (Fin 26) A) *
        specialIsogenyMatrix (g : _root_.Matrix.GeneralLinearGroup (Fin 26) A) = 1 := by
  rw [← specialIsogenyMatrix_mul_of_mem_points (g⁻¹ : points A).2 g.2, ← Subgroup.coe_mul,
    inv_mul_cancel, Subgroup.coe_one, specialIsogenyMatrix_one]

/-- The matrix formula on the points of the carrier over `𝔽₂`, valued in the ambient general
linear group. -/
private noncomputable def specialIsogenyGeneralLinear (A : Type v) [CommRing A]
    [Algebra (ZMod 2) A] [CharP A 2] :
    points A →* _root_.Matrix.GeneralLinearGroup (Fin 26) A :=
  MonoidHom.mk'
    (fun g => ⟨specialIsogenyMatrix (g : _root_.Matrix.GeneralLinearGroup (Fin 26) A),
      specialIsogenyMatrix ((g⁻¹ : points A) : _root_.Matrix.GeneralLinearGroup (Fin 26) A),
      specialIsogenyMatrix_mul_specialIsogenyMatrix_inv A g,
      specialIsogenyMatrix_inv_mul_specialIsogenyMatrix A g⟩)
    fun g h => Units.ext
      ((congrArg specialIsogenyMatrix (Subgroup.coe_mul (points A) g h)).trans
        (specialIsogenyMatrix_mul_of_mem_points g.2 h.2))

private theorem coe_specialIsogenyGeneralLinear [CharP A 2] (g : points A) :
    ((specialIsogenyGeneralLinear A g : _root_.Matrix.GeneralLinearGroup (Fin 26) A) :
        Matrix (Fin 26) (Fin 26) A) =
      specialIsogenyMatrix (g : _root_.Matrix.GeneralLinearGroup (Fin 26) A) := by
  rw [specialIsogenyGeneralLinear]
  rfl

/-- **The special isogeny carries a point of the carrier over `𝔽₂` to a point of it.** -/
private theorem specialIsogenyGeneralLinear_mem_points [CharP A 2] (g : points A) :
    specialIsogenyGeneralLinear A g ∈ points A := by
  have hle : points A ≤ TauCeti.GeneralLinear.generatedPointsSubgroup 26 generator A :=
    le_of_eq (points_def A)
  have hle' : TauCeti.GeneralLinear.generatedPointsSubgroup 26 generator A ≤ points A :=
    le_of_eq (points_def A).symm
  refine hle' ?_
  have himg := (TauCeti.GeneralLinear.generatedPointsEndomorphism 26 coordinateMap
    commonKernelHopfIdeal_toIdeal_le_ker_coordinateMap A
    ⟨(g : _root_.Matrix.GeneralLinearGroup (Fin 26) A), hle g.2⟩).2
  have heq : (TauCeti.GeneralLinear.generatedPointsEndomorphism 26 coordinateMap
      commonKernelHopfIdeal_toIdeal_le_ker_coordinateMap A
      ⟨(g : _root_.Matrix.GeneralLinearGroup (Fin 26) A), hle g.2⟩ :
      _root_.Matrix.GeneralLinearGroup (Fin 26) A) = specialIsogenyGeneralLinear A g :=
    Units.ext (by rw [coe_generatedPointsEndomorphism, coe_specialIsogenyGeneralLinear])
  rwa [heq] at himg

/-- **The special isogeny of the short-root type-`F₄` carrier over `𝔽₂` in characteristic two**:
the endomorphism of the carrier's points given by the matrix formula. -/
noncomputable def specialIsogeny (A : Type v) [CommRing A] [Algebra (ZMod 2) A] [CharP A 2] :
    points A →* points A :=
  MonoidHom.codRestrict (specialIsogenyGeneralLinear A) (points A)
    specialIsogenyGeneralLinear_mem_points

/-- The matrix of the special isogeny at a point of the carrier over `𝔽₂` is the matrix formula at
its matrix. -/
@[simp]
theorem coe_specialIsogeny [CharP A 2] (g : points A) :
    ((specialIsogeny A g : _root_.Matrix.GeneralLinearGroup (Fin 26) A) :
        Matrix (Fin 26) (Fin 26) A) =
      specialIsogenyMatrix (g : _root_.Matrix.GeneralLinearGroup (Fin 26) A) := by
  rw [specialIsogeny, MonoidHom.codRestrict_apply, coe_specialIsogenyGeneralLinear]

/-! ### The pinning and torus equations -/

/-- The matrix of a numbered simple-root point of the carrier over `𝔽₂` is the numbered simple
root element matrix of the same parameter. -/
private theorem coe_rootSubgroupPoints_rootElementMatrix (k : Fin 4 ⊕ Fin 4)
    (u : Multiplicative A) :
    (((rootSubgroupPoints k A u : points A) :
        _root_.Matrix.GeneralLinearGroup (Fin 26) A) : Matrix (Fin 26) (Fin 26) A) =
      rootElementMatrix k (Multiplicative.toAdd u) := by
  rw [coe_rootSubgroupPoints,
    _root_.TauCeti.F4ShortRoot.coe_rootSubgroupPoints_eq_rootElementMatrix]

/-- The matrix of a weight-torus point of the carrier over `𝔽₂` is the diagonal matrix of the
weight characters at that point. -/
private theorem coe_weightTorusPoints_diagonal (s : Fin 4 → Aˣ) :
    (((weightTorusPoints A s : points A) :
        _root_.Matrix.GeneralLinearGroup (Fin 26) A) : Matrix (Fin 26) (Fin 26) A) =
      Matrix.diagonal fun a => (torusCharacter s (f4ShortRootWeight a) : A) := by
  rw [coe_weightTorusPoints, _root_.TauCeti.F4ShortRoot.coe_weightTorusPoints_eq_diagonal]

/-- **The pinning equations of the special isogeny on the numbered simple root subgroups of the
carrier over `𝔽₂`**: the numbered simple-root point at `k` goes to the one at the
length-exchanged index, which reverses the Bourbaki numbering, with the parameter raised to the
exponent of `k`, one at the two long nodes and two at the two short ones. -/
@[simp]
theorem specialIsogeny_rootSubgroupPoints [CharP A 2] (k : Fin 4 ⊕ Fin 4) (t : A) :
    specialIsogeny A (rootSubgroupPoints k A (Multiplicative.ofAdd t)) =
      rootSubgroupPoints (isogenyReverse k) A
        (Multiplicative.ofAdd (t ^ isogenyExponent k)) :=
  Subtype.ext (Units.ext (by
    rw [coe_specialIsogeny, coe_rootSubgroupPoints_rootElementMatrix]
    exact specialIsogenyMatrix_of_coe_eq k t
      (coe_rootSubgroupPoints_rootElementMatrix k (Multiplicative.ofAdd t))))

/-- **The torus equation of the special isogeny on the carrier over `𝔽₂`**: a point of the split
weight torus goes to the point of the length-exchanged coordinates. -/
@[simp]
theorem specialIsogeny_weightTorusPoints [CharP A 2] (s : Fin 4 → Aˣ) :
    specialIsogeny A (weightTorusPoints A s) =
      weightTorusPoints A (isogenyTorusMap s) :=
  Subtype.ext (Units.ext (by
    rw [coe_specialIsogeny, coe_weightTorusPoints_diagonal]
    exact specialIsogenyMatrix_of_coe_eq_torus s (coe_weightTorusPoints_diagonal s)))

/-! ### The square relation against the Frobenius -/

/-- The twice-iterated matrix formula at the generic matrix of a generator is the entrywise
square. -/
private theorem specialIsogenyMatrix_specialIsogenyMatrix_generatorUnit
    (j : (Fin 4 ⊕ Fin 4) ⊕ Unit)
    (h : _root_.Matrix.GeneralLinearGroup (Fin 26) (generatorCodomain j))
    (hh : (h : Matrix (Fin 26) (Fin 26) (generatorCodomain j)) =
      specialIsogenyMatrix (generatorUnit j)) :
    specialIsogenyMatrix h =
      ((generatorUnit j : _root_.Matrix.GeneralLinearGroup (Fin 26) (generatorCodomain j)) :
        Matrix (Fin 26) (Fin 26) (generatorCodomain j)).map (· ^ 2) := by
  let : CharP (generatorCodomain j) 2 := TauCeti.charP_of_bialgebra 2 (generatorCodomain j)
  rcases j with k | ⟨⟩
  · obtain ⟨u, hu⟩ := exists_generatorUnit_inl k
    rw [hu] at hh ⊢
    rw [show h = (_root_.TauCeti.F4ShortRoot.rootSubgroupPoints (isogenyReverse k)
        (AdditiveGroup.coordinateHopfAlgebra (ZMod 2))
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ isogenyExponent k)) :
          _root_.Matrix.GeneralLinearGroup (Fin 26)
            (AdditiveGroup.coordinateHopfAlgebra (ZMod 2))) from
      Units.ext (by rw [hh, specialIsogenyMatrix_rootSubgroupPoints]),
      specialIsogenyMatrix_specialIsogenyMatrix_rootSubgroupPoints]
    ext a b
    rw [Matrix.map_apply, _root_.TauCeti.F4ShortRoot.coe_frobenius_apply]
    norm_num
  · obtain ⟨s, hs⟩ := exists_generatorUnit_inr
    rw [hs] at hh ⊢
    rw [show h = (_root_.TauCeti.F4ShortRoot.weightTorusPoints
        ((DiagonalizableGroup.coordinateRing (ZMod 2)
          (SplitTorus.characterGroup (Fin 4))).obj) (isogenyTorusMap s) :
          _root_.Matrix.GeneralLinearGroup (Fin 26)
            ((DiagonalizableGroup.coordinateRing (ZMod 2)
              (SplitTorus.characterGroup (Fin 4))).obj)) from
      Units.ext (by rw [hh, specialIsogenyMatrix_weightTorusPoints]),
      specialIsogenyMatrix_specialIsogenyMatrix_weightTorusPoints]
    ext a b
    rw [Matrix.map_apply, _root_.TauCeti.F4ShortRoot.coe_frobenius_apply]
    norm_num

/-- The matrix formula at the carrier's generic matrix, as an invertible matrix. -/
private noncomputable def carrierIsogenyUnit :
    _root_.Matrix.GeneralLinearGroup (Fin 26) carrierAlgebra :=
  specialIsogenyGeneralLinear carrierAlgebra ⟨carrierGenericUnit, carrierGenericUnit_mem_points⟩

private theorem coe_carrierIsogenyUnit :
    ((carrierIsogenyUnit : _root_.Matrix.GeneralLinearGroup (Fin 26) carrierAlgebra) :
        Matrix (Fin 26) (Fin 26) carrierAlgebra) =
      specialIsogenyMatrix carrierGenericUnit := by
  rw [carrierIsogenyUnit, coe_specialIsogenyGeneralLinear]

/-- Two coordinate morphisms out of `O(GL₂₆/𝔽₂)` with the same generic matrix are equal. -/
private theorem coordinate_hom_ext {K : CommHopfAlgCat (ZMod 2)}
    (chi chi' : TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26 ⟶ K)
    (h : (TauCeti.GeneralLinear.genericMatrix (ZMod 2) 26).map chi.hom.toAlgHom =
      (TauCeti.GeneralLinear.genericMatrix (ZMod 2) 26).map chi'.hom.toAlgHom) : chi = chi' := by
  refine CommHopfAlgCat.hom_ext ?_
  refine TauCeti.GeneralLinear.coordinateHopfAlgebra_bialgHom_ext (R := ZMod 2) (n := 26) ?_
  intro a b
  have hab := congrFun (congrFun h a) b
  rw [Matrix.map_apply, Matrix.map_apply, TauCeti.GeneralLinear.genericMatrix_apply] at hab
  simpa only [BialgHom.coe_toAlgHom] using hab

/-- **The coordinate morphism of the carrier's Frobenius**: the squaring map of the coordinate
Hopf algebra of `GL₂₆` over `𝔽₂`, followed by the quotient onto the carrier. -/
noncomputable def frobeniusCoordinateMap :
    TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26 ⟶ carrierAlgebra :=
  CommHopfAlgCat.ofHom
      (TauCeti.frobeniusBialgHom 2 (TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26)) ≫
    carrierQuotient

/-- The factorization of the special isogeny's coordinate morphism through the carrier. -/
private noncomputable def liftedCoordinateMap : carrierAlgebra ⟶ carrierAlgebra :=
  CommHopfAlgCat.liftQuotient (CommHopfAlgCat.commonKernelHopfIdeal generator) coordinateMap
    commonKernelHopfIdeal_toIdeal_le_ker_coordinateMap

private theorem map_liftedCoordinateMap_carrierGenericUnit :
    _root_.Matrix.GeneralLinearGroup.map
        (liftedCoordinateMap.hom.toAlgHom : carrierAlgebra →+* carrierAlgebra)
        carrierGenericUnit = carrierIsogenyUnit := by
  apply Units.ext
  rw [coe_map_generalLinearGroup, coe_carrierGenericUnit, ← map_genericMatrix_comp,
    liftedCoordinateMap, CommHopfAlgCat.mkQuotient_comp_liftQuotient,
    map_genericMatrix_coordinateMap, coe_carrierIsogenyUnit]

private theorem map_genericMatrix_comp_liftedCoordinateMap :
    (TauCeti.GeneralLinear.genericMatrix (ZMod 2) 26).map
        (coordinateMap ≫ liftedCoordinateMap).hom.toAlgHom =
      specialIsogenyMatrix carrierIsogenyUnit := by
  rw [map_genericMatrix_comp, map_genericMatrix_coordinateMap,
    ← map_liftedCoordinateMap_carrierGenericUnit, specialIsogenyMatrix_map_algHom]

private theorem map_genericMatrix_frobeniusCoordinateMap :
    (TauCeti.GeneralLinear.genericMatrix (ZMod 2) 26).map frobeniusCoordinateMap.hom.toAlgHom =
      ((carrierGenericUnit : _root_.Matrix.GeneralLinearGroup (Fin 26) carrierAlgebra) :
        Matrix (Fin 26) (Fin 26) carrierAlgebra).map (fun x => x ^ 2) := by
  rw [frobeniusCoordinateMap, map_genericMatrix_comp, coe_carrierGenericUnit, Matrix.map_map,
    Matrix.map_map]
  refine congrArg _ (funext fun x => ?_)
  simp only [Function.comp_apply, CommHopfAlgCat.hom_ofHom, BialgHom.coe_toAlgHom,
    TauCeti.frobeniusBialgHom_apply, map_pow]

/-- **The special isogeny composed with itself is the Frobenius, on coordinate morphisms.** The
two morphisms agree on every generator of the carrier, and the carrier is generated by them. -/
private theorem coordinateMap_comp_liftedCoordinateMap :
    coordinateMap ≫ liftedCoordinateMap = frobeniusCoordinateMap := by
  refine CommHopfAlgCat.commonKernelLift_hom_ext generator _ _ fun j => ?_
  refine coordinate_hom_ext _ _ ?_
  have hXj : _root_.Matrix.GeneralLinearGroup.map
        ((CommHopfAlgCat.commonKernelLift generator j).hom.toAlgHom :
          carrierAlgebra →+* generatorCodomain j) carrierGenericUnit = generatorUnit j := by
    apply Units.ext
    rw [coe_generatorUnit, coe_map_generalLinearGroup, coe_carrierGenericUnit,
      ← map_genericMatrix_comp, CommHopfAlgCat.mkQuotient_comp_commonKernelLift]
  have hUj : ((_root_.Matrix.GeneralLinearGroup.map
        ((CommHopfAlgCat.commonKernelLift generator j).hom.toAlgHom :
          carrierAlgebra →+* generatorCodomain j) carrierIsogenyUnit :
        _root_.Matrix.GeneralLinearGroup (Fin 26) (generatorCodomain j)) :
        Matrix (Fin 26) (Fin 26) (generatorCodomain j)) =
      specialIsogenyMatrix (generatorUnit j) := by
    rw [coe_map_generalLinearGroup, coe_carrierIsogenyUnit, ← specialIsogenyMatrix_map_algHom,
      hXj]
  rw [map_genericMatrix_comp (coordinateMap ≫ liftedCoordinateMap)
      (CommHopfAlgCat.commonKernelLift generator j),
    map_genericMatrix_comp_liftedCoordinateMap,
    map_genericMatrix_comp frobeniusCoordinateMap
      (CommHopfAlgCat.commonKernelLift generator j),
    map_genericMatrix_frobeniusCoordinateMap, ← specialIsogenyMatrix_map_algHom,
    specialIsogenyMatrix_specialIsogenyMatrix_generatorUnit j _ hUj, Matrix.map_map]
  have hpow : ∀ x : carrierAlgebra,
      (CommHopfAlgCat.commonKernelLift generator j).hom.toAlgHom (x ^ 2) =
        ((CommHopfAlgCat.commonKernelLift generator j).hom.toAlgHom x) ^ 2 :=
    fun x => map_pow _ x 2
  rw [show ((CommHopfAlgCat.commonKernelLift generator j).hom.toAlgHom : carrierAlgebra → _) ∘
      (fun x : carrierAlgebra => x ^ 2) =
      (fun y => y ^ 2) ∘ ((CommHopfAlgCat.commonKernelLift generator j).hom.toAlgHom :
        carrierAlgebra → _) from funext hpow, ← Matrix.map_map, ← coe_map_generalLinearGroup,
    hXj]

/-- **The twice-iterated matrix formula at the carrier's generic matrix is the entrywise
square.** -/
private theorem specialIsogenyMatrix_carrierIsogenyUnit :
    specialIsogenyMatrix carrierIsogenyUnit =
      ((carrierGenericUnit : _root_.Matrix.GeneralLinearGroup (Fin 26) carrierAlgebra) :
        Matrix (Fin 26) (Fin 26) carrierAlgebra).map (fun x => x ^ 2) := by
  rw [← map_genericMatrix_comp_liftedCoordinateMap, coordinateMap_comp_liftedCoordinateMap,
    map_genericMatrix_frobeniusCoordinateMap]

/-- **The twice-iterated matrix formula at a point of the carrier over `𝔽₂` is the entrywise
square.** -/
private theorem specialIsogenyMatrix_specialIsogenyMatrix_of_mem_points
    {g h : _root_.Matrix.GeneralLinearGroup (Fin 26) A} (hg : g ∈ points A)
    (hh : (h : Matrix (Fin 26) (Fin 26) A) = specialIsogenyMatrix g) :
    specialIsogenyMatrix h =
      ((g : _root_.Matrix.GeneralLinearGroup (Fin 26) A) :
        Matrix (Fin 26) (Fin 26) A).map (fun x => x ^ 2) := by
  have hker : ∀ x : TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26,
      x ∈ CommHopfAlgCat.commonKernelHopfIdeal generator →
        ((TauCeti.GeneralLinear.pointsMulEquiv (R := ZMod 2) 26).symm g).ofConv x = 0 := by
    have hmem := le_of_eq (points_def A) hg
    rw [TauCeti.GeneralLinear.mem_generatedPointsSubgroup_iff] at hmem
    exact hmem
  set q := CommHopfAlgCat.liftQuotientPoint
    (TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26)
    (CommHopfAlgCat.commonKernelHopfIdeal generator) (CommAlgCat.of (ZMod 2) A)
    ((TauCeti.GeneralLinear.pointsMulEquiv (R := ZMod 2) 26).symm g) hker with hq
  have hcomp : (q.ofConv : carrierAlgebra → A) ∘
        (carrierQuotient.hom.toAlgHom :
          TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26 → carrierAlgebra) =
      (((TauCeti.GeneralLinear.pointsMulEquiv (R := ZMod 2) 26).symm g).ofConv :
        TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26 → A) := by
    funext x
    rw [Function.comp_apply, hq, carrierQuotient, BialgHom.coe_toAlgHom,
      CommHopfAlgCat.mkQuotient_apply]
    exact CommHopfAlgCat.liftQuotientPoint_mk
      (TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26)
      (CommHopfAlgCat.commonKernelHopfIdeal generator) (CommAlgCat.of (ZMod 2) A)
      ((TauCeti.GeneralLinear.pointsMulEquiv (R := ZMod 2) 26).symm g) hker x
  have hphi : _root_.Matrix.GeneralLinearGroup.map (q.ofConv : carrierAlgebra →+* A)
      carrierGenericUnit = g := by
    apply Units.ext
    rw [coe_map_generalLinearGroup, coe_carrierGenericUnit, Matrix.map_map, hcomp,
      map_ofConv_genericMatrix]
  have hh' : h = _root_.Matrix.GeneralLinearGroup.map (q.ofConv : carrierAlgebra →+* A)
      carrierIsogenyUnit := by
    apply Units.ext
    rw [hh, coe_map_generalLinearGroup, coe_carrierIsogenyUnit,
      ← specialIsogenyMatrix_map_algHom, hphi]
  rw [hh', specialIsogenyMatrix_map_algHom, specialIsogenyMatrix_carrierIsogenyUnit, ← hphi,
    coe_map_generalLinearGroup, Matrix.map_map, Matrix.map_map]
  exact congrArg _ (funext fun x => map_pow (q.ofConv : carrierAlgebra →+* A) x 2)

/-- **The special isogeny of the carrier over `𝔽₂` squares to the carrier's Frobenius.** -/
theorem specialIsogeny_specialIsogeny [CharP A 2] (g : points A) :
    specialIsogeny A (specialIsogeny A g) = frobenius 1 A g := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_specialIsogeny,
    specialIsogenyMatrix_specialIsogenyMatrix_of_mem_points g.2 (coe_specialIsogeny g)]
  ext a b
  rw [Matrix.map_apply, coe_frobenius_apply]
  norm_num

end PrimeField

end TauCeti.F4ShortRoot
