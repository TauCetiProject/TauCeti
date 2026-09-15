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
public import TauCeti.Algebra.Lie.G2.ShortRoot.CarrierSpecialIsogeny
public import TauCeti.Algebra.Lie.G2.ShortRoot.PinnedCrossProduct
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Carrier

/-!
# The special isogeny of the short-root type-G2 carrier over the prime field

`Matrix.g2SpecialIsogeny` is the matrix of signed `2 × 2` minors realizing the special isogeny `τ`
of type `G₂` in characteristic three. This file makes it an endomorphism of the short-root
type-`G₂` carrier over `𝔽₃` and proves that it squares to the carrier's Frobenius.

The minor formula is multiplicative on matrices preserving the invariant cross product, the left
factor also fixing the invariant dual form by congruence. Both conditions are closed conditions on
`GL₇` cut out by a Hopf ideal, so the carrier satisfies them as soon as its generators do, which
they do. Applied to the carrier's own generic matrix, multiplicativity makes the matrix of minors
grouplike, so it is the image of the generic matrix under a morphism `ψ` of commutative Hopf
algebras out of the coordinate algebra of `GL₇`: a homomorphism from the carrier to `GL₇`.

Because the defining ideal of the carrier over `𝔽₃` is the largest Hopf ideal killed by the
generators, `ψ` maps the carrier into itself once each generator goes to a generator, and the
pinning equations say exactly that. The resulting endomorphism of the carrier's points is the
minor formula, and comparing `ψ ∘ ψ` with the cube map of the coordinate algebra on the generators
gives the square relation on every point.

The carrier is not identified with the pinned simply connected group scheme of type `G₂`, and
constructions made here transfer to that group scheme only along such an identification.

## Main definitions

* `TauCeti.G2ShortRoot.PrimeField.coordinateMap`: the coordinate morphism of the special isogeny,
  with `TauCeti.G2ShortRoot.PrimeField.frobeniusCoordinateMap` the one of the Frobenius.
* `TauCeti.G2ShortRoot.PrimeField.specialIsogeny`: the special isogeny as an endomorphism of the
  carrier's points in characteristic three.

## Main results

* `TauCeti.G2ShortRoot.PrimeField.preservesG2Cross_of_mem_points` and
  `TauCeti.G2ShortRoot.PrimeField.preservesDualForm_of_mem_points`: **every point of the carrier
  preserves the cross product and fixes the invariant dual form by congruence.**
* `TauCeti.G2ShortRoot.PrimeField.g2SpecialIsogeny_mul_of_mem_points` and
  `TauCeti.G2ShortRoot.PrimeField.commonKernelHopfIdeal_toIdeal_le_ker_coordinateMap`: **the minor
  formula is multiplicative on the carrier's points and maps the carrier into itself.**
* `TauCeti.G2ShortRoot.PrimeField.coe_specialIsogeny`,
  `TauCeti.G2ShortRoot.PrimeField.specialIsogeny_rootSubgroupPoints` and
  `TauCeti.G2ShortRoot.PrimeField.specialIsogeny_weightTorusPoints`: the matrix of the special
  isogeny and **its pinning and torus equations.**
* `TauCeti.G2ShortRoot.PrimeField.specialIsogeny_specialIsogeny` and
  `TauCeti.G2ShortRoot.PrimeField.specialIsogeny_comp_specialIsogeny`: **the square relation**,
  pointwise and as an equality of endomorphisms, that
  the special isogeny composed with itself is the carrier's Frobenius at exponent one.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* R. W. Carter, *Simple Groups of Lie Type*, §§12.3 and 13.4.
* S. Garibaldi and R. M. Guralnick, *Simple groups stabilizing polynomials*, Forum of Mathematics
  Pi **3** (2015), §6, for the cross product and the quotient by the short-root ideal.
-/

-- Adapted from `TauCeti.Algebra.Lie.G2.ShortRoot.PointsSpecialIsogeny`, which carries out the
-- same programme over an arbitrary commutative ring, with the same sequence of declarations.

public section

open CategoryTheory Matrix WithConv
open scoped TensorProduct

namespace TauCeti.G2ShortRoot

open TauCeti.UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

universe v

local notation "CM" => CartanMatrix.G₂
local notation "rootGen" => TauCeti.serreRootGenerator CM
local notation "cartanGen" => TauCeti.serreH ℚ CM

namespace PrimeField

variable {A : Type v} [CommRing A] [Algebra (ZMod 3) A]

/-- The reduced structure matrices of the type-`G₂` cross product over `𝔽₃`. -/
private noncomputable def crossOperatorPrime : Fin 7 → Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  fun a => (crossOperator a).map (Int.cast : ℤ → ZMod 3)

/-- The reduced invariant dual form over `𝔽₃`. -/
private noncomputable def invariantDualFormPrime : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  invariantDualForm.map (Int.cast : ℤ → ZMod 3)

private theorem map_algebraMap_crossOperatorPrime (a : Fin 7) :
    (crossOperatorPrime a).map (algebraMap (ZMod 3) A) =
      (crossOperator a).map (Int.cast : ℤ → A) := by
  rw [crossOperatorPrime, Matrix.map_map]
  exact congrArg _ (funext fun z => map_intCast (algebraMap (ZMod 3) A) z)

private theorem map_algebraMap_invariantDualFormPrime :
    invariantDualFormPrime.map (algebraMap (ZMod 3) A) =
      invariantDualForm.map (Int.cast : ℤ → A) := by
  rw [invariantDualFormPrime, Matrix.map_map]
  exact congrArg _ (funext fun z => map_intCast (algebraMap (ZMod 3) A) z)

/-- Preserving the type-`G₂` cross product is preserving the constant multiplication over `𝔽₃`
whose structure matrices are the reduced cross-product operators. -/
private theorem preserves_crossOperatorPrime_iff (g : Matrix (Fin 7) (Fin 7) A) :
    ConstantMultiplication.Preserves (ZMod 3) 7 crossOperatorPrime g ↔ PreservesG2Cross g := by
  rw [ConstantMultiplication.preserves_def, preservesG2Cross_def]
  simp only [ConstantMultiplication.imageStructureMatrix_def, map_algebraMap_crossOperatorPrime]

/-! ### The generic matrices of the generators -/

/-- The generic matrix of a reduced root-subgroup coordinate map is a numbered simple-root point
of the integral carrier, over the additive coordinate algebra of `𝔾ₐ` over `𝔽₃`. -/
private theorem exists_map_genericMatrix_generator_inl (k : Fin 2 ⊕ Fin 2) :
    ∃ u : Multiplicative (AdditiveGroup.coordinateHopfAlgebra (ZMod 3)),
      (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7).map
          (generator (.inl k)).hom.toAlgHom =
        ((_root_.TauCeti.G2ShortRoot.rootSubgroupPoints k
          (AdditiveGroup.coordinateHopfAlgebra (ZMod 3)) u :
          _root_.Matrix.GeneralLinearGroup (Fin 7)
            (AdditiveGroup.coordinateHopfAlgebra (ZMod 3))) :
          Matrix (Fin 7) (Fin 7) (AdditiveGroup.coordinateHopfAlgebra (ZMod 3))) := by
  set B : CommAlgCat (ZMod 3) :=
    CommAlgCat.of (ZMod 3) (AdditiveGroup.coordinateHopfAlgebra (ZMod 3)) with hB
  set q : HopfAlgebra.points (R := ZMod 3)
      (H := AdditiveGroup.coordinateHopfAlgebra (ZMod 3)) B :=
    toConv (AlgHom.id (ZMod 3) (AdditiveGroup.coordinateHopfAlgebra (ZMod 3))) with hq
  have hid : (CommHopfAlgCat.mapPointsFunctor (generator (.inl k))).app B q =
      toConv (generator (.inl k)).hom.toAlgHom := by
    rw [CommHopfAlgCat.mapPointsFunctor_app_apply, hq, WithConv.ofConv_toConv, AlgHom.id_comp]
  refine ⟨AdditiveGroup.gaPointsMulEquiv (R := ZMod 3) q, ?_⟩
  rw [← coe_rootSubgroupPoints, coe_rootSubgroupPoints_gaPointsMulEquiv, hid,
    TauCeti.GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear,
    TauCeti.GeneralLinear.pointsMulEquiv_apply]

/-- The generic matrix of the reduced weight-torus coordinate map is a weight-torus point of the
integral carrier, over the coordinate algebra of the split torus over `𝔽₃`. -/
private theorem exists_map_genericMatrix_generator_inr :
    ∃ s : Fin 2 → ((DiagonalizableGroup.coordinateRing (ZMod 3)
      (SplitTorus.characterGroup (Fin 2))).obj)ˣ,
      (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7).map
          (generator (.inr ())).hom.toAlgHom =
        ((_root_.TauCeti.G2ShortRoot.weightTorusPoints
          ((DiagonalizableGroup.coordinateRing (ZMod 3)
            (SplitTorus.characterGroup (Fin 2))).obj) s :
          _root_.Matrix.GeneralLinearGroup (Fin 7)
            ((DiagonalizableGroup.coordinateRing (ZMod 3)
              (SplitTorus.characterGroup (Fin 2))).obj)) :
          Matrix (Fin 7) (Fin 7) ((DiagonalizableGroup.coordinateRing (ZMod 3)
            (SplitTorus.characterGroup (Fin 2))).obj)) := by
  set B : CommAlgCat (ZMod 3) :=
    CommAlgCat.of (ZMod 3) ((DiagonalizableGroup.coordinateRing (ZMod 3)
      (SplitTorus.characterGroup (Fin 2))).obj) with hB
  set q : HopfAlgebra.points (R := ZMod 3)
      (H := (DiagonalizableGroup.coordinateRing (ZMod 3)
        (SplitTorus.characterGroup (Fin 2))).obj) B :=
    toConv (AlgHom.id (ZMod 3) ((DiagonalizableGroup.coordinateRing (ZMod 3)
      (SplitTorus.characterGroup (Fin 2))).obj)) with hq
  have hid : (CommHopfAlgCat.mapPointsFunctor (generator (.inr ()))).app B q =
      toConv (generator (.inr ())).hom.toAlgHom := by
    rw [CommHopfAlgCat.mapPointsFunctor_app_apply, hq, WithConv.ofConv_toConv, AlgHom.id_comp]
  refine ⟨SplitTorus.pointsMulEquiv q, ?_⟩
  rw [← coe_weightTorusPoints, coe_weightTorusPoints_pointsMulEquiv, hid,
    TauCeti.GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear,
    TauCeti.GeneralLinear.pointsMulEquiv_apply]

/-! ### The invariants of the carrier's points -/

/-- **Every point of the short-root type-`G₂` carrier over `𝔽₃` preserves the cross product.** -/
theorem preservesG2Cross_of_mem_points {g : _root_.Matrix.GeneralLinearGroup (Fin 7) A}
    (hg : g ∈ points A) :
    PreservesG2Cross ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) := by
  rw [← preserves_crossOperatorPrime_iff]
  refine TauCeti.GeneralLinear.preserves_of_mem_generatedPointsSubgroup 7 generator
    crossOperatorPrime (fun j => ?_) A (points_def A ▸ hg)
  rcases j with k | ⟨⟩
  · obtain ⟨u, hu⟩ := exists_map_genericMatrix_generator_inl k
    rw [hu, preserves_crossOperatorPrime_iff]
    exact preservesG2Cross_coe_rootSubgroupPoints k u
  · obtain ⟨s, hs⟩ := exists_map_genericMatrix_generator_inr
    rw [hs, preserves_crossOperatorPrime_iff, coe_weightTorusPoints_eq_diagonal]
    exact preservesG2Cross_weightTorusMatrix s

/-- **Every point of the short-root type-`G₂` carrier over `𝔽₃` fixes the invariant dual form by
congruence.** -/
theorem preservesDualForm_of_mem_points {g : _root_.Matrix.GeneralLinearGroup (Fin 7) A}
    (hg : g ∈ points A) :
    ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) *
        invariantDualForm.map (Int.cast : ℤ → A) *
        ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A)ᵀ =
      invariantDualForm.map (Int.cast : ℤ → A) := by
  have key := TauCeti.GeneralLinear.mul_mul_transpose_of_mem_generatedPointsSubgroup 7 generator
    invariantDualFormPrime (fun j => ?_) A (points_def A ▸ hg)
  · rwa [map_algebraMap_invariantDualFormPrime] at key
  · rcases j with k | ⟨⟩
    · obtain ⟨u, hu⟩ := exists_map_genericMatrix_generator_inl k
      rw [hu, map_algebraMap_invariantDualFormPrime]
      exact preservesDualForm_coe_rootSubgroupPoints k u
    · obtain ⟨s, hs⟩ := exists_map_genericMatrix_generator_inr
      rw [hs, map_algebraMap_invariantDualFormPrime, coe_weightTorusPoints_eq_diagonal]
      exact preservesDualForm_weightTorusMatrix s

/-! ### Transport of the invariants along a morphism of value algebras -/

private theorem preservesG2Cross_map {S T : Type} [CommRing S] [CommRing T] [Algebra (ZMod 3) S]
    [Algebra (ZMod 3) T] (f : S →ₐ[ZMod 3] T) {M : Matrix (Fin 7) (Fin 7) S}
    (h : PreservesG2Cross M) : PreservesG2Cross (M.map f) := by
  rw [← preserves_crossOperatorPrime_iff] at h ⊢
  exact ConstantMultiplication.Preserves.map (ZMod 3) 7 crossOperatorPrime h f

private theorem preservesDualForm_map {S T : Type} [CommRing S] [CommRing T] [Algebra (ZMod 3) S]
    [Algebra (ZMod 3) T] (f : S →ₐ[ZMod 3] T) {M : Matrix (Fin 7) (Fin 7) S}
    (h : M * invariantDualForm.map (Int.cast : ℤ → S) * Mᵀ =
      invariantDualForm.map (Int.cast : ℤ → S)) :
    M.map f * invariantDualForm.map (Int.cast : ℤ → T) * (M.map f)ᵀ =
      invariantDualForm.map (Int.cast : ℤ → T) := by
  have hform : (invariantDualForm.map (Int.cast : ℤ → S)).map (f : S → T) =
      invariantDualForm.map (Int.cast : ℤ → T) := by
    rw [Matrix.map_map]
    exact congrArg _ (funext fun z => map_intCast f z)
  have himg := congrArg (fun N : Matrix (Fin 7) (Fin 7) S => N.map (f : S →+* T)) h
  simp only [Matrix.map_mul, Matrix.transpose_map, AlgHom.coe_toRingHom] at himg
  rwa [hform] at himg

/-! ### The coordinate morphism of the special isogeny -/

/-- The coordinate Hopf algebra of the short-root type-`G₂` carrier over `𝔽₃`. -/
noncomputable abbrev carrierAlgebra : CommHopfAlgCat (ZMod 3) :=
  CommHopfAlgCat.quotient (TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7)
    (CommHopfAlgCat.commonKernelHopfIdeal generator)

/-- The quotient morphism onto the coordinate Hopf algebra of the carrier over `𝔽₃`. -/
private noncomputable abbrev carrierQuotient :
    TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7 ⟶ carrierAlgebra :=
  CommHopfAlgCat.mkQuotient (TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7)
    (CommHopfAlgCat.commonKernelHopfIdeal generator)

/-- The generic matrix of the short-root type-`G₂` carrier over `𝔽₃`: the image of the generic
matrix of `GL₇` in the carrier's coordinate Hopf algebra. It is the matrix of the universal point
of the carrier. -/
noncomputable def carrierGenericMatrix : Matrix (Fin 7) (Fin 7) carrierAlgebra :=
  (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7).map carrierQuotient.hom.toAlgHom

/-- The matrix of the universal point is the carrier's generic matrix. -/
private theorem coe_universalPoint :
    ((TauCeti.GeneralLinear.pointToGeneralLinear 7 (toConv carrierQuotient.hom.toAlgHom) :
        _root_.Matrix.GeneralLinearGroup (Fin 7) carrierAlgebra) :
      Matrix (Fin 7) (Fin 7) carrierAlgebra) = carrierGenericMatrix := by
  rw [carrierGenericMatrix,
    TauCeti.GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear]

/-- **The universal point of the carrier over `𝔽₃` is one of its points.** -/
private theorem universalPoint_mem_points :
    TauCeti.GeneralLinear.pointToGeneralLinear 7 (toConv carrierQuotient.hom.toAlgHom) ∈
      points carrierAlgebra := by
  rw [points_def, TauCeti.GeneralLinear.mem_generatedPointsSubgroup_iff]
  intro x hx
  rw [← TauCeti.GeneralLinear.pointsMulEquiv_apply, MulEquiv.symm_apply_apply,
    WithConv.ofConv_toConv]
  have hker : x ∈ RingHom.ker (CommHopfAlgCat.mkQuotient
      (TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7)
      (CommHopfAlgCat.commonKernelHopfIdeal generator)).hom.toAlgHom.toRingHom := by
    rw [CommHopfAlgCat.mkQuotient_ker]
    exact hx
  rw [RingHom.mem_ker] at hker
  exact hker

/-- The carrier's generic matrix preserves the cross product. -/
private theorem preservesG2Cross_carrierGenericMatrix : PreservesG2Cross carrierGenericMatrix := by
  rw [← coe_universalPoint]
  exact preservesG2Cross_of_mem_points universalPoint_mem_points

/-- The carrier's generic matrix fixes the invariant dual form by congruence. -/
private theorem preservesDualForm_carrierGenericMatrix :
    carrierGenericMatrix * invariantDualForm.map (Int.cast : ℤ → carrierAlgebra) *
        carrierGenericMatrixᵀ =
      invariantDualForm.map (Int.cast : ℤ → carrierAlgebra) := by
  rw [← coe_universalPoint]
  exact preservesDualForm_of_mem_points universalPoint_mem_points

/-- Entrywise cubing commutes with an algebra morphism: the two `Matrix.map`s can be interchanged
because the morphism is multiplicative. -/
private theorem map_pow_map {S T : Type*} [CommRing S] [CommRing T]
    [Algebra (ZMod 3) S] [Algebra (ZMod 3) T] (f : S →ₐ[ZMod 3] T)
    (g : Matrix (Fin 7) (Fin 7) S) :
    (g.map (fun x => x ^ 3)).map f = (g.map f).map (fun y => y ^ 3) := by
  ext a b
  rw [Matrix.map_apply, Matrix.map_apply, Matrix.map_apply, Matrix.map_apply, map_pow]

/-- The matrix of signed minors of the carrier's generic matrix satisfies the comultiplication
condition: the carrier's generic matrix is grouplike, and the minor formula is multiplicative on
the two tensor inclusions of a matrix preserving the cross product and the dual form. -/
private theorem comul_g2SpecialIsogeny_carrierGenericMatrix :
    (g2SpecialIsogeny carrierGenericMatrix).map
        (Bialgebra.comulAlgHom (ZMod 3) carrierAlgebra) =
      (g2SpecialIsogeny carrierGenericMatrix).map
          (Algebra.TensorProduct.includeLeft (R := ZMod 3) (S := ZMod 3)) *
        (g2SpecialIsogeny carrierGenericMatrix).map
          (Algebra.TensorProduct.includeRight (R := ZMod 3)) := by
  let : CharP (carrierAlgebra ⊗[ZMod 3] carrierAlgebra) 3 :=
    charP_tensorSquare_of_bialgebra 3 carrierAlgebra
  have hX : carrierGenericMatrix.map (Bialgebra.comulAlgHom (ZMod 3) carrierAlgebra) =
      carrierGenericMatrix.map
          (Algebra.TensorProduct.includeLeft (R := ZMod 3) (S := ZMod 3)) *
        carrierGenericMatrix.map (Algebra.TensorProduct.includeRight (R := ZMod 3)) := by
    simpa only [carrierGenericMatrix, BialgHom.coe_toAlgHom] using
      TauCeti.GeneralLinear.map_genericMatrix_map_comul carrierQuotient.hom
  set iL : carrierAlgebra →ₐ[ZMod 3] carrierAlgebra ⊗[ZMod 3] carrierAlgebra :=
    Algebra.TensorProduct.includeLeft with hiL
  set iR : carrierAlgebra →ₐ[ZMod 3] carrierAlgebra ⊗[ZMod 3] carrierAlgebra :=
    Algebra.TensorProduct.includeRight with hiR
  have hmul := g2SpecialIsogeny_mul
    (preservesG2Cross_map iL preservesG2Cross_carrierGenericMatrix)
    (preservesDualForm_map iL preservesDualForm_carrierGenericMatrix)
    (preservesG2Cross_map iR preservesG2Cross_carrierGenericMatrix)
  rw [← g2SpecialIsogeny_map (Bialgebra.comulAlgHom (ZMod 3) carrierAlgebra), hX, hmul,
    g2SpecialIsogeny_map iL, g2SpecialIsogeny_map iR]

/-- The matrix of signed minors of the carrier's generic matrix satisfies the counit condition. -/
private theorem counit_g2SpecialIsogeny_carrierGenericMatrix :
    (g2SpecialIsogeny carrierGenericMatrix).map
      (Bialgebra.counitAlgHom (ZMod 3) carrierAlgebra) = 1 := by
  have hX : carrierGenericMatrix.map (Bialgebra.counitAlgHom (ZMod 3) carrierAlgebra) = 1 := by
    simpa only [carrierGenericMatrix, BialgHom.coe_toAlgHom] using
      TauCeti.GeneralLinear.map_genericMatrix_map_counit carrierQuotient.hom
  rw [← g2SpecialIsogeny_map (Bialgebra.counitAlgHom (ZMod 3) carrierAlgebra), hX,
    g2SpecialIsogeny_one]

/-- **The coordinate morphism of the special isogeny of the carrier over `𝔽₃`**: the morphism out
of the coordinate Hopf algebra of `GL₇` carrying the generic matrix to the matrix of signed
minors of the carrier's generic matrix. -/
noncomputable def coordinateMap :
    TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7 ⟶ carrierAlgebra :=
  CommHopfAlgCat.ofHom (TauCeti.GeneralLinear.coordinateBialgHomOfGroupLike (ZMod 3) 7
    (g2SpecialIsogeny carrierGenericMatrix) comul_g2SpecialIsogeny_carrierGenericMatrix
    counit_g2SpecialIsogeny_carrierGenericMatrix)

/-- **The generic matrix of the special isogeny's coordinate morphism is the matrix of signed
minors of the carrier's generic matrix.**

This is not a `simp` lemma: the simplifier rewrites the bialgebra-morphism coercion on the left,
so the left-hand side is not in normal form. -/
theorem map_genericMatrix_coordinateMap :
    (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7).map coordinateMap.hom.toAlgHom =
      g2SpecialIsogeny carrierGenericMatrix := by
  rw [coordinateMap]
  simpa only [CommHopfAlgCat.hom_ofHom, BialgHom.coe_toAlgHom] using
    TauCeti.GeneralLinear.map_genericMatrix_coordinateBialgHomOfGroupLike (ZMod 3) 7
      (g2SpecialIsogeny carrierGenericMatrix) comul_g2SpecialIsogeny_carrierGenericMatrix
      counit_g2SpecialIsogeny_carrierGenericMatrix

/-! ### The generator equations -/

/-- Transporting the generic matrix along a composite is transporting it twice. -/
private theorem map_genericMatrix_comp {K L : CommHopfAlgCat (ZMod 3)}
    (chi : TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7 ⟶ K) (chi' : K ⟶ L) :
    (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7).map (chi ≫ chi').hom.toAlgHom =
      ((TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7).map chi.hom.toAlgHom).map
        chi'.hom.toAlgHom := by
  rw [Matrix.map_map]
  exact congrArg _ (funext fun x => CommHopfAlgCat.comp_apply chi chi' x)

/-- **The special isogeny's coordinate morphism followed by a factored generator is the minor
formula at that generator's generic matrix.** -/
private theorem map_genericMatrix_coordinateMap_comp_commonKernelLift (j : (Fin 2 ⊕ Fin 2) ⊕ Unit) :
    (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7).map
        (coordinateMap ≫ CommHopfAlgCat.commonKernelLift generator j).hom.toAlgHom =
      g2SpecialIsogeny ((TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7).map
        (generator j).hom.toAlgHom) := by
  have hgen : (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7).map (generator j).hom.toAlgHom =
      carrierGenericMatrix.map
        (CommHopfAlgCat.commonKernelLift generator j).hom.toAlgHom := by
    rw [carrierGenericMatrix, ← map_genericMatrix_comp,
      CommHopfAlgCat.mkQuotient_comp_commonKernelLift]
  rw [map_genericMatrix_comp, map_genericMatrix_coordinateMap, hgen,
    g2SpecialIsogeny_map]

/-- A coordinate morphism out of `O(GL₇/𝔽₃)` whose generic matrix is the matrix of a point of the
carrier over `𝔽₃` is killed by the carrier's defining Hopf ideal. -/
private theorem toIdeal_le_ker_of_map_genericMatrix_eq {K : CommHopfAlgCat (ZMod 3)}
    (chi : TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7 ⟶ K) (g : points K)
    (h : (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7).map chi.hom.toAlgHom =
      ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)) :
    (CommHopfAlgCat.commonKernelHopfIdeal generator).toIdeal ≤
      RingHom.ker chi.hom.toAlgHom.toRingHom := by
  apply TauCeti.GeneralLinear.toIdeal_le_ker_of_pointToGeneralLinear_mem_hopfIdealPointsSubgroup
  have hg : TauCeti.GeneralLinear.pointToGeneralLinear 7 (toConv chi.hom.toAlgHom) =
      (g : _root_.Matrix.GeneralLinearGroup (Fin 7) K) := by
    apply Units.ext
    rw [← TauCeti.GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear, h]
  rw [hg]
  have hle : points K ≤ TauCeti.GeneralLinear.hopfIdealPointsSubgroup 7
      (CommHopfAlgCat.commonKernelHopfIdeal generator) K :=
    le_of_eq ((points_eq_hopfIdealPointsSubgroup K).trans
      (congrArg (fun I => TauCeti.GeneralLinear.hopfIdealPointsSubgroup 7 I
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
  rcases j with k | ⟨⟩
  · obtain ⟨u, hu⟩ := exists_map_genericMatrix_generator_inl k
    refine toIdeal_le_ker_of_map_genericMatrix_eq _
      (rootSubgroupPoints (specialIsogenyRootIndex k)
        (AdditiveGroup.coordinateHopfAlgebra (ZMod 3))
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ specialIsogenyExponent k))) ?_
    rw [map_genericMatrix_coordinateMap_comp_commonKernelLift, hu, coe_rootSubgroupPoints]
    exact g2SpecialIsogeny_coe_rootSubgroupPoints k (Multiplicative.toAdd u)
  · obtain ⟨s, hs⟩ := exists_map_genericMatrix_generator_inr
    refine toIdeal_le_ker_of_map_genericMatrix_eq _
      (weightTorusPoints ((DiagonalizableGroup.coordinateRing (ZMod 3)
        (SplitTorus.characterGroup (Fin 2))).obj) (specialIsogenyTorusMap s)) ?_
    rw [map_genericMatrix_coordinateMap_comp_commonKernelLift, hs, coe_weightTorusPoints]
    exact g2SpecialIsogeny_coe_weightTorusPoints s

/-! ### The endomorphism of the carrier's points -/

/-- The generic matrix transported along the point of an invertible matrix is that matrix. -/
private theorem map_ofConv_genericMatrix (h : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
    (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7).map
        ((TauCeti.GeneralLinear.pointsMulEquiv (R := ZMod 3) 7).symm h).ofConv =
      (h : Matrix (Fin 7) (Fin 7) A) := by
  rw [TauCeti.GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear,
    ← TauCeti.GeneralLinear.pointsMulEquiv_apply, WithConv.toConv_ofConv,
    MulEquiv.apply_symm_apply]

/-- **The endomorphism of points restricted from the special isogeny's coordinate morphism is the
minor formula.** -/
private theorem coe_generatedPointsEndomorphism
    (g : TauCeti.GeneralLinear.generatedPointsSubgroup 7 generator A) :
    ((TauCeti.GeneralLinear.generatedPointsEndomorphism 7 coordinateMap
          commonKernelHopfIdeal_toIdeal_le_ker_coordinateMap A g :
        _root_.Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) =
      g2SpecialIsogeny ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A) := by
  ext a b
  have hxy : (CommHopfAlgCat.mkQuotient (TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7)
        (CommHopfAlgCat.commonKernelHopfIdeal generator)).hom
        (g2SpecialIsogeny (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7) a b) =
      coordinateMap.hom (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7 a b) := by
    have hl := congrFun (congrFun (g2SpecialIsogeny_map carrierQuotient.hom.toAlgHom
      (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7)) a) b
    have hr := congrFun (congrFun map_genericMatrix_coordinateMap a) b
    simp only [Matrix.map_apply, BialgHom.coe_toAlgHom] at hl hr ⊢
    rw [hr, carrierGenericMatrix, ← hl]
    simp only [BialgHom.coe_toAlgHom]
  have key := TauCeti.GeneralLinear.ofConv_pointsMulEquiv_symm_generatedPointsEndomorphism 7
    coordinateMap commonKernelHopfIdeal_toIdeal_le_ker_coordinateMap A g
    (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7 a b)
    (g2SpecialIsogeny (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7) a b) hxy
  have hL : ((TauCeti.GeneralLinear.pointsMulEquiv (R := ZMod 3) 7).symm
        (TauCeti.GeneralLinear.generatedPointsEndomorphism 7 coordinateMap
          commonKernelHopfIdeal_toIdeal_le_ker_coordinateMap A g :
          _root_.Matrix.GeneralLinearGroup (Fin 7) A)).ofConv
        (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7 a b) =
      ((TauCeti.GeneralLinear.generatedPointsEndomorphism 7 coordinateMap
          commonKernelHopfIdeal_toIdeal_le_ker_coordinateMap A g :
        _root_.Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) a b := by
    rw [← map_ofConv_genericMatrix, Matrix.map_apply]
  have hR : ((TauCeti.GeneralLinear.pointsMulEquiv (R := ZMod 3) 7).symm
        (g : _root_.Matrix.GeneralLinearGroup (Fin 7) A)).ofConv
        (g2SpecialIsogeny (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7) a b) =
      g2SpecialIsogeny ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A) a b := by
    rw [← map_ofConv_genericMatrix (g : _root_.Matrix.GeneralLinearGroup (Fin 7) A),
      g2SpecialIsogeny_map, Matrix.map_apply]
  rw [hL, hR] at key
  exact key

/-! ### The special isogeny -/

/-- **The special isogeny is multiplicative on the points of the carrier over `𝔽₃`** in
characteristic three. -/
theorem g2SpecialIsogeny_mul_of_mem_points [CharP A 3]
    {g h : _root_.Matrix.GeneralLinearGroup (Fin 7) A} (hg : g ∈ points A) (hh : h ∈ points A) :
    g2SpecialIsogeny (((g * h : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A)) =
      g2SpecialIsogeny ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
          Matrix (Fin 7) (Fin 7) A) *
        g2SpecialIsogeny ((h : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
          Matrix (Fin 7) (Fin 7) A) := by
  rw [Units.val_mul]
  exact g2SpecialIsogeny_mul (preservesG2Cross_of_mem_points hg)
    (preservesDualForm_of_mem_points hg) (preservesG2Cross_of_mem_points hh)

variable (A) in
private theorem g2SpecialIsogeny_mul_g2SpecialIsogeny_inv [CharP A 3] (g : points A) :
    g2SpecialIsogeny ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
          Matrix (Fin 7) (Fin 7) A) *
        g2SpecialIsogeny (((g⁻¹ : points A) : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
          Matrix (Fin 7) (Fin 7) A) = 1 := by
  rw [← g2SpecialIsogeny_mul_of_mem_points g.2 (g⁻¹ : points A).2, ← Subgroup.coe_mul,
    mul_inv_cancel, Subgroup.coe_one, Units.val_one, g2SpecialIsogeny_one]

variable (A) in
private theorem g2SpecialIsogeny_inv_mul_g2SpecialIsogeny [CharP A 3] (g : points A) :
    g2SpecialIsogeny (((g⁻¹ : points A) : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
          Matrix (Fin 7) (Fin 7) A) *
        g2SpecialIsogeny ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
          Matrix (Fin 7) (Fin 7) A) = 1 := by
  rw [← g2SpecialIsogeny_mul_of_mem_points (g⁻¹ : points A).2 g.2, ← Subgroup.coe_mul,
    inv_mul_cancel, Subgroup.coe_one, Units.val_one, g2SpecialIsogeny_one]

/-- The minor formula on the points of the carrier over `𝔽₃`, valued in the ambient general
linear group. -/
private noncomputable def specialIsogenyGeneralLinear (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] [CharP A 3] :
    points A →* _root_.Matrix.GeneralLinearGroup (Fin 7) A :=
  MonoidHom.mk'
    (fun g => ⟨g2SpecialIsogeny ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A),
      g2SpecialIsogeny (((g⁻¹ : points A) : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A),
      g2SpecialIsogeny_mul_g2SpecialIsogeny_inv A g,
      g2SpecialIsogeny_inv_mul_g2SpecialIsogeny A g⟩)
    fun g h => Units.ext (g2SpecialIsogeny_mul_of_mem_points g.2 h.2)

private theorem coe_specialIsogenyGeneralLinear [CharP A 3] (g : points A) :
    ((specialIsogenyGeneralLinear A g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A) =
      g2SpecialIsogeny ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A) := by
  rw [specialIsogenyGeneralLinear]
  rfl

/-- **The special isogeny carries a point of the carrier over `𝔽₃` to a point of it.** -/
private theorem specialIsogenyGeneralLinear_mem_points [CharP A 3] (g : points A) :
    specialIsogenyGeneralLinear A g ∈ points A := by
  have hle : points A ≤ TauCeti.GeneralLinear.generatedPointsSubgroup 7 generator A :=
    le_of_eq (points_def A)
  have hle' : TauCeti.GeneralLinear.generatedPointsSubgroup 7 generator A ≤ points A :=
    le_of_eq (points_def A).symm
  refine hle' ?_
  have himg := (TauCeti.GeneralLinear.generatedPointsEndomorphism 7 coordinateMap
    commonKernelHopfIdeal_toIdeal_le_ker_coordinateMap A
    ⟨(g : _root_.Matrix.GeneralLinearGroup (Fin 7) A), hle g.2⟩).2
  have heq : (TauCeti.GeneralLinear.generatedPointsEndomorphism 7 coordinateMap
      commonKernelHopfIdeal_toIdeal_le_ker_coordinateMap A
      ⟨(g : _root_.Matrix.GeneralLinearGroup (Fin 7) A), hle g.2⟩ :
      _root_.Matrix.GeneralLinearGroup (Fin 7) A) = specialIsogenyGeneralLinear A g :=
    Units.ext (by rw [coe_generatedPointsEndomorphism, coe_specialIsogenyGeneralLinear])
  rwa [heq] at himg

/-- **The special isogeny of the short-root type-`G₂` carrier over `𝔽₃` in characteristic
three**: the endomorphism of the carrier's points given by the matrix of signed `2 × 2` minors. -/
noncomputable def specialIsogeny (A : Type v) [CommRing A] [Algebra (ZMod 3) A] [CharP A 3] :
    points A →* points A :=
  MonoidHom.codRestrict (specialIsogenyGeneralLinear A) (points A)
    specialIsogenyGeneralLinear_mem_points

/-- The matrix of the special isogeny at a point of the carrier over `𝔽₃` is the minor formula at
its matrix. -/
@[simp]
theorem coe_specialIsogeny [CharP A 3] (g : points A) :
    ((specialIsogeny A g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A) =
      g2SpecialIsogeny ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A) := by
  rw [specialIsogeny, MonoidHom.codRestrict_apply, coe_specialIsogenyGeneralLinear]

/-! ### The pinning equations -/

/-- **The pinning equations of the special isogeny on the numbered simple root subgroups of the
carrier over `𝔽₃`**: the numbered simple-root point at `k` goes to the one at the length-exchanged
index, with the parameter raised to the exponent of `k`, three at the short node and one at the
long node. -/
@[simp]
theorem specialIsogeny_rootSubgroupPoints [CharP A 3] (k : Fin 2 ⊕ Fin 2) (t : A) :
    specialIsogeny A (rootSubgroupPoints k A (Multiplicative.ofAdd t)) =
      rootSubgroupPoints (specialIsogenyRootIndex k) A
        (Multiplicative.ofAdd (t ^ specialIsogenyExponent k)) :=
  Subtype.ext (Units.ext (by
    rw [coe_specialIsogeny, coe_rootSubgroupPoints, coe_rootSubgroupPoints,
      g2SpecialIsogeny_coe_rootSubgroupPoints]))

/-- **The torus equation of the special isogeny on the carrier over `𝔽₃`**: a point of the split
weight torus goes to the point of the length-exchanged coordinates `(s₁, s₀³)`. -/
@[simp]
theorem specialIsogeny_weightTorusPoints [CharP A 3] (s : Fin 2 → Aˣ) :
    specialIsogeny A (weightTorusPoints A s) =
      weightTorusPoints A (specialIsogenyTorusMap s) :=
  Subtype.ext (Units.ext (by
    rw [coe_specialIsogeny, coe_weightTorusPoints, coe_weightTorusPoints,
      g2SpecialIsogeny_coe_weightTorusPoints]))

/-! ### The square relation against the Frobenius -/

/-- Applying the length-exchanging map on torus points twice cubes every coordinate. -/
private theorem specialIsogenyTorusMap_specialIsogenyTorusMap {B : Type*} [CommRing B]
    (s : Fin 2 → Bˣ) :
    specialIsogenyTorusMap (specialIsogenyTorusMap s) = s ^ 3 := by
  funext i
  fin_cases i <;>
    simp only [specialIsogenyTorusMap_def, Matrix.cons_val_zero, Matrix.cons_val_one,
      Pi.pow_apply, Fin.isValue, Fin.zero_eta, Fin.mk_one]

/-- The twice-iterated minor formula at a numbered simple-root point of the integral carrier is
the entrywise cube. -/
private theorem g2SpecialIsogeny_g2SpecialIsogeny_coe_rootSubgroupPoints_eq_map_pow
    {B : Type} [CommRing B] [CharP B 3] (k : Fin 2 ⊕ Fin 2) (u : Multiplicative B) :
    g2SpecialIsogeny (g2SpecialIsogeny
        ((_root_.TauCeti.G2ShortRoot.rootSubgroupPoints k B u :
          _root_.Matrix.GeneralLinearGroup (Fin 7) B) : Matrix (Fin 7) (Fin 7) B)) =
      ((_root_.TauCeti.G2ShortRoot.rootSubgroupPoints k B u :
        _root_.Matrix.GeneralLinearGroup (Fin 7) B) :
        Matrix (Fin 7) (Fin 7) B).map (fun x => x ^ 3) := by
  obtain ⟨t, rfl⟩ : ∃ t : B, Multiplicative.ofAdd t = u := ⟨Multiplicative.toAdd u, rfl⟩
  have hsq :=
    g2SpecialIsogeny_g2SpecialIsogeny_coe_rootSubgroupPoints_eq_frobenius (A := B) k t
  rw [hsq]
  ext a b
  rw [Matrix.map_apply, _root_.TauCeti.G2ShortRoot.coe_frobenius_apply]
  norm_num

/-- The twice-iterated minor formula at a weight-torus point of the integral carrier is the
entrywise cube. -/
private theorem g2SpecialIsogeny_g2SpecialIsogeny_coe_weightTorusPoints_eq_map_pow
    {B : Type} [CommRing B] [CharP B 3] (s : Fin 2 → Bˣ) :
    g2SpecialIsogeny (g2SpecialIsogeny
        ((_root_.TauCeti.G2ShortRoot.weightTorusPoints B s :
          _root_.Matrix.GeneralLinearGroup (Fin 7) B) : Matrix (Fin 7) (Fin 7) B)) =
      ((_root_.TauCeti.G2ShortRoot.weightTorusPoints B s :
        _root_.Matrix.GeneralLinearGroup (Fin 7) B) :
        Matrix (Fin 7) (Fin 7) B).map (fun x => x ^ 3) := by
  rw [g2SpecialIsogeny_coe_weightTorusPoints, g2SpecialIsogeny_coe_weightTorusPoints,
    specialIsogenyTorusMap_specialIsogenyTorusMap]
  have hfrob := _root_.TauCeti.G2ShortRoot.frobenius_weightTorusPoints 3 1 B s
  rw [pow_one] at hfrob
  rw [← hfrob]
  ext a b
  rw [Matrix.map_apply, _root_.TauCeti.G2ShortRoot.coe_frobenius_apply]
  norm_num

/-- Two coordinate morphisms out of `O(GL₇/𝔽₃)` with the same generic matrix are equal. -/
private theorem coordinate_hom_ext {K : CommHopfAlgCat (ZMod 3)}
    (chi chi' : TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7 ⟶ K)
    (h : (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7).map chi.hom.toAlgHom =
      (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7).map chi'.hom.toAlgHom) : chi = chi' := by
  refine CommHopfAlgCat.hom_ext ?_
  refine TauCeti.GeneralLinear.coordinateHopfAlgebra_bialgHom_ext (R := ZMod 3) (n := 7) ?_
  intro a b
  have hab := congrFun (congrFun h a) b
  rw [Matrix.map_apply, Matrix.map_apply, TauCeti.GeneralLinear.genericMatrix_apply] at hab
  simpa only [BialgHom.coe_toAlgHom] using hab

/-- **The coordinate morphism of the carrier's Frobenius**: the cube map of the coordinate Hopf
algebra of `GL₇` over `𝔽₃`, followed by the quotient onto the carrier. -/
noncomputable def frobeniusCoordinateMap :
    TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7 ⟶ carrierAlgebra :=
  CommHopfAlgCat.ofHom
      (TauCeti.frobeniusBialgHom 3 (TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7)) ≫
    carrierQuotient

/-- The factorization of the special isogeny's coordinate morphism through the carrier. -/
private noncomputable def liftedCoordinateMap : carrierAlgebra ⟶ carrierAlgebra :=
  CommHopfAlgCat.liftQuotient (CommHopfAlgCat.commonKernelHopfIdeal generator) coordinateMap
    commonKernelHopfIdeal_toIdeal_le_ker_coordinateMap

private theorem map_genericMatrix_comp_liftedCoordinateMap :
    (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7).map
        (coordinateMap ≫ liftedCoordinateMap).hom.toAlgHom =
      g2SpecialIsogeny (g2SpecialIsogeny carrierGenericMatrix) := by
  have hq : carrierGenericMatrix.map liftedCoordinateMap.hom.toAlgHom =
      g2SpecialIsogeny carrierGenericMatrix := by
    conv_lhs => rw [carrierGenericMatrix]
    rw [← map_genericMatrix_comp, liftedCoordinateMap,
      CommHopfAlgCat.mkQuotient_comp_liftQuotient, map_genericMatrix_coordinateMap]
  rw [map_genericMatrix_comp, map_genericMatrix_coordinateMap,
    ← g2SpecialIsogeny_map, hq]

/-- **The generic matrix of the Frobenius coordinate morphism is the entrywise cube of the
carrier's generic matrix.** -/
theorem map_genericMatrix_frobeniusCoordinateMap :
    (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7).map frobeniusCoordinateMap.hom.toAlgHom =
      carrierGenericMatrix.map (fun x => x ^ 3) := by
  rw [frobeniusCoordinateMap, map_genericMatrix_comp, carrierGenericMatrix, Matrix.map_map,
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
  have hXj : carrierGenericMatrix.map
        (CommHopfAlgCat.commonKernelLift generator j).hom.toAlgHom =
      (TauCeti.GeneralLinear.genericMatrix (ZMod 3) 7).map (generator j).hom.toAlgHom := by
    conv_lhs => rw [carrierGenericMatrix]
    rw [← map_genericMatrix_comp, CommHopfAlgCat.mkQuotient_comp_commonKernelLift]
  let : CharP (generatorCodomain j) 3 := TauCeti.charP_of_bialgebra 3 (generatorCodomain j)
  rw [map_genericMatrix_comp (coordinateMap ≫ liftedCoordinateMap)
      (CommHopfAlgCat.commonKernelLift generator j),
    map_genericMatrix_comp_liftedCoordinateMap,
    map_genericMatrix_comp frobeniusCoordinateMap
      (CommHopfAlgCat.commonKernelLift generator j),
    map_genericMatrix_frobeniusCoordinateMap, ← g2SpecialIsogeny_map,
    ← g2SpecialIsogeny_map, map_pow_map, hXj]
  rcases j with k | ⟨⟩
  · obtain ⟨u, hu⟩ := exists_map_genericMatrix_generator_inl k
    rw [hu]
    exact g2SpecialIsogeny_g2SpecialIsogeny_coe_rootSubgroupPoints_eq_map_pow k u
  · obtain ⟨s, hs⟩ := exists_map_genericMatrix_generator_inr
    rw [hs]
    exact g2SpecialIsogeny_g2SpecialIsogeny_coe_weightTorusPoints_eq_map_pow s

/-- **The twice-iterated minor formula at the carrier's generic matrix is the entrywise cube.** -/
private theorem g2SpecialIsogeny_g2SpecialIsogeny_carrierGenericMatrix :
    g2SpecialIsogeny (g2SpecialIsogeny carrierGenericMatrix) =
      carrierGenericMatrix.map (fun x => x ^ 3) := by
  rw [← map_genericMatrix_comp_liftedCoordinateMap, coordinateMap_comp_liftedCoordinateMap,
    map_genericMatrix_frobeniusCoordinateMap]

/-- **The twice-iterated minor formula at a point of the carrier over `𝔽₃` is the entrywise
cube.** -/
private theorem g2SpecialIsogeny_g2SpecialIsogeny_of_mem_points
    {g : _root_.Matrix.GeneralLinearGroup (Fin 7) A} (hg : g ∈ points A) :
    g2SpecialIsogeny (g2SpecialIsogeny ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A)) =
      ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A).map (fun x => x ^ 3) := by
  have hker : ∀ h : TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7,
      h ∈ CommHopfAlgCat.commonKernelHopfIdeal generator →
        ((TauCeti.GeneralLinear.pointsMulEquiv (R := ZMod 3) 7).symm g).ofConv h = 0 := by
    have hmem := le_of_eq (points_def A) hg
    rw [TauCeti.GeneralLinear.mem_generatedPointsSubgroup_iff] at hmem
    exact hmem
  set q := CommHopfAlgCat.liftQuotientPoint
    (TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7)
    (CommHopfAlgCat.commonKernelHopfIdeal generator) (CommAlgCat.of (ZMod 3) A)
    ((TauCeti.GeneralLinear.pointsMulEquiv (R := ZMod 3) 7).symm g) hker with hq
  have hcomp : (q.ofConv : carrierAlgebra → A) ∘
        (carrierQuotient.hom.toAlgHom :
          TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7 → carrierAlgebra) =
      (((TauCeti.GeneralLinear.pointsMulEquiv (R := ZMod 3) 7).symm g).ofConv :
        TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7 → A) := by
    funext x
    rw [Function.comp_apply, hq, carrierQuotient, BialgHom.coe_toAlgHom,
      CommHopfAlgCat.mkQuotient_apply]
    exact CommHopfAlgCat.liftQuotientPoint_mk
      (TauCeti.GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7)
      (CommHopfAlgCat.commonKernelHopfIdeal generator) (CommAlgCat.of (ZMod 3) A)
      ((TauCeti.GeneralLinear.pointsMulEquiv (R := ZMod 3) 7).symm g) hker x
  have hphi : carrierGenericMatrix.map q.ofConv =
      ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) := by
    rw [carrierGenericMatrix, Matrix.map_map, hcomp, map_ofConv_genericMatrix]
  rw [← hphi, g2SpecialIsogeny_map, g2SpecialIsogeny_map,
    g2SpecialIsogeny_g2SpecialIsogeny_carrierGenericMatrix, Matrix.map_map, Matrix.map_map]
  exact congrArg _ (funext fun x => map_pow q.ofConv x 3)

/-- **The special isogeny of the carrier over `𝔽₃` squares to the carrier's Frobenius.** -/
theorem specialIsogeny_specialIsogeny [CharP A 3] (g : points A) :
    specialIsogeny A (specialIsogeny A g) = frobenius 1 A g := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_specialIsogeny, coe_specialIsogeny,
    g2SpecialIsogeny_g2SpecialIsogeny_of_mem_points g.2]
  ext a b
  rw [Matrix.map_apply, coe_frobenius_apply]
  norm_num

/-- **The square relation as an equality of endomorphisms** of the carrier's points. -/
theorem specialIsogeny_comp_specialIsogeny [CharP A 3] :
    (specialIsogeny A).comp (specialIsogeny A) = frobenius 1 A :=
  MonoidHom.ext fun g => specialIsogeny_specialIsogeny g

end PrimeField

end TauCeti.G2ShortRoot
