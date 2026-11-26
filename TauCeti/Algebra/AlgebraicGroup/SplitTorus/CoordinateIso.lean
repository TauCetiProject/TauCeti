/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Basic
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.Product
public import TauCeti.Algebra.Bialgebra.MonoidAlgebra.Product
public import TauCeti.Data.Finsupp.Fin
import TauCeti.Algebra.Bialgebra.MonoidAlgebra.Equiv

/-!
# Universe lifting and rank-two tensor presentation of split-torus coordinate algebras

For every rank, lifting the finite coordinate indices to the base ring's universe identifies
the two split-torus coordinate Hopf algebras. On points, this identification reads the
coordinate tuple at the lifted indices. This is the adapter used by chosen split maximal tori.

For rank two over any commutative semiring `R`, this file also packages the coordinate bialgebra
isomorphism `R[Multiplicative (ULift (Fin 2) →₀ ℤ)] ≃ₐc[R] R[T;T⁻¹] ⊗[R] R[T;T⁻¹]`
(`TauCeti.SplitTorus.rankTwoTensorBialgEquiv`) induced by `Finsupp.uliftFinTwoAddEquiv`, together
with its action on monomials and on tensor-product points.

The coordinate construction follows
`TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.MaximalTorus`, using Mathlib's
`MonoidAlgebra.domCongrBialgEquiv` and `Finsupp.domCongr`.
-/

public section

open WithConv
open scoped LaurentPolynomial TensorProduct

namespace TauCeti.SplitTorus

universe u v

section ULift

variable (R : Type u) [CommRing R] (n : ℕ)

/-- Lift the coordinate indices of a rank-`n` split torus to the base ring's universe. -/
noncomputable def uliftCoordinateRingIso :
    (DiagonalizableGroup.coordinateRing R (characterGroup (Fin n))).obj ≅
      (DiagonalizableGroup.coordinateRing R (characterGroup (ULift.{u} (Fin n)))).obj :=
  -- Specify the unbundled character types so elaboration does not seek an additive
  -- structure on the bundled multiplicative character groups.
  _root_.CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv R R
    (show Multiplicative (Fin n →₀ ℤ) ≃* Multiplicative (ULift.{u} (Fin n) →₀ ℤ) from
      AddEquiv.toMultiplicative (Finsupp.domCongr (M := ℤ) Equiv.ulift.symm)))

/-- The lifted coordinate map is Mathlib's reindexing of the monoid algebra. -/
@[simp↓]
theorem uliftCoordinateRingIso_hom_apply
    (x : MonoidAlgebra R (Multiplicative (Fin n →₀ ℤ))) :
    (uliftCoordinateRingIso R n).hom.hom x =
      MonoidAlgebra.domCongr R R
        (AddEquiv.toMultiplicative
          (Finsupp.domCongr (M := ℤ) (Equiv.ulift.symm : Fin n ≃ ULift.{u} (Fin n)))) x :=
  (rfl)

/-- Lifting split-torus coordinates reads a point's coordinate at the lifted index. -/
-- Apply before `BialgHom.mapDomain_apply` expands point precomposition.
@[simp↓]
theorem pointsMulEquiv_mapDomain_uliftCoordinateRingIso
    {A : Type v} [CommRing A] [Algebra R A]
    (q : WithConv (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) →ₐ[R] A))
    (i : Fin n) :
    pointsMulEquiv (BialgHom.mapDomain (uliftCoordinateRingIso R n).hom.hom q) i =
      pointsMulEquiv q (ULift.up i) := by
  apply Units.ext
  rw [pointsMulEquiv_apply_coe, pointsMulEquiv_apply_coe,
    BialgHom.mapDomain_apply, AlgHom.comp_apply, BialgHom.coe_toAlgHom]
  rw [uliftCoordinateRingIso_hom_apply, MonoidAlgebra.domCongr_single]
  simp [AddEquiv.toMultiplicative_apply_apply, Finsupp.domCongr_apply]

end ULift

section RankTwo

/-- Multiplicative equivalence identifying the rank-two lifted character lattice
`Multiplicative (ULift (Fin 2) →₀ ℤ)` with `Multiplicative ℤ × Multiplicative ℤ`. -/
noncomputable def finTwoMulEquiv :
    Multiplicative (ULift.{u} (Fin 2) →₀ ℤ) ≃* Multiplicative ℤ × Multiplicative ℤ :=
  (AddEquiv.toMultiplicative (Finsupp.uliftFinTwoAddEquiv ℤ)).trans
    (MulEquiv.prodMultiplicative ℤ ℤ)

@[simp]
theorem finTwoMulEquiv_apply (m : Multiplicative (ULift.{u} (Fin 2) →₀ ℤ)) :
    finTwoMulEquiv m =
      (Multiplicative.ofAdd (m.toAdd ⟨0⟩), Multiplicative.ofAdd (m.toAdd ⟨1⟩)) := by
  simp [finTwoMulEquiv]

private noncomputable def rankTwoTensorAux (R : Type v) [CommSemiring R] :
    MonoidAlgebra R (Multiplicative ℤ) ⊗[R] MonoidAlgebra R (Multiplicative ℤ) ≃ₐc[R]
      R[T;T⁻¹] ⊗[R] R[T;T⁻¹] :=
  let eL := (AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).symm
  BialgEquiv.ofBialgHom
    (_root_.Bialgebra.TensorProduct.map eL.toBialgHom eL.toBialgHom)
    (_root_.Bialgebra.TensorProduct.map eL.symm.toBialgHom eL.symm.toBialgHom)
    (TauCeti.Bialgebra.TensorProduct.map_comp_map_eq_id_iff.mpr ⟨eL.comp_symm, eL.comp_symm⟩)
    (TauCeti.Bialgebra.TensorProduct.map_comp_map_eq_id_iff.mpr ⟨eL.symm_comp, eL.symm_comp⟩)

private theorem rankTwoTensorAux_tmul (R : Type v) [CommSemiring R]
    (x y : MonoidAlgebra R (Multiplicative ℤ)) :
    rankTwoTensorAux R (x ⊗ₜ[R] y) =
      (AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).symm x ⊗ₜ[R]
        (AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).symm y := by
  rw [rankTwoTensorAux, ← BialgEquiv.coe_toBialgHom, BialgEquiv.coe_ofBialgHom]
  exact Bialgebra.TensorProduct.map_tmul _ _ x y

/-- Coordinate bialgebra isomorphism identifying the rank-two split torus with
`R[T;T⁻¹] ⊗[R] R[T;T⁻¹]` over any commutative semiring `R`. -/
noncomputable def rankTwoTensorBialgEquiv (R : Type v) [CommSemiring R] :
    MonoidAlgebra R (Multiplicative (ULift.{u} (Fin 2) →₀ ℤ)) ≃ₐc[R]
      R[T;T⁻¹] ⊗[R] R[T;T⁻¹] :=
  (MonoidAlgebra.domCongrBialgEquiv R R finTwoMulEquiv.{u}).trans
    ((MonoidAlgebra.prodTensorBialgEquiv R).trans (rankTwoTensorAux R))

/-- The rank-two tensor presentation sends a monomial `single m r` to
`T (m.toAdd ⟨0⟩) ⊗ₜ (C r * T (m.toAdd ⟨1⟩))`. -/
@[simp]
theorem rankTwoTensorBialgEquiv_single (R : Type v) [CommSemiring R]
    (m : Multiplicative (ULift.{u} (Fin 2) →₀ ℤ)) (r : R) :
    rankTwoTensorBialgEquiv.{u} R (MonoidAlgebra.single m r) =
      LaurentPolynomial.T (m.toAdd ⟨0⟩) ⊗ₜ[R]
        (LaurentPolynomial.C r * LaurentPolynomial.T (m.toAdd ⟨1⟩)) := by
  have hdom : MonoidAlgebra.domCongrBialgEquiv R R finTwoMulEquiv.{u}
      (MonoidAlgebra.single m r) =
      MonoidAlgebra.single (Multiplicative.ofAdd (m.toAdd ⟨0⟩),
        Multiplicative.ofAdd (m.toAdd ⟨1⟩)) r := by
    simp [MonoidAlgebra.domCongrBialgEquiv]
  rw [rankTwoTensorBialgEquiv, ← BialgEquiv.coe_toBialgHom, BialgEquiv.trans_toBialgHom,
    BialgEquiv.trans_toBialgHom, BialgHom.comp_apply, BialgHom.comp_apply,
    BialgEquiv.coe_toBialgHom, BialgEquiv.coe_toBialgHom, BialgEquiv.coe_toBialgHom, hdom,
    MonoidAlgebra.prodTensorBialgEquiv_single, rankTwoTensorAux_tmul]
  simp only [AddMonoidAlgebra.toMultiplicativeBialgEquiv_symm_single, toAdd_ofAdd,
    LaurentPolynomial.single_eq_C_mul_T, map_one, one_mul]

/-- Evaluating a tensor-product point transported along `rankTwoTensorBialgEquiv` at any character
monomial `single m 1`. -/
theorem mapDomain_rankTwoTensorBialgEquiv_single {R A : Type*} [CommSemiring R]
    [CommSemiring A] [Algebra R A]
    (p : WithConv (R[T;T⁻¹] →ₐ[R] A) × WithConv (R[T;T⁻¹] →ₐ[R] A))
    (m : Multiplicative (ULift.{u} (Fin 2) →₀ ℤ)) :
    (BialgHom.mapDomain (rankTwoTensorBialgEquiv.{u} R).toBialgHom
        (AffineGroup.Product.pointsMulEquiv.symm p)).ofConv (MonoidAlgebra.single m 1) =
      ((MultiplicativeGroup.pointsMulEquiv p.1 ^ m.toAdd ⟨0⟩ *
        MultiplicativeGroup.pointsMulEquiv p.2 ^ m.toAdd ⟨1⟩ : Aˣ) : A) := by
  have hp1 : p.1.ofConv = laurentEval (R := R) (MultiplicativeGroup.pointsMulEquiv p.1) := by simp
  have hp2 : p.2.ofConv = laurentEval (R := R) (MultiplicativeGroup.pointsMulEquiv p.2) := by simp
  rw [BialgHom.mapDomain_apply_apply, BialgEquiv.toBialgHom_eq_coe, BialgEquiv.coe_toBialgHom,
    rankTwoTensorBialgEquiv_single, map_one, one_mul,
    AffineGroup.Product.pointsMulEquiv_symm_apply, ofConv_toConv,
    Algebra.TensorProduct.productMap_apply_tmul, hp1, hp2, laurentEval_T, laurentEval_T,
    Units.val_mul]

/-- Reading the two split-torus coordinates of a tensor-product point transported along
`rankTwoTensorBialgEquiv`. -/
theorem pointsMulEquiv_mapDomain_rankTwoTensorBialgEquiv {R A : Type*} [CommSemiring R]
    [CommSemiring A] [Algebra R A]
    (p : WithConv (R[T;T⁻¹] →ₐ[R] A) × WithConv (R[T;T⁻¹] →ₐ[R] A)) :
    (pointsMulEquiv (BialgHom.mapDomain (rankTwoTensorBialgEquiv.{u} R).toBialgHom
        (AffineGroup.Product.pointsMulEquiv.symm p)) ⟨0⟩,
      pointsMulEquiv (BialgHom.mapDomain (rankTwoTensorBialgEquiv.{u} R).toBialgHom
        (AffineGroup.Product.pointsMulEquiv.symm p)) ⟨1⟩) =
      (MultiplicativeGroup.pointsMulEquiv p.1, MultiplicativeGroup.pointsMulEquiv p.2) := by
  apply Prod.ext <;> apply Units.ext <;>
    rw [pointsMulEquiv_apply_coe, mapDomain_rankTwoTensorBialgEquiv_single] <;> simp

end RankTwo

end TauCeti.SplitTorus
