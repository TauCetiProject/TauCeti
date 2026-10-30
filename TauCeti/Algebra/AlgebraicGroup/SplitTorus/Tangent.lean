/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Cocharacter
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Map

/-!
# Tangent coordinates of a split torus

For a character lattice with a finite basis, evaluation on the coordinate monomials identifies
the tangent space of the split torus with the corresponding power of the coefficient algebra.
The coordinate vectors are the differentials of its coordinate cocharacters.

## Main declarations

* `derivation_ext`: coordinate monomials determine tangent derivations, even in infinite rank.
* `tangentLinearEquiv`: the coordinate equivalence over any commutative coefficient algebra.
* `tangentBasis_apply`: the basis vectors are the coordinate-cocharacter differentials.
* `tangentLinearEquiv_symm_apply`: the finite coordinate decomposition.
* `range_derivationCompLieHom`: the tangent image is spanned by the cocharacter differentials.
-/

public section

namespace TauCeti.SplitTorus

open TauCeti.Bialgebra

noncomputable section

variable {R B I : Type*} [CommRing R] [CommRing B] [Algebra R B]

local notation "A" => MonoidAlgebra R (Multiplicative (I →₀ ℤ))
local notation "C" => CounitAlgebra R A B

private def monomialDerivative (d : Derivation R A C) : (I →₀ ℤ) →+ C where
  toFun m := d (MonoidAlgebra.single (Multiplicative.ofAdd m) 1)
  map_zero' := by
    simpa only [ofAdd_zero, ← MonoidAlgebra.one_def] using d.map_one_eq_zero
  map_add' m n := by
    rw [ofAdd_add, ← mul_one (1 : R), ← MonoidAlgebra.single_mul_single,
      Derivation.leibniz]
    simp only [Algebra.smul_def, CounitAlgebra.algebraMap_apply,
      MonoidAlgebra.counit_single, _root_.Bialgebra.counit_one, map_one]
    -- The counit calculation leaves `1 : B`, while derivation values lie in the synonym `C`.
    -- Display its identical multiplication on `C` so that `one_mul` applies.
    change (1 : C) * d _ + (1 : C) * d _ = d _ + d _
    simp only [one_mul, add_comm]

/-- A tangent derivation of a split torus is determined by its coordinate monomials.
The index type need not be finite for this generator test. -/
@[ext]
theorem derivation_ext {d e : Derivation R A C}
    (h : ∀ i, d (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i 1)) 1) =
      e (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i 1)) 1)) : d = e := by
  have hmon : monomialDerivative d = monomialDerivative e := by
    apply Finsupp.addHom_ext'
    intro i
    apply AddMonoidHom.ext_int
    exact h i
  apply Derivation.ext
  intro a
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | single m r =>
    have hm : d (MonoidAlgebra.single m 1) = e (MonoidAlgebra.single m 1) := by
      simpa only [monomialDerivative, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ofAdd_toAdd] using
        DFunLike.congr_fun hmon m.toAdd
    have hs : MonoidAlgebra.single m r = r • MonoidAlgebra.single m (1 : R) := by
      rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rw [hs, Derivation.map_smul, Derivation.map_smul, hm]

private def tangentCoordinates : Derivation R A C →ₗ[B] (I → B) where
  toFun d i :=
    CounitAlgebra.algEquivSelf R A B
      (d (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i 1)) 1))
  map_add' _d _e := funext fun _i ↦ (CounitAlgebra.algEquivSelf R A B).map_add _ _
  map_smul' b d := funext fun _i ↦ algEquivSelf_derivation_smul_apply b d _

private theorem tangentCoordinates_apply (d : Derivation R A C) (i : I) :
    tangentCoordinates d i =
      CounitAlgebra.algEquivSelf R A B
        (d (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i 1)) 1)) :=
  rfl

private def coordinateDerivation (i : I) : Derivation R A C :=
  derivationCompLieHom
    ((BialgHom.id R A).cocharacter (Finsupp.applyAddHom i).toMultiplicative)
    ((MultiplicativeGroup.tangentLinearEquiv (R := R) (B := B)).symm 1)

private theorem tangentCoordinates_coordinateDerivation [DecidableEq I] (i j : I) :
    tangentCoordinates (coordinateDerivation (R := R) (B := B) i) j =
      if i = j then 1 else 0 := by
  rw [tangentCoordinates_apply]
  simp only [coordinateDerivation, derivationCompLieHom_apply,
    algEquivSelf_derivationComp_apply, BialgHom.coe_toAlgHom, BialgHom.cocharacter_id_single,
    AddMonoidHom.coe_toMultiplicative, Function.comp_apply, toAdd_ofAdd,
    Finsupp.applyAddHom_apply]
  rw [← LaurentPolynomial.T]
  by_cases h : i = j
  · subst j
    simp only [Finsupp.single_eq_same, MultiplicativeGroup.tangentLinearEquiv_symm_apply_T,
      one_smul, ↓reduceIte]
  · simp only [Finsupp.single_eq_of_ne h, LaurentPolynomial.T_zero,
      Derivation.map_one_eq_zero, map_zero, h, ↓reduceIte]

private theorem tangentCoordinates_injective :
    Function.Injective (tangentCoordinates (R := R) (B := B) (I := I)) := by
  intro d e h
  apply derivation_ext
  intro i
  apply (CounitAlgebra.algEquivSelf R A B).injective
  exact congrFun h i

private theorem tangentCoordinates_surjective [Finite I] :
    Function.Surjective (tangentCoordinates (R := R) (B := B) (I := I)) := by
  classical
  let := Fintype.ofFinite I
  intro b
  refine ⟨∑ i, b i • coordinateDerivation i, ?_⟩
  ext j
  simp [map_sum, tangentCoordinates_coordinateDerivation]

/-- Evaluation on the coordinate monomials identifies the tangent space of a finite split
torus with the corresponding power of any coefficient algebra. -/
def tangentLinearEquiv [Finite I] : Derivation R A C ≃ₗ[B] (I → B) :=
  LinearEquiv.ofBijective tangentCoordinates
    ⟨tangentCoordinates_injective, tangentCoordinates_surjective⟩

/-- The tangent coordinates are the values on the standard character monomials. -/
@[simp]
theorem tangentLinearEquiv_apply [Finite I] (d : Derivation R A C) (i : I) :
    tangentLinearEquiv d i =
      CounitAlgebra.algEquivSelf R A B
        (d (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i 1)) 1)) := by
  exact congrFun (LinearEquiv.ofBijective_apply tangentCoordinates
    (hf := ⟨tangentCoordinates_injective, tangentCoordinates_surjective⟩) d) i

/-- The tangent basis of a split torus, indexed by its coordinate cocharacters. -/
def tangentBasis [Finite I] : Module.Basis I B (Derivation R A C) :=
  Module.Basis.ofEquivFun tangentLinearEquiv

/-- The tangent basis has the coordinate equivalence as its function-valued representation. -/
@[simp]
theorem tangentBasis_equivFun [Finite I] :
    (tangentBasis (R := R) (B := B) (I := I)).equivFun = tangentLinearEquiv :=
  Module.Basis.equivFun_ofEquivFun _

/-- A tangent basis coefficient is the value on the corresponding character monomial. -/
@[simp]
theorem tangentBasis_repr_apply [Finite I] (d : Derivation R A C) (i : I) :
    (tangentBasis (R := R) (B := B)).repr d i =
      CounitAlgebra.algEquivSelf R A B
        (d (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i 1)) 1)) := by
  rw [← Module.Basis.equivFun_apply, tangentBasis_equivFun, tangentLinearEquiv_apply]

/-- The tangent basis vector of index `i` is the differential of the corresponding
coordinate cocharacter, evaluated on the Laurent tangent vector with value one on `T`. -/
theorem tangentBasis_apply [Finite I] (i : I) :
    tangentBasis (R := R) (B := B) i =
      derivationCompLieHom
        ((BialgHom.id R A).cocharacter (Finsupp.applyAddHom i).toMultiplicative)
        ((MultiplicativeGroup.tangentLinearEquiv (R := R) (B := B)).symm 1) := by
  classical
  apply (tangentLinearEquiv (R := R) (B := B) (I := I)).injective
  simp only [tangentBasis, Module.Basis.coe_ofEquivFun, LinearEquiv.apply_symm_apply]
  ext j
  rw [tangentLinearEquiv_apply]
  simpa only [coordinateDerivation, tangentCoordinates_apply, Pi.single_apply, eq_comm] using
    (tangentCoordinates_coordinateDerivation (R := R) (B := B) i j).symm

/-- Every tangent vector is the sum of its coordinate values times the coordinate
cocharacter differentials. -/
theorem tangentLinearEquiv_symm_apply [Fintype I] (b : I → B) :
    (tangentLinearEquiv (R := R) (B := B)).symm b =
      ∑ i, b i • tangentBasis (R := R) (B := B) i := by
  simpa only [tangentBasis_equivFun] using
    (tangentBasis (R := R) (B := B) (I := I)).equivFun_symm_apply b

variable {H : Type*} [CommRing H] [Bialgebra R H]

/-- A split-torus differential sends a coordinate tangent vector to the differential of
the corresponding cocharacter of its target. -/
theorem derivationCompLieHom_tangentBasis [Finite I] (π : H →ₐc[R] A) (i : I) :
    derivationCompLieHom (B := B) π
        (tangentBasis (R := R) (B := B) i) =
      derivationCompLieHom (π.cocharacter (Finsupp.applyAddHom i).toMultiplicative)
        ((MultiplicativeGroup.tangentLinearEquiv (R := R) (B := B)).symm 1) := by
  rw [tangentBasis_apply, ← LieHom.comp_apply, ← derivationCompLieHom_comp,
    BialgHom.cocharacter_id_comp]

/-- The tangent image of a finite split torus is the span of the differentials of its
coordinate cocharacters. The map from the torus need not be an immersion. -/
theorem range_derivationCompLieHom [Finite I] (π : H →ₐc[R] A) :
    LinearMap.range (derivationCompLieHom (B := B) π).toLinearMap =
      Submodule.span B (Set.range fun i : I ↦
        derivationCompLieHom (π.cocharacter (Finsupp.applyAddHom i).toMultiplicative)
          ((MultiplicativeGroup.tangentLinearEquiv (R := R) (B := B)).symm 1)) := by
  have h := congrArg (Submodule.map (derivationCompLieHom (B := B) π).toLinearMap)
    (tangentBasis (R := R) (B := B) (I := I)).span_eq
  rw [Submodule.map_span, Submodule.map_top] at h
  rw [← h, ← Set.range_comp']
  simp only [LieHom.coe_toLinearMap, derivationCompLieHom_tangentBasis]

end

end TauCeti.SplitTorus
