/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Basis
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Galois.Basic
public import TauCeti.FieldTheory.RatFunc.Galois

/-!
# The fixed field of the coefficient action on a Weierstrass function field

For a Galois extension `K/F`, the functions on `W_K` fixed by every coefficient automorphism are
exactly the functions defined over `F`. This applies to infinite Galois extensions, including the
separable closure over an imperfect field. Neither ellipticity nor perfectness is required.

The basis `{1, y}` over `K(x)` separates a function into two rational functions; coefficient
automorphisms act on those two coefficients and fix the basis. This supplies the fixed-field
calculation needed to descend equivariant function-field maps.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2 and III.6.
-/

public section

open Polynomial
open scoped WeierstrassCurve RatFunc nonZeroDivisors

namespace WeierstrassCurve

variable {F K : Type*} [Field F] [Field K] [Algebra F K] (W : WeierstrassCurve F)

/-- The coefficient action on the Weierstrass function field restricts to the coefficient action
on its rational-function subfield. -/
@[simp]
theorem functionFieldGaloisAction_algebraMap_ratFunc (σ : K ≃ₐ[F] K) (z : RatFunc K) :
    functionFieldGaloisAction W σ (algebraMap (RatFunc K) (W⁄K).toAffine.FunctionField z) =
      algebraMap (RatFunc K) (W⁄K).toAffine.FunctionField
        (RatFunc.mapRingHom (Polynomial.mapRingHom σ.toRingHom)
          (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
            (Polynomial.map_injective _ σ.injective)) z) := by
  have hpoly (p : K[X]) : functionFieldGaloisAction W σ
      (algebraMap K[X] (W⁄K).toAffine.FunctionField p) =
      algebraMap K[X] (W⁄K).toAffine.FunctionField (p.map σ.toRingHom) := by
    simp only [IsScalarTower.algebraMap_apply K[X] (W⁄K).toAffine.CoordinateRing
      (W⁄K).toAffine.FunctionField, AdjoinRoot.algebraMap_eq,
      functionFieldGaloisAction_algebraMap_coordinateRing, coordinateRingGaloisAction_of]
    rfl
  induction z using RatFunc.induction_on with
  | f p q _ =>
    rw [RatFunc.coe_mapRingHom_eq_coe_map, RatFunc.map_apply_div]
    simp only [map_div₀, ← IsScalarTower.algebraMap_apply, hpoly, Polynomial.coe_mapRingHom]

/-- The coefficients of a function in the basis `{1, y}` transform by the coefficient action on
rational functions. -/
theorem functionFieldGaloisAction_basis_repr (σ : K ≃ₐ[F] K)
    (z : (W⁄K).toAffine.FunctionField) (i : Fin 2) :
    (Affine.FunctionField.basis (W⁄K).toAffine (RatFunc K)).repr
        (functionFieldGaloisAction W σ z) i =
      RatFunc.mapRingHom (Polynomial.mapRingHom σ.toRingHom)
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
          (Polynomial.map_injective _ σ.injective))
        ((Affine.FunctionField.basis (W⁄K).toAffine (RatFunc K)).repr z i) := by
  let b := Affine.FunctionField.basis (W⁄K).toAffine (RatFunc K)
  have hfixed (j : Fin 2) : functionFieldGaloisAction W σ (b j) = b j := by
    fin_cases j <;> simp [b]
  have hexp : functionFieldGaloisAction W σ z = ∑ j : Fin 2,
      RatFunc.mapRingHom (Polynomial.mapRingHom σ.toRingHom)
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
          (Polynomial.map_injective _ σ.injective)) (b.repr z j) • b j := by
    conv_lhs => rw [← b.sum_repr z, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Algebra.smul_def, map_mul, functionFieldGaloisAction_algebraMap_ratFunc, hfixed]
  have hrepr := congrArg (fun u ↦ b.repr u i) hexp
  fin_cases i <;> simpa [Module.Basis.repr_self] using hrepr

/-- The functions fixed by every coefficient automorphism of a Galois extension are exactly the
images of ground-field functions. This holds for infinite extensions as well. -/
theorem mem_range_functionFieldMap_iff_fixed [IsGalois F K]
    (z : (W⁄K).toAffine.FunctionField) :
    z ∈ Set.range (Affine.FunctionField.map W.toAffine (algebraMap F K)) ↔
      ∀ σ : K ≃ₐ[F] K, functionFieldGaloisAction W σ z = z := by
  constructor
  · rintro ⟨w, rfl⟩ σ
    exact functionFieldGaloisAction_map_algebraMap W σ w
  · intro hz
    let b := Affine.FunctionField.basis (W⁄K).toAffine (RatFunc K)
    have hcoeff (i : Fin 2) : b.repr z i ∈ Set.range
        (RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap F K))
          (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
            (Polynomial.map_injective _ (algebraMap F K).injective))) := by
      apply (RatFunc.mem_range_mapRingHom_iff_fixed (b.repr z i)).mpr
      intro σ
      rw [← functionFieldGaloisAction_basis_repr, hz σ]
    choose r hr using hcoeff
    let bF := Affine.FunctionField.basis W.toAffine (RatFunc F)
    have hb (i : Fin 2) :
        Affine.FunctionField.map W.toAffine (algebraMap F K) (bF i) = b i := by
      -- The named basis and coordinate lemmas reduce both cases. The final reflexivity
      -- identifies `W.toAffine.map (algebraMap F K)` with `(W⁄K).toAffine`, the same base change.
      fin_cases i <;> simp [b, bF] <;> rfl
    refine ⟨∑ i : Fin 2, r i • bF i, ?_⟩
    simp only [map_sum, Algebra.smul_def, map_mul,
      Affine.FunctionField.map_algebraMap_ratFunc, hr, hb]
    exact b.sum_repr z

end WeierstrassCurve

end
