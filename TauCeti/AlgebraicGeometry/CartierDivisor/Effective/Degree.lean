/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Effective.Difference
public import TauCeti.AlgebraicGeometry.CartierDivisor.Effective.IdealSheaf
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Degree.EulerCharacteristic
import TauCeti.AlgebraicGeometry.Noetherian

/-!
# Additivity of degree on integral proper curves

Let `X` be an integral scheme, proper over a field `k` with fibres of dimension at most one, such
that `H⁰(X, 𝒪_X)` and `H¹(X, 𝒪_X)` are finite-dimensional over `k`. The curve `X` may be singular.
The Euler-characteristic degree `deg L = χ(L) - χ(𝒪_X)` of line bundles on `X` is additive under
tensor product:

`deg (L ⊗ M) = deg L + deg M`.

For an effective Cartier divisor `D` on `X`, the ideal sheaf `𝒪_X(-D) ⊆ 𝒪_X`
(`Scheme.CartierDivisor.IsEffective.sectionsIdealSheaf`) cuts out a closed subscheme finite over
`k`, and the exact sequence `0 ⟶ L(-D) ⟶ L ⟶ L|_D ⟶ 0` shows that `deg 𝒪_X(D) = dim_k Γ(D, 𝒪_D)` and
that twisting by `𝒪_X(D)` adds this degree, for every line bundle `L` with finite-dimensional
`H⁰` and `H¹`. Every line bundle on `X` is `𝒪_X(E) ⊗ 𝒪_X(F)⁻¹` with `E` and `F` effective
(`Scheme.CartierDivisor.exists_isEffective_toLineBundleClass_mul_inv_eq`), so `H⁰` and `H¹` of
every line bundle are finite-dimensional, and additivity follows from additivity along twists by
effective divisors.

When the codimension-one local rings of `X` are discrete valuation rings, additivity is
`LineBundleClass.eulerDegree_mul`, proved through Weil divisors. Integral curves with singular
points, such as the reduced irreducible components of the special fibre of a regular model of a
curve over a discrete valuation ring, are covered here.

## Main results

* `Scheme.CartierDivisor.IsEffective.eulerDegree_toLineBundleClass`: the degree of `𝒪_X(D)` for
  an effective Cartier divisor `D` is `dim_k Γ(D, 𝒪_D)`.
* `InvertibleSheaf.finiteDimensional_cohomology_of_isIntegral`: `H⁰` and `H¹` of every line
  bundle are finite-dimensional.
* `LineBundleClass.eulerDegree_mul_of_isIntegral` and
  `LineBundleClass.eulerDegree_inv_of_isIntegral`: the degree is additive on the Picard group.

## References

* [The Stacks Project, Section 33.44](https://stacks.math.columbia.edu/tag/0AYQ), *Degrees on
  curves*: the degree of invertible modules on a proper curve over a field is additive, proved
  by writing invertible modules in terms of effective Cartier divisors.
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Section 7.3, on the degree of divisors and
  invertible sheaves on projective curves.
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules (finiteDimensional_cohomology_congr)
open TauCeti.AlgebraicGeometry.Scheme.Modules (Cohomology)

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] [RelativeDimensionLE 1 (X ↘ Spec (.of k))]
  [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial X).obj 0)]
  [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial X).obj 1)]

namespace Scheme.CartierDivisor

variable {D : CartierDivisor X}

/-- **The degree of an effective divisor on a curve.** Let `X` be an integral scheme, proper over
`k` with fibres of dimension at most one and with finite-dimensional `H⁰(X, 𝒪_X)` and
`H¹(X, 𝒪_X)`. For an effective Cartier divisor `D` on `X`, the line bundle `𝒪_X(D)` has degree
`dim_k Γ(D, 𝒪_D)`, the rank of the finite morphism `D ⟶ Spec k` from the closed subscheme cut out
by `𝒪_X(-D)`. -/
theorem IsEffective.eulerDegree_toLineBundleClass (hD : D.IsEffective) (s : Spec (.of k)) :
    LineBundleClass.eulerDegree k D.toLineBundleClass =
      (hD.sectionsIdealSheaf.subschemeι ≫ X ↘ Spec (.of k)).finrank s := by
  have hI := hD.isEffectiveCartier_sectionsIdealSheaf
  have : IsFinite (hD.sectionsIdealSheaf.subschemeι ≫ X ↘ Spec (.of k)) :=
    hI.isFinite_subschemeι_comp
  rw [← inv_inv D.toLineBundleClass, ← hD.mk_toInvertibleSheaf_sectionsIdealSheaf]
  exact hI.eulerDegree_inv_mk_toInvertibleSheaf k _ s

/-- Twisting a line bundle with finite-dimensional `H⁰` and `H¹` by an effective divisor adds the
degree of the divisor. -/
private theorem IsEffective.eulerDegree_mk_mul_toLineBundleClass (hD : D.IsEffective)
    (L : InvertibleSheaf X) [FiniteDimensional k (Cohomology L.obj 0)]
    [FiniteDimensional k (Cohomology L.obj 1)] :
    LineBundleClass.eulerDegree k (LineBundleClass.mk L * D.toLineBundleClass) =
      L.eulerDegree k + LineBundleClass.eulerDegree k D.toLineBundleClass := by
  have hI := hD.isEffectiveCartier_sectionsIdealSheaf
  have : IsFinite (hD.sectionsIdealSheaf.subschemeι ≫ X ↘ Spec (.of k)) :=
    hI.isFinite_subschemeι_comp
  rw [← inv_inv D.toLineBundleClass, ← hD.mk_toInvertibleSheaf_sectionsIdealSheaf,
    hI.eulerDegree_mk_mul_inv_mk_toInvertibleSheaf k _ L,
    hI.eulerDegree_inv_mk_toInvertibleSheaf k _ default,
    hI.eulerDegree_toInvertibleSheaf k _ default, sub_neg_eq_add]

omit [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial X).obj 0)]
  [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial X).obj 1)] in
/-- Twisting by an effective divisor does not change whether all line bundles in a class have
finite-dimensional `H⁰` and `H¹`. -/
private theorem IsEffective.forall_finiteDimensional_mul_toLineBundleClass_iff
    (hD : D.IsEffective) (a : LineBundleClass X) :
    (∀ L : InvertibleSheaf X, LineBundleClass.mk L = a * D.toLineBundleClass →
        ∀ i < 2, FiniteDimensional k (Cohomology L.obj i)) ↔
      ∀ L : InvertibleSheaf X, LineBundleClass.mk L = a →
        ∀ i < 2, FiniteDimensional k (Cohomology L.obj i) := by
  have hI := hD.isEffectiveCartier_sectionsIdealSheaf
  have : IsFinite (hD.sectionsIdealSheaf.subschemeι ≫ X ↘ Spec (.of k)) :=
    hI.isFinite_subschemeι_comp
  -- `L ⊗ 𝒪_X(-D)` has class `[L] [𝒪_X(D)]⁻¹`, and its cohomology is finite exactly when that of
  -- `L` is (`finiteDimensional_cohomology_tensor_sheaf_iff`).
  have key (L M : InvertibleSheaf X)
      (h : LineBundleClass.mk L = LineBundleClass.mk M * D.toLineBundleClass⁻¹) (i : ℕ) :
      FiniteDimensional k (Cohomology L.obj i) ↔
        FiniteDimensional k (Cohomology (M.obj ⊗ hD.sectionsIdealSheaf.sheaf) i) := by
    rw [← hD.mk_toInvertibleSheaf_sectionsIdealSheaf, ← LineBundleClass.mk_tensorProduct,
      LineBundleClass.mk_eq_mk_iff] at h
    obtain ⟨e⟩ := h
    exact finiteDimensional_cohomology_congr k
      (e ≪≫ InvertibleSheaf.tensorProductObjIso M hI.toInvertibleSheaf ≪≫
        eqToIso (by rw [Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf_obj])) i
  -- Twisting a line bundle `M` by `𝒪_X(-D)` preserves finiteness of `H⁰` and `H¹`.
  have hiff (M : InvertibleSheaf X) :
      (∀ i < 2, FiniteDimensional k (Cohomology (M.obj ⊗ hD.sectionsIdealSheaf.sheaf) i)) ↔
        ∀ i < 2, FiniteDimensional k (Cohomology M.obj i) := by
    have h := Scheme.IdealSheafData.finiteDimensional_cohomology_tensor_sheaf_iff
      hD.sectionsIdealSheaf (k := k) (E := (InvertibleSheaf.toFixedRankOne X).obj M)
    rwa [InvertibleSheaf.toFixedRankOne_obj_obj, ObjectProperty.ιOfLE_obj_obj] at h
  have hL (L : InvertibleSheaf X) :
      LineBundleClass.mk (InvertibleSheaf.tensorProduct L hI.toInvertibleSheaf) =
        LineBundleClass.mk L * D.toLineBundleClass⁻¹ := by
    rw [LineBundleClass.mk_tensorProduct, hD.mk_toInvertibleSheaf_sectionsIdealSheaf]
  constructor
  · -- `L` with class `a` is `M ⊗ 𝒪_X(-D)` for any `M` of class `a [𝒪_X(D)]`.
    intro h L hLa i hi
    obtain ⟨M, hM⟩ := LineBundleClass.mk_surjective (a * D.toLineBundleClass)
    refine (key L M (by rw [hM, hLa, mul_inv_cancel_right]) i).mpr ?_
    exact (hiff M).mpr (h M hM) i hi
  · -- For `L` of class `a [𝒪_X(D)]`, the twist `L ⊗ 𝒪_X(-D)` has class `a`.
    intro h L hLa i hi
    refine (hiff L).mp (fun j hj ↦ ?_) i hi
    exact (key _ L (hL L) j).mp (h _ (by rw [hL, hLa, mul_inv_cancel_right]) j hj)

end Scheme.CartierDivisor

/-- **Line bundles on a curve have finite-dimensional cohomology.** Let `X` be an integral scheme,
proper over `k` with fibres of dimension at most one, such that `H⁰(X, 𝒪_X)` and `H¹(X, 𝒪_X)` are
finite-dimensional. Then `H⁰(X, L)` and `H¹(X, L)` are finite-dimensional for every line bundle
`L` on `X`. -/
theorem InvertibleSheaf.finiteDimensional_cohomology_of_isIntegral (L : InvertibleSheaf X)
    {i : ℕ} (hi : i < 2) : FiniteDimensional k (Cohomology L.obj i) := by
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
  obtain ⟨E, F, hE, hF, hEF⟩ :=
    Scheme.CartierDivisor.exists_isEffective_toLineBundleClass_mul_inv_eq
    (coheight_le_of_relativeDimensionLE_of_field (d := 1) (X ↘ Spec (.of k)))
    (LineBundleClass.mk L)
  -- The trivial class has finite cohomology, and twisting by `𝒪_X(F)` and `𝒪_X(E)` keeps it so.
  have h₁ : ∀ M : InvertibleSheaf X, LineBundleClass.mk M = 1 →
      ∀ i < 2, FiniteDimensional k (Cohomology M.obj i) := fun M hM i hi ↦ by
    rw [← LineBundleClass.mk_trivial, LineBundleClass.mk_eq_mk_iff] at hM
    obtain ⟨e⟩ := hM
    refine (finiteDimensional_cohomology_congr k e i).mpr ?_
    interval_cases i <;> infer_instance
  have h₂ := (hF.forall_finiteDimensional_mul_toLineBundleClass_iff k
    F.toLineBundleClass⁻¹).mp (by rwa [inv_mul_cancel])
  have h₃ := (hE.forall_finiteDimensional_mul_toLineBundleClass_iff k
    F.toLineBundleClass⁻¹).mpr h₂
  exact h₃ L (by rw [← hEF, mul_comm]) i hi

namespace LineBundleClass

/-- Twisting by an effective divisor adds its degree, for every line-bundle class. -/
private theorem eulerDegree_mul_toLineBundleClass_of_isEffective {D : Scheme.CartierDivisor X}
    (hD : D.IsEffective) (a : LineBundleClass X) :
    eulerDegree k (a * D.toLineBundleClass) =
      eulerDegree k a + eulerDegree k D.toLineBundleClass := by
  obtain ⟨L, rfl⟩ := mk_surjective a
  have := L.finiteDimensional_cohomology_of_isIntegral k (i := 0) (by norm_num)
  have := L.finiteDimensional_cohomology_of_isIntegral k (i := 1) (by norm_num)
  rw [hD.eulerDegree_mk_mul_toLineBundleClass k L, eulerDegree_mk]

/-- **Additivity of degree on an integral proper curve.** Let `X` be an integral scheme, proper
over `k` with fibres of dimension at most one, such that `H⁰(X, 𝒪_X)` and `H¹(X, 𝒪_X)` are
finite-dimensional. Then the Euler-characteristic degree is additive on line-bundle classes. The
curve `X` may be singular. -/
@[simp]
theorem eulerDegree_mul_of_isIntegral (a b : LineBundleClass X) :
    eulerDegree k (a * b) = eulerDegree k a + eulerDegree k b := by
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
  obtain ⟨E, F, hE, hF, rfl⟩ :=
    Scheme.CartierDivisor.exists_isEffective_toLineBundleClass_mul_inv_eq
    (coheight_le_of_relativeDimensionLE_of_field (d := 1) (X ↘ Spec (.of k))) b
  -- Twisting by `𝒪_X(F)⁻¹` subtracts the degree of `𝒪_X(F)`.
  have hsub (c : LineBundleClass X) :
      eulerDegree k (c * F.toLineBundleClass⁻¹) =
        eulerDegree k c - eulerDegree k F.toLineBundleClass := by
    have h := eulerDegree_mul_toLineBundleClass_of_isEffective k hF (c * F.toLineBundleClass⁻¹)
    rw [inv_mul_cancel_right] at h
    linarith
  have h := eulerDegree_mul_toLineBundleClass_of_isEffective k hE a
  have h₁ := eulerDegree_mul_toLineBundleClass_of_isEffective k hE 1
  rw [← mul_assoc, hsub, hsub, h, ← one_mul E.toLineBundleClass, h₁, eulerDegree_one]
  ring

/-- The inverse class has the opposite degree on an integral proper curve over `k` with
finite-dimensional `H⁰(X, 𝒪_X)` and `H¹(X, 𝒪_X)`. -/
@[simp]
theorem eulerDegree_inv_of_isIntegral (a : LineBundleClass X) :
    eulerDegree k a⁻¹ = -eulerDegree k a := by
  have h := eulerDegree_mul_of_isIntegral k a⁻¹ a
  rw [inv_mul_cancel, eulerDegree_one] at h
  linarith

end LineBundleClass

end

end AlgebraicGeometry

end TauCeti
