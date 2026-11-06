/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Node.Cotangent.Basic
import Mathlib.RingTheory.TensorProduct.Quotient
import TauCeti.RingTheory.Spectrum.Prime.Point

/-!
# Relative differentials along an unramified singular locus

Let `A` be an essentially finite type algebra over an arbitrary commutative ring `R`. Suppose
that the closed subscheme defined by `Fitt₁(Ω[A⁄R])` is unramified over `R`. Then every field-valued
fibre of the relative differentials has dimension at most two, and `Fitt₂(Ω[A⁄R]) = A`.
In particular, at a singular point of a nodal relative curve the relative differentials need
exactly two generators. This is the rank condition for presenting a nodal relative curve as a
hypersurface in a smooth relative surface.

The base need not be Noetherian, reduced, or a field. The assertions concern relative
differentials, not the absolute Zariski cotangent space of `A`: a node in a family can have a
higher-dimensional absolute tangent space because the base contributes tangent directions.

The proof reduces to the field-base theorem
`TauCeti.finrank_tensor_kaehlerDifferential_eq_two`. Both differentials and their Fitting ideals
commute with base change, and the singular subscheme remains unramified after base change to a
residue field of `R`.

## Main results

* `TauCeti.finrank_tensor_kaehlerDifferential_le_two`: every field-valued fibre has dimension
  at most two.
* `TauCeti.fittingIdeal_kaehlerDifferential_two_eq_top`: the second Fitting ideal is the unit ideal.

## References

* [Stacks Project, Lemma 53.20.1, Tag 0C58](https://stacks.math.columbia.edu/tag/0C58): the
  singular-locus criterion and local structure of families of nodal curves.
-/

public section

noncomputable section

open Module TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace TauCeti

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [Algebra.EssFiniteType R A]
  [Algebra.FormallyUnramified R (A ⧸ fittingIdeal A Ω[A⁄R] 1)]

/-- If the first Fitting ideal of the relative differentials cuts out an unramified subscheme,
then every field-valued fibre of the differentials has dimension at most two. -/
theorem finrank_tensor_kaehlerDifferential_le_two {L : Type*} [Field L] [Algebra A L] :
    finrank L (L ⊗[A] Ω[A⁄R]) ≤ 2 := by
  let : Algebra R L := ((algebraMap A L).comp (algebraMap R A)).toAlgebra
  have : IsScalarTower R A L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  -- Pass to the fibre over the image of the field-valued point in `Spec R`.
  let p := RingHom.ker (algebraMap R L)
  have : p.IsPrime := RingHom.ker_isPrime _
  obtain ⟨_, _⟩ := Ideal.exists_algebra_residueField_isScalarTower (F := L) p rfl
  let K := p.ResidueField
  let B := K ⊗[R] A
  let μ : B →ₐ[K] L := Algebra.TensorProduct.lift (Algebra.ofId K L)
    (IsScalarTower.toAlgHom R A L) (fun _ _ ↦ .all _ _)
  let : Algebra B L := μ.toRingHom.toAlgebra
  have : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq (R := A) (S := B) (A := L)
    fun a ↦ by
      rw [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.right_algebraMap_apply]
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, μ,
        Algebra.TensorProduct.lift_tmul (R := R) (S := K), map_one, one_mul,
        IsScalarTower.toAlgHom_apply]
  have hfit (k : ℕ) : fittingIdeal B Ω[B⁄K] k =
      (fittingIdeal A Ω[A⁄R] k).map (algebraMap A B) :=
    fittingIdeal_kaehlerDifferential_eq_map R K A B k
  have : Algebra.FormallyUnramified K (B ⧸ fittingIdeal B Ω[B⁄K] 1) := by
    rw [hfit 1]
    exact Algebra.FormallyUnramified.of_equiv
      (Algebra.TensorProduct.tensorQuotientEquiv (R := R) K A K
        (fittingIdeal A Ω[A⁄R] 1))
  by_cases h : fittingIdeal A Ω[A⁄R] 1 ≤ RingHom.ker (algebraMap A L)
  · -- At a singular point the field-base theorem gives dimension exactly two. Compare the
    -- two fibres through their Fitting ideals, avoiding choices of tensor associativity maps.
    have hB : fittingIdeal B Ω[B⁄K] 1 ≤ RingHom.ker (algebraMap B L) := by
      rw [hfit, Ideal.map_le_iff_le_comap, RingHom.comap_ker,
        ← IsScalarTower.algebraMap_eq A B L]
      exact h
    have h2 := finrank_tensor_kaehlerDifferential_eq_two hB
    have hcomp (k : ℕ) :
        k < finrank L (L ⊗[B] Ω[B⁄K]) ↔ k < finrank L (L ⊗[A] Ω[A⁄R]) := by
      rw [← fittingIdeal_map_eq_bot_iff_lt_finrank, hfit,
        Ideal.map_map, ← IsScalarTower.algebraMap_eq A B L,
        fittingIdeal_map_eq_bot_iff_lt_finrank]
    have := (hcomp 2).not.mp (by omega : ¬ 2 < finrank L (L ⊗[B] Ω[B⁄K]))
    omega
  · -- Away from the first Fitting locus the dimension is at most one.
    have := (fittingIdeal_map_eq_bot_iff_lt_finrank L 1 (R := A) (M := Ω[A⁄R]))
    rw [Ideal.map_eq_bot_iff_le_ker] at this
    have := this.not.mp h
    omega

/-- If the first Fitting ideal of the relative differentials has unramified quotient over the
base, then their second Fitting ideal is the unit ideal. Equivalently, the relative differentials
are locally generated by at most two elements. -/
@[simp]
theorem fittingIdeal_kaehlerDifferential_two_eq_top : fittingIdeal A Ω[A⁄R] 2 = ⊤ := by
  by_contra h
  obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal (fittingIdeal A Ω[A⁄R] 2) h
  have := (fittingIdeal_le_iff_lt_finrank p 2).mp hle
  have := finrank_tensor_kaehlerDifferential_le_two (R := R) (A := A) (L := p.ResidueField)
  omega

end TauCeti
