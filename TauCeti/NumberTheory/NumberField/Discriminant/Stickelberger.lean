/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import TauCeti.LinearAlgebra.Matrix.LeibnizPart

/-!
# Stickelberger's congruence

The discriminant of a number field is congruent to `0` or `1` modulo `4`.

Let `b` be a `ℚ`-basis of the number field `K` consisting of algebraic integers, and let `M` be the
matrix of its images under the embeddings of `K` into an algebraic closure `E` of `ℚ`, so that
`disc b = (det M) ^ 2`. Splitting the Leibniz expansion of `det M` into the sums `P` and `N` over
the even and the odd permutations gives `disc b = (P + N) ^ 2 - 4 * (P * N)`. An automorphism of
`E` permutes the embeddings, hence the columns of `M`, and so fixes `P + N` and `P * N`. Both are
algebraic integers, so both are rational integers, and `disc b` is a square minus four times an
integer. Taking `b` to be an integral basis gives the congruence for `NumberField.discr K`.

The congruence concerns the absolute discriminant only: the relative discriminant of an extension
of Dedekind domains is an ideal, and has no residue modulo `4`.

## Main results

* `TauCeti.NumberField.exists_discr_eq_sq_sub_four_mul_of_isIntegral`: the discriminant of a
  `ℚ`-basis of algebraic integers has the form `s ^ 2 - 4 * p` with `s p : ℤ`.
* `TauCeti.NumberField.exists_discr_eq_sq_sub_four_mul`: the same for the discriminant of `K`.
* `TauCeti.NumberField.discr_emod_four_eq_zero_or_one`: **Stickelberger's congruence**,
  `NumberField.discr K % 4 = 0 ∨ NumberField.discr K % 4 = 1`.

## References

* L. Stickelberger, *Über eine neue Eigenschaft der Diskriminanten algebraischer Zahlkörper*,
  Verhandlungen des ersten Internationalen Mathematiker-Kongresses (1897).
* W. Narkiewicz, *Elementary and Analytic Theory of Algebraic Numbers*, Chapter 4.
-/

public section

open Matrix Module
open scoped NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **The discriminant of a basis of algebraic integers is a square minus four times an
integer.** For a `ℚ`-basis `b` of a number field consisting of algebraic integers, there are
`s p : ℤ` with `Algebra.discr ℚ b = s ^ 2 - 4 * p`; here `s` and `p` are the sum and the product of
the even and the odd parts of the Leibniz expansion of the embedding determinant. -/
theorem exists_discr_eq_sq_sub_four_mul_of_isIntegral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℚ K) (hb : ∀ i, IsIntegral ℤ (b i)) :
    ∃ s p : ℤ, Algebra.discr ℚ b = s ^ 2 - 4 * p := by
  let E := AlgebraicClosure ℚ
  let e : ι ≃ (K →ₐ[ℚ] E) :=
    Fintype.equivOfCardEq ((AlgHom.card ℚ K E).trans (finrank_eq_card_basis b)).symm
  set M := Algebra.embeddingsMatrixReindex ℚ E b e with hM
  -- An algebraic integer of `E` fixed by every automorphism is a rational integer.
  have hZ {x : E} (hfix : ∀ τ : Gal(E/ℚ), τ x = x) (hx : IsIntegral ℤ x) :
      ∃ z : ℤ, algebraMap ℤ E z = x := by
    obtain ⟨q, rfl⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed x).mpr hfix
    obtain ⟨z, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp <|
      (isIntegral_algHom_iff ((Algebra.ofId ℚ E).restrictScalars ℤ)
        (algebraMap ℚ E).injective).mp hx
    exact ⟨z, IsScalarTower.algebraMap_apply ℤ ℚ E z⟩
  -- An automorphism `τ` of `E` acts on `M` by permuting its columns, through `φ ↦ τ ∘ φ` on the
  -- embeddings.
  have hmap (τ : Gal(E/ℚ)) :
      M.map τ = M.submatrix id (e.trans ((AlgEquiv.arrowCongr AlgEquiv.refl τ).trans e.symm)) := by
    ext i j
    simp [M, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix]
  have hint (s : ℤˣ) : IsIntegral ℤ (M.leibnizPart s) := by
    rw [leibnizPart_def]
    refine IsIntegral.sum _ fun σ _ ↦ IsIntegral.prod _ fun i _ ↦ ?_
    exact (hb (σ i)).map ((e i).restrictScalars ℤ)
  obtain ⟨s, hs⟩ := hZ (x := M.permanent)
    (fun τ ↦ by
      rw [← leibnizPart_one_add_leibnizPart_neg_one, map_add, ← leibnizPart_map τ,
        ← leibnizPart_map τ, leibnizPart_one_add_leibnizPart_neg_one, hmap τ,
        permanent_permute_rows, leibnizPart_one_add_leibnizPart_neg_one])
    (by rw [← leibnizPart_one_add_leibnizPart_neg_one]; exact (hint 1).add (hint (-1)))
  obtain ⟨p, hp⟩ := hZ (x := M.leibnizPart 1 * M.leibnizPart (-1))
    (fun τ ↦ by
      rw [map_mul, ← leibnizPart_map τ, ← leibnizPart_map τ, hmap τ,
        leibnizPart_one_mul_leibnizPart_neg_one_submatrix_right])
    ((hint 1).mul (hint (-1)))
  refine ⟨s, p, (algebraMap ℚ E).injective ?_⟩
  rw [Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ E b e, ← hM,
    det_sq_eq_permanent_sq_sub_four_mul, ← hs, ← hp]
  simp only [map_sub, map_mul, map_pow, map_ofNat, eq_intCast, map_intCast]

/-- **The discriminant of a number field is a square minus four times an integer.** -/
theorem exists_discr_eq_sq_sub_four_mul (K : Type*) [Field K] [NumberField K] :
    ∃ s p : ℤ, NumberField.discr K = s ^ 2 - 4 * p := by
  obtain ⟨s, p, h⟩ :=
    exists_discr_eq_sq_sub_four_mul_of_isIntegral (NumberField.integralBasis K) fun i ↦ by
      rw [NumberField.integralBasis_apply]
      exact NumberField.RingOfIntegers.isIntegral_coe _
  exact ⟨s, p, by exact_mod_cast (NumberField.coe_discr K).trans h⟩

/-- **Stickelberger's congruence.** The discriminant of a number field is congruent to `0` or `1`
modulo `4`. -/
theorem discr_emod_four_eq_zero_or_one (K : Type*) [Field K] [NumberField K] :
    NumberField.discr K % 4 = 0 ∨ NumberField.discr K % 4 = 1 := by
  obtain ⟨s, p, h⟩ := exists_discr_eq_sq_sub_four_mul K
  have hs := Int.sq_emod_four s
  rw [h]
  generalize s ^ 2 = t at hs
  omega

end TauCeti.NumberField

end
