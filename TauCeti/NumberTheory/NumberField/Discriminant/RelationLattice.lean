/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import TauCeti.Analysis.InnerProductSpace.Gram.Hadamard
public import TauCeti.LinearAlgebra.Basis.ToMatrix
public import TauCeti.NumberTheory.Height.Arakelov.IntMatrix
public import TauCeti.NumberTheory.NumberField.Discriminant.OfIntegralBasis

/-!
# The lattice of integer relations among algebraic integers

Let `K` be a number field of degree `n` and `y : κ → 𝓞 K` a finite family of algebraic integers.
The integer relations `c : κ → ℤ` with `∑ a, c a • y a = 0` form a lattice `L` in the real span
of the rational relations, the `intLattice` of the kernel of
`Fintype.linearCombination ℚ (fun a ↦ (y a : K))`. This file bounds its covolume by the conjugates
of the `y a`, keeping the discriminant of `K` in the denominator.

Write `V` for the matrix with rows indexed by the family and columns by the embeddings
`σ : K →ₐ[ℚ] ℂ`, with entries `σ (y a)` (Mathlib's `Algebra.embeddingsMatrix`), and `B` for the
`n × |κ|` matrix of coordinates of the `y a` in a basis of `K`. Then `V` factors through `B` and
the embeddings matrix of the basis, whose determinant squared is the discriminant of the basis.
Hence the **Gram–discriminant identity**

  `det (Vᴴ V) = |disc b| · det (B Bᵀ)`

for every `ℚ`-basis `b` of `K`, and `det (Vᴴ V) = |disc K| · det (B Bᵀ)` with an integer matrix `B`
when `b` is a `ℤ`-basis of `𝓞 K`. In that case `L` is the lattice of integer solutions of
`B c = 0`. When the `y a` span `K` over `ℚ`, the rows of `B` are independent, so `L` has covolume
`√det (B Bᵀ) / g`, where `g ≥ 1` is the gcd of the maximal minors of `B`
(`Matrix.covolume_intLattice_ker_mulVecLin`). Combining the two,

  `covol L ≤ √(det (Vᴴ V) / |disc K|) ≤ √(∏_σ ∑_a |σ (y a)|²) / √|disc K|`,

the second step being Hadamard's inequality for the Gram matrix `Vᴴ V` of the conjugate vectors
`(σ (y a))_a`. If every `|σ (y a)|` is at most `H`, the bound becomes
`√((|κ| H²) ^ n) / √|disc K|`.

For the monomials of degree at most `d` evaluated at a tuple of algebraic integers generating `K`,
these are the relations of degree at most `d` satisfied by the tuple, and this is the covolume
estimate that Couveignes uses, together with Minkowski's second theorem, to find short polynomial
equations for a number field.

## Main results

* `Module.Basis.det_conjTranspose_mul_self_embeddingsMatrix`: the Gram–discriminant identity for a
  `ℚ`-basis `b` of `K`.
* `Module.Basis.det_conjTranspose_mul_self_embeddingsMatrix_ringOfIntegers`: the same for a
  `ℤ`-basis of `𝓞 K`, with the field discriminant.
* `Module.Basis.covolume_intLattice_ker_linearCombination`: for a spanning family and a `ℤ`-basis
  `β` of `𝓞 K`, the relation lattice has covolume `√det (B Bᵀ) / minorGcd B`, `B = β.toMatrix y`.
* `TauCeti.NumberField.covolume_intLattice_ker_linearCombination_le`,
  `TauCeti.NumberField.covolume_intLattice_ker_linearCombination_le_sqrt_prod` and
  `TauCeti.NumberField.covolume_intLattice_ker_linearCombination_le_of_norm_le`: the covolume
  bounds in terms of `det (Vᴴ V)`, of the conjugates of the `y a`, and of a uniform bound on them.

## References

* J.-M. Couveignes, *Enumerating number fields*, Ann. of Math. 192 (2020), 487–497, §3,
  pp. 493–494.
-/

public section

open Module Matrix Submodule
open scoped NumberField

namespace Module.Basis

variable {K : Type*} [Field K] [NumberField K] {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ]

open scoped Classical in
/-- **The Gram–discriminant identity.** Let `V` be the matrix of the values `σ (y a)` of a finite
family `y` in a number field `K` under the embeddings `σ : K →ₐ[ℚ] ℂ`. For every `ℚ`-basis `b` of
`K`, the determinant of `Vᴴ V` is the absolute discriminant of `b` times the Gram determinant of
the coordinate matrix of `y` in `b`. -/
theorem det_conjTranspose_mul_self_embeddingsMatrix (b : Basis ι ℚ K) (y : κ → K) :
    ((Algebra.embeddingsMatrix ℚ ℂ y)ᴴ * Algebra.embeddingsMatrix ℚ ℂ y).det =
      ((|Algebra.discr ℚ b| * (b.toMatrix y * (b.toMatrix y)ᵀ).det : ℚ) : ℂ) := by
  set B := (b.toMatrix y).map (algebraMap ℚ ℂ)
  set E := Algebra.embeddingsMatrix ℚ ℂ b
  have hB : Bᵀᴴ = B := by
    ext i a
    simp [B]
  have e : ι ≃ (K →ₐ[ℚ] ℂ) :=
    Fintype.equivOfCardEq ((AlgHom.card ℚ K ℂ).trans (finrank_eq_card_basis b)).symm
  set P := Algebra.embeddingsMatrixReindex ℚ ℂ b e
  rw [b.embeddingsMatrix_eq_transpose_mul ℂ, conjTranspose_mul, hB]
  have hP : P = E.submatrix id e := by
    simp [P, E, Algebra.embeddingsMatrixReindex]
  have hsub : (Eᴴ * B * (Bᵀ * E)).submatrix e e = Pᴴ * (B * Bᵀ) * P := by
    simp only [Matrix.mul_assoc]
    ext i j
    simp [hP, Matrix.mul_apply]
  rw [← det_submatrix_equiv_self e, hsub, det_mul, det_mul, det_conjTranspose]
  have hdisc := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ b e
  have hBB : (B * Bᵀ).det = algebraMap ℚ ℂ (b.toMatrix y * (b.toMatrix y)ᵀ).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul, transpose_map]
  have hnorm : star P.det * P.det = ((|Algebra.discr ℚ b| : ℚ) : ℂ) := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← norm_pow,
      ← hdisc]
    simp only [eq_ratCast, Complex.norm_ratCast]
    rw [← Rat.cast_abs, Complex.ofReal_ratCast]
  rw [hBB, mul_right_comm, hnorm, Rat.cast_mul, eq_ratCast]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] in
/-- The coordinates of a family of algebraic integers in the `ℚ`-basis of `K` induced by a
`ℤ`-basis `β` of `𝓞 K` are its integer coordinates in `β`. -/
private theorem toMatrix_localizationLocalization_coe (β : Basis ι ℤ (𝓞 K)) (y : κ → 𝓞 K) :
    (β.localizationLocalization ℚ (nonZeroDivisors ℤ) K).toMatrix (fun a ↦ (y a : K)) =
      (β.toMatrix y).map ((↑) : ℤ → ℚ) := by
  have h := β.toMatrix_localizationLocalization (Rₛ := ℚ) (nonZeroDivisors ℤ) (Aₛ := K) y
  rw [algebraMap_int_eq, Int.coe_castRingHom] at h
  exact h

open scoped Classical in
/-- **The Gram–discriminant identity for an integral basis.** Let `V` be the matrix of the values
`σ (y a)` of a finite family `y` of algebraic integers under the embeddings `σ : K →ₐ[ℚ] ℂ`. For
every `ℤ`-basis `β` of `𝓞 K`, the determinant of `Vᴴ V` is `|disc K|` times the Gram determinant
of the integer coordinate matrix of `y` in `β`. -/
theorem det_conjTranspose_mul_self_embeddingsMatrix_ringOfIntegers (β : Basis ι ℤ (𝓞 K))
    (y : κ → 𝓞 K) :
    ((Algebra.embeddingsMatrix ℚ ℂ fun a ↦ (y a : K))ᴴ *
        Algebra.embeddingsMatrix ℚ ℂ fun a ↦ (y a : K)).det =
      ((|NumberField.discr K| * (β.toMatrix y * (β.toMatrix y)ᵀ).det : ℤ) : ℂ) := by
  set b := β.localizationLocalization ℚ (nonZeroDivisors ℤ) K
  have hb : ⇑b = fun i ↦ algebraMap (𝓞 K) K (β i) := funext (β.localizationLocalization_apply ℚ _ K)
  have hmat : (β.toMatrix y).map ((↑) : ℤ → ℚ) * ((β.toMatrix y).map ((↑) : ℤ → ℚ))ᵀ =
      (β.toMatrix y * (β.toMatrix y)ᵀ).map ((↑) : ℤ → ℚ) :=
    (Matrix.map_mul (f := Int.castRingHom ℚ)).symm
  rw [b.det_conjTranspose_mul_self_embeddingsMatrix, toMatrix_localizationLocalization_coe, hb,
    NumberField.discr_eq_of_integralBasis, hmat, ← Int.cast_det, ← Int.cast_abs, ← Int.cast_mul,
    Rat.cast_intCast]

/-- **The covolume of the lattice of integer relations.** Let `y` be a finite family of algebraic
integers spanning `K` over `ℚ`, and `B` its integer coordinate matrix in a `ℤ`-basis `β` of `𝓞 K`.
The lattice of integer relations `∑ a, c a • y a = 0` has covolume `√det (B Bᵀ)` divided by the
gcd of the maximal minors of `B`. -/
theorem covolume_intLattice_ker_linearCombination {p : ℕ} (β : Basis (Fin p) ℤ (𝓞 K))
    {y : κ → 𝓞 K} (hy : span ℚ (Set.range fun a ↦ (y a : K)) = ⊤) :
    ZLattice.covolume (LinearMap.ker (Fintype.linearCombination ℚ fun a ↦ (y a : K))).intLattice =
      √((β.toMatrix y * (β.toMatrix y)ᵀ).det : ℝ) / ((β.toMatrix y).minorGcd : ℝ) := by
  set b := β.localizationLocalization ℚ (nonZeroDivisors ℤ) K
  have hB := toMatrix_localizationLocalization_coe β y
  rw [← b.ker_mulVecLin_toMatrix, hB]
  exact covolume_intLattice_ker_mulVecLin (hB ▸ (b.linearIndependent_row_toMatrix_iff _).2 hy)

end Module.Basis

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {κ : Type*} [Fintype κ]

open scoped Classical in
/-- **The covolume of the lattice of integer relations, through the conjugates.** For a finite
family `y` of algebraic integers spanning `K` over `ℚ`, with `V` the matrix of the values
`σ (y a)` under the embeddings `σ : K →ₐ[ℚ] ℂ`, the lattice of integer relations among the `y a`
has covolume at most `√(det (Vᴴ V) / |disc K|)`. -/
theorem covolume_intLattice_ker_linearCombination_le {y : κ → 𝓞 K}
    (hy : span ℚ (Set.range fun a ↦ (y a : K)) = ⊤) :
    ZLattice.covolume (LinearMap.ker (Fintype.linearCombination ℚ fun a ↦ (y a : K))).intLattice ≤
      √(((Algebra.embeddingsMatrix ℚ ℂ fun a ↦ (y a : K))ᴴ *
          Algebra.embeddingsMatrix ℚ ℂ fun a ↦ (y a : K)).det.re /
        |(NumberField.discr K : ℝ)|) := by
  set β := (NumberField.RingOfIntegers.basis K).reindex (Fintype.equivFin _)
  have hrow : LinearIndependent ℚ ((β.toMatrix y).map ((↑) : ℤ → ℚ)).row := by
    rw [← β.toMatrix_localizationLocalization_coe y]
    exact (Basis.linearIndependent_row_toMatrix_iff _ _).2 hy
  have hd : (NumberField.discr K : ℝ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero K
  rw [β.covolume_intLattice_ker_linearCombination hy,
    β.det_conjTranspose_mul_self_embeddingsMatrix_ringOfIntegers y, Complex.intCast_re]
  push_cast
  rw [mul_div_cancel_left₀ _ (abs_ne_zero.2 hd)]
  exact div_le_self (Real.sqrt_nonneg _) (by exact_mod_cast Matrix.one_le_minorGcd hrow)

/-- **The covolume of the lattice of integer relations is bounded by the conjugates.** For a finite
family `y` of algebraic integers spanning `K` over `ℚ`, the lattice of integer relations among the
`y a` has covolume at most `√(∏_σ ∑_a |σ (y a)|²) / √|disc K|`, the product running over the
embeddings `σ : K →ₐ[ℚ] ℂ`. -/
theorem covolume_intLattice_ker_linearCombination_le_sqrt_prod {y : κ → 𝓞 K}
    (hy : span ℚ (Set.range fun a ↦ (y a : K)) = ⊤) :
    ZLattice.covolume (LinearMap.ker (Fintype.linearCombination ℚ fun a ↦ (y a : K))).intLattice ≤
      √(∏ σ : K →ₐ[ℚ] ℂ, ∑ a, ‖σ (y a)‖ ^ 2) / √|(NumberField.discr K : ℝ)| := by
  classical
  refine (covolume_intLattice_ker_linearCombination_le hy).trans ?_
  rw [Real.sqrt_div' _ (abs_nonneg _)]
  gcongr
  set v : (K →ₐ[ℚ] ℂ) → EuclideanSpace ℂ κ := fun σ ↦ WithLp.toLp 2 fun a ↦ σ (y a)
  have hgram : ((Algebra.embeddingsMatrix ℚ ℂ fun a ↦ (y a : K))ᴴ *
      Algebra.embeddingsMatrix ℚ ℂ fun a ↦ (y a : K)) = gram ℂ v := by
    ext σ τ
    simp [v, gram, Matrix.mul_apply, PiLp.inner_apply, mul_comm]
  have h := re_det_gram_le_prod_norm_sq (𝕜 := ℂ) v
  rw [RCLike.re_to_complex] at h
  rw [hgram]
  refine h.trans_eq ?_
  simp [v, EuclideanSpace.norm_sq_eq]

/-- **The covolume of the lattice of integer relations, uniform form.** For a finite family `y` of
algebraic integers spanning `K` over `ℚ` whose conjugates `σ (y a)` all have absolute value at
most `H`, the lattice of integer relations among the `y a` has covolume at most
`√((|κ| H²) ^ [K : ℚ]) / √|disc K|`. -/
theorem covolume_intLattice_ker_linearCombination_le_of_norm_le {y : κ → 𝓞 K}
    (hy : span ℚ (Set.range fun a ↦ (y a : K)) = ⊤) {H : ℝ}
    (hH : ∀ (σ : K →ₐ[ℚ] ℂ) (a : κ), ‖σ (y a)‖ ≤ H) :
    ZLattice.covolume (LinearMap.ker (Fintype.linearCombination ℚ fun a ↦ (y a : K))).intLattice ≤
      √((Fintype.card κ * H ^ 2) ^ finrank ℚ K) / √|(NumberField.discr K : ℝ)| := by
  refine (covolume_intLattice_ker_linearCombination_le_sqrt_prod hy).trans ?_
  gcongr
  rw [← AlgHom.card ℚ K ℂ, ← Finset.card_univ (α := K →ₐ[ℚ] ℂ), ← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun σ _ ↦ ?_
  calc ∑ a, ‖σ (y a)‖ ^ 2 ≤ ∑ _a : κ, H ^ 2 :=
        Finset.sum_le_sum fun a _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hH σ a) 2
    _ = Fintype.card κ * H ^ 2 := by simp

end TauCeti.NumberField
