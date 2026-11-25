/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.GramSchmidtOrtho
public import TauCeti.LinearAlgebra.Matrix.Jacobi
import TauCeti.LinearAlgebra.Span.Basic

/-!
# Lanczos tridiagonalization along normalized Gram–Schmidt chains

For any inner product space `E` over `𝕜` (`ℝ` or `ℂ`), any linear endomorphism `T : E →ₗ[𝕜] E`,
and any finite chain of vectors `w : Fin (n + 1) → E` satisfying `T (w k.castSucc) = w k.succ`,
pairing along the normalized Gram–Schmidt family `e = gramSchmidtNormed 𝕜 w` vanishes strictly
below the first subdiagonal (`TauCeti.inner_gramSchmidtNormed_apply_eq_zero_of_add_one_lt`) and
gives `‖gramSchmidt 𝕜 w k.castSucc‖⁻¹ * ‖gramSchmidt 𝕜 w k.succ‖` on the first subdiagonal
(`TauCeti.inner_gramSchmidtNormed_succ_apply_castSucc`), without any linear-independence
assumption on `w`.

When `T` is symmetric (`T.IsSymmetric`), its matrix elements `⟪e i, T (e j)⟫` form the real
symmetric tridiagonal Jacobi matrix `TauCeti.symmJacobiMatrix` with diagonal `r ↦ re ⟪e r, T (e r)⟫`
and nonnegative subdiagonal `k ↦ ‖gramSchmidt 𝕜 w k.castSucc‖⁻¹ * ‖gramSchmidt 𝕜 w k.succ‖`
(`TauCeti.inner_gramSchmidtNormed_apply_eq_symmJacobiMatrix_map`).

## Main results

* `TauCeti.inner_gramSchmidtNormed_succ_apply_castSucc`: unconditional Lanczos subdiagonal formula
  `⟪e (k + 1), T (e k)⟫ = ‖gramSchmidt 𝕜 w k‖⁻¹ * ‖gramSchmidt 𝕜 w (k + 1)‖`.
* `TauCeti.inner_gramSchmidtNormed_apply_eq_zero_of_add_one_lt`: unconditional upper-Hessenberg
  vanishing `⟪e i, T (e j)⟫ = 0` for `j + 1 < i`.
* `TauCeti.inner_gramSchmidtNormed_apply_eq_symmJacobiMatrix_map`: unconditional Lanczos
  tridiagonalization of a symmetric operator along `gramSchmidtNormed 𝕜 w`.

## References

* I. Dumitriu, A. Edelman, *Matrix models for beta ensembles*, J. Math. Phys. 43 (2002),
  5830–5847.
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §4.5.1.
-/

public section

noncomputable section

open InnerProductSpace

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {n : ℕ}

/-- **Lanczos subdiagonal formula**: if `T (w k.castSucc) = w k.succ` for every `k : Fin n`, then
pairing the `(k + 1)`-st normalized Gram–Schmidt vector of `w` against the image of the `k`-th
under `T` gives `‖gramSchmidt 𝕜 w k.castSucc‖⁻¹ * ‖gramSchmidt 𝕜 w k.succ‖` unconditionally
(vanishing automatically if either Gram–Schmidt residual vanishes). -/
theorem inner_gramSchmidtNormed_succ_apply_castSucc {T : E →ₗ[𝕜] E} {w : Fin (n + 1) → E}
    (hw : ∀ k : Fin n, T (w k.castSucc) = w k.succ) (k : Fin n) :
    inner 𝕜 (gramSchmidtNormed 𝕜 w k.succ) (T (gramSchmidtNormed 𝕜 w k.castSucc)) =
      ((‖gramSchmidt 𝕜 w k.castSucc‖⁻¹ * ‖gramSchmidt 𝕜 w k.succ‖ : ℝ) : 𝕜) := by
  have hdiff : T (gramSchmidt 𝕜 w k.castSucc) - w k.succ =
      T (gramSchmidt 𝕜 w k.castSucc - w k.castSucc) := by
    rw [map_sub, hw k]
  have h0 : inner 𝕜 (gramSchmidtNormed 𝕜 w k.succ)
      (T (gramSchmidt 𝕜 w k.castSucc) - w k.succ) = 0 := by
    rw [hdiff]
    exact inner_gramSchmidtNormed_eq_zero_of_mem_span_Iio w k.succ
      (map_gramSchmidt_sub_mem_span_Iio hw k)
  have hstep1 : inner 𝕜 (gramSchmidtNormed 𝕜 w k.succ) (T (gramSchmidt 𝕜 w k.castSucc)) =
      inner 𝕜 (gramSchmidtNormed 𝕜 w k.succ) (w k.succ) :=
    sub_eq_zero.mp (by rw [← inner_sub_right, h0])
  have he_cast : gramSchmidtNormed 𝕜 w k.castSucc =
      (‖gramSchmidt 𝕜 w k.castSucc‖ : 𝕜)⁻¹ • gramSchmidt 𝕜 w k.castSucc := by
    rw [gramSchmidtNormed]
  rw [he_cast, map_smul, inner_smul_right, hstep1, inner_gramSchmidtNormed_eq_norm,
    ← RCLike.ofReal_inv, ← RCLike.ofReal_mul]

/-- If `T (w k.castSucc) = w k.succ` for every `k : Fin n`, then the matrix elements of `T` along
`gramSchmidtNormed 𝕜 w` vanish strictly below the first subdiagonal (`j + 1 < i`). -/
theorem inner_gramSchmidtNormed_apply_eq_zero_of_add_one_lt {T : E →ₗ[𝕜] E}
    {w : Fin (n + 1) → E} (hw : ∀ k : Fin n, T (w k.castSucc) = w k.succ)
    {i j : Fin (n + 1)} (h : j.val + 1 < i.val) :
    inner 𝕜 (gramSchmidtNormed 𝕜 w i) (T (gramSchmidtNormed 𝕜 w j)) = 0 := by
  let j' : Fin n := ⟨j.val, by omega⟩
  have hj_eq : j = j'.castSucc := Fin.ext rfl
  have hej : gramSchmidtNormed 𝕜 w j ∈ Submodule.span 𝕜 (w '' Set.Iic j'.castSucc) := by
    rw [← span_gramSchmidt_Iic 𝕜 w j'.castSucc, ← span_gramSchmidtNormed w, hj_eq]
    exact Submodule.subset_span ⟨j'.castSucc, Set.mem_Iic.mpr le_rfl, rfl⟩
  have hsub : Set.Iic j'.succ ⊆ Set.Iio i := fun x hx => by
    simp only [Set.mem_Iic, Set.mem_Iio, Fin.le_def, Fin.lt_def, Fin.val_succ, j'] at hx ⊢
    omega
  exact inner_gramSchmidtNormed_eq_zero_of_mem_span_Iio w i
    (Submodule.span_mono (Set.image_mono hsub)
      (Submodule.map_mem_span_Iic_of_apply_castSucc hw j' hej))

/-- **Lanczos tridiagonalization**: for a symmetric operator `T` and any chain `w` satisfying
`T (w k.castSucc) = w k.succ`, the matrix elements of `T` along `gramSchmidtNormed 𝕜 w` form the
real symmetric Jacobi matrix with diagonal `r ↦ re ⟪e r, T (e r)⟫` and subdiagonal
`k ↦ ‖gramSchmidt 𝕜 w k.castSucc‖⁻¹ * ‖gramSchmidt 𝕜 w k.succ‖`. -/
theorem inner_gramSchmidtNormed_apply_eq_symmJacobiMatrix_map {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    {w : Fin (n + 1) → E} (hw : ∀ k : Fin n, T (w k.castSucc) = w k.succ) (i j : Fin (n + 1)) :
    inner 𝕜 (gramSchmidtNormed 𝕜 w i) (T (gramSchmidtNormed 𝕜 w j)) =
      (symmJacobiMatrix
        (fun r => RCLike.re (inner 𝕜 (gramSchmidtNormed 𝕜 w r) (T (gramSchmidtNormed 𝕜 w r))))
        (fun k => ‖gramSchmidt 𝕜 w k.castSucc‖⁻¹ * ‖gramSchmidt 𝕜 w k.succ‖)).map
        (algebraMap ℝ 𝕜) i j := by
  let e := gramSchmidtNormed 𝕜 w
  have hT_conj : ∀ x y, inner 𝕜 x (T y) = starRingEnd 𝕜 (inner 𝕜 y (T x)) := fun x y => by
    rw [← hT x y, inner_conj_symm]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.map_apply, symmJacobiMatrix_apply_self, RCLike.algebraMap_eq_ofReal]
    exact (RCLike.conj_eq_iff_re.mp (hT_conj (e i) (e i)).symm).symm
  · by_cases h1 : j.val = i.val + 1
    · let k : Fin n := ⟨i.val, by omega⟩
      have hi' : i = k.castSucc := Fin.ext rfl
      have hj' : j = k.succ := Fin.ext (by simp [k, h1])
      rw [hi', hj', Matrix.map_apply, symmJacobiMatrix_apply_castSucc_succ,
        RCLike.algebraMap_eq_ofReal, hT_conj, inner_gramSchmidtNormed_succ_apply_castSucc hw k,
        RCLike.conj_ofReal]
    · by_cases h2 : i.val = j.val + 1
      · let k : Fin n := ⟨j.val, by omega⟩
        have hj' : j = k.castSucc := Fin.ext rfl
        have hi' : i = k.succ := Fin.ext (by simp [k, h2])
        rw [hi', hj', Matrix.map_apply, symmJacobiMatrix_apply_succ_castSucc,
          RCLike.algebraMap_eq_ofReal, inner_gramSchmidtNormed_succ_apply_castSucc hw k]
      · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
        · rw [Matrix.map_apply, symmJacobiMatrix_apply_of_add_one_lt_right _ _ (i := i) (j := j)
            (by omega), map_zero, hT_conj,
            inner_gramSchmidtNormed_apply_eq_zero_of_add_one_lt hw (by omega), map_zero]
        · rw [Matrix.map_apply, symmJacobiMatrix_apply_of_add_one_lt_left _ _ (i := i) (j := j)
            (by omega), map_zero]
          exact inner_gramSchmidtNormed_apply_eq_zero_of_add_one_lt hw (by omega)

end TauCeti
