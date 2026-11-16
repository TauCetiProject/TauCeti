/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import TauCeti.Algebra.BigOperators.Ring.SquareZero
import TauCeti.Analysis.InnerProductSpace.SkewSymmetric.Basic
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# Real normal form of skew-adjoint endomorphisms and Pfaffian powers of two-vectors

Every skew-adjoint endomorphism `A : E →ₗ[ℝ] E` of a finite-dimensional real inner product space
satisfies `A† = -A`. In odd dimension its determinant therefore satisfies `det A = -det A = 0`, so
`A` admits a unit vector in its kernel (`LinearMap.det_eq_zero_of_skew_odd`,
`LinearMap.exists_norm_eq_one_apply_eq_zero_of_skew_odd`).

In even dimension `2 * r`, iterating the spectral theorem on the symmetric positive semidefinite
operator `-A²` splits `E` into `r` pairwise orthogonal `A`-invariant planes: there is an
orthonormal basis `(p₀, q₀, …, p_{r-1}, q_{r-1})` and nonnegative scalars `μ₀, …, μ_{r-1}` with
`A pⱼ = μⱼ qⱼ` and `A qⱼ = -μⱼ pⱼ` (`LinearMap.exists_orthonormalBasis_skew_normalForm`).

Applying this normal form to the skew-adjoint contraction `TauCeti.twoVectorContraction F` of a
two-vector `F ∈ ⋀² E` writes `F = ∑ⱼ μⱼ (pⱼ ∧ qⱼ)` in that orthonormal basis. Because elements of
`⋀² E` are central in the exterior algebra and each decomposable two-vector squares to zero, the
multinomial theorem for square-zero elements evaluates the divided `r`-th exterior power:
`(r!)⁻¹ Fʳ = (∏ⱼ μⱼ) (p₀ ∧ q₀ ∧ ⋯ ∧ p_{r-1} ∧ q_{r-1})`
(`TauCeti.exists_orthonormalBasis_twoVector_normalForm`).

## Main results

* `LinearMap.det_eq_zero_of_skew_odd`, `LinearMap.exists_norm_eq_one_apply_eq_zero_of_skew_odd`:
  a skew-adjoint endomorphism of an odd-dimensional real inner product space has determinant zero
  and a unit vector in its kernel.
* `LinearMap.exists_orthonormalBasis_skew_normalForm`: the real block-diagonal normal form of a
  skew-adjoint endomorphism in even dimension `2 * r`.
* `TauCeti.ExteriorAlgebra.noncommProd_univ_smul_ιMulti_two` and
  `TauCeti.ExteriorAlgebra.pow_sum_smul_ιMulti_two`: exterior products and `r`-th powers of sums
  of weighted decomposable two-vectors.
* `TauCeti.twoVector_eq_sum_of_skew_normalForm`: a two-vector whose contraction is in normal form
  decomposes as `∑ⱼ μⱼ (pⱼ ∧ qⱼ)`.
* `TauCeti.exists_orthonormalBasis_twoVector_normalForm`: simultaneous normal form and Pfaffian
  divided-power identity for any two-vector in even dimension `2 * r`.

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), §II.6.
* H. Federer, *Geometric Measure Theory*, Springer (1969), §1.8.2.
-/

public section

open Module
open scoped RealInnerProductSpace

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A skew-adjoint endomorphism of an odd-dimensional real inner product space has determinant
zero, because `A† = -A` forces `det A = (-1)^(dim E) det A = -det A`. -/
theorem det_eq_zero_of_skew_odd (A : E →ₗ[ℝ] E)
    (hA : ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫) (hodd : Odd (finrank ℝ E)) :
    A.det = 0 := by
  have hadj : -A = A.adjoint := by
    rw [eq_adjoint_iff]
    intro x y
    rw [LinearMap.neg_apply, inner_neg_left]
    linarith [hA x y]
  have hdet : A.det = (-A).det := by
    simpa [← hadj] using (det_adjoint A).symm
  have hneg : (-A).det = (-1 : ℝ) ^ finrank ℝ E * A.det := by
    simpa [neg_one_smul] using det_smul (-1 : ℝ) A
  rw [hneg, hodd.neg_one_pow] at hdet
  linarith

/-- A skew-adjoint endomorphism of an odd-dimensional real inner product space has a unit vector
in its kernel. -/
theorem exists_norm_eq_one_apply_eq_zero_of_skew_odd (A : E →ₗ[ℝ] E)
    (hA : ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫) (hodd : Odd (finrank ℝ E)) :
    ∃ u : E, ‖u‖ = 1 ∧ A u = 0 := by
  have hker : ker A ≠ ⊥ := det_eq_zero_iff_ker_ne_bot.mp (A.det_eq_zero_of_skew_odd hA hodd)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨‖v‖⁻¹ • v, norm_smul_inv_norm hv0, ?_⟩
  rw [map_smul, mem_ker.mp hv, smul_zero]

/-- On an even-dimensional positive-dimensional real inner product space, every skew-adjoint
endomorphism admits an invariant two-dimensional plane spanned by an orthonormal pair `(p, q)` on
which `A p = c • q` and `A q = -(c • p)` for some `c ≥ 0`. -/
private theorem exists_skew_invariant_plane {r : ℕ} (hdim : finrank ℝ E = 2 * (r + 1))
    (A : E →ₗ[ℝ] E) (hA : ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫) :
    ∃ (p q : E) (c : ℝ), 0 ≤ c ∧ ‖p‖ = 1 ∧ ‖q‖ = 1 ∧ ⟪p, q⟫ = 0 ∧
      A p = c • q ∧ A q = -(c • p) := by
  let S : E →ₗ[ℝ] E := -(A.comp A)
  have hS : S.IsSymmetric := fun x y ↦ by
    change ⟪-(A (A x)), y⟫ = ⟪x, -(A (A y))⟫
    rw [inner_neg_left, inner_neg_right, hA (A x) y, hA x (A y), neg_neg]
  let e := hS.eigenvectorBasis rfl
  let i₀ : Fin (finrank ℝ E) := ⟨0, by omega⟩
  set p := e i₀
  have hp : ‖p‖ = 1 := e.orthonormal.1 i₀
  have hSp : -(A (A p)) = hS.eigenvalues rfl i₀ • p := by
    simpa [S, p] using hS.apply_eigenvectorBasis rfl i₀
  have hAp_sq : ‖A p‖ ^ 2 = hS.eigenvalues rfl i₀ := by
    have h1 : ⟪-(A (A p)), p⟫ = ‖A p‖ ^ 2 := by
      rw [inner_neg_left, hA (A p) p, neg_neg, real_inner_self_eq_norm_sq]
    rw [hSp, real_inner_smul_left, real_inner_self_eq_norm_sq, hp] at h1
    linarith
  by_cases hAp : A p = 0
  · let W : Submodule ℝ E := (ℝ ∙ p)ᗮ
    have hW_inv : ∀ x ∈ W, A x ∈ W := fun x hx ↦ by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hx ⊢
      rw [← neg_eq_zero, ← hA p x, hAp, inner_zero_left]
    let AW : W →ₗ[ℝ] W := A.restrict hW_inv
    have hAW : ∀ x y : W, ⟪AW x, y⟫ = -⟪x, AW y⟫ := fun x y ↦ hA x.1 y.1
    have hp0 : p ≠ 0 := norm_ne_zero_iff.mp (by rw [hp]; exact one_ne_zero)
    have hW_dim : finrank ℝ W = 2 * r + 1 := by
      have h := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ p)
      rw [finrank_span_singleton hp0, hdim] at h
      dsimp only [W]
      omega
    obtain ⟨q, hq, hAq⟩ := AW.exists_norm_eq_one_apply_eq_zero_of_skew_odd hAW ⟨r, hW_dim⟩
    refine ⟨p, q.1, 0, le_rfl, hp, by simpa using hq,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp q.2, by simp [hAp], ?_⟩
    simpa [AW] using congrArg Subtype.val hAq
  · have hpos : 0 < ‖A p‖ := norm_pos_iff.mpr hAp
    refine ⟨p, ‖A p‖⁻¹ • A p, ‖A p‖, hpos.le, hp, norm_smul_inv_norm hAp, ?_, ?_, ?_⟩
    · rw [real_inner_smul_right, TauCeti.inner_self_apply_eq_zero_of_skew hA p, mul_zero]
    · rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
    · rw [map_smul, neg_eq_iff_eq_neg.mp hSp, ← hAp_sq, smul_neg, smul_smul, sq,
        inv_mul_cancel_left₀ hpos.ne']

omit [FiniteDimensional ℝ E] in
private theorem finrank_span_pair_of_orthonormal {p q : E}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : ⟪p, q⟫ = 0) :
    finrank ℝ (Submodule.span ℝ {p, q}) = 2 := by
  have hpq_orth : Orthonormal ℝ ![p, q] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hp, hq, hpq, real_inner_comm]
  have hrange : Set.range ![p, q] = {p, q} := by ext x; simp [eq_comm, or_comm]
  rw [← hrange, finrank_span_eq_card hpq_orth.linearIndependent, Fintype.card_fin]

omit [FiniteDimensional ℝ E] in
private theorem orthonormal_plane_append_orthogonal {r : ℕ} {p q : E}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : ⟪p, q⟫ = 0)
    (bQ : OrthonormalBasis (Fin r × Fin 2) ℝ (Submodule.span ℝ {p, q})ᗮ) :
    Orthonormal ℝ (fun jk : Fin (r + 1) × Fin 2 ↦
      (Fin.cases (motive := fun _ ↦ Fin 2 → E) (fun k ↦ ![p, q] k)
        (fun j k ↦ (bQ (j, k) : E)) jk.1) jk.2) := by
  have hp_orth (j : Fin r) (k : Fin 2) : ⟪p, (bQ (j, k) : E)⟫ = 0 :=
    (bQ (j, k)).2 p (Submodule.subset_span (by simp))
  have hq_orth (j : Fin r) (k : Fin 2) : ⟪q, (bQ (j, k) : E)⟫ = 0 :=
    (bQ (j, k)).2 q (Submodule.subset_span (by simp))
  refine ⟨fun ⟨j, k⟩ ↦ ?_, fun ⟨j₁, k₁⟩ ⟨j₂, k₂⟩ hne ↦ ?_⟩
  · cases j using Fin.cases with
    | zero => fin_cases k <;> simp [hp, hq]
    | succ j => simp [Submodule.norm_coe]
  · cases j₁ using Fin.cases with
    | zero =>
      cases j₂ using Fin.cases with
      | zero =>
        fin_cases k₁ <;> fin_cases k₂
        · exact (hne rfl).elim
        · simpa using hpq
        · simpa [real_inner_comm] using hpq
        · exact (hne rfl).elim
      | succ j₂ =>
        fin_cases k₁
        · simpa using hp_orth j₂ k₂
        · simpa using hq_orth j₂ k₂
    | succ j₁ =>
      cases j₂ using Fin.cases with
      | zero =>
        fin_cases k₂
        · simpa [real_inner_comm] using hp_orth j₁ k₁
        · simpa [real_inner_comm] using hq_orth j₁ k₁
      | succ j₂ =>
        have hne' : (j₁, k₁) ≠ (j₂, k₂) := fun h ↦ hne (by cases h; rfl)
        simpa using bQ.orthonormal.2 hne'

/-- Reindex an orthonormal pair `(p, q)` together with an orthonormal basis of `(span {p, q})ᗮ`
into an orthonormal basis of `E` indexed by `Fin (r + 1) × Fin 2`. -/
private noncomputable def orthonormalBasisOfPlaneAndOrthogonal {r : ℕ} {p q : E}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : ⟪p, q⟫ = 0)
    (bQ : OrthonormalBasis (Fin r × Fin 2) ℝ (Submodule.span ℝ {p, q})ᗮ) :
    OrthonormalBasis (Fin (r + 1) × Fin 2) ℝ E := by
  let v : Fin (r + 1) × Fin 2 → E := fun jk ↦
    Fin.cases (fun k ↦ ![p, q] k) (fun j k ↦ (bQ (j, k) : E)) jk.1 jk.2
  have hv : Orthonormal ℝ v := orthonormal_plane_append_orthogonal hp hq hpq bQ
  have hcard : Fintype.card (Fin (r + 1) × Fin 2) = finrank ℝ E := by
    have h := Submodule.finrank_add_finrank_orthogonal (Submodule.span ℝ {p, q})
    have hQ : finrank ℝ (Submodule.span ℝ {p, q})ᗮ = 2 * r := by
      simpa [mul_comm] using (finrank_eq_card_basis bQ.toBasis)
    rw [finrank_span_pair_of_orthonormal hp hq hpq, hQ] at h
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  exact (basisOfLinearIndependentOfCardEqFinrank' v hv.linearIndependent hcard).toOrthonormalBasis
    (by simpa only [coe_basisOfLinearIndependentOfCardEqFinrank'] using hv)

/-- **Real normal form of a skew-adjoint endomorphism**: on a `2r`-dimensional real inner product
space, every skew-adjoint endomorphism `A` is block-diagonal in some orthonormal basis
`(b (j, 0), b (j, 1))`, with `A (b (j, 0)) = μ j • b (j, 1)` and
`A (b (j, 1)) = -(μ j • b (j, 0))` for nonnegative scalars `μ j`. -/
theorem exists_orthonormalBasis_skew_normalForm {r : ℕ}
    (hdim : finrank ℝ E = 2 * r) (A : E →ₗ[ℝ] E)
    (hA : ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫) :
    ∃ (b : OrthonormalBasis (Fin r × Fin 2) ℝ E) (μ : Fin r → ℝ),
      (∀ j, 0 ≤ μ j) ∧
      (∀ j, A (b (j, 0)) = μ j • b (j, 1)) ∧
      (∀ j, A (b (j, 1)) = -(μ j • b (j, 0))) := by
  induction r generalizing E with
  | zero =>
    refine ⟨(stdOrthonormalBasis ℝ E).reindex
      (Fintype.equivOfCardEq (by simp [hdim])), Fin.elim0,
      fun j ↦ j.elim0, fun j ↦ j.elim0, fun j ↦ j.elim0⟩
  | succ r ih =>
    obtain ⟨p, q, c, hc, hp, hq, hpq, hAp, hAq⟩ := exists_skew_invariant_plane hdim A hA
    let P : Submodule ℝ E := Submodule.span ℝ {p, q}
    have hQ_inv : ∀ x ∈ Pᗮ, A x ∈ Pᗮ := fun x hx y hy ↦ by
      have hp_x : ⟪p, x⟫ = 0 := hx p (Submodule.subset_span (by simp))
      have hq_x : ⟪q, x⟫ = 0 := hx q (Submodule.subset_span (by simp))
      refine Submodule.span_induction (p := fun y _ ↦ ⟪y, A x⟫ = 0) ?_ (by simp)
        (fun a b _ _ ha hb ↦ by rw [inner_add_left, ha, hb, add_zero])
        (fun s a _ ha ↦ by rw [real_inner_smul_left, ha, mul_zero]) hy
      rintro y (hy | hy)
      · rw [hy, ← neg_eq_zero, ← hA p x, hAp, real_inner_smul_left, hq_x, mul_zero]
      · rw [hy, ← neg_eq_zero, ← hA q x, hAq, inner_neg_left, real_inner_smul_left, hp_x, mul_zero,
          neg_zero]
    have hQ_dim : finrank ℝ Pᗮ = 2 * r := by
      have h := Submodule.finrank_add_finrank_orthogonal P
      rw [finrank_span_pair_of_orthonormal hp hq hpq, hdim] at h
      omega
    obtain ⟨bQ, μQ, hμQ, hAQ0, hAQ1⟩ := ih hQ_dim (A.restrict hQ_inv) (fun x y ↦ hA x.1 y.1)
    let b := orthonormalBasisOfPlaneAndOrthogonal hp hq hpq bQ
    have hb0 : b (0, 0) = p := by simp [b, orthonormalBasisOfPlaneAndOrthogonal]
    have hb1 : b (0, 1) = q := by simp [b, orthonormalBasisOfPlaneAndOrthogonal]
    have hbs (j : Fin r) (k : Fin 2) : b (j.succ, k) = (bQ (j, k) : E) := by
      simp [b, orthonormalBasisOfPlaneAndOrthogonal]
    refine ⟨b, Fin.cases c μQ, Fin.cases hc hμQ,
      Fin.cases (by simpa [hb0, hb1] using hAp)
        (fun j ↦ by simpa [hbs] using congrArg Subtype.val (hAQ0 j)),
      Fin.cases (by simpa [hb0, hb1] using hAq)
        (fun j ↦ by simpa [hbs] using congrArg Subtype.val (hAQ1 j))⟩

end LinearMap

namespace TauCeti

/-! ### Exterior powers of sums of weighted decomposable two-vectors -/

namespace ExteriorAlgebra

section WeightedTwoVectors

open scoped Function

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Any two weighted decomposable two-vectors commute in the exterior algebra. -/
theorem commute_smul_ιMulti_two (a b : R) (u₁ w₁ u₂ w₂ : M) :
    Commute (a • _root_.ExteriorAlgebra.ιMulti R 2 ![u₁, w₁])
      (b • _root_.ExteriorAlgebra.ιMulti R 2 ![u₂, w₂]) := by
  have hmem : a • _root_.ExteriorAlgebra.ιMulti R 2 ![u₁, w₁] ∈ ⋀[R]^2 M :=
    Submodule.smul_mem _ _ (exteriorPower.ιMulti R 2 ![u₁, w₁]).2
  exact Subalgebra.mem_center_iff.mp (mem_center_of_mem_of_even hmem even_two) _ |>.symm

/-- Every weighted decomposable two-vector squares to zero in the exterior algebra. -/
theorem smul_ιMulti_two_mul_self (a : R) (u w : M) :
    (a • _root_.ExteriorAlgebra.ιMulti R 2 ![u, w]) *
        (a • _root_.ExteriorAlgebra.ιMulti R 2 ![u, w]) = 0 := by
  rw [smul_mul_smul_comm, _root_.ExteriorAlgebra.ιMulti_mul_ιMulti]
  have h0 : _root_.ExteriorAlgebra.ιMulti R (2 + 2) (Fin.append ![u, w] ![u, w]) = 0 :=
    (_root_.ExteriorAlgebra.ιMulti R 4).map_eq_zero_of_eq _ (i := 0) (j := 2) rfl (by decide)
  rw [h0, smul_zero]

/-- The noncommutative product of `r` weighted consecutive pairs `μ j • (v_{2j} ∧ v_{2j+1})` in
the exterior algebra is `(∏ j, μ j) • (v₀ ∧ ⋯ ∧ v_{2r-1})`. -/
theorem noncommProd_univ_smul_ιMulti_two {r : ℕ} (μ : Fin r → R) (v : Fin (2 * r) → M)
    (hcomm : ((Finset.univ : Finset (Fin r)) : Set (Fin r)).Pairwise
      (Commute on fun j : Fin r ↦ μ j • _root_.ExteriorAlgebra.ιMulti R 2
        ![v ⟨2 * (j : ℕ), by omega⟩, v ⟨2 * (j : ℕ) + 1, by omega⟩])) :
    (Finset.univ : Finset (Fin r)).noncommProd
        (fun j : Fin r ↦ μ j • _root_.ExteriorAlgebra.ιMulti R 2
          ![v ⟨2 * (j : ℕ), by omega⟩, v ⟨2 * (j : ℕ) + 1, by omega⟩]) hcomm =
      (∏ j : Fin r, μ j) • _root_.ExteriorAlgebra.ιMulti R (2 * r) v := by
  have huniv_eq : (Finset.univ : Finset (Fin r)) = (List.finRange r).toFinset := by
    ext j; simp
  refine ((Finset.noncommProd_congr huniv_eq (fun _ _ ↦ rfl) hcomm).trans
    (Finset.noncommProd_toFinset _ _ _ (List.nodup_finRange r))).trans ?_
  clear huniv_eq hcomm
  induction r with
  | zero =>
    simp [_root_.ExteriorAlgebra.ιMulti_zero_apply]
  | succ r ih =>
    let v' : Fin (2 * r) → M := fun i ↦ v ⟨(i : ℕ), by omega⟩
    rw [List.finRange_succ_last, List.map_append, List.prod_append, List.map_map,
      List.map_singleton, List.prod_singleton]
    have hih := ih (μ ∘ Fin.castSucc) v'
    rw [show ((List.finRange r).map ((fun j : Fin (r + 1) ↦ μ j • _root_.ExteriorAlgebra.ιMulti R 2
        ![v ⟨2 * (j : ℕ), by omega⟩, v ⟨2 * (j : ℕ) + 1, by omega⟩]) ∘ Fin.castSucc)).prod =
        (∏ j : Fin r, μ j.castSucc) • _root_.ExteriorAlgebra.ιMulti R (2 * r) v' from hih]
    rw [Fin.prod_univ_castSucc, smul_mul_smul_comm, _root_.ExteriorAlgebra.ιMulti_mul_ιMulti]
    congr 1
    apply congrArg (_root_.ExteriorAlgebra.ιMulti R (2 * (r + 1)))
    ext i
    by_cases hi : (i : ℕ) < 2 * r
    · have hcast : i = Fin.castAdd 2 ⟨(i : ℕ), hi⟩ := Fin.ext rfl
      rw [hcast, Fin.append_left]
      rfl
    · have hcast : i = Fin.natAdd (2 * r) ⟨(i : ℕ) - 2 * r, by omega⟩ := Fin.ext (by simp; omega)
      rw [hcast, Fin.append_right]
      have hidx : (i : ℕ) - 2 * r = 0 ∨ (i : ℕ) - 2 * r = 1 := by omega
      rcases hidx with h0 | h1
      · simp [h0]; rfl
      · simp [h1]; rfl

/-- The `r`-th exterior power of a sum of `r` weighted decomposable two-vectors is `r!` times the
product of the weights times the `2r`-fold wedge product of the frame. -/
theorem pow_sum_smul_ιMulti_two {r : ℕ} (μ : Fin r → R) (v : Fin (2 * r) → M) :
    (∑ j : Fin r, μ j • _root_.ExteriorAlgebra.ιMulti R 2
        ![v ⟨2 * (j : ℕ), by omega⟩, v ⟨2 * (j : ℕ) + 1, by omega⟩]) ^ r =
      r.factorial • ((∏ j : Fin r, μ j) • _root_.ExteriorAlgebra.ιMulti R (2 * r) v) := by
  have hcomm : Pairwise (Commute on fun j : Fin r ↦ μ j • _root_.ExteriorAlgebra.ιMulti R 2
      ![v ⟨2 * (j : ℕ), by omega⟩, v ⟨2 * (j : ℕ) + 1, by omega⟩]) :=
    fun _ _ _ ↦ commute_smul_ιMulti_two _ _ _ _ _ _
  rw [Finset.sum_pow_of_pairwise_commute_of_mul_self_eq_zero Finset.univ _ hcomm
    (fun j _ ↦ smul_ιMulti_two_mul_self _ _ _) r]
  have hpow : (Finset.univ : Finset (Fin r)).powersetCard r = {Finset.univ} := by
    ext t
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and, Finset.mem_singleton]
    exact ⟨fun ht ↦ Finset.eq_univ_of_card t (by simpa using ht),
      fun ht ↦ by simp [ht]⟩
  rw [hpow, Finset.sum_singleton, noncommProd_univ_smul_ιMulti_two]

end WeightedTwoVectors

end ExteriorAlgebra

/-! ### Normal form and Pfaffian divided power of a two-vector -/

section TwoVectorNormalForm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A two-vector `F ∈ ⋀² E` whose skew-adjoint contraction `TauCeti.twoVectorContraction F` is
block-diagonal in an orthonormal basis `(b (j, 0), b (j, 1))` with weights `μ j` decomposes as
`F = ∑ j, μ j • (b (j, 0) ∧ b (j, 1))`. -/
theorem twoVector_eq_sum_of_skew_normalForm {r : ℕ} (F : ⋀[ℝ]^2 E)
    (b : OrthonormalBasis (Fin r × Fin 2) ℝ E) (μ : Fin r → ℝ)
    (h0 : ∀ j, twoVectorContraction F (b (j, 0)) = μ j • b (j, 1))
    (h1 : ∀ j, twoVectorContraction F (b (j, 1)) = -(μ j • b (j, 0))) :
    F = ∑ j : Fin r, μ j • exteriorPower.ιMulti ℝ 2 ![b (j, 0), b (j, 1)] := by
  refine exteriorPower.ext_inner_ιMulti_two fun u w ↦ ?_
  rw [← inner_twoVectorContraction_apply]
  have expand (x : E) : x = ∑ j : Fin r,
      (⟪b (j, 0), x⟫ • b (j, 0) + ⟪b (j, 1), x⟫ • b (j, 1)) := by
    conv_lhs => rw [← b.sum_repr' x]
    rw [Fintype.sum_prod_type]
    simp [Fin.sum_univ_two]
  conv_lhs => rw [expand u]
  simp only [map_sum, map_add, map_smul, h0, h1, sum_inner, inner_add_left,
    inner_neg_left, real_inner_smul_left, exteriorPower.inner_ιMulti_two]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- **Simultaneous normal form and Pfaffian divided power of a two-vector**: on a `2r`-dimensional
real inner product space `E`, every two-vector `F ∈ ⋀² E` admits an orthonormal basis
`b : OrthonormalBasis (Fin (2 * r)) ℝ E` and nonnegative weights `μ : Fin r → ℝ` putting
`TauCeti.twoVectorContraction F` in block-diagonal normal form, decomposing
`F = ∑ j, μ j • (b_{2j} ∧ b_{2j+1})`, and evaluating the divided `r`-th exterior power as
`(r!)⁻¹ • Fʳ = (∏ j, μ j) • (b₀ ∧ ⋯ ∧ b_{2r-1})`. -/
theorem exists_orthonormalBasis_twoVector_normalForm {r : ℕ}
    (hdim : finrank ℝ E = 2 * r) (F : ⋀[ℝ]^2 E) :
    ∃ (b : OrthonormalBasis (Fin (2 * r)) ℝ E) (μ : Fin r → ℝ),
      (∀ j, 0 ≤ μ j) ∧
      (∀ j : Fin r, twoVectorContraction F (b ⟨2 * (j : ℕ), by omega⟩) =
        μ j • b ⟨2 * (j : ℕ) + 1, by omega⟩) ∧
      (∀ j : Fin r, twoVectorContraction F (b ⟨2 * (j : ℕ) + 1, by omega⟩) =
        -(μ j • b ⟨2 * (j : ℕ), by omega⟩)) ∧
      F = ∑ j : Fin r, μ j • exteriorPower.ιMulti ℝ 2
        ![b ⟨2 * (j : ℕ), by omega⟩, b ⟨2 * (j : ℕ) + 1, by omega⟩] ∧
      (r.factorial : ℝ)⁻¹ •
          (⟨(F : _root_.ExteriorAlgebra ℝ E) ^ r, by
            simpa [pow_mul] using Submodule.pow_mem_pow _ F.2 r⟩ : ⋀[ℝ]^(2 * r) E) =
        (∏ j : Fin r, μ j) • exteriorPower.ιMulti ℝ (2 * r) b := by
  obtain ⟨b₀, μ, hμ, h0, h1⟩ := (twoVectorContraction F).exists_orthonormalBasis_skew_normalForm
    hdim (inner_twoVectorContraction_apply_left F)
  let e : Fin r × Fin 2 ≃ Fin (2 * r) := finProdFinEquiv.trans (finCongr (Nat.mul_comm r 2))
  let b : OrthonormalBasis (Fin (2 * r)) ℝ E := b₀.reindex e
  have he0 (j : Fin r) : e (j, 0) = ⟨2 * (j : ℕ), by omega⟩ :=
    Fin.ext (by simp [e, Nat.mul_comm])
  have he1 (j : Fin r) : e (j, 1) = ⟨2 * (j : ℕ) + 1, by omega⟩ :=
    Fin.ext (by simp [e, Nat.mul_comm, Nat.add_comm])
  have hb0 (j : Fin r) : b ⟨2 * (j : ℕ), by omega⟩ = b₀ (j, 0) := by
    rw [← he0 j]; simp [b]
  have hb1 (j : Fin r) : b ⟨2 * (j : ℕ) + 1, by omega⟩ = b₀ (j, 1) := by
    rw [← he1 j]; simp [b]
  have hF : F = ∑ j : Fin r, μ j • exteriorPower.ιMulti ℝ 2
      ![b ⟨2 * (j : ℕ), by omega⟩, b ⟨2 * (j : ℕ) + 1, by omega⟩] := by
    simpa only [hb0, hb1] using twoVector_eq_sum_of_skew_normalForm F b₀ μ h0 h1
  refine ⟨b, μ, hμ, fun j ↦ by simpa only [hb0, hb1] using h0 j,
    fun j ↦ by simpa only [hb0, hb1] using h1 j, hF, ?_⟩
  apply Subtype.ext
  have hcoe : (F : _root_.ExteriorAlgebra ℝ E) =
      ∑ j : Fin r, μ j • _root_.ExteriorAlgebra.ιMulti ℝ 2
        ![b ⟨2 * (j : ℕ), by omega⟩, b ⟨2 * (j : ℕ) + 1, by omega⟩] := by
    conv_lhs => rw [hF]
    simp
  simp only [SetLike.val_smul, hcoe, ExteriorAlgebra.pow_sum_smul_ιMulti_two,
    exteriorPower.ιMulti_apply_coe, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  rw [inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r))]

end TwoVectorNormalForm

end TauCeti
