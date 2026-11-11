/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Forms
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Top-degree `bar∂`-primitives from the Poisson equation

On the coordinate space `ι → ℂ` of a finite linearly ordered index type `ι`, with coordinates
`z_j = x_j + I y_j`, the top-degree `bar∂`-equation reduces to the Poisson equation for the real
Laplacian `Δ = ∑_j (∂²/∂x_j² + ∂²/∂y_j²)`. Since `Δ = 4 ∑_j ∂²/∂(conj z_j) ∂z_j`
(`TauCeti.conjWirtingerDeriv_wirtingerDeriv_self`), for every `C²` function `v`

`bar∂ (∑_j (-1)^(j-1) ∂v/∂z_j d(conj z)_[j]) = (Δv / 4) d(conj z_1) ∧ ⋯ ∧ d(conj z_n)`,

where `d(conj z)_[j]` is the wedge product of all `d(conj z_i)` with `i ≠ j`, in increasing
order, and `j - 1` is the number of indices below `j`. Hence, on an open set where `Δv = 4f` can be
solved, the top-degree form `f d(conj z_1) ∧ ⋯ ∧ d(conj z_n)` is `bar∂`-exact with an explicit
primitive, as regular as `∂v`. Forms are recorded by their coefficient families, as for
`TauCeti.delBarCoeff`. Since `F` is arbitrary, this covers `(p,n)`-forms as well, through the
`(0,n)`-forms with coefficients in `Finset ι → F`, whose `bar∂` differs by the sign `(-1)^p`.

## Main declarations

* `TauCeti.topDegreePrimitiveCoeff v`: the coefficients of the `(0,n-1)`-form
  `∑_j (-1)^(j-1) ∂v/∂z_j d(conj z)_[j]`.
* `TauCeti.delBarCoeff_topDegreePrimitiveCoeff_univ`: its `bar∂` is
  `∑_j ∂²v/∂(conj z_j) ∂z_j d(conj z_1) ∧ ⋯ ∧ d(conj z_n)`.
* `TauCeti.delBarCoeff_topDegreePrimitiveCoeff_univ_eq_inv_four_smul_sum`: for `C²` functions
  `v` this is `(Δv / 4) d(conj z_1) ∧ ⋯ ∧ d(conj z_n)`.
* `TauCeti.exists_contDiffOn_delBarCoeff_univ_eq_of_sum_iteratedFDeriv_eq`: a solution of the
  Poisson equation `Δv = 4f` on an open set gives a `bar∂`-primitive of
  `f d(conj z_1) ∧ ⋯ ∧ d(conj z_n)` there.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Section 2.1.
* B. Malgrange, *Existence et approximation des solutions des équations aux dérivées
  partielles et des équations de convolution*, Ann. Inst. Fourier 6 (1956), 271–355.
-/

public section

open Complex Finset

namespace TauCeti

variable {ι : Type*} [LinearOrder ι] [Fintype ι] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- The coefficients of the `(0,n-1)`-form `∑_j (-1)^(j-1) ∂v/∂z_j d(conj z)_[j]` on `ι → ℂ`,
where `d(conj z)_[j]` is the wedge product of the `d(conj z_i)`, `i ≠ j`, in increasing order and
`j - 1` is the number of indices below `j`. The coefficient of `d(conj z)_J` is
`(-1)^#{i | i < j} ∂v/∂z_j` if `J` omits exactly the index `j`, and zero otherwise. -/
noncomputable def topDegreePrimitiveCoeff (v : (ι → ℂ) → F) (J : Finset ι) (z : ι → ℂ) : F :=
  ∑ j, if J = univ.erase j then (-1 : ℂ) ^ #{i | i < j} • wirtingerDeriv v z (Pi.single j 1)
    else 0

/-- The coefficient of `d(conj z)_[j]` in `topDegreePrimitiveCoeff v` is
`(-1)^#{i | i < j} ∂v/∂z_j`. -/
@[simp]
theorem topDegreePrimitiveCoeff_univ_erase (v : (ι → ℂ) → F) (j : ι) (z : ι → ℂ) :
    topDegreePrimitiveCoeff v (univ.erase j) z =
      (-1 : ℂ) ^ #{i | i < j} • wirtingerDeriv v z (Pi.single j 1) := by
  rw [topDegreePrimitiveCoeff, Finset.sum_eq_single j (fun k _ hkj ↦ ?_) (by simp)]
  · simp
  · simp [Finset.erase_inj _ (mem_univ j), Ne.symm hkj]

/-- The coefficients of `topDegreePrimitiveCoeff v` indexed by sets that do not omit exactly one
index vanish. -/
theorem topDegreePrimitiveCoeff_of_forall_ne (v : (ι → ℂ) → F) {J : Finset ι}
    (hJ : ∀ j, J ≠ univ.erase j) : topDegreePrimitiveCoeff v J = 0 := by
  ext z
  simp [topDegreePrimitiveCoeff, hJ]

/-- A coefficient of `topDegreePrimitiveCoeff v` is `C^m` at a point where `v` is `C^(m+1)`. -/
theorem contDiffAt_topDegreePrimitiveCoeff {v : (ι → ℂ) → F} {z : ι → ℂ} {m n : WithTop ℕ∞}
    (hv : ContDiffAt ℝ n v z) (hmn : m + 1 ≤ n) (J : Finset ι) :
    ContDiffAt ℝ m (topDegreePrimitiveCoeff v J) z := by
  by_cases hJ : ∃ j, J = univ.erase j
  · obtain ⟨j, rfl⟩ := hJ
    rw [show topDegreePrimitiveCoeff v (univ.erase j) = _ from
      funext (topDegreePrimitiveCoeff_univ_erase v j)]
    exact (hv.wirtingerDeriv_apply hmn (Pi.single j 1)).const_smul _
  · rw [topDegreePrimitiveCoeff_of_forall_ne v (not_exists.1 hJ)]
    exact contDiffAt_const

/-- The `bar∂` of `∑_j (-1)^(j-1) ∂v/∂z_j d(conj z)_[j]` is
`∑_j ∂²v/∂(conj z_j) ∂z_j d(conj z_1) ∧ ⋯ ∧ d(conj z_n)`: the signs of the primitive cancel those
of `bar∂`. -/
theorem delBarCoeff_topDegreePrimitiveCoeff_univ (v : (ι → ℂ) → F) (z : ι → ℂ) :
    delBarCoeff (topDegreePrimitiveCoeff v) univ z =
      ∑ j, conjWirtingerDeriv (fun y ↦ wirtingerDeriv v y (Pi.single j 1)) z (Pi.single j 1) := by
  rw [delBarCoeff_def]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have h : topDegreePrimitiveCoeff v (univ.erase j) =
      (-1 : ℂ) ^ #{i | i < j} • fun y ↦ wirtingerDeriv v y (Pi.single j 1) :=
    funext (topDegreePrimitiveCoeff_univ_erase v j)
  rw [h, conjWirtingerDeriv_const_smul, _root_.smul_apply, smul_smul, ← mul_pow, neg_one_mul,
    neg_neg, one_pow, one_smul]

/-- **The top-degree `bar∂`-primitive.** For `v` that is `C²` at `z`, the `bar∂` of
`∑_j (-1)^(j-1) ∂v/∂z_j d(conj z)_[j]` is `(Δv / 4) d(conj z_1) ∧ ⋯ ∧ d(conj z_n)` at `z`, where
`Δv = ∑_j (∂²v/∂x_j² + ∂²v/∂y_j²)` is the real Laplacian of `v` in the coordinates
`z_j = x_j + I y_j`. -/
theorem delBarCoeff_topDegreePrimitiveCoeff_univ_eq_inv_four_smul_sum {v : (ι → ℂ) → F}
    {z : ι → ℂ} (hv : ContDiffAt ℝ 2 v z) :
    delBarCoeff (topDegreePrimitiveCoeff v) univ z = (4 : ℂ)⁻¹ • ∑ j,
      (iteratedFDeriv ℝ 2 v z ![Pi.single j 1, Pi.single j 1] +
        iteratedFDeriv ℝ 2 v z ![Pi.single j I, Pi.single j I]) := by
  rw [delBarCoeff_topDegreePrimitiveCoeff_univ, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [conjWirtingerDeriv_wirtingerDeriv_self hv, ← Pi.single_smul, smul_eq_mul, mul_one]

/-- **Top-degree `bar∂`-exactness from the Poisson equation.** If `v` is `C^(m+1)`, `m ≥ 1`, on an
open set `Ω ⊆ ι → ℂ` and solves the Poisson equation `Δv = 4f` there, where
`Δv = ∑_j (∂²v/∂x_j² + ∂²v/∂y_j²)` is the real Laplacian in the coordinates `z_j = x_j + I y_j`,
then the top-degree form `f d(conj z_1) ∧ ⋯ ∧ d(conj z_n)` is the `bar∂` of a `(0,n-1)`-form with
`C^m` coefficients on `Ω`. -/
theorem exists_contDiffOn_delBarCoeff_univ_eq_of_sum_iteratedFDeriv_eq {Ω : Set (ι → ℂ)}
    (hΩ : IsOpen Ω) {m : WithTop ℕ∞} (hm : 1 ≤ m) {v f : (ι → ℂ) → F}
    (hv : ContDiffOn ℝ (m + 1) v Ω)
    (hvf : ∀ z ∈ Ω, ∑ j, (iteratedFDeriv ℝ 2 v z ![Pi.single j 1, Pi.single j 1] +
      iteratedFDeriv ℝ 2 v z ![Pi.single j I, Pi.single j I]) = (4 : ℂ) • f z) :
    ∃ u : Finset ι → (ι → ℂ) → F, (∀ J, ContDiffOn ℝ m (u J) Ω) ∧
      ∀ z ∈ Ω, delBarCoeff u univ z = f z := by
  have hv' {z : ι → ℂ} (hz : z ∈ Ω) : ContDiffAt ℝ (m + 1) v z := hv.contDiffAt (hΩ.mem_nhds hz)
  refine ⟨topDegreePrimitiveCoeff v, fun J z hz ↦
    (contDiffAt_topDegreePrimitiveCoeff (hv' hz) le_rfl J).contDiffWithinAt, fun z hz ↦ ?_⟩
  have h2 : (2 : WithTop ℕ∞) ≤ m + 1 := by
    simpa [one_add_one_eq_two] using add_le_add_left hm 1
  rw [delBarCoeff_topDegreePrimitiveCoeff_univ_eq_inv_four_smul_sum ((hv' hz).of_le h2), hvf z hz,
    smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]

end TauCeti
