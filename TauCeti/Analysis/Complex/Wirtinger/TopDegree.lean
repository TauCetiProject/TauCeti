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

On the coordinate space `ι → ℂ` of a finite linearly ordered index type `ι` with
`n = Fintype.card ι` elements, with coordinates `z_j = x_j + I y_j`, the top-degree
`bar∂`-equation reduces to the Poisson equation for the real Laplacian
`Δ = ∑_j (∂²/∂x_j² + ∂²/∂y_j²)`. Since `Δ = 4 ∑_j ∂²/∂(conj z_j) ∂z_j`
(`TauCeti.conjWirtingerDeriv_wirtingerDeriv_self`), for every `C²` function `v`

`bar∂ (∑_j (-1)^(j-1) ∂v/∂z_j d(conj z)_[j]) = (Δv / 4) d(conj z_1) ∧ ⋯ ∧ d(conj z_n)`,

where `d(conj z)_[j]` is the wedge product of all `d(conj z_i)` with `i ≠ j`, in increasing
order, and `j - 1` is the number of indices below `j`. Hence, on an open set where `Δv = 4f` can be
solved, the top-degree form `f d(conj z_1) ∧ ⋯ ∧ d(conj z_n)` is `bar∂`-exact with an explicit
primitive, as regular as `∂v`. Forms are recorded by their coefficient families, as for
`TauCeti.delBarCoeff`. Since `F` is arbitrary, this covers `(p,n)`-forms as well, through the
`(0,n)`-forms with coefficients in `Finset ι → F`, whose `bar∂` differs by the sign `(-1)^p`.

## Main declarations

* `TauCeti.topDegreeDelBarPrimitiveCoeff v`: the coefficients of the `(0,n-1)`-form
  `∑_j (-1)^(j-1) ∂v/∂z_j d(conj z)_[j]`.
* `TauCeti.delBarCoeff_topDegreeDelBarPrimitiveCoeff_univ`,
  `TauCeti.delBarCoeff_topDegreeDelBarPrimitiveCoeff_of_ne_univ`: its `bar∂` is
  `∑_j ∂²v/∂(conj z_j) ∂z_j d(conj z_1) ∧ ⋯ ∧ d(conj z_n)`.
* `TauCeti.delBarCoeff_topDegreeDelBarPrimitiveCoeff_univ_eq_inv_four_smul_sum`: for `C²`
  functions `v` this is `(Δv / 4) d(conj z_1) ∧ ⋯ ∧ d(conj z_n)`.
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

open Complex Finset Filter Topology

namespace TauCeti

variable {ι : Type*} [LinearOrder ι] [Fintype ι] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- The coefficients of the `(0,n-1)`-form `∑_j (-1)^(j-1) ∂v/∂z_j d(conj z)_[j]` on `ι → ℂ`,
where `n = Fintype.card ι`, `d(conj z)_[j]` is the wedge product of the `d(conj z_i)`, `i ≠ j`,
in increasing order and `j - 1` is the number of indices below `j`. The coefficient of
`d(conj z)_J` is `(-1)^#{i | i < j} ∂v/∂z_j` if `J` omits exactly the index `j`, and zero
otherwise. -/
noncomputable def topDegreeDelBarPrimitiveCoeff (v : (ι → ℂ) → F) (J : Finset ι) (z : ι → ℂ) :
    F :=
  ∑ j, if J = univ.erase j then (-1 : ℂ) ^ #{i | i < j} • wirtingerDeriv v z (Pi.single j 1)
    else 0

/-- The defining formula of `TauCeti.topDegreeDelBarPrimitiveCoeff`. -/
theorem topDegreeDelBarPrimitiveCoeff_def (v : (ι → ℂ) → F) (J : Finset ι) (z : ι → ℂ) :
    topDegreeDelBarPrimitiveCoeff v J z =
      ∑ j, if J = univ.erase j then (-1 : ℂ) ^ #{i | i < j} • wirtingerDeriv v z (Pi.single j 1)
        else 0 :=
  (rfl)

/-- The coefficient of `d(conj z)_[j]` in `topDegreeDelBarPrimitiveCoeff v` is
`(-1)^#{i | i < j} ∂v/∂z_j`. -/
@[simp]
theorem topDegreeDelBarPrimitiveCoeff_erase_univ (v : (ι → ℂ) → F) (j : ι) (z : ι → ℂ) :
    topDegreeDelBarPrimitiveCoeff v (univ.erase j) z =
      (-1 : ℂ) ^ #{i | i < j} • wirtingerDeriv v z (Pi.single j 1) := by
  rw [topDegreeDelBarPrimitiveCoeff_def, Finset.sum_eq_single j (fun k _ hkj ↦ ?_) (by simp)]
  · simp
  · simp [Finset.erase_inj _ (mem_univ j), Ne.symm hkj]

/-- The function-valued form of `TauCeti.topDegreeDelBarPrimitiveCoeff_erase_univ`, used to
differentiate the coefficient of `d(conj z)_[j]`. -/
private theorem topDegreeDelBarPrimitiveCoeff_erase_univ_eq_fun (v : (ι → ℂ) → F) (j : ι) :
    topDegreeDelBarPrimitiveCoeff v (univ.erase j) =
      (-1 : ℂ) ^ #{i | i < j} • fun y ↦ wirtingerDeriv v y (Pi.single j 1) :=
  funext (topDegreeDelBarPrimitiveCoeff_erase_univ v j)

/-- The coefficients of `topDegreeDelBarPrimitiveCoeff v` indexed by sets that do not omit
exactly one index vanish. -/
theorem topDegreeDelBarPrimitiveCoeff_of_forall_ne (v : (ι → ℂ) → F) {J : Finset ι}
    (hJ : ∀ j, J ≠ univ.erase j) : topDegreeDelBarPrimitiveCoeff v J = 0 := by
  ext z
  simp [topDegreeDelBarPrimitiveCoeff_def, hJ]

/-- The coefficients of `topDegreeDelBarPrimitiveCoeff v` outside degree `n - 1`, where
`n = Fintype.card ι`, vanish. -/
theorem topDegreeDelBarPrimitiveCoeff_of_card_add_one_ne (v : (ι → ℂ) → F) {J : Finset ι}
    (hJ : #J + 1 ≠ Fintype.card ι) : topDegreeDelBarPrimitiveCoeff v J = 0 := by
  refine topDegreeDelBarPrimitiveCoeff_of_forall_ne v fun j h ↦ hJ ?_
  rw [h, card_erase_of_mem (mem_univ j), card_univ,
    Nat.sub_add_cancel (Fintype.card_pos_iff.2 ⟨j⟩)]

/-- The top-degree coefficient of `topDegreeDelBarPrimitiveCoeff v` vanishes. -/
@[simp]
theorem topDegreeDelBarPrimitiveCoeff_univ (v : (ι → ℂ) → F) :
    topDegreeDelBarPrimitiveCoeff v univ = 0 :=
  topDegreeDelBarPrimitiveCoeff_of_forall_ne v fun j h ↦ by simpa using h.le (mem_univ j)

/-- The primitive built from the zero function vanishes. -/
@[simp]
theorem topDegreeDelBarPrimitiveCoeff_zero :
    topDegreeDelBarPrimitiveCoeff (0 : (ι → ℂ) → F) = 0 := by
  ext J z
  simp [topDegreeDelBarPrimitiveCoeff_def]

/-- The coefficients of `topDegreeDelBarPrimitiveCoeff v` at `z` only depend on the germ of `v`
at `z`. -/
theorem topDegreeDelBarPrimitiveCoeff_congr {v w : (ι → ℂ) → F} {z : ι → ℂ} (h : v =ᶠ[𝓝 z] w)
    (J : Finset ι) : topDegreeDelBarPrimitiveCoeff v J z = topDegreeDelBarPrimitiveCoeff w J z := by
  simp only [topDegreeDelBarPrimitiveCoeff_def, h.wirtingerDeriv_eq]

/-- `topDegreeDelBarPrimitiveCoeff` is additive on real-differentiable functions. -/
theorem topDegreeDelBarPrimitiveCoeff_add {v w : (ι → ℂ) → F} {z : ι → ℂ}
    (hv : DifferentiableAt ℝ v z) (hw : DifferentiableAt ℝ w z) (J : Finset ι) :
    topDegreeDelBarPrimitiveCoeff (v + w) J z =
      topDegreeDelBarPrimitiveCoeff v J z + topDegreeDelBarPrimitiveCoeff w J z := by
  simp only [topDegreeDelBarPrimitiveCoeff_def, wirtingerDeriv_add hv hw, ← sum_add_distrib]
  refine sum_congr rfl fun j _ ↦ ?_
  split_ifs <;> simp [smul_add]

/-- `topDegreeDelBarPrimitiveCoeff` commutes with subtraction of real-differentiable functions. -/
theorem topDegreeDelBarPrimitiveCoeff_sub {v w : (ι → ℂ) → F} {z : ι → ℂ}
    (hv : DifferentiableAt ℝ v z) (hw : DifferentiableAt ℝ w z) (J : Finset ι) :
    topDegreeDelBarPrimitiveCoeff (v - w) J z =
      topDegreeDelBarPrimitiveCoeff v J z - topDegreeDelBarPrimitiveCoeff w J z := by
  simp only [topDegreeDelBarPrimitiveCoeff_def, wirtingerDeriv_sub hv hw, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ ↦ ?_
  split_ifs <;> simp [smul_sub]

/-- `topDegreeDelBarPrimitiveCoeff` commutes with constant complex scaling. -/
theorem topDegreeDelBarPrimitiveCoeff_const_smul (c : ℂ) (v : (ι → ℂ) → F) :
    topDegreeDelBarPrimitiveCoeff (c • v) = c • topDegreeDelBarPrimitiveCoeff v := by
  ext J z
  simp only [topDegreeDelBarPrimitiveCoeff_def, wirtingerDeriv_const_smul, Pi.smul_apply,
    smul_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  split_ifs <;> simp [smul_comm c]

/-- `topDegreeDelBarPrimitiveCoeff` commutes with negation. -/
theorem topDegreeDelBarPrimitiveCoeff_neg (v : (ι → ℂ) → F) :
    topDegreeDelBarPrimitiveCoeff (-v) = -topDegreeDelBarPrimitiveCoeff v := by
  rw [← neg_one_smul ℂ v, topDegreeDelBarPrimitiveCoeff_const_smul, neg_one_smul]

/-- A coefficient of `topDegreeDelBarPrimitiveCoeff v` is `C^m` at a point where `v` is
`C^(m+1)`. -/
theorem _root_.ContDiffAt.topDegreeDelBarPrimitiveCoeff {v : (ι → ℂ) → F} {z : ι → ℂ}
    {m k : WithTop ℕ∞} (hv : ContDiffAt ℝ k v z) (hmk : m + 1 ≤ k) (J : Finset ι) :
    ContDiffAt ℝ m (topDegreeDelBarPrimitiveCoeff v J) z := by
  by_cases hJ : ∃ j, J = univ.erase j
  · obtain ⟨j, rfl⟩ := hJ
    rw [topDegreeDelBarPrimitiveCoeff_erase_univ_eq_fun]
    exact (hv.wirtingerDeriv_apply hmk (Pi.single j 1)).const_smul _
  · rw [topDegreeDelBarPrimitiveCoeff_of_forall_ne v (not_exists.1 hJ)]
    exact contDiffAt_const

/-- The coefficients of `topDegreeDelBarPrimitiveCoeff v` are `C^m` on an open set where `v` is
`C^(m+1)`. -/
theorem _root_.ContDiffOn.topDegreeDelBarPrimitiveCoeff_of_isOpen {v : (ι → ℂ) → F}
    {Ω : Set (ι → ℂ)} {m k : WithTop ℕ∞} (hv : ContDiffOn ℝ k v Ω) (hΩ : IsOpen Ω)
    (hmk : m + 1 ≤ k) (J : Finset ι) : ContDiffOn ℝ m (topDegreeDelBarPrimitiveCoeff v J) Ω :=
  fun _ hz ↦ ((hv.contDiffAt (hΩ.mem_nhds hz)).topDegreeDelBarPrimitiveCoeff hmk J).contDiffWithinAt

/-- The `bar∂` of `∑_j (-1)^(j-1) ∂v/∂z_j d(conj z)_[j]` has no coefficients below top degree. -/
theorem delBarCoeff_topDegreeDelBarPrimitiveCoeff_of_ne_univ (v : (ι → ℂ) → F) {I : Finset ι}
    (hI : I ≠ univ) : delBarCoeff (topDegreeDelBarPrimitiveCoeff v) I = 0 := by
  ext z
  rw [delBarCoeff_def, Pi.zero_apply]
  refine sum_eq_zero fun j hj ↦ ?_
  rw [topDegreeDelBarPrimitiveCoeff_of_card_add_one_ne v]
  · simp
  rw [card_erase_of_mem hj, Nat.sub_add_cancel (card_pos.2 ⟨j, hj⟩)]
  exact fun h ↦ hI (eq_univ_of_card I h)

/-- The `bar∂` of `∑_j (-1)^(j-1) ∂v/∂z_j d(conj z)_[j]` is
`∑_j ∂²v/∂(conj z_j) ∂z_j d(conj z_1) ∧ ⋯ ∧ d(conj z_n)`, where `n = Fintype.card ι`: the signs
of the primitive cancel those of `bar∂`. -/
theorem delBarCoeff_topDegreeDelBarPrimitiveCoeff_univ (v : (ι → ℂ) → F) (z : ι → ℂ) :
    delBarCoeff (topDegreeDelBarPrimitiveCoeff v) univ z =
      ∑ j, conjWirtingerDeriv (fun y ↦ wirtingerDeriv v y (Pi.single j 1)) z (Pi.single j 1) := by
  rw [delBarCoeff_def]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [topDegreeDelBarPrimitiveCoeff_erase_univ_eq_fun, conjWirtingerDeriv_const_smul]
  simp [smul_smul, ← mul_pow]

/-- **The top-degree `bar∂`-primitive.** For `v` that is `C²` at `z`, the `bar∂` of
`∑_j (-1)^(j-1) ∂v/∂z_j d(conj z)_[j]` is `(Δv / 4) d(conj z_1) ∧ ⋯ ∧ d(conj z_n)` at `z`, where
`n = Fintype.card ι` and `Δv = ∑_j (∂²v/∂x_j² + ∂²v/∂y_j²)` is the real Laplacian of `v` in the
coordinates `z_j = x_j + I y_j`. -/
theorem delBarCoeff_topDegreeDelBarPrimitiveCoeff_univ_eq_inv_four_smul_sum {v : (ι → ℂ) → F}
    {z : ι → ℂ} (hv : ContDiffAt ℝ 2 v z) :
    delBarCoeff (topDegreeDelBarPrimitiveCoeff v) univ z = (4 : ℂ)⁻¹ • ∑ j,
      (iteratedFDeriv ℝ 2 v z ![Pi.single j 1, Pi.single j 1] +
        iteratedFDeriv ℝ 2 v z ![Pi.single j I, Pi.single j I]) := by
  rw [delBarCoeff_topDegreeDelBarPrimitiveCoeff_univ, smul_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [conjWirtingerDeriv_wirtingerDeriv_self hv, ← Pi.single_smul, smul_eq_mul, mul_one]

/-- **Top-degree `bar∂`-exactness from the Poisson equation.** If `v` is `C^k`, `k ≥ 2`, on an
open set `Ω ⊆ ι → ℂ` and solves the Poisson equation `Δv = 4f` there, where
`Δv = ∑_j (∂²v/∂x_j² + ∂²v/∂y_j²)` is the real Laplacian in the coordinates `z_j = x_j + I y_j`,
then, with `n = Fintype.card ι`, the top-degree form `f d(conj z_1) ∧ ⋯ ∧ d(conj z_n)` is the
`bar∂` of a `(0,n-1)`-form with `C^m` coefficients on `Ω` for every `m` with `m + 1 ≤ k`. -/
theorem exists_contDiffOn_delBarCoeff_univ_eq_of_sum_iteratedFDeriv_eq {Ω : Set (ι → ℂ)}
    (hΩ : IsOpen Ω) {m k : WithTop ℕ∞} (hk : 2 ≤ k) (hmk : m + 1 ≤ k) {v f : (ι → ℂ) → F}
    (hv : ContDiffOn ℝ k v Ω)
    (hvf : ∀ z ∈ Ω, ∑ j, (iteratedFDeriv ℝ 2 v z ![Pi.single j 1, Pi.single j 1] +
      iteratedFDeriv ℝ 2 v z ![Pi.single j I, Pi.single j I]) = (4 : ℂ) • f z) :
    ∃ u : Finset ι → (ι → ℂ) → F, (∀ J, ContDiffOn ℝ m (u J) Ω) ∧
      ∀ z ∈ Ω, delBarCoeff u univ z = f z := by
  refine ⟨topDegreeDelBarPrimitiveCoeff v, hv.topDegreeDelBarPrimitiveCoeff_of_isOpen hΩ hmk,
    fun z hz ↦ ?_⟩
  rw [delBarCoeff_topDegreeDelBarPrimitiveCoeff_univ_eq_inv_four_smul_sum
    ((hv.contDiffAt (hΩ.mem_nhds hz)).of_le hk), hvf z hz, smul_smul, inv_mul_cancel₀ (by norm_num),
    one_smul]

end TauCeti
