/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: the Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.Lattice
import TauCeti.Analysis.SpecialFunctions.Log.BirkhoffCrossRatio

/-!
# Hilbert's projective metric and Birkhoff's contraction theorem

For two vectors `x y : ι → ℝ` over a finite type, Hilbert's projective metric is
`TauCeti.hilbertProjectiveDist x y = ⨆ i, ⨆ j, log (x i * y j / (y i * x j))`. On strictly
positive vectors this is the classical `log (max_i (x i / y i) / min_i (x i / y i))`: it is a
pseudometric which vanishes exactly on proportional vectors, so it is a metric on the rays of the
positive orthant. It is unchanged by rescaling either argument, by a common diagonal scaling of
both arguments, and by taking entrywise inverses.

A matrix `K` with strictly positive entries maps the positive orthant into itself, and its
*projective diameter* `Matrix.projectiveDiameter K` is the Hilbert diameter of its columns,
`Δ(K) = ⨆ i i' j j', log (K i j * K i' j' / (K i j' * K i' j))`. Every image `K *ᵥ u` of a
nonnegative vector lies within `Δ(K)` of every other. Birkhoff's theorem sharpens this to a
contraction: `K` contracts Hilbert's projective metric by the factor `tanh (Δ(K) / 4) < 1`.

Diagonal scaling invariance, inversion invariance and the contraction of `K` and of its transpose
are what make the alternating row and column normalisations of a positive kernel (the Sinkhorn
iteration) a contraction for Hilbert's projective metric.

## Main definitions

* `TauCeti.hilbertProjectiveDist x y`: Hilbert's projective metric between two real vectors.
* `Matrix.projectiveDiameter K`: Birkhoff's projective diameter of a matrix.

## Main results

* `TauCeti.hilbertProjectiveDist_triangle`, `TauCeti.hilbertProjectiveDist_comm` and
  `TauCeti.hilbertProjectiveDist_eq_zero_iff`: the pseudometric laws, with zero distance exactly
  for proportional positive vectors.
* `TauCeti.hilbertProjectiveDist_smul_left`, `TauCeti.hilbertProjectiveDist_mul_left` and
  `TauCeti.hilbertProjectiveDist_inv`: invariance under rescaling, diagonal scaling and inversion.
* `Matrix.hilbertProjectiveDist_mulVec_le_projectiveDiameter`: the images of nonnegative vectors
  under a positive matrix lie within its projective diameter of each other.
* `Matrix.hilbertProjectiveDist_mulVec_le`: **Birkhoff's contraction theorem**,
  `d (K *ᵥ x) (K *ᵥ y) ≤ tanh (Δ(K) / 4) * d x y` for a strictly positive matrix `K` and strictly
  positive vectors `x` and `y`.

## References

* G. Birkhoff, *Extensions of Jentzsch's theorem*, Trans. Amer. Math. Soc. 85 (1957), 219--227.
* P. J. Bushell, *Hilbert's metric and positive contraction mappings in a Banach space*,
  Arch. Rational Mech. Anal. 52 (1973), 330--338.
* E. Seneta, *Non-negative Matrices and Markov Chains*, Springer (2006), Chapter 3.
* G. Peyré and M. Cuturi, *Computational Optimal Transport*, Found. Trends Mach. Learn. 11 (2019),
  Section 4.2, for the use of this contraction in the Sinkhorn iteration.
-/
public section

open Real

namespace TauCeti

variable {ι : Type*}

/-! ### Hilbert's projective metric -/

/-- **Hilbert's projective metric** between two real vectors, the supremum over all pairs of
indices of the logarithm of the cross ratio `x i * y j / (y i * x j)`.

For strictly positive `x` and `y` this is `log (max_i (x i / y i) / min_i (x i / y i))`; the
pseudometric laws below are stated under the positivity they use. The formula is defined for all
real vectors, with Mathlib's conventions `a / 0 = 0` and `Real.log 0 = 0`. -/
noncomputable def hilbertProjectiveDist (x y : ι → ℝ) : ℝ :=
  ⨆ i, ⨆ j, log (x i * y j / (y i * x j))

/-- The defining formula of Hilbert's projective metric. -/
theorem hilbertProjectiveDist_def (x y : ι → ℝ) :
    hilbertProjectiveDist x y = ⨆ i, ⨆ j, log (x i * y j / (y i * x j)) :=
  -- `(rfl)` rather than `rfl`: this lemma is the supported unfolding interface, so the body of
  -- `hilbertProjectiveDist` need not be exposed.
  (rfl)

/-- Each logarithmic cross ratio is at most Hilbert's projective metric. -/
theorem log_le_hilbertProjectiveDist [Finite ι] (x y : ι → ℝ) (i j : ι) :
    log (x i * y j / (y i * x j)) ≤ hilbertProjectiveDist x y :=
  le_ciSup_of_le (Set.finite_range _).bddAbove i <|
    le_ciSup (Set.finite_range fun j ↦ log (x i * y j / (y i * x j))).bddAbove j

/-- Hilbert's projective metric is at most any nonnegative bound on all logarithmic cross ratios. -/
theorem hilbertProjectiveDist_le {x y : ι → ℝ} {C : ℝ}
    (h : ∀ i j, log (x i * y j / (y i * x j)) ≤ C) (hC : 0 ≤ C) :
    hilbertProjectiveDist x y ≤ C :=
  Real.iSup_le (fun i ↦ Real.iSup_le (h i) hC) hC

/-- Hilbert's projective metric is nonnegative: the diagonal cross ratios have logarithm `0`. -/
theorem hilbertProjectiveDist_nonneg [Finite ι] (x y : ι → ℝ) :
    0 ≤ hilbertProjectiveDist x y :=
  Real.iSup_nonneg fun i ↦ le_ciSup_of_le (Set.finite_range _).bddAbove i <| by
    rw [mul_comm (y i), log_div_self]

/-- Every vector is at Hilbert distance `0` from itself. -/
@[simp]
theorem hilbertProjectiveDist_self (x : ι → ℝ) : hilbertProjectiveDist x x = 0 := by
  simp only [hilbertProjectiveDist_def, log_div_self, Real.iSup_const_zero]

/-- Hilbert's projective metric is symmetric. -/
theorem hilbertProjectiveDist_comm [Finite ι] (x y : ι → ℝ) :
    hilbertProjectiveDist x y = hilbertProjectiveDist y x := by
  have key : ∀ x y : ι → ℝ, hilbertProjectiveDist y x ≤ hilbertProjectiveDist x y :=
    fun x y ↦ hilbertProjectiveDist_le (fun i j ↦ by
      rw [mul_comm (y i), mul_comm (x i)]
      exact log_le_hilbertProjectiveDist x y j i) (hilbertProjectiveDist_nonneg x y)
  exact le_antisymm (key y x) (key x y)

/-- The **triangle inequality** for Hilbert's projective metric. Only the middle vector needs
nonzero entries. -/
theorem hilbertProjectiveDist_triangle [Finite ι] (x z : ι → ℝ) {y : ι → ℝ}
    (hy : ∀ i, y i ≠ 0) :
    hilbertProjectiveDist x z ≤ hilbertProjectiveDist x y + hilbertProjectiveDist y z := by
  refine hilbertProjectiveDist_le (fun i j ↦ ?_)
    (add_nonneg (hilbertProjectiveDist_nonneg x y) (hilbertProjectiveDist_nonneg y z))
  have hxz : x i * z j / (z i * x j) =
      x i * y j / (y i * x j) * (y i * z j / (z i * y j)) := by
    rw [← mul_div_mul_left (x i * z j) (z i * x j) (mul_ne_zero (hy i) (hy j))]
    ring
  rw [hxz]
  rcases eq_or_ne (x i * y j / (y i * x j)) 0 with h₁ | h₁
  · rw [h₁, zero_mul, log_zero]
    exact add_nonneg (hilbertProjectiveDist_nonneg x y) (hilbertProjectiveDist_nonneg y z)
  rcases eq_or_ne (y i * z j / (z i * y j)) 0 with h₂ | h₂
  · rw [h₂, mul_zero, log_zero]
    exact add_nonneg (hilbertProjectiveDist_nonneg x y) (hilbertProjectiveDist_nonneg y z)
  rw [log_mul h₁ h₂]
  exact add_le_add (log_le_hilbertProjectiveDist x y i j) (log_le_hilbertProjectiveDist y z i j)

/-- Rescaling the first vector by a nonzero scalar does not change Hilbert's projective metric. -/
@[simp]
theorem hilbertProjectiveDist_smul_left {c : ℝ} (hc : c ≠ 0) (x y : ι → ℝ) :
    hilbertProjectiveDist (c • x) y = hilbertProjectiveDist x y := by
  simp only [hilbertProjectiveDist_def, Pi.smul_apply, smul_eq_mul]
  refine iSup_congr fun i ↦ iSup_congr fun j ↦ congrArg log ?_
  rw [← mul_div_mul_left (x i * y j) (y i * x j) hc]
  ring

/-- Rescaling the second vector by a nonzero scalar does not change Hilbert's projective
metric. -/
@[simp]
theorem hilbertProjectiveDist_smul_right {c : ℝ} (hc : c ≠ 0) (x y : ι → ℝ) :
    hilbertProjectiveDist x (c • y) = hilbertProjectiveDist x y := by
  simp only [hilbertProjectiveDist_def, Pi.smul_apply, smul_eq_mul]
  refine iSup_congr fun i ↦ iSup_congr fun j ↦ congrArg log ?_
  rw [← mul_div_mul_left (x i * y j) (y i * x j) hc]
  ring

/-- A common diagonal scaling by a vector with nonzero entries does not change Hilbert's
projective metric. -/
theorem hilbertProjectiveDist_mul_left {w : ι → ℝ} (hw : ∀ i, w i ≠ 0) (x y : ι → ℝ) :
    hilbertProjectiveDist (w * x) (w * y) = hilbertProjectiveDist x y := by
  simp only [hilbertProjectiveDist_def, Pi.mul_apply]
  refine iSup_congr fun i ↦ iSup_congr fun j ↦ congrArg log ?_
  rw [← mul_div_mul_left (x i * y j) (y i * x j) (mul_ne_zero (hw i) (hw j))]
  ring

/-- Taking entrywise inverses does not change Hilbert's projective metric. -/
@[simp]
theorem hilbertProjectiveDist_inv [Finite ι] (x y : ι → ℝ) :
    hilbertProjectiveDist x⁻¹ y⁻¹ = hilbertProjectiveDist x y := by
  rw [hilbertProjectiveDist_comm x y]
  simp only [hilbertProjectiveDist_def, Pi.inv_apply]
  refine iSup_congr fun i ↦ iSup_congr fun j ↦ congrArg log ?_
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  ring

/-- Hilbert's projective metric vanishes on two strictly positive vectors exactly when they are
proportional. -/
theorem hilbertProjectiveDist_eq_zero_iff [Finite ι] {x y : ι → ℝ} (hx : ∀ i, 0 < x i)
    (hy : ∀ i, 0 < y i) :
    hilbertProjectiveDist x y = 0 ↔ ∃ c : ℝ, 0 < c ∧ x = c • y := by
  constructor
  · intro h
    -- every cross ratio is at most `1`, hence by symmetry equal to `1`
    have hle : ∀ i j, x i * y j ≤ y i * x j := fun i j ↦ by
      have h₁ := (log_le_hilbertProjectiveDist x y i j).trans h.le
      rwa [log_nonpos_iff (div_pos (mul_pos (hx i) (hy j)) (mul_pos (hy i) (hx j))).le,
        div_le_one (mul_pos (hy i) (hx j))] at h₁
    rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
    · exact ⟨1, one_pos, funext fun i ↦ hι.elim i⟩
    refine ⟨x i₀ / y i₀, div_pos (hx i₀) (hy i₀), funext fun j ↦ ?_⟩
    have := le_antisymm (hle i₀ j) (by linarith [hle j i₀])
    rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff (hy i₀).ne']
    linarith
  · rintro ⟨c, hc, rfl⟩
    rw [hilbertProjectiveDist_smul_left hc.ne', hilbertProjectiveDist_self]

end TauCeti

/-! ### Birkhoff's contraction theorem -/

namespace Matrix

open TauCeti

variable {ι κ : Type*}

/-- **Birkhoff's projective diameter** of a matrix: the Hilbert projective diameter of its columns,
`⨆ j, ⨆ j', hilbertProjectiveDist (fun i ↦ K i j) (fun i ↦ K i j')`.

For a matrix with strictly positive entries this is the classical
`Δ(K) = log max_{i, i', j, j'} (K i j * K i' j' / (K i j' * K i' j))`, and it bounds the Hilbert
distance between any two images of nonnegative vectors under `K`. -/
noncomputable def projectiveDiameter (K : Matrix ι κ ℝ) : ℝ :=
  ⨆ j, ⨆ j', hilbertProjectiveDist (fun i ↦ K i j) (fun i ↦ K i j')

/-- The defining formula of the projective diameter. -/
theorem projectiveDiameter_def (K : Matrix ι κ ℝ) :
    K.projectiveDiameter = ⨆ j, ⨆ j', hilbertProjectiveDist (fun i ↦ K i j) (fun i ↦ K i j') :=
  -- `(rfl)` rather than `rfl`: this lemma is the supported unfolding interface, so the body of
  -- `projectiveDiameter` need not be exposed.
  (rfl)

section Finite

variable [Finite ι] [Finite κ]

/-- Each logarithmic cross ratio of the entries of `K` is at most its projective diameter. -/
theorem log_le_projectiveDiameter (K : Matrix ι κ ℝ) (i i' : ι) (j j' : κ) :
    log (K i j * K i' j' / (K i j' * K i' j)) ≤ K.projectiveDiameter :=
  (log_le_hilbertProjectiveDist (fun i ↦ K i j) (fun i ↦ K i j') i i').trans <|
    le_ciSup_of_le (Set.finite_range _).bddAbove j <|
      le_ciSup (Set.finite_range fun j' ↦
        hilbertProjectiveDist (fun i ↦ K i j) (fun i ↦ K i j')).bddAbove j'

omit [Finite κ] in
/-- The projective diameter of a matrix is nonnegative. -/
theorem projectiveDiameter_nonneg (K : Matrix ι κ ℝ) : 0 ≤ K.projectiveDiameter :=
  Real.iSup_nonneg fun _ ↦ Real.iSup_nonneg fun _ ↦ hilbertProjectiveDist_nonneg _ _

omit [Finite ι] [Finite κ] in
/-- The projective diameter of a matrix is at most any nonnegative bound on all logarithmic cross
ratios of its entries. -/
theorem projectiveDiameter_le {K : Matrix ι κ ℝ} {C : ℝ}
    (h : ∀ i i' j j', log (K i j * K i' j' / (K i j' * K i' j)) ≤ C) (hC : 0 ≤ C) :
    K.projectiveDiameter ≤ C :=
  Real.iSup_le (fun j ↦ Real.iSup_le (fun j' ↦ hilbertProjectiveDist_le (h · · j j') hC) hC) hC

/-- A matrix and its transpose have the same projective diameter: both are the supremum of the
same logarithmic cross ratios of entries. -/
@[simp]
theorem projectiveDiameter_transpose (K : Matrix ι κ ℝ) :
    Kᵀ.projectiveDiameter = K.projectiveDiameter := by
  refine le_antisymm (projectiveDiameter_le (fun j j' i i' ↦ ?_) (projectiveDiameter_nonneg K))
    (projectiveDiameter_le (fun i i' j j' ↦ ?_) (projectiveDiameter_nonneg Kᵀ))
  · rw [transpose_apply, transpose_apply, transpose_apply, transpose_apply, mul_comm (K i' j)]
    exact log_le_projectiveDiameter K i i' j j'
  · have := log_le_projectiveDiameter Kᵀ j j' i i'
    rwa [transpose_apply, transpose_apply, transpose_apply, transpose_apply,
      mul_comm (K i' j)] at this

end Finite

variable [Finite ι] [Fintype κ]

/-- The cross-ratio form of the projective diameter bound: for nonnegative `u` and `v`,
`(K *ᵥ u) i * (K *ᵥ v) i' ≤ exp Δ(K) * ((K *ᵥ v) i * (K *ᵥ u) i')`. -/
private theorem mulVec_mul_mulVec_le {K : Matrix ι κ ℝ} (hK : ∀ i j, 0 < K i j) {u v : κ → ℝ}
    (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j) (i i' : ι) :
    (K *ᵥ u) i * (K *ᵥ v) i' ≤ exp K.projectiveDiameter * ((K *ᵥ v) i * (K *ᵥ u) i') := by
  have hcross : ∀ j j', K i j * K i' j' ≤ exp K.projectiveDiameter * (K i j' * K i' j) :=
    fun j j' ↦ by
      have hpos := mul_pos (hK i j') (hK i' j)
      rw [← div_le_iff₀ hpos, ← log_le_iff_le_exp (div_pos (mul_pos (hK i j) (hK i' j')) hpos)]
      exact log_le_projectiveDiameter K i i' j j'
  simp only [mulVec, dotProduct]
  calc (∑ j, K i j * u j) * ∑ j', K i' j' * v j'
      = ∑ j, ∑ j', (K i j * K i' j') * (u j * v j') := by
        rw [Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
    _ ≤ ∑ j, ∑ j', exp K.projectiveDiameter * (K i j' * K i' j) * (u j * v j') :=
        Finset.sum_le_sum fun j _ ↦ Finset.sum_le_sum fun j' _ ↦
          mul_le_mul_of_nonneg_right (hcross j j') (mul_nonneg (hu j) (hv j'))
    _ = exp K.projectiveDiameter * ((∑ j', K i j' * v j') * ∑ j, K i' j * u j) := by
        rw [Finset.sum_mul_sum, Finset.sum_comm, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ ↦ by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- The images of two nonnegative vectors under a matrix with strictly positive entries lie within
its projective diameter of each other. -/
theorem hilbertProjectiveDist_mulVec_le_projectiveDiameter {K : Matrix ι κ ℝ}
    (hK : ∀ i j, 0 < K i j) {u v : κ → ℝ} (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j) :
    hilbertProjectiveDist (K *ᵥ u) (K *ᵥ v) ≤ K.projectiveDiameter := by
  have hnonneg : ∀ {w : κ → ℝ}, (∀ j, 0 ≤ w j) → ∀ i, 0 ≤ (K *ᵥ w) i := fun hw i ↦
    Finset.sum_nonneg fun j _ ↦ mul_nonneg (hK i j).le (hw j)
  refine hilbertProjectiveDist_le (fun i i' ↦ ?_) (projectiveDiameter_nonneg K)
  set r := (K *ᵥ u) i * (K *ᵥ v) i' / ((K *ᵥ v) i * (K *ᵥ u) i')
  rcases eq_or_ne r 0 with hr | hr
  · rw [hr, log_zero]
    exact projectiveDiameter_nonneg K
  have hden : 0 < (K *ᵥ v) i * (K *ᵥ u) i' :=
    (mul_nonneg (hnonneg hv i) (hnonneg hu i')).lt_of_ne fun h ↦ hr (by simp [r, ← h])
  have hr_pos : 0 < r :=
    (div_nonneg (mul_nonneg (hnonneg hu i) (hnonneg hv i')) hden.le).lt_of_ne hr.symm
  rw [log_le_iff_le_exp hr_pos, div_le_iff₀ hden]
  exact mulVec_mul_mulVec_le hK hu hv i i'

/- The proof of Birkhoff's theorem follows the classical reduction to two dimensions. With
`m ≤ x j / y j ≤ M`, the vectors `x - m • y` and `M • y - x` are nonnegative, so their images
`α` and `β` under `K` satisfy the cross-ratio bound `α i * β i' ≤ exp Δ(K) * β i * α i'`. Writing
`K *ᵥ x` and `K *ᵥ y` in terms of `α` and `β` turns each cross ratio of the images into a
two-dimensional quantity bounded by `((1 + λ s) / (λ + s)) ^ 2`, where `λ = exp (Δ(K) / 2)` and
`s ^ 2 = M / m` (`TauCeti.birkhoff_cross_ratio_le`), and the concavity estimate
`log ((1 + λ s) / (λ + s)) ≤ tanh (Δ(K) / 4) * log s`
(`TauCeti.log_one_add_mul_exp_div_add_exp_le`) finishes the proof
(`TauCeti.log_birkhoff_cross_ratio_le`). -/

/-- The cross-ratio estimate behind Birkhoff's theorem, for `m * y ≤ x ≤ M * y` with both bounds
strict somewhere: every logarithmic cross ratio of `K *ᵥ x` and `K *ᵥ y` is at most
`(l - 1) / (l + 1) * log (M / m)`, where `l = exp (Δ(K) / 2)`. -/
private theorem log_cross_mulVec_le {K : Matrix ι κ ℝ} (hK : ∀ i j, 0 < K i j) {x y : κ → ℝ}
    (hy : ∀ j, 0 < y j) {m M : ℝ} (hm : 0 < m) (hmx : ∀ j, m * y j ≤ x j)
    (hxM : ∀ j, x j ≤ M * y j) {j₁ j₂ : κ} (hj₁ : m * y j₁ < x j₁) (hj₂ : x j₂ < M * y j₂)
    (i i' : ι) :
    log ((K *ᵥ x) i * (K *ᵥ y) i' / ((K *ᵥ y) i * (K *ᵥ x) i')) ≤
      (exp (K.projectiveDiameter / 2) - 1) / (exp (K.projectiveDiameter / 2) + 1) *
        log (M / m) := by
  have hmM : m < M := lt_of_mul_lt_mul_right (hj₁.trans_le (hxM j₁)) (hy j₁).le
  -- the images `α` and `β` of the nonnegative vectors `x - m • y` and `M • y - x`
  have hu : ∀ j, 0 ≤ (x - m • y) j := fun j ↦ by simpa using hmx j
  have hv : ∀ j, 0 ≤ (M • y - x) j := fun j ↦ by simpa using hxM j
  have hpos : ∀ {w : κ → ℝ}, (∀ j, 0 ≤ w j) → ∀ {j₀}, 0 < w j₀ → ∀ i, 0 < (K *ᵥ w) i :=
    fun hw j₀ hj₀ i ↦ Finset.sum_pos' (fun j _ ↦ mul_nonneg (hK i j).le (hw j))
      ⟨j₀, Finset.mem_univ j₀, mul_pos (hK i j₀) hj₀⟩
  have hα := hpos hu (j₀ := j₁) (by simpa using hj₁)
  have hβ := hpos hv (j₀ := j₂) (by simpa using hj₂)
  have hcross := mulVec_mul_mulVec_le hK hu hv i i'
  rw [← add_halves K.projectiveDiameter, exp_add, ← sq] at hcross
  have key := log_birkhoff_cross_ratio_le (R := M / m) (hα i) (hβ i) (hα i') (hβ i')
    ((one_le_div hm).2 hmM.le) (one_le_exp (by linarith [projectiveDiameter_nonneg K])) hcross
  -- `(M / m) • α + β = (M - m) / m • K *ᵥ x` and `α + β = (M - m) • K *ᵥ y`
  have hcongr : ∀ i, M / m * (K *ᵥ (x - m • y)) i + (K *ᵥ (M • y - x)) i =
      (M - m) / m * (K *ᵥ x) i ∧
      (K *ᵥ (x - m • y)) i + (K *ᵥ (M • y - x)) i = (M - m) * (K *ᵥ y) i := fun i ↦ by
    simp only [mulVec_sub, mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    constructor
    · field_simp
      ring
    · ring
  rw [(hcongr i).1, (hcongr i).2, (hcongr i').1, (hcongr i').2] at key
  have hc : (M - m) / m * (M - m) ≠ 0 := by
    have := sub_pos.2 hmM
    positivity
  convert key using 2
  rw [← mul_div_mul_left ((K *ᵥ x) i * (K *ᵥ y) i') ((K *ᵥ y) i * (K *ᵥ x) i') hc]
  ring

/-- **Birkhoff's contraction theorem.** A matrix `K` with strictly positive entries contracts
Hilbert's projective metric between strictly positive vectors by the factor
`tanh (K.projectiveDiameter / 4)`, which is strictly less than `1`. -/
theorem hilbertProjectiveDist_mulVec_le {K : Matrix ι κ ℝ} (hK : ∀ i j, 0 < K i j)
    {x y : κ → ℝ} (hx : ∀ j, 0 < x j) (hy : ∀ j, 0 < y j) :
    hilbertProjectiveDist (K *ᵥ x) (K *ᵥ y) ≤
      tanh (K.projectiveDiameter / 4) * hilbertProjectiveDist x y := by
  -- `tanh (Δ / 4) = (l - 1) / (l + 1)` for `l = exp (Δ / 2)`
  have htanh : tanh (K.projectiveDiameter / 4) =
      (exp (K.projectiveDiameter / 2) - 1) / (exp (K.projectiveDiameter / 2) + 1) := by
    have h : exp (K.projectiveDiameter / 2) =
        exp (K.projectiveDiameter / 4) * exp (K.projectiveDiameter / 4) := by
      rw [← exp_add]
      ring_nf
    have := exp_pos (K.projectiveDiameter / 4)
    rw [tanh_eq, exp_neg, h]
    field_simp
  have hk : 0 ≤ tanh (K.projectiveDiameter / 4) := by
    have := one_le_exp (by linarith [projectiveDiameter_nonneg K] : 0 ≤ K.projectiveDiameter / 2)
    rw [htanh]
    exact div_nonneg (by linarith) (by linarith)
  have hkd := mul_nonneg hk (hilbertProjectiveDist_nonneg x y)
  refine hilbertProjectiveDist_le (fun i i' ↦ ?_) hkd
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · simpa [mulVec, dotProduct, Finset.univ_eq_empty] using hkd
  -- the extreme ratios `m ≤ x j / y j ≤ M`, attained at `j₂` and `j₁`
  obtain ⟨j₁, hj₁⟩ := Finite.exists_max fun j ↦ x j / y j
  obtain ⟨j₂, hj₂⟩ := Finite.exists_min fun j ↦ x j / y j
  set M := x j₁ / y j₁
  set m := x j₂ / y j₂
  have hm : 0 < m := div_pos (hx j₂) (hy j₂)
  have hmM : m ≤ M := hj₂ j₁
  rcases hmM.eq_or_lt with hmM | hmM
  · -- `x = m • y`, so the images are proportional
    have hxy : x = m • y := funext fun j ↦ by
      have := le_antisymm ((hj₁ j).trans hmM.ge) (hj₂ j)
      rw [Pi.smul_apply, smul_eq_mul, ← this, div_mul_cancel₀ _ (hy j).ne']
    calc log ((K *ᵥ x) i * (K *ᵥ y) i' / ((K *ᵥ y) i * (K *ᵥ x) i'))
        ≤ hilbertProjectiveDist (K *ᵥ x) (K *ᵥ y) := log_le_hilbertProjectiveDist _ _ i i'
      _ = 0 := by rw [hxy, mulVec_smul, hilbertProjectiveDist_smul_left hm.ne',
          hilbertProjectiveDist_self]
      _ ≤ _ := hkd
  have hd : log (M / m) ≤ hilbertProjectiveDist x y := by
    rw [div_div_div_eq]
    exact log_le_hilbertProjectiveDist x y j₁ j₂
  rw [htanh]
  refine (log_cross_mulVec_le hK hy hm (fun j ↦ (le_div_iff₀ (hy j)).1 (hj₂ j))
    (fun j ↦ (div_le_iff₀ (hy j)).1 (hj₁ j)) (j₁ := j₁) (j₂ := j₂)
    ((lt_div_iff₀ (hy j₁)).1 hmM) ((div_lt_iff₀ (hy j₂)).1 hmM) i i').trans ?_
  rw [htanh] at hk
  exact mul_le_mul_of_nonneg_left hd hk

end Matrix
