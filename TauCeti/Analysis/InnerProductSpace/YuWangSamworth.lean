/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.CourantFischer
public import TauCeti.Analysis.InnerProductSpace.HoffmanWielandt

/-!
# Population-gap residual bounds for corresponding eigenblocks

Let `T` (the population operator) and `S` (its perturbation) be symmetric endomorphisms of an
`n`-dimensional inner product space over `ℝ` or `ℂ`, with decreasingly ordered eigenvalues
`λ₀ ≥ ⋯ ≥ λₙ₋₁` of `T`, `μ₀ ≥ ⋯ ≥ μₙ₋₁` of `S`, and orthonormal eigenbases `(vₖ)` of `T` and
`(uⱼ)` of `S`. Fix an index block `s`. The Yu–Wang–Samworth variant of the Davis–Kahan theorem
measures the motion of the eigenblock `(uⱼ)_{j ∈ s}` away from `(vⱼ)_{j ∈ s}` by the cross-block
overlap `∑_{j ∈ s} ∑_{k ∉ s} |⟪vₖ, uⱼ⟫|²`, which is the squared Frobenius sine of the angles
between the two eigenblocks. Unlike the classical theorem, its gap hypothesis is placed on the
population spectrum alone: `Δ ≤ |λⱼ - λₖ|` for `j ∈ s` and `k ∉ s`.

The argument runs through the *residual columns* `Rⱼ = λⱼ uⱼ - T uⱼ`, which pair a population
eigenvalue with a perturbed eigenvector, and sandwiches `∑_{j ∈ s} ‖Rⱼ‖²` between the overlap and
the size of `S - T`.

* Below, in the eigenbasis `(vₖ)`, `‖c x - T x‖² = ∑ₖ (c - λₖ)² |⟪vₖ, x⟫|²`; so the population
  gap gives `Δ² ∑_{j ∈ s} ∑_{k ∉ s} |⟪vₖ, uⱼ⟫|² ≤ ∑_{j ∈ s} ‖Rⱼ‖²`. This holds with any vectors
  in place of the `uⱼ`.
* Above, `Rⱼ = (λⱼ - μⱼ) uⱼ + (S - T) uⱼ`. The Hoffman–Wielandt inequality bounds the
  eigenvalue displacements in Frobenius norm, which gives `∑_{j ∈ s} ‖Rⱼ‖² ≤ 4 ‖S - T‖_F²`;
  Weyl's inequality bounds each of them by `ε` when `‖(S - T) x‖ ≤ ε ‖x‖`, which gives
  `∑_{j ∈ s} ‖Rⱼ‖² ≤ 4 |s| ε²`.

Combining the two sides bounds `Δ² ∑_{j ∈ s} ∑_{k ∉ s} |⟪vₖ, uⱼ⟫|²` by both `4 ‖S - T‖_F²` and
`4 |s| ε²`, with no gap assumed in the spectrum of `S`.

## Main statements

* `LinearMap.IsSymmetric.norm_smul_sub_apply_sq_eq_sum`: the eigenbasis expansion
  `‖c x - T x‖² = ∑ₖ (c - λₖ)² |⟪vₖ, x⟫|²`.
* `LinearMap.IsSymmetric.sq_mul_sum_sum_norm_inner_sq_le_sum_norm_smul_sub_apply_sq`: the lower
  residual bound `Δ² ∑_{j ∈ s} ∑_{k ∉ s} |⟪vₖ, wⱼ⟫|² ≤ ∑_{j ∈ s} ‖λⱼ wⱼ - T wⱼ‖²`.
* `LinearMap.IsSymmetric.smul_sub_apply_eigenvectorBasis`: the residual decomposition
  `c uⱼ - T uⱼ = (c - μⱼ) uⱼ + (S - T) uⱼ`, with the norm form
  `LinearMap.IsSymmetric.norm_smul_sub_apply_eigenvectorBasis_le`.
* `LinearMap.IsSymmetric.sum_norm_smul_sub_apply_eigenvectorBasis_sq_le_four_mul_frobenius_sq`
  and `LinearMap.IsSymmetric.sum_norm_smul_sub_apply_eigenvectorBasis_sq_le_four_mul_card_mul_sq`:
  the Frobenius and operator-norm upper residual bounds.
* `LinearMap.IsSymmetric.sq_mul_sum_sum_norm_inner_sq_le_four_mul_frobenius_sq` and
  `LinearMap.IsSymmetric.sq_mul_sum_sum_norm_inner_sq_le_four_mul_card_mul_sq`: the
  population-gap bounds on the cross-block overlap.

## References

* Y. Yu, T. Wang, R. J. Samworth, *A useful variant of the Davis–Kahan theorem for statisticians*,
  Biometrika **102** (2015), 315–323, Theorem 1 and its proof.
* C. Davis, W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*, SIAM J. Numer.
  Anal. **7** (1970), 1–46.
-/

public section

open Module (finrank)
open scoped InnerProductSpace
open TauCeti.UnitarilyInvariantSeminorm (sq_frobenius_apply)

namespace LinearMap.IsSymmetric

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {T S : E →ₗ[𝕜] E} {n : ℕ}

/-! ### The lower residual bound -/

/-- **Eigenbasis expansion of a shifted residual.** For symmetric `T` with eigenvalues `λₖ` and
orthonormal eigenbasis `(vₖ)`, every real `c` and vector `x` satisfy
`‖c x - T x‖² = ∑ₖ (c - λₖ)² |⟪vₖ, x⟫|²`. -/
theorem norm_smul_sub_apply_sq_eq_sum (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (c : ℝ)
    (x : E) :
    ‖(c : 𝕜) • x - T x‖ ^ 2 =
      ∑ k, (c - hT.eigenvalues hn k) ^ 2 * ‖⟪hT.eigenvectorBasis hn k, x⟫_𝕜‖ ^ 2 := by
  rw [← (hT.eigenvectorBasis hn).sum_sq_norm_inner_right]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [inner_sub_right, inner_smul_right, ← hT, hT.apply_eigenvectorBasis]
  simp [inner_smul_left, ← sub_mul, norm_mul, mul_pow, ← RCLike.ofReal_sub, -map_sub]

/-- **Gap bound for one shifted residual.** If `c` is at distance at least `Δ ≥ 0` from every
eigenvalue `λₖ` of `T` with `k ∈ t`, then `Δ² ∑_{k ∈ t} |⟪vₖ, x⟫|² ≤ ‖c x - T x‖²`. -/
theorem sq_mul_sum_norm_inner_sq_le_norm_smul_sub_apply_sq (hT : T.IsSymmetric)
    (hn : finrank 𝕜 E = n) {c Δ : ℝ} (hΔ : 0 ≤ Δ) {t : Finset (Fin n)}
    (hgap : ∀ k ∈ t, Δ ≤ |c - hT.eigenvalues hn k|) (x : E) :
    Δ ^ 2 * ∑ k ∈ t, ‖⟪hT.eigenvectorBasis hn k, x⟫_𝕜‖ ^ 2 ≤ ‖(c : 𝕜) • x - T x‖ ^ 2 := by
  rw [hT.norm_smul_sub_apply_sq_eq_sum hn, Finset.mul_sum]
  refine (Finset.sum_le_sum fun k hk ↦ ?_).trans
    (Finset.sum_le_univ_sum_of_nonneg fun k ↦ by positivity)
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [← sq_abs (c - _)]
  exact pow_le_pow_left₀ hΔ (hgap k hk) 2

/-- **The lower residual bound.** Let `Δ ≥ 0` separate the eigenvalues of `T` indexed by `s` from
the remaining ones. Then for every family `(wⱼ)`, the residuals `λⱼ wⱼ - T wⱼ` bound the overlap
of the `wⱼ` with the complementary eigenvectors:
`Δ² ∑_{j ∈ s} ∑_{k ∉ s} |⟪vₖ, wⱼ⟫|² ≤ ∑_{j ∈ s} ‖λⱼ wⱼ - T wⱼ‖²`. -/
theorem sq_mul_sum_sum_norm_inner_sq_le_sum_norm_smul_sub_apply_sq (hT : T.IsSymmetric)
    (hn : finrank 𝕜 E = n) {Δ : ℝ} (hΔ : 0 ≤ Δ) {s : Finset (Fin n)}
    (hgap : ∀ j ∈ s, ∀ k ∉ s, Δ ≤ |hT.eigenvalues hn j - hT.eigenvalues hn k|)
    (w : Fin n → E) :
    Δ ^ 2 * ∑ j ∈ s, ∑ k ∈ sᶜ, ‖⟪hT.eigenvectorBasis hn k, w j⟫_𝕜‖ ^ 2 ≤
      ∑ j ∈ s, ‖(hT.eigenvalues hn j : 𝕜) • w j - T (w j)‖ ^ 2 := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j hj ↦ hT.sq_mul_sum_norm_inner_sq_le_norm_smul_sub_apply_sq hn hΔ
    (fun k hk ↦ hgap j hj k (Finset.mem_compl.mp hk)) (w j)

/-! ### The upper residual bounds -/

/-- **The residual decomposition.** For an eigenvector `uⱼ` of `S` with eigenvalue `μⱼ` and any
real `c`, `c uⱼ - T uⱼ = (c - μⱼ) uⱼ + (S - T) uⱼ`: an eigenvalue displacement plus the
perturbation applied to `uⱼ`. -/
theorem smul_sub_apply_eigenvectorBasis (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n) (c : ℝ)
    (j : Fin n) :
    (c : 𝕜) • hS.eigenvectorBasis hn j - T (hS.eigenvectorBasis hn j) =
      ((c - hS.eigenvalues hn j : ℝ) : 𝕜) • hS.eigenvectorBasis hn j +
        (S - T) (hS.eigenvectorBasis hn j) := by
  rw [sub_apply, hS.apply_eigenvectorBasis, RCLike.ofReal_sub, sub_smul]
  abel

/-- **The residual norm bound.** For an eigenvector `uⱼ` of `S` with eigenvalue `μⱼ` and any real
`c`, `‖c uⱼ - T uⱼ‖ ≤ |c - μⱼ| + ‖(S - T) uⱼ‖`. -/
theorem norm_smul_sub_apply_eigenvectorBasis_le (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) (c : ℝ) (j : Fin n) :
    ‖(c : 𝕜) • hS.eigenvectorBasis hn j - T (hS.eigenvectorBasis hn j)‖ ≤
      |c - hS.eigenvalues hn j| + ‖(S - T) (hS.eigenvectorBasis hn j)‖ := by
  rw [hS.smul_sub_apply_eigenvectorBasis hn]
  refine (norm_add_le _ _).trans_eq ?_
  rw [norm_smul, RCLike.norm_ofReal, (hS.eigenvectorBasis hn).orthonormal.1 j, mul_one]

/-- **The Frobenius upper residual bound.** The residuals `Rⱼ = λⱼ(T) uⱼ - T uⱼ` of the
eigenvectors `uⱼ` of `S` satisfy `∑_{j ∈ s} ‖Rⱼ‖² ≤ 4 ‖S - T‖_F²` for every index block `s`. -/
theorem sum_norm_smul_sub_apply_eigenvectorBasis_sq_le_four_mul_frobenius_sq
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n) (s : Finset (Fin n)) :
    ∑ j ∈ s, ‖(hT.eigenvalues hn j : 𝕜) • hS.eigenvectorBasis hn j -
        T (hS.eigenvectorBasis hn j)‖ ^ 2 ≤
      4 * TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E E (S - T) ^ 2 := by
  set u := hS.eigenvectorBasis hn
  set d := fun j ↦ hT.eigenvalues hn j - hS.eigenvalues hn j
  set F := TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E E (S - T)
  have hres (j : Fin n) : ‖(hT.eigenvalues hn j : 𝕜) • u j - T (u j)‖ ^ 2 ≤
      2 * (d j ^ 2 + ‖(S - T) (u j)‖ ^ 2) := by
    refine (pow_le_pow_left₀ (norm_nonneg _)
      (hS.norm_smul_sub_apply_eigenvectorBasis_le hn _ j) 2).trans ?_
    rw [← sq_abs (d j)]
    exact add_sq_le
  -- Hoffman–Wielandt, computed in the eigenbasis `u` of `S`.
  have hHW : ∑ j, d j ^ 2 ≤ F ^ 2 := by
    rw [sq_frobenius_apply u]
    simpa only [sub_apply, norm_sub_rev (S _)] using
      hT.sum_sq_eigenvalues_sub_le_sum_sq_norm_apply hS hn u
  calc ∑ j ∈ s, ‖(hT.eigenvalues hn j : 𝕜) • u j - T (u j)‖ ^ 2
      ≤ ∑ j, 2 * (d j ^ 2 + ‖(S - T) (u j)‖ ^ 2) :=
        (Finset.sum_le_sum fun j _ ↦ hres j).trans
          (Finset.sum_le_univ_sum_of_nonneg fun j ↦ by positivity)
    _ = 2 * (∑ j, d j ^ 2 + F ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, sq_frobenius_apply u]
    _ ≤ 4 * F ^ 2 := by linarith

/-- **The operator-norm upper residual bound.** If `‖(S - T) x‖ ≤ ε ‖x‖` for every `x`, then the
residuals `Rⱼ = λⱼ(T) uⱼ - T uⱼ` of the eigenvectors `uⱼ` of `S` satisfy
`∑_{j ∈ s} ‖Rⱼ‖² ≤ 4 |s| ε²` for every index block `s`. -/
theorem sum_norm_smul_sub_apply_eigenvectorBasis_sq_le_four_mul_card_mul_sq
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n) {ε : ℝ}
    (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) (s : Finset (Fin n)) :
    ∑ j ∈ s, ‖(hT.eigenvalues hn j : 𝕜) • hS.eigenvectorBasis hn j -
        T (hS.eigenvectorBasis hn j)‖ ^ 2 ≤
      4 * s.card * ε ^ 2 := by
  have hres (j : Fin n) : ‖(hT.eigenvalues hn j : 𝕜) • hS.eigenvectorBasis hn j -
      T (hS.eigenvectorBasis hn j)‖ ^ 2 ≤ 4 * ε ^ 2 := by
    -- Weyl's inequality bounds the eigenvalue displacement by `ε`.
    have hweyl := hS.abs_eigenvalue_sub_eigenvalue_le hT hn hε j
    have hpert := hε (hS.eigenvectorBasis hn j)
    rw [(hS.eigenvectorBasis hn).orthonormal.1 j, mul_one] at hpert
    have h := (hS.norm_smul_sub_apply_eigenvectorBasis_le hn (hT.eigenvalues hn j) j).trans
      (add_le_add ((abs_sub_comm _ _).trans_le hweyl) hpert)
    exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq (by ring)
  calc _ ≤ ∑ _j ∈ s, 4 * ε ^ 2 := Finset.sum_le_sum fun j _ ↦ hres j
    _ = 4 * s.card * ε ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-! ### The population-gap overlap bounds -/

/-- **The Yu–Wang–Samworth overlap bound, Frobenius form.** If `Δ ≥ 0` separates the eigenvalues of
the population operator `T` indexed by `s` from the remaining ones, then the eigenvectors `uⱼ` of
the perturbation `S` satisfy `Δ² ∑_{j ∈ s} ∑_{k ∉ s} |⟪vₖ, uⱼ⟫|² ≤ 4 ‖S - T‖_F²`. No gap is
assumed in the spectrum of `S`. -/
theorem sq_mul_sum_sum_norm_inner_sq_le_four_mul_frobenius_sq (hT : T.IsSymmetric)
    (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n) {Δ : ℝ} (hΔ : 0 ≤ Δ) {s : Finset (Fin n)}
    (hgap : ∀ j ∈ s, ∀ k ∉ s, Δ ≤ |hT.eigenvalues hn j - hT.eigenvalues hn k|) :
    Δ ^ 2 * ∑ j ∈ s, ∑ k ∈ sᶜ,
        ‖⟪hT.eigenvectorBasis hn k, hS.eigenvectorBasis hn j⟫_𝕜‖ ^ 2 ≤
      4 * TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E E (S - T) ^ 2 :=
  (hT.sq_mul_sum_sum_norm_inner_sq_le_sum_norm_smul_sub_apply_sq hn hΔ hgap _).trans
    (hT.sum_norm_smul_sub_apply_eigenvectorBasis_sq_le_four_mul_frobenius_sq hS hn s)

/-- **The Yu–Wang–Samworth overlap bound, operator-norm form.** If `Δ ≥ 0` separates the
eigenvalues of the population operator `T` indexed by `s` from the remaining ones and
`‖(S - T) x‖ ≤ ε ‖x‖` for every `x`, then the eigenvectors `uⱼ` of the perturbation `S` satisfy
`Δ² ∑_{j ∈ s} ∑_{k ∉ s} |⟪vₖ, uⱼ⟫|² ≤ 4 |s| ε²`. No gap is assumed in the spectrum of `S`. -/
theorem sq_mul_sum_sum_norm_inner_sq_le_four_mul_card_mul_sq (hT : T.IsSymmetric)
    (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n) {Δ : ℝ} (hΔ : 0 ≤ Δ) {s : Finset (Fin n)}
    (hgap : ∀ j ∈ s, ∀ k ∉ s, Δ ≤ |hT.eigenvalues hn j - hT.eigenvalues hn k|) {ε : ℝ}
    (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    Δ ^ 2 * ∑ j ∈ s, ∑ k ∈ sᶜ,
        ‖⟪hT.eigenvectorBasis hn k, hS.eigenvectorBasis hn j⟫_𝕜‖ ^ 2 ≤
      4 * s.card * ε ^ 2 :=
  (hT.sq_mul_sum_sum_norm_inner_sq_le_sum_norm_smul_sub_apply_sq hn hΔ hgap _).trans
    (hT.sum_norm_smul_sub_apply_eigenvectorBasis_sq_le_four_mul_card_mul_sq hS hn hε s)

end LinearMap.IsSymmetric
