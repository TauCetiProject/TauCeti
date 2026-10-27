/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.PiL2

/-!
# The Hilbert-space supremum of a real matrix

For a finite real matrix `a : Matrix ι κ ℝ`, let `Γ(a)` be the supremum of
`|∑ i, ∑ j, a i j * ⟪u i, v j⟫|` over all families `u : ι → E`, `v : κ → E` of vectors of norm
at most one in all real inner product spaces `E`. Grothendieck's inequality bounds `Γ(a)` by a
universal constant times the supremum of `|∑ i, ∑ j, a i j * s i * t j|` over scalars
`|s i|, |t j| ≤ 1`, which is the case `E = ℝ`.

Inner products of finitely many vectors only depend on their span, which has dimension at most
`card ι + card κ` and therefore embeds isometrically into `EuclideanSpace ℝ (ι ⊕ κ)`. We define
`Matrix.innerProductSup a` as the supremum over this single Euclidean space, and prove that it
bounds the sum in every real inner product space, in any universe. Together with
`Matrix.innerProductSup_le_iff`, this identifies it with the supremum over all real inner product
spaces. It is finite, being at most `∑ i, ∑ j, |a i j|`.

The bound in an arbitrary space is what makes `Γ(a)` usable in the truncation proof of
Grothendieck's inequality, where it is applied to Gaussian variables in `L²` and to their
truncation errors, whose norms are small but not at most one; hence the scaled form
`Matrix.abs_sum_sum_mul_inner_le_innerProductSup_mul_mul`.

## Main declarations

* `Matrix.innerProductSup`: the supremum `Γ(a)`.
* `Matrix.abs_sum_sum_mul_inner_le_innerProductSup`: `Γ(a)` bounds the sum for unit-ball families
  in every real inner product space.
* `Matrix.abs_sum_sum_mul_inner_le_innerProductSup_mul_mul`: the bound `Γ(a) * R * S` for families
  of norms at most `R` and `S`.
* `Matrix.innerProductSup_le_iff`: `Γ(a) ≤ c` as soon as `c` bounds the sum for unit-ball families
  in `EuclideanSpace ℝ (ι ⊕ κ)`.
* `Matrix.abs_sum_sum_mul_mul_le_innerProductSup`: the scalar sum is at most `Γ(a)`.
* `Matrix.innerProductSup_le_sum_sum_abs`, `Matrix.innerProductSup_smul`: finiteness and
  homogeneity.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §8.1.
-/

public section

open scoped InnerProductSpace

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The supremum `Γ(a)` of `|∑ i, ∑ j, a i j * ⟪u i, v j⟫|` over families of vectors of norm at
most one. It is defined in `EuclideanSpace ℝ (ι ⊕ κ)`; by
`Matrix.abs_sum_sum_mul_inner_le_innerProductSup` and `Matrix.innerProductSup_le_iff` it is the
same supremum over every real inner product space. -/
noncomputable def innerProductSup (a : Matrix ι κ ℝ) : ℝ :=
  sSup {r | ∃ (u : ι → EuclideanSpace ℝ (ι ⊕ κ)) (v : κ → EuclideanSpace ℝ (ι ⊕ κ)),
    (∀ i, ‖u i‖ ≤ 1) ∧ (∀ j, ‖v j‖ ≤ 1) ∧ |∑ i, ∑ j, a i j * ⟪u i, v j⟫_ℝ| = r}

/-- For families of vectors of norm at most one, each inner product has absolute value at most
one, so the sum is at most `∑ i, ∑ j, |a i j|`. -/
private theorem abs_sum_sum_mul_inner_le_sum_sum_abs (a : Matrix ι κ ℝ) {u : ι → E}
    {v : κ → E} (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ j, ‖v j‖ ≤ 1) :
    |∑ i, ∑ j, a i j * ⟪u i, v j⟫_ℝ| ≤ ∑ i, ∑ j, |a i j| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans <| Finset.sum_le_sum fun i _ ↦
    (Finset.abs_sum_le_sum_abs _ _).trans <| Finset.sum_le_sum fun j _ ↦ ?_
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) <| (abs_real_inner_le_norm _ _).trans <|
    (mul_le_mul (hu i) (hv j) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

/-- Finitely many vectors of a real inner product space have isometric copies in
`EuclideanSpace ℝ (ι ⊕ κ)` with the same norms and mutual inner products: their span has dimension
at most `card (ι ⊕ κ)`. -/
private theorem exists_euclideanSpace_inner_eq (u : ι → E) (v : κ → E) :
    ∃ (u' : ι → EuclideanSpace ℝ (ι ⊕ κ)) (v' : κ → EuclideanSpace ℝ (ι ⊕ κ)),
      (∀ i, ‖u' i‖ = ‖u i‖) ∧ (∀ j, ‖v' j‖ = ‖v j‖) ∧ ∀ i j, ⟪u' i, v' j⟫_ℝ = ⟪u i, v j⟫_ℝ := by
  let W := Submodule.span ℝ (Set.range (Sum.elim u v))
  have : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  obtain ⟨L⟩ : Nonempty (W →ₗᵢ[ℝ] EuclideanSpace ℝ (ι ⊕ κ)) :=
    EuclideanSpace.nonempty_linearIsometry_iff_finrank_le.2 <|
      finrank_range_le_card (R := ℝ) (Sum.elim u v)
  have hu (i : ι) : u i ∈ W := Submodule.subset_span ⟨Sum.inl i, rfl⟩
  have hv (j : κ) : v j ∈ W := Submodule.subset_span ⟨Sum.inr j, rfl⟩
  refine ⟨fun i ↦ L ⟨u i, hu i⟩, fun j ↦ L ⟨v j, hv j⟩, fun i ↦ ?_, fun j ↦ ?_, fun i j ↦ ?_⟩
  · rw [L.norm_map, ← Submodule.norm_coe]
  · rw [L.norm_map, ← Submodule.norm_coe]
  · rw [L.inner_map_map, Submodule.coe_inner]

private theorem bddAbove_innerProductSup_set (a : Matrix ι κ ℝ) :
    BddAbove {r | ∃ (u : ι → EuclideanSpace ℝ (ι ⊕ κ)) (v : κ → EuclideanSpace ℝ (ι ⊕ κ)),
      (∀ i, ‖u i‖ ≤ 1) ∧ (∀ j, ‖v j‖ ≤ 1) ∧ |∑ i, ∑ j, a i j * ⟪u i, v j⟫_ℝ| = r} := by
  refine ⟨∑ i, ∑ j, |a i j|, ?_⟩
  rintro r ⟨u, v, hu, hv, rfl⟩
  exact abs_sum_sum_mul_inner_le_sum_sum_abs a hu hv

/-- `Γ(a)` bounds `|∑ i, ∑ j, a i j * ⟪u i, v j⟫|` for families of vectors of norm at most one in
any real inner product space. -/
theorem abs_sum_sum_mul_inner_le_innerProductSup (a : Matrix ι κ ℝ) {u : ι → E} {v : κ → E}
    (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ j, ‖v j‖ ≤ 1) :
    |∑ i, ∑ j, a i j * ⟪u i, v j⟫_ℝ| ≤ a.innerProductSup := by
  obtain ⟨u', v', hu', hv', huv⟩ := exists_euclideanSpace_inner_eq u v
  refine le_csSup (bddAbove_innerProductSup_set a) ⟨u', v', fun i ↦ (hu' i).trans_le (hu i),
    fun j ↦ (hv' j).trans_le (hv j), ?_⟩
  simp only [huv]

/-- `Γ(a)` is at most `c` if and only if `c` bounds `|∑ i, ∑ j, a i j * ⟪u i, v j⟫|` for families
of vectors of norm at most one in `EuclideanSpace ℝ (ι ⊕ κ)`. -/
theorem innerProductSup_le_iff {a : Matrix ι κ ℝ} {c : ℝ} :
    a.innerProductSup ≤ c ↔
      ∀ (u : ι → EuclideanSpace ℝ (ι ⊕ κ)) (v : κ → EuclideanSpace ℝ (ι ⊕ κ)),
        (∀ i, ‖u i‖ ≤ 1) → (∀ j, ‖v j‖ ≤ 1) → |∑ i, ∑ j, a i j * ⟪u i, v j⟫_ℝ| ≤ c := by
  refine ⟨fun h u v hu hv ↦ (abs_sum_sum_mul_inner_le_innerProductSup a hu hv).trans h,
    fun h ↦ csSup_le ⟨_, 0, 0, by simp, by simp, rfl⟩ ?_⟩
  rintro r ⟨u, v, hu, hv, rfl⟩
  exact h u v hu hv

/-- `Γ(a)` is nonnegative. -/
theorem innerProductSup_nonneg (a : Matrix ι κ ℝ) : 0 ≤ a.innerProductSup :=
  (abs_nonneg _).trans <|
    a.abs_sum_sum_mul_inner_le_innerProductSup (E := ℝ) (u := 0) (v := 0) (by simp) (by simp)

/-- `Γ(a)` is finite: it is at most the sum of the absolute values of the entries of `a`. -/
theorem innerProductSup_le_sum_sum_abs (a : Matrix ι κ ℝ) :
    a.innerProductSup ≤ ∑ i, ∑ j, |a i j| :=
  innerProductSup_le_iff.2 fun _ _ hu hv ↦ abs_sum_sum_mul_inner_le_sum_sum_abs a hu hv

/-- The zero matrix has `Γ(0) = 0`. -/
@[simp]
theorem innerProductSup_zero : (0 : Matrix ι κ ℝ).innerProductSup = 0 :=
  le_antisymm (by simpa using innerProductSup_le_sum_sum_abs (0 : Matrix ι κ ℝ))
    (innerProductSup_nonneg 0)

/-- For families of vectors of norms at most `R` and `S` in any real inner product space,
`|∑ i, ∑ j, a i j * ⟪u i, v j⟫|` is at most `Γ(a) * R * S`. -/
theorem abs_sum_sum_mul_inner_le_innerProductSup_mul_mul (a : Matrix ι κ ℝ) {u : ι → E}
    {v : κ → E} {R S : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S) (hu : ∀ i, ‖u i‖ ≤ R)
    (hv : ∀ j, ‖v j‖ ≤ S) :
    |∑ i, ∑ j, a i j * ⟪u i, v j⟫_ℝ| ≤ a.innerProductSup * R * S := by
  rcases hR.eq_or_lt with rfl | hR
  · simp [fun i ↦ norm_le_zero_iff.1 (hu i)]
  rcases hS.eq_or_lt with rfl | hS
  · simp [fun j ↦ norm_le_zero_iff.1 (hv j)]
  -- Rescale both families into the closed unit ball.
  have hu' (i : ι) : ‖R⁻¹ • u i‖ ≤ 1 := by
    rw [norm_smul_of_nonneg (inv_nonneg.2 hR.le)]
    exact inv_mul_le_one_of_le₀ (hu i) hR.le
  have hv' (j : κ) : ‖S⁻¹ • v j‖ ≤ 1 := by
    rw [norm_smul_of_nonneg (inv_nonneg.2 hS.le)]
    exact inv_mul_le_one_of_le₀ (hv j) hS.le
  have key := a.abs_sum_sum_mul_inner_le_innerProductSup hu' hv'
  have hsum : ∑ i, ∑ j, a i j * ⟪R⁻¹ • u i, S⁻¹ • v j⟫_ℝ =
      (R * S)⁻¹ * ∑ i, ∑ j, a i j * ⟪u i, v j⟫_ℝ := by
    simp only [real_inner_smul_left, real_inner_smul_right, Finset.mul_sum, mul_inv]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  rw [hsum, abs_mul, abs_of_pos (inv_pos.2 (mul_pos hR hS))] at key
  rw [mul_assoc, mul_comm]
  exact (inv_mul_le_iff₀ (mul_pos hR hS)).1 key

/-- The scalar sum `|∑ i, ∑ j, a i j * s i * t j|` with `|s i|, |t j| ≤ 1` is at most `Γ(a)`: this
is the case `E = ℝ`, the trivial direction of Grothendieck's inequality. -/
theorem abs_sum_sum_mul_mul_le_innerProductSup (a : Matrix ι κ ℝ) {s : ι → ℝ} {t : κ → ℝ}
    (hs : ∀ i, |s i| ≤ 1) (ht : ∀ j, |t j| ≤ 1) :
    |∑ i, ∑ j, a i j * s i * t j| ≤ a.innerProductSup := by
  simpa [mul_assoc, mul_comm (t _)] using
    a.abs_sum_sum_mul_inner_le_innerProductSup (E := ℝ) (u := s) (v := t) hs ht

private theorem innerProductSup_smul_le (c : ℝ) (a : Matrix ι κ ℝ) :
    (c • a).innerProductSup ≤ |c| * a.innerProductSup := by
  refine innerProductSup_le_iff.2 fun u v hu hv ↦ ?_
  have : ∑ i, ∑ j, (c • a) i j * ⟪u i, v j⟫_ℝ = c * ∑ i, ∑ j, a i j * ⟪u i, v j⟫_ℝ := by
    simp [Finset.mul_sum, mul_assoc]
  rw [this, abs_mul]
  exact mul_le_mul_of_nonneg_left (a.abs_sum_sum_mul_inner_le_innerProductSup hu hv)
    (abs_nonneg c)

/-- `Γ` is absolutely homogeneous. -/
theorem innerProductSup_smul (c : ℝ) (a : Matrix ι κ ℝ) :
    (c • a).innerProductSup = |c| * a.innerProductSup := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  refine le_antisymm (innerProductSup_smul_le c a) ?_
  have h := innerProductSup_smul_le c⁻¹ (c • a)
  rw [inv_smul_smul₀ hc, abs_inv] at h
  exact (le_inv_mul_iff₀ (abs_pos.2 hc)).1 h

end Matrix
