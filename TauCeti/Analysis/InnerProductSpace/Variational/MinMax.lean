/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The min–max principle for a variational eigenvalue problem

Let `B` be a symmetric bilinear form on a real vector space `V` with `B v v ≥ 0`, and let
`J : V →ₗ[ℝ] H` be a linear map into a real inner product space. Suppose the variational
eigenvalue problem `B u v = κ ⟪J u, J v⟫` (for all `v`) has a complete system of solutions: an
orthonormal basis `(eⱼ)` of `H`, indexed by `ℕ`, with `eⱼ = J uⱼ` and `B uⱼ v = κⱼ ⟪eⱼ, J v⟫` for
every `v`, where `κ₀ ≤ κ₁ ≤ ⋯`. The **Courant–Fischer min–max principle** identifies `κₖ` without
reference to the eigenfunctions: it is the least `C` for which some subspace `W` of `V`, whose
image `J W` has dimension at least `k + 1`, satisfies `B v v ≤ C ‖J v‖²` on `W`
(`TauCeti.isLeast_minMax_of_hilbertBasis`). The minimum is attained on the span of
`u₀, …, uₖ`. In particular `κ` is determined by `B` and `J`.

For the Dirichlet problem of a divergence-form operator, `V = H¹₀(Ω)`, `H = L²(Ω)`, `J` is the
inclusion and `B` the energy form; the `κₖ` are then the Dirichlet eigenvalues counted with
multiplicity.

## The argument

* On the span of `u₀, …, uₖ` the form is diagonal: for `v = ∑ dᵢ uᵢ`,
  `B v v = ∑ κᵢ dᵢ² ≤ κₖ ∑ dᵢ² = κₖ ‖J v‖²`
  (`TauCeti.apply_self_le_mul_norm_sq_of_mem_span`).
* **Bessel's inequality for `B`**: for every `v` and `N`,
  `∑_{j < N} κⱼ ⟪eⱼ, J v⟫² ≤ B v v`. This is `0 ≤ B w w` for `w = v - ∑_{j < N} ⟪eⱼ, J v⟫ uⱼ`,
  expanded with symmetry and the eigenvalue equations. If `J v` is orthogonal to
  `e₀, …, e_{k-1}`, the left side is at least `κₖ ∑_{j < N} ⟪eⱼ, J v⟫²`, which tends to
  `κₖ ‖J v‖²` by Parseval's identity (`TauCeti.mul_norm_sq_le_apply_self_of_forall_inner_eq_zero`).
* A subspace `W` with `dim J W ≥ k + 1` contains some `v` with `J v ≠ 0` orthogonal to
  `e₀, …, e_{k-1}`, since only `k` linear conditions are imposed
  (`TauCeti.exists_mem_apply_ne_zero_mul_norm_sq_le_apply_self`).

## Main declarations

* `TauCeti.apply_self_le_mul_norm_sq_of_mem_span`: the upper bound on the first `k + 1`
  eigenfunctions.
* `TauCeti.mul_norm_sq_le_apply_self_of_forall_inner_eq_zero`: the lower bound off the first `k`
  eigenfunctions.
* `TauCeti.exists_mem_apply_ne_zero_mul_norm_sq_le_apply_self`: the lower bound on every
  subspace of dimension at least `k + 1`.
* `TauCeti.isLeast_minMax_of_hilbertBasis`: the min–max principle.

## References

* R. Courant and D. Hilbert, *Methods of Mathematical Physics*, Vol. I, Chapter VI, §1.
* D. Gilbarg and N. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 8.12.
-/

public section

noncomputable section

open Filter Set
open scoped InnerProductSpace Topology

namespace TauCeti

variable {V H : Type*} [AddCommGroup V] [Module ℝ V] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {J : V →ₗ[ℝ] H} {kappa : ℕ → ℝ}
  {u : ℕ → V}

/-- **The upper half of the min–max principle.** Let `u₀, u₁, …` have orthonormal images
`J uⱼ` and satisfy `B uⱼ v = κⱼ ⟪J uⱼ, J v⟫` for every `v`, with `κ` nondecreasing. Then every `v`
in the span of `u₀, …, uₖ` has `B v v ≤ κₖ ‖J v‖²`. -/
theorem apply_self_le_mul_norm_sq_of_mem_span (hkappa : Monotone kappa)
    (hu : Orthonormal ℝ fun j ↦ J (u j))
    (heq : ∀ (j : ℕ) (v : V), B (u j) v = kappa j * ⟪J (u j), J v⟫_ℝ) {k : ℕ} {v : V}
    (hv : v ∈ Submodule.span ℝ (Set.range fun i : Fin (k + 1) ↦ u i)) :
    B v v ≤ kappa k * ‖J v‖ ^ 2 := by
  obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hv
  have he : Orthonormal ℝ fun i : Fin (k + 1) ↦ J (u i) := hu.comp _ Fin.val_injective
  have hlin (w : V) : B (∑ i, d i • u i) w = ∑ i, d i * B (u i) w := by
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul]
  have hJ : J (∑ i, d i • u i) = ∑ i, d i • J (u i) := by
    simp only [map_sum, map_smul]
  generalize ∑ i, d i • u i = v at hlin hJ
  -- The coordinates of `J v` in the orthonormal family are the coefficients `d i`.
  have hcoord (i : Fin (k + 1)) : ⟪J (u i), J v⟫_ℝ = d i := by
    rw [hJ, he.inner_right_fintype]
  have hB : B v v = ∑ i : Fin (k + 1), kappa i * d i ^ 2 := by
    rw [hlin]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [heq, hcoord]
    ring
  have hnorm : ‖J v‖ ^ 2 = ∑ i, d i ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    nth_rewrite 1 [hJ]
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [real_inner_smul_left, hcoord, sq]
  rw [hB, hnorm, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ ↦
    mul_le_mul_of_nonneg_right (hkappa (Nat.lt_succ_iff.1 i.2)) (sq_nonneg _)

/-- **Bessel's inequality and the lower half of the min–max principle.** Let `B` be symmetric
with `B v v ≥ 0`, let `(eⱼ)` be an orthonormal basis of `H` with `eⱼ = J uⱼ` and
`B uⱼ v = κⱼ ⟪eⱼ, J v⟫` for every `v`, where `κ` is nondecreasing. If `J v` is orthogonal to
`e₀, …, e_{k-1}`, then `κₖ ‖J v‖² ≤ B v v`. -/
theorem mul_norm_sq_le_apply_self_of_forall_inner_eq_zero (hsymm : ∀ v w : V, B v w = B w v)
    (hnonneg : ∀ v : V, 0 ≤ B v v) (e : HilbertBasis ℕ ℝ H) (hkappa : Monotone kappa)
    (hJu : ∀ j, J (u j) = e j) (heq : ∀ (j : ℕ) (v : V), B (u j) v = kappa j * ⟪J (u j), J v⟫_ℝ)
    {k : ℕ} {v : V} (hv : ∀ j < k, ⟪e j, J v⟫_ℝ = 0) :
    kappa k * ‖J v‖ ^ 2 ≤ B v v := by
  have hBu (j : ℕ) (w : V) : B (u j) w = kappa j * ⟪e j, J w⟫_ℝ := by rw [heq, hJu]
  -- Bessel's inequality `∑_{j < N} κⱼ ⟪eⱼ, J v⟫² ≤ B v v`, from `0 ≤ B (v - s) (v - s)`.
  have hbessel (N : ℕ) : ∑ j ∈ Finset.range N, kappa j * ⟪e j, J v⟫_ℝ ^ 2 ≤ B v v := by
    set s := ∑ j ∈ Finset.range N, ⟪e j, J v⟫_ℝ • u j
    have hs (w : V) : B s w = ∑ j ∈ Finset.range N, ⟪e j, J v⟫_ℝ * (kappa j * ⟪e j, J w⟫_ℝ) := by
      simp only [s, map_sum, map_smul, LinearMap.sum_apply,
        LinearMap.smul_apply, smul_eq_mul, hBu]
    have hJs : J s = ∑ j ∈ Finset.range N, ⟪e j, J v⟫_ℝ • e j := by
      simp only [s, map_sum, map_smul, hJu]
    have hsv : B s v = ∑ j ∈ Finset.range N, kappa j * ⟪e j, J v⟫_ℝ ^ 2 :=
      (hs v).trans (Finset.sum_congr rfl fun j _ ↦ by ring)
    have hss : B s s = ∑ j ∈ Finset.range N, kappa j * ⟪e j, J v⟫_ℝ ^ 2 := by
      rw [hs]
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      rw [hJs, e.orthonormal.inner_right_sum _ hj]
      ring
    have h := hnonneg (v - s)
    simp only [map_sub, LinearMap.sub_apply] at h
    rw [hsymm v s] at h
    linarith
  have hpartial (N : ℕ) : kappa k * ∑ j ∈ Finset.range N, ⟪e j, J v⟫_ℝ ^ 2 ≤ B v v := by
    refine le_trans ?_ (hbessel N)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ ↦ ?_
    rcases lt_or_ge j k with hj | hj
    · simp [hv j hj]
    · exact mul_le_mul_of_nonneg_right (hkappa hj) (sq_nonneg _)
  -- Parseval's identity `∑ⱼ ⟪eⱼ, J v⟫² = ‖J v‖²`.
  have hlim : Tendsto (fun N ↦ ∑ j ∈ Finset.range N, ⟪e j, J v⟫_ℝ ^ 2) atTop
      (𝓝 (‖J v‖ ^ 2)) := by
    simpa only [real_inner_comm (e _), ← sq, real_inner_self_eq_norm_sq] using
      (e.hasSum_inner_mul_inner (J v) (J v)).tendsto_sum_nat
  exact le_of_tendsto' (hlim.const_mul (kappa k)) hpartial

/-- **The lower half of the min–max principle on a subspace.** In the setting of
`TauCeti.mul_norm_sq_le_apply_self_of_forall_inner_eq_zero`, every subspace `W` of `V` whose image
`J W` has dimension at least `k + 1` contains some `v` with `J v ≠ 0` and
`κₖ ‖J v‖² ≤ B v v`. -/
theorem exists_mem_apply_ne_zero_mul_norm_sq_le_apply_self (hsymm : ∀ v w : V, B v w = B w v)
    (hnonneg : ∀ v : V, 0 ≤ B v v) (e : HilbertBasis ℕ ℝ H) (hkappa : Monotone kappa)
    (hJu : ∀ j, J (u j) = e j) (heq : ∀ (j : ℕ) (v : V), B (u j) v = kappa j * ⟪J (u j), J v⟫_ℝ)
    {k : ℕ} {W : Submodule ℝ V} (hW : k + 1 ≤ Module.finrank ℝ (W.map J)) :
    ∃ v ∈ W, J v ≠ 0 ∧ kappa k * ‖J v‖ ^ 2 ≤ B v v := by
  have : FiniteDimensional ℝ (W.map J) := Module.finite_of_finrank_pos (by omega)
  -- The `k` coordinates along `e₀, …, e_{k-1}` vanish at some nonzero vector of `J W`.
  let f : W.map J →ₗ[ℝ] Fin k → ℝ :=
    LinearMap.pi fun j ↦ (innerₗ H (e j)).comp (W.map J).subtype
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := f) (by rw [Module.finrank_fin_fun]; omega))
  obtain ⟨v, hvW, hvx⟩ := Submodule.mem_map.1 x.2
  refine ⟨v, hvW, hvx ▸ fun h ↦ hx0 (Subtype.ext h),
    mul_norm_sq_le_apply_self_of_forall_inner_eq_zero hsymm hnonneg e hkappa hJu heq
      fun j hj ↦ ?_⟩
  simpa [f, hvx] using congrFun (LinearMap.mem_ker.1 hx) ⟨j, hj⟩

/-- **The Courant–Fischer min–max principle.** Let `B` be symmetric with `B v v ≥ 0`, and let
`(eⱼ)` be an orthonormal basis of `H` with `eⱼ = J uⱼ` and `B uⱼ v = κⱼ ⟪eⱼ, J v⟫` for every `v`,
where `κ` is nondecreasing. Then `κₖ` is the least `C` for which some subspace `W` of `V` with
`dim J W ≥ k + 1` satisfies `B v v ≤ C ‖J v‖²` for every `v ∈ W`. The minimum is attained on the
span of `u₀, …, uₖ`. -/
theorem isLeast_minMax_of_hilbertBasis (hsymm : ∀ v w : V, B v w = B w v)
    (hnonneg : ∀ v : V, 0 ≤ B v v) (e : HilbertBasis ℕ ℝ H) (hkappa : Monotone kappa)
    (hJu : ∀ j, J (u j) = e j) (heq : ∀ (j : ℕ) (v : V), B (u j) v = kappa j * ⟪J (u j), J v⟫_ℝ)
    (k : ℕ) :
    IsLeast {C : ℝ | ∃ W : Submodule ℝ V, k + 1 ≤ Module.finrank ℝ (W.map J) ∧
      ∀ v ∈ W, B v v ≤ C * ‖J v‖ ^ 2} (kappa k) := by
  refine ⟨⟨Submodule.span ℝ (Set.range fun i : Fin (k + 1) ↦ u i), ?_,
    fun v hv ↦ apply_self_le_mul_norm_sq_of_mem_span hkappa
      (by simpa only [hJu] using e.orthonormal) heq hv⟩, ?_⟩
  · -- The images of `u₀, …, uₖ` are the linearly independent vectors `e₀, …, eₖ`.
    rw [Submodule.map_span, ← Set.range_comp]
    have hrange : (J ∘ fun i : Fin (k + 1) ↦ u i) = fun i : Fin (k + 1) ↦ e i :=
      funext fun i ↦ hJu i
    rw [hrange]
    exact (finrank_span_eq_card (e.orthonormal.linearIndependent.comp _ Fin.val_injective)).trans
      (Fintype.card_fin _) |>.ge
  · rintro C ⟨W, hW, hC⟩
    obtain ⟨v, hvW, hv0, hv⟩ := exists_mem_apply_ne_zero_mul_norm_sq_le_apply_self hsymm hnonneg
      e hkappa hJu heq hW
    exact le_of_mul_le_mul_right (hv.trans (hC v hvW)) (by positivity)

end TauCeti
