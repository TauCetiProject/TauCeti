/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The min–max principle for a variational eigenvalue problem

Let `B` be a Hermitian sesquilinear form on a vector space `V` over `𝕜 = ℝ` or `ℂ`, conjugate
linear in its first argument, with `re B v v ≥ 0`, and let `J : V →ₗ[𝕜] H` be a linear map into
an inner product space. Suppose the variational eigenvalue problem `B u v = κ ⟪J u, J v⟫` (for all
`v`) has a complete system of solutions: an orthonormal basis `(eⱼ)` of `H`, indexed by `ℕ`, with
`eⱼ = J uⱼ` and `B uⱼ v = κⱼ ⟪eⱼ, J v⟫` for every `v`, where `κ₀ ≤ κ₁ ≤ ⋯`. The
**Courant–Fischer min–max principle** identifies `κₖ` without reference to the eigenfunctions.
Over `ℝ`, `κₖ` is the least `C` for which some subspace `W` of `V`, whose image `J W` has
dimension at least `k + 1`, satisfies `B v v ≤ C ‖J v‖²` on `W`
(`TauCeti.isLeast_minMax_of_hilbertBasis`). The minimum is attained on the span of
`u₀, …, uₖ`. In particular `κ` is determined by `B` and `J`.

For the Dirichlet problem of a divergence-form operator, `V = H¹₀(Ω)`, `H = L²(Ω)`, `J` is the
inclusion and `B` the energy form; the `κₖ` are then the Dirichlet eigenvalues counted with
multiplicity. The estimates are also the ones behind the min–max principle for a compact form
pair, applied there to a form that is nonnegative only after a shift.

## The argument

* On the span of `u₀, …, uₖ` the form is diagonal: for `v = ∑ dᵢ uᵢ`,
  `re B v v = ∑ κᵢ |dᵢ|² ≤ κₖ ∑ |dᵢ|² = κₖ ‖J v‖²`
  (`TauCeti.re_apply_self_le_mul_norm_sq_of_mem_span`).
* **Bessel's inequality for `B`**: for every `v` and every finite set `s` of indices,
  `∑_{j ∈ s} κⱼ |⟪eⱼ, J v⟫|² ≤ re B v v`. This is `0 ≤ re B w w` for
  `w = v - ∑_{j ∈ s} ⟪eⱼ, J v⟫ uⱼ`, expanded with conjugate symmetry and the eigenvalue
  equations (`TauCeti.sum_mul_norm_inner_sq_le_re_apply_self`). If `J v` is orthogonal to
  `e₀, …, e_{k-1}`, the left side for `s = {0, …, N - 1}` is at least
  `κₖ ∑_{j < N} |⟪eⱼ, J v⟫|²`, which tends to `κₖ ‖J v‖²` by Parseval's identity
  (`TauCeti.mul_norm_sq_le_re_apply_self_of_forall_inner_eq_zero`).
* A subspace `W` with `dim J W ≥ k + 1` contains some `v` with `J v ≠ 0` orthogonal to
  `e₀, …, e_{k-1}`, since only `k` linear conditions are imposed
  (`TauCeti.exists_mem_apply_ne_zero_mul_norm_sq_le_re_apply_self`).

## Main declarations

* `TauCeti.re_apply_self_le_mul_norm_sq_of_mem_span`: the upper bound on the first `k + 1`
  eigenfunctions.
* `TauCeti.sum_mul_norm_inner_sq_le_re_apply_self`: Bessel's inequality for `B`.
* `TauCeti.mul_norm_sq_le_re_apply_self_of_forall_inner_eq_zero`: the lower bound off the first
  `k` eigenfunctions.
* `TauCeti.exists_mem_apply_ne_zero_mul_norm_sq_le_re_apply_self`: the lower bound on every
  subspace of dimension at least `k + 1`.
* `TauCeti.apply_sum_smul_eq_sum_mul_inner`, `TauCeti.apply_sum_smul_sum_smul_eq_sum_mul_sq`:
  over `ℝ`, the form on finite combinations of eigenfunctions.
* `TauCeti.sum_mul_inner_sq_le_apply_self`: Bessel's inequality for `B` over `ℝ`, for any
  orthonormal family of eigenfunction images.
* `TauCeti.isLeast_minMax_of_hilbertBasis`: the min–max principle over `ℝ`.

## References

* R. Courant and D. Hilbert, *Methods of Mathematical Physics*, Vol. I, Chapter VI, §1.
* D. Gilbarg and N. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 8.12.
-/

public section

noncomputable section

open Filter RCLike Set
open scoped ComplexConjugate InnerProductSpace Topology

namespace TauCeti

section RCLike

variable {𝕜 V H : Type*} [RCLike 𝕜] [AddCommGroup V] [Module 𝕜 V] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] {B : V →ₗ⋆[𝕜] V →ₗ[𝕜] 𝕜} {J : V →ₗ[𝕜] H} {kappa : ℕ → ℝ}
  {u : ℕ → V}

/-- **The upper half of the min–max principle.** Let `u₀, u₁, …` have orthonormal images
`J uⱼ` and satisfy `B uⱼ v = κⱼ ⟪J uⱼ, J v⟫` for every `v`, with `κᵢ ≤ κₖ` for `i ≤ k`. Then every
`v` in the span of `u₀, …, uₖ` has `re B v v ≤ κₖ ‖J v‖²`. -/
theorem re_apply_self_le_mul_norm_sq_of_mem_span {k : ℕ} (hkappa : ∀ i ≤ k, kappa i ≤ kappa k)
    (hu : Orthonormal 𝕜 fun j ↦ J (u j))
    (heq : ∀ (j : ℕ) (v : V), B (u j) v = (kappa j : 𝕜) * ⟪J (u j), J v⟫_𝕜) {v : V}
    (hv : v ∈ Submodule.span 𝕜 (Set.range fun i : Fin (k + 1) ↦ u i)) :
    re (B v v) ≤ kappa k * ‖J v‖ ^ 2 := by
  obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).1 hv
  have he : Orthonormal 𝕜 fun i : Fin (k + 1) ↦ J (u i) := hu.comp _ Fin.val_injective
  set v := ∑ i, d i • u i with hv_def
  have hJ : J v = ∑ i, d i • J (u i) := by
    simp only [v, map_sum, map_smul]
  -- The form is diagonal along the `uᵢ`, and the coordinates of `J v` are the `d i`.
  have hB : B v v = ∑ i : Fin (k + 1), conj (d i) * ((kappa i : 𝕜) * d i) := by
    nth_rewrite 1 [hv_def]
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, heq, hJ, he.inner_right_fintype]
  have hre : re (B v v) = ∑ i : Fin (k + 1), kappa i * ‖d i‖ ^ 2 := by
    rw [hB, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mul_left_comm, RCLike.conj_mul, ← ofReal_pow, ← ofReal_mul, ofReal_re]
  have hnorm : ‖J v‖ ^ 2 = ∑ i, ‖d i‖ ^ 2 := by
    rw [hJ, ← ofReal_inj (K := 𝕜)]
    push_cast
    rw [← inner_self_eq_norm_sq_to_K, he.inner_sum]
    exact Finset.sum_congr rfl fun i _ ↦ RCLike.conj_mul _
  rw [hre, hnorm, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ ↦
    mul_le_mul_of_nonneg_right (hkappa i (Nat.lt_succ_iff.1 i.isLt)) (sq_nonneg _)

/-- **Bessel's inequality for a nonnegative Hermitian form.** Let `B` be Hermitian with
`re B v v ≥ 0`, and let `u` have orthonormal images `J uⱼ` and satisfy `B uⱼ v = κⱼ ⟪J uⱼ, J v⟫`
for every `v`. Then `∑_{j ∈ s} κⱼ |⟪J uⱼ, J v⟫|² ≤ re B v v` for every finite set `s` of
indices. This is `0 ≤ re B w w` for `w = v - ∑_{j ∈ s} ⟪J uⱼ, J v⟫ uⱼ`. -/
theorem sum_mul_norm_inner_sq_le_re_apply_self {ι : Type*} {u : ι → V} {kappa : ι → ℝ}
    (hsymm : ∀ v w : V, B v w = star (B w v)) (hnonneg : ∀ v : V, 0 ≤ re (B v v))
    (hu : Orthonormal 𝕜 fun j ↦ J (u j))
    (heq : ∀ (j : ι) (v : V), B (u j) v = (kappa j : 𝕜) * ⟪J (u j), J v⟫_𝕜) (v : V)
    (s : Finset ι) :
    ∑ j ∈ s, kappa j * ‖⟪J (u j), J v⟫_𝕜‖ ^ 2 ≤ re (B v v) := by
  set d : ι → 𝕜 := fun j ↦ ⟪J (u j), J v⟫_𝕜
  set w := ∑ j ∈ s, d j • u j
  -- The form is diagonal along the `uⱼ`, with entries `κⱼ`.
  have hBw (x : V) : B w x = ∑ j ∈ s, conj (d j) * ((kappa j : 𝕜) * ⟪J (u j), J x⟫_𝕜) := by
    simp only [w, map_sum, map_smulₛₗ, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, heq]
  have hsum : B w v = ((∑ j ∈ s, kappa j * ‖d j‖ ^ 2 : ℝ) : 𝕜) := by
    rw [hBw]
    push_cast
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← RCLike.conj_mul]
    ring
  have hww : B w w = B w v := by
    rw [hBw, hBw]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    simp only [w, map_sum, map_smul, hu.inner_right_sum d hj, d]
  have hnn := hnonneg (v - w)
  have hre : re (B (v - w) (v - w)) = re (B v v) - re (B w v) := by
    simp only [map_sub, LinearMap.sub_apply, hww, hsymm v w, star_def, conj_re]
    ring
  rw [hre, hsum, ofReal_re] at hnn
  linarith

/-- **The lower half of the min–max principle.** Let `B` be Hermitian with `re B v v ≥ 0`, let
`(eⱼ)` be an orthonormal basis of `H` with `eⱼ = J uⱼ` and `B uⱼ v = κⱼ ⟪eⱼ, J v⟫` for every `v`,
where `κₖ ≤ κⱼ` for `k ≤ j`. If `J v` is orthogonal to `e₀, …, e_{k-1}`, then
`κₖ ‖J v‖² ≤ re B v v`. -/
theorem mul_norm_sq_le_re_apply_self_of_forall_inner_eq_zero
    (hsymm : ∀ v w : V, B v w = star (B w v)) (hnonneg : ∀ v : V, 0 ≤ re (B v v))
    (e : HilbertBasis ℕ 𝕜 H) {k : ℕ} (hkappa : ∀ j, k ≤ j → kappa k ≤ kappa j)
    (hJu : ∀ j, J (u j) = e j)
    (heq : ∀ (j : ℕ) (v : V), B (u j) v = (kappa j : 𝕜) * ⟪J (u j), J v⟫_𝕜) {v : V}
    (hv : ∀ j < k, ⟪e j, J v⟫_𝕜 = 0) :
    kappa k * ‖J v‖ ^ 2 ≤ re (B v v) := by
  have hu : Orthonormal 𝕜 fun j ↦ J (u j) := by simpa only [hJu] using e.orthonormal
  -- Bessel's inequality, with `κⱼ ≥ κₖ` on the nonzero coefficients.
  have hpartial (N : ℕ) : kappa k * ∑ j ∈ Finset.range N, ‖⟪e j, J v⟫_𝕜‖ ^ 2 ≤ re (B v v) := by
    refine le_trans ?_
      (sum_mul_norm_inner_sq_le_re_apply_self hsymm hnonneg hu heq v (Finset.range N))
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ ↦ ?_
    rw [hJu]
    rcases lt_or_ge j k with hj | hj
    · simp [hv j hj]
    · exact mul_le_mul_of_nonneg_right (hkappa j hj) (sq_nonneg _)
  -- Parseval's identity `∑ⱼ |⟪eⱼ, J v⟫|² = ‖J v‖²`.
  exact le_of_tendsto' ((e.hasSum_norm_inner_sq (J v)).tendsto_sum_nat.const_mul (kappa k))
    hpartial

/-- **The lower half of the min–max principle on a subspace.** In the setting of
`TauCeti.mul_norm_sq_le_re_apply_self_of_forall_inner_eq_zero`, every subspace `W` of `V` whose
image `J W` has dimension at least `k + 1` contains some `v` with `J v ≠ 0` and
`κₖ ‖J v‖² ≤ re B v v`. -/
theorem exists_mem_apply_ne_zero_mul_norm_sq_le_re_apply_self
    (hsymm : ∀ v w : V, B v w = star (B w v)) (hnonneg : ∀ v : V, 0 ≤ re (B v v))
    (e : HilbertBasis ℕ 𝕜 H) {k : ℕ} (hkappa : ∀ j, k ≤ j → kappa k ≤ kappa j)
    (hJu : ∀ j, J (u j) = e j)
    (heq : ∀ (j : ℕ) (v : V), B (u j) v = (kappa j : 𝕜) * ⟪J (u j), J v⟫_𝕜)
    {W : Submodule 𝕜 V} (hW : k + 1 ≤ Module.finrank 𝕜 (W.map J)) :
    ∃ v ∈ W, J v ≠ 0 ∧ kappa k * ‖J v‖ ^ 2 ≤ re (B v v) := by
  have : FiniteDimensional 𝕜 (W.map J) := Module.finite_of_finrank_pos (by omega)
  -- The `k` coordinates along `e₀, …, e_{k-1}` vanish at some nonzero vector of `J W`.
  let f : W.map J →ₗ[𝕜] Fin k → 𝕜 :=
    LinearMap.pi fun j ↦ (innerₛₗ 𝕜 (e j)).comp (W.map J).subtype
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := f) (by rw [Module.finrank_fin_fun]; omega))
  obtain ⟨v, hvW, hvx⟩ := Submodule.mem_map.1 x.property
  refine ⟨v, hvW, hvx ▸ fun h ↦ hx0 (Subtype.ext h),
    mul_norm_sq_le_re_apply_self_of_forall_inner_eq_zero hsymm hnonneg e hkappa hJu heq
      fun j hj ↦ ?_⟩
  simpa [f, hvx] using congrFun (LinearMap.mem_ker.1 hx) ⟨j, hj⟩

end RCLike

section Real

variable {V H : Type*} [AddCommGroup V] [Module ℝ V] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {J : V →ₗ[ℝ] H} {kappa : ℕ → ℝ}
  {u : ℕ → V}

/-- Let `u i` satisfy `B (u i) v = κᵢ ⟪J (u i), J v⟫` for every `v`, with images `e i = J (u i)`.
Then a finite combination `∑ cᵢ uᵢ` pairs with every `v` through the eigenvalues:
`B (∑ cᵢ uᵢ) v = ∑ κᵢ cᵢ ⟪e i, J v⟫`. -/
theorem apply_sum_smul_eq_sum_mul_inner {ι : Type*} {kappa : ι → ℝ} {u : ι → V} {e : ι → H}
    (hJu : ∀ i, J (u i) = e i) (heq : ∀ i v, B (u i) v = kappa i * ⟪J (u i), J v⟫_ℝ)
    (c : ι → ℝ) (t : Finset ι) (v : V) :
    B (∑ i ∈ t, c i • u i) v = ∑ i ∈ t, kappa i * c i * ⟪e i, J v⟫_ℝ := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, heq, hJu]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- **The energy of a finite combination of eigenvectors.** In the setting of
`TauCeti.apply_sum_smul_eq_sum_mul_inner`, if the images `e i = J (u i)` are orthonormal then
the `u i` are orthogonal for `B` with `B (u i) (u i) = κᵢ`, so
`B (∑ cᵢ uᵢ) (∑ cᵢ uᵢ) = ∑ κᵢ cᵢ²`. -/
theorem apply_sum_smul_sum_smul_eq_sum_mul_sq {ι : Type*} {kappa : ι → ℝ} {u : ι → V}
    {e : ι → H} (he : Orthonormal ℝ e) (hJu : ∀ i, J (u i) = e i)
    (heq : ∀ i v, B (u i) v = kappa i * ⟪J (u i), J v⟫_ℝ) (c : ι → ℝ) (t : Finset ι) :
    B (∑ i ∈ t, c i • u i) (∑ i ∈ t, c i • u i) = ∑ i ∈ t, kappa i * c i ^ 2 := by
  rw [apply_sum_smul_eq_sum_mul_inner hJu heq]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  simp only [map_sum, map_smul, hJu]
  rw [he.inner_right_sum c hi]
  ring

/-- **Bessel's inequality for `B` over `ℝ`.** Let `B` be symmetric with `B v v ≥ 0`, and let
`u i` have orthonormal images `e i = J (u i)` and satisfy `B (u i) v = κᵢ ⟪J (u i), J v⟫` for every
`v`. Then every finite sum of `κᵢ ⟪e i, J v⟫²` is at most `B v v`. This is the real case of
`TauCeti.sum_mul_norm_inner_sq_le_re_apply_self`. -/
theorem sum_mul_inner_sq_le_apply_self {ι : Type*} {kappa : ι → ℝ} {u : ι → V} {e : ι → H}
    (hsymm : ∀ v w : V, B v w = B w v) (hnonneg : ∀ v : V, 0 ≤ B v v) (he : Orthonormal ℝ e)
    (hJu : ∀ i, J (u i) = e i) (heq : ∀ i v, B (u i) v = kappa i * ⟪J (u i), J v⟫_ℝ) (v : V)
    (t : Finset ι) : ∑ i ∈ t, kappa i * ⟪e i, J v⟫_ℝ ^ 2 ≤ B v v := by
  have h := sum_mul_norm_inner_sq_le_re_apply_self (B := B)
    (fun v w ↦ by rw [star_trivial]; exact hsymm v w) hnonneg (by simpa only [hJu] using he)
    heq v t
  simpa only [hJu, Real.norm_eq_abs, sq_abs, re_to_real] using h

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
  -- Over `ℝ` the form is its own conjugate and the real part is the identity.
  have hsymm' (v w : V) : B v w = star (B w v) := by rw [star_trivial]; exact hsymm v w
  refine ⟨⟨Submodule.span ℝ (Set.range fun i : Fin (k + 1) ↦ u i), ?_,
    fun v hv ↦ re_apply_self_le_mul_norm_sq_of_mem_span (B := B) (fun _ hi ↦ hkappa hi)
      (by simpa only [hJu] using e.orthonormal) heq hv⟩, ?_⟩
  · -- The images of `u₀, …, uₖ` are the linearly independent vectors `e₀, …, eₖ`.
    rw [Submodule.map_span, ← Set.range_comp]
    have hrange : (J ∘ fun i : Fin (k + 1) ↦ u i) = fun i : Fin (k + 1) ↦ e i :=
      funext fun i ↦ hJu i
    rw [hrange]
    exact (finrank_span_eq_card (e.orthonormal.linearIndependent.comp _ Fin.val_injective)).trans
      (Fintype.card_fin _) |>.ge
  · rintro C ⟨W, hW, hC⟩
    obtain ⟨v, hvW, hv0, hv⟩ := exists_mem_apply_ne_zero_mul_norm_sq_le_re_apply_self (B := B)
      hsymm' hnonneg e (fun _ hj ↦ hkappa hj) hJu heq hW
    exact le_of_mul_le_mul_right (hv.trans (hC v hvW)) (by positivity)

end Real

end TauCeti
