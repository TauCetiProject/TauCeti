/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.RademacherSum.Moment

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# The Kahane–Khintchine contraction principle and finite truncations

For a real normed space `E`, real scalars `α : ι → ℝ` bounded in absolute value by `M`, and any
convex nondecreasing function `Φ : ℝ → ℝ` on `[0, ∞)`, the expected value of
`Φ ‖∑ i, εᵢ (αᵢ xᵢ)‖` over the sign cube is at most that of `Φ (M ‖∑ i, εᵢ xᵢ‖)`. Writing each
coordinate `t ∈ [-1, 1]` as the convex combination `((1 - t) / 2) (-1) + ((1 + t) / 2) 1` and
flipping the sign `εᵢ` on the `-1` endpoint replaces the coefficients by `1` one coordinate at a
time without branching on a maximizing corner.

Specializing `Φ` to `id` and to `t ↦ t ^ p` (`1 ≤ p`) gives the `L¹`, `K_p`, and `R₂` contraction
principles with sharp constant `1`, both for an explicit bound `∀ i, |α i| ≤ M` and in terms of
`‖WithLp.toLp ∞ α‖`. Specializing `α` to `{0, 1}` indicator functions shows that restricting a
family to a subset can only decrease `K_p` for `1 ≤ p`; consequently, for an arbitrary index type
`α` and `1 ≤ p`, the finite truncations `s ↦ K_p(x|_s)` on `Finset α` are monotone and converge
along `Filter.atTop` whenever they are bounded above (in particular whenever `∑' i, ‖xᵢ‖ < ∞`).

## Main declarations

* `TauCeti.expect_apply_norm_sum_smul_le`: convex contraction principle on `[0, ∞)`.
* `TauCeti.expect_norm_sum_smul_le`, `TauCeti.expect_norm_sum_smul_le_norm_toLp_top`: `L¹`
  contraction principle.
* `TauCeti.rademacherMoment_smul_le`, `TauCeti.rademacherMoment_smul_le_norm_toLp_top`: `K_p`
  contraction principle for `1 ≤ p`.
* `TauCeti.rademacherSecondMoment_smul_le`, `TauCeti.rademacherSecondMoment_smul_le_norm_toLp_top`:
  `R₂` contraction principle.
* `TauCeti.rademacherMoment_ite_mem_le`: subset restriction bound on a finite index type.
* `TauCeti.rademacherMoment_subtype_mono`, `TauCeti.abs_rademacherMoment_subtype_sub_le`,
  `TauCeti.tendsto_rademacherMoment_subtype_atTop_ciSup`: monotonicity, Cauchy bound, and
  convergence of finite truncations of an arbitrary family.

## References

* M. Ledoux and M. Talagrand, *Probability in Banach Spaces*, Theorem 4.4.
* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Proposition 6.1.5.
-/

public section

noncomputable section

open Filter Finset
open scoped BigOperators ENNReal Topology

namespace TauCeti

section Contraction

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [SeminormedAddCommGroup E]

/-- Replacing a single real coefficient `α i₀ ∈ [-1, 1]` by `1` does not decrease
`𝔼_ε Φ ‖∑ i, εᵢ (αᵢ xᵢ)‖` when `Φ` is convex and monotone on `[0, ∞)`. -/
private theorem expect_apply_norm_sum_smul_le_update_one [NormedSpace ℝ E] {Φ : ℝ → ℝ}
    (hΦ_conv : ConvexOn ℝ (Set.Ici 0) Φ) (hΦ_mono : MonotoneOn Φ (Set.Ici 0))
    (α : ι → ℝ) {i₀ : ι} (hi₀ : |α i₀| ≤ 1) (x : ι → E) :
    𝔼 ε : ι → ℤˣ, Φ ‖∑ i, ε i • (α i • x i)‖ ≤
      𝔼 ε : ι → ℤˣ, Φ ‖∑ i, ε i • (Function.update α i₀ 1 i • x i)‖ := by
  obtain ⟨hneg, hpos⟩ := abs_le.1 hi₀
  let a : ℝ := (1 - α i₀) / 2
  let b : ℝ := (1 + α i₀) / 2
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hab : a + b = 1 := by dsimp [a, b]; ring
  let u (ε : ι → ℤˣ) : E := ∑ i ∈ univ.erase i₀, ε i • (α i • x i)
  let v (ε : ι → ℤˣ) : E := ε i₀ • x i₀
  have hsplit (β : ι → ℝ) (ε : ι → ℤˣ) (hβ : ∀ i ≠ i₀, β i = α i) :
      ∑ i, ε i • (β i • x i) = u ε + β i₀ • v ε := by
    rw [← add_sum_erase _ _ (mem_univ i₀), add_comm, smul_comm (ε i₀) (β i₀)]
    congr 1
    exact sum_congr rfl fun i hi ↦ by rw [hβ i (ne_of_mem_erase hi)]
  have hpt (ε : ι → ℤˣ) :
      Φ ‖u ε + α i₀ • v ε‖ ≤ a * Φ ‖u ε - v ε‖ + b * Φ ‖u ε + v ε‖ := by
    have hba : b - a = α i₀ := by dsimp [a, b]; ring
    have hlin : u ε + α i₀ • v ε = a • (u ε - v ε) + b • (u ε + v ε) := calc
      u ε + α i₀ • v ε = (a + b) • u ε + (b - a) • v ε := by rw [hab, hba, one_smul]
      _ = a • (u ε - v ε) + b • (u ε + v ε) := by
        rw [add_smul, sub_smul, smul_sub, smul_add]; abel
    have hnorm : ‖u ε + α i₀ • v ε‖ ≤ a * ‖u ε - v ε‖ + b * ‖u ε + v ε‖ := by
      rw [hlin]
      exact (norm_add_le _ _).trans_eq (by rw [norm_smul_of_nonneg ha, norm_smul_of_nonneg hb])
    exact (hΦ_mono (Set.mem_Ici.2 (norm_nonneg _)) (Set.mem_Ici.2 (by positivity)) hnorm).trans
      (hΦ_conv.2 (Set.mem_Ici.2 (norm_nonneg _)) (Set.mem_Ici.2 (norm_nonneg _)) ha hb hab)
  let σ := Equiv.mulLeft (Pi.mulSingle i₀ (-1) : ι → ℤˣ)
  have hflip : 𝔼 ε : ι → ℤˣ, Φ ‖u ε - v ε‖ = 𝔼 ε : ι → ℤˣ, Φ ‖u ε + v ε‖ := by
    refine Fintype.expect_equiv σ _ _ fun ε ↦ ?_
    have hu : u (σ ε) = u ε := sum_congr rfl fun i hi ↦ by
      simp [σ, Pi.mulSingle_eq_of_ne (ne_of_mem_erase hi)]
    have hv : v (σ ε) = -v ε := by simp [v, σ, Units.smul_def]
    rw [hu, hv, ← sub_eq_add_neg]
  simp_rw [hsplit α _ (fun _ _ ↦ rfl),
    hsplit (Function.update α i₀ 1) _ (fun _ hi ↦ Function.update_of_ne hi 1 α),
    Function.update_self, one_smul]
  calc 𝔼 ε : ι → ℤˣ, Φ ‖u ε + α i₀ • v ε‖
      ≤ 𝔼 ε : ι → ℤˣ, (a * Φ ‖u ε - v ε‖ + b * Φ ‖u ε + v ε‖) :=
        expect_le_expect fun ε _ ↦ hpt ε
    _ = 𝔼 ε : ι → ℤˣ, Φ ‖u ε + v ε‖ := by
        rw [expect_add_distrib, ← mul_expect, ← mul_expect, hflip, ← add_mul, hab, one_mul]

/-- Unit-interval form of convex contraction: if `∀ i, |α i| ≤ 1`, replacing every `α i` by `1`
does not decrease `𝔼_ε Φ ‖∑ i, εᵢ (αᵢ xᵢ)‖`. -/
private theorem expect_apply_norm_sum_smul_le_of_abs_le_one [NormedSpace ℝ E] {Φ : ℝ → ℝ}
    (hΦ_conv : ConvexOn ℝ (Set.Ici 0) Φ) (hΦ_mono : MonotoneOn Φ (Set.Ici 0))
    {α : ι → ℝ} (hα : ∀ i, |α i| ≤ 1) (x : ι → E) :
    𝔼 ε : ι → ℤˣ, Φ ‖∑ i, ε i • (α i • x i)‖ ≤ 𝔼 ε : ι → ℤˣ, Φ ‖∑ i, ε i • x i‖ := by
  suffices ∀ (s : Finset ι) (β : ι → ℝ), (∀ i ∈ s, |β i| ≤ 1) →
      𝔼 ε : ι → ℤˣ, Φ ‖∑ i, ε i • (β i • x i)‖ ≤
        𝔼 ε : ι → ℤˣ, Φ ‖∑ i, ε i • ((if i ∈ s then 1 else β i) • x i)‖ by
    simpa using this univ α fun i _ ↦ hα i
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i₀ s hi₀ ih =>
    intro β hβ
    refine (expect_apply_norm_sum_smul_le_update_one hΦ_conv hΦ_mono β
      (hβ i₀ (mem_insert_self i₀ s)) x).trans ?_
    refine (ih (Function.update β i₀ 1) fun i hi ↦ ?_).trans_eq ?_
    · rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hi₀)]
      exact hβ i (mem_insert_of_mem hi)
    · congr 1; ext ε; congr 2; refine sum_congr rfl fun i _ ↦ ?_
      by_cases hi : i = i₀
      · subst hi; simp [hi₀]
      · simp [hi]

/-- **Convex Rademacher contraction principle.** For any convex nondecreasing function `Φ` on
`[0, ∞)` and real coefficients satisfying `∀ i, |α i| ≤ M`, the average of
`Φ ‖∑ i, εᵢ (αᵢ xᵢ)‖` is at most that of `Φ (M * ‖∑ i, εᵢ xᵢ‖)`. -/
theorem expect_apply_norm_sum_smul_le [NormedSpace ℝ E] {Φ : ℝ → ℝ}
    (hΦ_conv : ConvexOn ℝ (Set.Ici 0) Φ) (hΦ_mono : MonotoneOn Φ (Set.Ici 0))
    {α : ι → ℝ} {M : ℝ} (hα : ∀ i, |α i| ≤ M) (x : ι → E) :
    𝔼 ε : ι → ℤˣ, Φ ‖∑ i, ε i • (α i • x i)‖ ≤
      𝔼 ε : ι → ℤˣ, Φ (M * ‖∑ i, ε i • x i‖) := by
  rcases isEmpty_or_nonempty ι with hι | hne
  · simp
  obtain ⟨i₀⟩ := hne
  have hM : 0 ≤ M := (abs_nonneg (α i₀)).trans (hα i₀)
  rcases eq_or_lt_of_le hM with rfl | hMpos
  · have hα₀ (i : ι) : α i = 0 := abs_nonpos_iff.1 (hα i)
    simp [hα₀]
  · let Ψ (t : ℝ) : ℝ := Φ (M * t)
    have hΨ_conv : ConvexOn ℝ (Set.Ici 0) Ψ := by
      refine ⟨convex_Ici 0, fun u hu v hv a b ha hb hab ↦ ?_⟩
      dsimp [Ψ]
      rw [mul_add, mul_left_comm M a u, mul_left_comm M b v]
      exact hΦ_conv.2 (Set.mem_Ici.2 (mul_nonneg hM hu))
        (Set.mem_Ici.2 (mul_nonneg hM hv)) ha hb hab
    have hΨ_mono : MonotoneOn Ψ (Set.Ici 0) := fun u hu v hv huv ↦
      hΦ_mono (Set.mem_Ici.2 (mul_nonneg hM hu)) (Set.mem_Ici.2 (mul_nonneg hM hv))
        (mul_le_mul_of_nonneg_left huv hM)
    have hβ (i : ι) : |α i / M| ≤ 1 := by
      rw [abs_div, abs_of_pos hMpos]
      exact (div_le_one hMpos).2 (hα i)
    have key := expect_apply_norm_sum_smul_le_of_abs_le_one hΨ_conv hΨ_mono hβ x
    refine le_of_eq_of_le ?_ key
    congr 1; ext ε
    dsimp [Ψ]
    rw [← norm_smul_of_nonneg hM, smul_sum]
    congr 2
    refine sum_congr rfl fun i _ ↦ ?_
    rw [smul_comm M (ε i), smul_smul, mul_div_cancel₀ _ hMpos.ne']

/-- **Kahane–Khintchine contraction principle** in `L¹`: if `∀ i, |α i| ≤ M`, then
`𝔼_ε ‖∑ i, εᵢ (αᵢ xᵢ)‖ ≤ M * 𝔼_ε ‖∑ i, εᵢ xᵢ‖`. -/
theorem expect_norm_sum_smul_le [NormedSpace ℝ E] {α : ι → ℝ} {M : ℝ} (hα : ∀ i, |α i| ≤ M)
    (x : ι → E) :
    𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • (α i • x i)‖ ≤ M * 𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • x i‖ := by
  simpa [mul_expect] using
    expect_apply_norm_sum_smul_le (convexOn_id (convex_Ici 0)) monotoneOn_id hα x

/-- **`L¹` contraction principle** written with the `ℓ^∞` norm `‖WithLp.toLp ∞ α‖`. -/
theorem expect_norm_sum_smul_le_norm_toLp_top [NormedSpace ℝ E] (α : ι → ℝ) (x : ι → E) :
    𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • (α i • x i)‖ ≤
      ‖WithLp.toLp ∞ α‖ * 𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • x i‖ :=
  expect_norm_sum_smul_le (fun i ↦ PiLp.norm_apply_le (WithLp.toLp ∞ α) i) x

/-- **Kahane–Khintchine contraction principle** for `K_p` (`1 ≤ p`): if `∀ i, |α i| ≤ M`, then
`K_p(αᵢ • xᵢ) ≤ M * K_p(x)`. -/
theorem rademacherMoment_smul_le [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p) {α : ι → ℝ} {M : ℝ}
    (hα : ∀ i, |α i| ≤ M) (x : ι → E) :
    rademacherMoment p (fun i ↦ α i • x i) ≤ M * rademacherMoment p x := by
  have hp₀ : 0 < p := zero_lt_one.trans_le hp
  rcases isEmpty_or_nonempty ι with hι | hne
  · simp [rademacherMoment_of_isEmpty hp₀.ne']
  obtain ⟨i₀⟩ := hne
  have hM : 0 ≤ M := (abs_nonneg (α i₀)).trans (hα i₀)
  refine rademacherMoment_le_of_rpow_le hp₀ (mul_nonneg hM (rademacherMoment_nonneg p x)) ?_
  have hconv := expect_apply_norm_sum_smul_le (convexOn_rpow hp)
    (Real.monotoneOn_rpow_Ici_of_exponent_nonneg hp₀.le) hα x
  refine hconv.trans_eq ?_
  simp_rw [Real.mul_rpow hM (norm_nonneg _), ← mul_expect, ← rademacherMoment_rpow]
  rw [← Real.mul_rpow hM (rademacherMoment_nonneg p x)]

/-- **`K_p` contraction principle** (`1 ≤ p`) written with `‖WithLp.toLp ∞ α‖`. -/
theorem rademacherMoment_smul_le_norm_toLp_top [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p)
    (α : ι → ℝ) (x : ι → E) :
    rademacherMoment p (fun i ↦ α i • x i) ≤ ‖WithLp.toLp ∞ α‖ * rademacherMoment p x :=
  rademacherMoment_smul_le hp (fun i ↦ PiLp.norm_apply_le (WithLp.toLp ∞ α) i) x

/-- **Contraction principle for `rademacherSecondMoment`**: if `∀ i, |α i| ≤ M`, then
`R₂(αᵢ • xᵢ) ≤ M * R₂(x)`. -/
theorem rademacherSecondMoment_smul_le [NormedSpace ℝ E] {α : ι → ℝ} {M : ℝ}
    (hα : ∀ i, |α i| ≤ M) (x : ι → E) :
    rademacherSecondMoment (fun i ↦ α i • x i) ≤ M * rademacherSecondMoment x := by
  simpa [← rademacherMoment_two] using rademacherMoment_smul_le one_le_two hα x

/-- **Contraction principle for `rademacherSecondMoment`** written with `‖WithLp.toLp ∞ α‖`. -/
theorem rademacherSecondMoment_smul_le_norm_toLp_top [NormedSpace ℝ E] (α : ι → ℝ) (x : ι → E) :
    rademacherSecondMoment (fun i ↦ α i • x i) ≤
      ‖WithLp.toLp ∞ α‖ * rademacherSecondMoment x :=
  rademacherSecondMoment_smul_le (fun i ↦ PiLp.norm_apply_le (WithLp.toLp ∞ α) i) x

/-- Setting coordinates outside a subset `s` to zero does not increase `rademacherMoment p` for
`1 ≤ p` in a real normed space. -/
theorem rademacherMoment_ite_mem_le [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p) (s : Finset ι)
    (x : ι → E) :
    rademacherMoment p (fun i ↦ if i ∈ s then x i else 0) ≤ rademacherMoment p x := by
  have h := rademacherMoment_smul_le hp (α := fun i ↦ if i ∈ s then (1 : ℝ) else 0) (M := 1)
    (fun i ↦ by split_ifs <;> norm_num) x
  simpa [ite_smul] using h

end Contraction

/-! ### Finite truncations of an arbitrary indexed family -/

section Truncation

variable {α E : Type*} [DecidableEq α] [SeminormedAddCommGroup E]

/-- Padding a restriction to `s` with zeros on `t \ s` (`s ⊆ t`) gives the indicator-masked family
on `t`, with the same Rademacher `p`-th moment. -/
private theorem rademacherMoment_subtype_eq_ite {s t : Finset α} (hst : s ⊆ t) (p : ℝ)
    (x : α → E) :
    rademacherMoment p (fun i : s ↦ x i) =
      rademacherMoment p (fun j : t ↦ if (j : α) ∈ s then x j else 0) := by
  let e : s ⊕ (t \ s : Finset α) ≃ t :=
    { toFun := Sum.elim (fun i ↦ ⟨i.1, hst i.2⟩) (fun i ↦ ⟨i.1, (Finset.mem_sdiff.1 i.2).1⟩)
      invFun := fun j ↦ if hj : (j : α) ∈ s then Sum.inl ⟨j, hj⟩
        else Sum.inr ⟨j, Finset.mem_sdiff.2 ⟨j.2, hj⟩⟩
      left_inv := by
        rintro (⟨i, hi⟩ | ⟨i, hi⟩)
        · simp [hi]
        · simp [(Finset.mem_sdiff.1 hi).2]
      right_inv := fun ⟨j, hj⟩ ↦ by by_cases h : j ∈ s <;> simp [h] }
  rw [← rademacherMoment_sumElim_zero (κ := (t \ s : Finset α)) p (fun i : s ↦ x i),
    ← rademacherMoment_comp_equiv e.symm p]
  congr 1; ext j
  by_cases hj : (j : α) ∈ s <;> simp [e, hj]

/-- For `1 ≤ p` in a real normed space, the Rademacher `p`-th moment of the finite truncations
`s ↦ K_p(x|_s)` is monotone with respect to inclusion `s ⊆ t`. -/
theorem rademacherMoment_subtype_mono [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p) (x : α → E) :
    Monotone (fun s : Finset α ↦ rademacherMoment p (fun i : s ↦ x i)) := by
  intro s t hst
  dsimp only
  rw [rademacherMoment_subtype_eq_ite hst p x]
  exact rademacherMoment_ite_mem_le hp (univ.filter fun j : t ↦ (j : α) ∈ s) (fun j : t ↦ x j)
    |>.trans_eq' (by congr 1; ext j; simp)

/-- For `1 ≤ p` and `s ⊆ t`, the difference between the Rademacher `p`-th moments on `t` and `s`
is bounded by the Rademacher `p`-th moment on `t \ s`. -/
theorem abs_rademacherMoment_subtype_sub_le {p : ℝ} (hp : 1 ≤ p) {s t : Finset α} (hst : s ⊆ t)
    (x : α → E) :
    |rademacherMoment p (fun i : t ↦ x i) - rademacherMoment p (fun i : s ↦ x i)| ≤
      rademacherMoment p (fun i : (t \ s : Finset α) ↦ x i) := by
  rw [rademacherMoment_subtype_eq_ite hst p x,
    rademacherMoment_subtype_eq_ite sdiff_subset p x]
  refine (abs_rademacherMoment_sub_le hp _ _).trans_eq ?_
  congr 1; ext j
  by_cases hj : (j : α) ∈ s <;> simp [hj, j.2]

/-- If the finite truncations `s ↦ K_p(x|_s)` (`1 ≤ p`) are bounded above in a real normed space,
they converge along `Filter.atTop` to their supremum. -/
theorem tendsto_rademacherMoment_subtype_atTop_ciSup [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p)
    (x : α → E)
    (hbdd : BddAbove (Set.range fun s : Finset α ↦ rademacherMoment p (fun i : s ↦ x i))) :
    Tendsto (fun s : Finset α ↦ rademacherMoment p (fun i : s ↦ x i)) atTop
      (𝓝 (⨆ s : Finset α, rademacherMoment p (fun i : s ↦ x i))) :=
  tendsto_atTop_ciSup (rademacherMoment_subtype_mono hp x) hbdd

/-- If `∑' i, ‖x i‖` converges, the finite truncations `s ↦ K_p(x|_s)` (`1 ≤ p`) are bounded above
and converge along `Filter.atTop` to their supremum in any real normed space. -/
theorem tendsto_rademacherMoment_subtype_of_summable_norm [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p)
    {x : α → E} (hx : Summable fun i ↦ ‖x i‖) :
    Tendsto (fun s : Finset α ↦ rademacherMoment p (fun i : s ↦ x i)) atTop
      (𝓝 (⨆ s : Finset α, rademacherMoment p (fun i : s ↦ x i))) := by
  refine tendsto_rademacherMoment_subtype_atTop_ciSup hp x ⟨∑' i, ‖x i‖, ?_⟩
  rintro _ ⟨s, rfl⟩
  calc rademacherMoment p (fun i : s ↦ x i)
      ≤ ∑ i : s, ‖x i‖ := rademacherMoment_le_sum_norm (zero_lt_one.trans_le hp) _
    _ = ∑ i ∈ s, ‖x i‖ := s.sum_coe_sort (fun i ↦ ‖x i‖)
    _ ≤ ∑' i, ‖x i‖ := hx.sum_le_tsum s fun _ _ ↦ norm_nonneg _

end Truncation

end TauCeti
