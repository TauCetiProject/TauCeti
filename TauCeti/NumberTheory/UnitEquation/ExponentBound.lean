/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Log.AddMulLog
public import TauCeti.NumberTheory.NumberField.Units.House

/-!
# An explicit exponent bound for the unit equation

Let `K` be a number field of degree `d`, let `u` be a family of `rank K` units of maximal rank,
and let `α, β ∈ Kˣ`. We bound the exponents of the solutions `x, y ∈ (𝓞 K)ˣ` of the unit
equation `α x + β y = 1`, assuming a lower bound for linear forms in logarithms in its
multiplicative form: for some `C ≥ 0`, every complex embedding `σ`, every
`γ ∈ {α ζ, β ζ : ζ ∈ torsion K}` and every `e ∈ ℤ^r` with `σ (γ * ∏ j, u j ^ e j) ≠ 1`,

  `|σ (γ * ∏ j, u j ^ e j) - 1| ≥ (exp 1 * max(1, maxⱼ |e j|)) ^ (-C)`.

Baker's theorem supplies such a `C`. Writing `x = ζₓ * ∏ j, u j ^ e j` and
`y = ζ_y * ∏ j, u j ^ f j` with `ζₓ, ζ_y` roots of unity, the bound is
`maxⱼ max(|e j|, |f j|) ≤ max(1, 2 A + 2 B₀ (log (2 B₀) - 1))`, where
`κ = 2 (d - 1) κ(u)`, `κ(u)` is the operator norm of the coordinate map of the logarithmic
space on the basis given by `u`, `H = max(house α, house β)`, `A = κ (d - 1) (log H + C)` and
`B₀ = κ (d - 1) C`.

The proof bounds the houses of both unknowns. A unit `y` has a conjugate `σ y` of absolute value
at most `house y ^ (-1 / (d - 1))`, so `σ (α x) - 1 = -σ (β y)` is small, and the lower bound
gives `log (house y) ≤ (d - 1) (log H + C (1 + log M))`, where `M = max(1, B)` and
`B = maxⱼ max(|e j|, |f j|)` is the largest exponent. The exponent bound `|e j| ≤ κ log (house x)`
for units turns this into `B ≤ A + B₀ log M`. If `B ≤ 1` the final bound is immediate; otherwise
`M = B`, and `B ≤ A + B₀ log B` is solved for `B`. With `C` a Baker constant for the finitely
many relevant tuples, the bound confines the solutions of the unit equation to an explicit finite
region.

## Main results

* `TauCeti.NumberField.Units.max_abs_le_of_mul_add_mul_eq_one`: the exponent bound above.

## References

* [J.-H. Evertse, *Diophantine Approximation*, lecture notes, Leiden/Mastermath, 2019],
  Chapter 5, Theorem 5.12 and its proof, pp. 94–95.
-/

public section

open Module NumberField NumberField.InfinitePlace NumberField.Units
open NumberField.Units.dirichletUnitTheorem
open scoped NumberField

namespace TauCeti.NumberField.Units

variable {K : Type*} [Field K] [NumberField K]

/-- Let `z + δ y = 1` with `y` a unit, `δ ≠ 0` and `house δ ≤ H`. If
`|σ z - 1| ≥ (exp 1 * M) ^ (-C)` whenever `σ z ≠ 1`, then
`log (house y) ≤ (d - 1) (log H + C (1 + log M))`. -/
private theorem log_house_le_of_add_mul_eq_one (hd : 2 ≤ finrank ℚ K) {z δ : K} (hδ : δ ≠ 0)
    {H : ℝ} (hδH : house δ ≤ H) {y : (𝓞 K)ˣ} (h : z + δ * y = 1) {C M : ℝ} (hM : 0 < M)
    (hLB : ∀ σ : K →+* ℂ, σ z ≠ 1 → (Real.exp 1 * M) ^ (-C) ≤ ‖σ z - 1‖) :
    Real.log (house (y : K)) ≤
      (finrank ℚ K - 1 : ℝ) * (Real.log H + C * (1 + Real.log M)) := by
  obtain ⟨σ, hσ⟩ := Units.exists_norm_embedding_le_house_rpow y hd
  have hz : σ z - 1 = -(σ δ * σ y) := by
    have := congrArg σ h
    rw [map_add, map_mul, map_one] at this
    linear_combination this
  have hσy : σ δ * σ y ≠ 0 :=
    mul_ne_zero ((map_ne_zero σ).mpr hδ) ((map_ne_zero σ).mpr (coe_ne_zero y))
  have hne : σ z ≠ 1 := fun h1 ↦ hσy (by rw [h1, sub_self] at hz; exact neg_eq_zero.mp hz.symm)
  have hδpos : 0 < house δ :=
    (norm_pos_iff.mpr ((map_ne_zero σ).mpr hδ)).trans_le (norm_embedding_le_house δ σ)
  have hHy : 0 < house (y : K) := zero_lt_one.trans_le (Units.one_le_house y)
  have hd1 : (0 : ℝ) < finrank ℚ K - 1 := by
    rw [sub_pos, Nat.one_lt_cast]
    omega
  -- The lower bound against the upper bound `house δ * house y ^ (-1 / (d - 1))`.
  have key : (Real.exp 1 * M) ^ (-C) ≤ house δ * house (y : K) ^ (-1 / (finrank ℚ K - 1 : ℝ)) := by
    refine (hLB σ hne).trans ?_
    rw [hz, norm_neg, norm_mul]
    exact mul_le_mul (norm_embedding_le_house δ σ) hσ (norm_nonneg _) hδpos.le
  have hlog := Real.log_le_log (by positivity) key
  rw [Real.log_rpow (by positivity), Real.log_mul hδpos.ne' (by positivity), Real.log_rpow hHy,
    Real.log_mul (Real.exp_pos 1).ne' hM.ne', Real.log_exp] at hlog
  have hdiv : -1 / (finrank ℚ K - 1 : ℝ) * Real.log (house (y : K)) =
      -(Real.log (house (y : K)) / (finrank ℚ K - 1 : ℝ)) := by
    ring
  rw [hdiv] at hlog
  rw [← div_le_iff₀' hd1]
  linarith [Real.log_le_log hδpos hδH]

open scoped Classical in
/-- Under the hypotheses of `log_house_le_of_add_mul_eq_one`, if `y = ζ ∏ j, u j ^ e j` with `ζ` a
root of unity and `u` of maximal rank, then
`|e j| ≤ 2 (d - 1) κ(u) ((d - 1) (log H + C (1 + log M)))`. -/
private theorem abs_le_of_add_mul_eq_one {u : Fin (rank K) → (𝓞 K)ˣ} (hu : IsMaxRank u)
    (hd : 2 ≤ finrank ℚ K) {z δ : K} (hδ : δ ≠ 0) {H : ℝ} (hδH : house δ ≤ H)
    {y ζ : (𝓞 K)ˣ} (hζ : ζ ∈ torsion K) {e : Fin (rank K) → ℤ} (hy : y = ζ * ∏ j, u j ^ e j)
    (h : z + δ * y = 1) {C M : ℝ} (hM : 0 < M)
    (hLB : ∀ σ : K →+* ℂ, σ z ≠ 1 → (Real.exp 1 * M) ^ (-C) ≤ ‖σ z - 1‖) (j : Fin (rank K)) :
    |(e j : ℝ)| ≤ 2 * (finrank ℚ K - 1) *
      ‖((basisOfIsMaxRank hu).equivFunL : logSpace K →L[ℝ] Fin (rank K) → ℝ)‖ *
        ((finrank ℚ K - 1 : ℝ) * (Real.log H + C * (1 + Real.log M))) := by
  have hd1 : (0 : ℝ) ≤ finrank ℚ K - 1 := by
    rw [sub_nonneg, Nat.one_le_cast]
    omega
  exact (abs_le_mul_log_house_of_eq_mul_prod_zpow hu hζ hy j).trans
    (mul_le_mul_of_nonneg_left (log_house_le_of_add_mul_eq_one hd hδ hδH h hM hLB)
      (by positivity))

open scoped Classical in
/-- **Exponent bound for the unit equation.** Let `u` be a family of units of maximal rank in a
number field `K` of degree `d`, let `α, β ≠ 0`, and let `C ≥ 0` be such that for every complex
embedding `σ`, every `γ ∈ {α, β}`, every root of unity `ζ` and every `e ∈ ℤ^r`,
`|σ (γ ζ ∏ j, u j ^ e j) - 1| ≥ (exp 1 * max(1, maxⱼ |e j|)) ^ (-C)` unless
`σ (γ ζ ∏ j, u j ^ e j) = 1`. If `α x + β y = 1` with `x = ζₓ ∏ j, u j ^ e j` and
`y = ζ_y ∏ j, u j ^ f j` for roots of unity `ζₓ, ζ_y`, then
`max(|e j|, |f j|) ≤ max(1, 2 A + 2 B₀ (log (2 B₀) - 1))` for every `j`, where
`κ = 2 (d - 1) ‖(basisOfIsMaxRank hu).equivFunL‖`, `A = κ (d - 1) (log H + C)` with
`H = max(house α, house β)`, and `B₀ = κ (d - 1) C`. -/
theorem max_abs_le_of_mul_add_mul_eq_one {u : Fin (rank K) → (𝓞 K)ˣ} (hu : IsMaxRank u)
    {α β : K} (hα : α ≠ 0) (hβ : β ≠ 0) {C : ℝ} (hC : 0 ≤ C)
    (hLB : ∀ σ : K →+* ℂ, ∀ γ ∈ ({α, β} : Set K), ∀ ζ ∈ torsion K, ∀ e : Fin (rank K) → ℤ,
      σ (γ * ζ * ∏ j, (u j : K) ^ e j) ≠ 1 →
        (Real.exp 1 * max 1 ((Finset.univ.sup fun j ↦ (e j).natAbs : ℕ) : ℝ)) ^ (-C) ≤
          ‖σ (γ * ζ * ∏ j, (u j : K) ^ e j) - 1‖)
    {x y ζx ζy : (𝓞 K)ˣ} (hxy : α * x + β * y = 1) (hζx : ζx ∈ torsion K)
    (hζy : ζy ∈ torsion K) {ex ey : Fin (rank K) → ℤ} (hx : x = ζx * ∏ j, u j ^ ex j)
    (hy : y = ζy * ∏ j, u j ^ ey j) (j : Fin (rank K)) :
    let κ : ℝ := 2 * (finrank ℚ K - 1) *
      ‖((basisOfIsMaxRank hu).equivFunL : logSpace K →L[ℝ] Fin (rank K) → ℝ)‖
    let A : ℝ := κ * (finrank ℚ K - 1) * (Real.log (max (house α) (house β)) + C)
    let B₀ : ℝ := κ * (finrank ℚ K - 1) * C
    max |(ex j : ℝ)| |(ey j : ℝ)| ≤ max 1 (2 * A + 2 * B₀ * (Real.log (2 * B₀) - 1)) := by
  intro κ A B₀
  set H := max (house α) (house β)
  -- The largest exponent `Bn` is attained at some `j₀`.
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_mem_eq_sup Finset.univ ⟨j, Finset.mem_univ j⟩
    fun j ↦ max (ex j).natAbs (ey j).natAbs
  set Bn : ℕ := Finset.univ.sup fun j ↦ max (ex j).natAbs (ey j).natAbs
  set M : ℝ := max 1 (Bn : ℝ)
  have hM : 0 < M := zero_lt_one.trans_le (le_max_left _ _)
  -- A positive unit rank forces `d ≥ 2`.
  have hd : 2 ≤ finrank ℚ K := by
    have h1 := j.pos
    have h2 := card_add_two_mul_card_eq_rank K
    have h3 := card_eq_nrRealPlaces_add_nrComplexPlaces K
    rw [rank] at h1
    omega
  have hB₀ : 0 ≤ B₀ := by
    have hd1 : (0 : ℝ) ≤ finrank ℚ K - 1 := by
      rw [sub_nonneg, Nat.one_le_cast]
      omega
    positivity
  have hcoe (e : Fin (rank K) → ℤ) :
      ((∏ j, u j ^ e j : (𝓞 K)ˣ) : K) = ∏ j, (u j : K) ^ e j := by
    simp only [← coe_zpow]
    exact map_prod ((Units.coeHom K).comp (Units.map (algebraMap (𝓞 K) K).toMonoidHom)) _ _
  -- The lower bound, with `max 1 (maxⱼ |e j|)` enlarged to `M`.
  have hLB' {γ : K} (hγ : γ ∈ ({α, β} : Set K)) {ζ : (𝓞 K)ˣ} (hζ : ζ ∈ torsion K)
      {e : Fin (rank K) → ℤ} (he : (Finset.univ.sup fun j ↦ (e j).natAbs) ≤ Bn)
      {w : (𝓞 K)ˣ} (hw : w = ζ * ∏ j, u j ^ e j) (σ : K →+* ℂ) (hσ : σ (γ * w) ≠ 1) :
      (Real.exp 1 * M) ^ (-C) ≤ ‖σ (γ * w) - 1‖ := by
    have hγw : γ * (w : K) = γ * ζ * ∏ j, (u j : K) ^ e j := by
      rw [hw, coe_mul, hcoe, mul_assoc]
    rw [hγw] at hσ ⊢
    refine (Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (neg_nonpos.mpr hC)).trans
      (hLB σ γ hγ ζ hζ e hσ)
    gcongr
    exact max_le_max le_rfl (by exact_mod_cast he)
  -- Hence every exponent is at most `A + B₀ log M`.
  have hexp (j : Fin (rank K)) : max |(ex j : ℝ)| |(ey j : ℝ)| ≤ A + B₀ * Real.log M := by
    have hAB : κ * ((finrank ℚ K - 1 : ℝ) * (Real.log H + C * (1 + Real.log M))) =
        A + B₀ * Real.log M := by
      simp only [A, B₀, H]
      ring
    rw [← hAB]
    exact max_le
      (abs_le_of_add_mul_eq_one hu hd hα (le_max_left _ _) hζx hx (by rwa [add_comm]) hM
        (hLB' (by simp) hζy (Finset.sup_mono_fun fun j _ ↦ le_max_right _ _) hy) j)
      (abs_le_of_add_mul_eq_one hu hd hβ (le_max_right _ _) hζy hy hxy hM
        (hLB' (by simp) hζx (Finset.sup_mono_fun fun j _ ↦ le_max_left _ _) hx) j)
  -- The largest exponent `Bn` satisfies `Bn ≤ A + B₀ log (max 1 Bn)`.
  have hcast (j : Fin (rank K)) :
      ((max (ex j).natAbs (ey j).natAbs : ℕ) : ℝ) = max |(ex j : ℝ)| |(ey j : ℝ)| := by
    rw [Nat.cast_max, Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]
  have hBn : (Bn : ℝ) ≤ A + B₀ * Real.log M := by
    rw [hj₀, hcast]
    exact hexp j₀
  have hj : max |(ex j : ℝ)| |(ey j : ℝ)| ≤ Bn := by
    rw [← hcast]
    exact_mod_cast Finset.le_sup (f := fun j ↦ max (ex j).natAbs (ey j).natAbs)
      (Finset.mem_univ j)
  rcases le_or_gt (Bn : ℝ) 1 with h1 | h1
  · exact hj.trans (h1.trans (le_max_left _ _))
  · have hMB : M = Bn := max_eq_right h1.le
    rw [hMB] at hBn
    exact hj.trans ((Real.le_two_mul_add_of_le_add_mul_log hB₀ (zero_lt_one.trans h1) hBn).trans
      (le_max_right _ _))

end TauCeti.NumberField.Units
