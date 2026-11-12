/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Exponential

/-!
# Decay of the derivatives of `exp ∘ ℓ`

Let `ℓ : E → ℝ` be smooth on a real normed space. By the Leibniz rule applied to
`D (exp ∘ ℓ) = exp ℓ • D ℓ`, the derivatives of `exp ∘ ℓ` are controlled by those of `ℓ`. This
file records the estimates used to differentiate semilinear equations such as
`Δ ℓ = (exp ℓ - 1) / 4`:

* if `exp ∘ ℓ` is bounded along a filter and the derivatives of `ℓ` of orders `1, …, N` are
  `O(g)` for a bounded weight `g`, then so are those of `exp ∘ ℓ`
  (`TauCeti.isBigO_norm_iteratedFDeriv_exp_comp`);
* the Leibniz residual `Dⁿ (exp ∘ ℓ) - exp ℓ • Dⁿ ℓ` involves only derivatives of `ℓ` of order
  less than `n` (`TauCeti.norm_iteratedFDeriv_exp_comp_sub_smul_le`), and so does its derivative
  up to one top-order term (`TauCeti.norm_fderiv_iteratedFDeriv_exp_comp_sub_smul_le`); hence it
  decays with the lower derivatives (`TauCeti.isBigO_norm_fderiv_iteratedFDeriv_exp_comp_sub_smul`);
* if moreover `ℓ → 0`, the derivatives of `exp ∘ ℓ - 1` of every order are `O(g)`
  (`TauCeti.isBigO_norm_iteratedFDeriv_exp_comp_sub_one`).

It also records two elementary facts about exponential weights `exp (-c ‖z‖)`: a mean value bound
for a map whose derivative decays at that rate
(`TauCeti.norm_sub_comp_add_le_of_norm_fderiv_le`), and the extraction of an explicit radius and
a nonnegative constant from an `O(exp (-c ‖z‖))` bound at infinity
(`TauCeti.exists_nonneg_forall_norm_le_mul_exp_of_isBigO`).
-/

public section

noncomputable section

namespace TauCeti

open Filter Metric Topology Asymptotics
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative of `exp ∘ ℓ` is `exp ℓ • fderiv ℓ`. -/
private theorem fderiv_exp_comp {ℓ : E → ℝ} (hℓ : Differentiable ℝ ℓ) :
    fderiv ℝ (fun w ↦ Real.exp (ℓ w)) = fun w ↦ Real.exp (ℓ w) • fderiv ℝ ℓ w :=
  funext fun w ↦ fderiv_exp (hℓ w)

/-- **Derivatives of `exp ∘ ℓ`.** Let `g` be a weight bounded along a filter `l`. If `exp ∘ ℓ` is
bounded along `l` and the derivatives of `ℓ` of orders `1, …, N` are `O(g)` along `l`, then so
are those of `exp ∘ ℓ`. -/
theorem isBigO_norm_iteratedFDeriv_exp_comp {ℓ : E → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) {l : Filter E}
    {g : E → ℝ} (hg : g =O[l] fun _ ↦ (1 : ℝ))
    (hbdd : (fun z ↦ Real.exp (ℓ z)) =O[l] fun _ ↦ (1 : ℝ)) {N : ℕ}
    (hdec : ∀ j, 1 ≤ j → j ≤ N → (fun z ↦ ‖iteratedFDeriv ℝ j ℓ z‖) =O[l] g)
    {i : ℕ} (hi₁ : 1 ≤ i) (hiN : i ≤ N) :
    (fun z ↦ ‖iteratedFDeriv ℝ i (fun w ↦ Real.exp (ℓ w)) z‖) =O[l] g := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hE : ContDiff ℝ ∞ (fun w ↦ Real.exp (ℓ w)) := Real.contDiff_exp.comp hℓ
  have hℓ' : ContDiff ℝ ∞ (fderiv ℝ ℓ) := hℓ.fderiv_right (by norm_cast)
  -- Leibniz: `D^(k+1) exp ℓ = D^k (exp ℓ • Dℓ)`.
  have hle (z : E) : ‖iteratedFDeriv ℝ (k + 1) (fun w ↦ Real.exp (ℓ w)) z‖ ≤
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
        ‖iteratedFDeriv ℝ j (fun w ↦ Real.exp (ℓ w)) z‖ * ‖iteratedFDeriv ℝ (k + 1 - j) ℓ z‖ := by
    rw [← norm_iteratedFDeriv_fderiv, fderiv_exp_comp (hℓ.differentiable (by simp))]
    refine (norm_iteratedFDeriv_smul_le hE hℓ' z (by exact_mod_cast le_top)).trans_eq
      (Finset.sum_congr rfl fun j hj ↦ ?_)
    rw [norm_iteratedFDeriv_fderiv, show k - j + 1 = k + 1 - j by
      have := Finset.mem_range.mp hj; omega]
  have hsum : (fun z ↦ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
      ‖iteratedFDeriv ℝ j (fun w ↦ Real.exp (ℓ w)) z‖ * ‖iteratedFDeriv ℝ (k + 1 - j) ℓ z‖)
      =O[l] g := by
    apply IsBigO.fun_sum
    intro j hj
    have hj := Finset.mem_range.mp hj
    -- The factor `D^j exp ℓ` is bounded and `D^(k+1-j) ℓ` decays.
    have hEj : (fun z ↦ ‖iteratedFDeriv ℝ j (fun w ↦ Real.exp (ℓ w)) z‖) =O[l]
        fun _ ↦ (1 : ℝ) := by
      rcases Nat.eq_zero_or_pos j with rfl | hj₀
      · have h0 : (fun z ↦ ‖iteratedFDeriv ℝ 0 (fun w ↦ Real.exp (ℓ w)) z‖) =
            fun z ↦ ‖Real.exp (ℓ z)‖ := funext fun z ↦ norm_iteratedFDeriv_zero
        rw [h0]
        exact hbdd.norm_left
      · exact (ih j hj hj₀ (by omega)).trans hg
    have hprod := (hEj.mul (hdec (k + 1 - j) (by omega) (by omega))).const_mul_left
      (k.choose j : ℝ)
    simpa only [one_mul, mul_assoc] using hprod
  refine IsBigO.trans (IsBigO.of_bound 1 (Eventually.of_forall fun z ↦ ?_)) hsum
  rw [norm_norm, one_mul, Real.norm_of_nonneg (Finset.sum_nonneg fun j _ ↦ by positivity)]
  exact hle z

/-- **The Leibniz residual of `exp ∘ ℓ`.** The `(k+1)`-st derivative of `exp ∘ ℓ` is
`exp ℓ` times that of `ℓ`, up to terms involving only derivatives of order at most `k`. -/
theorem norm_iteratedFDeriv_exp_comp_sub_smul_le {ℓ : E → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) (k : ℕ)
    (z : E) :
    ‖iteratedFDeriv ℝ (k + 1) (fun w ↦ Real.exp (ℓ w)) z -
        Real.exp (ℓ z) • iteratedFDeriv ℝ (k + 1) ℓ z‖ ≤
      ∑ j ∈ Finset.Ico 1 (k + 1), (k.choose j : ℝ) *
        ‖iteratedFDeriv ℝ j (fun w ↦ Real.exp (ℓ w)) z‖ * ‖iteratedFDeriv ℝ (k + 1 - j) ℓ z‖ := by
  set Ex : E → ℝ := fun w ↦ Real.exp (ℓ w)
  have hE : ContDiff ℝ ∞ Ex := Real.contDiff_exp.comp hℓ
  have hℓ' : ContDiff ℝ ∞ (fderiv ℝ ℓ) := hℓ.fderiv_right (by norm_cast)
  have hEc : ContDiff ℝ ∞ (fun w ↦ Ex w - Ex z) := hE.sub contDiff_const
  -- Subtracting `exp ℓ(z) • Dℓ` turns the top term into the derivative of `(Ex - Ex z) • Dℓ`.
  have hsub : iteratedFDeriv ℝ k (fun w ↦ Ex w • fderiv ℝ ℓ w) z - Ex z • iteratedFDeriv ℝ k
      (fderiv ℝ ℓ) z = iteratedFDeriv ℝ k (fun w ↦ (Ex w - Ex z) • fderiv ℝ ℓ w) z := by
    rw [← iteratedFDeriv_const_smul_apply' (hℓ'.contDiffAt.of_le (by exact_mod_cast le_top)),
      ← iteratedFDeriv_sub_apply (f := fun w ↦ Ex w • fderiv ℝ ℓ w)
        (g := fun w ↦ Ex z • fderiv ℝ ℓ w)
        ((hE.smul hℓ').contDiffAt.of_le (by exact_mod_cast le_top))
        ((hℓ'.const_smul (Ex z)).contDiffAt.of_le (by exact_mod_cast le_top))]
    congr 1
    ext1 w
    simp [sub_smul]
  set Ψ := (continuousMultilinearCurryRightEquiv' ℝ k E ℝ).symm
  have hΨE : iteratedFDeriv ℝ (k + 1) Ex z = Ψ (iteratedFDeriv ℝ k (fderiv ℝ Ex) z) := by
    rw [iteratedFDeriv_succ_eq_comp_right]; rfl
  have hΨℓ : iteratedFDeriv ℝ (k + 1) ℓ z = Ψ (iteratedFDeriv ℝ k (fderiv ℝ ℓ) z) := by
    rw [iteratedFDeriv_succ_eq_comp_right]; rfl
  rw [hΨE, hΨℓ, ← Ψ.map_smul, ← Ψ.map_sub, Ψ.norm_map,
    fderiv_exp_comp (hℓ.differentiable (by simp)), hsub]
  refine (norm_iteratedFDeriv_smul_le hEc hℓ' z (by exact_mod_cast le_top)).trans_eq ?_
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), norm_iteratedFDeriv_zero,
    sub_self, norm_zero, mul_zero, zero_mul, zero_add]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj := Finset.mem_Ico.mp hj
  rw [norm_iteratedFDeriv_fderiv, show k - j + 1 = k + 1 - j by omega,
    show (fun w ↦ Ex w - Ex z) = Ex - fun _ ↦ Ex z from rfl,
    iteratedFDeriv_sub_apply (hE.contDiffAt.of_le (by exact_mod_cast le_top)) contDiffAt_const,
    iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, sub_zero]

/-- The derivative of the Leibniz residual `D^n (exp ∘ ℓ) - exp ℓ • D^n ℓ` is the residual of order
`n + 1`, up to the term `D (exp ∘ ℓ) ⊗ D^n ℓ`. -/
theorem norm_fderiv_iteratedFDeriv_exp_comp_sub_smul_le {ℓ : E → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) (n : ℕ)
    (z : E) :
    ‖fderiv ℝ (fun w ↦ iteratedFDeriv ℝ n (fun v ↦ Real.exp (ℓ v)) w -
        Real.exp (ℓ w) • iteratedFDeriv ℝ n ℓ w) z‖ ≤
      ‖iteratedFDeriv ℝ (n + 1) (fun v ↦ Real.exp (ℓ v)) z -
          Real.exp (ℓ z) • iteratedFDeriv ℝ (n + 1) ℓ z‖ +
        ‖fderiv ℝ (fun v ↦ Real.exp (ℓ v)) z‖ * ‖iteratedFDeriv ℝ n ℓ z‖ := by
  set Ex : E → ℝ := fun w ↦ Real.exp (ℓ w)
  have hE : ContDiff ℝ ∞ Ex := Real.contDiff_exp.comp hℓ
  have hGd : DifferentiableAt ℝ (iteratedFDeriv ℝ n Ex) z :=
    (hE.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)) z
  have hFd : DifferentiableAt ℝ (iteratedFDeriv ℝ n ℓ) z :=
    (hℓ.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)) z
  set Φ := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ E) ℝ
  have hΦE : fderiv ℝ (iteratedFDeriv ℝ n Ex) z = Φ (iteratedFDeriv ℝ (n + 1) Ex z) := by
    rw [fderiv_iteratedFDeriv]; rfl
  have hΦℓ : fderiv ℝ (iteratedFDeriv ℝ n ℓ) z = Φ (iteratedFDeriv ℝ (n + 1) ℓ z) := by
    rw [fderiv_iteratedFDeriv]; rfl
  have hEd : DifferentiableAt ℝ Ex z := hE.differentiable (by simp) z
  rw [fderiv_fun_sub (f := iteratedFDeriv ℝ n Ex) (g := fun w ↦ Ex w • iteratedFDeriv ℝ n ℓ w) hGd
    (DifferentiableAt.smul hEd hFd), fderiv_fun_smul hEd hFd, hΦE, hΦℓ, ← sub_sub, ← Φ.map_smul,
    ← Φ.map_sub]
  refine (norm_sub_le (E := E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ E) ℝ) _ _).trans
    (le_of_eq ?_)
  rw [Φ.norm_map, ContinuousLinearMap.norm_smulRight_apply]

/-- **Decay of the derivative of the Leibniz residual.** Let `g` be a weight bounded along a
filter `l`. If `exp ∘ ℓ` is bounded along `l` and the derivatives of `ℓ` of orders `1, …, n`,
`n ≥ 1`, are `O(g)` along `l`, then the derivative of the Leibniz residual
`D^n (exp ∘ ℓ) - exp ℓ • D^n ℓ` is `O(g)` along `l`. -/
theorem isBigO_norm_fderiv_iteratedFDeriv_exp_comp_sub_smul {ℓ : E → ℝ} (hℓ : ContDiff ℝ ∞ ℓ)
    {l : Filter E} {g : E → ℝ} (hg : g =O[l] fun _ ↦ (1 : ℝ))
    (hbdd : (fun z ↦ Real.exp (ℓ z)) =O[l] fun _ ↦ (1 : ℝ)) {n : ℕ} (hn : 1 ≤ n)
    (hdec : ∀ j, 1 ≤ j → j ≤ n → (fun z ↦ ‖iteratedFDeriv ℝ j ℓ z‖) =O[l] g) :
    (fun z ↦ ‖fderiv ℝ (fun w ↦ iteratedFDeriv ℝ n (fun v ↦ Real.exp (ℓ v)) w -
        Real.exp (ℓ w) • iteratedFDeriv ℝ n ℓ w) z‖) =O[l] g := by
  have hEdec := fun i (hi₁ : 1 ≤ i) (hin : i ≤ n) ↦
    isBigO_norm_iteratedFDeriv_exp_comp hℓ hg hbdd hdec hi₁ hin
  have hres : (fun z ↦ ∑ j ∈ Finset.Ico 1 (n + 1), (n.choose j : ℝ) *
      ‖iteratedFDeriv ℝ j (fun v ↦ Real.exp (ℓ v)) z‖ * ‖iteratedFDeriv ℝ (n + 1 - j) ℓ z‖)
      =O[l] g := by
    apply IsBigO.fun_sum
    intro j hj
    have hj := Finset.mem_Ico.mp hj
    simpa only [one_mul, mul_assoc] using
      (((hEdec j hj.1 (by omega)).trans hg).mul
        (hdec (n + 1 - j) (by omega) (by omega))).const_mul_left (n.choose j : ℝ)
  have hE1 : (fun z ↦ ‖fderiv ℝ (fun v ↦ Real.exp (ℓ v)) z‖ * ‖iteratedFDeriv ℝ n ℓ z‖)
      =O[l] g := by
    have h1 := (hEdec 1 le_rfl hn).trans hg
    simp only [norm_iteratedFDeriv_one] at h1
    simpa only [one_mul] using h1.mul (hdec n hn le_rfl)
  refine IsBigO.trans (IsBigO.of_bound 1 (Eventually.of_forall fun z ↦ ?_)) (hres.add hE1)
  have h := (norm_fderiv_iteratedFDeriv_exp_comp_sub_smul_le hℓ n z).trans
    (add_le_add (norm_iteratedFDeriv_exp_comp_sub_smul_le hℓ n z) le_rfl)
  have h0 := ContinuousLinearMap.opNorm_nonneg (fderiv ℝ (fun w ↦ iteratedFDeriv ℝ n
    (fun v ↦ Real.exp (ℓ v)) w - Real.exp (ℓ w) • iteratedFDeriv ℝ n ℓ w) z)
  rw [Real.norm_eq_abs, abs_of_nonneg h0, one_mul, Real.norm_eq_abs, abs_of_nonneg (h0.trans h)]
  exact h

/-- **Derivatives of `exp ∘ ℓ - 1`.** Let `g` be a weight bounded along a filter `l`. If `ℓ → 0`
along `l` and the derivatives of `ℓ` of orders `0, …, n` are `O(g)` along `l`, then so is the
`n`-th derivative of `exp ∘ ℓ - 1`. -/
theorem isBigO_norm_iteratedFDeriv_exp_comp_sub_one {ℓ : E → ℝ} (hℓ : ContDiff ℝ ∞ ℓ)
    {l : Filter E} {g : E → ℝ} (hg : g =O[l] fun _ ↦ (1 : ℝ)) (hlim : Tendsto ℓ l (𝓝 0)) {n : ℕ}
    (hdec : ∀ j ≤ n, (fun z ↦ ‖iteratedFDeriv ℝ j ℓ z‖) =O[l] g) :
    (fun z ↦ ‖iteratedFDeriv ℝ n (fun w ↦ Real.exp (ℓ w) - 1) z‖) =O[l] g := by
  have hE : ContDiff ℝ ∞ (fun w ↦ Real.exp (ℓ w)) := Real.contDiff_exp.comp hℓ
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `|exp ℓ - 1| ≤ 2 |ℓ|` once `|ℓ| ≤ 1`.
    refine IsBigO.trans ?_ (hdec 0 le_rfl)
    refine IsBigO.of_bound 2 ((hlim.eventually (closedBall_mem_nhds 0 one_pos)).mono
      fun z hz ↦ ?_)
    have hz1 : |ℓ z| ≤ 1 := by simpa [dist_zero_right] using hz
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_abs]
    exact Real.abs_exp_sub_one_le hz1
  -- For `n ≥ 1`, the constant drops out.
  have hbdd : (fun z ↦ Real.exp (ℓ z)) =O[l] fun _ ↦ (1 : ℝ) := by
    have h := (Real.continuous_exp.tendsto 0).comp hlim
    rw [Real.exp_zero] at h
    exact h.isBigO_one ℝ
  have h := isBigO_norm_iteratedFDeriv_exp_comp hℓ hg hbdd (N := n)
    (fun j _ hj ↦ hdec j hj) hn le_rfl
  refine IsBigO.trans (IsBigO.of_bound 1 (Eventually.of_forall fun z ↦ ?_)) h
  rw [show (fun w ↦ Real.exp (ℓ w) - 1) = (fun w ↦ Real.exp (ℓ w)) - fun _ ↦ (1 : ℝ) from rfl,
    iteratedFDeriv_sub_apply (hE.contDiffAt.of_le (by exact_mod_cast le_top)) contDiffAt_const,
    iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, sub_zero, one_mul]

/-- **A mean value bound for exponentially decaying derivatives.** If the derivative of `φ` is
bounded by `K exp (-c ‖w‖)` outside the ball of radius `R`, where `c, K ≥ 0`, then for `‖z‖ ≥ R + 1`
and `‖k‖ ≤ 1`, `‖φ z - φ (z + k)‖ ≤ K exp c exp (-c ‖z‖) ‖k‖`. -/
theorem norm_sub_comp_add_le_of_norm_fderiv_le {B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] {φ : E → B} (hφ : Differentiable ℝ φ) {c K R : ℝ} (hc : 0 ≤ c)
    (hK : 0 ≤ K) (hbd : ∀ w : E, R ≤ ‖w‖ → ‖fderiv ℝ φ w‖ ≤ K * Real.exp (-(c * ‖w‖)))
    {z k : E} (hz : R + 1 ≤ ‖z‖) (hk : ‖k‖ ≤ 1) :
    ‖φ z - φ (z + k)‖ ≤ K * Real.exp c * Real.exp (-(c * ‖z‖)) * ‖k‖ := by
  have hball : ∀ w ∈ closedBall z 1,
      ‖fderiv ℝ φ w‖ ≤ K * Real.exp c * Real.exp (-(c * ‖z‖)) := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    have hw' : ‖z‖ - 1 ≤ ‖w‖ := by
      have := norm_sub_norm_le z w
      rw [norm_sub_rev] at this
      linarith
    refine (hbd w (by linarith)).trans ?_
    rw [mul_assoc, ← Real.exp_add]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) hK
  have h := (convex_closedBall z 1).norm_image_sub_le_of_norm_fderiv_le (fun w _ ↦ hφ w) hball
    (mem_closedBall_self zero_le_one)
    (show z + k ∈ closedBall z 1 by rwa [mem_closedBall, dist_eq_norm, add_sub_cancel_left])
  rwa [add_sub_cancel_left, norm_sub_rev] at h

omit [NormedSpace ℝ E] in
/-- An `O(exp (-c ‖z‖))` bound at infinity on a proper space holds outside an explicit ball, with a
nonnegative constant. -/
theorem exists_nonneg_forall_norm_le_mul_exp_of_isBigO [ProperSpace E] {f : E → ℝ} {c : ℝ}
    (h : f =O[cocompact E] fun z ↦ Real.exp (-(c * ‖z‖))) :
    ∃ K R, 0 ≤ K ∧ ∀ z : E, R ≤ ‖z‖ → ‖f z‖ ≤ K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨K, hK⟩ := h.bound
  obtain ⟨R, -, hR⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := E) ▸ hK)
  refine ⟨max K 0, R, le_max_right _ _, fun z hz ↦ (hR hz).trans ?_⟩
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

end TauCeti
