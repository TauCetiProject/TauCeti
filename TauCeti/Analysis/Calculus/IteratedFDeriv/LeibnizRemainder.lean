/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Remainders of the Leibniz and chain rules for iterated derivatives

The `n`-th derivative of a product `V • g` is `V` times the `n`-th derivative of `g`, plus terms in
which `V` is differentiated at least once. This file bounds that remainder,
`‖Dⁿ (V • g) p - V p • Dⁿ g p‖ ≤ 2ⁿ B M`, when the derivatives of `V` of orders `1` to `n` are
bounded by `B` and those of `g` of order less than `n` by `M` at `p`
(`TauCeti.norm_iteratedFDeriv_smul_sub_smul_le`).

Applied to the chain rule `D (G ∘ u) = (G' ∘ u) • Du`, it shows that the top-order term of
`Dⁿ⁺¹ (G ∘ u)` is `G'(u) Dⁿ⁺¹u`, up to terms involving only derivatives of `u` of order at most
`n` (`TauCeti.norm_iteratedFDeriv_succ_comp_sub_smul_le`). Finally, for fixed directions `m`, the
derivative of `y ↦ Dⁿ f y m - V y • Dⁿ w y m` is controlled by `Dⁿ⁺¹ f - V • Dⁿ⁺¹ w` and the
gradient of `V` (`TauCeti.norm_fderiv_iteratedFDeriv_apply_sub_smul_le`).

These are the estimates behind the differentiated form of a semilinear equation `Δu = G(u)`: each
derivative `w = Dⁿu (·) m` solves `Δ w = G'(u) w + f`, where the gradient of `f` only involves
derivatives of `u` of order at most `n`.
-/

public section

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **The Leibniz estimate for `Dⁿ (V • g) - V Dⁿ g`.** The `n`-th derivative of `V • g` differs
from `V` times the `n`-th derivative of `g` by terms in which `V` is differentiated at least once:
if `‖DⁱV p‖ ≤ B` for `1 ≤ i ≤ n` and `‖Dʲg p‖ ≤ M` for `j < n`, the difference is at most
`2ⁿ B M`. -/
theorem norm_iteratedFDeriv_smul_sub_smul_le {V : E → 𝕜} {g : E → F} {n : ℕ}
    (hV : ContDiff 𝕜 n V) (hg : ContDiff 𝕜 n g) (p : E) {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hVb : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv 𝕜 i V p‖ ≤ B)
    (hgb : ∀ j, j < n → ‖iteratedFDeriv 𝕜 j g p‖ ≤ M) :
    ‖iteratedFDeriv 𝕜 n (fun y ↦ V y • g y) p - V p • iteratedFDeriv 𝕜 n g p‖ ≤ 2 ^ n * B * M := by
  have hsub : (fun y ↦ (V y - V p) • g y) = (fun y ↦ V y • g y) - fun y ↦ V p • g y := by
    funext y
    simp [sub_smul]
  have h₁ : iteratedFDeriv 𝕜 n (fun y ↦ V y • g y) p - V p • iteratedFDeriv 𝕜 n g p =
      iteratedFDeriv 𝕜 n (fun y ↦ (V y - V p) • g y) p := by
    have hA : ContDiffAt 𝕜 n (fun y ↦ V y • g y) p := (hV.smul hg).contDiffAt
    have hA' : ContDiffAt 𝕜 n (fun y ↦ V p • g y) p := contDiffAt_const.smul hg.contDiffAt
    rw [hsub, iteratedFDeriv_sub_apply hA hA', iteratedFDeriv_const_smul_apply' hg.contDiffAt]
  rw [h₁]
  refine (norm_iteratedFDeriv_smul_le (hV.sub contDiff_const) hg p le_rfl).trans ?_
  calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv 𝕜 i (fun y ↦ V y - V p) p‖ * ‖iteratedFDeriv 𝕜 (n - i) g p‖
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (B * M) := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        rcases Nat.eq_zero_or_pos i with rfl | hi₀
        · simp only [norm_iteratedFDeriv_zero, sub_self, norm_zero, zero_mul]
          positivity
        · have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hVi : iteratedFDeriv 𝕜 i (fun y ↦ V y - V p) p = iteratedFDeriv 𝕜 i V p := by
            have hfun : (fun y ↦ V y - V p) = V - fun _ ↦ V p := rfl
            rw [hfun, iteratedFDeriv_sub_apply (hV.of_le (by exact_mod_cast hin)).contDiffAt
              contDiffAt_const, iteratedFDeriv_const_of_ne hi₀.ne', Pi.zero_apply, sub_zero]
          rw [hVi]
          exact mul_le_mul (hVb i hi₀ hin) (hgb (n - i) (by omega)) (norm_nonneg _) hB
    _ = 2 ^ n * B * M := by
      rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      push_cast
      ring

/-- **The top-order term of `Dⁿ⁺¹ (G ∘ u)`.** For `G` and `u` of class `Cⁿ⁺¹`, the `(n + 1)`-st
derivative of `G ∘ u` differs from `G'(u) Dⁿ⁺¹u` by terms involving only derivatives of `u` of
order at most `n`: if the derivatives of order `1` to `n` of `G' ∘ u` are bounded by `B` at `p`,
and those of `u` by `M`, the difference is at most `2ⁿ B M`. -/
theorem norm_iteratedFDeriv_succ_comp_sub_smul_le {u : E → 𝕜} {G : 𝕜 → 𝕜} {n : ℕ}
    (hG : ContDiff 𝕜 (n + 1) G) (hu : ContDiff 𝕜 (n + 1) u) (p : E) {B M : ℝ} (hB : 0 ≤ B)
    (hM : 0 ≤ M) (hVb : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv 𝕜 i (deriv G ∘ u) p‖ ≤ B)
    (hub : ∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv 𝕜 j u p‖ ≤ M) :
    ‖iteratedFDeriv 𝕜 (n + 1) (G ∘ u) p - deriv G (u p) • iteratedFDeriv 𝕜 (n + 1) u p‖ ≤
      2 ^ n * B * M := by
  have hG' : ContDiff 𝕜 n (deriv G) := (contDiff_succ_iff_deriv.mp hG).2.2
  -- The chain rule: `D (G ∘ u) = (G' ∘ u) • Du`.
  have hfd : (fun y ↦ fderiv 𝕜 (G ∘ u) y) = fun y ↦ (deriv G ∘ u) y • fderiv 𝕜 u y :=
    funext fun y ↦ (((hG.differentiable (by simp)) (u y)).hasDerivAt.comp_hasFDerivAt y
      ((hu.differentiable (by simp)) y).hasFDerivAt).fderiv
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right (f := u),
    Function.comp_apply, Function.comp_apply, hfd]
  set Φ := (continuousMultilinearCurryRightEquiv' 𝕜 n E 𝕜).symm
  have hΦ : ∀ a b : E [×n]→L[𝕜] E →L[𝕜] 𝕜, Φ a - deriv G (u p) • Φ b =
      Φ (a - deriv G (u p) • b) := fun a b ↦ by
    rw [LinearIsometryEquiv.map_sub, LinearIsometryEquiv.map_smul]
  rw [hΦ, LinearIsometryEquiv.norm_map]
  refine norm_iteratedFDeriv_smul_sub_smul_le (hG'.comp (hu.of_le le_self_add))
    (hu.fderiv_right le_rfl) p hB hM hVb fun j hj ↦ ?_
  rw [norm_iteratedFDeriv_fderiv]
  exact hub (j + 1) (by omega) (by omega)

/-- **The derivative of `Dⁿ f (·) m - V • Dⁿ w (·) m`.** If the `n`-th derivatives of `f` and `w`
and the function `V` are differentiable at `p`, then for directions `m` the function
`y ↦ Dⁿ f y m - V y • Dⁿ w y m` has derivative at `p` of norm at most
`(‖Dⁿ⁺¹ f p - V p • Dⁿ⁺¹ w p‖ + ‖DV p‖ ‖Dⁿ w p‖) ∏ ‖mᵢ‖`. -/
theorem norm_fderiv_iteratedFDeriv_apply_sub_smul_le {f w : E → F} {V : E → 𝕜} {n : ℕ} {p : E}
    (hf : DifferentiableAt 𝕜 (iteratedFDeriv 𝕜 n f) p)
    (hw : DifferentiableAt 𝕜 (iteratedFDeriv 𝕜 n w) p) (hV : DifferentiableAt 𝕜 V p)
    (m : Fin n → E) :
    ‖fderiv 𝕜 (fun y ↦ iteratedFDeriv 𝕜 n f y m - V y • iteratedFDeriv 𝕜 n w y m) p‖ ≤
      (‖iteratedFDeriv 𝕜 (n + 1) f p - V p • iteratedFDeriv 𝕜 (n + 1) w p‖ +
        ‖fderiv 𝕜 V p‖ * ‖iteratedFDeriv 𝕜 n w p‖) * ∏ i, ‖m i‖ := by
  -- The derivative of `Dⁿg (·) m` in the direction `v` is `Dⁿ⁺¹g (cons v m)`.
  have happly : ∀ {g : E → F}, DifferentiableAt 𝕜 (iteratedFDeriv 𝕜 n g) p → ∀ v,
      fderiv 𝕜 (fun y ↦ iteratedFDeriv 𝕜 n g y m) p v =
        iteratedFDeriv 𝕜 (n + 1) g p (Fin.cons v m) := fun hg v ↦ by
    rw [hg.iteratedFDeriv_succ_apply_left', Fin.tail_cons, Fin.cons_zero]
  have happ_diff : ∀ {g : E → F}, DifferentiableAt 𝕜 (iteratedFDeriv 𝕜 n g) p →
      DifferentiableAt 𝕜 (fun y ↦ iteratedFDeriv 𝕜 n g y m) p := fun hg ↦
    (ContinuousMultilinearMap.apply 𝕜 (fun _ : Fin n ↦ E) F m).differentiableAt.comp p hg
  have hF := (happ_diff hf).hasFDerivAt.fun_sub (hV.hasFDerivAt.fun_smul (happ_diff hw).hasFDerivAt)
  rw [hF.fderiv]
  set T := iteratedFDeriv 𝕜 (n + 1) f p - V p • iteratedFDeriv 𝕜 (n + 1) w p
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  have happ : (fderiv 𝕜 (fun y ↦ iteratedFDeriv 𝕜 n f y m) p -
      (V p • fderiv 𝕜 (fun y ↦ iteratedFDeriv 𝕜 n w y m) p +
        (fderiv 𝕜 V p).smulRight (iteratedFDeriv 𝕜 n w p m))) v =
      T (Fin.cons v m) - fderiv 𝕜 V p v • iteratedFDeriv 𝕜 n w p m := by
    simp only [T, sub_apply, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
      happly hf, happly hw]
    abel
  rw [happ]
  calc ‖T (Fin.cons v m) - fderiv 𝕜 V p v • iteratedFDeriv 𝕜 n w p m‖
      ≤ ‖T‖ * ‖v‖ * ∏ i, ‖m i‖ +
          ‖fderiv 𝕜 V p‖ * ‖v‖ * (‖iteratedFDeriv 𝕜 n w p‖ * ∏ i, ‖m i‖) := by
        refine (norm_sub_le _ _).trans (add_le_add (T.norm_map_cons_le v m) ?_)
        rw [norm_smul]
        exact mul_le_mul ((fderiv 𝕜 V p).le_opNorm v)
          ((iteratedFDeriv 𝕜 n w p).le_opNorm m) (norm_nonneg _) (by positivity)
    _ = _ := by ring

end TauCeti
