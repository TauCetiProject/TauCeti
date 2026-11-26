/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.CompLinear
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Basic.Real.Sign
public import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompactSupport
import TauCeti.Basic.Real.Sign
import TauCeti.Analysis.Holder.Examples
import TauCeti.Analysis.Holder.Jet.Bounds
import TauCeti.Analysis.Holder.Localization
import TauCeti.Analysis.SpecialFunctions.Pow.Regularity
import TauCeti.Analysis.SpecialFunctions.Pow.Holder
import TauCeti.Topology.MetricSpace.Holder

/-!
# The power `|x|^(k + β)` in the bounded Hölder spaces

For `k : ℕ` and `0 < β ≤ 1`, the function `|x|^(k + β)` on `ℝ` is `C^k`, and its `k`-th derivative
is `c · sgn(x)^k |x|^β` with `c = (k + β)(k + β - 1) ⋯ (β + 1)`. This file shows that it sits
exactly in the bounded Hölder space `C_b^{k,β}` near the origin and in no smaller one:

* **Membership** (`TauCeti.exists_ckHolderSpace_eqOn_abs_rpow`). Cut off away from the origin,
  `|x|^(k + β)` is an element of `C_b^{k,β}(ℝ)` with compact support, equal to `|x|^(k + β)` on
  `(-1, 1)`.
* **Sharpness** (`TauCeti.not_exists_ckHolderSpace_eqOn_abs_rpow`). For `α > β` no element of
  `C_b^{k,α}(ℝ)` agrees with `|x|^(k + β)` on `(-1, 1)`: the `k`-th derivative would be
  `α`-Hölder near `0`, while `|x|^β` is not.

Both transfer along a nonzero continuous linear functional `ℓ` on a normed space `E`, by
precomposition (`TauCeti.CkHolderSpace.compLinearL`): `|ℓ x|^(k + β)` agrees near the hyperplane
`ℓ = 0` with an element of `C_b^{k,β}(E)` (`TauCeti.exists_ckHolderSpace_eq_abs_rpow_comp`) and
with no element of `C_b^{k,α}(E)` for `α > β` (`TauCeti.not_exists_ckHolderSpace_eq_abs_rpow_comp`).
These are the data that show the data spaces of the parabolic Cauchy problem to be sharp.

The `k`-th derivative is computed by `TauCeti.iteratedDeriv_abs_rpow`, through the signed powers
`|x|^r sgn(x)^j` of `TauCeti.Analysis.SpecialFunctions.Pow.Regularity`. For `β ≤ 1` the signed
power `|x|^β sgn(x)^j` is `β`-Hölder with constant `2` (`TauCeti.holderWith_abs_rpow_mul_sign_pow`),
and for `α > β` it is not `α`-Hölder on `(-1, 1)`
(`TauCeti.not_holderOnWith_abs_rpow_mul_sign_pow_Ioo`), since its absolute value is the cusp
`|x|^β` of `TauCeti.not_holderOnWith_abs_rpow_Ioo`.
-/

public section

open Filter Metric Set
open scoped NNReal Topology

namespace TauCeti

/-! ### Signed powers -/

/-- The absolute value of the signed power `|x|^r sgn(x)^j` is `|x|^r`, for `r > 0`. -/
private theorem abs_abs_rpow_mul_sign_pow {r : ℝ} (hr : 0 < r) (j : ℕ) (x : ℝ) :
    |(|x| ^ r * Real.sign x ^ j)| = |x| ^ r := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [Real.zero_rpow hr.ne']
  · rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) r), abs_pow,
      Real.abs_sign_of_ne_zero hx, one_pow, mul_one]

/-- For `β ≤ 1`, the signed power `|x|^β sgn(x)^j` is `β`-Hölder with constant `2`. -/
theorem holderWith_abs_rpow_mul_sign_pow {β : ℝ≥0} (hβ1 : β ≤ 1) (j : ℕ) :
    HolderWith 2 β (fun x : ℝ ↦ |x| ^ (β : ℝ) * Real.sign x ^ j) := by
  refine holderOnWith_univ.mp (HolderOnWith.of_dist_le fun x _ y _ ↦ ?_)
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_ofNat]
  have hxy : 0 ≤ |x - y| ^ (β : ℝ) := Real.rpow_nonneg (abs_nonneg _) _
  by_cases hs : Real.sign x ^ j = Real.sign y ^ j
  · -- Equal signs: the Hölder bound of `t ↦ t^β` on `[0, ∞)`.
    rw [hs, ← sub_mul, abs_mul]
    calc |(|x| ^ (β : ℝ) - |y| ^ (β : ℝ))| * |Real.sign y ^ j|
        ≤ |(|x| ^ (β : ℝ) - |y| ^ (β : ℝ))| :=
          mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sign_pow_le_one y j)
      _ ≤ |(|x| - |y|)| ^ (β : ℝ) :=
          Real.abs_rpow_sub_rpow_le (abs_nonneg x) (abs_nonneg y) β.coe_nonneg hβ1
      _ ≤ |x - y| ^ (β : ℝ) :=
          Real.rpow_le_rpow (abs_nonneg _) (abs_abs_sub_abs_le_abs_sub x y) β.coe_nonneg
      _ ≤ 2 * |x - y| ^ (β : ℝ) := by linarith
  · -- Different signs: `x` and `y` lie on opposite sides of `0`, so both are at most `|x - y|`.
    have hmul : x * y ≤ 0 := by
      by_contra h
      rcases pos_and_pos_or_neg_and_neg_of_mul_pos (not_le.1 h) with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · exact hs (by rw [Real.sign_of_pos hx, Real.sign_of_pos hy])
      · exact hs (by rw [Real.sign_of_neg hx, Real.sign_of_neg hy])
    have hx : |x| ≤ |x - y| := sq_le_sq.mp (by nlinarith)
    have hy : |y| ≤ |x - y| := sq_le_sq.mp (by nlinarith)
    calc |(|x| ^ (β : ℝ) * Real.sign x ^ j - |y| ^ (β : ℝ) * Real.sign y ^ j)|
        ≤ |(|x| ^ (β : ℝ) * Real.sign x ^ j)| + |(|y| ^ (β : ℝ) * Real.sign y ^ j)| :=
          abs_sub _ _
      _ ≤ |x| ^ (β : ℝ) + |y| ^ (β : ℝ) :=
          add_le_add (abs_abs_rpow_mul_sign_pow_le j x) (abs_abs_rpow_mul_sign_pow_le j y)
      _ ≤ |x - y| ^ (β : ℝ) + |x - y| ^ (β : ℝ) :=
          add_le_add (Real.rpow_le_rpow (abs_nonneg _) hx β.coe_nonneg)
            (Real.rpow_le_rpow (abs_nonneg _) hy β.coe_nonneg)
      _ = 2 * |x - y| ^ (β : ℝ) := by ring

/-- For `0 < β < α`, the signed power `|x|^β sgn(x)^j` is not `α`-Hölder on `(-1, 1)`: its
absolute value is the cusp `|x|^β`. -/
theorem not_holderOnWith_abs_rpow_mul_sign_pow_Ioo {α β C : ℝ≥0} (hβ0 : 0 < β) (hβα : β < α)
    (j : ℕ) :
    ¬ HolderOnWith C α (fun x : ℝ ↦ |x| ^ (β : ℝ) * Real.sign x ^ j) (Ioo (-1) 1) := by
  intro h
  refine not_holderOnWith_abs_rpow_Ioo (C := C) hβ0 hβα (HolderOnWith.of_dist_le fun x hx y hy ↦ ?_)
  have hβ0' : (0 : ℝ) < β := hβ0
  have hd := h.dist_le hx hy
  rw [Real.dist_eq] at hd ⊢
  rw [← abs_abs_rpow_mul_sign_pow hβ0' j x, ← abs_abs_rpow_mul_sign_pow hβ0' j y]
  exact (abs_abs_sub_abs_le_abs_sub _ _).trans hd

/-- For `0 < β ≤ 1`, the `k`-th derivative of `|x|^(k + β)` is `β`-Hölder on `ℝ`. -/
private theorem holderWith_iteratedFDeriv_abs_rpow (k : ℕ) {β : ℝ≥0} (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) :
    HolderWith (2 * ‖(descPochhammer ℝ k).eval ((k : ℝ) + β)‖₊) β
      (iteratedFDeriv ℝ k fun x : ℝ ↦ |x| ^ ((k : ℝ) + β)) := by
  have hkp : (k : ℝ) < k + β := lt_add_of_pos_right _ hβ0
  rw [iteratedFDeriv_eq_equiv_comp, iteratedDeriv_abs_rpow hkp, add_sub_cancel_left]
  exact (LinearIsometryEquiv.isometry _).comp_holderWith
    ((holderWith_abs_rpow_mul_sign_pow hβ1 k).smul ((descPochhammer ℝ k).eval ((k : ℝ) + β)))

/-! ### `|x|^(k + β)` in `C_b^{k,β}` and not in `C_b^{k,α}` -/

/-- **`|x|^(k + β)` is `C^{k,β}` near the origin.** For `0 < β ≤ 1`, some compactly supported
element of `C_b^{k,β}(ℝ)` equals `|x|^(k + β)` on `(-1, 1)`: the power multiplied by a smooth
cutoff. -/
theorem exists_ckHolderSpace_eqOn_abs_rpow (k : ℕ) {β : ℝ≥0} (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    ∃ f : CkHolderSpace k β ℝ ℝ, HasCompactSupport f ∧
      ∀ x ∈ Ioo (-1 : ℝ) 1, f x = |x| ^ ((k : ℝ) + β) := by
  have hkp : (k : ℝ) < k + β := lt_add_of_pos_right _ hβ0
  let χ : ContDiffBump (0 : ℝ) := ⟨1, 3 / 2, one_pos, by norm_num⟩
  have hχs : tsupport χ ⊆ ball (0 : ℝ) 2 := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_ball (by norm_num [χ])
  obtain ⟨N, -, hN⟩ := χ.hasCompactSupport.exists_bound_iteratedFDeriv χ.contDiff (k + 1)
  obtain ⟨M, -, hM⟩ :=
    (isCompact_closedBall (0 : ℝ) 2).exists_bound_iteratedFDeriv (contDiff_abs_rpow hkp)
  have hfH := (holderWith_iteratedFDeriv_abs_rpow k hβ0 hβ1).holderOnWith (ball (0 : ℝ) 2)
  let f := CkHolderSpace.cutoff (M := M.toNNReal) (N := N.toNNReal)
    (contDiff_abs_rpow hkp).contDiffOn ((χ.contDiff (n := ⊤)).of_le (mod_cast le_top)) isOpen_ball
    (convex_ball 0 2) hχs hβ1
    (fun i hi x hx ↦ (hM i hi x (ball_subset_closedBall hx)).trans (Real.le_coe_toNNReal M))
    (fun i hi x ↦ (hN i hi x).trans (Real.le_coe_toNNReal N)) hfH
  refine ⟨f, χ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _)
    (CkHolderSpace.tsupport_cutoff_subset ..), fun x hx ↦ ?_⟩
  have hx1 : x ∈ closedBall (0 : ℝ) χ.rIn := by
    rw [mem_closedBall, Real.dist_0_eq_abs]
    exact (abs_lt.2 hx).le
  dsimp only [f]
  rw [CkHolderSpace.cutoff_apply, χ.one_of_mem_closedBall hx1, one_smul]

/-- **`|x|^(k + β)` is not `C^{k,α}` near the origin for `α > β`.** No element of `C_b^{k,α}(ℝ)`
equals `|x|^(k + β)` on `(-1, 1)`: its `k`-th derivative would be `α`-Hölder there, while the
`k`-th derivative of `|x|^(k + β)` is a nonzero multiple of `sgn(x)^k |x|^β`. -/
theorem not_exists_ckHolderSpace_eqOn_abs_rpow (k : ℕ) {α β : ℝ≥0} (hβ0 : 0 < β)
    (hβα : β < α) :
    ¬ ∃ f : CkHolderSpace k α ℝ ℝ, ∀ x ∈ Ioo (-1 : ℝ) 1, f x = |x| ^ ((k : ℝ) + β) := by
  rintro ⟨f, hf⟩
  obtain ⟨C, hC⟩ := f.memHolder_iteratedFDeriv
  have hkp : (k : ℝ) < k + β := lt_add_of_pos_right _ hβ0
  set c := (descPochhammer ℝ k).eval ((k : ℝ) + β)
  have hc : 0 < c := descPochhammer_pos (by linarith)
  -- On `(-1, 1)` the `k`-th derivative of `f` is that of `|x|^(k + β)`.
  have heq : ∀ x ∈ Ioo (-1 : ℝ) 1, iteratedFDeriv ℝ k f x =
      iteratedFDeriv ℝ k (fun x : ℝ ↦ |x| ^ ((k : ℝ) + β)) x := fun x hx ↦
    (Filter.EventuallyEq.iteratedFDeriv ℝ
      (eventually_of_mem (isOpen_Ioo.mem_nhds hx) hf) k).self_of_nhds
  refine not_holderOnWith_abs_rpow_mul_sign_pow_Ioo (C := C * ‖c⁻¹‖₊) hβ0 hβα k
    (HolderOnWith.of_dist_le fun x hx y hy ↦ ?_)
  have h := hC.dist_le x y
  rw [heq x hx, heq y hy, iteratedFDeriv_eq_equiv_comp, Function.comp_apply, Function.comp_apply,
    LinearIsometryEquiv.dist_map, iteratedDeriv_abs_rpow hkp, add_sub_cancel_left,
    Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hc] at h
  rw [Real.dist_eq, NNReal.coe_mul, coe_nnNorm, Real.norm_eq_abs, abs_inv, abs_of_pos hc]
  calc |(|x| ^ (β : ℝ) * Real.sign x ^ k - |y| ^ (β : ℝ) * Real.sign y ^ k)|
      = c⁻¹ * (c * |(|x| ^ (β : ℝ) * Real.sign x ^ k - |y| ^ (β : ℝ) * Real.sign y ^ k)|) := by
        field_simp
    _ ≤ c⁻¹ * (C * dist x y ^ (α : ℝ)) := by gcongr
    _ = C * c⁻¹ * dist x y ^ (α : ℝ) := by ring

/-! ### Along a linear functional -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For `0 < β ≤ 1` and a continuous linear functional `ℓ`, some element of `C_b^{k,β}(E)` equals
`|ℓ x|^(k + β)` wherever `|ℓ x| < 1`. -/
theorem exists_ckHolderSpace_eq_abs_rpow_comp (k : ℕ) {β : ℝ≥0} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (ℓ : E →L[ℝ] ℝ) :
    ∃ f : CkHolderSpace k β E ℝ, ∀ x, |ℓ x| < 1 → f x = |ℓ x| ^ ((k : ℝ) + β) := by
  obtain ⟨g, -, hg⟩ := exists_ckHolderSpace_eqOn_abs_rpow k hβ0 hβ1
  exact ⟨CkHolderSpace.compLinearL ℓ g, fun x hx ↦ by
    rw [CkHolderSpace.compLinearL_apply]
    exact hg _ (abs_lt.1 hx)⟩

/-- For `0 < β ≤ 1` and `α ≤ 1`, some element of `C_b^{k,α}(E)` equals `|ℓ x|^(k + 1 + β)` wherever
`|ℓ x| < 1`, whatever the order of `α` and `β`: the element of `C_b^{k+1,β}(E)` of
`TauCeti.exists_ckHolderSpace_eq_abs_rpow_comp` has bounded `k`-th derivative with bounded
derivative, which is therefore `α`-Hölder. -/
theorem exists_ckHolderSpace_eq_abs_rpow_comp_succ (k : ℕ) {α β : ℝ≥0} (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) (hα1 : α ≤ 1) (ℓ : E →L[ℝ] ℝ) :
    ∃ f : CkHolderSpace k α E ℝ, ∀ x, |ℓ x| < 1 → f x = |ℓ x| ^ (((k + 1 : ℕ) : ℝ) + β) := by
  obtain ⟨g, hg⟩ := exists_ckHolderSpace_eq_abs_rpow_comp (k + 1) hβ0 hβ1 ℓ
  refine ⟨CkHolderSpace.ofContDiff g (g.contDiff.of_le (by exact_mod_cast k.le_succ))
    (fun i hi ↦ ⟨‖g‖, g.norm_iteratedFDeriv_apply_le (by omega)⟩) ?_, fun x hx ↦ by
      rw [CkHolderSpace.coe_ofContDiff]
      exact hg x hx⟩
  exact ⟨_, holderOnWith_univ.mp (g.contDiff.contDiffOn.holderOnWith_iteratedFDeriv_of_lt
    isOpen_univ convex_univ (M := ‖g‖₊) (L := ‖g‖₊) (Nat.lt_succ_self k) hα1
    (fun x _ ↦ g.norm_iteratedFDeriv_apply_le k.le_succ x)
    (fun x _ ↦ g.norm_iteratedFDeriv_apply_le le_rfl x))⟩

/-- For `0 < β < α` and a nonzero continuous linear functional `ℓ`, no element of `C_b^{k,α}(E)`
equals `|ℓ x|^(k + β)` wherever `|ℓ x| < 1`: restricted to a line on which `ℓ` is a coordinate, it
would give an element of `C_b^{k,α}(ℝ)` equal to `|t|^(k + β)` on `(-1, 1)`. -/
theorem not_exists_ckHolderSpace_eq_abs_rpow_comp (k : ℕ) {α β : ℝ≥0} (hβ0 : 0 < β)
    (hβα : β < α) {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) :
    ¬ ∃ f : CkHolderSpace k α E ℝ, ∀ x, |ℓ x| < 1 → f x = |ℓ x| ^ ((k : ℝ) + β) := by
  rintro ⟨f, hf⟩
  obtain ⟨v, hv⟩ : ∃ v, ℓ v ≠ 0 := by
    simpa using DFunLike.ne_iff.1 hℓ
  let e : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight ((ℓ v)⁻¹ • v)
  have he : ∀ t, ℓ (e t) = t := fun t ↦ by
    simp [e, map_smul, inv_mul_cancel₀ hv]
  refine not_exists_ckHolderSpace_eqOn_abs_rpow k hβ0 hβα
    ⟨CkHolderSpace.compLinearL e f, fun t ht ↦ ?_⟩
  rw [CkHolderSpace.compLinearL_apply, hf _ (by rw [he]; exact abs_lt.2 ht), he]

end TauCeti
