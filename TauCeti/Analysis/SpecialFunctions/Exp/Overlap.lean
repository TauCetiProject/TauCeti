/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Analysis.SpecialFunctions.Exp
import TauCeti.Analysis.SpecialFunctions.Exp.Shift

/-!
# Pointwise overlap of exponentially decaying functions

If `‖f z‖ ≤ K exp (-(c₁ ‖z‖))` and `‖g z‖ ≤ L exp (-(c₂ ‖z‖))`, then `f` decays about `0` and the
translate `g (· + a)` decays about `-a`. Since `‖a‖ ≤ ‖z‖ + ‖z + a‖`, their product is
exponentially small in the separation `‖a‖`. Any part `0 ≤ b ≤ c₂` of the rates can be spent on
the separation, and the rest `c₁ - b` kept as decay in `z`.

## Main results

* `TauCeti.norm_mul_norm_le_mul_exp_mul_exp`: the overlap is at most
  `K L exp (-(b ‖a‖)) exp (-((c₁ - b) ‖z‖))` for every `0 ≤ b ≤ c₂`.
* `TauCeti.norm_mul_norm_le_mul_exp_neg_mul_norm`: for a common rate `c`, the case `b = c`, a
  bound `K L exp (-(c ‖a‖))` uniform in `z`.
* `TauCeti.exists_mul_le_mul_exp_neg_mul_norm_of_forall_lt`: the same for nonnegative functions
  decaying at every rate below a threshold.

The same holds for functions decaying away from finitely many centres instead of one. If `f`
decays at rate `b` in the distance to a finite multiset `S` of points and `g` in the distance to
`T`, the triangle inequality bounds their product by `exp (-(c δ))` for every `0 ≤ c < b`, where
`δ` bounds the distances between points of `S` and points of `T` from below. The remaining rate
`b - c` is kept as decay about the points of `S`.

* `TauCeti.mul_le_mul_exp_mul_sum_exp_of_forall_le_norm_sub`: the product is at most
  `K L exp (-(c δ)) ∑_{a ∈ S} exp (-((b - c) ‖z - a‖))`.
-/

public section

namespace TauCeti

variable {E F G : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [SeminormedAddCommGroup G] {f : E → F} {g : E → G} {K L c : ℝ}

/-- Two values bounded by `K exp (-(b₁ r))` and `L exp (-(b₂ r'))` with `δ ≤ r + r'` have product
at most `K L exp (-(c δ)) exp (-((b₁ - c) r))`, for `0 ≤ c ≤ b₂` and `0 ≤ r'`. -/
private theorem mul_le_mul_exp_mul_exp_of_le_add {u v b₁ b₂ δ r r' : ℝ} (hc : 0 ≤ c)
    (hcb : c ≤ b₂) (hr' : 0 ≤ r') (hv : 0 ≤ v) (hu : u ≤ K * Real.exp (-(b₁ * r)))
    (hvL : v ≤ L * Real.exp (-(b₂ * r'))) (hδ : δ ≤ r + r') (hK : 0 ≤ K) (hL : 0 ≤ L) :
    u * v ≤ K * L * Real.exp (-(c * δ)) * Real.exp (-((b₁ - c) * r)) := by
  have hexp : Real.exp (-(b₁ * r)) * Real.exp (-(b₂ * r')) ≤
      Real.exp (-(c * δ)) * Real.exp (-((b₁ - c) * r)) := by
    rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
    nlinarith [mul_le_mul_of_nonneg_left hδ hc, mul_le_mul_of_nonneg_right hcb hr']
  calc u * v ≤ K * Real.exp (-(b₁ * r)) * (L * Real.exp (-(b₂ * r'))) :=
        mul_le_mul hu hvL hv (by positivity)
    _ = K * L * (Real.exp (-(b₁ * r)) * Real.exp (-(b₂ * r'))) := by ring
    _ ≤ K * L * (Real.exp (-(c * δ)) * Real.exp (-((b₁ - c) * r))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by ring

/-- **Overlap of exponentially decaying functions, splitting the rate.** If
`‖f z‖ ≤ K exp (-(c₁ ‖z‖))` and `‖g z‖ ≤ L exp (-(c₂ ‖z‖))`, then for every `0 ≤ b ≤ c₂` the
product of `f` and of the translate `g (· + a)` is at most
`K L exp (-(b ‖a‖)) exp (-((c₁ - b) ‖z‖))`: part `b` of the rates is spent on the separation
`‖a‖` and the rest is kept as decay in `z`. -/
theorem norm_mul_norm_le_mul_exp_mul_exp {c₁ c₂ b : ℝ} (hb : 0 ≤ b) (hbc : b ≤ c₂)
    (hf : ∀ z, ‖f z‖ ≤ K * Real.exp (-(c₁ * ‖z‖)))
    (hg : ∀ z, ‖g z‖ ≤ L * Real.exp (-(c₂ * ‖z‖))) (z a : E) :
    ‖f z‖ * ‖g (z + a)‖ ≤ K * L * Real.exp (-(b * ‖a‖)) * Real.exp (-((c₁ - b) * ‖z‖)) := by
  -- `‖a‖ ≤ ‖z‖ + ‖z + a‖`, so the two decay factors together beat `exp (-(b ‖a‖))`.
  have ha : ‖a‖ ≤ ‖z‖ + ‖z + a‖ := by
    simpa [add_comm ‖z‖] using norm_sub_le (z + a) z
  have hK : 0 ≤ K := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hf z)) (Real.exp_pos _)
  have hL : 0 ≤ L := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hg z)) (Real.exp_pos _)
  exact mul_le_mul_exp_mul_exp_of_le_add hb hbc (norm_nonneg _) (norm_nonneg _) (hf z) (hg _) ha
    hK hL

/-- **Overlap of exponentially decaying functions, pointwise.** If `‖f z‖ ≤ K exp (-(c ‖z‖))`
and `‖g z‖ ≤ L exp (-(c ‖z‖))` with `0 ≤ c`, then the product of `f` and of the translate
`g (· + a)`, which decays about `-a`, is at most `K L exp (-(c ‖a‖))` everywhere. -/
theorem norm_mul_norm_le_mul_exp_neg_mul_norm (hc : 0 ≤ c)
    (hf : ∀ z, ‖f z‖ ≤ K * Real.exp (-(c * ‖z‖)))
    (hg : ∀ z, ‖g z‖ ≤ L * Real.exp (-(c * ‖z‖))) (z a : E) :
    ‖f z‖ * ‖g (z + a)‖ ≤ K * L * Real.exp (-(c * ‖a‖)) := by
  simpa using norm_mul_norm_le_mul_exp_mul_exp hc le_rfl hf hg z a

/-- **Overlap of nonnegative functions decaying at every rate below `r`, pointwise.** If
`0 ≤ f`, `0 ≤ g` and both are at most `K exp (-(c ‖z‖))` for every rate `c < r`, with `K`
depending on `c`, then `f z g (z + a) ≤ K exp (-(c ‖a‖))` for every rate `c < r`. -/
theorem exists_mul_le_mul_exp_neg_mul_norm_of_forall_lt {f g : E → ℝ} {r : ℝ}
    (hf₀ : ∀ z, 0 ≤ f z) (hg₀ : ∀ z, 0 ≤ g z)
    (hf : ∀ c < r, ∃ K, ∀ z, f z ≤ K * Real.exp (-(c * ‖z‖)))
    (hg : ∀ c < r, ∃ K, ∀ z, g z ≤ K * Real.exp (-(c * ‖z‖))) (hr : 0 < r) (hc : c < r) :
    ∃ K, ∀ z a, f z * g (z + a) ≤ K * Real.exp (-(c * ‖a‖)) := by
  obtain ⟨Kf, hKf⟩ := hf (max c 0) (max_lt hc hr)
  obtain ⟨Kg, hKg⟩ := hg (max c 0) (max_lt hc hr)
  refine ⟨Kf * Kg, fun z a ↦ ?_⟩
  have h := norm_mul_norm_le_mul_exp_neg_mul_norm (le_max_right c 0) (f := f) (g := g)
    (fun w ↦ (Real.norm_of_nonneg (hf₀ w)).trans_le (hKf w))
    (fun w ↦ (Real.norm_of_nonneg (hg₀ w)).trans_le (hKg w)) z a
  rw [Real.norm_of_nonneg (hf₀ z), Real.norm_of_nonneg (hg₀ _)] at h
  have hKfg : 0 ≤ Kf * Kg :=
    nonneg_of_mul_nonneg_left ((mul_nonneg (hf₀ z) (hg₀ (z + a))).trans h) (Real.exp_pos _)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hKfg)
  exact Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (norm_nonneg a)))

/-- **Overlap of functions decaying away from separated finite sets of centres.** Let
`0 ≤ c < b`. Suppose that `0 ≤ f z ≤ K exp (-(b ρ))` whenever every point of the multiset `S` is
at distance at least `ρ` from `z`, that `0 ≤ g z ≤ L exp (-(b ρ))` whenever every point of `T`
is, and that every point of `S` is at distance at least `δ` from every point of `T`. Then

`f z g z ≤ K L exp (-(c δ)) ∑_{a ∈ S} exp (-((b - c) ‖z - a‖))`.

When `S` or `T` is empty the corresponding function vanishes, and so does the product. -/
theorem mul_le_mul_exp_mul_sum_exp_of_forall_le_norm_sub {f g : E → ℝ} {S T : Multiset E}
    {b δ : ℝ} (hc : 0 ≤ c) (hcb : c < b) (hf₀ : ∀ z, 0 ≤ f z) (hg₀ : ∀ z, 0 ≤ g z)
    (hf : ∀ z ρ, (∀ a ∈ S, ρ ≤ ‖z - a‖) → f z ≤ K * Real.exp (-(b * ρ)))
    (hg : ∀ z ρ, (∀ a ∈ T, ρ ≤ ‖z - a‖) → g z ≤ L * Real.exp (-(b * ρ)))
    (hST : ∀ a ∈ S, ∀ a' ∈ T, δ ≤ ‖a - a'‖) (z : E) :
    f z * g z ≤
      K * L * Real.exp (-(c * δ)) * (S.map fun a ↦ Real.exp (-((b - c) * ‖z - a‖))).sum := by
  have hb : 0 < b := hc.trans_lt hcb
  -- The radius `ρ = 0` is always admissible, so `K` and `L` are nonnegative.
  have hK : 0 ≤ K := by simpa using (hf₀ z).trans (hf z 0 fun a _ ↦ norm_nonneg _)
  have hL : 0 ≤ L := by simpa using (hg₀ z).trans (hg z 0 fun a _ ↦ norm_nonneg _)
  have hterm : ∀ y ∈ S.map fun a ↦ Real.exp (-((b - c) * ‖z - a‖)), 0 ≤ y := fun _ hy ↦ by
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hy
    positivity
  have hrhs : 0 ≤ K * L * Real.exp (-(c * δ)) *
      (S.map fun a ↦ Real.exp (-((b - c) * ‖z - a‖))).sum :=
    mul_nonneg (by positivity) (Multiset.sum_nonneg hterm)
  -- Without centres the bound holds for every radius, so the function vanishes.
  rcases S.empty_or_exists_mem with rfl | ⟨a₁, ha₁⟩
  · have := nonpos_of_forall_le_mul_exp hb fun ρ ↦ hf z ρ (by simp)
    nlinarith [hf₀ z, hg₀ z]
  rcases T.empty_or_exists_mem with rfl | ⟨a₂, ha₂⟩
  · have := nonpos_of_forall_le_mul_exp hb fun ρ ↦ hg z ρ (by simp)
    nlinarith [hf₀ z, hg₀ z]
  classical
  -- Otherwise use the nearest centres `a ∈ S` and `a' ∈ T`, with `δ ≤ ‖z - a‖ + ‖z - a'‖`.
  obtain ⟨a, ha, hamin⟩ := S.toFinset.exists_min_image (fun a ↦ ‖z - a‖)
    ⟨a₁, Multiset.mem_toFinset.2 ha₁⟩
  obtain ⟨a', ha', ha'min⟩ := T.toFinset.exists_min_image (fun a ↦ ‖z - a‖)
    ⟨a₂, Multiset.mem_toFinset.2 ha₂⟩
  rw [Multiset.mem_toFinset] at ha ha'
  have hδ : δ ≤ ‖z - a‖ + ‖z - a'‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub a z a'
    rw [norm_sub_rev a z] at this
    linarith [hST a ha a' ha']
  refine (mul_le_mul_exp_mul_exp_of_le_add hc hcb.le (norm_nonneg _) (hg₀ z)
    (hf z ‖z - a‖ fun x hx ↦ hamin x (Multiset.mem_toFinset.2 hx))
    (hg z ‖z - a'‖ fun x hx ↦ ha'min x (Multiset.mem_toFinset.2 hx)) hδ hK hL).trans ?_
  exact mul_le_mul_of_nonneg_left (Multiset.single_le_sum hterm _ (Multiset.mem_map_of_mem _ ha))
    (by positivity)

end TauCeti
