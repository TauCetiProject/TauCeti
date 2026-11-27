/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.AbsRpow
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.HeatEquation
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Solvability

/-!
# The initial datum `|x|^{3+β}`: the data space of the Cauchy problem is sharp

For every order `k` and `0 < α < 1`, the heat equation has an isomorphism
`u ↦ (∂ₜu - Δu, u(·, 0))` from `C_{par,b}^{k+2+α}` onto `C_{par,b}^{k+α} × C_b^{k+2,α}`
(`TauCeti.ParabolicCkHolderSpace.heatInitialDataCLE`), and so does every uniformly parabolic
equation with coefficients in `C_{par,b}^{k+α}`
(`TauCeti.ParabolicCkHolderSpace.euclideanInitialDataCLE`). This file first shows on the line, at
order `k = 1`, that the initial datum cannot be taken in a larger space than `C_b^{3,α}`, and then
the same at every order for every uniformly parabolic operator.

Let `0 < β < α` and let `χ` be a `C⁴` cutoff with compact support. The datum
`u₀(x) = χ(x) |x|^{3+β}` has third derivative `(3 + β)(2 + β)(1 + β) sign(x) |x|^β` near the
origin wherever `χ = 1` there, which is `β`-Hölder but not `α`-Hölder at `0`. So

* `u₀ ∈ C_b^{3,β}` for `β ≤ 1` (`TauCeti.exists_ckHolderSpace_coe_eq_mul_abs_rpow` at `k = 3`, in
  `Holder/AbsRpow.lean`);
* no element of `C_b^{3,α}` agrees with `|x|^{3+β}` near `0`
  (`TauCeti.not_exists_ckHolderSpace_coe_eq_of_eventuallyEq_abs_rpow`, ibid.);
* hence no map in `C_{par,b}^{3+α}` has such a time slice
  (`TauCeti.not_exists_parabolicCkHolderSpace_slabMk_eq_of_eventuallyEq_abs_rpow`), since the
  slices of a map of order `3 + α` lie in `C_b^{3,α}`;
* the solution of the heat equation with datum `u₀` lies in `C_{par,b}^{3+β}` but not in
  `C_{par,b}^{3+α}`
  (`TauCeti.exists_heatInitialDataL_fst_eq_zero_and_not_exists_parabolicCkHolderSpace_coe_eq`).

Thus the solution is no more regular than its datum, and the order-one isomorphism at exponent
`α` does not extend to data in `C_b^{3,β}`.

## Every order and every uniformly parabolic operator

On `ℝⁿ = EuclideanSpace ℝ ι` and a time slab `ℝⁿ × [0, T]`, the initial-data isomorphism of order
`k` (`TauCeti.ParabolicCkHolderSpace.euclideanInitialDataCLE`) solves

`P u = f`, `u(·, 0) = g`, `P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`,

for `f ∈ C_{par,b}^{k+α}` and `g ∈ C_b^{k+2,α}` with a solution in `C_{par,b}^{k+2+α}`. The
Hölder exponent of the initial datum cannot be lowered here either, even at the price of one more
derivative. Let `0 < β < α < 1` and let `g` be the power `|xᵢ|^(k + 3 + β)` of one coordinate,
cut off away from the hyperplane `xᵢ = 0`. Then:

* the datum `g` constructed by `TauCeti.exists_ckHolderSpace_eq_abs_rpow_comp_succ` lies in
  `C_b^{k+3,β}` and, as the same function, in `C_b^{k+2,α}`, so the isomorphism of order `k`
  applies and gives a solution `u ∈ C_{par,b}^{k+2+α}`;
* `g` does not lie in `C_b^{k+3,α}` (`TauCeti.not_exists_ckHolderSpace_eq_abs_rpow_comp`), so the
  isomorphism of order `k + 1` does not apply;
* and `u` does not lie in `C_{par,b}^{k+3+α}`, for any coefficients and any forcing
  (`TauCeti.ParabolicCkHolderSpace.not_exists_eq_euclideanInitialDataCLE_symm_of_eq_abs_rpow`).

The obstruction is the initial trace: every element of `C_{par,b}^{k+α}` restricts at every time
to an element of `C_b^{k,α}` (`TauCeti.ParabolicCkHolderSpace.spatialTrace`), while
`|ℓ x|^(k + β)` agrees near `ℓ = 0` with no element of `C_b^{k,α}` when `β < α`
(`TauCeti.ParabolicCkHolderSpace.not_exists_eq_abs_rpow_comp`).

For `k = 0`, the heat equation and `ι` with one element, this gives the same conclusion as the
order-one statement on the line above, `u ∉ C_{par,b}^{3+α}`, but for the order-zero solution at
exponent `α`, where the theorem above uses the order-one solution at exponent `β`.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4
  (the heat equation in parabolic Hölder spaces).
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
-/

public section

namespace TauCeti

open Filter Metric Set Topology ParabolicSpaceTime
open scoped NNReal

/-! ### Parabolic Hölder maps and the heat equation -/

/-- **No map of order `3 + α` has a slice `|x|^{3+β}`.** For `0 < β < α`, no map in
`C_{par,b}^{3+α}(ℝ × [a, b])` has, at any time `t`, a spatial slice that agrees with
`|x|^{3+β}` near `0`, since every slice lies in `C_b^{3,α}`. -/
theorem not_exists_parabolicCkHolderSpace_slabMk_eq_of_eventuallyEq_abs_rpow {β α : ℝ≥0}
    (hβ : 0 < β) (hβα : β < α) {a b : ℝ} (hab : a < b) {g : ℝ → ℝ}
    (hg : g =ᶠ[𝓝 0] fun x ↦ |x| ^ (3 + (β : ℝ))) (t : Icc a b) :
    ¬ ∃ v : ParabolicCkHolderSpace 3 α ℝ ℝ hab, ∀ x, v (slabMk x t) = g x := by
  rintro ⟨v, hv⟩
  exact not_exists_ckHolderSpace_coe_eq_of_eventuallyEq_abs_rpow 3 hβ hβα
    (by simpa only [Nat.cast_ofNat] using hg)
    ⟨v.spatialTrace t, funext fun x ↦ by rw [ParabolicCkHolderSpace.spatialTrace_apply, hv]⟩

/-- **The data space of the order-one Cauchy problem is sharp.** Let `0 < β < 1`, `β < α`,
`T > 0`, and let `χ` be a compactly supported `C⁴` function on the line equal to `1` near `0`.
The heat equation `∂ₜu - u'' = 0` on `ℝ × [0, T]` with initial datum `χ(x) |x|^{3+β}`, which
lies in `C_b^{3,β}` but not in `C_b^{3,α}`, has a solution `u` in `C_{par,b}^{3+β}`, and no map in
`C_{par,b}^{3+α}` has the values of `u`. -/
theorem exists_heatInitialDataL_fst_eq_zero_and_not_exists_parabolicCkHolderSpace_coe_eq
    {β α T : ℝ≥0} (hβ₀ : 0 < β) (hβ₁ : β < 1) (hβα : β < α) (hT : (0 : ℝ) < T)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 4 χ) (hχc : HasCompactSupport χ) (hχ₁ : χ =ᶠ[𝓝 0] 1) :
    ∃ u : ParabolicCkHolderSpace 3 β ℝ ℝ hT,
      (ParabolicCkHolderSpace.heatInitialDataL 1 hβ₁.le hT u).1 = 0 ∧
      (∀ x, u (slabMk x ⟨0, left_mem_Icc.2 hT.le⟩) = χ x * |x| ^ (3 + (β : ℝ))) ∧
      ¬ ∃ v : ParabolicCkHolderSpace 3 α ℝ ℝ hT, ⇑v = ⇑u := by
  obtain ⟨g, hg⟩ := exists_ckHolderSpace_coe_eq_mul_abs_rpow 3 hβ₀ hβ₁.le hχ hχc
  have hu := ParabolicCkHolderSpace.heatInitialDataL_heatSolutionL (k := 1) (hT := hT) hβ₀ hβ₁
    (0, g)
  set u := ParabolicCkHolderSpace.heatSolutionL 1 hβ₀ hβ₁ hT (0, g)
  have htrace (x : ℝ) : u (slabMk x ⟨0, left_mem_Icc.2 hT.le⟩) = χ x * |x| ^ (3 + (β : ℝ)) := by
    have h := congrArg (fun d ↦ d.2 x) hu
    simp only [ParabolicCkHolderSpace.heatInitialDataL_snd,
      ParabolicCkHolderSpace.spatialTrace_apply] at h
    rw [h, hg, Nat.cast_ofNat]
  refine ⟨u, by rw [hu], htrace, fun ⟨v, hv⟩ ↦ ?_⟩
  refine not_exists_parabolicCkHolderSpace_slabMk_eq_of_eventuallyEq_abs_rpow hβ₀ hβα hT
    (g := fun x ↦ χ x * |x| ^ (3 + (β : ℝ))) ?_ ⟨0, left_mem_Icc.2 hT.le⟩
    ⟨v, fun x ↦ by rw [hv, htrace]⟩
  filter_upwards [hχ₁] with x hx
  simp [hx]

/-! ### Every order -/

namespace ParabolicCkHolderSpace

/-- **No parabolic Hölder map of order `k` has `|ℓ x|^(k + β)` as a time slice, for `β < α`.** For
`0 < β < α`, a nonzero continuous linear functional `ℓ` and any time `t` of the slab, no element of
`C_{par,b}^{k+α}(E × [a, b])` equals `|ℓ x|^(k + β)` at time `t` wherever `|ℓ x| < 1`: its slice at
time `t` lies in `C_b^{k,α}(E)`. -/
theorem not_exists_eq_abs_rpow_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    {α β : ℝ≥0} {a b : ℝ} {hab : a < b} (hβ0 : 0 < β) (hβα : β < α) {ℓ : E →L[ℝ] ℝ}
    (hℓ : ℓ ≠ 0) (t : Icc a b) :
    ¬ ∃ u : ParabolicCkHolderSpace k α E ℝ hab,
      ∀ x, |ℓ x| < 1 → u (slabMk x t) = |ℓ x| ^ ((k : ℝ) + β) := by
  rintro ⟨u, hu⟩
  exact not_exists_ckHolderSpace_eq_abs_rpow_comp k hβ0 hβα hℓ
    ⟨u.spatialTrace t, fun x hx ↦ by rw [spatialTrace_apply]; exact hu x hx⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ} {α β T : ℝ≥0} {hT : (0 : ℝ) < T}

/-- **The solution of the Cauchy problem gains no regularity from a better datum of lower Hölder
exponent.** Let `0 < β < α < 1`, let the coefficients and the forcing have order `k`, and let the
initial datum `g ∈ C_b^{k+2,α}` equal `|xᵢ|^(k + 3 + β)` wherever `|xᵢ| < 1`. Then the solution
`u ∈ C_{par,b}^{k+2+α}` of `P u = f`, `u(·, 0) = g` does not lie in `C_{par,b}^{k+3+α}`. Such data
exist: `TauCeti.exists_ckHolderSpace_eq_abs_rpow_comp_succ` constructs one that, as the same
function, also lies in `C_b^{k+3,β}`. That higher membership is a property of the constructed
datum; the hypothesis here only asks `g` to match the power where `|xᵢ| < 1`. -/
theorem not_exists_eq_euclideanInitialDataCLE_symm_of_eq_abs_rpow (hα₀ : 0 < α)
    (hα₁ : α < 1) (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    (f : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    {g : CkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ} (hβ0 : 0 < β) (hβα : β < α) (i : ι)
    (hg : ∀ x : EuclideanSpace ℝ ι, |x i| < 1 → g x = |x i| ^ (((k + 3 : ℕ) : ℝ) + β)) :
    ¬ ∃ v : ParabolicCkHolderSpace (k + 3) α (EuclideanSpace ℝ ι) ℝ hT,
      ∀ p, v p = (euclideanInitialDataCLE hα₀ hα₁ a b c ha).symm (f, g) p := by
  rintro ⟨v, hv⟩
  have hproj : EuclideanSpace.proj (𝕜 := ℝ) i ≠ 0 := fun h ↦ by
    simpa using congrArg (fun e ↦ e (EuclideanSpace.single i 1)) h
  refine not_exists_eq_abs_rpow_comp hβ0 hβα hproj ⟨0, left_mem_Icc.2 hT.le⟩ ⟨v, fun x hx ↦ ?_⟩
  have htrace := spatialTrace_euclideanInitialDataCLE_symm_apply hα₀ hα₁ a b c ha (f, g)
  rw [hv, ← spatialTrace_apply, htrace]
  exact hg x hx

end ParabolicCkHolderSpace

end TauCeti
