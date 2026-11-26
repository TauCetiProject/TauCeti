/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.AbsRpow
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Solvability

/-!
# The data space of the parabolic Cauchy problem is sharp

On `ℝⁿ = EuclideanSpace ℝ ι` and a time slab `ℝⁿ × [0, T]`, the initial-data isomorphism of order
`k` (`TauCeti.ParabolicCkHolderSpace.euclideanInitialDataCLE`) solves

`P u = f`, `u(·, 0) = g`, `P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`,

for `f ∈ C_{par,b}^{k+α}` and `g ∈ C_b^{k+2,α}` with a solution in `C_{par,b}^{k+2+α}`. This file
shows that the Hölder exponent of the initial datum cannot be lowered, even at the price of one
more derivative. Let `0 < β < α < 1` and let `g` be the power `|xᵢ|^(k + 3 + β)` of one coordinate,
cut off away from the hyperplane `xᵢ = 0`. Then:

* `g` lies in `C_b^{k+3,β}` (`TauCeti.exists_ckHolderSpace_eq_abs_rpow_comp`) and in
  `C_b^{k+2,α}` (`TauCeti.exists_ckHolderSpace_eq_abs_rpow_comp_succ`), so the isomorphism of
  order `k` applies and gives a solution `u ∈ C_{par,b}^{k+2+α}`;
* `g` does not lie in `C_b^{k+3,α}` (`TauCeti.not_exists_ckHolderSpace_eq_abs_rpow_comp`), so the
  isomorphism of order `k + 1` does not apply;
* and `u` does not lie in `C_{par,b}^{k+3+α}`, for any coefficients and any forcing
  (`TauCeti.ParabolicCkHolderSpace.not_exists_eq_euclideanInitialDataCLE_symm_of_eq_abs_rpow`).

For `k = 0`, the heat equation and dimension one this is the sharpness of the data space in the
order-one isomorphism: `u₀ = |x|^(3 + β)`, smoothed at infinity, is in `C_b^{3,β} ∖ C_b^{3,α}`,
and the solution of `∂ₜu - ∂ₓ²u = 0` with initial value `u₀` is not in `C_{par,b}^{3+α}`.

The obstruction is the initial trace: every element of `C_{par,b}^{k+α}` restricts at every time
to an element of `C_b^{k,α}` (`TauCeti.ParabolicCkHolderSpace.spatialTrace`), while
`|ℓ x|^(k + β)` agrees near `ℓ = 0` with no element of `C_b^{k,α}` when `β < α`
(`TauCeti.ParabolicCkHolderSpace.not_exists_eq_abs_rpow_comp`).

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
-/

public section

namespace TauCeti

open Set ParabolicSpaceTime
open scoped NNReal

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
exist (`TauCeti.exists_ckHolderSpace_eq_abs_rpow_comp_succ`), and they lie in `C_b^{k+3,β}`
(`TauCeti.exists_ckHolderSpace_eq_abs_rpow_comp`). -/
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
