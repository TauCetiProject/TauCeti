/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.LineDeriv.Basic
import TauCeti.Analysis.Sobolev.Wkp.BilinOfAeMul
import TauCeti.Analysis.Sobolev.Leibniz
import TauCeti.Analysis.Sobolev.W1p.Convex
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Multiplication in `W^{k,∞}(Ω)`

For every open set `Ω` of a finite-dimensional real inner product space and every order `k`, the
Sobolev space `W^{k,∞}(Ω)` is closed under pointwise multiplication, and multiplication is a
bounded bilinear map `W^{k,∞}(Ω) × W^{k,∞}(Ω) → W^{k,∞}(Ω)`
(`TauCeti.Wkp.mulTopL`). This is the endpoint `p = ∞` of the algebra property of `W^{k,p}` for
`k > n / p`: at `p = ∞` the condition holds at every order, including `k = 0`, where the space is
`L^∞(Ω)`. Neither boundedness nor boundary regularity of `Ω` is assumed.

A positive-order element of `W^{k,∞}(Ω)` has a representative that is locally Lipschitz on `Ω`,
the precise representative of its first-order part
(`TauCeti.W1p.locallyLipschitzOn_preciseRepresentative`), whose classical directional derivatives
are almost everywhere its weak ones (`TauCeti.W1p.lineDeriv_preciseRepresentative_ae_eq`). The
Leibniz rule with a locally Lipschitz factor (`TauCeti.HasWeakLineDerivOn.locallyLipschitzOn_smul`)
then gives the weak Leibniz rule `∂ᵥ(u w) = (∂ᵥu) w + u (∂ᵥw)`
(`TauCeti.Wkp.hasWeakLineDerivOn_value_mul_top`). Higher orders follow by induction, describing
`W^{k+1,∞}` by first derivatives (`TauCeti.Wkp.exists_value_ae_eq_of_forall_hasWeakLineDerivOn`):
both terms of the Leibniz rule are products of two elements of `W^{k,∞}`. Every factor is
bounded, so no interpolation inequality is needed. Boundedness of the bilinear map comes from the
closed graph theorem, through the shared construction `TauCeti.Wkp.bilinOfAeMul`.

## Main declarations

* `TauCeti.Wkp.hasWeakLineDerivOn_value_mul_top`: the weak Leibniz rule for products of
  positive-order elements of `W^{k,∞}(Ω)`, possibly of different orders.
* `TauCeti.Wkp.exists_value_ae_eq_mul_top`: the product of two elements of `W^{k,∞}(Ω)` lies in
  `W^{k,∞}(Ω)`.
* `TauCeti.Wkp.mulTopL`: multiplication on `W^{k,∞}(Ω)` as a bounded bilinear map, characterized
  by `TauCeti.Wkp.value_mulTopL_ae` and `TauCeti.Wkp.eq_mulTopL_iff`.
* `TauCeti.Wkp.mulTopL_comm`, `TauCeti.Wkp.mulTopL_assoc`: the product is commutative and
  associative.
* `TauCeti.Wkp.lowerOrder_mulTopL`: it commutes with forgetting the highest derivative.
* `TauCeti.Wkp.lineDerivL_mulTopL`: the Leibniz rule for the bundled product.

## References

* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 4.39.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised ed.,
  §4.2.3 (Lipschitz functions and `W^{1,∞}`).

The induction on the order is adapted from Tau Ceti contribution
[#1135](https://git.taucetiproject.org/TauCetiProject/TauCeti/pulls/1135),
*multiplication in `W^{k,p}(ℝⁿ)` for `p > n` at every order*.
-/

public section

noncomputable section

open Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology InnerProductSpace

namespace TauCeti

namespace Wkp

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E}

/-! ### The weak Leibniz rule -/

/-- **The weak Leibniz rule in `W^{k,∞}(Ω)`.** The product of `u ∈ W^{i+1,∞}(Ω)` and
`w ∈ W^{m+1,∞}(Ω)` has, in every direction `v`, the weak derivative `(∂ᵥu) w + u (∂ᵥw)`. -/
theorem hasWeakLineDerivOn_value_mul_top {i m : ℕ} (u : Wkp mu Omega ∞ (i + 1))
    (w : Wkp mu Omega ∞ (m + 1)) (v : E) :
    HasWeakLineDerivOn mu Omega (fun x => value (i + 1) u x * value (m + 1) w x)
      (fun x => value i (lineDerivL v i u) x * value (m + 1) w x +
        value (i + 1) u x * value m (lineDerivL v m w) x) v := by
  -- The precise representative `ψ` of `w` is locally Lipschitz, equal to `w` almost everywhere,
  -- and its classical directional derivative is almost everywhere `∂ᵥw`.
  have hll := W1p.locallyLipschitzOn_preciseRepresentative (firstOrder m w)
  have hψ := W1p.ae_eq_preciseRepresentative (firstOrder m w)
  have hdψ := W1p.lineDeriv_preciseRepresentative_ae_eq (firstOrder m w) v
  have hgrad := ((W1p.hasWeakFDerivOn (firstOrder m w)).hasWeakLineDerivOn v).ae_eq
    (by simpa only [value_firstOrder] using hasWeakLineDerivOn_lineDerivL v m w)
  rw [value_firstOrder] at hll hψ hdψ
  refine (((hasWeakLineDerivOn_lineDerivL v i u).locallyLipschitzOn_smul hll).congr_ae
    ?_).congr_ae_deriv ?_
  · filter_upwards [hψ] with x hx
    rw [smul_eq_mul, ← hx, mul_comm]
  · filter_upwards [hψ, hdψ, hgrad] with x hx hdx hgx
    rw [smul_eq_mul, smul_eq_mul, ← hx, hdx, ← innerSL_apply_apply ℝ, hgx]
    ring

/-! ### Products of every order -/

/-- The pointwise product of two `L^∞` values is in `L^∞`. -/
private theorem memLp_value_mul_top {i m : ℕ} (u : Wkp mu Omega ∞ i) (w : Wkp mu Omega ∞ m) :
    MemLp (fun x => value i u x * value m w x) ∞ (mu.restrict Omega) :=
  (Lp.memLp (value i u)).mul (Lp.memLp (value m w))

/-- **`W^{k,∞}(Ω)` is closed under multiplication.** For `u, w ∈ W^{k,∞}(Ω)` some element of
`W^{k,∞}(Ω)` has value `u w` almost everywhere on `Ω`. -/
theorem exists_value_ae_eq_mul_top : ∀ (k : ℕ) (u w : Wkp mu Omega ∞ k),
    ∃ z : Wkp mu Omega ∞ k,
      (value k z : E → ℝ) =ᵐ[mu.restrict Omega] fun x => value k u x * value k w x
  | 0, u, w => ⟨(memLp_value_mul_top u w).toLp _, by
      rw [value_zero]
      exact (memLp_value_mul_top u w).coeFn_toLp⟩
  | k + 1, u, w => by
    -- By the Leibniz rule each directional derivative of `u w` is a sum of two products of
    -- elements of `W^{k,∞}(Ω)`, which lie in `W^{k,∞}(Ω)` by induction.
    have hd : ∀ v : E, ∃ d : Wkp mu Omega ∞ k, HasWeakLineDerivOn mu Omega
        (fun x => value (k + 1) u x * value (k + 1) w x) (value k d) v := by
      intro v
      obtain ⟨z₁, hz₁⟩ := exists_value_ae_eq_mul_top k (lineDerivL v k u) (lowerOrder k w)
      obtain ⟨z₂, hz₂⟩ := exists_value_ae_eq_mul_top k (lowerOrder k u) (lineDerivL v k w)
      refine ⟨z₁ + z₂, (hasWeakLineDerivOn_value_mul_top u w v).congr_ae_deriv ?_⟩
      filter_upwards [hz₁, hz₂, value_add_ae k z₁ z₂] with x h₁ h₂ h₃
      rw [h₃, Pi.add_apply, h₁, h₂, ← value_succ, ← value_succ]
    choose d hd using hd
    exact exists_value_ae_eq_of_forall_hasWeakLineDerivOn k (memLp_value_mul_top u w) d hd

/-! ### Multiplication as a bounded bilinear map -/

/-- **Multiplication in `W^{k,∞}(Ω)`**, as a bounded bilinear map: there is a constant `C`, the
norm of `mulTopL k`, with `‖u w‖ ≤ C ‖u‖ ‖w‖` (`ContinuousLinearMap.le_opNorm₂`). The value of
`mulTopL k u w` is the pointwise product of the values of `u` and `w`
(`TauCeti.Wkp.value_mulTopL_ae`), and this determines it (`TauCeti.Wkp.eq_mulTopL_iff`). -/
def mulTopL (k : ℕ) : Wkp mu Omega ∞ k →L[ℝ] Wkp mu Omega ∞ k →L[ℝ] Wkp mu Omega ∞ k :=
  bilinOfAeMul k (exists_value_ae_eq_mul_top k) fun u =>
    ⟨‖value k u‖, Lp.ae_norm_le_norm_top (value k u)⟩

/-- The value of the product `mulTopL k u w` is the pointwise product of the values. -/
theorem value_mulTopL_ae (k : ℕ) (u w : Wkp mu Omega ∞ k) :
    (value k (mulTopL k u w) : E → ℝ) =ᵐ[mu.restrict Omega]
      fun x => value k u x * value k w x :=
  value_bilinOfAeMul_ae u w

/-- The product `mulTopL k u w` is the unique element of `W^{k,∞}(Ω)` whose value is the pointwise
product of the values of `u` and `w`. -/
theorem eq_mulTopL_iff {k : ℕ} {u w z : Wkp mu Omega ∞ k} :
    z = mulTopL k u w ↔
      (value k z : E → ℝ) =ᵐ[mu.restrict Omega] fun x => value k u x * value k w x :=
  eq_bilinOfAeMul_iff

/-- Multiplication in `W^{k,∞}(Ω)` is commutative. -/
theorem mulTopL_comm (k : ℕ) (u w : Wkp mu Omega ∞ k) : mulTopL k u w = mulTopL k w u :=
  bilinOfAeMul_comm u w

/-- Multiplication in `W^{k,∞}(Ω)` is associative. -/
theorem mulTopL_assoc (k : ℕ) (u w z : Wkp mu Omega ∞ k) :
    mulTopL k (mulTopL k u w) z = mulTopL k u (mulTopL k w z) :=
  bilinOfAeMul_assoc u w z

/-- Forgetting the highest derivative commutes with multiplication. -/
theorem lowerOrder_mulTopL (k : ℕ) (u w : Wkp mu Omega ∞ (k + 1)) :
    lowerOrder k (mulTopL (k + 1) u w) = mulTopL k (lowerOrder k u) (lowerOrder k w) := by
  refine eq_mulTopL_iff.2 ?_
  simpa only [← value_succ] using value_mulTopL_ae (k + 1) u w

/-- **The Leibniz rule for `mulTopL`.** The directional derivative of a product in
`W^{k+1,∞}(Ω)` is `∂ᵥ(u w) = (∂ᵥu) w + u (∂ᵥw)`, computed in `W^{k,∞}(Ω)`. -/
theorem lineDerivL_mulTopL (v : E) (k : ℕ) (u w : Wkp mu Omega ∞ (k + 1)) :
    lineDerivL v k (mulTopL (k + 1) u w) =
      mulTopL k (lineDerivL v k u) (lowerOrder k w) +
        mulTopL k (lowerOrder k u) (lineDerivL v k w) := by
  refine lineDerivL_eq_of_hasWeakLineDerivOn (((hasWeakLineDerivOn_value_mul_top u w v).congr_ae
    (value_mulTopL_ae (k + 1) u w).symm).congr_ae_deriv ?_)
  filter_upwards [value_add_ae k (mulTopL k (lineDerivL v k u) (lowerOrder k w))
      (mulTopL k (lowerOrder k u) (lineDerivL v k w)),
    value_mulTopL_ae k (lineDerivL v k u) (lowerOrder k w),
    value_mulTopL_ae k (lowerOrder k u) (lineDerivL v k w)] with x h₁ h₂ h₃
  rw [h₁, Pi.add_apply, h₂, h₃, ← value_succ, ← value_succ]

end Wkp

end TauCeti
