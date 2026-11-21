/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
import Mathlib.Analysis.Normed.Operator.Banach
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
closed graph theorem, applied in each variable in turn.

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

The induction on the order and the closed-graph construction of the bilinear map are adapted from
Tau Ceti contribution
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

/-- A chosen product `u w` in `W^{k,∞}(Ω)`; see `TauCeti.Wkp.mulTopL`. -/
private def mulAux (k : ℕ) (u w : Wkp mu Omega ∞ k) : Wkp mu Omega ∞ k :=
  (exists_value_ae_eq_mul_top k u w).choose

private theorem value_mulAux (k : ℕ) (u w : Wkp mu Omega ∞ k) :
    (value k (mulAux k u w) : E → ℝ) =ᵐ[mu.restrict Omega]
      fun x => value k u x * value k w x :=
  (exists_value_ae_eq_mul_top k u w).choose_spec

private theorem eq_mulAux_iff {k : ℕ} {u w z : Wkp mu Omega ∞ k} :
    z = mulAux k u w ↔
      (value k z : E → ℝ) =ᵐ[mu.restrict Omega] fun x => value k u x * value k w x :=
  ⟨fun h => h ▸ value_mulAux k u w,
    fun h => ext k (Lp.ext (h.trans (value_mulAux k u w).symm))⟩

private theorem mulAux_comm (k : ℕ) (u w : Wkp mu Omega ∞ k) : mulAux k u w = mulAux k w u := by
  refine eq_mulAux_iff.2 ?_
  filter_upwards [value_mulAux k u w] with x hx
  rw [hx, mul_comm]

private theorem mulAux_add_right (k : ℕ) (u w z : Wkp mu Omega ∞ k) :
    mulAux k u (w + z) = mulAux k u w + mulAux k u z := by
  refine (eq_mulAux_iff.2 ?_).symm
  filter_upwards [value_add_ae k (mulAux k u w) (mulAux k u z), value_mulAux k u w,
    value_mulAux k u z, value_add_ae k w z] with x h₁ h₂ h₃ h₄
  rw [h₁, Pi.add_apply, h₂, h₃, h₄, Pi.add_apply, mul_add]

private theorem mulAux_smul_right (k : ℕ) (c : ℝ) (u w : Wkp mu Omega ∞ k) :
    mulAux k u (c • w) = c • mulAux k u w := by
  refine (eq_mulAux_iff.2 ?_).symm
  filter_upwards [value_smul_ae k c (mulAux k u w), value_mulAux k u w, value_smul_ae k c w]
    with x h₁ h₂ h₃
  rw [h₁, Pi.smul_apply, h₂, h₃, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm]

private theorem mulAux_sub_right (k : ℕ) (u w z : Wkp mu Omega ∞ k) :
    mulAux k u (w - z) = mulAux k u w - mulAux k u z :=
  eq_sub_of_add_eq (by rw [← mulAux_add_right, sub_add_cancel])

private theorem mulAux_add_left (k : ℕ) (u w z : Wkp mu Omega ∞ k) :
    mulAux k (u + w) z = mulAux k u z + mulAux k w z := by
  rw [mulAux_comm, mulAux_add_right, mulAux_comm k z, mulAux_comm k z]

private theorem mulAux_smul_left (k : ℕ) (c : ℝ) (u w : Wkp mu Omega ∞ k) :
    mulAux k (c • u) w = c • mulAux k u w := by
  rw [mulAux_comm, mulAux_smul_right, mulAux_comm k w]

/-- The value of the product `u w` is bounded in `L^∞` by `‖u‖ ‖w‖`. -/
private theorem norm_value_mulAux_le (k : ℕ) (u w : Wkp mu Omega ∞ k) :
    ‖value k (mulAux k u w)‖ ≤ ‖u‖ * ‖w‖ :=
  (Lp.norm_le_mul_norm_of_ae_eq_smul (Lp.ae_norm_le_norm_top (value k u))
    (value_mulAux k u w)).trans
    (mul_le_mul (norm_value_le k u) (norm_value_le k w) (norm_nonneg _) (norm_nonneg _))

/-- If `w n → z` in `W^{k,∞}(Ω)`, then the values of the products `u (w n)` converge in `L^∞` to
the value of `u z`. -/
private theorem tendsto_value_mulAux (k : ℕ) (u : Wkp mu Omega ∞ k) {w : ℕ → Wkp mu Omega ∞ k}
    {z : Wkp mu Omega ∞ k} (hw : Tendsto w atTop (𝓝 z)) :
    Tendsto (fun n => value k (mulAux k u (w n))) atTop (𝓝 (value k (mulAux k u z))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n => ‖u‖ * ‖w n - z‖) atTop (𝓝 (‖u‖ * 0)) :=
    (tendsto_iff_norm_sub_tendsto_zero.1 hw).const_mul _
  rw [mul_zero] at hlim
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hlim
  rw [← value_sub, ← mulAux_sub_right]
  exact norm_value_mulAux_le k u _

/-- Multiplication by `u`, as a linear map on `W^{k,∞}(Ω)`. -/
private def mulLeftₗ (k : ℕ) (u : Wkp mu Omega ∞ k) : Wkp mu Omega ∞ k →ₗ[ℝ] Wkp mu Omega ∞ k where
  toFun := mulAux k u
  map_add' := mulAux_add_right k u
  map_smul' c w := mulAux_smul_right k c u w

/-- Multiplication by `u`, as a continuous linear map on `W^{k,∞}(Ω)`, by the closed graph
theorem: the value of the product depends continuously on the value of the second factor. -/
private def mulLeftL (k : ℕ) (u : Wkp mu Omega ∞ k) : Wkp mu Omega ∞ k →L[ℝ] Wkp mu Omega ∞ k :=
  ContinuousLinearMap.ofSeqClosedGraph (g := mulLeftₗ k u) fun _ _ _ hw hz =>
    ext k (tendsto_nhds_unique (tendsto_value hz) (tendsto_value_mulAux k u hw))

private theorem mulLeftL_apply (k : ℕ) (u w : Wkp mu Omega ∞ k) :
    mulLeftL k u w = mulAux k u w := by
  rw [mulLeftL, ContinuousLinearMap.coeFn_ofSeqClosedGraph, mulLeftₗ, LinearMap.coe_mk,
    AddHom.coe_mk]

/-- Multiplication on `W^{k,∞}(Ω)`, as a linear map into continuous linear maps. -/
private def mulₗ (k : ℕ) : Wkp mu Omega ∞ k →ₗ[ℝ] Wkp mu Omega ∞ k →L[ℝ] Wkp mu Omega ∞ k where
  toFun := mulLeftL k
  map_add' u u' := ContinuousLinearMap.ext fun w => by
    rw [add_apply, mulLeftL_apply, mulLeftL_apply, mulLeftL_apply,
      mulAux_add_left]
  map_smul' c u := ContinuousLinearMap.ext fun w => by
    rw [RingHom.id_apply, smul_apply, mulLeftL_apply, mulLeftL_apply,
      mulAux_smul_left]

private theorem mulₗ_apply_apply (k : ℕ) (u w : Wkp mu Omega ∞ k) :
    mulₗ k u w = mulAux k u w := by
  rw [mulₗ, LinearMap.coe_mk, AddHom.coe_mk, mulLeftL_apply]

/-- **Multiplication in `W^{k,∞}(Ω)`**, as a bounded bilinear map: there is a constant `C`, the
norm of `mulTopL k`, with `‖u w‖ ≤ C ‖u‖ ‖w‖` (`ContinuousLinearMap.le_opNorm₂`). The value of
`mulTopL k u w` is the pointwise product of the values of `u` and `w`
(`TauCeti.Wkp.value_mulTopL_ae`), and this determines it (`TauCeti.Wkp.eq_mulTopL_iff`). -/
def mulTopL (k : ℕ) : Wkp mu Omega ∞ k →L[ℝ] Wkp mu Omega ∞ k →L[ℝ] Wkp mu Omega ∞ k :=
  ContinuousLinearMap.ofSeqClosedGraph (g := mulₗ k) fun u z T hu hT => by
    refine ContinuousLinearMap.ext fun w => ext k (tendsto_nhds_unique
      (f := fun n => value k (mulAux k (u n) w)) (l := atTop) ?_ ?_)
    · -- Evaluation at `w` is continuous, so `u n * w → T w`.
      refine tendsto_value ((((ContinuousLinearMap.apply ℝ _ w).continuous.tendsto T).comp
        hT).congr fun n => ?_)
      rw [Function.comp_apply, Function.comp_apply, ContinuousLinearMap.apply_apply,
        mulₗ_apply_apply]
    · -- Multiplication by `w` is continuous, so `u n * w → z * w`.
      rw [mulₗ_apply_apply]
      simpa only [mulAux_comm k w] using tendsto_value_mulAux k w hu

private theorem mulTopL_apply_apply (k : ℕ) (u w : Wkp mu Omega ∞ k) :
    mulTopL k u w = mulAux k u w := by
  rw [mulTopL, ContinuousLinearMap.coeFn_ofSeqClosedGraph, mulₗ_apply_apply]

/-- The value of the product `mulTopL k u w` is the pointwise product of the values. -/
theorem value_mulTopL_ae (k : ℕ) (u w : Wkp mu Omega ∞ k) :
    (value k (mulTopL k u w) : E → ℝ) =ᵐ[mu.restrict Omega]
      fun x => value k u x * value k w x := by
  rw [mulTopL_apply_apply]
  exact value_mulAux k u w

/-- The product `mulTopL k u w` is the unique element of `W^{k,∞}(Ω)` whose value is the pointwise
product of the values of `u` and `w`. -/
theorem eq_mulTopL_iff {k : ℕ} {u w z : Wkp mu Omega ∞ k} :
    z = mulTopL k u w ↔
      (value k z : E → ℝ) =ᵐ[mu.restrict Omega] fun x => value k u x * value k w x := by
  rw [mulTopL_apply_apply]
  exact eq_mulAux_iff

/-- Multiplication in `W^{k,∞}(Ω)` is commutative. -/
theorem mulTopL_comm (k : ℕ) (u w : Wkp mu Omega ∞ k) : mulTopL k u w = mulTopL k w u := by
  rw [mulTopL_apply_apply, mulTopL_apply_apply]
  exact mulAux_comm k u w

/-- Multiplication in `W^{k,∞}(Ω)` is associative. -/
theorem mulTopL_assoc (k : ℕ) (u w z : Wkp mu Omega ∞ k) :
    mulTopL k (mulTopL k u w) z = mulTopL k u (mulTopL k w z) := by
  refine eq_mulTopL_iff.2 ?_
  filter_upwards [value_mulTopL_ae k (mulTopL k u w) z, value_mulTopL_ae k u w,
    value_mulTopL_ae k w z] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, mul_assoc]

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
