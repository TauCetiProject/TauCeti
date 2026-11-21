/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.SupercriticalMultiplication
public import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
import Mathlib.Analysis.Normed.Operator.Banach
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Measure.Restrict

/-!
# Multiplication in supercritical Sobolev spaces of every order

Let `E` have real dimension `n` and let `n < p < ∞`. Then `W^{k,p}(ℝⁿ)` is an algebra under
pointwise multiplication for every order `k ≥ 1`: the product of two of its elements is again in
`W^{k,p}(ℝⁿ)`, and multiplication is a bounded bilinear map (`TauCeti.Wkp.mulL`). More generally,
for `j ≤ i` and `j ≤ m + 1`, the product of `u ∈ W^{i,p}(ℝⁿ)` and `v ∈ W^{m+1,p}(ℝⁿ)` lies in
`W^{j,p}(ℝⁿ)` (`TauCeti.Wkp.exists_value_ae_eq_mul`); in particular
`W^{j,p}(ℝⁿ)` is a module over `W^{k,p}(ℝⁿ)` for `j ≤ k`.

The input is the first-order case `TauCeti.W1p.mul`: by Morrey's embedding every element of
`W^{1,p}(ℝⁿ)` has a bounded continuous representative, and the product of two `W^{1,p}`
functions satisfies the weak Leibniz rule `∂ₑ(u v) = (∂ₑu) v + u (∂ₑv)`
(`TauCeti.Wkp.hasWeakLineDerivOn_value_mul`). The higher orders follow by induction on the order
of the product, describing `W^{j+1,p}` by first derivatives
(`TauCeti.Wkp.exists_value_ae_eq_of_forall_hasWeakLineDerivOn`): both terms of the Leibniz rule
are products of an element of `W^{j,p}` with an element of a space of order at least `j + 1`, so
they lie in `W^{j,p}` by the induction hypothesis. No Gagliardo–Nirenberg interpolation is needed
in this range, since every factor of positive order is bounded. Boundedness of the bilinear map
comes from the closed graph theorem, applied in each variable in turn.

This is the global counterpart, on the Banach spaces `TauCeti.Wkp` over `ℝⁿ` in every dimension,
of the algebra property `TauCeti.MemWkpLoc.bilin_succ` of the local Sobolev classes on planar
domains.

The assumption `p > n` is what makes every positive-order factor bounded. For `n / k < p ≤ n` the
space `W^{k,p}(ℝⁿ)` is still an algebra, but the intermediate derivatives must be estimated by
Sobolev embeddings, which this file does not do.

## Main declarations

* `TauCeti.Wkp.hasWeakLineDerivOn_value_mul`: the weak Leibniz rule for products of
  positive-order Sobolev functions when `p > n`.
* `TauCeti.Wkp.exists_value_ae_eq_mul`: the product of `u ∈ W^{i,p}(ℝⁿ)` and
  `v ∈ W^{m+1,p}(ℝⁿ)` lies in `W^{j,p}(ℝⁿ)` for `j ≤ i` and `j ≤ m + 1`.
* `TauCeti.Wkp.mulL`: multiplication on `W^{k+1,p}(ℝⁿ)` as a bounded bilinear map, characterized
  by `TauCeti.Wkp.value_mulL_ae` and `TauCeti.Wkp.eq_mulL_iff`.
* `TauCeti.Wkp.mulL_comm`, `TauCeti.Wkp.mulL_assoc`: the product is commutative and associative.
* `TauCeti.Wkp.lowerOrder_mulL`, `TauCeti.Wkp.firstOrder_mulL`: it commutes with forgetting
  derivatives, and its first-order part is the product `TauCeti.W1p.mul` of the first-order
  parts.

## References

* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 4.39.
-/

public section

noncomputable section

namespace TauCeti

namespace Wkp

open Filter MeasureTheory Module TopologicalSpace
open scoped ENNReal NNReal Topology

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]

/-! ### Bounded representatives -/

/-- A positive-order Sobolev function on `ℝⁿ`, `n < p`, is represented by the Morrey
representative of its first-order part. -/
private theorem value_ae_eq_morreyRepresentative (hp : (finrank ℝ E : ℝ≥0) < p) {k : ℕ}
    (u : Wkp mu ⊤ (p : ℝ≥0∞) (k + 1)) :
    (value (k + 1) u : E → ℝ) =ᵐ[mu] W1p.morreyRepresentative (firstOrder k u) hp := by
  simpa only [value_firstOrder] using W1p.value_ae_eq_morreyRepresentative (firstOrder k u) hp

/-- The Morrey representative of a positive-order Sobolev function is bounded by a fixed multiple
of its Sobolev norm. -/
private theorem norm_morreyRepresentative_firstOrder_le (hp : (finrank ℝ E : ℝ≥0) < p) (k : ℕ)
    (u : Wkp mu ⊤ (p : ℝ≥0∞) (k + 1)) (x : E) :
    ‖W1p.morreyRepresentative (firstOrder k u) hp x‖ ≤
      ‖(W1p.morreyEmbedding (mu := mu) hp).comp (firstOrderL k)‖ * ‖u‖ := by
  calc ‖W1p.morreyRepresentative (firstOrder k u) hp x‖
      ≤ ‖W1p.morreyEmbedding hp (firstOrder k u)‖ :=
        W1p.norm_morreyRepresentative_le_norm_morreyEmbedding hp _ x
    _ = ‖(W1p.morreyEmbedding hp).comp (firstOrderL k) u‖ := by
        rw [ContinuousLinearMap.comp_apply, firstOrderL_apply]
    _ ≤ _ := ContinuousLinearMap.le_opNorm _ _

/-- The product of an `Lᵖ` value with the value of a positive-order Sobolev function is in `Lᵖ`,
since the latter is bounded. -/
private theorem memLp_value_mul (hp : (finrank ℝ E : ℝ≥0) < p) {i m : ℕ}
    (u : Wkp mu ⊤ (p : ℝ≥0∞) i) (v : Wkp mu ⊤ (p : ℝ≥0∞) (m + 1)) :
    MemLp (fun x => value i u x * value (m + 1) v x) p (mu.restrict ⊤) := by
  refine (MemLp.fun_mul (p := ∞) (q := (p : ℝ≥0∞)) (r := (p : ℝ≥0∞))
    (W1p.memLp_top_morreyRepresentative hp (firstOrder m v)) (Lp.memLp (value i u))).ae_eq ?_
  rw [EventuallyEq, Measure.ae_restrict_coe_opens_top]
  filter_upwards [value_ae_eq_morreyRepresentative hp v] with x hx
  rw [hx, mul_comm]

/-! ### The weak Leibniz rule and products of every order -/

/-- **The weak Leibniz rule in the supercritical range.** If `p > n`, the product of
`u ∈ W^{i+1,p}(ℝⁿ)` and `v ∈ W^{m+1,p}(ℝⁿ)` has, in every direction `e`, the weak derivative
`(∂ₑu) v + u (∂ₑv)`. -/
theorem hasWeakLineDerivOn_value_mul (hp : (finrank ℝ E : ℝ≥0) < p) {i m : ℕ}
    (u : Wkp mu ⊤ (p : ℝ≥0∞) (i + 1)) (v : Wkp mu ⊤ (p : ℝ≥0∞) (m + 1)) (e : E) :
    HasWeakLineDerivOn mu ⊤ (fun x => value (i + 1) u x * value (m + 1) v x)
      (fun x => value i (lineDerivL e i u) x * value (m + 1) v x +
        value (i + 1) u x * value m (lineDerivL e m v) x) e := by
  -- The directional derivatives of the first-order parts are those of `u` and `v`.
  have hgu : (fun x => innerSL ℝ (W1p.gradient (firstOrder i u) x) e) =ᵐ[mu.restrict ⊤]
      value i (lineDerivL e i u) := by
    have h := (W1p.hasWeakFDerivOn (firstOrder i u)).hasWeakLineDerivOn e
    rw [value_firstOrder] at h
    exact h.ae_eq (hasWeakLineDerivOn_lineDerivL e i u)
  have hgv : (fun x => innerSL ℝ (W1p.gradient (firstOrder m v) x) e) =ᵐ[mu.restrict ⊤]
      value m (lineDerivL e m v) := by
    have h := (W1p.hasWeakFDerivOn (firstOrder m v)).hasWeakLineDerivOn e
    rw [value_firstOrder] at h
    exact h.ae_eq (hasWeakLineDerivOn_lineDerivL e m v)
  have hu := ae_restrict_of_ae (s := ((⊤ : Opens E) : Set E))
    (value_ae_eq_morreyRepresentative hp u)
  have hv := ae_restrict_of_ae (s := ((⊤ : Opens E) : Set E))
    (value_ae_eq_morreyRepresentative hp v)
  -- Transport the Leibniz rule for the Morrey representatives of the first-order parts.
  refine (((W1p.hasWeakFDerivOn_mul_morreyRepresentative hp (firstOrder i u)
    (firstOrder m v)).hasWeakLineDerivOn e).congr_ae ?_).congr_ae_deriv ?_
  · filter_upwards [hu, hv] with x hx hy
    rw [hx, hy]
  · filter_upwards [hgu, hgv, hu, hv] with x h₁ h₂ h₃ h₄
    simp only [innerSL_apply_apply] at h₁ h₂ ⊢
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, h₁, h₂, h₃, h₄]
    ring

/-- **Products in supercritical Sobolev spaces.** Let `p > n`. If `u ∈ W^{i,p}(ℝⁿ)` and
`v ∈ W^{m+1,p}(ℝⁿ)`, then `u v ∈ W^{j,p}(ℝⁿ)` for every `j ≤ i` with `j ≤ m + 1`: some element of
`W^{j,p}(ℝⁿ)` has value `u v` almost everywhere. For `i = j = m + 1` this says that
`W^{m+1,p}(ℝⁿ)` is closed under multiplication. -/
theorem exists_value_ae_eq_mul (hp : (finrank ℝ E : ℝ≥0) < p) {i j m : ℕ} (hi : j ≤ i)
    (hm : j ≤ m + 1) (u : Wkp mu ⊤ (p : ℝ≥0∞) i) (v : Wkp mu ⊤ (p : ℝ≥0∞) (m + 1)) :
    ∃ w : Wkp mu ⊤ (p : ℝ≥0∞) j,
      (value j w : E → ℝ) =ᵐ[mu] fun x => value i u x * value (m + 1) v x := by
  induction j generalizing i m with
  | zero =>
    refine ⟨(memLp_value_mul hp u v).toLp _, ?_⟩
    rw [value_zero, EventuallyEq, ← Measure.ae_restrict_coe_opens_top]
    exact (memLp_value_mul hp u v).coeFn_toLp
  | succ j ih =>
    obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    -- By the Leibniz rule, every directional derivative of `u v` is a sum of two products, each
    -- of an element of order at least `j` with an element of order at least `j + 1`.
    have hd : ∀ e : E, ∃ d : Wkp mu ⊤ (p : ℝ≥0∞) j, HasWeakLineDerivOn mu ⊤
        (fun x => value (i + 1) u x * value (m + 1) v x) (value j d) e := by
      intro e
      obtain ⟨w₁, hw₁⟩ := ih (by omega) (by omega) (lineDerivL e i u) v
      obtain ⟨w₂, hw₂⟩ := ih (i := m) (m := i) (by omega) (by omega) (lineDerivL e m v) u
      refine ⟨w₁ + w₂, (hasWeakLineDerivOn_value_mul hp u v e).congr_ae_deriv ?_⟩
      filter_upwards [ae_restrict_of_ae hw₁, ae_restrict_of_ae hw₂, value_add_ae j w₁ w₂]
        with x h₁ h₂ h₃
      rw [h₃, Pi.add_apply, h₁, h₂, mul_comm (value m (lineDerivL e m v) x)]
    choose d hd using hd
    obtain ⟨w, hw⟩ := exists_value_ae_eq_of_forall_hasWeakLineDerivOn j
      (memLp_value_mul hp u v) d hd
    exact ⟨w, by rwa [EventuallyEq, Measure.ae_restrict_coe_opens_top] at hw⟩

/-! ### Multiplication as a bounded bilinear map -/

/-- A chosen product `u v` in `W^{k+1,p}(ℝⁿ)`; see `TauCeti.Wkp.mulL`. -/
private def mulAux (hp : (finrank ℝ E : ℝ≥0) < p) (k : ℕ) (u v : Wkp mu ⊤ (p : ℝ≥0∞) (k + 1)) :
    Wkp mu ⊤ (p : ℝ≥0∞) (k + 1) :=
  (exists_value_ae_eq_mul hp le_rfl le_rfl u v).choose

private theorem value_mulAux (hp : (finrank ℝ E : ℝ≥0) < p) (k : ℕ)
    (u v : Wkp mu ⊤ (p : ℝ≥0∞) (k + 1)) :
    (value (k + 1) (mulAux hp k u v) : E → ℝ) =ᵐ[mu]
      fun x => value (k + 1) u x * value (k + 1) v x :=
  (exists_value_ae_eq_mul hp le_rfl le_rfl u v).choose_spec

private theorem eq_mulAux_iff (hp : (finrank ℝ E : ℝ≥0) < p) {k : ℕ}
    {u v w : Wkp mu ⊤ (p : ℝ≥0∞) (k + 1)} :
    w = mulAux hp k u v ↔
      (value (k + 1) w : E → ℝ) =ᵐ[mu] fun x => value (k + 1) u x * value (k + 1) v x :=
  ⟨fun h => h ▸ value_mulAux hp k u v,
    fun h => ext_ae (h.trans (value_mulAux hp k u v).symm)⟩

private theorem mulAux_comm (hp : (finrank ℝ E : ℝ≥0) < p) (k : ℕ)
    (u v : Wkp mu ⊤ (p : ℝ≥0∞) (k + 1)) : mulAux hp k u v = mulAux hp k v u := by
  refine (eq_mulAux_iff hp).2 ?_
  filter_upwards [value_mulAux hp k u v] with x hx
  rw [hx, mul_comm]

private theorem mulAux_add_right (hp : (finrank ℝ E : ℝ≥0) < p) (k : ℕ)
    (u v w : Wkp mu ⊤ (p : ℝ≥0∞) (k + 1)) :
    mulAux hp k u (v + w) = mulAux hp k u v + mulAux hp k u w := by
  refine ((eq_mulAux_iff hp).2 ?_).symm
  filter_upwards [(Measure.ae_restrict_coe_opens_top mu).ge
      (value_add_ae (k + 1) (mulAux hp k u v) (mulAux hp k u w)),
    value_mulAux hp k u v, value_mulAux hp k u w,
    (Measure.ae_restrict_coe_opens_top mu).ge (value_add_ae (k + 1) v w)] with x h₁ h₂ h₃ h₄
  rw [h₁, Pi.add_apply, h₂, h₃, h₄, Pi.add_apply, mul_add]

private theorem mulAux_smul_right (hp : (finrank ℝ E : ℝ≥0) < p) (k : ℕ) (c : ℝ)
    (u v : Wkp mu ⊤ (p : ℝ≥0∞) (k + 1)) : mulAux hp k u (c • v) = c • mulAux hp k u v := by
  refine ((eq_mulAux_iff hp).2 ?_).symm
  filter_upwards [(Measure.ae_restrict_coe_opens_top mu).ge
      (value_smul_ae (k + 1) c (mulAux hp k u v)), value_mulAux hp k u v,
    (Measure.ae_restrict_coe_opens_top mu).ge (value_smul_ae (k + 1) c v)] with x h₁ h₂ h₃
  rw [h₁, Pi.smul_apply, h₂, h₃, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm]

private theorem mulAux_sub_right (hp : (finrank ℝ E : ℝ≥0) < p) (k : ℕ)
    (u v w : Wkp mu ⊤ (p : ℝ≥0∞) (k + 1)) :
    mulAux hp k u (v - w) = mulAux hp k u v - mulAux hp k u w :=
  eq_sub_of_add_eq (by rw [← mulAux_add_right, sub_add_cancel])

private theorem mulAux_add_left (hp : (finrank ℝ E : ℝ≥0) < p) (k : ℕ)
    (u v w : Wkp mu ⊤ (p : ℝ≥0∞) (k + 1)) :
    mulAux hp k (u + v) w = mulAux hp k u w + mulAux hp k v w := by
  rw [mulAux_comm, mulAux_add_right, mulAux_comm hp k w, mulAux_comm hp k w]

private theorem mulAux_smul_left (hp : (finrank ℝ E : ℝ≥0) < p) (k : ℕ) (c : ℝ)
    (u v : Wkp mu ⊤ (p : ℝ≥0∞) (k + 1)) : mulAux hp k (c • u) v = c • mulAux hp k u v := by
  rw [mulAux_comm, mulAux_smul_right, mulAux_comm hp k v]

/-- The value of the product `u v` is bounded in `Lᵖ` by `C ‖u‖ ‖v‖`: the Morrey representative
of `u` is bounded by a multiple of `‖u‖`. -/
private theorem norm_value_mulAux_le (hp : (finrank ℝ E : ℝ≥0) < p) (k : ℕ)
    (u v : Wkp mu ⊤ (p : ℝ≥0∞) (k + 1)) :
    ‖value (k + 1) (mulAux hp k u v)‖ ≤
      ‖(W1p.morreyEmbedding (mu := mu) hp).comp (firstOrderL k)‖ * ‖u‖ * ‖v‖ := by
  refine (Lp.norm_le_mul_norm_of_ae_eq_smul
    (ψ := W1p.morreyRepresentative (firstOrder k u) hp)
    (Eventually.of_forall fun x => norm_morreyRepresentative_firstOrder_le hp k u x) ?_).trans
    (mul_le_mul_of_nonneg_left (norm_value_le _ v) (by positivity))
  rw [EventuallyEq, Measure.ae_restrict_coe_opens_top]
  filter_upwards [value_mulAux hp k u v, value_ae_eq_morreyRepresentative hp u] with x h₁ h₂
  rw [h₁, h₂, smul_eq_mul]

/-- If `v n → x` in `W^{k+1,p}(ℝⁿ)`, then the values of the products `u (v n)` converge in `Lᵖ`
to the value of `u x`. -/
private theorem tendsto_value_mulAux (hp : (finrank ℝ E : ℝ≥0) < p) (k : ℕ)
    (u : Wkp mu ⊤ (p : ℝ≥0∞) (k + 1)) {v : ℕ → Wkp mu ⊤ (p : ℝ≥0∞) (k + 1)}
    {x : Wkp mu ⊤ (p : ℝ≥0∞) (k + 1)} (hv : Tendsto v atTop (𝓝 x)) :
    Tendsto (fun n => value (k + 1) (mulAux hp k u (v n))) atTop
      (𝓝 (value (k + 1) (mulAux hp k u x))) := by
  set C := ‖(W1p.morreyEmbedding (mu := mu) hp).comp (firstOrderL k)‖ * ‖u‖
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n => C * ‖v n - x‖) atTop (𝓝 (C * 0)) :=
    (tendsto_iff_norm_sub_tendsto_zero.1 hv).const_mul _
  rw [mul_zero] at hlim
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hlim
  rw [← value_sub, ← mulAux_sub_right]
  exact norm_value_mulAux_le hp k u _

/-- Multiplication by `u`, as a linear map on `W^{k+1,p}(ℝⁿ)`. -/
private def mulLeftₗ (hp : (finrank ℝ E : ℝ≥0) < p) (k : ℕ) (u : Wkp mu ⊤ (p : ℝ≥0∞) (k + 1)) :
    Wkp mu ⊤ (p : ℝ≥0∞) (k + 1) →ₗ[ℝ] Wkp mu ⊤ (p : ℝ≥0∞) (k + 1) where
  toFun := mulAux hp k u
  map_add' := mulAux_add_right hp k u
  map_smul' c v := mulAux_smul_right hp k c u v

/-- Multiplication by `u`, as a continuous linear map on `W^{k+1,p}(ℝⁿ)`, by the closed graph
theorem: the value of the product depends continuously on the value of `v`. -/
private def mulLeftL (hp : (finrank ℝ E : ℝ≥0) < p) (k : ℕ) (u : Wkp mu ⊤ (p : ℝ≥0∞) (k + 1)) :
    Wkp mu ⊤ (p : ℝ≥0∞) (k + 1) →L[ℝ] Wkp mu ⊤ (p : ℝ≥0∞) (k + 1) :=
  ContinuousLinearMap.ofSeqClosedGraph (g := mulLeftₗ hp k u) fun _ _ _ hv hy =>
    ext (k + 1) (tendsto_nhds_unique (tendsto_value hy) (tendsto_value_mulAux hp k u hv))

private theorem mulLeftL_apply (hp : (finrank ℝ E : ℝ≥0) < p) (k : ℕ)
    (u v : Wkp mu ⊤ (p : ℝ≥0∞) (k + 1)) : mulLeftL hp k u v = mulAux hp k u v := by
  rw [mulLeftL, ContinuousLinearMap.coeFn_ofSeqClosedGraph, mulLeftₗ, LinearMap.coe_mk,
    AddHom.coe_mk]

/-- Multiplication on `W^{k+1,p}(ℝⁿ)`, as a linear map into continuous linear maps. -/
private def mulₗ (hp : (finrank ℝ E : ℝ≥0) < p) (k : ℕ) :
    Wkp mu ⊤ (p : ℝ≥0∞) (k + 1) →ₗ[ℝ]
      Wkp mu ⊤ (p : ℝ≥0∞) (k + 1) →L[ℝ] Wkp mu ⊤ (p : ℝ≥0∞) (k + 1) where
  toFun := mulLeftL hp k
  map_add' u u' := ContinuousLinearMap.ext fun v => by
    rw [add_apply, mulLeftL_apply, mulLeftL_apply, mulLeftL_apply, mulAux_add_left]
  map_smul' c u := ContinuousLinearMap.ext fun v => by
    rw [RingHom.id_apply, smul_apply, mulLeftL_apply, mulLeftL_apply, mulAux_smul_left]

private theorem mulₗ_apply_apply (hp : (finrank ℝ E : ℝ≥0) < p) (k : ℕ)
    (u v : Wkp mu ⊤ (p : ℝ≥0∞) (k + 1)) : mulₗ hp k u v = mulAux hp k u v := by
  rw [mulₗ, LinearMap.coe_mk, AddHom.coe_mk, mulLeftL_apply]

/-- **Multiplication in `W^{k+1,p}(ℝⁿ)` for `p > n`**, as a bounded bilinear map. The value of
`mulL hp k u v` is the pointwise product of the values of `u` and `v`
(`TauCeti.Wkp.value_mulL_ae`), and this determines it (`TauCeti.Wkp.eq_mulL_iff`). -/
def mulL (hp : (finrank ℝ E : ℝ≥0) < p) (k : ℕ) :
    Wkp mu ⊤ (p : ℝ≥0∞) (k + 1) →L[ℝ]
      Wkp mu ⊤ (p : ℝ≥0∞) (k + 1) →L[ℝ] Wkp mu ⊤ (p : ℝ≥0∞) (k + 1) :=
  ContinuousLinearMap.ofSeqClosedGraph (g := mulₗ hp k) fun u x T hu hT => by
    refine ContinuousLinearMap.ext fun v => ext (k + 1) (tendsto_nhds_unique
      (f := fun n => value (k + 1) (mulAux hp k (u n) v)) (l := atTop) ?_ ?_)
    · -- Evaluation at `v` is continuous, so `u n * v → T v`.
      refine tendsto_value ((((ContinuousLinearMap.apply ℝ _ v).continuous.tendsto T).comp
        hT).congr fun n => ?_)
      rw [Function.comp_apply, Function.comp_apply, ContinuousLinearMap.apply_apply,
        mulₗ_apply_apply]
    · -- Multiplication by `v` is continuous, so `u n * v → x * v`.
      rw [mulₗ_apply_apply]
      simpa only [mulAux_comm hp k v] using tendsto_value_mulAux hp k v hu

private theorem mulL_apply_apply (hp : (finrank ℝ E : ℝ≥0) < p) (k : ℕ)
    (u v : Wkp mu ⊤ (p : ℝ≥0∞) (k + 1)) : mulL hp k u v = mulAux hp k u v := by
  rw [mulL, ContinuousLinearMap.coeFn_ofSeqClosedGraph, mulₗ_apply_apply]

/-- The value of the product `mulL hp k u v` is the pointwise product of the values. -/
theorem value_mulL_ae (hp : (finrank ℝ E : ℝ≥0) < p) (k : ℕ)
    (u v : Wkp mu ⊤ (p : ℝ≥0∞) (k + 1)) :
    (value (k + 1) (mulL hp k u v) : E → ℝ) =ᵐ[mu]
      fun x => value (k + 1) u x * value (k + 1) v x := by
  rw [mulL_apply_apply]
  exact value_mulAux hp k u v

/-- The product `mulL hp k u v` is the unique element of `W^{k+1,p}(ℝⁿ)` whose value is the
pointwise product of the values of `u` and `v`. -/
theorem eq_mulL_iff (hp : (finrank ℝ E : ℝ≥0) < p) {k : ℕ}
    {u v w : Wkp mu ⊤ (p : ℝ≥0∞) (k + 1)} :
    w = mulL hp k u v ↔
      (value (k + 1) w : E → ℝ) =ᵐ[mu] fun x => value (k + 1) u x * value (k + 1) v x := by
  rw [mulL_apply_apply]
  exact eq_mulAux_iff hp

/-- Multiplication in `W^{k+1,p}(ℝⁿ)` is commutative. -/
theorem mulL_comm (hp : (finrank ℝ E : ℝ≥0) < p) (k : ℕ) (u v : Wkp mu ⊤ (p : ℝ≥0∞) (k + 1)) :
    mulL hp k u v = mulL hp k v u := by
  rw [mulL_apply_apply, mulL_apply_apply]
  exact mulAux_comm hp k u v

/-- Multiplication in `W^{k+1,p}(ℝⁿ)` is associative. -/
theorem mulL_assoc (hp : (finrank ℝ E : ℝ≥0) < p) (k : ℕ)
    (u v w : Wkp mu ⊤ (p : ℝ≥0∞) (k + 1)) :
    mulL hp k (mulL hp k u v) w = mulL hp k u (mulL hp k v w) := by
  refine (eq_mulL_iff hp).2 ?_
  filter_upwards [value_mulL_ae hp k (mulL hp k u v) w, value_mulL_ae hp k u v,
    value_mulL_ae hp k v w] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, mul_assoc]

/-- Forgetting the highest derivative commutes with multiplication. -/
theorem lowerOrder_mulL (hp : (finrank ℝ E : ℝ≥0) < p) (k : ℕ)
    (u v : Wkp mu ⊤ (p : ℝ≥0∞) (k + 2)) :
    lowerOrder (k + 1) (mulL hp (k + 1) u v) =
      mulL hp k (lowerOrder (k + 1) u) (lowerOrder (k + 1) v) := by
  refine (eq_mulL_iff hp).2 ?_
  simpa only [← value_succ] using value_mulL_ae hp (k + 1) u v

/-- The first-order part of a product in `W^{k+1,p}(ℝⁿ)` is the product `TauCeti.W1p.mul` of the
first-order parts. -/
theorem firstOrder_mulL (hp : (finrank ℝ E : ℝ≥0) < p) (k : ℕ)
    (u v : Wkp mu ⊤ (p : ℝ≥0∞) (k + 1)) :
    firstOrder k (mulL hp k u v) = W1p.mul hp (firstOrder k u) (firstOrder k v) := by
  refine W1p.ext_value (Lp.ext ?_)
  rw [EventuallyEq, Measure.ae_restrict_coe_opens_top, value_firstOrder]
  filter_upwards [value_mulL_ae hp k u v, W1p.value_mul_ae hp (firstOrder k u) (firstOrder k v),
    value_ae_eq_morreyRepresentative hp u, value_ae_eq_morreyRepresentative hp v]
    with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]

end Wkp

end TauCeti
