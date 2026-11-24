/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Multiplication in `W^{k,p}(Ω)` from closure under products

Suppose that `W^{k,p}(Ω)` is closed under pointwise multiplication, in the sense that for any
two of its elements some third element has as value the pointwise product of their values, and
that the value of each of its elements is essentially bounded. Then multiplication on
`W^{k,p}(Ω)` is a bounded bilinear map (`TauCeti.Wkp.bilinOfAeMul`), which is commutative and
associative.

The product of `u` and `w` is unique, since an element of `W^{k,p}(Ω)` is determined by its value.
It is bilinear because the pointwise product is. Boundedness comes from the closed graph theorem,
applied in each variable in turn: if the value of `u` is bounded by `C`, the value of the product
`u w` has `Lᵖ` norm at most `C ‖w‖`, so it depends continuously on `w`.

## Main declarations

* `TauCeti.Wkp.bilinOfAeMul`: multiplication on `W^{k,p}(Ω)` as a bounded bilinear map,
  characterized by `TauCeti.Wkp.value_bilinOfAeMul_ae` and `TauCeti.Wkp.eq_bilinOfAeMul_iff`.
* `TauCeti.Wkp.bilinOfAeMul_comm`, `TauCeti.Wkp.bilinOfAeMul_assoc`: the product is commutative
  and associative.

The closed-graph construction is that of Tau Ceti contribution
[#1135](https://git.taucetiproject.org/TauCetiProject/TauCeti/pulls/1135),
*multiplication in `W^{k,p}(ℝⁿ)` for `p > n` at every order*.
-/

public section

noncomputable section

open Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace TauCeti

namespace Wkp

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}
  {h : ∀ u w : Wkp mu Omega p k, ∃ z : Wkp mu Omega p k,
    (value k z : E → ℝ) =ᵐ[mu.restrict Omega] fun x => value k u x * value k w x}
  {hb : ∀ u : Wkp mu Omega p k, ∃ C : ℝ, ∀ᵐ x ∂mu.restrict Omega, ‖value k u x‖ ≤ C}

variable (h) in
/-- A chosen product `u w` in `W^{k,p}(Ω)`; see `TauCeti.Wkp.bilinOfAeMul`. -/
private def mulAux (u w : Wkp mu Omega p k) : Wkp mu Omega p k :=
  (h u w).choose

private theorem value_mulAux (u w : Wkp mu Omega p k) :
    (value k (mulAux h u w) : E → ℝ) =ᵐ[mu.restrict Omega]
      fun x => value k u x * value k w x :=
  (h u w).choose_spec

private theorem eq_mulAux_iff {u w z : Wkp mu Omega p k} :
    z = mulAux h u w ↔
      (value k z : E → ℝ) =ᵐ[mu.restrict Omega] fun x => value k u x * value k w x :=
  ⟨fun hz => hz ▸ value_mulAux u w,
    fun hz => ext k (Lp.ext (hz.trans (value_mulAux u w).symm))⟩

private theorem mulAux_comm (u w : Wkp mu Omega p k) : mulAux h u w = mulAux h w u := by
  refine eq_mulAux_iff.2 ?_
  filter_upwards [value_mulAux (h := h) u w] with x hx
  rw [hx, mul_comm]

private theorem mulAux_add_right (u w z : Wkp mu Omega p k) :
    mulAux h u (w + z) = mulAux h u w + mulAux h u z := by
  refine (eq_mulAux_iff.2 ?_).symm
  filter_upwards [value_add_ae k (mulAux h u w) (mulAux h u z), value_mulAux (h := h) u w,
    value_mulAux (h := h) u z, value_add_ae k w z] with x h₁ h₂ h₃ h₄
  rw [h₁, Pi.add_apply, h₂, h₃, h₄, Pi.add_apply, mul_add]

private theorem mulAux_smul_right (c : ℝ) (u w : Wkp mu Omega p k) :
    mulAux h u (c • w) = c • mulAux h u w := by
  refine (eq_mulAux_iff.2 ?_).symm
  filter_upwards [value_smul_ae k c (mulAux h u w), value_mulAux (h := h) u w,
    value_smul_ae k c w] with x h₁ h₂ h₃
  rw [h₁, Pi.smul_apply, h₂, h₃, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm]

private theorem mulAux_sub_right (u w z : Wkp mu Omega p k) :
    mulAux h u (w - z) = mulAux h u w - mulAux h u z :=
  eq_sub_of_add_eq (by rw [← mulAux_add_right, sub_add_cancel])

private theorem mulAux_add_left (u w z : Wkp mu Omega p k) :
    mulAux h (u + w) z = mulAux h u z + mulAux h w z := by
  rw [mulAux_comm, mulAux_add_right, mulAux_comm (h := h) z, mulAux_comm (h := h) z]

private theorem mulAux_smul_left (c : ℝ) (u w : Wkp mu Omega p k) :
    mulAux h (c • u) w = c • mulAux h u w := by
  rw [mulAux_comm, mulAux_smul_right, mulAux_comm (h := h) w]

include hb in
variable (hb) in
/-- If `w n → z` in `W^{k,p}(Ω)`, then the values of the products `u (w n)` converge in `Lᵖ` to
the value of `u z`: if the value of `u` is bounded by `C ≥ 0`, then `‖u w‖ ≤ C ‖w‖`. -/
private theorem tendsto_value_mulAux (u : Wkp mu Omega p k) {w : ℕ → Wkp mu Omega p k}
    {z : Wkp mu Omega p k} (hw : Tendsto w atTop (𝓝 z)) :
    Tendsto (fun n => value k (mulAux h u (w n))) atTop (𝓝 (value k (mulAux h u z))) := by
  obtain ⟨C, hC⟩ := hb u
  have hC' : ∀ᵐ x ∂mu.restrict Omega, ‖value k u x‖ ≤ max C 0 :=
    hC.mono fun x hx => hx.trans (le_max_left C 0)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n => max C 0 * ‖w n - z‖) atTop (𝓝 (max C 0 * 0)) :=
    (tendsto_iff_norm_sub_tendsto_zero.1 hw).const_mul _
  rw [mul_zero] at hlim
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hlim
  rw [← value_sub, ← mulAux_sub_right]
  exact (Lp.norm_le_mul_norm_of_ae_eq_smul hC' (value_mulAux u (w n - z))).trans
    (mul_le_mul_of_nonneg_left (norm_value_le k _) (le_max_right C 0))

variable (h) in
/-- Multiplication by `u`, as a linear map on `W^{k,p}(Ω)`. -/
private def mulLeftₗ (u : Wkp mu Omega p k) : Wkp mu Omega p k →ₗ[ℝ] Wkp mu Omega p k where
  toFun := mulAux h u
  map_add' := mulAux_add_right u
  map_smul' c w := mulAux_smul_right c u w

include hb in
variable (h hb) in
/-- Multiplication by `u`, as a continuous linear map on `W^{k,p}(Ω)`, by the closed graph
theorem: the value of the product depends continuously on the value of the second factor. -/
private def mulLeftL (u : Wkp mu Omega p k) : Wkp mu Omega p k →L[ℝ] Wkp mu Omega p k :=
  ContinuousLinearMap.ofSeqClosedGraph (g := mulLeftₗ h u) fun _ _ _ hw hz =>
    ext k (tendsto_nhds_unique (tendsto_value hz) (tendsto_value_mulAux hb u hw))

private theorem mulLeftL_apply (u w : Wkp mu Omega p k) : mulLeftL h hb u w = mulAux h u w := by
  rw [mulLeftL, ContinuousLinearMap.coeFn_ofSeqClosedGraph, mulLeftₗ, LinearMap.coe_mk,
    AddHom.coe_mk]

variable (h hb) in
/-- Multiplication on `W^{k,p}(Ω)`, as a linear map into continuous linear maps. -/
private def mulₗ : Wkp mu Omega p k →ₗ[ℝ] Wkp mu Omega p k →L[ℝ] Wkp mu Omega p k where
  toFun := mulLeftL h hb
  map_add' u u' := ContinuousLinearMap.ext fun w => by
    rw [add_apply, mulLeftL_apply, mulLeftL_apply, mulLeftL_apply,
      mulAux_add_left]
  map_smul' c u := ContinuousLinearMap.ext fun w => by
    rw [RingHom.id_apply, smul_apply, mulLeftL_apply, mulLeftL_apply,
      mulAux_smul_left]

private theorem mulₗ_apply_apply (u w : Wkp mu Omega p k) : mulₗ h hb u w = mulAux h u w := by
  rw [mulₗ, LinearMap.coe_mk, AddHom.coe_mk, mulLeftL_apply]

variable (k h hb) in
/-- **Multiplication in `W^{k,p}(Ω)`**, as a bounded bilinear map, when `W^{k,p}(Ω)` is closed
under pointwise products (`h`) and the value of each of its elements is essentially bounded
(`hb`). The value of `bilinOfAeMul k h hb u w` is the pointwise product of the values of `u` and
`w` (`TauCeti.Wkp.value_bilinOfAeMul_ae`), and this determines it
(`TauCeti.Wkp.eq_bilinOfAeMul_iff`). -/
def bilinOfAeMul : Wkp mu Omega p k →L[ℝ] Wkp mu Omega p k →L[ℝ] Wkp mu Omega p k :=
  ContinuousLinearMap.ofSeqClosedGraph (g := mulₗ h hb) fun u z T hu hT => by
    refine ContinuousLinearMap.ext fun w => ext k (tendsto_nhds_unique
      (f := fun n => value k (mulAux h (u n) w)) (l := atTop) ?_ ?_)
    · -- Evaluation at `w` is continuous, so `u n * w → T w`.
      refine tendsto_value ((((ContinuousLinearMap.apply ℝ _ w).continuous.tendsto T).comp
        hT).congr fun n => ?_)
      rw [Function.comp_apply, Function.comp_apply, ContinuousLinearMap.apply_apply,
        mulₗ_apply_apply]
    · -- Multiplication by `w` is continuous, so `u n * w → z * w`.
      rw [mulₗ_apply_apply]
      simpa only [mulAux_comm (h := h) w] using tendsto_value_mulAux (h := h) hb w hu

private theorem bilinOfAeMul_apply_apply (u w : Wkp mu Omega p k) :
    bilinOfAeMul k h hb u w = mulAux h u w := by
  rw [bilinOfAeMul, ContinuousLinearMap.coeFn_ofSeqClosedGraph, mulₗ_apply_apply]

/-- The value of the product `bilinOfAeMul k h hb u w` is the pointwise product of the values. -/
theorem value_bilinOfAeMul_ae (u w : Wkp mu Omega p k) :
    (value k (bilinOfAeMul k h hb u w) : E → ℝ) =ᵐ[mu.restrict Omega]
      fun x => value k u x * value k w x := by
  rw [bilinOfAeMul_apply_apply]
  exact value_mulAux u w

/-- The product `bilinOfAeMul k h hb u w` is the unique element of `W^{k,p}(Ω)` whose value is the
pointwise product of the values of `u` and `w`. -/
theorem eq_bilinOfAeMul_iff {u w z : Wkp mu Omega p k} :
    z = bilinOfAeMul k h hb u w ↔
      (value k z : E → ℝ) =ᵐ[mu.restrict Omega] fun x => value k u x * value k w x := by
  rw [bilinOfAeMul_apply_apply]
  exact eq_mulAux_iff

/-- The product `bilinOfAeMul k h hb` is commutative. -/
theorem bilinOfAeMul_comm (u w : Wkp mu Omega p k) :
    bilinOfAeMul k h hb u w = bilinOfAeMul k h hb w u := by
  rw [bilinOfAeMul_apply_apply, bilinOfAeMul_apply_apply]
  exact mulAux_comm u w

/-- The product `bilinOfAeMul k h hb` is associative. -/
theorem bilinOfAeMul_assoc (u w z : Wkp mu Omega p k) :
    bilinOfAeMul k h hb (bilinOfAeMul k h hb u w) z =
      bilinOfAeMul k h hb u (bilinOfAeMul k h hb w z) := by
  refine eq_bilinOfAeMul_iff.2 ?_
  filter_upwards [value_bilinOfAeMul_ae (hb := hb) (bilinOfAeMul k h hb u w) z,
    value_bilinOfAeMul_ae (hb := hb) u w, value_bilinOfAeMul_ae (hb := hb) w z] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, mul_assoc]

end Wkp

end TauCeti
