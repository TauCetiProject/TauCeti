/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Operator.Basic
public import TauCeti.Analysis.Normed.Order.OrderUnit.Basic

/-!
# Completion of an order-unit space

Let `(E, e)` be a real order-unit space with `he : TauCeti.IsOrderUnitNorm e`. Its Banach-space
completion `UniformSpace.Completion E`, equipped with the closure of the image of the positive
cone `{a : E | 0 ≤ a}`, is again a complete order-unit space with the same order unit `e` and the
inherited completion norm.

This file packages that structure as `TauCeti.OrderUnitCompletion he`, keeping the order instances
local to the wrapper type rather than registering a global order on `UniformSpace.Completion`.

## Main definitions

* `TauCeti.OrderUnitCompletion`: the norm completion of an order-unit space equipped with the
  closed positive cone.
* `TauCeti.OrderUnitCompletion.toCompletionₗᵢ`: the canonical linear isometry equivalence onto
  `UniformSpace.Completion E`.
* `TauCeti.OrderUnitCompletion.coe`: the canonical dense linear isometric order embedding
  `E →ₗᵢ[ℝ] OrderUnitCompletion he`.
* `TauCeti.OrderUnitCompletion.extend`: the unique continuous linear extension of a bounded real
  linear map `E →L[ℝ] F` into a complete space `F`.

## Main results

* `TauCeti.OrderUnitCompletion.coe_le_coe_iff`: `coe he` is an order embedding.
* `TauCeti.OrderUnitCompletion.isOrderUnitNorm`: `coe he e` satisfies `IsOrderUnitNorm` on
  `OrderUnitCompletion he`.
* `TauCeti.OrderUnitCompletion.opNorm_extend`: extending a bounded linear map preserves its
  operator norm.
* `TauCeti.OrderUnitCompletion.monotone_extend`: extending a monotone bounded linear map into a
  complete space with closed order preserves monotonicity.

## References

* M. A. Rieffel, *Metrics on state spaces*, Doc. Math. **4** (1999), 559–600, §1.
-/

public section

noncomputable section

open Set Filter Topology

namespace TauCeti

/-- The norm completion of an order-unit space `(E, e)`, equipped with the closure of the image of
the positive cone of `E` as its positive cone. -/
@[ext]
structure OrderUnitCompletion {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [Preorder E] [IsOrderedAddMonoid E] {e : E} (he : IsOrderUnitNorm e) where
  /-- The underlying element of `UniformSpace.Completion E`. -/
  toCompletion : UniformSpace.Completion E

namespace OrderUnitCompletion

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [Preorder E]
  [IsOrderedAddMonoid E] {e : E} {he : IsOrderUnitNorm e}

instance : Zero (OrderUnitCompletion he) := ⟨⟨0⟩⟩
instance : Add (OrderUnitCompletion he) := ⟨fun x y => ⟨x.toCompletion + y.toCompletion⟩⟩
instance : Neg (OrderUnitCompletion he) := ⟨fun x => ⟨-x.toCompletion⟩⟩
instance : Sub (OrderUnitCompletion he) := ⟨fun x y => ⟨x.toCompletion - y.toCompletion⟩⟩
instance : SMul ℕ (OrderUnitCompletion he) := ⟨fun n x => ⟨n • x.toCompletion⟩⟩
instance : SMul ℤ (OrderUnitCompletion he) := ⟨fun n x => ⟨n • x.toCompletion⟩⟩
instance : SMul ℝ (OrderUnitCompletion he) := ⟨fun r x => ⟨r • x.toCompletion⟩⟩

@[simp] theorem toCompletion_zero : (0 : OrderUnitCompletion he).toCompletion = 0 := (rfl)
@[simp] theorem toCompletion_add (x y : OrderUnitCompletion he) :
    (x + y).toCompletion = x.toCompletion + y.toCompletion := (rfl)
@[simp] theorem toCompletion_neg (x : OrderUnitCompletion he) :
    (-x).toCompletion = -x.toCompletion := (rfl)
@[simp] theorem toCompletion_sub (x y : OrderUnitCompletion he) :
    (x - y).toCompletion = x.toCompletion - y.toCompletion := (rfl)
@[simp] theorem toCompletion_smul (r : ℝ) (x : OrderUnitCompletion he) :
    (r • x).toCompletion = r • x.toCompletion := (rfl)

instance : AddCommGroup (OrderUnitCompletion he) :=
  Function.Injective.addCommGroup toCompletion (fun _ _ h => OrderUnitCompletion.ext h)
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance : Module ℝ (OrderUnitCompletion he) :=
  Function.Injective.module ℝ
    { toFun := toCompletion, map_zero' := rfl, map_add' := fun _ _ => rfl }
    (fun _ _ h => OrderUnitCompletion.ext h) (fun _ _ => rfl)

instance : NormedAddCommGroup (OrderUnitCompletion he) :=
  NormedAddCommGroup.induced (OrderUnitCompletion he) (UniformSpace.Completion E)
    ({ toFun := toCompletion, map_zero' := rfl, map_add' := fun _ _ => rfl } :
      OrderUnitCompletion he →+ UniformSpace.Completion E)
    (fun _ _ h => OrderUnitCompletion.ext h)

@[simp]
theorem norm_toCompletion (x : OrderUnitCompletion he) : ‖x.toCompletion‖ = ‖x‖ := (rfl)

instance : NormedSpace ℝ (OrderUnitCompletion he) where
  norm_smul_le r x := by
    rw [← norm_toCompletion (r • x), toCompletion_smul, ← norm_toCompletion x]
    exact norm_smul_le r x.toCompletion

/-- The canonical linear isometry equivalence `OrderUnitCompletion he ≃ₗᵢ[ℝ] Completion E`. -/
def toCompletionₗᵢ (he : IsOrderUnitNorm e) :
    OrderUnitCompletion he ≃ₗᵢ[ℝ] UniformSpace.Completion E where
  toFun := toCompletion
  invFun := mk
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

@[simp]
theorem toCompletionₗᵢ_apply (x : OrderUnitCompletion he) :
    toCompletionₗᵢ he x = x.toCompletion := (rfl)

@[simp]
theorem toCompletionₗᵢ_symm_apply (x : UniformSpace.Completion E) :
    (toCompletionₗᵢ he).symm x = ⟨x⟩ := (rfl)

instance : CompleteSpace (OrderUnitCompletion he) :=
  (completeSpace_congr (e := (toCompletionₗᵢ he).toEquiv)
    (toCompletionₗᵢ he).isometry.isUniformEmbedding).mpr inferInstance

/-- If `r • ↑e + x` and `r • ↑e - x` both lie in the closed positive cone of `Completion E`, then
`‖x‖ ≤ r`. -/
private theorem norm_le_of_mem_closure_nonneg (he : IsOrderUnitNorm e)
    {x : UniformSpace.Completion E} {r : ℝ} (hr : 0 ≤ r)
    (h1 : x + r • (e : UniformSpace.Completion E) ∈
      closure (((↑) : E → UniformSpace.Completion E) '' {a : E | 0 ≤ a}))
    (h2 : r • (e : UniformSpace.Completion E) - x ∈
      closure (((↑) : E → UniformSpace.Completion E) '' {a : E | 0 ≤ a})) : ‖x‖ ≤ r := by
  let y : UniformSpace.Completion E := r • (e : UniformSpace.Completion E)
  obtain ⟨u, hu_mem, hu_lim⟩ := mem_closure_iff_seq_limit.mp h2
  obtain ⟨v, hv_mem, hv_lim⟩ := mem_closure_iff_seq_limit.mp h1
  choose u' hu' hu'_eq using hu_mem
  choose v' hv' hv'_eq using hv_mem
  let a : ℕ → E := fun n => (2⁻¹ : ℝ) • (v' n - u' n)
  let s : ℕ → E := fun n => (2⁻¹ : ℝ) • (v' n + u' n)
  have ha_lim : Tendsto (fun n => (a n : UniformSpace.Completion E)) atTop (𝓝 x) := by
    have h := (hv_lim.sub hu_lim).const_smul (2⁻¹ : ℝ)
    have hmid : (2⁻¹ : ℝ) • ((x + y) - (y - x)) = x := by
      have hdiff : (x + y) - (y - x) = (2 : ℝ) • x := by rw [two_smul]; abel
      rw [hdiff, smul_smul]
      norm_num
    rw [hmid] at h
    exact h.congr fun n => by
      simp [a, hu'_eq n, hv'_eq n, UniformSpace.Completion.coe_smul,
        UniformSpace.Completion.coe_sub]
  have hs_lim : Tendsto (fun n => (s n : UniformSpace.Completion E)) atTop (𝓝 y) := by
    have h := (hv_lim.add hu_lim).const_smul (2⁻¹ : ℝ)
    have hmid : (2⁻¹ : ℝ) • ((x + y) + (y - x)) = y := by
      have hsum : (x + y) + (y - x) = (2 : ℝ) • y := by rw [two_smul]; abel
      rw [hsum, smul_smul]
      norm_num
    rw [hmid] at h
    exact h.congr fun n => by
      simp [s, hu'_eq n, hv'_eq n, UniformSpace.Completion.coe_smul,
        UniformSpace.Completion.coe_add]
  have hle : ∀ n, ‖(a n : UniformSpace.Completion E)‖ ≤ ‖(s n : UniformSpace.Completion E)‖ := by
    intro n
    rw [UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
    refine he.norm_le_of_neg_le_of_le ?_ ?_
    · rw [← sub_nonneg, sub_neg_eq_add]
      have : a n + s n = v' n := by
        simp only [a, s, ← smul_add, sub_add_add_cancel, ← two_smul ℝ, smul_smul]; norm_num
      exact this ▸ hv' n
    · rw [← sub_nonneg]
      have : s n - a n = u' n := by
        simp only [a, s, ← smul_sub, add_sub_sub_cancel, ← two_smul ℝ, smul_smul]; norm_num
      exact this ▸ hu' n
  have hnorm_lim := le_of_tendsto_of_tendsto ha_lim.norm hs_lim.norm (Eventually.of_forall hle)
  simpa [y, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, UniformSpace.Completion.norm_coe,
    he.norm_e] using hnorm_lim

instance : PartialOrder (OrderUnitCompletion he) where
  le x y := y.toCompletion - x.toCompletion ∈
    closure (((↑) : E → UniformSpace.Completion E) '' {a : E | 0 ≤ a})
  le_refl x := by
    have h0 : (0 : UniformSpace.Completion E) ∈
        closure (((↑) : E → UniformSpace.Completion E) '' {a : E | 0 ≤ a}) :=
      subset_closure ⟨0, le_rfl, UniformSpace.Completion.coe_zero⟩
    simpa using h0
  le_trans x y z hxy hyz := by
    have hmem : (z.toCompletion - y.toCompletion, y.toCompletion - x.toCompletion) ∈
        closure ((((↑) : E → UniformSpace.Completion E) '' {a : E | 0 ≤ a}) ×ˢ
          (((↑) : E → UniformSpace.Completion E) '' {a : E | 0 ≤ a})) := by
      rw [closure_prod_eq]
      exact ⟨hyz, hxy⟩
    have himg := image_closure_subset_closure_image continuous_add ⟨_, hmem, rfl⟩
    have hadd : (z.toCompletion - y.toCompletion) + (y.toCompletion - x.toCompletion) ∈
        closure (((↑) : E → UniformSpace.Completion E) '' {a : E | 0 ≤ a}) := by
      refine closure_minimal ?_ isClosed_closure himg
      rintro _ ⟨⟨_, _⟩, ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, rfl⟩
      exact subset_closure ⟨a + b, add_nonneg ha hb, UniformSpace.Completion.coe_add a b⟩
    rwa [sub_add_sub_cancel] at hadd
  le_antisymm x y hxy hyx := by
    have hnorm : ‖y.toCompletion - x.toCompletion‖ ≤ 0 :=
      norm_le_of_mem_closure_nonneg he le_rfl (by simpa using hxy) (by simpa using hyx)
    exact OrderUnitCompletion.ext (sub_eq_zero.mp (norm_le_zero_iff.mp hnorm)).symm

theorem le_iff (x y : OrderUnitCompletion he) :
    x ≤ y ↔ y.toCompletion - x.toCompletion ∈
      closure (((↑) : E → UniformSpace.Completion E) '' {a : E | 0 ≤ a}) := Iff.rfl

instance : IsOrderedAddMonoid (OrderUnitCompletion he) where
  add_le_add_left x y h z := by
    rw [le_iff] at h ⊢
    simpa [add_sub_add_left_eq_sub] using h

/-- The canonical linear isometric embedding `E →ₗᵢ[ℝ] OrderUnitCompletion he`. -/
def coe (he : IsOrderUnitNorm e) : E →ₗᵢ[ℝ] OrderUnitCompletion he :=
  (toCompletionₗᵢ he).symm.toLinearIsometry.comp (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℝ))

@[simp]
theorem toCompletion_coe (a : E) : (coe he a).toCompletion = (a : UniformSpace.Completion E) :=
  (rfl)

/-- The canonical embedding `coe he : E →ₗᵢ[ℝ] OrderUnitCompletion he` has dense range. -/
theorem denseRange_coe (he : IsOrderUnitNorm e) : DenseRange (coe he) :=
  (toCompletionₗᵢ he).symm.toHomeomorph.surjective.denseRange.comp
    UniformSpace.Completion.denseRange_coe (toCompletionₗᵢ he).symm.continuous

/-- The canonical embedding `coe he` preserves and reflects the order:
`coe he a ≤ coe he b ↔ a ≤ b`. -/
@[simp]
theorem coe_le_coe_iff (a b : E) : coe he a ≤ coe he b ↔ a ≤ b := by
  rw [le_iff, toCompletion_coe, toCompletion_coe, ← UniformSpace.Completion.coe_sub]
  have hind := (UniformSpace.Completion.isDenseInducing_coe (α := E)).isInducing
  have hcl := hind.closure_eq_preimage_closure_image {c : E | 0 ≤ c}
  rw [he.isClosed_nonneg.closure_eq] at hcl
  rw [← Set.mem_preimage (f := ((↑) : E → UniformSpace.Completion E)), ← hcl]
  simp [sub_nonneg]

private theorem le_norm_smul_coe (x : OrderUnitCompletion he) : x ≤ ‖x‖ • coe he e := by
  rw [le_iff, toCompletion_smul, toCompletion_coe, ← norm_toCompletion]
  have hy : x.toCompletion ∈ closure (Set.range ((↑) : E → UniformSpace.Completion E)) :=
    UniformSpace.Completion.denseRange_coe x.toCompletion
  obtain ⟨u, hu_mem, hu_lim⟩ := mem_closure_iff_seq_limit.mp hy
  choose a ha using hu_mem
  have hnorm : Tendsto (fun n => ‖a n‖) atTop (𝓝 ‖x.toCompletion‖) := by
    refine hu_lim.norm.congr fun n => ?_
    rw [← ha n, UniformSpace.Completion.norm_coe]
  have hlim : Tendsto (fun n => (((‖a n‖ • e - a n : E) : UniformSpace.Completion E)))
      atTop (𝓝 (‖x.toCompletion‖ • (e : UniformSpace.Completion E) - x.toCompletion)) := by
    have hsub := (hnorm.smul_const (e : UniformSpace.Completion E)).sub
      (hu_lim.congr fun n => (ha n).symm)
    refine hsub.congr fun n => ?_
    simp [UniformSpace.Completion.coe_sub, UniformSpace.Completion.coe_smul]
  refine mem_closure_of_tendsto hlim (Eventually.of_forall fun n => ?_)
  exact ⟨‖a n‖ • e - a n, sub_nonneg.mpr (he.le_norm_smul (a n)), rfl⟩

/-- The order-unit norm on `OrderUnitCompletion he` satisfies `IsOrderUnitNorm (coe he e)`. -/
theorem isOrderUnitNorm (he : IsOrderUnitNorm e) : IsOrderUnitNorm (coe he e) where
  norm_e := by rw [(coe he).norm_map, he.norm_e]
  norm_le_iff x r hr := by
    refine ⟨fun hx => ?_, fun ⟨h1, h2⟩ => ?_⟩
    · have hnonneg : (0 : OrderUnitCompletion he) ≤ (r - ‖x‖) • coe he e := by
        rw [← (coe he).map_zero, ← (coe he).map_smul, coe_le_coe_iff]
        exact he.smul_nonneg_of_nonneg (sub_nonneg.mpr hx)
      have hupper : x ≤ r • coe he e := by
        calc x ≤ ‖x‖ • coe he e := le_norm_smul_coe x
          _ ≤ ‖x‖ • coe he e + (r - ‖x‖) • coe he e := le_add_of_nonneg_right hnonneg
          _ = r • coe he e := by rw [← add_smul, add_sub_cancel]
      have hlower : -r • coe he e ≤ x := by
        have hneg : -x ≤ r • coe he e := by
          calc -x ≤ ‖-x‖ • coe he e := le_norm_smul_coe (-x)
            _ = ‖x‖ • coe he e := by rw [norm_neg]
            _ ≤ ‖x‖ • coe he e + (r - ‖x‖) • coe he e := le_add_of_nonneg_right hnonneg
            _ = r • coe he e := by rw [← add_smul, add_sub_cancel]
        rw [neg_smul]
        exact neg_le.mp hneg
      exact ⟨hlower, hupper⟩
    · rw [← norm_toCompletion]
      refine norm_le_of_mem_closure_nonneg he hr ?_ ?_
      · simpa [le_iff, neg_smul, sub_neg_eq_add] using h1
      · simpa [le_iff] using h2

instance : PosSMulMono ℝ (OrderUnitCompletion he) :=
  (isOrderUnitNorm he).posSMulMono

instance : OrderClosedTopology (OrderUnitCompletion he) :=
  (isOrderUnitNorm he).orderClosedTopology

/-- Continuous linear extension of a bounded real linear map `E →L[ℝ] F` to
`OrderUnitCompletion he`, when `F` is complete. -/
def extend (he : IsOrderUnitNorm e) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (T : E →L[ℝ] F) : OrderUnitCompletion he →L[ℝ] F :=
  (T.extend (UniformSpace.Completion.toComplL : E →L[ℝ] UniformSpace.Completion E)).comp
    (toCompletionₗᵢ he).toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
theorem extend_coe {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (T : E →L[ℝ] F) (a : E) : extend he T (coe he a) = T a := by
  rw [extend, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, toCompletionₗᵢ_apply, toCompletion_coe,
    ← UniformSpace.Completion.coe_toComplL (S := ℝ)]
  exact ContinuousLinearMap.extend_eq T UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe E) a

/-- Uniqueness of continuous linear extension: any continuous linear map
`S : OrderUnitCompletion he →L[ℝ] F` agreeing with `T` on `coe he` equals `extend he T`. -/
theorem extend_unique {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (T : E →L[ℝ] F) {S : OrderUnitCompletion he →L[ℝ] F}
    (hS : ∀ a : E, S (coe he a) = T a) : S = extend he T := by
  ext x
  exact congr_fun (DenseRange.equalizer (denseRange_coe he) S.continuous (extend he T).continuous
    (funext fun a => (hS a).trans (extend_coe T a).symm)) x

/-- Continuous linear extension to `OrderUnitCompletion he` preserves the operator norm:
`‖extend he T‖ = ‖T‖`. -/
theorem opNorm_extend {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (T : E →L[ℝ] F) : ‖extend he T‖ = ‖T‖ := by
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) fun x => ?_
    obtain ⟨u, hu_mem, hu_lim⟩ := mem_closure_iff_seq_limit.mp (denseRange_coe he x)
    choose a ha using hu_mem
    have hlim : Tendsto (fun n => coe he (a n)) atTop (𝓝 x) :=
      hu_lim.congr fun n => (ha n).symm
    refine le_of_tendsto_of_tendsto (((extend he T).continuous.tendsto x).comp hlim).norm
      (hlim.norm.const_mul ‖T‖) (Eventually.of_forall fun n => ?_)
    simp only [Function.comp_apply, extend_coe, (coe he).norm_map]
    exact T.le_opNorm (a n)
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun a => ?_
    calc ‖T a‖ = ‖extend he T (coe he a)‖ := by rw [extend_coe]
      _ ≤ ‖extend he T‖ * ‖coe he a‖ := (extend he T).le_opNorm _
      _ = ‖extend he T‖ * ‖a‖ := by rw [(coe he).norm_map]

/-- The continuous extension of a monotone continuous linear map into a complete space with closed
order is again monotone. -/
theorem monotone_extend {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [Preorder F] [IsOrderedAddMonoid F] [OrderClosedTopology F]
    {T : E →L[ℝ] F} (hT : Monotone T) : Monotone (extend he T) := by
  intro x y hxy
  rw [← sub_nonneg, ← map_sub]
  have hcone : (y - x).toCompletion ∈
      closure (((↑) : E → UniformSpace.Completion E) '' {a : E | 0 ≤ a}) := hxy
  obtain ⟨u, hu_mem, hu_lim⟩ := mem_closure_iff_seq_limit.mp hcone
  choose a ha ha_eq using hu_mem
  have hlim : Tendsto (fun n => coe he (a n)) atTop (𝓝 (y - x)) := by
    have hcont := (toCompletionₗᵢ he).symm.continuous.tendsto (y - x).toCompletion
    have h1 := hcont.comp (hu_lim.congr fun n => (ha_eq n).symm)
    have htarget : (toCompletionₗᵢ he).symm (y - x).toCompletion = y - x := rfl
    rw [htarget] at h1
    exact h1.congr fun _ => rfl
  have hTlim : Tendsto (fun n => T (a n)) atTop (𝓝 (extend he T (y - x))) :=
    (((extend he T).continuous.tendsto (y - x)).comp hlim).congr fun n => extend_coe T (a n)
  exact ge_of_tendsto' hTlim fun n => by
    simpa only [map_zero] using hT (ha n)

end OrderUnitCompletion

end TauCeti
