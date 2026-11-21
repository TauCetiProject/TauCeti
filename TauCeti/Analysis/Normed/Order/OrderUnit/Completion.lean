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
* `TauCeti.OrderUnitCompletion.coe`: the canonical dense linear isometry
  `E →ₗᵢ[ℝ] OrderUnitCompletion he` preserving and reflecting order (an embedding when `E` is
  separated).
* `TauCeti.OrderUnitCompletion.extend`: the unique continuous linear extension of a bounded real
  linear map `E →L[ℝ] F` into a complete space `F`.

## Main results

* `TauCeti.OrderUnitCompletion.coe_le_coe_iff`: `coe he` preserves and reflects order (forming
  an order embedding when `E` is separated).
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
  let C : Set (UniformSpace.Completion E) :=
    ((↑) : E → UniformSpace.Completion E) '' {a : E | 0 ≤ a}
  let halfDiff : UniformSpace.Completion E × UniformSpace.Completion E →
      UniformSpace.Completion E := fun p => (2⁻¹ : ℝ) • (p.1 - p.2)
  let halfSum : UniformSpace.Completion E × UniformSpace.Completion E →
      UniformSpace.Completion E := fun p => (2⁻¹ : ℝ) • (p.1 + p.2)
  have hhd : Continuous halfDiff := by dsimp only [halfDiff]; fun_prop
  have hhs : Continuous halfSum := by dsimp only [halfSum]; fun_prop
  have hclosed : IsClosed {p : UniformSpace.Completion E × UniformSpace.Completion E |
      ‖halfDiff p‖ ≤ ‖halfSum p‖} :=
    isClosed_le hhd.norm hhs.norm
  have hsub : C ×ˢ C ⊆ {p | ‖halfDiff p‖ ≤ ‖halfSum p‖} := by
    rintro ⟨_, _⟩ ⟨⟨v, hv, rfl⟩, ⟨u, hu, rfl⟩⟩
    simp only [Set.mem_ofPred_eq, halfDiff, halfSum, ← UniformSpace.Completion.coe_sub,
      ← UniformSpace.Completion.coe_add, ← UniformSpace.Completion.coe_smul,
      UniformSpace.Completion.norm_coe]
    refine he.norm_le_of_neg_le_of_le ?_ ?_
    · rw [← sub_nonneg, sub_neg_eq_add, ← smul_add]
      have hsum : (v - u) + (v + u) = (2 : ℝ) • v := by rw [two_smul]; abel
      rw [hsum, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
      exact hv
    · rw [← sub_nonneg, ← smul_sub]
      have hdiff : (v + u) - (v - u) = (2 : ℝ) • u := by rw [two_smul]; abel
      rw [hdiff, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
      exact hu
  have hmem : (x + y, y - x) ∈ closure (C ×ˢ C) := by
    rw [closure_prod_eq]
    exact ⟨h1, h2⟩
  have hineq := closure_minimal hsub hclosed hmem
  have hhalfDiff : halfDiff (x + y, y - x) = x := by
    have hdiff : (x + y) - (y - x) = (2 : ℝ) • x := by rw [two_smul]; abel
    dsimp only [halfDiff]
    rw [hdiff, smul_smul]
    norm_num
  have hhalfSum : halfSum (x + y, y - x) = y := by
    have hsum : (x + y) + (y - x) = (2 : ℝ) • y := by rw [two_smul]; abel
    dsimp only [halfSum]
    rw [hsum, smul_smul]
    norm_num
  rw [Set.mem_ofPred_eq, hhalfDiff, hhalfSum] at hineq
  simpa [y, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, UniformSpace.Completion.norm_coe,
    he.norm_e] using hineq

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

/-- The canonical dense linear isometry `E →ₗᵢ[ℝ] OrderUnitCompletion he` preserving and reflecting
order (an embedding when `E` is separated). -/
def coe (he : IsOrderUnitNorm e) : E →ₗᵢ[ℝ] OrderUnitCompletion he :=
  (toCompletionₗᵢ he).symm.toLinearIsometry.comp (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℝ))

@[simp]
theorem toCompletion_coe (a : E) : (coe he a).toCompletion = (a : UniformSpace.Completion E) :=
  (rfl)

/-- The canonical linear isometry `coe he : E →ₗᵢ[ℝ] OrderUnitCompletion he` has dense range. -/
theorem denseRange_coe (he : IsOrderUnitNorm e) : DenseRange (coe he) :=
  (toCompletionₗᵢ he).symm.toHomeomorph.surjective.denseRange.comp
    UniformSpace.Completion.denseRange_coe (toCompletionₗᵢ he).symm.continuous

/-- The canonical linear isometry `coe he` preserves and reflects order (forming an order embedding
when `E` is separated): `coe he a ≤ coe he b ↔ a ≤ b`. -/
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
  let f : UniformSpace.Completion E → UniformSpace.Completion E :=
    fun z => ‖z‖ • (e : UniformSpace.Completion E) - z
  have hf : Continuous f :=
    (continuous_norm.smul continuous_const).sub continuous_id
  have hsub : Set.range ((↑) : E → UniformSpace.Completion E) ⊆
      f ⁻¹' closure (((↑) : E → UniformSpace.Completion E) '' {a : E | 0 ≤ a}) := by
    rintro _ ⟨a, rfl⟩
    refine subset_closure ⟨‖a‖ • e - a, sub_nonneg.mpr (he.le_norm_smul a), ?_⟩
    simp [f, UniformSpace.Completion.norm_coe, UniformSpace.Completion.coe_sub,
      UniformSpace.Completion.coe_smul]
  have hx : x.toCompletion ∈ closure (Set.range ((↑) : E → UniformSpace.Completion E)) :=
    UniformSpace.Completion.denseRange_coe x.toCompletion
  exact closure_minimal hsub (isClosed_closure.preimage hf) hx

/-- The order-unit norm on `OrderUnitCompletion he` satisfies `IsOrderUnitNorm (coe he e)`. -/
theorem isOrderUnitNorm (he : IsOrderUnitNorm e) : IsOrderUnitNorm (coe he e) where
  norm_e := by rw [(coe he).norm_map, he.norm_e]
  norm_le_iff x r hr := by
    refine ⟨fun hx => ?_, fun ⟨h1, h2⟩ => ?_⟩
    · have hupper : ∀ y : OrderUnitCompletion he, ‖y‖ ≤ r → y ≤ r • coe he e := by
        intro y hy
        have hnonneg : (0 : OrderUnitCompletion he) ≤ (r - ‖y‖) • coe he e := by
          rw [← (coe he).map_zero, ← (coe he).map_smul, coe_le_coe_iff]
          exact he.smul_nonneg_of_nonneg (sub_nonneg.mpr hy)
        calc y ≤ ‖y‖ • coe he e := le_norm_smul_coe y
          _ ≤ ‖y‖ • coe he e + (r - ‖y‖) • coe he e := le_add_of_nonneg_right hnonneg
          _ = r • coe he e := by rw [← add_smul, add_sub_cancel]
      refine ⟨?_, hupper x hx⟩
      rw [neg_smul]
      exact neg_le.mp (hupper (-x) (by simpa [norm_neg] using hx))
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
    have hclosed : IsClosed {z : OrderUnitCompletion he | ‖extend he T z‖ ≤ ‖T‖ * ‖z‖} :=
      isClosed_le (extend he T).continuous.norm (continuous_const.mul continuous_norm)
    have hsub : Set.range (coe he) ⊆
        {z : OrderUnitCompletion he | ‖extend he T z‖ ≤ ‖T‖ * ‖z‖} := by
      rintro _ ⟨a, rfl⟩
      simpa [extend_coe, (coe he).norm_map] using T.le_opNorm a
    exact closure_minimal hsub hclosed ((denseRange_coe he) x)
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
      closure (((↑) : E → UniformSpace.Completion E) '' {a : E | 0 ≤ a}) := by
    rw [toCompletion_sub]
    exact (le_iff x y).mp hxy
  have hclosed : IsClosed {z : UniformSpace.Completion E |
      0 ≤ extend he T ((toCompletionₗᵢ he).symm z)} :=
    isClosed_Ici.preimage ((extend he T).continuous.comp (toCompletionₗᵢ he).symm.continuous)
  have hsub : ((↑) : E → UniformSpace.Completion E) '' {a : E | 0 ≤ a} ⊆
      {z : UniformSpace.Completion E | 0 ≤ extend he T ((toCompletionₗᵢ he).symm z)} := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Set.mem_ofPred_eq, ← toCompletion_coe (he := he) a, ← toCompletionₗᵢ_apply,
      (toCompletionₗᵢ he).symm_apply_apply, extend_coe]
    simpa only [map_zero] using hT ha
  simpa only [Set.mem_ofPred_eq, ← toCompletionₗᵢ_apply, (toCompletionₗᵢ he).symm_apply_apply]
    using closure_minimal hsub hclosed hcone

end OrderUnitCompletion

end TauCeti
