/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Operator.Basic
public import TauCeti.Analysis.Normed.Order.OrderUnit.Basic
import Mathlib.Analysis.Normed.Operator.Extend

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

* `TauCeti.OrderUnitCompletion.le_iff`: characterizes `x ≤ y` for arbitrary elements of
  `OrderUnitCompletion he` as membership of `y.toCompletion - x.toCompletion` in the closure of
  the embedded positive cone.
* `TauCeti.OrderUnitCompletion.coe_le_coe_iff`: `coe he` preserves and reflects order on embedded
  elements from `E` (forming an order embedding when `E` is separated).
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

/-- The closed positive cone in `OrderUnitCompletion he`, formed as the topological closure of the
image of `AddSubmonoid.nonneg E` under `coe he`. -/
def closedNonnegCone (he : IsOrderUnitNorm e) : AddSubmonoid (OrderUnitCompletion he) :=
  ((AddSubmonoid.nonneg E).map (coe he).toAddMonoidHom).topologicalClosure

private theorem mem_closedNonnegCone_iff {x : OrderUnitCompletion he} :
    x ∈ closedNonnegCone he ↔ x ∈ closure (coe he '' {a : E | 0 ≤ a}) := by
  rw [closedNonnegCone, ← SetLike.mem_coe, AddSubmonoid.coe_topologicalClosure,
    AddSubmonoid.coe_map, AddSubmonoid.coe_nonneg]
  rfl

private theorem coe_mem_closedNonnegCone {a : E} (ha : 0 ≤ a) :
    coe he a ∈ closedNonnegCone he :=
  AddSubmonoid.le_topologicalClosure _ (AddSubmonoid.mem_map.mpr ⟨a, ha, rfl⟩)

private theorem norm_sub_le_norm_add_of_nonneg (he : IsOrderUnitNorm e)
    {v u : E} (hv : 0 ≤ v) (hu : 0 ≤ u) : ‖v - u‖ ≤ ‖v + u‖ := by
  refine he.norm_le_of_neg_le_of_le ?_ ?_
  · rw [neg_add, sub_eq_add_neg]
    exact add_le_add ((neg_nonpos.mpr hv).trans hv) le_rfl
  · rw [sub_eq_add_neg]
    exact add_le_add le_rfl ((neg_nonpos.mpr hu).trans hu)

private theorem norm_sub_le_norm_add_of_mem_closedNonnegCone (he : IsOrderUnitNorm e)
    {v u : OrderUnitCompletion he}
    (hv : v ∈ closedNonnegCone he) (hu : u ∈ closedNonnegCone he) :
    ‖v - u‖ ≤ ‖v + u‖ := by
  let C : Set (OrderUnitCompletion he) := coe he '' {a : E | 0 ≤ a}
  have hclosed : IsClosed {p : OrderUnitCompletion he × OrderUnitCompletion he |
      ‖p.1 - p.2‖ ≤ ‖p.1 + p.2‖} :=
    isClosed_le (continuous_fst.sub continuous_snd).norm
      (continuous_fst.add continuous_snd).norm
  have hsub : C ×ˢ C ⊆ {p | ‖p.1 - p.2‖ ≤ ‖p.1 + p.2‖} := by
    rintro ⟨_, _⟩ ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩
    simp only [Set.mem_ofPred_eq, ← map_sub, ← map_add, (coe he).norm_map]
    exact norm_sub_le_norm_add_of_nonneg he ha hb
  have hmem : (v, u) ∈ closure (C ×ˢ C) := by
    rw [closure_prod_eq]
    exact ⟨mem_closedNonnegCone_iff.mp hv, mem_closedNonnegCone_iff.mp hu⟩
  exact closure_minimal hsub hclosed hmem

private theorem eq_zero_of_mem_closedNonnegCone_of_neg_mem (he : IsOrderUnitNorm e)
    {z : OrderUnitCompletion he}
    (hz : z ∈ closedNonnegCone he) (hneg : -z ∈ closedNonnegCone he) :
    z = 0 := by
  have hineq := norm_sub_le_norm_add_of_mem_closedNonnegCone he hz hneg
  rw [sub_neg_eq_add, ← two_smul ℝ z, add_neg_cancel, norm_zero, norm_smul, Real.norm_eq_abs,
    abs_of_pos zero_lt_two] at hineq
  exact norm_eq_zero.mp (le_antisymm (by linarith) (norm_nonneg z))

/-- If `x + r • coe he e` and `r • coe he e - x` both lie in the closed positive cone of
`OrderUnitCompletion he`, then `‖x‖ ≤ r`. -/
private theorem norm_le_of_mem_closedNonnegCone (he : IsOrderUnitNorm e)
    {x : OrderUnitCompletion he} {r : ℝ} (hr : 0 ≤ r)
    (h1 : x + r • coe he e ∈ closedNonnegCone he)
    (h2 : r • coe he e - x ∈ closedNonnegCone he) : ‖x‖ ≤ r := by
  let y : OrderUnitCompletion he := r • coe he e
  have hineq := norm_sub_le_norm_add_of_mem_closedNonnegCone he h1 h2
  have hdiff : (x + y) - (y - x) = (2 : ℝ) • x := by rw [two_smul]; abel
  have hsum : (x + y) + (y - x) = (2 : ℝ) • y := by rw [two_smul]; abel
  rw [hdiff, hsum, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos zero_lt_two] at hineq
  have hy : ‖y‖ = r := by
    simp [y, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, (coe he).norm_map, he.norm_e]
  linarith

instance : PartialOrder (OrderUnitCompletion he) where
  le x y := y - x ∈ closedNonnegCone he
  le_refl x := by
    rw [sub_self]
    exact (closedNonnegCone he).zero_mem
  le_trans x y z hxy hyz := by
    rw [← sub_add_sub_cancel z y x]
    exact (closedNonnegCone he).add_mem hyz hxy
  le_antisymm x y hxy hyx := by
    have hneg : -(y - x) ∈ closedNonnegCone he := by
      rw [neg_sub]
      exact hyx
    exact (sub_eq_zero.mp (eq_zero_of_mem_closedNonnegCone_of_neg_mem he hxy hneg)).symm

private theorem le_iff_mem_closedNonnegCone (x y : OrderUnitCompletion he) :
    x ≤ y ↔ y - x ∈ closedNonnegCone he := Iff.rfl

/-- Order characterization on arbitrary elements of `OrderUnitCompletion he`: `x ≤ y` if and
only if `y.toCompletion - x.toCompletion` belongs to the closure of the image of the positive cone
of `E`. -/
theorem le_iff (x y : OrderUnitCompletion he) :
    x ≤ y ↔ y.toCompletion - x.toCompletion ∈
      closure (((↑) : E → UniformSpace.Completion E) '' {a : E | 0 ≤ a}) := by
  rw [le_iff_mem_closedNonnegCone, mem_closedNonnegCone_iff]
  have himg : (toCompletionₗᵢ he).toHomeomorph '' (coe he '' {a : E | 0 ≤ a}) =
      (((↑) : E → UniformSpace.Completion E) '' {a : E | 0 ≤ a}) := by
    ext z
    simp [toCompletion_coe]
  rw [← himg, ← Homeomorph.image_closure,
    ← (toCompletionₗᵢ he).toHomeomorph.injective.mem_set_image]
  rfl

instance : IsOrderedAddMonoid (OrderUnitCompletion he) where
  add_le_add_left x y h z := by
    rw [le_iff_mem_closedNonnegCone] at h ⊢
    simpa [add_sub_add_left_eq_sub] using h

/-- The canonical linear isometry `coe he` preserves and reflects order (forming an order embedding
when `E` is separated): `coe he a ≤ coe he b ↔ a ≤ b`. -/
@[simp]
theorem coe_le_coe_iff (a b : E) : coe he a ≤ coe he b ↔ a ≤ b := by
  rw [le_iff_mem_closedNonnegCone, ← map_sub, mem_closedNonnegCone_iff]
  have hind := (Isometry.isUniformInducing (coe he).isometry).isInducing
  have hcl := hind.closure_eq_preimage_closure_image {c : E | 0 ≤ c}
  rw [he.isClosed_nonneg.closure_eq] at hcl
  rw [← Set.mem_preimage (f := coe he), ← hcl]
  simp [sub_nonneg]

private theorem le_norm_smul_coe (x : OrderUnitCompletion he) : x ≤ ‖x‖ • coe he e := by
  rw [le_iff_mem_closedNonnegCone]
  let f : OrderUnitCompletion he → OrderUnitCompletion he := fun z => ‖z‖ • coe he e - z
  have hf : Continuous f :=
    (continuous_norm.smul continuous_const).sub continuous_id
  have hsub : Set.range (coe he) ⊆ f ⁻¹' (closedNonnegCone he : Set (OrderUnitCompletion he)) := by
    rintro _ ⟨a, rfl⟩
    have hmem : coe he (‖a‖ • e - a) ∈ closedNonnegCone he :=
      coe_mem_closedNonnegCone (sub_nonneg.mpr (he.le_norm_smul a))
    simpa [f, (coe he).norm_map] using hmem
  exact closure_minimal hsub ((AddSubmonoid.isClosed_topologicalClosure _).preimage hf)
    ((denseRange_coe he) x)

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
    · refine norm_le_of_mem_closedNonnegCone he hr ?_ ?_
      · rw [le_iff_mem_closedNonnegCone, neg_smul, sub_neg_eq_add] at h1
        exact h1
      · exact (le_iff_mem_closedNonnegCone _ _).mp h2

instance : PosSMulMono ℝ (OrderUnitCompletion he) :=
  (isOrderUnitNorm he).posSMulMono

instance : OrderClosedTopology (OrderUnitCompletion he) :=
  (isOrderUnitNorm he).orderClosedTopology

/-- Continuous linear extension of a bounded real linear map `E →L[ℝ] F` to
`OrderUnitCompletion he`, when `F` is complete. -/
def extend (he : IsOrderUnitNorm e) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (T : E →L[ℝ] F) : OrderUnitCompletion he →L[ℝ] F :=
  T.extend (coe he).toContinuousLinearMap

/-- `extend he T` agrees with `T` on the canonical dense image `coe he`. -/
@[simp]
theorem extend_coe {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (T : E →L[ℝ] F) (a : E) : extend he T (coe he a) = T a :=
  ContinuousLinearMap.extend_eq T (denseRange_coe he)
    (Isometry.isUniformInducing (coe he).isometry) a

/-- Uniqueness of continuous linear extension: any continuous linear map
`S : OrderUnitCompletion he →L[ℝ] F` agreeing with `T` on `coe he` equals `extend he T`. -/
theorem extend_unique {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (T : E →L[ℝ] F) {S : OrderUnitCompletion he →L[ℝ] F}
    (hS : ∀ a : E, S (coe he a) = T a) : S = extend he T :=
  (ContinuousLinearMap.extend_unique T (e := (coe he).toContinuousLinearMap) (denseRange_coe he)
    (Isometry.isUniformInducing (coe he).isometry) S (ContinuousLinearMap.ext hS)).symm

/-- Continuous linear extension to `OrderUnitCompletion he` preserves the operator norm:
`‖extend he T‖ = ‖T‖`. -/
theorem opNorm_extend {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (T : E →L[ℝ] F) : ‖extend he T‖ = ‖T‖ := by
  refine le_antisymm ?_ ?_
  · have hbound : ∀ a : E, ‖(T : E →ₗ[ℝ] F) a‖ ≤ ‖T‖ * ‖coe he a‖ := fun a => by
      simpa [(coe he).norm_map] using T.le_opNorm a
    have heq : (T : E →ₗ[ℝ] F).extendOfNorm (coe he).toLinearMap = extend he T :=
      LinearMap.extendOfNorm_unique (denseRange_coe he) ‖T‖ hbound (extend he T)
        (LinearMap.ext fun a => extend_coe T a)
    rw [← heq]
    exact LinearMap.opNorm_extendOfNorm_le (denseRange_coe he) (norm_nonneg T) hbound
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
  have hclosed : IsClosed {z : OrderUnitCompletion he | 0 ≤ extend he T z} :=
    isClosed_Ici.preimage (extend he T).continuous
  have hsub : coe he '' {a : E | 0 ≤ a} ⊆
      {z : OrderUnitCompletion he | 0 ≤ extend he T z} := by
    rintro _ ⟨a, ha, rfl⟩
    simp only [Set.mem_ofPred_eq, extend_coe]
    simpa only [map_zero] using hT ha
  exact closure_minimal hsub hclosed
    (mem_closedNonnegCone_iff.mp ((le_iff_mem_closedNonnegCone x y).mp hxy))

end OrderUnitCompletion

end TauCeti
