/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Algebra.Order.Group.Pointwise.Interval
public import Mathlib.Topology.Subpath

/-!
# Total variation of paths

The length of a bundled path is its existing `eVariationOn` on the unit interval. This agrees
with the variation of `Path.extend` on the real interval `[0, 1]`, so length statements for
real-parameter curves apply to bundled paths as well.

Binary and finite concatenations add lengths, and restriction to a subpath recovers the variation
on its parameter interval. Reversal and increasing continuous reparametrizations preserve length.
All length identities are extended nonnegative identities, allowing paths of infinite length.
In particular, concatenation is rectifiable exactly when both constituent paths are rectifiable.
-/

-- Central Mathlib inputs: `eVariationOn.comp_eq_of_monotoneOn`,
-- `eVariationOn.comp_eq_of_antitoneOn`, and `eVariationOn.Icc_add_Icc`.

public section

open Set
open scoped unitInterval ENNReal

namespace Path

variable {X : Type*} [TopologicalSpace X] {x y z : X}

/-- The function underlying a subpath is composition with the affine parameter map. -/
@[simp]
theorem coe_subpath (γ : Path x y) (s t : I) :
    ⇑(γ.subpath s t) = γ ∘ Icc.convexComb s t := (rfl)

variable [WeakPseudoEMetricSpace X]

/-- Extending a path to the real line preserves its variation on every subset of its original
parameter interval. -/
@[simp]
theorem eVariationOn_extend_image (γ : Path x y) (s : Set I) :
    eVariationOn γ.extend (Subtype.val '' s) = eVariationOn γ s := by
  rw [← eVariationOn.comp_eq_of_monotoneOn γ.extend Subtype.val
    (fun _ _ _ _ h ↦ h)]
  exact eVariationOn.eq_of_eqOn fun t _ ↦ γ.extend_extends' t

/-- The variation of a path's real extension on `[0, 1]` is its intrinsic length. -/
@[simp]
theorem eVariationOn_extend (γ : Path x y) :
    eVariationOn γ.extend (Icc 0 1) = eVariationOn γ univ := by
  simpa only [image_univ, Subtype.range_coe_subtype, ofPred_mem_eq, unitInterval] using
    γ.eVariationOn_extend_image univ

/-- A constant path has zero length. -/
@[simp]
theorem eVariationOn_refl (x : X) : eVariationOn (Path.refl x) univ = 0 := by
  exact eVariationOn.constant_on (by rw [image_univ, refl_range]; exact subsingleton_singleton)

/-- Reversing a path preserves length, including infinite length. -/
@[simp]
theorem eVariationOn_symm (γ : Path x y) :
    eVariationOn γ.symm univ = eVariationOn γ univ := by
  have heq : ⇑γ.symm = γ ∘ unitInterval.symm := funext (symm_apply γ)
  rw [heq, eVariationOn.comp_eq_of_antitoneOn γ unitInterval.symm
    (unitInterval.strictAnti_symm.antitone.antitoneOn univ), image_univ,
    unitInterval.symm_bijective.surjective.range_eq]

/-- Reversing a path preserves rectifiability. -/
@[simp]
theorem boundedVariationOn_symm_iff (γ : Path x y) :
    BoundedVariationOn γ.symm univ ↔ BoundedVariationOn γ univ := by
  simp only [BoundedVariationOn, eVariationOn_symm]

/-- The length of a concatenation is the sum of the two path lengths. No rectifiability
hypothesis is required. -/
@[simp]
theorem eVariationOn_trans (γ : Path x y) (δ : Path y z) :
    eVariationOn (γ.trans δ) univ = eVariationOn γ univ + eVariationOn δ univ := by
  have hleft : eVariationOn (γ.trans δ).extend (Icc 0 (1 / 2)) =
      eVariationOn γ.extend (Icc 0 1) := by
    have heq : EqOn (γ.trans δ).extend (γ.extend ∘ fun t : ℝ ↦ 2 * t)
        (Icc 0 (1 / 2)) := fun t ht ↦ γ.extend_trans_of_le_half δ ht.2
    rw [eVariationOn.eq_of_eqOn heq,
      eVariationOn.comp_eq_of_monotoneOn γ.extend (fun t : ℝ ↦ 2 * t)
        (fun _ _ _ _ h ↦ mul_le_mul_of_nonneg_left h (by norm_num))]
    rw [image_mul_left_Icc' (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hright : eVariationOn (γ.trans δ).extend (Icc (1 / 2) 1) =
      eVariationOn δ.extend (Icc 0 1) := by
    have heq : EqOn (γ.trans δ).extend (δ.extend ∘ fun t : ℝ ↦ 2 * t - 1)
        (Icc (1 / 2) 1) := fun t ht ↦ γ.extend_trans_of_half_le δ ht.1
    rw [eVariationOn.eq_of_eqOn heq,
      eVariationOn.comp_eq_of_monotoneOn δ.extend (fun t : ℝ ↦ 2 * t - 1)
        (fun _ _ _ _ h ↦ sub_le_sub_right (mul_le_mul_of_nonneg_left h (by norm_num)) _)]
    simp only [sub_eq_add_neg]
    rw [image_affine_Icc' (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hadd := eVariationOn.Icc_add_Icc (γ.trans δ).extend (s := univ)
    (a := 0) (b := 1 / 2) (c := 1) (by norm_num) (by norm_num) (mem_univ _)
  simpa only [univ_inter, hleft, hright, eVariationOn_extend] using hadd.symm

/-- A concatenation is rectifiable if and only if each constituent path is rectifiable. -/
@[simp]
theorem boundedVariationOn_trans_iff (γ : Path x y) (δ : Path y z) :
    BoundedVariationOn (γ.trans δ) univ ↔
      BoundedVariationOn γ univ ∧ BoundedVariationOn δ univ := by
  simp only [BoundedVariationOn, eVariationOn_trans, ENNReal.add_ne_top]

/-- The length of a finite concatenation is the sum of the constituent lengths.
The empty concatenation has length zero. -/
@[simp]
theorem eVariationOn_concat {n : ℕ} (p : Fin (n + 1) → X)
    (F : (k : Fin n) → Path (p k.castSucc) (p k.succ)) :
    eVariationOn (Path.concat p F) univ = ∑ k, eVariationOn (F k) univ := by
  induction n with
  | zero => simp
  | succ n ih =>
    -- Pass to functions before rewriting: the endpoint indices in `concat_succ` are
    -- definitionally equal but have different expressions.
    have hcoe : ⇑(concat p F) =
        ⇑((concat (p ∘ Fin.castSucc) (fun k ↦ F k.castSucc)).trans (F (Fin.last n))) :=
      congrArg (fun q : Path (p 0) (p (Fin.last (n + 1))) ↦ (q : I → X)) (concat_succ p F)
    rw [hcoe, eVariationOn_trans, ih, Fin.sum_univ_castSucc]

/-- The length of a subpath is the variation on the corresponding unordered parameter interval.
This includes reversed and constant subpaths. -/
@[simp↓]
theorem eVariationOn_subpath (γ : Path x y) (s t : I) :
    eVariationOn (γ.subpath s t) univ = eVariationOn γ (uIcc s t) := by
  wlog hst : s ≤ t
  · rw [← symm_subpath, eVariationOn_symm, uIcc_comm]
    exact this γ t s (le_of_not_ge hst)
  have hm : Monotone (Icc.convexComb s t) := by
    intro u v huv
    rw [← Subtype.coe_le_coe]
    simp only [Icc.coe_convexComb]
    have huv' : (u : ℝ) ≤ v := huv
    have hst' : (s : ℝ) ≤ t := hst
    nlinarith [mul_nonneg (sub_nonneg.mpr huv') (sub_nonneg.mpr hst')]
  rw [coe_subpath, eVariationOn.comp_eq_of_monotoneOn γ _ (hm.monotoneOn univ),
    image_univ, range_subpathAux]

/-- Every subpath of a rectifiable path is rectifiable. -/
theorem boundedVariationOn_subpath (γ : Path x y) (hγ : BoundedVariationOn γ univ) (s t : I) :
    BoundedVariationOn (γ.subpath s t) univ := by
  rw [BoundedVariationOn, eVariationOn_subpath]
  exact hγ.mono (subset_univ _)

/-- Increasing continuous reparametrization fixing the endpoints preserves path length.
Pauses in the reparametrization are allowed. -/
@[simp↓]
theorem eVariationOn_reparam (γ : Path x y) {f : I → I} (hf : Monotone f)
    (hc : Continuous f) (h0 : f 0 = 0) (h1 : f 1 = 1) :
    eVariationOn (γ.reparam f hc h0 h1) univ = eVariationOn γ univ := by
  have hrange : range f = univ := by
    rw [unitInterval.univ_eq_Icc, ← h0, ← h1,
      ← hc.continuousOn.image_Icc_of_monotoneOn zero_le_one (hf.monotoneOn _),
      ← unitInterval.univ_eq_Icc, image_univ]
  rw [coe_reparam, eVariationOn.comp_eq_of_monotoneOn γ f (hf.monotoneOn univ), image_univ, hrange]

/-- Increasing continuous reparametrization fixing the endpoints preserves rectifiability.
Pauses in the reparametrization are allowed. -/
@[simp↓]
theorem boundedVariationOn_reparam_iff (γ : Path x y) {f : I → I} (hf : Monotone f)
    (hc : Continuous f) (h0 : f 0 = 0) (h1 : f 1 = 1) :
    BoundedVariationOn (γ.reparam f hc h0 h1) univ ↔ BoundedVariationOn γ univ := by
  simp only [BoundedVariationOn, eVariationOn_reparam γ hf hc h0 h1]

end Path
