/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.Morse.Deformation
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Topology.ContinuousMap.ApplyProdMk
import TauCeti.Topology.Homotopy.DeformationRetract

/-!
# Attaching the negative disc bundle across a Morse–Bott critical level

Near a nondegenerate critical submanifold `C` of index `λ` with critical value `c`, a Morse–Bott
function has, after the Morse–Bott lemma, the normal form `f = c - ‖u‖² + ‖v‖²` on a tube around
`C`, where `u` and `v` are the components of a normal vector in the negative and positive normal
bundles `ν⁻` and `ν⁺`. Passing the critical level attaches the negative disc bundle
`{‖u‖² ≤ ε, v = 0}` of radius `√ε` to the lower sublevel `M_{c-ε} = {f ≤ c - ε}` along its sphere
bundle. For an isolated nondegenerate critical point the base is a point and this is Milnor's
attachment of a `λ`-cell.

This file proves the deformation part of this attachment theorem from the normal form alone,
written intrinsically on `M`. The tube is an open set `W` carrying smooth functions `s, t ≥ 0`, the
squared norms `s = ‖u‖²` and `t = ‖v‖²`, with `f = c - s + t` on `W`, and a continuous scaling
`φ : [0, 1] × W → W` of the positive directions, `(τ, u, v) ↦ (u, τ v)`: it preserves `s`,
multiplies `t` by `τ²`, is the identity at `τ = 1` and fixes the points with `t = 0`. Moreover, at
every point with `t ≠ 0` some tangent vector, `(0, v)` in the normal form, is killed by `ds` but
not by `dt`. If the band `f⁻¹[c - ε, c + ε]` is compact, its critical points lie in `W`, and the
part `{s + 2t ≤ 2ε}` of the tube is compact, then `M_{c+ε}` strong deformation retracts onto
`M_{c-ε}` together with the negative disc bundle `{x ∈ W | t x = 0, s x ≤ ε}`
(`TauCeti.exists_sublevel_union_negativeDiscBundle_deformation`). The tube may have several
components, for instance one for each critical submanifold on the level.

The proof is Milnor's, adapting the argument of `TauCeti.exists_sublevel_union_cells_deformation`,
the chart version for isolated nondegenerate critical points. The function `F = f - μ(s + 2t)`,
lowered on the tube by a smooth nonincreasing cutoff `μ` equal to `2ε` on `(-∞, ε]` and to `0` on
`[2ε, ∞)`, has the same sublevel `{F ≤ c + ε} = M_{c+ε}` and no critical points in the band
`F⁻¹[c - ε, c + ε]`: off the tube it is `f` near the band, along a vector killed by `ds` its
derivative is `(1 - 2μ') dt ≠ 0` where `t ≠ 0`, and where `t = 0` it lies below `c - ε`. So
`M_{c+ε}` deformation retracts onto `{F ≤ c - ε}` (`TauCeti.exists_sublevelDeformation`). This
sublevel in turn retracts onto `M_{c-ε}` with the disc bundle attached: at time `τ` the retraction
scales the positive directions of a point by `(1 - τ) min 1 √((s - ε) / t) + τ`, which only lowers
`F`. The scaling factor jumps where `t = 0`, but there `φ` does not move the point at any time, and
since `[0, 1]` is compact the deformation is still continuous.

## Main results

* `TauCeti.exists_sublevel_union_negativeDiscBundle_deformation`: across a compact band around a
  critical level, the sublevel `M_{c+ε}` strong deformation retracts onto `M_{c-ε}` with the
  negative disc bundle of a quadratic normal form attached.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  proof of Theorem 3.2.
* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse Theory*, lecture notes, 2006,
  Theorem 15.4.
-/

public section

noncomputable section

open Function Set Filter Topology
open scoped ContDiff Manifold

namespace TauCeti

/-! ### Scaling the positive directions onto the disc bundle -/

section Retraction

variable {M : Type*} {f s t : M → ℝ} {c ε : ℝ} {W : Set M} {x : M}

/-- The factor by which Milnor's retraction scales the positive directions of a point at time
`τ`: the convex combination `(1 - τ) min 1 √((s - ε) / t) + τ`. At time `0` it brings the point to
the level `t = s - ε` when it lies above it with `s ≥ ε`, and to `t = 0` when `s < ε`. -/
private def retractionScale (s t : M → ℝ) (ε : ℝ) (τ : unitInterval) (x : M) : unitInterval :=
  ⟨(1 - τ) * min 1 √((s x - ε) / t x) + τ, by
    have h₀ : 0 ≤ min 1 √((s x - ε) / t x) := le_min zero_le_one (Real.sqrt_nonneg _)
    have h₁ : min 1 √((s x - ε) / t x) ≤ 1 := min_le_left _ _
    constructor <;> nlinarith [τ.2.1, τ.2.2]⟩

private theorem coe_retractionScale (τ : unitInterval) (x : M) :
    (retractionScale s t ε τ x : ℝ) = (1 - τ) * min 1 √((s x - ε) / t x) + τ :=
  rfl

private theorem retractionScale_one (x : M) : retractionScale s t ε 1 x = 1 :=
  Subtype.ext (by simp [coe_retractionScale])

/-- For `0 < t ≤ s - ε`, the scaling factor is `1` at all times. -/
private theorem retractionScale_eq_one (τ : unitInterval) (ht : 0 < t x)
    (hst : t x ≤ s x - ε) : retractionScale s t ε τ x = 1 := by
  have h1 : 1 ≤ √((s x - ε) / t x) := Real.one_le_sqrt.2 ((one_le_div ht).2 hst)
  exact Subtype.ext (by simp [coe_retractionScale, min_eq_left h1])

/-- At time `0`, scaling the positive directions brings `t` down to at most `s - ε` when
`s ≥ ε`. -/
private theorem retractionScale_zero_sq_mul_le (ht₀ : 0 ≤ t x) (hs : ε ≤ s x) :
    (retractionScale s t ε 0 x : ℝ) ^ 2 * t x ≤ s x - ε := by
  rcases ht₀.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    linarith
  set m := min 1 √((s x - ε) / t x)
  have hm : (retractionScale s t ε 0 x : ℝ) = m := by simp [coe_retractionScale, m]
  have hm₀ : 0 ≤ m := le_min zero_le_one (Real.sqrt_nonneg _)
  have hm2 : m ^ 2 ≤ (s x - ε) / t x := by
    calc m ^ 2 ≤ √((s x - ε) / t x) ^ 2 := pow_le_pow_left₀ hm₀ (min_le_right _ _) 2
      _ = (s x - ε) / t x := Real.sq_sqrt (div_nonneg (by linarith) ht₀)
  rw [hm]
  calc m ^ 2 * t x ≤ (s x - ε) / t x * t x := mul_le_mul_of_nonneg_right hm2 ht₀
    _ = s x - ε := div_mul_cancel₀ _ hpos.ne'

/-- At time `0`, a point with `s < ε` is scaled onto `t = 0`. -/
private theorem retractionScale_zero_eq_zero (ht₀ : 0 ≤ t x) (hs : s x < ε) :
    retractionScale s t ε 0 x = 0 := by
  have h : √((s x - ε) / t x) = 0 :=
    Real.sqrt_eq_zero'.2 (div_nonpos_of_nonpos_of_nonneg (by linarith) ht₀)
  exact Subtype.ext (by simp [coe_retractionScale, h])

variable [TopologicalSpace M]

open scoped Classical in
/-- Milnor's retraction of a tube onto the lower sublevel with the negative disc bundle attached:
at time `τ` it scales the positive directions of a point of the tube by `retractionScale`, and it
fixes the points off the tube. -/
private def tubeRetraction (φ : C(unitInterval × W, W)) (s t : M → ℝ) (ε : ℝ) (τ : unitInterval)
    (x : M) : M :=
  if hx : x ∈ W then φ (retractionScale s t ε τ x, ⟨x, hx⟩) else x

variable {φ : C(unitInterval × W, W)}

private theorem tubeRetraction_of_mem (τ : unitInterval) (hx : x ∈ W) :
    tubeRetraction φ s t ε τ x = φ (retractionScale s t ε τ x, ⟨x, hx⟩) := by
  simp [tubeRetraction, hx]

private theorem tubeRetraction_of_notMem (τ : unitInterval) (hx : x ∉ W) :
    tubeRetraction φ s t ε τ x = x := by
  simp [tubeRetraction, hx]

variable (hφs : ∀ τ x, s (φ (τ, x)) = s x) (hφt : ∀ τ x, t (φ (τ, x)) = τ ^ 2 * t x)
  (hφ₁ : ∀ x, φ (1, x) = x) (hφ₀ : ∀ τ (x : W), t x = 0 → φ (τ, x) = x)

include hφ₁ in
private theorem tubeRetraction_one (x : M) : tubeRetraction φ s t ε 1 x = x := by
  by_cases hx : x ∈ W
  · rw [tubeRetraction_of_mem _ hx, retractionScale_one, hφ₁]
  · exact tubeRetraction_of_notMem _ hx

include hφ₁ hφ₀ in
/-- The retraction does not move the points of the tube with `t = 0` or on or below the level
`t = s - ε`. -/
private theorem tubeRetraction_eq_self (τ : unitInterval) (hx : x ∈ W) (ht₀ : 0 ≤ t x)
    (h : t x = 0 ∨ t x ≤ s x - ε) : tubeRetraction φ s t ε τ x = x := by
  rw [tubeRetraction_of_mem _ hx]
  by_cases h0 : t x = 0
  · exact congrArg Subtype.val (hφ₀ _ _ h0)
  · rw [retractionScale_eq_one τ (lt_of_le_of_ne' ht₀ h0) (h.resolve_left h0), hφ₁]

include hφs hφt in
/-- At time `0` the retraction lands in the lower sublevel or in the negative disc bundle. -/
private theorem tubeRetraction_zero_mem (hf : ∀ x ∈ W, f x = c - s x + t x)
    (ht₀ : ∀ x ∈ W, 0 ≤ t x) (hx : x ∈ W) :
    tubeRetraction φ s t ε 0 x ∈ {x | f x ≤ c - ε} ∪ {x | x ∈ W ∧ t x = 0 ∧ s x ≤ ε} := by
  rw [tubeRetraction_of_mem _ hx]
  set y := φ (retractionScale s t ε 0 x, ⟨x, hx⟩)
  rcases lt_or_ge (s x) ε with hs | hs
  · refine .inr ⟨y.2, ?_, ?_⟩
    · rw [hφt, retractionScale_zero_eq_zero (ht₀ x hx) hs]
      simp
    · rw [hφs]
      exact hs.le
  · refine .inl ?_
    simp only [mem_ofPred_eq]
    rw [hf _ y.2, hφs, hφt]
    linarith [retractionScale_zero_sq_mul_le (ht₀ x hx) hs]

include hφ₀ in
/-- **Milnor's retraction is continuous** on any set `X` whose points outside a closed subset `C`
of the open tube are not moved. Where `t ≠ 0` the scaling factor is continuous; where `t = 0` it
jumps, but `φ` does not move the point at any time, so by compactness of `[0, 1]` the scaled
points of nearby points stay nearby. -/
private theorem continuous_tubeRetraction (hW : IsOpen W) (hs : ContinuousOn s W)
    (ht : ContinuousOn t W) {X C : Set M} (hC : IsClosed C) (hCW : C ⊆ W)
    (hfix : ∀ x ∈ X, x ∉ C → ∀ τ, tubeRetraction φ s t ε τ x = x) :
    Continuous fun p : unitInterval × X ↦ tubeRetraction φ s t ε p.1 p.2 := by
  have hval : Continuous fun p : unitInterval × X ↦ (p.2 : M) :=
    continuous_subtype_val.comp continuous_snd
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  by_cases hp₀ : (p₀.2 : M) ∈ W
  swap
  · -- Off the tube, the retraction is the identity near `p₀`.
    have hpC : (p₀.2 : M) ∉ C := fun h ↦ hp₀ (hCW h)
    refine hval.continuousAt.congr (eventually_of_mem
      ((hC.isOpen_compl.preimage hval).mem_nhds hpC) fun q hq ↦ ?_)
    exact (hfix q.2 q.2.2 hq q.1).symm
  -- On the tube, read the retraction on the open set of pairs whose point lies in `W`.
  set U := {p : unitInterval × X | (p.2 : M) ∈ W}
  have hU : IsOpen U := hW.preimage hval
  refine ContinuousWithinAt.continuousAt ?_ (hU.mem_nhds hp₀)
  rw [continuousWithinAt_iff_continuousAt_domRestrict _ (show p₀ ∈ U from hp₀)]
  set w : U → W := fun q ↦ ⟨q.1.2, q.2⟩
  have hw : Continuous w := (hval.comp continuous_subtype_val).subtype_mk _
  have heq : U.domRestrict (fun p : unitInterval × X ↦ tubeRetraction φ s t ε p.1 p.2) =
      fun q ↦ (φ (retractionScale s t ε q.1.1 q.1.2, w q) : M) :=
    funext fun q ↦ tubeRetraction_of_mem (x := (q.1.2 : M)) q.1.1 q.2
  rw [heq]
  -- Where `t ≠ 0`, the scaling factor is continuous; where `t = 0`, `φ` fixes the point at all
  -- times, so the tube lemma over the compact `[0, 1]` applies whatever the scaling factor.
  have hst (g : M → ℝ) (hg : ContinuousOn g W) (q : U) :
      ContinuousAt (fun p : U ↦ g p.1.2) q :=
    ContinuousAt.comp (f := fun q : U ↦ ((q.1.2 : X) : M)) (hg.continuousAt (hW.mem_nhds q.2))
      (hval.comp continuous_subtype_val).continuousAt
  have hκ (q : U) (hq : w q ∉ {y : W | t y = 0}) :
      ContinuousAt (fun p : U ↦ retractionScale s t ε p.1.1 p.1.2) q := by
    refine ContinuousAt.codRestrict (f := fun q : U ↦ (1 - (q.1.1 : ℝ)) *
      min 1 √((s q.1.2 - ε) / t q.1.2) + q.1.1) (fun q ↦ (retractionScale s t ε _ _).2) ?_
    have hτ : Continuous fun q : U ↦ (q.1.1 : ℝ) :=
      continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)
    exact ((continuous_const.sub hτ).continuousAt.mul (continuousAt_const.min
      (((hst s hs q).sub continuousAt_const).div (hst t ht q) hq).sqrt)).add hτ.continuousAt
  exact (continuous_subtype_val.comp (φ.continuous_apply_prodMk_of_fixed
    (A := {y : W | t y = 0}) (fun τ y hy ↦ hφ₀ τ y hy) hw hκ)).continuousAt

include hφs hφt hφ₁ hφ₀ in
/-- **Milnor's retraction onto the lower sublevel with the negative disc bundle attached.** Let
`X` be a set preserved by scaling the positive directions of its points in the tube, whose points
outside a closed subset `C` of the tube lie in `{f ≤ c - ε}`. Then the intersection of `X` with
`{f ≤ c - ε}` and the negative disc bundle `{x ∈ W | t x = 0, s x ≤ ε}` is a strong deformation
retract of `X`. -/
private theorem exists_inter_sublevel_union_negativeDiscBundle_deformation (hW : IsOpen W)
    (hs : ContinuousOn s W) (ht : ContinuousOn t W) (ht₀ : ∀ x ∈ W, 0 ≤ t x)
    (hf : ∀ x ∈ W, f x = c - s x + t x) {X C : Set M} (hC : IsClosed C) (hCW : C ⊆ W)
    (hXC : ∀ x ∈ X, x ∉ C → f x ≤ c - ε) (hXφ : ∀ τ (x : W), (x : M) ∈ X → (φ (τ, x) : M) ∈ X) :
    ∃ r : C(X, ↥(X ∩ ({x | f x ≤ c - ε} ∪ {x | x ∈ W ∧ t x = 0 ∧ s x ≤ ε}))),
      (∀ x, r (ContinuousMap.inclusion inter_subset_left x) = x) ∧
      Nonempty (((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel
        (ContinuousMap.id X)
        {x | (x : M) ∈ {x | f x ≤ c - ε} ∪ {x | x ∈ W ∧ t x = 0 ∧ s x ≤ ε}}) := by
  set S := {x | f x ≤ c - ε} ∪ {x | x ∈ W ∧ t x = 0 ∧ s x ≤ ε}
  -- Points of `S` are not moved, at any time.
  have hfixS {x : M} (hxS : x ∈ S) (τ : unitInterval) : tubeRetraction φ s t ε τ x = x := by
    by_cases hx : x ∈ W
    · refine tubeRetraction_eq_self hφ₁ hφ₀ τ hx (ht₀ x hx) ?_
      rcases hxS with hxS | hxS
      · exact .inr (by simp only [mem_ofPred_eq, hf x hx] at hxS; linarith)
      · exact .inl hxS.2.1
    · exact tubeRetraction_of_notMem _ hx
  have hGX {x : M} (hxX : x ∈ X) (τ : unitInterval) : tubeRetraction φ s t ε τ x ∈ X := by
    by_cases hx : x ∈ W
    · rw [tubeRetraction_of_mem _ hx]
      exact hXφ _ ⟨x, hx⟩ hxX
    · rwa [tubeRetraction_of_notMem _ hx]
  have hG0S {x : M} (hxX : x ∈ X) : tubeRetraction φ s t ε 0 x ∈ S := by
    by_cases hx : x ∈ W
    · exact tubeRetraction_zero_mem hφs hφt hf ht₀ hx
    · rw [tubeRetraction_of_notMem _ hx]
      exact .inl (hXC x hxX fun h ↦ hx (hCW h))
  have hcont : Continuous fun p : unitInterval × X ↦ tubeRetraction φ s t ε p.1 p.2 :=
    continuous_tubeRetraction hφ₀ hW hs ht hC hCW fun x hxX hxC ↦ hfixS (.inl (hXC x hxX hxC))
  refine ⟨⟨fun x ↦ ⟨tubeRetraction φ s t ε 0 x, hGX x.2 0, hG0S x.2⟩,
      (hcont.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩,
    fun x ↦ Subtype.ext (hfixS x.2.2 0), ⟨?_⟩⟩
  exact
    { toFun p := ⟨tubeRetraction φ s t ε p.1 p.2, hGX p.2.2 p.1⟩
      continuous_toFun := hcont.subtype_mk _
      map_zero_left x := rfl
      map_one_left x := Subtype.ext (tubeRetraction_one hφ₁ x)
      prop' τ x hx := Subtype.ext ((hfixS hx τ).trans (hfixS hx 0).symm) }

end Retraction

/-! ### Milnor's lowered function -/

section MilnorFunction

variable {M : Type*} {f s t : M → ℝ} {c ε : ℝ} {W : Set M} {μ : ℝ → ℝ} {x : M}

variable (f s t W μ) in
/-- Milnor's function `f - μ(s + 2t)`, lowered on the tube `W` and equal to `f` off it. -/
private def tubeMilnorFunction (x : M) : ℝ :=
  f x - W.indicator (fun y ↦ μ (s y + 2 * t y)) x

private theorem tubeMilnorFunction_of_mem (hx : x ∈ W) :
    tubeMilnorFunction f s t W μ x = f x - μ (s x + 2 * t x) := by
  rw [tubeMilnorFunction, indicator_of_mem hx]

private theorem tubeMilnorFunction_of_notMem (hx : x ∉ W) :
    tubeMilnorFunction f s t W μ x = f x := by
  rw [tubeMilnorFunction, indicator_of_notMem hx, sub_zero]

private theorem tubeMilnorFunction_le (hμ : ∀ r, 0 ≤ μ r) (x : M) :
    tubeMilnorFunction f s t W μ x ≤ f x :=
  sub_le_self _ (indicator_nonneg (fun _ _ ↦ hμ _) _)

variable (hs₀ : ∀ x ∈ W, 0 ≤ s x) (ht₀ : ∀ x ∈ W, 0 ≤ t x) (hf : ∀ x ∈ W, f x = c - s x + t x)
  (hμ₀ : ∀ r, 2 * ε ≤ r → μ r = 0)

include hs₀ hf hμ₀ in
/-- Milnor's function has the same sublevel `{F ≤ c + ε}` as `f`: where it is lowered,
`s + 2t < 2ε`, so `f = c - s + t < c + ε`. -/
private theorem setOf_tubeMilnorFunction_le (hμ : ∀ r, 0 ≤ μ r) :
    {x | tubeMilnorFunction f s t W μ x ≤ c + ε} = {x | f x ≤ c + ε} := by
  ext x
  refine ⟨fun hx ↦ ?_, fun hx ↦ (tubeMilnorFunction_le hμ x).trans hx⟩
  simp only [mem_ofPred_eq] at hx ⊢
  by_cases hxW : x ∈ W
  · rw [tubeMilnorFunction_of_mem hxW] at hx
    rcases le_or_gt (2 * ε) (s x + 2 * t x) with h | h
    · rwa [hμ₀ _ h, sub_zero] at hx
    · rw [hf x hxW]
      linarith [hs₀ x hxW]
  · rwa [tubeMilnorFunction_of_notMem hxW] at hx

include hμ₀ in
/-- Away from the part `{s + 2t ≤ 2ε}` of the tube, Milnor's function is `f`. -/
private theorem tubeMilnorFunction_eq_of_notMem
    (hx : x ∉ {x | x ∈ W ∧ s x + 2 * t x ≤ 2 * ε}) : tubeMilnorFunction f s t W μ x = f x := by
  by_cases hxW : x ∈ W
  · rw [tubeMilnorFunction_of_mem hxW, hμ₀ _ (not_le.1 fun h ↦ hx ⟨hxW, h⟩).le, sub_zero]
  · exact tubeMilnorFunction_of_notMem hxW

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  (hK : IsCompact {x | x ∈ W ∧ s x + 2 * t x ≤ 2 * ε})

include hμ₀ hK in
/-- Away from the part `{s + 2t ≤ 2ε}` of the tube, Milnor's function agrees with `f` near each
point. -/
private theorem tubeMilnorFunction_eventuallyEq
    (hx : x ∉ {x | x ∈ W ∧ s x + 2 * t x ≤ 2 * ε}) : tubeMilnorFunction f s t W μ =ᶠ[𝓝 x] f :=
  eventually_of_mem (hK.isClosed.isOpen_compl.mem_nhds hx) fun _ hy ↦
    tubeMilnorFunction_eq_of_notMem hμ₀ hy

include hμ₀ hK in
/-- **Milnor's function is smooth.** The lowering term is supported in the compact part
`{s + 2t ≤ 2ε}` of the open tube, where it is smooth. -/
private theorem contMDiff_tubeMilnorFunction (hfs : ContMDiff I 𝓘(ℝ) ∞ f) (hW : IsOpen W)
    (hs : ContMDiffOn I 𝓘(ℝ) ∞ s W) (ht : ContMDiffOn I 𝓘(ℝ) ∞ t W) (hμs : ContDiff ℝ ∞ μ) :
    ContMDiff I 𝓘(ℝ) ∞ (tubeMilnorFunction f s t W μ) := by
  refine ContMDiff.sub hfs (contMDiff_of_tsupport fun y hy ↦ ?_)
  have hsub : tsupport (W.indicator fun y ↦ μ (s y + 2 * t y)) ⊆
      {x | x ∈ W ∧ s x + 2 * t x ≤ 2 * ε} :=
    closure_minimal (fun y hy ↦ by_contra fun h ↦ hy (by
      rw [indicator_apply_eq_zero]
      exact fun hyW ↦ hμ₀ _ (not_le.1 fun h' ↦ h ⟨hyW, h'⟩).le)) hK.isClosed
  have hyW : y ∈ W := (hsub hy).1
  have hterm : ContMDiffAt I 𝓘(ℝ) ∞ (fun y ↦ μ (s y + 2 * t y)) y :=
    -- `μ (a + 2 b)` is a smooth function of `(a, b) = (s y, t y)`.
    have hg : ContDiff ℝ ∞ fun p : ℝ × ℝ ↦ μ (p.1 + 2 * p.2) := hμs.comp (by fun_prop)
    hg.contMDiff.contMDiffAt.comp y ((hs.contMDiffAt (hW.mem_nhds hyW)).prodMk_space
      (ht.contMDiffAt (hW.mem_nhds hyW)))
  exact hterm.congr_of_eventuallyEq
    (eventually_of_mem (hW.mem_nhds hyW) fun z hz ↦ indicator_of_mem hz _)

omit [T2Space M] in
include hf in
/-- **Milnor's function has no critical points where `t ≠ 0`.** Near a point of the tube it is
`c - s + t - μ(s + 2t)`, whose derivative along a vector killed by `ds` is `(1 - 2μ') dt`, while
`μ' ≤ 0`. -/
private theorem mfderiv_tubeMilnorFunction_ne_zero (hW : IsOpen W)
    (hs : ContMDiffOn I 𝓘(ℝ) ∞ s W) (ht : ContMDiffOn I 𝓘(ℝ) ∞ t W) (hμs : ContDiff ℝ ∞ μ)
    (hμa : Antitone μ)
    (hdir : ∀ x ∈ W, t x ≠ 0 → ∃ v : TangentSpace I x,
      mfderiv I 𝓘(ℝ) s x v = 0 ∧ mfderiv I 𝓘(ℝ) t x v ≠ 0)
    (hx : x ∈ W) (htx : t x ≠ 0) :
    mfderiv I 𝓘(ℝ) (tubeMilnorFunction f s t W μ) x ≠ 0 := by
  obtain ⟨v, hsv, htv⟩ := hdir x hx htx
  have hxW : W ∈ 𝓝 x := hW.mem_nhds hx
  have hsd : HasMFDerivAt I 𝓘(ℝ) s x (mfderiv I 𝓘(ℝ) s x) :=
    ((hs.contMDiffAt hxW).mdifferentiableAt (by simp)).hasMFDerivAt
  have htd : HasMFDerivAt I 𝓘(ℝ) t x (mfderiv I 𝓘(ℝ) t x) :=
    ((ht.contMDiffAt hxW).mdifferentiableAt (by simp)).hasMFDerivAt
  set r := s x + 2 * t x
  have hμd : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ) μ r ((1 : ℝ →L[ℝ] ℝ).smulRight (deriv μ r)) :=
    ((hμs.differentiable (by simp)) r).hasDerivAt.hasFDerivAt.hasMFDerivAt
  -- Near `x`, Milnor's function is `c - s + t - μ (s + 2 t)`.
  have hg := (((hasMFDerivAt_const c x).sub hsd).add htd).sub
    (hμd.comp x (hsd.add (htd.const_smul (2 : ℝ))))
  have heq : tubeMilnorFunction f s t W μ =ᶠ[𝓝 x] (fun _ ↦ c) - s + t - μ ∘ (s + (2 : ℝ) • t) :=
    eventually_of_mem hxW fun y hy ↦ by
      simp only [tubeMilnorFunction_of_mem hy, hf y hy, Pi.sub_apply, Pi.add_apply, comp_apply,
        Pi.smul_apply, smul_eq_mul]
  rw [(hg.congr_of_eventuallyEq_abuse heq).mfderiv]
  intro h0
  -- The tangent spaces of `M` at `x` and of `ℝ` are `E` and `ℝ`, so the derivatives of `s` and `t`
  -- are linear maps `E →L[ℝ] ℝ`, in which the evaluation at a vector of `E` is a real number.
  set ds : E →L[ℝ] ℝ := mfderiv I 𝓘(ℝ) s x
  set dt : E →L[ℝ] ℝ := mfderiv I 𝓘(ℝ) t x
  have key (w : E) (hsw : ds w = 0) (htw : dt w ≠ 0) : False := by
    have h : ((0 : E →L[ℝ] ℝ) - ds + dt -
        ((1 : ℝ →L[ℝ] ℝ).smulRight (deriv μ r)).comp (ds + (2 : ℝ) • dt)) w = 0 :=
      congrArg (fun L ↦ L w) h0
    simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, smul_apply, zero_apply,
      ContinuousLinearMap.smulRight_apply, one_apply_eq_self, hsw, smul_eq_mul] at h
    have hμ' := hμa.deriv_nonpos (x := r)
    exact htw (by nlinarith [mul_self_nonneg (dt w)])
  exact key v hsv htv

end MilnorFunction

/-! ### The attachment theorem -/

section Attachment

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] {f s t : M → ℝ} {c ε : ℝ} {W : Set M}

/-- **Attaching the negative disc bundle across a Morse–Bott critical level** (Milnor's
Theorem 3.2 for a quadratic normal form). Let `f` be smooth and let `W` be an open tube on which
`f = c - s + t` for smooth functions `s, t ≥ 0`, the squared norms of the negative and the
positive normal components in a Morse–Bott normal form. Let `φ` scale the positive directions of
the tube: `φ (τ, x)` has the same `s` as `x` and `t` multiplied by `τ²`, `φ (1, x) = x`, and `φ`
fixes the points with `t = 0`. Suppose that at every point of the tube with `t ≠ 0` some tangent
vector is killed by `ds` but not by `dt`, that the part `{s + 2t ≤ 2ε}` of the tube is compact,
and that the band `f⁻¹[c - ε, c + ε]` is compact with its critical points in the tube.

Then the lower sublevel `{f ≤ c - ε}` together with the negative disc bundle
`{x ∈ W | t x = 0, s x ≤ ε}` is a strong deformation retract of `{f ≤ c + ε}`: there is a
retraction of `{f ≤ c + ε}` onto it, and a homotopy in `{f ≤ c + ε}` from this retraction to the
identity which fixes it pointwise. The disc bundle lies in `{f ≤ c}`, so intersecting with
`{f ≤ c + ε}` does not change the retract. -/
theorem exists_sublevel_union_negativeDiscBundle_deformation (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (hW : IsOpen W) (hs : ContMDiffOn I 𝓘(ℝ) ∞ s W) (ht : ContMDiffOn I 𝓘(ℝ) ∞ t W)
    (hs₀ : ∀ x ∈ W, 0 ≤ s x) (ht₀ : ∀ x ∈ W, 0 ≤ t x) (hf : ∀ x ∈ W, f x = c - s x + t x)
    (hdir : ∀ x ∈ W, t x ≠ 0 → ∃ v : TangentSpace I x,
      mfderiv I 𝓘(ℝ) s x v = 0 ∧ mfderiv I 𝓘(ℝ) t x v ≠ 0)
    (φ : C(unitInterval × W, W)) (hφs : ∀ τ x, s (φ (τ, x)) = s x)
    (hφt : ∀ τ x, t (φ (τ, x)) = τ ^ 2 * t x) (hφ₁ : ∀ x, φ (1, x) = x)
    (hφ₀ : ∀ τ (x : W), t x = 0 → φ (τ, x) = x) (hε : 0 < ε)
    (hK : IsCompact {x | x ∈ W ∧ s x + 2 * t x ≤ 2 * ε})
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) (c + ε)))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ W) :
    ∃ r : C({x | f x ≤ c + ε}, ↥({x | f x ≤ c + ε} ∩
        ({x | f x ≤ c - ε} ∪ {x | x ∈ W ∧ t x = 0 ∧ s x ≤ ε}))),
      (∀ x, r (ContinuousMap.inclusion inter_subset_left x) = x) ∧
      Nonempty (((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel
        (ContinuousMap.id _)
        {x | (x : M) ∈ {x | f x ≤ c - ε} ∪ {x | x ∈ W ∧ t x = 0 ∧ s x ≤ ε}}) := by
  -- Milnor's cutoff, equal to `2ε` on `(-∞, ε]` and to `0` on `[2ε, ∞)`.
  obtain ⟨μ, hμ, hμa, hμ_nonneg, hμ₀, hμ_eq, -⟩ :=
    exists_contDiff_antitone_cutoff (by linarith : ε < 2 * ε) (by positivity : 0 ≤ 2 * ε)
  set F := tubeMilnorFunction f s t W μ
  set S := {x | f x ≤ c - ε} ∪ {x | x ∈ W ∧ t x = 0 ∧ s x ≤ ε}
  set K := {x | x ∈ W ∧ s x + 2 * t x ≤ 2 * ε}
  have hF_of_mem {x : M} (hx : x ∈ W) : F x = c - s x + t x - μ (s x + 2 * t x) :=
    (tubeMilnorFunction_of_mem hx).trans (by rw [hf x hx])
  have hF_le (x : M) : F x ≤ f x := tubeMilnorFunction_le hμ_nonneg x
  have hFs : ContMDiff I 𝓘(ℝ) ∞ F := contMDiff_tubeMilnorFunction hμ₀ hK hfs hW hs ht hμ
  have hX : {x | F x ≤ c + ε} = {x | f x ≤ c + ε} :=
    setOf_tubeMilnorFunction_le hs₀ hf hμ₀ hμ_nonneg
  -- On the negative disc bundle, `F = c - s - 2ε ≤ c - ε`.
  have hSY : S ⊆ {x | F x ≤ c - ε} := by
    rintro x (hx | ⟨hxW, htx, hsx⟩)
    · exact (hF_le x).trans hx
    · rw [mem_ofPred_eq, hF_of_mem hxW, htx, mul_zero, add_zero, add_zero, hμ_eq _ hsx]
      linarith [hs₀ x hxW]
  have hab : c - ε ≤ c + ε := by linarith
  have hYX : {x | F x ≤ c - ε} ⊆ {x | F x ≤ c + ε} := fun _ hx ↦ le_trans hx hab
  have hFcompact : IsCompact (F ⁻¹' Icc (c - ε) (c + ε)) :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hFs.continuous) fun x hx ↦
      ⟨hx.1.trans (hF_le x), (Set.ext_iff.1 hX x).1 hx.2⟩
  -- `F` has no critical points in its band: on the tube where `t ≠ 0` by the transverse vector,
  -- on the tube where `t = 0` since there `F < c - ε`, and off the tube since `F = f` there.
  have hreg (x : M) (h₁ : c - ε ≤ F x) (h₂ : F x ≤ c + ε) : mfderiv I 𝓘(ℝ) F x ≠ 0 := by
    by_cases hxW : x ∈ W
    · by_cases htx : t x = 0
      · rw [hF_of_mem hxW, htx, mul_zero, add_zero, add_zero] at h₁
        rcases le_or_gt (s x) ε with h | h
        · rw [hμ_eq _ h] at h₁
          linarith [hs₀ x hxW]
        · linarith [hμ_nonneg (s x)]
      · exact mfderiv_tubeMilnorFunction_ne_zero hf hW hs ht hμ hμa hdir hxW htx
    · have hFx : F x = f x := tubeMilnorFunction_of_notMem hxW
      rw [(tubeMilnorFunction_eventuallyEq hμ₀ hK fun h ↦ hxW h.1).mfderiv_eq]
      exact fun h0 ↦ hxW (hcrit ⟨mem_criticalPoints_iff_mfderiv_eq_zero.2 h0, hFx ▸ h₁, hFx ▸ h₂⟩)
  -- Off `K`, a point of `{F ≤ c - ε}` lies in `{f ≤ c - ε}`.
  have hXK (x : M) (hx : x ∈ {x | F x ≤ c - ε}) (hxK : x ∉ K) : f x ≤ c - ε :=
    (tubeMilnorFunction_eq_of_notMem hμ₀ hxK).symm.trans_le hx
  -- Scaling the positive directions does not increase `F`.
  have hXφ (τ : unitInterval) (x : W) (hx : (x : M) ∈ {x | F x ≤ c - ε}) :
      (φ (τ, x) : M) ∈ {x | F x ≤ c - ε} := by
    have hτ : (τ : ℝ) ^ 2 ≤ 1 := pow_le_one₀ τ.2.1 τ.2.2
    have htx := ht₀ x x.2
    have hle := hμa (show s x + 2 * ((τ : ℝ) ^ 2 * t x) ≤ s x + 2 * t x by nlinarith)
    rw [mem_ofPred_eq, hF_of_mem x.2] at hx
    rw [mem_ofPred_eq, hF_of_mem (φ (τ, x)).2, hφs, hφt]
    nlinarith
  -- `{F ≤ c + ε}` retracts onto `{F ≤ c - ε}`, as `F` has no critical points in the compact band,
  -- which retracts onto `S` by scaling the positive directions.
  exact hX ▸ ContinuousMap.HomotopicRel.exists_inter_deformation_trans hYX
    (inter_subset_right.trans hSY)
    (sublevelInclusion_eq_inclusion F hab ▸ exists_sublevelDeformation hFs hab hFcompact hreg)
    (exists_inter_sublevel_union_negativeDiscBundle_deformation hφs hφt hφ₁ hφ₀ hW
      hs.continuousOn ht.continuousOn ht₀ hf hK.isClosed (fun _ hx ↦ hx.1) hXK hXφ)

end Attachment

end TauCeti
