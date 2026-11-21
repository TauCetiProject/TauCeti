/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.Morse.Deformation
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Manifold.Morse.MilnorFunction
import TauCeti.Topology.Compactness.LocallyCompact
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

A critical level may carry several critical submanifolds, each with its own normal form
`f ∘ Θ a = c - s a + t a` given by a partial diffeomorphism `Θ a : X a → M` near a compact core
`Z a`, where the spaces `X a` may have different dimensions. When the images `Θ a '' Z a` are
pairwise disjoint they have pairwise disjoint neighbourhoods, so for small `m` the tubes
`Θ a '' {s a + 2 t a < m}` are disjoint open subsets of `M`. On their union the functions `s a` and
`t a`, read through `Θ a⁻¹`, and the scalings of the positive directions glue to a single tube, and
crossing the level attaches all the disc bundles at once
(`TauCeti.exists_sublevel_union_iUnion_image_deformation`).

## Main results

* `TauCeti.exists_sublevel_union_negativeDiscBundle_deformation`: across a compact band around a
  critical level, the sublevel `M_{c+ε}` strong deformation retracts onto `M_{c-ε}` with the
  negative disc bundle of a quadratic normal form attached.
* `TauCeti.exists_sublevel_union_iUnion_image_deformation`: the same for finitely many normal forms
  `f ∘ Θ a = c - s a + t a`, each given by a partial diffeomorphism `Θ a` near a compact core, with
  pairwise disjoint cores and all small `ε > 0`, attaching all their disc bundles at once. The tube
  is the union of the images under `Θ a` of sublevels `{s a + 2 t a < m}`, which for small `m` have
  compact closed sublevels inside the source of `Θ a`
  (`TauCeti.exists_gt_setOf_lt_subset_and_isCompact`).

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
    constructor <;> nlinarith [τ.property.1, τ.property.2]⟩

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
  · refine .inr ⟨y.property, ?_, ?_⟩
    · rw [hφt, retractionScale_zero_eq_zero (ht₀ x hx) hs]
      simp
    · rw [hφs]
      exact hs.le
  · refine .inl ?_
    simp only [mem_ofPred_eq]
    rw [hf _ y.property, hφs, hφt]
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
    continuous_subtypeVal.comp continuous_snd
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  by_cases hp₀ : (p₀.2 : M) ∈ W
  swap
  · -- Off the tube, the retraction is the identity near `p₀`.
    have hpC : (p₀.2 : M) ∉ C := fun h ↦ hp₀ (hCW h)
    refine hval.continuousAt.congr (eventually_of_mem
      ((hC.isOpen_compl.preimage hval).mem_nhds hpC) fun q hq ↦ ?_)
    exact (hfix q.2 q.2.property hq q.1).symm
  -- On the tube, read the retraction on the open set of pairs whose point lies in `W`.
  set U := {p : unitInterval × X | (p.2 : M) ∈ W}
  have hU : IsOpen U := hW.preimage hval
  refine ContinuousWithinAt.continuousAt ?_ (hU.mem_nhds hp₀)
  rw [continuousWithinAt_iff_continuousAt_domRestrict _ (show p₀ ∈ U from hp₀)]
  set w : U → W := fun q ↦ ⟨q.val.2, q.property⟩
  have hw : Continuous w := (hval.comp continuous_subtypeVal).subtype_mk _
  have heq : U.domRestrict (fun p : unitInterval × X ↦ tubeRetraction φ s t ε p.1 p.2) =
      fun q ↦ (φ (retractionScale s t ε q.val.1 q.val.2, w q) : M) :=
    funext fun q ↦ tubeRetraction_of_mem (x := (q.val.2 : M)) q.val.1 q.property
  rw [heq]
  -- Where `t ≠ 0`, the scaling factor is continuous; where `t = 0`, `φ` fixes the point at all
  -- times, so the tube lemma over the compact `[0, 1]` applies whatever the scaling factor.
  have hst (g : M → ℝ) (hg : ContinuousOn g W) (q : U) :
      ContinuousAt (fun p : U ↦ g p.val.2) q :=
    ContinuousAt.comp (f := fun q : U ↦ ((q.val.2 : X) : M)) (hg.continuousAt
        (hW.mem_nhds q.property))
      (hval.comp continuous_subtypeVal).continuousAt
  have hκ (q : U) (hq : w q ∉ {y : W | t y = 0}) :
      ContinuousAt (fun p : U ↦ retractionScale s t ε p.val.1 p.val.2) q := by
    refine ContinuousAt.codRestrict (f := fun q : U ↦ (1 - (q.val.1 : ℝ)) *
      min 1 √((s q.val.2 - ε) / t q.val.2) + q.val.1) (fun q ↦ (retractionScale s t ε _ _).property)
          ?_
    have hτ : Continuous fun q : U ↦ (q.val.1 : ℝ) :=
      continuous_subtypeVal.comp (continuous_fst.comp continuous_subtypeVal)
    exact ((continuous_const.sub hτ).continuousAt.mul (continuousAt_const.min
      (((hst s hs q).sub continuousAt_const).div (hst t ht q) hq).sqrt)).add hτ.continuousAt
  exact (continuous_subtypeVal.comp (φ.continuous_apply_prodMk_of_fixed
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
  refine ⟨⟨fun x ↦ ⟨tubeRetraction φ s t ε 0 x, hGX x.property 0, hG0S x.property⟩,
      (hcont.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩,
    fun x ↦ Subtype.ext (hfixS x.property.2 0), ⟨?_⟩⟩
  exact
    { toFun p := ⟨tubeRetraction φ s t ε p.1 p.2, hGX p.2.property p.1⟩
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
private def tubeMilnorFunction : M → ℝ :=
  lowerOn (fun _ : Unit ↦ W) (fun _ y ↦ μ (s y + 2 * t y)) f

private theorem tubeMilnorFunction_of_mem (hx : x ∈ W) :
    tubeMilnorFunction f s t W μ x = f x - μ (s x + 2 * t x) :=
  lowerOn_of_mem (i := ()) Subsingleton.pairwise hx

private theorem tubeMilnorFunction_le (hμ : ∀ r, 0 ≤ μ r) (x : M) :
    tubeMilnorFunction f s t W μ x ≤ f x :=
  lowerOn_le (fun _ _ _ ↦ hμ _) x

variable (hs₀ : ∀ x ∈ W, 0 ≤ s x) (ht₀ : ∀ x ∈ W, 0 ≤ t x) (hf : ∀ x ∈ W, f x = c - s x + t x)
  (hμ₀ : ∀ r, 2 * ε ≤ r → μ r = 0)

include hs₀ hf hμ₀ in
/-- Milnor's function has the same sublevel `{F ≤ c + ε}` as `f`: where it is lowered,
`s + 2t < 2ε`, so `f = c - s + t < c + ε`. -/
private theorem setOf_tubeMilnorFunction_le (hμ : ∀ r, 0 ≤ μ r) :
    {x | tubeMilnorFunction f s t W μ x ≤ c + ε} = {x | f x ≤ c + ε} :=
  setOf_lowerOn_le Subsingleton.pairwise (fun _ _ _ ↦ hμ _) fun _ x hxW hμx ↦ by
    have h : s x + 2 * t x < 2 * ε := not_le.1 fun h ↦ hμx (hμ₀ _ h)
    rw [hf x hxW]
    linarith [hs₀ x hxW]

include hμ₀ in
/-- The lowering term of Milnor's function vanishes on the tube away from its part
`{s + 2t ≤ 2ε}`. -/
private theorem eqOn_zero_of_notMem_tube :
    EqOn (fun y ↦ μ (s y + 2 * t y)) 0 (W \ {x | x ∈ W ∧ s x + 2 * t x ≤ 2 * ε}) :=
  fun _ hy ↦ hμ₀ _ (not_le.1 fun h ↦ hy.2 ⟨hy.1, h⟩).le

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  (hK : IsCompact {x | x ∈ W ∧ s x + 2 * t x ≤ 2 * ε})

include hμ₀ hK in
/-- **Milnor's function is smooth.** The lowering term is supported in the compact part
`{s + 2t ≤ 2ε}` of the open tube, where it is smooth. -/
private theorem contMDiff_tubeMilnorFunction (hfs : ContMDiff I 𝓘(ℝ) ∞ f) (hW : IsOpen W)
    (hs : ContMDiffOn I 𝓘(ℝ) ∞ s W) (ht : ContMDiffOn I 𝓘(ℝ) ∞ t W) (hμs : ContDiff ℝ ∞ μ) :
    ContMDiff I 𝓘(ℝ) ∞ (tubeMilnorFunction f s t W μ) :=
  contMDiff_lowerOn (K := fun _ ↦ {x | x ∈ W ∧ s x + 2 * t x ≤ 2 * ε})
    (fun _ ↦ eqOn_zero_of_notMem_tube hμ₀) (fun _ ↦ hK.isClosed) (fun _ ↦ hW)
    (fun _ _ hx ↦ hx.1) hfs fun _ ↦
    -- `μ (a + 2 b)` is a smooth function of `(a, b) = (s y, t y)`.
    have hg : ContDiff ℝ ∞ fun p : ℝ × ℝ ↦ μ (p.1 + 2 * p.2) := hμs.comp (by fun_prop)
    hg.contMDiff.comp_contMDiffOn (hs.prodMk_space ht)

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
    · exact mfderiv_lowerOn_ne_zero_of_forall_notMem (K := fun _ ↦ K)
        (fun _ ↦ eqOn_zero_of_notMem_tube hμ₀) (fun _ ↦ hK.isClosed) (fun _ _ hx ↦ hx.1)
        (hcrit.trans (subset_iUnion (fun _ : Unit ↦ W) ())) (fun _ ↦ hxW) ⟨h₁, h₂⟩
  -- Off `K`, a point of `{F ≤ c - ε}` lies in `{f ≤ c - ε}`.
  have hXK (x : M) (hx : x ∈ {x | F x ≤ c - ε}) (hxK : x ∉ K) : f x ≤ c - ε :=
    (lowerOn_eq_of_notMem (K := fun _ ↦ K) (fun _ ↦ eqOn_zero_of_notMem_tube hμ₀)
      (by rwa [iUnion_const])).symm.trans_le hx
  -- Scaling the positive directions does not increase `F`.
  have hXφ (τ : unitInterval) (x : W) (hx : (x : M) ∈ {x | F x ≤ c - ε}) :
      (φ (τ, x) : M) ∈ {x | F x ≤ c - ε} := by
    have hτ : (τ : ℝ) ^ 2 ≤ 1 := pow_le_one₀ τ.property.1 τ.property.2
    have htx := ht₀ x x.property
    have hle := hμa (show s x + 2 * ((τ : ℝ) ^ 2 * t x) ≤ s x + 2 * t x by nlinarith)
    rw [mem_ofPred_eq, hF_of_mem x.property] at hx
    rw [mem_ofPred_eq, hF_of_mem (φ (τ, x)).property, hφs, hφt]
    nlinarith
  -- `{F ≤ c + ε}` retracts onto `{F ≤ c - ε}`, as `F` has no critical points in the compact band,
  -- which retracts onto `S` by scaling the positive directions.
  exact hX ▸ ContinuousMap.HomotopicRel.exists_inter_deformation_trans hYX
    (inter_subset_right.trans hSY)
    (sublevelInclusion_eq_inclusion F hab ▸ exists_sublevelDeformation hFs hab hFcompact hreg)
    (exists_inter_sublevel_union_negativeDiscBundle_deformation hφs hφt hφ₁ hφ₀ hW
      hs.continuousOn ht.continuousOn ht₀ hf hK.isClosed (fun _ hx ↦ hx.1) hXK hXφ)

end Attachment

/-! ### The attachment theorem through a partial diffeomorphism -/

section Transport

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- If a curve `γ` through `y` keeps `u` constant and `v` equal to `τ² b` near `τ = 1`, with
`b ≠ 0`, then its velocity at `τ = 1` is killed by `du` but not by `dv`. -/
private theorem exists_mfderiv_apply_eq_zero_and_ne_zero {u v : M → ℝ} {γ : ℝ → M} {y : M}
    {a b : ℝ} (hγ : MDifferentiableAt 𝓘(ℝ) I γ 1) (hγy : γ 1 = y)
    (hu : MDifferentiableAt I 𝓘(ℝ) u y) (hv : MDifferentiableAt I 𝓘(ℝ) v y)
    (huγ : u ∘ γ =ᶠ[𝓝 1] fun _ ↦ a) (hvγ : v ∘ γ =ᶠ[𝓝 1] fun τ ↦ τ ^ 2 * b) (hb : b ≠ 0) :
    ∃ w : TangentSpace I y, mfderiv I 𝓘(ℝ) u y w = 0 ∧ mfderiv I 𝓘(ℝ) v y w ≠ 0 := by
  subst hγy
  have hdu := mfderiv_comp_apply (I' := I) 1 hu hγ (1 : ℝ)
  have hdv := mfderiv_comp_apply (I' := I) 1 hv hγ (1 : ℝ)
  rw [huγ.mfderiv_eq, mfderiv_const] at hdu
  rw [(((hasDerivAt_pow 2 (1 : ℝ)).mul_const b).hasFDerivAt.hasMFDerivAt.congr_of_eventuallyEq_abuse
    hvγ).mfderiv] at hdv
  refine ⟨mfderiv 𝓘(ℝ) I γ 1 (1 : ℝ), hdu.symm, fun h0 ↦ hb ?_⟩
  rw [h0] at hdv
  -- The tangent spaces of `ℝ` are `ℝ`, so the derivative of `τ ↦ τ² b` at `1` is a multiple of `b`.
  exact (mul_eq_zero.1 ((ContinuousLinearMap.toSpanSingleton_apply_one (M₁ := ℝ) ℝ _).symm.trans
    hdv)).resolve_left (by norm_num)

variable {F G X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {K : ModelWithCorners ℝ F G} [TopologicalSpace X] [ChartedSpace G X]

/-- The image under a partial diffeomorphism `Θ` of a subset `W` of its source lies in its target,
and `Θ⁻¹` maps it back into `W`. -/
private theorem image_subset_target_and_symm_mem (Θ : PartialDiffeomorph K I X M ∞) {W : Set X}
    (hWΘ : W ⊆ Θ.source) : Θ '' W ⊆ Θ.target ∧ ∀ y ∈ Θ '' W, Θ.toPartialEquiv.symm y ∈ W := by
  refine ⟨image_subset_iff.2 fun x hx ↦ Θ.map_source (hWΘ hx), ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rwa [Θ.left_inv (hWΘ hx)]

/-- Let `s` and `t` be smooth on `X`, and let `ρ b` preserve `s` and multiply `t` by `b²`, with
`ρ 1 = id`. At a point `x` of the source of `Θ` with `t x ≠ 0`, the velocity at `b = 1` of the
curve `b ↦ Θ (ρ b x)` is killed by the derivative of `s ∘ Θ⁻¹` but not by that of `t ∘ Θ⁻¹`. -/
private theorem exists_mfderiv_comp_symm_apply_eq_zero_and_ne_zero
    (Θ : PartialDiffeomorph K I X M ∞) {s t : X → ℝ} (hs : ContMDiff K 𝓘(ℝ) ∞ s)
    (ht : ContMDiff K 𝓘(ℝ) ∞ t) (ρ : ℝ → X → X) (hρ : Continuous fun p : ℝ × X ↦ ρ p.1 p.2)
    (hρd : ∀ x, MDifferentiableAt 𝓘(ℝ) K (fun b ↦ ρ b x) 1) (hρs : ∀ b x, s (ρ b x) = s x)
    (hρt : ∀ b x, t (ρ b x) = b ^ 2 * t x) (hρ₁ : ∀ x, ρ 1 x = x) {x : X} (hx : x ∈ Θ.source)
    (htx : t x ≠ 0) : ∃ v : TangentSpace I (Θ x),
      mfderiv I 𝓘(ℝ) (s ∘ Θ.toPartialEquiv.symm) (Θ x) v = 0 ∧
        mfderiv I 𝓘(ℝ) (t ∘ Θ.toPartialEquiv.symm) (Θ x) v ≠ 0 := by
  have hΘs : ContMDiffAt I K ∞ Θ.toPartialEquiv.symm (Θ x) :=
    Θ.symm.contMDiffOn.contMDiffAt (Θ.open_target.mem_nhds (Θ.map_source hx))
  have hev : ∀ᶠ b in 𝓝 (1 : ℝ), ρ b x ∈ Θ.source :=
    (hρ.comp (continuous_id.prodMk continuous_const)).continuousAt.preimage_mem_nhds
      (Θ.open_source.mem_nhds (by simpa [hρ₁] using hx))
  refine exists_mfderiv_apply_eq_zero_and_ne_zero (γ := fun b ↦ Θ (ρ b x)) (a := s x)
    ((Θ.mdifferentiableAt (by simp) (by rwa [hρ₁])).comp (I' := K) 1 (hρd x))
    (by simp only [hρ₁]) (((hs _).comp _ hΘs).mdifferentiableAt (by simp))
    (((ht _).comp _ hΘs).mdifferentiableAt (by simp)) (hev.mono fun b hb ↦ ?_)
    (hev.mono fun b hb ↦ ?_) htx
  · simp only [comp_apply, Θ.left_inv hb, hρs]
  · simp only [comp_apply, Θ.left_inv hb, hρt]

end Transport

/-! ### Several normal forms with disjoint cores -/

section Family

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {ι : Type*}
  {F G X : ι → Type*} [∀ a, NormedAddCommGroup (F a)] [∀ a, NormedSpace ℝ (F a)]
  [∀ a, TopologicalSpace (G a)] {K : ∀ a, ModelWithCorners ℝ (F a) (G a)}
  [∀ a, TopologicalSpace (X a)] [∀ a, ChartedSpace (G a) (X a)]

/-- The scalings `ρ a` of the positive directions of open subsets `W a` of the sources of partial
diffeomorphisms `Θ a` with pairwise disjoint images, carried to the union of these images: at
time `τ` the point `Θ a x` goes to `Θ a (ρ a τ x)`. -/
private theorem exists_continuousMap_iUnion_image (Θ : ∀ a, PartialDiffeomorph (K a) I (X a) M ∞)
    (ρ : ∀ a, ℝ → X a → X a) (hρ : ∀ a, Continuous fun p : ℝ × X a ↦ ρ a p.1 p.2)
    {W : ∀ a, Set (X a)} (hWo : ∀ a, IsOpen (W a)) (hWΘ : ∀ a, W a ⊆ (Θ a).source)
    (hρW : ∀ a, ∀ τ : unitInterval, ∀ x ∈ W a, ρ a τ x ∈ W a)
    (hd : Pairwise (Disjoint on fun a ↦ Θ a '' W a)) :
    ∃ φ : C(unitInterval × ⋃ a, Θ a '' W a, ⋃ a, Θ a '' W a),
      ∀ a τ, ∀ x (hx : x ∈ W a), (φ (τ, ⟨Θ a x, mem_iUnion_of_mem a (mem_image_of_mem _ hx)⟩) : M) =
        Θ a (ρ a τ x) := by
  set T := fun a ↦ Θ a '' W a
  have hTo (a : ι) : IsOpen (T a) :=
    (Θ a).toOpenPartialHomeomorph.isOpen_image_of_subset_source (hWo a) (hWΘ a)
  -- On the part over `T a`, the scaling is the one of `Θ a`.
  let ψ (a : ι) : C({p : unitInterval × ⋃ b, T b | (p.2 : M) ∈ T a}, ⋃ b, T b) :=
    ⟨fun p ↦ ⟨Θ a (ρ a p.val.1 ((Θ a).toPartialEquiv.symm p.val.2)), mem_iUnion_of_mem a
      (mem_image_of_mem _ (hρW a _ _ ((image_subset_target_and_symm_mem _
          (hWΘ a)).2 _ p.property)))⟩,
    ((Θ a).contMDiffOn.continuousOn.comp_continuous ((hρ a).comp
      ((continuous_subtypeVal.comp (continuous_fst.comp continuous_subtypeVal)).prodMk
        ((Θ a).symm.contMDiffOn.continuousOn.comp_continuous
          (continuous_subtypeVal.comp (continuous_snd.comp continuous_subtypeVal))
          fun p ↦ (image_subset_target_and_symm_mem _ (hWΘ a)).1 p.property)))
      fun p ↦ hWΘ a (hρW a _ _ ((image_subset_target_and_symm_mem _
          (hWΘ a)).2 _ p.property))).subtype_mk
        _⟩
  refine ⟨ContinuousMap.liftCover (fun a ↦ {p | (p.2 : M) ∈ T a}) ψ
    (fun a b p ha hb ↦ ?_) (fun p ↦ ?_), fun a τ x hx ↦ ?_⟩
  · obtain rfl : a = b := by_contra fun hab ↦ (hd hab).ne_of_mem ha hb rfl
    rfl
  · obtain ⟨a, ha⟩ := mem_iUnion.1 p.2.property
    exact ⟨a, ((hTo a).preimage (continuous_subtypeVal.comp continuous_snd)).mem_nhds ha⟩
  · rw [ContinuousMap.liftCover_coe (i := a) ⟨_, mem_image_of_mem _ hx⟩]
    -- By definition `ψ a` sends `(τ, Θ a x)` to `Θ a (ρ a τ (Θ a⁻¹ (Θ a x)))`.
    exact congrArg (fun y ↦ Θ a (ρ a τ y)) ((Θ a).left_inv (hWΘ a hx))

variable [Finite ι]

/-- Functions `u a` on open subsets `W a` of the sources of partial diffeomorphisms `Θ a` with
pairwise disjoint images, read on `M` through `Θ a⁻¹`, glue to a function `glue u` on `M` which
agrees with `u a ∘ Θ a⁻¹` near each point of `Θ a '' W a`, so that `glue u (Θ a x) = u a x` for
`x ∈ W a`, is smooth on the union of the images if the `u a` are, and is nonnegative if the `u a`
are. -/
private theorem exists_glue (Θ : ∀ a, PartialDiffeomorph (K a) I (X a) M ∞) {W : ∀ a, Set (X a)}
    (hWo : ∀ a, IsOpen (W a)) (hWΘ : ∀ a, W a ⊆ (Θ a).source)
    (hd : Pairwise (Disjoint on fun a ↦ Θ a '' W a)) :
    ∃ glue : (∀ a, X a → ℝ) → M → ℝ,
      (∀ u a, ∀ x ∈ W a, glue u =ᶠ[𝓝 (Θ a x)] u a ∘ (Θ a).toPartialEquiv.symm) ∧
      (∀ u a, ∀ x ∈ W a, glue u (Θ a x) = u a x) ∧
      (∀ u, (∀ a, ContMDiff (K a) 𝓘(ℝ) ∞ (u a)) →
        ContMDiffOn I 𝓘(ℝ) ∞ (glue u) (⋃ a, Θ a '' W a)) ∧
      (∀ u, (∀ a x, 0 ≤ u a x) → ∀ y, 0 ≤ glue u y) ∧
      ∀ (u v : ∀ a, X a → ℝ) (p : ℝ → ℝ → Prop),
        {y | y ∈ ⋃ a, Θ a '' W a ∧ p (glue u y) (glue v y)} =
          ⋃ a, Θ a '' {x | x ∈ W a ∧ p (u a x) (v a x)} := by
  have := Fintype.ofFinite ι
  obtain ⟨glue, hglue_def⟩ : ∃ glue : (∀ a, X a → ℝ) → M → ℝ, ∀ u y,
      glue u y = ∑ a, (Θ a '' W a).indicator (u a ∘ (Θ a).toPartialEquiv.symm) y :=
    ⟨_, fun _ _ ↦ rfl⟩
  have hglue (u : ∀ a, X a → ℝ) (a : ι) (x : X a) (hx : x ∈ W a) :
      glue u =ᶠ[𝓝 (Θ a x)] u a ∘ (Θ a).toPartialEquiv.symm := by
    have hTo : IsOpen (Θ a '' W a) :=
      (Θ a).toOpenPartialHomeomorph.isOpen_image_of_subset_source (hWo a) (hWΘ a)
    filter_upwards [hTo.mem_nhds (mem_image_of_mem _ hx)] with y hy
    rw [hglue_def, Finset.sum_eq_single a (fun b _ hba ↦ indicator_of_notMem
      (fun hb ↦ (hd hba).ne_of_mem hb hy rfl) _) (by simp), indicator_of_mem hy]
  have hglueΘ (u : ∀ a, X a → ℝ) (a : ι) (x : X a) (hx : x ∈ W a) : glue u (Θ a x) = u a x := by
    rw [(hglue u a x hx).eq_of_nhds, comp_apply, (Θ a).left_inv (hWΘ a hx)]
  refine ⟨glue, hglue, hglueΘ, fun u hu ↦ ?_, fun u hu y ↦ (hglue_def u y).symm ▸
    Finset.sum_nonneg fun a _ ↦ indicator_nonneg (fun _ _ ↦ hu _ _) _, fun u v p ↦ ?_⟩
  · rintro _ hy
    obtain ⟨a, x, hx, rfl⟩ := mem_iUnion.1 hy
    exact (((hu a).contMDiffAt.comp _ ((Θ a).symm.contMDiffOn.contMDiffAt
      ((Θ a).open_target.mem_nhds ((Θ a).map_source (hWΘ a hx))))).congr_of_eventuallyEq
      (hglue u a x hx)).contMDiffWithinAt
  · ext y
    simp only [mem_ofPred_eq, mem_iUnion, mem_image]
    refine ⟨fun ⟨⟨a, x, hx, hxy⟩, hpy⟩ ↦ ⟨a, x, ⟨hx, ?_⟩, hxy⟩, fun ⟨a, x, ⟨hx, hpx⟩, hxy⟩ ↦
      ⟨⟨a, x, hx, hxy⟩, ?_⟩⟩
    · rwa [← hxy, hglueΘ u a x hx, hglueΘ v a x hx] at hpy
    · rwa [← hxy, hglueΘ u a x hx, hglueΘ v a x hx]

variable [T2Space M]

/-- Let `q a ≥ 0` be continuous functions on locally compact Hausdorff spaces `X a`, vanishing
exactly on compact subsets `Z a` of the sources of partial diffeomorphisms `Θ a`, whose images
`Θ a '' Z a` are pairwise disjoint, and suppose every point of `X a` is joined to `Z a` by a
preconnected set on which `q a` does not increase. Then for some `m > 0` the sublevels
`{q a < m}` lie in the sources of `Θ a`, have pairwise disjoint images, and their closed versions
`{q a ≤ δ}`, `δ < m`, are compact. -/
private theorem exists_pairwise_disjoint_image_setOf_lt [∀ a, LocallyCompactSpace (X a)]
    [∀ a, T2Space (X a)] (Θ : ∀ a, PartialDiffeomorph (K a) I (X a) M ∞) {Z : ∀ a, Set (X a)}
    (hZ : ∀ a, IsCompact (Z a)) (hZΘ : ∀ a, Z a ⊆ (Θ a).source)
    (hZd : Pairwise (Disjoint on fun a ↦ Θ a '' Z a)) {q : ∀ a, X a → ℝ}
    (hq : ∀ a, Continuous (q a)) (hqZ : ∀ a x, q a x ≤ 0 → x ∈ Z a)
    (hpath : ∀ a x, ∃ C : Set (X a), IsPreconnected C ∧ x ∈ C ∧ (C ∩ Z a).Nonempty ∧
      ∀ y ∈ C, q a y ≤ q a x) :
    ∃ m > 0, (∀ a, {x | q a x < m} ⊆ (Θ a).source) ∧
      (∀ a, ∀ δ < m, IsCompact {x | q a x ≤ δ}) ∧
      Pairwise (Disjoint on fun a ↦ Θ a '' {x | q a x < m}) := by
  have hZc (a : ι) : IsCompact (Θ a '' Z a) :=
    (hZ a).image_of_continuousOn ((Θ a).contMDiffOn.continuousOn.mono (hZΘ a))
  -- The compact cores have pairwise disjoint open neighbourhoods `U a`.
  obtain ⟨U, hU, hUd⟩ := Pairwise.exists_mem_filter_of_disjoint fun a b hab ↦
    separatedNhds_iff_disjoint.1 (SeparatedNhds.of_isCompact_isCompact (hZc a) (hZc b) (hZd hab))
  have hO (a : ι) : IsOpen ((Θ a).source ∩ Θ a ⁻¹' interior (U a)) :=
    (Θ a).contMDiffOn.continuousOn.isOpen_inter_preimage (Θ a).open_source isOpen_interior
  choose m hm hmO hmK using fun a ↦ exists_gt_setOf_lt_subset_and_isCompact (hZ a) (hO a)
    (fun x hx ↦ ⟨hZΘ a hx, subset_interior_iff_mem_nhdsSet.2 (hU a) (mem_image_of_mem _ hx)⟩)
    (hq a) (hqZ a) (hpath a)
  obtain ⟨m₀, hm₀, hm₀m⟩ : ∃ m₀ > 0, ∀ a, m₀ ≤ m a := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact ⟨1, one_pos, fun a ↦ hι.elim a⟩
    · obtain ⟨a₀, ha₀⟩ := Finite.exists_min m
      exact ⟨m a₀, hm a₀, ha₀⟩
  have hsub (a : ι) : {x | q a x < m₀} ⊆ (Θ a).source ∩ Θ a ⁻¹' interior (U a) :=
    fun x hx ↦ hmO a (lt_of_lt_of_le hx (hm₀m a))
  refine ⟨m₀, hm₀, fun a x hx ↦ (hsub a hx).1, fun a δ hδ ↦ hmK a δ (hδ.trans_le (hm₀m a)),
    fun a b hab ↦ (hUd hab).mono ?_ ?_⟩ <;>
  · rintro _ ⟨x, hx, rfl⟩
    exact interior_subset (hsub _ hx).2

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] {f : M → ℝ} {c : ℝ}

/-- The attachment theorem `TauCeti.exists_sublevel_union_negativeDiscBundle_deformation`, read
through finitely many partial diffeomorphisms `Θ a : X a → M`. On `X a`, the functions
`s a, t a ≥ 0` are smooth with `f ∘ Θ a = c - s a + t a`, and `ρ a b` scales the positive
directions: it preserves `s a`, multiplies `t a` by `b²`, is the identity for `b = 1` and fixes the
points with `t a = 0`. If the `W a ⊆ X a` are open subsets of the sources preserved by `ρ a τ` for
`τ ∈ [0, 1]`, with pairwise disjoint images, containing the disc bundles `{t a = 0, s a ≤ ε}`,
whose parts `{s a + 2 t a ≤ 2ε}` are compact and whose images contain the critical points of the
compact band `f⁻¹[c - ε, c + ε]`, then `{f ≤ c + ε}` strong deformation retracts onto
`{f ≤ c - ε}` with the images of the disc bundles attached. -/
private theorem exists_sublevel_union_iUnion_image_deformation_of_tube
    (hfs : ContMDiff I 𝓘(ℝ) ∞ f) (Θ : ∀ a, PartialDiffeomorph (K a) I (X a) M ∞)
    {s t : ∀ a, X a → ℝ} (hs : ∀ a, ContMDiff (K a) 𝓘(ℝ) ∞ (s a))
    (ht : ∀ a, ContMDiff (K a) 𝓘(ℝ) ∞ (t a)) (hs₀ : ∀ a x, 0 ≤ s a x) (ht₀ : ∀ a x, 0 ≤ t a x)
    (hf : ∀ a, ∀ x ∈ (Θ a).source, f (Θ a x) = c - s a x + t a x) (ρ : ∀ a, ℝ → X a → X a)
    (hρ : ∀ a, Continuous fun p : ℝ × X a ↦ ρ a p.1 p.2)
    (hρd : ∀ a x, MDifferentiableAt 𝓘(ℝ) (K a) (fun b ↦ ρ a b x) 1)
    (hρs : ∀ a b x, s a (ρ a b x) = s a x) (hρt : ∀ a b x, t a (ρ a b x) = b ^ 2 * t a x)
    (hρ₁ : ∀ a x, ρ a 1 x = x) (hρ₀ : ∀ a b x, t a x = 0 → ρ a b x = x) {W : ∀ a, Set (X a)}
    (hWo : ∀ a, IsOpen (W a)) (hWΘ : ∀ a, W a ⊆ (Θ a).source)
    (hρW : ∀ a, ∀ τ : unitInterval, ∀ x ∈ W a, ρ a τ x ∈ W a)
    (hWd : Pairwise (Disjoint on fun a ↦ Θ a '' W a)) {ε : ℝ} (hε : 0 < ε)
    (hD : ∀ a x, t a x = 0 → s a x ≤ ε → x ∈ W a)
    (hK : ∀ a, IsCompact {x | x ∈ W a ∧ s a x + 2 * t a x ≤ 2 * ε})
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) (c + ε)))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ ⋃ a, Θ a '' W a) :
    ∃ r : C({y | f y ≤ c + ε}, ↥({y | f y ≤ c + ε} ∩
        ({y | f y ≤ c - ε} ∪ ⋃ a, Θ a '' {x | t a x = 0 ∧ s a x ≤ ε}))),
      (∀ y, r (ContinuousMap.inclusion inter_subset_left y) = y) ∧
      Nonempty (((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel
        (ContinuousMap.id _)
        {y | (y : M) ∈ {y | f y ≤ c - ε} ∪ ⋃ a, Θ a '' {x | t a x = 0 ∧ s a x ≤ ε}}) := by
  -- The functions `s` and `t`, glued on the union `T` of the tubes `Θ a '' W a`; a condition on
  -- the values of `s a` and `t a` reads on `T` through `glue s` and `glue t`.
  set T := ⋃ a, Θ a '' W a
  have hTo : IsOpen T := isOpen_iUnion fun a ↦
    (Θ a).toOpenPartialHomeomorph.isOpen_image_of_subset_source (hWo a) (hWΘ a)
  obtain ⟨glue, hglue, hglueΘ, hsmooth, hglue₀, himage⟩ := exists_glue Θ hWo hWΘ hWd
  -- The scaling of the positive directions; every point of `T` is `Θ a x` with `x ∈ W a`.
  obtain ⟨φ, hφ⟩ := exists_continuousMap_iUnion_image Θ ρ hρ hWo hWΘ hρW hWd
  have hT (y : T) : ∃ a x, ∃ hx : x ∈ W a,
      y = ⟨Θ a x, mem_iUnion_of_mem a (mem_image_of_mem _ hx)⟩ := by
    obtain ⟨a, x, hx, hxy⟩ := mem_iUnion.1 y.property
    exact ⟨a, x, hx, Subtype.ext hxy.symm⟩
  have key := exists_sublevel_union_negativeDiscBundle_deformation hfs hTo (hsmooth s hs)
    (hsmooth t ht) (fun y _ ↦ hglue₀ s hs₀ y) (fun y _ ↦ hglue₀ t ht₀ y) ?_ ?_ φ ?_ ?_ ?_ ?_ hε ?_
    hcompact hcrit
  · have hDW (a : ι) : {x | x ∈ W a ∧ (t a x = 0 ∧ s a x ≤ ε)} = {x | t a x = 0 ∧ s a x ≤ ε} :=
      Set.ext fun x ↦ ⟨And.right, fun hx ↦ ⟨hD a x hx.1 hx.2, hx⟩⟩
    rwa [himage s t (fun u v ↦ v = 0 ∧ u ≤ ε), iUnion_congr fun a ↦ congrArg (Θ a '' ·) (hDW a)]
      at key
  · rintro _ hy
    obtain ⟨a, x, hx, rfl⟩ := mem_iUnion.1 hy
    rw [hf a x (hWΘ a hx), hglueΘ s a x hx, hglueΘ t a x hx]
  · rintro _ hy hty
    obtain ⟨a, x, hx, rfl⟩ := mem_iUnion.1 hy
    obtain ⟨v, hv₀, hv₁⟩ := exists_mfderiv_comp_symm_apply_eq_zero_and_ne_zero (Θ a) (hs a)
      (ht a) (ρ a) (hρ a) (hρd a) (hρs a) (hρt a) (hρ₁ a) (hWΘ a hx)
      (by rwa [hglueΘ t a x hx] at hty)
    refine ⟨v, ?_, ?_⟩
    · rw [(hglue s a x hx).mfderiv_eq, ContinuousLinearMap.comp_apply, hv₀, map_zero]
    · rw [(hglue t a x hx).mfderiv_eq, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe]
      exact EmbeddingLike.map_ne_zero_iff.2 hv₁
  · intro τ y
    obtain ⟨a, x, hx, rfl⟩ := hT y
    rw [hφ a τ x hx, hglueΘ s a _ (hρW a τ x hx), hglueΘ s a x hx, hρs]
  · intro τ y
    obtain ⟨a, x, hx, rfl⟩ := hT y
    rw [hφ a τ x hx, hglueΘ t a _ (hρW a τ x hx), hglueΘ t a x hx, hρt]
  · intro y
    obtain ⟨a, x, hx, rfl⟩ := hT y
    exact Subtype.ext ((hφ a 1 x hx).trans (by rw [Set.Icc.coe_one, hρ₁]))
  · intro τ y hty
    obtain ⟨a, x, hx, rfl⟩ := hT y
    exact Subtype.ext ((hφ a τ x hx).trans (by rw [hρ₀ a _ x (by rwa [hglueΘ t a x hx] at hty)]))
  · rw [himage s t (fun u v ↦ u + 2 * v ≤ 2 * ε)]
    exact isCompact_iUnion fun a ↦ (hK a).image_of_continuousOn
      ((Θ a).contMDiffOn.continuousOn.mono fun x hx ↦ hWΘ a hx.1)

/-- **Attaching the negative disc bundles of several normal forms with disjoint cores.** For each
`a` in a finite index type, let `Θ a : X a → M` be a smooth partial diffeomorphism from a locally
compact Hausdorff manifold, with a normal form `f ∘ Θ a = c - s a + t a` on the source of `Θ a`:
the smooth functions `s a, t a ≥ 0` on `X a` vanish together exactly on a compact core `Z a` in the
source of `Θ a`. Let the maps `σ a b' b : X a → X a`, continuous jointly in `b'`, `b` and the point,
rescale `s a` by `b'²` and `t a` by `b²`; let `σ a 1 1` be the identity, `σ a 1 b` fix the points
with `t a = 0` and be differentiable in `b` at `b = 1`, and let `σ a 0 0` map into `Z a`. Suppose
the images `Θ a '' Z a` of the cores are pairwise disjoint; they are, for instance, the critical
submanifolds of `f` on the level `c`.

Then there is an `ε₀ > 0` such that for `0 < ε < ε₀`, if the band `f⁻¹[c - ε, c + ε]` is compact
and its critical points lie in the union of the `Θ a '' Z a`, each disc bundle
`D a ε = {t a = 0, s a ≤ ε}` lies in the source of `Θ a`, the images `Θ a (D a ε)` are pairwise
disjoint, and `{f ≤ c - ε} ∪ ⋃ a, Θ a (D a ε)` is a strong deformation retract of
`{f ≤ c + ε}`: there is a retraction of `{f ≤ c + ε}` onto it, and a homotopy in `{f ≤ c + ε}`
from this retraction to the identity which fixes it pointwise. This is
`TauCeti.exists_sublevel_union_negativeDiscBundle_deformation` for the tube
`⋃ a, Θ a '' {s a + 2 t a < m}` with `m > 0` so small that these pieces are disjoint. -/
theorem exists_sublevel_union_iUnion_image_deformation [∀ a, LocallyCompactSpace (X a)]
    [∀ a, T2Space (X a)] (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (Θ : ∀ a, PartialDiffeomorph (K a) I (X a) M ∞) {s t : ∀ a, X a → ℝ}
    (hs : ∀ a, ContMDiff (K a) 𝓘(ℝ) ∞ (s a)) (ht : ∀ a, ContMDiff (K a) 𝓘(ℝ) ∞ (t a))
    (hs₀ : ∀ a x, 0 ≤ s a x) (ht₀ : ∀ a x, 0 ≤ t a x)
    (hf : ∀ a, ∀ x ∈ (Θ a).source, f (Θ a x) = c - s a x + t a x) {Z : ∀ a, Set (X a)}
    (hZ : ∀ a, IsCompact (Z a)) (hZΘ : ∀ a, Z a ⊆ (Θ a).source)
    (hZst : ∀ a, ∀ x ∈ Z a, s a x = 0 ∧ t a x = 0) (hstZ : ∀ a x, s a x = 0 → t a x = 0 → x ∈ Z a)
    (hZd : Pairwise (Disjoint on fun a ↦ Θ a '' Z a)) (σ : ∀ a, ℝ → ℝ → X a → X a)
    (hσ : ∀ a, Continuous fun p : (ℝ × ℝ) × X a ↦ σ a p.1.1 p.1.2 p.2)
    (hσd : ∀ a x, MDifferentiableAt 𝓘(ℝ) (K a) (fun b ↦ σ a 1 b x) 1)
    (hσs : ∀ a b' b x, s a (σ a b' b x) = b' ^ 2 * s a x)
    (hσt : ∀ a b' b x, t a (σ a b' b x) = b ^ 2 * t a x) (hσ₁ : ∀ a x, σ a 1 1 x = x)
    (hσ₀ : ∀ a b x, t a x = 0 → σ a 1 b x = x) (hσZ : ∀ a x, σ a 0 0 x ∈ Z a) :
    ∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀, IsCompact (f ⁻¹' Icc (c - ε) (c + ε)) →
      criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ ⋃ a, Θ a '' Z a →
      (∀ a, {x | t a x = 0 ∧ s a x ≤ ε} ⊆ (Θ a).source) ∧
      Pairwise (Disjoint on fun a ↦ Θ a '' {x | t a x = 0 ∧ s a x ≤ ε}) ∧
      ∃ r : C({y | f y ≤ c + ε}, ↥({y | f y ≤ c + ε} ∩
          ({y | f y ≤ c - ε} ∪ ⋃ a, Θ a '' {x | t a x = 0 ∧ s a x ≤ ε}))),
        (∀ y, r (ContinuousMap.inclusion inter_subset_left y) = y) ∧
        Nonempty (((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel
          (ContinuousMap.id _)
          {y | (y : M) ∈ {y | f y ≤ c - ε} ∪ ⋃ a, Θ a '' {x | t a x = 0 ∧ s a x ≤ ε}}) := by
  set q : ∀ a, X a → ℝ := fun a x ↦ s a x + 2 * t a x with hq_def
  have hq (a : ι) : Continuous (q a) :=
    (hs a).continuous.add (continuous_const.mul (ht a).continuous)
  have hq_le (a : ι) (b' b : ℝ) (hb' : b' ^ 2 ≤ 1) (hb : b ^ 2 ≤ 1) (x : X a) :
      q a (σ a b' b x) ≤ q a x := by
    simp only [hq_def, hσs, hσt]
    nlinarith [hs₀ a x, ht₀ a x]
  -- The rays `b ↦ σ a b b x`, `b ∈ [0, 1]`, join each point to the core, with `q a` at most
  -- `q a x`, so small sublevels `{q a < m}` are disjoint tubes around the cores.
  obtain ⟨m, hm, hmΘ, hmK, hmd⟩ := exists_pairwise_disjoint_image_setOf_lt Θ hZ hZΘ hZd hq
    (fun a x (hx : s a x + 2 * t a x ≤ 0) ↦
      hstZ a x (by linarith [hs₀ a x, ht₀ a x]) (by linarith [hs₀ a x, ht₀ a x]))
    fun a x ↦ ⟨(fun b ↦ σ a b b x) '' Icc 0 1, isPreconnected_Icc.image _
      ((hσ a).comp ((continuous_id.prodMk continuous_id).prodMk continuous_const)).continuousOn,
      ⟨1, ⟨zero_le_one, le_rfl⟩, hσ₁ a x⟩, ⟨σ a 0 0 x, ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩, hσZ a x⟩,
      by rintro _ ⟨b, hb, rfl⟩; exact hq_le a b b (pow_le_one₀ hb.1 hb.2) (pow_le_one₀ hb.1 hb.2) x⟩
  refine ⟨m / 2, half_pos hm, fun ε hε hcompact hcrit ↦ ?_⟩
  have hεm : 2 * ε < m := by linarith [hε.2]
  have hD (a : ι) (x : X a) (ht : t a x = 0) (hs : s a x ≤ ε) : q a x < m := by
    simp only [hq_def, ht, mul_zero, add_zero]
    linarith [hε.1]
  refine ⟨fun a x hx ↦ hmΘ a (hD a x hx.1 hx.2),
    fun a b hab ↦ (hmd hab).mono (image_mono fun x hx ↦ hD a x hx.1 hx.2)
      (image_mono fun x hx ↦ hD b x hx.1 hx.2),
    exists_sublevel_union_iUnion_image_deformation_of_tube hfs Θ hs ht hs₀ ht₀ hf
    (fun a ↦ σ a 1) (fun a ↦ (hσ a).comp ((continuous_const.prodMk continuous_fst).prodMk
      continuous_snd)) hσd (fun a b x ↦ by rw [hσs, one_pow, one_mul])
    (fun a ↦ hσt a 1) (fun a ↦ hσ₁ a) (fun a ↦ hσ₀ a) (W := fun a ↦ {x | q a x < m})
    (fun a ↦ isOpen_lt (hq a) continuous_const) hmΘ
    (fun a τ x hx ↦ (hq_le a 1 τ
        (by norm_num) (pow_le_one₀ τ.property.1 τ.property.2) x).trans_lt hx) hmd hε.1
    hD (fun a ↦ ?_) hcompact (hcrit.trans (iUnion_mono fun a ↦ image_mono fun x hx ↦ ?_))⟩
  · have hset : {x | x ∈ {x | q a x < m} ∧ s a x + 2 * t a x ≤ 2 * ε} = {x | q a x ≤ 2 * ε} :=
      Set.ext fun x ↦ ⟨fun hx ↦ hx.2, fun hx ↦ ⟨lt_of_le_of_lt hx hεm, hx⟩⟩
    exact hset ▸ hmK a (2 * ε) hεm
  · simp only [mem_ofPred_eq, hq_def, (hZst a x hx).1, (hZst a x hx).2, mul_zero, add_zero, hm]

end Family

end TauCeti
