/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Gluing.Pair
public import TauCeti.Geometry.Manifold.Morse.Boundary.Pair.Commutation
import TauCeti.Geometry.Manifold.Boundary.LocalModels
import Mathlib.Geometry.Manifold.Metrizable
import TauCeti.Dynamics.Flow.Lyapunov

/-!
# The mod-two pair map is a chain map

Let `f₀` and `f₁` be Morse functions on a compact boundaryless manifold `M`, with Morse–Smale
pseudo-gradients `X₀` and `X₁` adapted to them, forming a Morse–Smale pair
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmalePair`). The pair map counts the points of the rigid
intersections `W^u_{X₀}(p) ∩ W^s_{X₁}(q)`; for the pair transported by the transition
diffeomorphism of a transverse continuation these are the continuation trajectories
(`TauCeti.IsContinuationField.eventually_morseContinuationSlice_eq_preimage_mpullback`). By
`IsMorseSmalePair.signedMorseBoundary_comp_signedPairMap_eq_iff`, the pair map commutes with the
Morse boundaries modulo two exactly when, between a critical point `p` of `f₀` and a critical
point `r` of `f₁`, the configurations broken at the source
(`TauCeti.IsAdaptedPseudoGradient.morseSourceBrokenPairSet`) and at the target
(`TauCeti.IsAdaptedPseudoGradient.morseTargetBrokenPairSet`) are evenly many in total. This file
proves that they are
(`IsMorseSmalePair.even_ncard_morseSourceBrokenPairSet_add_ncard_morseTargetBrokenPairSet`), so the
pair map with coefficients in `ZMod 2` is a chain map
(`IsMorseSmalePair.signedMorseBoundary_comp_signedPairMap_zmod_two`).

When `ind p = ind r + 1`, the broken configurations are the endpoints of the compactified
one-dimensional intersection `S = W^u_{X₀}(p) ∩ W^s_{X₁}(r)`, and the count is that of the
boundary of a compact one-manifold (`TauCeti.even_ncard_of_forall_exists_homeomorph_Ico`). The
compactification is built inside `M × M × M`. Choose a level `c₀` below `f₀ p` and above every
critical value of `f₀` below `f₀ p`, and a level `c₁` above `f₁ r` and below every critical value
of `f₁` above `f₁ r`. A point `x` of `S` is recorded by the triple of

* the point of its `X₀`-orbit on the level `max (f₀ x) c₀`,
* the point `x` itself, and
* the point of its `X₁`-orbit on the level `min (f₁ x) c₁`.

Truncating the levels at `f₀ x` and `f₁ x` makes both outer points depend continuously on `x`,
also at the critical points `p` and `r`, which may lie on `S`. The records of the points of `S`
form a copy of `S`, hence a one-manifold. Their limits break at most once: at the source, along a
trajectory of `X₀` from `p` to a critical point `a`, whose point on the level `c₀` is the limit of
the first components; or at the target, along a trajectory of `X₁` from a critical point `b` to
`r`, whose point on the level `c₁` is the limit of the third components. The records of the broken
configurations are in bijection with the configurations themselves, so they are finitely many.
Near each of them, the half-open gluing charts of
`TauCeti.Geometry.Manifold.Morse.Gluing.Pair`, which record a point by a single orbit, transfer
to the triple records (`TauCeti.exists_homeomorph_Ico_closure_of_homeomorph_Ico`), since the
remaining component is a continuous function of the middle one.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient.IsMorseSmalePair`:

* `even_ncard_morseSourceBrokenPairSet_add_ncard_morseTargetBrokenPairSet`: between any two
  critical points, the configurations broken at the source and at the target are evenly many in
  total.
* `signedMorseBoundary_comp_signedPairMap_zmod_two`: the pair map with coefficients in `ZMod 2`
  commutes with the Morse boundaries.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.1 (the continuation map is a chain map, by counting the
  ends of the one-dimensional moduli spaces of continuation trajectories).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (compactness and gluing of trajectories) and Chapter 6 (invariance of Morse homology
  by continuation).
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]

namespace IsAdaptedPseudoGradient

/-! ### The compactified intersection of a Morse–Smale pair -/

section Pair

variable {f₀ f₁ : M → ℝ} {X₀ X₁ : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  (hX₀ : IsAdaptedPseudoGradient f₀ X₀) (hX₁ : IsAdaptedPseudoGradient f₁ X₁)

/-- The record of a point `x` of `W^u_{X₀}(p) ∩ W^s_{X₁}(r)`: the point of its `X₀`-orbit on the
level `max (f₀ x) c₀`, the point itself, and the point of its `X₁`-orbit on the level
`min (f₁ x) c₁`. -/
private noncomputable def pairRecord (c₀ c₁ : ℝ) (x : M) : M × M × M :=
  (hX₀.upperLevelPoint c₀ x, x, hX₁.lowerLevelPoint c₁ x)

private theorem pairRecord_apply (c₀ c₁ : ℝ) (x : M) :
    hX₀.pairRecord hX₁ c₀ c₁ x = (hX₀.upperLevelPoint c₀ x, x, hX₁.lowerLevelPoint c₁ x) :=
  rfl

/-- The records of the configurations broken at the source: a point of a trajectory of `X₀` from
`p` to a critical point `a` on the level `c₀`, a point `y` of `W^u_{X₀}(a) ∩ W^s_{X₁}(r)`, and the
point of the `X₁`-orbit of `y` on the level `min (f₁ y) c₁`. -/
private def sourceBrokenRecords (p r : M) (c₀ c₁ : ℝ) : Set (M × M × M) :=
  {w | ∃ a, manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ a + 1 ∧
    manifoldMorseIndex 𝓘(ℝ, E) f₀ a = manifoldMorseIndex 𝓘(ℝ, E) f₁ r ∧
    w.1 ∈ hX₀.flow.unstableSet p ∩ hX₀.flow.stableSet a ∧ f₀ w.1 = c₀ ∧
    w.2.1 ∈ hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet r ∧
    w.2.2 = hX₁.lowerLevelPoint c₁ w.2.1}

/-- The records of the configurations broken at the target: the point of the `X₀`-orbit of a
point `y` of `W^u_{X₀}(p) ∩ W^s_{X₁}(b)` on the level `max (f₀ y) c₀`, the point `y`, and a point
of a trajectory of `X₁` from `b` to `r` on the level `c₁`. -/
private def targetBrokenRecords (p r : M) (c₀ c₁ : ℝ) : Set (M × M × M) :=
  {w | ∃ b, manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ b ∧
    manifoldMorseIndex 𝓘(ℝ, E) f₁ b = manifoldMorseIndex 𝓘(ℝ, E) f₁ r + 1 ∧
    w.2.1 ∈ hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet b ∧
    w.1 = hX₀.upperLevelPoint c₀ w.2.1 ∧
    w.2.2 ∈ hX₁.flow.unstableSet b ∩ hX₁.flow.stableSet r ∧ f₁ w.2.2 = c₁}

/-- No configuration breaks both at the source and at the target. -/
private theorem disjoint_sourceBrokenRecords_targetBrokenRecords (p r : M) (c₀ c₁ : ℝ) :
    Disjoint (hX₀.sourceBrokenRecords hX₁ p r c₀ c₁) (hX₀.targetBrokenRecords hX₁ p r c₀ c₁) := by
  refine disjoint_left.2 ?_
  rintro w ⟨a, hpa, -, -, -, hy, -⟩ ⟨b, -, -, hy', -⟩
  exact (Flow.disjoint_unstableSet (x := p) (y := a) (by rintro rfl; omega)).notMem_of_mem_left
    hy'.1 hy.1

variable {p r : M} {c₀ c₁ : ℝ}

/-- The records of the configurations broken at the source are the images of the configurations
of `morseSourceBrokenPairSet`, moving the point of the trajectory from `p` to the level `c₀`. -/
private theorem sourceBrokenRecords_eq_image (hc₀ : c₀ < f₀ p)
    (hgap₀ : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f₀, f₀ x < f₀ p → f₀ x < c₀) :
    hX₀.sourceBrokenRecords hX₁ p r c₀ c₁ =
      (fun x : criticalPoints 𝓘(ℝ, E) f₀ × M × M ↦
        (hX₀.levelPoint c₀ x.2.1, x.2.2, hX₁.lowerLevelPoint c₁ x.2.2)) ''
        hX₀.morseSourceBrokenPairSet hX₁ p r := by
  ext w
  constructor
  · rintro ⟨a, hpa, har, hw₁, hw₁c, hy, hw₃⟩
    have ha := mem_criticalPoints_iff_mfderiv_eq_zero.2 (hX₀.mfderiv_eq_zero_of_mem_stableSet hw₁.2)
    have hpa' : p ≠ a := by rintro rfl; omega
    have hfa := hX₀.mem_Ioo_of_mem_unstableSet_inter_stableSet hpa' hw₁
    -- `w.1` is the level point of a point of the middle-level slice.
    obtain ⟨z, hz, hzw⟩ := ((hX₀.bijOn_flow_levelCrossingTime_midpoint hpa' (hw₁c ▸ hfa.1)
      (hw₁c ▸ hfa.2)).congr fun z _ ↦ (hX₀.levelPoint_def c₀ z).symm).surjOn ⟨hw₁, hw₁c⟩
    exact ⟨(⟨a, ha⟩, z, w.2.1), (hX₀.mem_morseSourceBrokenPairSet hX₁).2
      ⟨hpa, har, (hX₀.mem_morseTrajectorySlice).2 ⟨hz.1.1, hz.1.2, hz.2⟩, hy⟩,
      Prod.ext hzw (Prod.ext rfl hw₃.symm)⟩
  · rintro ⟨⟨a, z, y⟩, hx, rfl⟩
    obtain ⟨hpa, har, hz, hy⟩ := (hX₀.mem_morseSourceBrokenPairSet hX₁).1 hx
    dsimp only at hpa har hz hy
    rw [mem_morseTrajectorySlice] at hz
    have hpa' : p ≠ a := by rintro rfl; omega
    have hfa := hX₀.mem_Ioo_of_mem_unstableSet_inter_stableSet hpa' ⟨hz.1, hz.2.1⟩
    obtain ⟨hmem, hc⟩ := hX₀.mapsTo_levelPoint hpa' (hgap₀ a a.property (hfa.1.trans hfa.2)) hc₀
      ⟨hz.1, hz.2.1⟩
    exact ⟨a, hpa, har, hmem, hc, hy, rfl⟩

/-- Distinct configurations broken at the source have distinct records. -/
private theorem injOn_sourceBrokenRecords (hc₀ : c₀ < f₀ p)
    (hgap₀ : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f₀, f₀ x < f₀ p → f₀ x < c₀) :
    InjOn (fun x : criticalPoints 𝓘(ℝ, E) f₀ × M × M ↦
        (hX₀.levelPoint c₀ x.2.1, x.2.2, hX₁.lowerLevelPoint c₁ x.2.2))
      (hX₀.morseSourceBrokenPairSet hX₁ p r) := by
  rintro ⟨a, z, y⟩ hx ⟨a', z', y'⟩ hx' heq
  obtain ⟨hpa, -, hz, -⟩ := (hX₀.mem_morseSourceBrokenPairSet hX₁).1 hx
  obtain ⟨hpa₂, -, hz', -⟩ := (hX₀.mem_morseSourceBrokenPairSet hX₁).1 hx'
  dsimp only at hpa hz hpa₂ hz'
  simp only [Prod.mk.injEq] at heq
  obtain ⟨heq, rfl, -⟩ := heq
  rw [mem_morseTrajectorySlice] at hz hz'
  have hpa' : p ≠ a := by rintro rfl; omega
  have hpa₂' : p ≠ a' := by rintro rfl; omega
  have hfa := hX₀.mem_Ioo_of_mem_unstableSet_inter_stableSet hpa' ⟨hz.1, hz.2.1⟩
  have hfa' := hX₀.mem_Ioo_of_mem_unstableSet_inter_stableSet hpa₂' ⟨hz'.1, hz'.2.1⟩
  have hac := hgap₀ a a.property (hfa.1.trans hfa.2)
  obtain ⟨hmem, -⟩ := hX₀.mapsTo_levelPoint hpa' hac hc₀ ⟨hz.1, hz.2.1⟩
  obtain ⟨hmem', -⟩ := hX₀.mapsTo_levelPoint hpa₂' (hgap₀ a' a'.property (hfa'.1.trans hfa'.2))
    hc₀ ⟨hz'.1, hz'.2.1⟩
  -- The common level point lies on the stable sets of `a` and `a'`, so `a = a'`.
  obtain rfl : a = a' := Subtype.ext <| by
    by_contra hne
    exact (Flow.disjoint_stableSet hne).notMem_of_mem_left hmem.2 (heq ▸ hmem'.2)
  -- The level point is injective on the middle-level slice.
  rw [((hX₀.bijOn_flow_levelCrossingTime_midpoint hpa' hac hc₀).congr fun z _ ↦
    (hX₀.levelPoint_def c₀ z).symm).injOn ⟨⟨hz.1, hz.2.1⟩, hz.2.2⟩ ⟨⟨hz'.1, hz'.2.1⟩, hz'.2.2⟩
    heq]

/-- The records of the configurations broken at the target are the images of the configurations
of `morseTargetBrokenPairSet`, moving the point of the trajectory to `r` to the level `c₁`. -/
private theorem targetBrokenRecords_eq_image (hc₁ : f₁ r < c₁)
    (hgap₁ : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f₁, f₁ r < f₁ x → c₁ < f₁ x) :
    hX₀.targetBrokenRecords hX₁ p r c₀ c₁ =
      (fun x : criticalPoints 𝓘(ℝ, E) f₁ × M × M ↦
        (hX₀.upperLevelPoint c₀ x.2.1, x.2.1, hX₁.levelPoint c₁ x.2.2)) ''
        hX₀.morseTargetBrokenPairSet hX₁ p r := by
  ext w
  constructor
  · rintro ⟨b, hpb, hbr, hy, hw₁, hw₃, hw₃c⟩
    have hb := mem_criticalPoints_iff_mfderiv_eq_zero.2
      (hX₁.mfderiv_eq_zero_of_mem_unstableSet hw₃.1)
    have hbr' : b ≠ r := by rintro rfl; omega
    have hfb := hX₁.mem_Ioo_of_mem_unstableSet_inter_stableSet hbr' hw₃
    -- `w.2.2` is the level point of a point of the middle-level slice.
    obtain ⟨z, hz, hzw⟩ := ((hX₁.bijOn_flow_levelCrossingTime_midpoint hbr' (hw₃c ▸ hfb.1)
      (hw₃c ▸ hfb.2)).congr fun z _ ↦ (hX₁.levelPoint_def c₁ z).symm).surjOn ⟨hw₃, hw₃c⟩
    exact ⟨(⟨b, hb⟩, w.2.1, z), (hX₀.mem_morseTargetBrokenPairSet hX₁).2
      ⟨hpb, hbr, hy, (hX₁.mem_morseTrajectorySlice).2 ⟨hz.1.1, hz.1.2, hz.2⟩⟩,
      Prod.ext hw₁.symm (Prod.ext rfl hzw)⟩
  · rintro ⟨⟨b, y, z⟩, hx, rfl⟩
    obtain ⟨hpb, hbr, hy, hz⟩ := (hX₀.mem_morseTargetBrokenPairSet hX₁).1 hx
    dsimp only at hpb hbr hy hz
    rw [mem_morseTrajectorySlice] at hz
    have hbr' : b ≠ r := by rintro rfl; omega
    have hfb := hX₁.mem_Ioo_of_mem_unstableSet_inter_stableSet hbr' ⟨hz.1, hz.2.1⟩
    obtain ⟨hmem, hc⟩ := hX₁.mapsTo_levelPoint hbr' hc₁ (hgap₁ b b.property (hfb.1.trans hfb.2))
      ⟨hz.1, hz.2.1⟩
    exact ⟨b, hpb, hbr, hy, rfl, hmem, hc⟩

/-- Distinct configurations broken at the target have distinct records. -/
private theorem injOn_targetBrokenRecords (hc₁ : f₁ r < c₁)
    (hgap₁ : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f₁, f₁ r < f₁ x → c₁ < f₁ x) :
    InjOn (fun x : criticalPoints 𝓘(ℝ, E) f₁ × M × M ↦
        (hX₀.upperLevelPoint c₀ x.2.1, x.2.1, hX₁.levelPoint c₁ x.2.2))
      (hX₀.morseTargetBrokenPairSet hX₁ p r) := by
  rintro ⟨b, y, z⟩ hx ⟨b', y', z'⟩ hx' heq
  obtain ⟨-, hbr, -, hz⟩ := (hX₀.mem_morseTargetBrokenPairSet hX₁).1 hx
  obtain ⟨-, hbr₂, -, hz'⟩ := (hX₀.mem_morseTargetBrokenPairSet hX₁).1 hx'
  dsimp only at hbr hz hbr₂ hz'
  simp only [Prod.mk.injEq] at heq
  obtain ⟨-, rfl, heq⟩ := heq
  rw [mem_morseTrajectorySlice] at hz hz'
  have hbr' : b ≠ r := by rintro rfl; omega
  have hbr₂' : b' ≠ r := by rintro rfl; omega
  have hfb := hX₁.mem_Ioo_of_mem_unstableSet_inter_stableSet hbr' ⟨hz.1, hz.2.1⟩
  have hfb' := hX₁.mem_Ioo_of_mem_unstableSet_inter_stableSet hbr₂' ⟨hz'.1, hz'.2.1⟩
  have hcb := hgap₁ b b.property (hfb.1.trans hfb.2)
  obtain ⟨hmem, -⟩ := hX₁.mapsTo_levelPoint hbr' hc₁ hcb ⟨hz.1, hz.2.1⟩
  obtain ⟨hmem', -⟩ := hX₁.mapsTo_levelPoint hbr₂' hc₁ (hgap₁ b' b'.property (hfb'.1.trans hfb'.2))
    ⟨hz'.1, hz'.2.1⟩
  -- The common level point lies on the unstable sets of `b` and `b'`, so `b = b'`.
  obtain rfl : b = b' := Subtype.ext <| by
    by_contra hne
    exact (Flow.disjoint_unstableSet hne).notMem_of_mem_left hmem.1 (heq ▸ hmem'.1)
  -- The level point is injective on the middle-level slice.
  rw [((hX₁.bijOn_flow_levelCrossingTime_midpoint hbr' hc₁ hcb).congr fun z _ ↦
    (hX₁.levelPoint_def c₁ z).symm).injOn ⟨⟨hz.1, hz.2.1⟩, hz.2.2⟩ ⟨⟨hz'.1, hz'.2.1⟩, hz'.2.2⟩
    heq]


/-- **Reversing the pair reverses the records.** Reading triples backwards carries the records of
the reversed pair `(-X₁, -X₀)`, on the levels `-c₁` and `-c₀`, to those of `(X₀, X₁)`. -/
private theorem image_pairRecord_neg (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
    (hc₀ : c₀ < f₀ p) (hc₁ : f₁ r < c₁) :
    (fun q : M × M × M ↦ (q.2.2, q.2.1, q.1)) ''
        ((hX₁.neg hf₁).pairRecord (hX₀.neg hf₀) (-c₁) (-c₀) ''
          ((hX₁.neg hf₁).flow.unstableSet r ∩ (hX₀.neg hf₀).flow.stableSet p)) =
      hX₀.pairRecord hX₁ c₀ c₁ '' (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r) := by
  rw [← hX₀.unstableSet_inter_stableSet_eq_neg hX₁ hf₀ hf₁, image_image]
  refine image_congr fun x hx ↦ ?_
  rw [pairRecord_apply, pairRecord_apply,
    ← hX₀.upperLevelPoint_eq_lowerLevelPoint_neg hf₀ hx.1 hc₀,
    ← hX₁.lowerLevelPoint_eq_upperLevelPoint_neg hf₁ hx.2 hc₁]

namespace IsMorseSmalePair

variable {hX₀ hX₁} (h : IsMorseSmalePair hX₀ hX₁) (h₀ : hX₀.IsMorseSmale)
  (h₁ : hX₁.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
  (hind : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ r + 1)
  (hc₀ : c₀ < f₀ p) (hgap₀ : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f₀, f₀ x < f₀ p → f₀ x < c₀)
  (hc₁ : f₁ r < c₁) (hgap₁ : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f₁, f₁ r < f₁ x → c₁ < f₁ x)

include h h₀ h₁ hf₀ hf₁ hind hc₀ hgap₀ hc₁ hgap₁

/-- **The limits of records of `W^u_{X₀}(p) ∩ W^s_{X₁}(r)`**, for `ind p = ind r + 1`, are records
of its points or of configurations broken at the source or at the target. -/
private theorem closure_pairRecords_subset :
    closure (hX₀.pairRecord hX₁ c₀ c₁ '' (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r)) ⊆
      hX₀.pairRecord hX₁ c₀ c₁ '' (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r) ∪
        (hX₀.sourceBrokenRecords hX₁ p r c₀ c₁ ∪ hX₀.targetBrokenRecords hX₁ p r c₀ c₁) := by
  have := Manifold.metrizableSpace 𝓘(ℝ, E) M
  set S := hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r
  intro q hq
  obtain ⟨v, hvP, hvq⟩ := mem_closure_iff_seq_limit.1 hq
  choose x hxS hxv using hvP
  obtain rfl : (fun n ↦ hX₀.pairRecord hX₁ c₀ c₁ (x n)) = v := funext hxv
  set y := q.2.1
  have hx : Tendsto x atTop (𝓝 y) := ((continuous_fst.comp continuous_snd).tendsto q).comp hvq
  have h₁q : Tendsto (fun n ↦ hX₀.upperLevelPoint c₀ (x n)) atTop (𝓝 q.1) :=
    (continuous_fst.tendsto q).comp hvq
  have h₃q : Tendsto (fun n ↦ hX₁.lowerLevelPoint c₁ (x n)) atTop (𝓝 q.2.2) :=
    ((continuous_snd.comp continuous_snd).tendsto q).comp hvq
  have hxS' : Tendsto x atTop (𝓝[S] y) := tendsto_nhdsWithin_iff.2 ⟨hx, .of_forall hxS⟩
  -- Where the limit lies on `W^u_{X₀}(p)`, resp. `W^s_{X₁}(r)`, its records are the limits.
  have hup (hy : y ∈ hX₀.flow.unstableSet p) : q.1 = hX₀.upperLevelPoint c₀ y :=
    tendsto_nhds_unique h₁q ((hX₀.continuousOn_upperLevelPoint hf₀ hc₀ y hy).tendsto.comp
      (tendsto_nhdsWithin_mono_right inter_subset_left hxS'))
  have hlow (hy : y ∈ hX₁.flow.stableSet r) : q.2.2 = hX₁.lowerLevelPoint c₁ y :=
    tendsto_nhds_unique h₃q ((hX₁.continuousOn_lowerLevelPoint hf₁ hc₁ y hy).tendsto.comp
      (tendsto_nhdsWithin_mono_right inter_subset_right hxS'))
  rcases h.closure_unstableSet_inter_stableSet_subset h₀ h₁ hf₀ hf₁ hind
    (mem_closure_of_tendsto hx (.of_forall hxS)) with (hy | hy) | hy
  · exact Or.inl ⟨y, hy, Prod.ext (hup hy.1).symm (Prod.ext rfl (hlow hy.2).symm)⟩
  · -- Breaking at the source, at a critical point `a` below the level `c₀`.
    obtain ⟨a, ⟨har, z, hz⟩, hya⟩ := mem_iUnion₂.1 hy
    have hpa : p ≠ a := by rintro rfl; omega
    have hfa := hX₀.mem_Ioo_of_mem_unstableSet_inter_stableSet hpa hz
    have hac : f₀ a < c₀ := hgap₀ a (mem_criticalPoints_iff_mfderiv_eq_zero.2
      (hX₀.mfderiv_eq_zero_of_mem_unstableSet hya.1)) (hfa.1.trans hfa.2)
    obtain ⟨hq₁, hq₁c⟩ := h₀.mem_of_tendsto_upperLevelPoint_of_mem_unstableSet hf₀ hpa
      (by omega) hya.1 hac hc₀ (fun n ↦ (hxS n).1) hx h₁q
    exact Or.inr (Or.inl ⟨a, by omega, har, hq₁, hq₁c, hya, hlow hya.2⟩)
  · -- Breaking at the target, at a critical point `b` above the level `c₁`.
    obtain ⟨b, ⟨hbp, z, hz⟩, hyb⟩ := mem_iUnion₂.1 hy
    have hbr : b ≠ r := by rintro rfl; omega
    have hfb := hX₁.mem_Ioo_of_mem_unstableSet_inter_stableSet hbr hz
    have hcb : c₁ < f₁ b := hgap₁ b (mem_criticalPoints_iff_mfderiv_eq_zero.2
      (hX₁.mfderiv_eq_zero_of_mem_stableSet hyb.2)) (hfb.1.trans hfb.2)
    obtain ⟨hq₃, hq₃c⟩ := h₁.mem_of_tendsto_lowerLevelPoint_of_mem_stableSet hf₁ hbr
      (by omega) hyb.2 hc₁ hcb (fun n ↦ (hxS n).2) hx h₃q
    exact Or.inr (Or.inr ⟨b, by omega, by omega, hyb, hup hyb.1, hq₃, hq₃c⟩)


omit hind in
/-- There are finitely many records of broken configurations. -/
private theorem finite_brokenRecords :
    (hX₀.sourceBrokenRecords hX₁ p r c₀ c₁ ∪ hX₀.targetBrokenRecords hX₁ p r c₀ c₁).Finite := by
  rw [hX₀.sourceBrokenRecords_eq_image hX₁ (r := r) (c₁ := c₁) hc₀ hgap₀,
    hX₀.targetBrokenRecords_eq_image hX₁ (p := p) (c₀ := c₀) hc₁ hgap₁]
  exact ((h.finite_morseSourceBrokenPairSet h₀ h₁ hf₀ hf₁ p r).image _).union
    ((h.finite_morseTargetBrokenPairSet h₀ h₁ hf₀ hf₁ p r).image _)

/-- Near any of its points `w`, the compactified space contains only `w` and records of points of
the intersection: it adds finitely many records of broken configurations. -/
private theorem eventually_eq_or_mem_pairRecords (w : M × M × M) :
    ∀ᶠ q in 𝓝[closure (hX₀.pairRecord hX₁ c₀ c₁ ''
        (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r))] w,
      q = w ∨ q ∈ hX₀.pairRecord hX₁ c₀ c₁ '' (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r) := by
  have hfar : ((hX₀.sourceBrokenRecords hX₁ p r c₀ c₁ ∪ hX₀.targetBrokenRecords hX₁ p r c₀ c₁) \
      {w})ᶜ ∈ 𝓝 w :=
    (h.finite_brokenRecords h₀ h₁ hf₀ hf₁ hc₀ hgap₀ hc₁ hgap₁).sdiff.isClosed.isOpen_compl.mem_nhds
      (by simp)
  filter_upwards [nhdsWithin_le_nhds hfar, self_mem_nhdsWithin] with q hq hqcl
  rcases h.closure_pairRecords_subset h₀ h₁ hf₀ hf₁ hind hc₀ hgap₀ hc₁ hgap₁ hqcl with hqP | hqB
  · exact Or.inr hqP
  · exact Or.inl (not_not.1 fun hne ↦ hq ⟨hqB, hne⟩)

/-- **The compactified intersection is one-dimensional at unbroken records.** Every record of a
point of `W^u_{X₀}(p) ∩ W^s_{X₁}(r)` has a neighbourhood in the closure of the records
homeomorphic to an open subset of `ℝ`. -/
private theorem exists_nhds_homeomorph_of_mem_pairRecords {q : M × M × M}
    (hq : q ∈ closure (hX₀.pairRecord hX₁ c₀ c₁ ''
      (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r)))
    (hqP : q ∈ hX₀.pairRecord hX₁ c₀ c₁ '' (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r)) :
    ∃ N ∈ 𝓝 (⟨q, hq⟩ : closure (hX₀.pairRecord hX₁ c₀ c₁ ''
        (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r))),
      ∃ V : Set ℝ, IsOpen V ∧ Nonempty (V ≃ₜ N) := by
  obtain ⟨x₀, hx₀, rfl⟩ := hqP
  set S := hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r
  set P := hX₀.pairRecord hX₁ c₀ c₁ '' S
  have hx₀P : hX₀.pairRecord hX₁ c₀ c₁ x₀ ∈ P := mem_image_of_mem _ hx₀
  have hcont : ContinuousOn (hX₀.pairRecord hX₁ c₀ c₁) S :=
    ((hX₀.continuousOn_upperLevelPoint hf₀ hc₀).mono inter_subset_left).prodMk
      (continuousOn_id.prodMk ((hX₁.continuousOn_lowerLevelPoint hf₁ hc₁).mono inter_subset_right))
  -- The records of the points of `S` form a copy of `S`.
  have hmemS (w : P) : (w : M × M × M).2.1 ∈ S := by
    obtain ⟨_, x, hx, rfl⟩ := w
    exact hx
  let Φ : P ≃ₜ S :=
    { toFun w := ⟨(w : M × M × M).2.1, hmemS w⟩
      invFun x := ⟨hX₀.pairRecord hX₁ c₀ c₁ x, mem_image_of_mem _ x.property⟩
      left_inv := by rintro ⟨_, ⟨x, hx, rfl⟩⟩; rfl
      right_inv _ := rfl
      continuous_toFun :=
        ((continuous_fst.comp continuous_snd).comp continuous_subtypeVal).subtype_mk hmemS
      continuous_invFun :=
        (hcont.comp_continuous continuous_subtypeVal fun x ↦ x.property).subtype_mk _ }
  -- `S` is a manifold modelled on a line `L`.
  obtain ⟨L, hL, C, -, -⟩ := h.exists_unstableSet_inter_stableSet_isManifold hf₀ ⟨x₀, hx₀⟩
  let _ := C
  have hL1 : Module.finrank ℝ L = Module.finrank ℝ ℝ := by rw [Module.finrank_self]; omega
  -- The unbroken records sit openly in the compactified space.
  let ι : P → closure P := fun x ↦ ⟨x.val, subset_closure x.property⟩
  have hι : IsOpenEmbedding ι := by
    refine ⟨(IsEmbedding.of_comp_iff IsEmbedding.subtypeVal).1 IsEmbedding.subtypeVal, ?_⟩
    have hc : IsClosed ((↑) ⁻¹' (closure P \ P) : Set (closure P)) :=
      ((h.finite_brokenRecords h₀ h₁ hf₀ hf₁ hc₀ hgap₀ hc₁ hgap₁).subset fun w hw ↦
        ((h.closure_pairRecords_subset h₀ h₁ hf₀ hf₁ hind hc₀ hgap₀ hc₁ hgap₁
          (mem_of_mem_sdiff hw)).resolve_left (notMem_of_mem_sdiff hw))).isClosed.preimage
          continuous_subtypeVal
    convert hc.isOpen_compl using 1
    ext x
    simp only [mem_range, mem_compl_iff, mem_preimage, Set.mem_sdiff, Subtype.coe_prop, true_and,
      not_not]
    exact ⟨by rintro ⟨y, rfl⟩; exact y.property, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩
  have : Nonempty P := ⟨⟨_, hx₀P⟩⟩
  let G := ((hι.toOpenPartialHomeomorph ι).symm.trans Φ.toOpenPartialHomeomorph).trans
    ((chartAt L (Φ ⟨_, hx₀P⟩)).trans
      (ContinuousLinearEquiv.ofFinrankEq hL1).toHomeomorph.toOpenPartialHomeomorph)
  refine ⟨G.source, G.open_source.mem_nhds ?_, G.target, G.open_target,
    ⟨G.toHomeomorphSourceTarget.symm⟩⟩
  have hιw : ι ⟨_, hx₀P⟩ = ⟨_, hq⟩ := rfl
  simp [G, ← hιw, hι.toOpenPartialHomeomorph_left_inv]

/-- **A configuration broken at the source is an endpoint.** The record of a configuration broken
at the source lies in the closure of the records of `W^u_{X₀}(p) ∩ W^s_{X₁}(r)`, and has a
neighbourhood there homeomorphic to a half-open interval `[0, δ)`, by a homeomorphism sending `0`
to it. -/
private theorem exists_homeomorph_Ico_of_mem_sourceBrokenRecords {w : M × M × M}
    (hw : w ∈ hX₀.sourceBrokenRecords hX₁ p r c₀ c₁) :
    ∃ hb : w ∈ closure (hX₀.pairRecord hX₁ c₀ c₁ ''
        (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r)),
      ∃ N ∈ 𝓝 (⟨w, hb⟩ : closure (hX₀.pairRecord hX₁ c₀ c₁ ''
          (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r))),
        ∃ (δ : ℝ) (hδ : 0 < δ) (e : Ico (0 : ℝ) δ ≃ₜ N),
          (e ⟨0, left_mem_Ico.2 hδ⟩ : closure (hX₀.pairRecord hX₁ c₀ c₁ ''
            (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r))) = ⟨w, hb⟩ := by
  have hcont₀ : Continuous f₀ := hX₀.mdifferentiable.continuous
  have hnear := h.eventually_eq_or_mem_pairRecords h₀ h₁ hf₀ hf₁ hind hc₀ hgap₀ hc₁ hgap₁ w
  obtain ⟨a₁, y, w₃⟩ := w
  obtain ⟨a, hpa, har, ha₁, ha₁c, hy, hw₃⟩ := hw
  dsimp only at ha₁ ha₁c hy hw₃
  subst hw₃
  have hpa' : p ≠ a := by rintro rfl; omega
  have hyc : f₀ y < c₀ := (Flow.le_of_mem_unstableSet_of_antitone hy.1
    hcont₀.continuousAt (hX₀.antitone_flow y)).trans_lt
      (ha₁c ▸ (hX₀.mem_Ioo_of_mem_unstableSet_inter_stableSet hpa' ha₁).1)
  obtain ⟨N, δ, hδ, e, he, hNsub, hN⟩ := h.exists_homeomorph_Ico_of_source h₀ hf₀ hpa har ha₁ hy
  -- The gluing chart records a point by its `X₀`-orbit on the level `c₀`; the third component of
  -- the records is a continuous function of the second.
  have hlow : ContinuousOn (fun v : M × M ↦ hX₁.lowerLevelPoint c₁ v.2) (insert (a₁, y)
      {v | v.2 ∈ hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r ∧ f₀ v.1 = f₀ a₁ ∧
        ∃ t, hX₀.flow t v.1 = v.2}) :=
    (hX₁.continuousOn_lowerLevelPoint hf₁ hc₁).comp continuous_snd.continuousOn fun v hv ↦ by
      rcases hv with rfl | hv
      exacts [hy.2, hv.1.2]
  refine exists_homeomorph_Ico_closure_of_homeomorph_Ico (fun q ↦ (q.1, q.2.1))
    (fun v ↦ (v.1, v.2, hX₁.lowerLevelPoint c₁ v.2)) (by fun_prop)
    (continuousOn_fst.prodMk (continuousOn_snd.prodMk hlow)) (fun _ _ ↦ rfl) rfl ?_ ?_ hδ e he
    hNsub hN
  · -- Near `(a₁, y)`, the points of the chart lie below the level `c₀`, so they are records.
    have hev : ∀ᶠ v in 𝓝 (a₁, y), f₀ v.2 < c₀ :=
      ((hcont₀.comp continuous_snd).tendsto (a₁, y)).eventually (gt_mem_nhds hyc)
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with v hv hvR
    obtain ⟨hvS, hv₁, t, ht⟩ := hvR.1.resolve_left hvR.2
    obtain ⟨a', hpa'', hva'⟩ := hX₀.exists_mem_unstableSet_inter_stableSet_of_mem_unstableSet
      hf₀ hvS.1 (ne_of_apply_ne f₀ (hv.trans hc₀).ne)
    have hup : hX₀.upperLevelPoint c₀ v.2 = v.1 := by
      rw [hX₀.upperLevelPoint_of_lt hv, hX₀.levelPoint_eq hpa'' hva' (t := -t)
        (by rw [← ht, Flow.map_neg_apply_map, hv₁, ha₁c]), ← ht, Flow.map_neg_apply_map]
    exact ⟨v.2, hvS, by rw [pairRecord_apply, hup]⟩
  · -- Near the broken record, the records lie below the level `c₀` and come from the chart.
    have hev : ∀ᶠ q in 𝓝 (a₁, y, hX₁.lowerLevelPoint c₁ y), f₀ q.2.1 < c₀ :=
      (((hcont₀.comp continuous_fst).comp continuous_snd).tendsto _).eventually (gt_mem_nhds hyc)
    filter_upwards [hnear, nhdsWithin_le_nhds hev] with q hq hqc
    rcases hq with rfl | ⟨x, hxS, rfl⟩
    · exact ⟨mem_insert _ _, rfl⟩
    · rw [pairRecord_apply] at hqc ⊢
      have hup := hX₀.upperLevelPoint_of_lt hqc
      refine ⟨Or.inr ⟨hxS, ?_, -Flow.levelCrossingTime hX₀.flow f₀ c₀ x, ?_⟩, rfl⟩ <;> dsimp only
      · rw [hup, hX₀.apply_levelPoint (hX₀.exists_flow_eq_of_mem_unstableSet hf₀ hxS.1 hc₀ hqc),
          ha₁c]
      · rw [hup, hX₀.levelPoint_def, Flow.map_neg_apply_map]

/-- **A configuration broken at the target is an endpoint.** The record of a configuration broken
at the target lies in the closure of the records of `W^u_{X₀}(p) ∩ W^s_{X₁}(r)`, and has a
neighbourhood there homeomorphic to a half-open interval `[0, δ)`, by a homeomorphism sending `0`
to it. -/
private theorem exists_homeomorph_Ico_of_mem_targetBrokenRecords {w : M × M × M}
    (hw : w ∈ hX₀.targetBrokenRecords hX₁ p r c₀ c₁) :
    ∃ hb : w ∈ closure (hX₀.pairRecord hX₁ c₀ c₁ ''
        (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r)),
      ∃ N ∈ 𝓝 (⟨w, hb⟩ : closure (hX₀.pairRecord hX₁ c₀ c₁ ''
          (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r))),
        ∃ (δ : ℝ) (hδ : 0 < δ) (e : Ico (0 : ℝ) δ ≃ₜ N),
          (e ⟨0, left_mem_Ico.2 hδ⟩ : closure (hX₀.pairRecord hX₁ c₀ c₁ ''
            (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r))) = ⟨w, hb⟩ := by
  -- Reversing both fields, the configuration read backwards breaks at the source for the pair
  -- `(-X₁, -X₀)` from `r` to `p`, with the Morse indices `n - ind` of `-f₁` and `-f₀`.
  obtain ⟨b, hpb, hbr, hy, hw₁, ha₂, ha₂c⟩ := hw
  have hp := hf₀.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero
    (hX₀.mfderiv_eq_zero_of_mem_unstableSet hy.1)
  have hb := hf₁.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero
    (hX₁.mfderiv_eq_zero_of_mem_stableSet hy.2)
  have hr := hf₁.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero
    (hX₁.mfderiv_eq_zero_of_mem_stableSet ha₂.2)
  have := hp.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
  have := hb.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
  have := hr.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
  obtain ⟨hb', N, hN, δ, hδ, e, he⟩ :=
    (h.neg hf₀ hf₁).exists_homeomorph_Ico_of_mem_sourceBrokenRecords (h₁.neg hf₁) (h₀.neg hf₀)
      hf₁.neg hf₀.neg (p := r) (r := p) (c₀ := -c₁) (c₁ := -c₀) (by omega) (neg_lt_neg hc₁)
      (fun x hx hxr ↦ neg_lt_neg (hgap₁ x (by rwa [criticalPoints_neg] at hx) (by simpa using hxr)))
      (neg_lt_neg hc₀)
      (fun x hx hpx ↦ neg_lt_neg (hgap₀ x (by rwa [criticalPoints_neg] at hx) (by simpa using hpx)))
      (w := (w.2.2, w.2.1, w.1))
      ⟨b, hb.manifoldMorseIndex_neg_eq_add_one_of_eq_add_one hr hbr, by omega,
        hX₁.unstableSet_inter_stableSet_eq_neg hX₁ hf₁ hf₁ b r ▸ ha₂,
        congrArg Neg.neg ha₂c, hX₀.unstableSet_inter_stableSet_eq_neg hX₁ hf₀ hf₁ p b ▸ hy,
        hw₁.trans (hX₀.upperLevelPoint_eq_lowerLevelPoint_neg hf₀ hy.1 hc₀)⟩
  -- Reading triples backwards carries the records of `(-X₁, -X₀)` to those of `(X₀, X₁)`, hence
  -- the closure of the former onto that of the latter.
  let σ : M × M × M ≃ₜ M × M × M :=
    { toFun q := (q.2.2, q.2.1, q.1)
      invFun q := (q.2.2, q.2.1, q.1)
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hσ (q : M × M × M) : σ q = (q.2.2, q.2.1, q.1) := rfl
  have hcl (q : M × M × M) : q ∈ closure ((hX₁.neg hf₁).pairRecord (hX₀.neg hf₀) (-c₁) (-c₀) ''
      ((hX₁.neg hf₁).flow.unstableSet r ∩ (hX₀.neg hf₀).flow.stableSet p)) ↔
      σ q ∈ closure (hX₀.pairRecord hX₁ c₀ c₁ ''
        (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r)) := by
    rw [← hX₀.image_pairRecord_neg hX₁ hf₀ hf₁ hc₀ hc₁, ← funext hσ, ← σ.image_closure,
      σ.injective.mem_set_image]
  -- Transport the half-open chart along the induced homeomorphism of the closures.
  let Φ := σ.subtype hcl
  have hΦ : Φ ⟨_, hb'⟩ = ⟨w, (hcl _).1 hb'⟩ :=
    Subtype.ext ((Homeomorph.subtype_apply_coe _ _ _).trans (hσ _))
  refine ⟨(hcl _).1 hb', Φ '' N, hΦ ▸ Φ.isOpenMap.image_mem_nhds hN, δ, hδ, e.trans (Φ.image N),
    ?_⟩
  rw [Homeomorph.trans_apply, Homeomorph.image_apply_coe, he, hΦ]

end IsMorseSmalePair


namespace IsMorseSmalePair

variable {hX₀ hX₁} (h : IsMorseSmalePair hX₀ hX₁) (h₀ : hX₀.IsMorseSmale)
  (h₁ : hX₁.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
include h h₀ h₁ hf₀ hf₁

/-- **Broken configurations of a Morse–Smale pair come in pairs.** Let `(X₀, X₁)` be a Morse–Smale
pair of Morse–Smale pseudo-gradients adapted to Morse functions `f₀` and `f₁` on a compact
boundaryless manifold. Between any critical point `p` of `f₀` and any critical point `r` of `f₁`,
the configurations broken at the source and those broken at the target are evenly many in total:
when `ind p = ind r + 1` they are the endpoints of the compactified one-dimensional intersection
`W^u_{X₀}(p) ∩ W^s_{X₁}(r)`, and otherwise there are none. -/
theorem even_ncard_morseSourceBrokenPairSet_add_ncard_morseTargetBrokenPairSet
    (p : criticalPoints 𝓘(ℝ, E) f₀) (r : criticalPoints 𝓘(ℝ, E) f₁) :
    Even ((hX₀.morseSourceBrokenPairSet hX₁ p r).ncard +
      (hX₀.morseTargetBrokenPairSet hX₁ p r).ncard) := by
  by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ r + 1
  swap
  · -- Without an index drop by one, no configuration breaks.
    have hs : hX₀.morseSourceBrokenPairSet hX₁ p r = ∅ := eq_empty_of_forall_notMem fun x hx ↦ by
      obtain ⟨h₁, h₂, -⟩ := (hX₀.mem_morseSourceBrokenPairSet hX₁).1 hx
      omega
    have ht : hX₀.morseTargetBrokenPairSet hX₁ p r = ∅ := eq_empty_of_forall_notMem fun x hx ↦ by
      obtain ⟨h₁, h₂, -⟩ := (hX₀.mem_morseTargetBrokenPairSet hX₁).1 hx
      omega
    simp [hs, ht]
  -- Record the points of the intersection on levels `c₀` below `p` and `c₁` above `r`.
  obtain ⟨c₀, hc₀, hgap₀⟩ := hf₀.exists_lt_forall_lt (f₀ p)
  obtain ⟨c₁, hc₁, hgap₁⟩ := hf₁.exists_gt_forall_gt (f₁ r)
  set P := hX₀.pairRecord hX₁ c₀ c₁ '' (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r)
  have hcl := h.closure_pairRecords_subset h₀ h₁ hf₀ hf₁ hind hc₀ hgap₀ hc₁ hgap₁
  have hs (w : M × M × M) (hw : w ∈ hX₀.sourceBrokenRecords hX₁ p r c₀ c₁) :=
    h.exists_homeomorph_Ico_of_mem_sourceBrokenRecords h₀ h₁ hf₀ hf₁ hind hc₀ hgap₀ hc₁ hgap₁ hw
  have ht (w : M × M × M) (hw : w ∈ hX₀.targetBrokenRecords hX₁ p r c₀ c₁) :=
    h.exists_homeomorph_Ico_of_mem_targetBrokenRecords h₀ h₁ hf₀ hf₁ hind hc₀ hgap₀ hc₁ hgap₁ hw
  have hfin := h.finite_brokenRecords h₀ h₁ hf₀ hf₁ hc₀ hgap₀ hc₁ hgap₁
  -- The closure of the records is a compact space locally modelled on the half-line, whose
  -- endpoints are the records of broken configurations.
  have : CompactSpace (closure P) := isCompact_iff_compactSpace.1 isClosed_closure.isCompact
  have hE : Even (((↑) : closure P → M × M × M) ⁻¹'
      (hX₀.sourceBrokenRecords hX₁ p r c₀ c₁ ∪ hX₀.targetBrokenRecords hX₁ p r c₀ c₁)).ncard := by
    refine even_ncard_of_forall_exists_homeomorph_Ico (F := ℝ) (Module.finrank_self ℝ)
      (fun q hq ↦ ?_) fun q hq ↦ ?_
    · rcases hq with hq | hq
      · obtain ⟨_, N, hN, δ, hδ, e, he⟩ := hs _ hq
        exact ⟨N, hN, δ, hδ, e, he⟩
      · obtain ⟨_, N, hN, δ, hδ, e, he⟩ := ht _ hq
        exact ⟨N, hN, δ, hδ, e, he⟩
    · exact h.exists_nhds_homeomorph_of_mem_pairRecords h₀ h₁ hf₀ hf₁ hind hc₀ hgap₀ hc₁ hgap₁
        q.property ((hcl q.property).resolve_right hq)
  -- Count the endpoints through the records of the broken configurations.
  rw [ncard_preimage_of_injective_subset_range Subtype.val_injective (by
      rw [Subtype.range_coe]
      exact union_subset (fun w hw ↦ (hs w hw).1) fun w hw ↦ (ht w hw).1),
    ncard_union_eq (hX₀.disjoint_sourceBrokenRecords_targetBrokenRecords hX₁ p r c₀ c₁)
      (hfin.subset subset_union_left) (hfin.subset subset_union_right),
    hX₀.sourceBrokenRecords_eq_image hX₁ hc₀ hgap₀, hX₀.targetBrokenRecords_eq_image hX₁ hc₁ hgap₁,
    (hX₀.injOn_sourceBrokenRecords hX₁ hc₀ hgap₀).ncard_image,
    (hX₀.injOn_targetBrokenRecords hX₁ hc₁ hgap₁).ncard_image] at hE
  exact hE

/-- **The mod-two pair map is a chain map.** For a Morse–Smale pair `(X₀, X₁)` of Morse–Smale
pseudo-gradients adapted to Morse functions on a compact boundaryless manifold, and any choice of
orientations, the pair map with coefficients in `ZMod 2` commutes with the Morse boundaries:
`∂₁ ∘ Φ = Φ ∘ ∂₀`. -/
theorem signedMorseBoundary_comp_signedPairMap_zmod_two {𝔬₀ : MorseOrientation f₀ X₀}
    {𝔬₁ : MorseOrientation f₁ X₁} :
    hX₁.signedMorseBoundary 𝔬₁ hf₁ (ZMod 2) ∘ₗ hX₀.signedPairMap hX₁ 𝔬₀ 𝔬₁ hf₁ (ZMod 2) =
      hX₀.signedPairMap hX₁ 𝔬₀ 𝔬₁ hf₁ (ZMod 2) ∘ₗ hX₀.signedMorseBoundary 𝔬₀ hf₀ (ZMod 2) := by
  refine (h.signedMorseBoundary_comp_signedPairMap_eq_iff h₀ h₁ hf₀ hf₁).2 fun p r ↦ ?_
  -- Modulo two, the signed counts are the numbers of broken configurations, whose sum is even.
  rw [h.intCast_finsum_mem_targetBrokenPairSign h₀ h₁ hf₀ hf₁,
    h.intCast_finsum_mem_sourceBrokenPairSign h₀ h₁ hf₀ hf₁, ← CharTwo.add_eq_zero,
    ← Nat.cast_add, add_comm, ZMod.natCast_eq_zero_iff_even]
  exact h.even_ncard_morseSourceBrokenPairSet_add_ncard_morseTargetBrokenPairSet h₀ h₁ hf₀ hf₁ p r

end IsMorseSmalePair

end Pair

end IsAdaptedPseudoGradient

end TauCeti
