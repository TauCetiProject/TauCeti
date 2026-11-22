/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import TauCeti.Dynamics.Billiard.GeneratingFunction
public import TauCeti.Dynamics.Billiard.Inverse
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import TauCeti.LinearAlgebra.Determinant.Prod
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Periodic
import TauCeti.MeasureTheory.Measure.Subtype

/-!
# The billiard map preserves area, and Poincaré recurrence for billiards

Let `χ` be an arclength parametrization of the boundary of a strictly convex billiard table
(`TauCeti.StrictConvexBilliardTable`), with period `L`, and let `B(s, v) = (t, w)` be its
next-collision map on the strip `ℝ × (-1, 1)`. When `χ` is twice differentiable, `B` preserves
Lebesgue measure `ds dv` on the strip
(`TauCeti.StrictConvexBilliardTable.measurePreserving_nextCollisionEquiv`), and the billiard map
`β` on the space of collision states `AddCircle L × (-1, 1)` preserves the product of the Haar
measure of the circle with Lebesgue measure, a finite measure of total mass `2 L`
(`TauCeti.StrictConvexBilliardTable.measurePreserving_billiardMap`).

The proof reads the area form `ds ∧ dv` in the chord coordinates `(s, t)`, `s < t < s + L`, given by
the generating function `S(s, t) = -‖χ(t) - χ(s)‖`. The maps

`(s, t) ↦ (s, v) = (s, ∂_s S(s, t))`, `(s, t) ↦ (t, w) = (t, -∂_t S(s, t))`

send a chord to its initial and final collision states, and `B` carries the first to the second.
Both are injective and differentiable on the window `s < t < s + L`, and their Jacobian
determinants are the same mixed partial derivative `∂_t ∂_s S = ∂_s ∂_t S` of the generating
function (`TauCeti.StrictConvexBilliardTable.hasDerivAt_deriv_generatingFunction_left`,
`TauCeti.StrictConvexBilliardTable.hasDerivAt_deriv_generatingFunction_right`). By the change of
variables formula both maps therefore send a set of chords to sets of states of the same area,
and `B` preserves area. This is the measure-theoretic form of `B^*(dv ∧ ds) = dv ∧ ds`, read
off from `dv ∧ ds = ∂_t ∂_s S dt ∧ ds = dw ∧ dt`. Measurability of `B` comes from the
Lusin–Souslin theorem, through `measurable_image_of_fderivWithin`, so no continuity of `B` is
needed. The billiard map is induced by `B` on the quotient by the deck translation
`τ(s, v) = (s + L, v)`, which `B` commutes with, so it preserves the quotient measure
(`AddCircle.measurePreserving_of_lift`).

A self-map preserving a finite measure is conservative
(`MeasureTheory.MeasurePreserving.conservative`), and the product measure on
`AddCircle L × (-1, 1)` charges every nonempty open set. Hence
**Poincaré recurrence** holds for convex billiards: every nonempty open set of collision states
contains a state that returns to it
(`TauCeti.StrictConvexBilliardTable.exists_mem_iterate_billiardMap_mem`), and almost every state
returns infinitely often to each of its neighbourhoods
(`TauCeti.StrictConvexBilliardTable.ae_frequently_iterate_billiardMap_mem`).

## Main results

* `TauCeti.StrictConvexBilliardTable.measurePreserving_nextCollisionEquiv`: the next-collision
  map preserves Lebesgue measure on the strip.
* `TauCeti.StrictConvexBilliardTable.measurePreserving_billiardMap`: the billiard map preserves
  the finite product measure on `AddCircle L × (-1, 1)`.
* `TauCeti.StrictConvexBilliardTable.exists_mem_iterate_billiardMap_mem`,
  `TauCeti.StrictConvexBilliardTable.ae_frequently_iterate_billiardMap_mem`: Poincaré recurrence.

## References

* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 5.2 (the billiard map preserves area, and Poincaré recurrence).
* Serge Tabachnikov, *Geometry and Billiards*, Student Mathematical Library 30, American
  Mathematical Society, 2005, Chapter 3 (the invariant area form of the billiard map).
-/

public section

noncomputable section

open Function MeasureTheory Set Filter Topology Module
open scoped RealInnerProductSpace

namespace TauCeti

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2)]

namespace StrictConvexBilliardTable

variable {o : Orientation ℝ E (Fin 2)} (χ : StrictConvexBilliardTable o)

/-! ### Chord coordinates -/

/-- The window `{(s, t) | s < t < s + L}` of chords from `χ(s)` to `χ(t)`. -/
private def window : Set (ℝ × ℝ) :=
  {p | p.2 ∈ Ioo p.1 (p.1 + χ.period)}

/-- The state `(s, v)` at `χ(s)` leaving along the chord to `χ(t)`: `v = ∂_s S(s, t)`. -/
private def chordStart (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1, ⟪deriv χ p.1, χ.chordDir p.1 p.2⟫)

/-- The state `(t, w)` at `χ(t)` after arriving along the chord from `χ(s)`:
`w = -∂_t S(s, t)`. -/
private def chordEnd (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.2, ⟪deriv χ p.2, χ.chordDir p.1 p.2⟫)

/-- The chord from `χ(s)` to the next collision point of the state `(s, v)` starts at `(s, v)`. -/
private theorem chordStart_nextParam {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    χ.chordStart (s, χ.nextParam s v) = (s, v) := by
  simp [chordStart, χ.inner_deriv_chordDir_nextParam hv]

/-- The next-collision map sends the initial state of a chord to its final state. -/
private theorem nextCollision_chordStart {p : ℝ × ℝ} (hp : p ∈ χ.window) :
    χ.nextCollision (χ.chordStart p) = χ.chordEnd p := by
  have hv := χ.inner_deriv_chordDir_mem_Ioo p.1 p.2
  have ht : χ.nextParam p.1 ⟪deriv χ p.1, χ.chordDir p.1 p.2⟫ = p.2 :=
    χ.nextParam_inner_deriv_chordDir hp
  have hu := χ.chordDir_nextParam (s := p.1) hv
  rw [ht] at hu
  simp only [nextCollision_apply, chordStart, chordEnd, nextTangential_def, ht, ← hu,
    real_inner_comm]

private theorem measurable_chordEnd : Measurable χ.chordEnd := by
  borelize E
  have hd : Measurable fun p : ℝ × ℝ ↦ χ p.2 - χ p.1 :=
    ((χ.continuous.comp continuous_snd).sub (χ.continuous.comp continuous_fst)).measurable
  have hu : Measurable fun p : ℝ × ℝ ↦ χ.chordDir p.1 p.2 := by
    simp only [chordDir_eq_inv_norm_smul]
    exact hd.norm.inv.smul hd
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  exact measurable_snd.prodMk (Measurable.inner ((measurable_deriv χ).comp measurable_snd) hu)

private theorem isOpen_window : IsOpen χ.window :=
  (isOpen_lt continuous_fst continuous_snd).inter
    (isOpen_lt continuous_snd (continuous_fst.add continuous_const))

private theorem chordStart_mem_strip (p : ℝ × ℝ) : χ.chordStart p ∈ univ ×ˢ Ioo (-1 : ℝ) 1 :=
  ⟨mem_univ _, χ.inner_deriv_chordDir_mem_Ioo p.1 p.2⟩

private theorem injOn_chordStart : InjOn χ.chordStart χ.window := by
  intro p hp q hq h
  obtain ⟨h1, h2⟩ := Prod.ext_iff.1 h
  refine Prod.ext h1 ?_
  rw [← χ.nextParam_inner_deriv_chordDir hp, ← χ.nextParam_inner_deriv_chordDir hq]
  exact congrArg₂ χ.nextParam h1 h2

private theorem injOn_chordEnd : InjOn χ.chordEnd χ.window := by
  intro p hp q hq h
  rw [← χ.nextCollision_chordStart hp, ← χ.nextCollision_chordStart hq] at h
  exact χ.injOn_chordStart hp hq
    (χ.injOn_nextCollision (χ.chordStart_mem_strip p) (χ.chordStart_mem_strip q) h)

/-- The twist `∂_t ∂_s S = ∂_s ∂_t S` of the generating function at the chord `p`. -/
private def twist (p : ℝ × ℝ) : ℝ :=
  ‖χ p.2 - χ p.1‖⁻¹ * (o.areaForm (deriv χ p.1) (χ.chordDir p.1 p.2) *
    o.areaForm (deriv χ p.2) (χ.chordDir p.1 p.2))

/-- The initial state map is differentiable on the window, with Jacobian determinant the twist. -/
private theorem exists_hasFDerivAt_chordStart (hχ : Differentiable ℝ (deriv χ)) {p : ℝ × ℝ}
    (hp : p ∈ χ.window) :
    ∃ L : ℝ × ℝ →L[ℝ] ℝ × ℝ, HasFDerivAt χ.chordStart L p ∧ L.det = χ.twist p := by
  have h := χ.apply_ne_of_mem_Ioo hp
  set g : ℝ × ℝ → ℝ := fun q ↦ ⟪deriv χ q.1, χ.chordDir q.1 q.2⟫
  have hg : HasFDerivAt g (fderiv ℝ g p) p :=
    (((hχ p.1).comp p differentiableAt_fst).inner ℝ (χ.differentiableAt_chordDir h)).hasFDerivAt
  refine ⟨(ContinuousLinearMap.fst ℝ ℝ ℝ).prod (fderiv ℝ g p), hasFDerivAt_fst.prodMk hg, ?_⟩
  -- The derivative along `(0, 1)` is the partial derivative `∂_t ∂_s S`.
  have ht : HasDerivAt (fun t ↦ g (p.1, t)) (fderiv ℝ g p (0, 1)) p.2 :=
    hg.comp_hasDerivAt_of_eq p.2 (HasDerivAt.prodMk (hasDerivAt_const _ _) (hasDerivAt_id _)) rfl
  have ht' : HasDerivAt (fun t ↦ g (p.1, t)) (χ.twist p) p.2 :=
    (χ.hasDerivAt_deriv_generatingFunction_left h).congr_of_eventuallyEq
      (by filter_upwards [χ.continuous.continuousAt.eventually_ne h] with t' ht'
          exact ((χ.hasDerivAt_generatingFunction_left ht').deriv).symm)
  rw [ContinuousLinearMap.det, LinearMap.det_finTwoProd]
  simp [ht.unique ht']

/-- The final state map is differentiable on the window, with Jacobian determinant the twist. -/
private theorem exists_hasFDerivAt_chordEnd (hχ : Differentiable ℝ (deriv χ)) {p : ℝ × ℝ}
    (hp : p ∈ χ.window) :
    ∃ L : ℝ × ℝ →L[ℝ] ℝ × ℝ, HasFDerivAt χ.chordEnd L p ∧ L.det = χ.twist p := by
  have h := χ.apply_ne_of_mem_Ioo hp
  set g : ℝ × ℝ → ℝ := fun q ↦ ⟪deriv χ q.2, χ.chordDir q.1 q.2⟫
  have hg : HasFDerivAt g (fderiv ℝ g p) p :=
    (((hχ p.2).comp p differentiableAt_snd).inner ℝ (χ.differentiableAt_chordDir h)).hasFDerivAt
  refine ⟨(ContinuousLinearMap.snd ℝ ℝ ℝ).prod (fderiv ℝ g p), hasFDerivAt_snd.prodMk hg, ?_⟩
  -- The derivative along `(1, 0)` is minus the partial derivative `∂_s ∂_t S`.
  have hs : HasDerivAt (fun s ↦ g (s, p.2)) (fderiv ℝ g p (1, 0)) p.1 :=
    hg.comp_hasDerivAt_of_eq p.1 (HasDerivAt.prodMk (hasDerivAt_id _) (hasDerivAt_const _ _)) rfl
  have hs' : HasDerivAt (fun s ↦ g (s, p.2)) (-χ.twist p) p.1 :=
    (χ.hasDerivAt_deriv_generatingFunction_right h).neg.congr_of_eventuallyEq
      (by filter_upwards [χ.continuous.continuousAt.eventually_ne h.symm] with s' hs'
          rw [Pi.neg_apply, (χ.hasDerivAt_generatingFunction_right hs'.symm).deriv, neg_neg])
  rw [ContinuousLinearMap.det, LinearMap.det_finTwoProd]
  simp [hs.unique hs']

/-- The initial and final state maps send every measurable set of chords to sets of states of the
same area, since their Jacobian determinants agree. -/
private theorem volume_image_chordStart (hχ : Differentiable ℝ (deriv χ)) {K : Set (ℝ × ℝ)}
    (hK : MeasurableSet K) (hKw : K ⊆ χ.window) :
    volume (χ.chordStart '' K) = volume (χ.chordEnd '' K) := by
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  choose! L₁ hL₁ hdet₁ using fun p (hp : p ∈ χ.window) ↦ χ.exists_hasFDerivAt_chordStart hχ hp
  choose! L₂ hL₂ hdet₂ using fun p (hp : p ∈ χ.window) ↦ χ.exists_hasFDerivAt_chordEnd hχ hp
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image volume hK
      (fun p hp ↦ (hL₁ p (hKw hp)).hasFDerivWithinAt) (χ.injOn_chordStart.mono hKw),
    ← lintegral_abs_det_fderiv_eq_addHaar_image volume hK
      (fun p hp ↦ (hL₂ p (hKw hp)).hasFDerivWithinAt) (χ.injOn_chordEnd.mono hKw)]
  exact setLIntegral_congr_fun hK fun p hp ↦ by rw [hdet₁ p (hKw hp), hdet₂ p (hKw hp)]

/-! ### The next-collision map preserves area -/

/-- The inclusion of the strip `ℝ × (-1, 1)` in the plane. -/
private def stripIncl (x : ℝ × Ioo (-1 : ℝ) 1) : ℝ × ℝ :=
  (x.1, x.2)

@[simp]
private theorem stripIncl_apply (x : ℝ × Ioo (-1 : ℝ) 1) : stripIncl x = (x.1, (x.2 : ℝ)) :=
  rfl

private theorem stripIncl_eq_prodMap : stripIncl = Prod.map id ((↑) : Ioo (-1 : ℝ) 1 → ℝ) :=
  rfl

private theorem measurableEmbedding_stripIncl : MeasurableEmbedding stripIncl := by
  rw [stripIncl_eq_prodMap]
  exact MeasurableEmbedding.id.prodMap (MeasurableEmbedding.subtypeVal measurableSet_Ioo)

/-- The inclusion of the strip carries its measure to Lebesgue measure. -/
private theorem volume_image_stripIncl (A : Set (ℝ × Ioo (-1 : ℝ) 1)) :
    volume (stripIncl '' A) = (volume.prod (volume.comap Subtype.val)) A := by
  have hS : MeasurableSet ((univ : Set ℝ) ×ˢ Ioo (-1 : ℝ) 1) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  have hmp : MeasurePreserving stripIncl (volume.prod (volume.comap Subtype.val))
      (volume.restrict (univ ×ˢ Ioo (-1 : ℝ) 1)) := by
    rw [stripIncl_eq_prodMap, Measure.volume_eq_prod]
    exact measurePreserving_prodMap_subtype_coe _ _ measurableSet_Ioo
  conv_rhs => rw [← measurableEmbedding_stripIncl.injective.preimage_image A]
  rw [hmp.measure_preimage_emb measurableEmbedding_stripIncl, Measure.restrict_apply' hS,
    inter_eq_left.2]
  rintro _ ⟨x, -, rfl⟩
  exact ⟨mem_univ _, x.2.property⟩

private theorem stripIncl_nextCollisionEquiv (x : ℝ × Ioo (-1 : ℝ) 1) :
    stripIncl (χ.nextCollisionEquiv x) = χ.nextCollision (stripIncl x) := by
  simp [nextCollision_apply]

/-- The state `x` of the strip is the initial state of its chord. -/
private theorem chordStart_eq_stripIncl (x : ℝ × Ioo (-1 : ℝ) 1) :
    χ.chordStart (x.1, χ.nextParam x.1 x.2) = stripIncl x := by
  rw [stripIncl_apply]
  exact χ.chordStart_nextParam x.2.property

private theorem stripIncl_mem_image_chordEnd (x : ℝ × Ioo (-1 : ℝ) 1) :
    stripIncl x ∈ χ.chordEnd '' χ.window := by
  set z := χ.nextCollisionEquiv.symm x
  refine ⟨(z.1, χ.nextParam z.1 z.2), χ.nextParam_mem_Ioo (s := z.1) z.2.property, ?_⟩
  rw [← χ.nextCollision_chordStart (χ.nextParam_mem_Ioo (s := z.1) z.2.property),
    chordStart_eq_stripIncl, ← stripIncl_nextCollisionEquiv, Equiv.apply_symm_apply]

/-- Preimages under the next-collision map, read in chord coordinates: a state lies in the
preimage of `A` exactly when it is the initial state of a chord whose final state lies in `A`. -/
private theorem image_preimage_nextCollisionEquiv (A : Set (ℝ × Ioo (-1 : ℝ) 1)) :
    stripIncl '' (χ.nextCollisionEquiv ⁻¹' A) =
      χ.chordStart '' (χ.window ∩ χ.chordEnd ⁻¹' (stripIncl '' A)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hp := χ.nextParam_mem_Ioo (s := x.1) x.2.property
    refine ⟨(x.1, χ.nextParam x.1 x.2), ⟨hp, ?_⟩, χ.chordStart_eq_stripIncl x⟩
    rw [mem_preimage, ← χ.nextCollision_chordStart hp, chordStart_eq_stripIncl,
      ← stripIncl_nextCollisionEquiv]
    exact mem_image_of_mem _ hx
  · rintro ⟨p, ⟨hp, a, ha, hpa⟩, rfl⟩
    refine ⟨(p.1, ⟨_, χ.inner_deriv_chordDir_mem_Ioo p.1 p.2⟩), ?_, by simp [chordStart]⟩
    have : χ.nextCollisionEquiv (p.1, ⟨_, χ.inner_deriv_chordDir_mem_Ioo p.1 p.2⟩) = a := by
      refine measurableEmbedding_stripIncl.injective ?_
      rw [hpa, stripIncl_nextCollisionEquiv, ← χ.nextCollision_chordStart hp]
      simp [chordStart]
    rw [mem_preimage, this]
    exact ha

private theorem measurableSet_window_inter (A : Set (ℝ × Ioo (-1 : ℝ) 1)) (hA : MeasurableSet A) :
    MeasurableSet (χ.window ∩ χ.chordEnd ⁻¹' (stripIncl '' A)) :=
  χ.isOpen_window.measurableSet.inter
    (χ.measurable_chordEnd (measurableEmbedding_stripIncl.measurableSet_image.2 hA))

variable {χ}

/-- **The next-collision map preserves area.** If the arclength parametrization `χ` is twice
differentiable, the next-collision map `B(s, v) = (t, w)` preserves Lebesgue measure `ds dv` on the
strip `ℝ × (-1, 1)`. -/
theorem measurePreserving_nextCollisionEquiv (hχ : Differentiable ℝ (deriv χ)) :
    MeasurePreserving χ.nextCollisionEquiv (volume.prod (volume.comap Subtype.val))
      (volume.prod (volume.comap Subtype.val)) := by
  choose! L hL _ using fun p (hp : p ∈ χ.window) ↦ χ.exists_hasFDerivAt_chordStart hχ hp
  have hmeas : Measurable χ.nextCollisionEquiv := fun A hA ↦ by
    rw [← measurableEmbedding_stripIncl.measurableSet_image, image_preimage_nextCollisionEquiv]
    exact measurable_image_of_fderivWithin (χ.measurableSet_window_inter A hA)
      (fun p hp ↦ (hL p hp.1).hasFDerivWithinAt) (χ.injOn_chordStart.mono inter_subset_left)
  refine ⟨hmeas, Measure.ext fun A hA ↦ ?_⟩
  rw [Measure.map_apply hmeas hA, ← volume_image_stripIncl, image_preimage_nextCollisionEquiv,
    χ.volume_image_chordStart hχ (χ.measurableSet_window_inter A hA) inter_subset_left,
    image_inter_preimage, inter_eq_right.2, volume_image_stripIncl]
  rintro _ ⟨x, -, rfl⟩
  exact χ.stripIncl_mem_image_chordEnd x

/-- **The billiard map preserves area.** If the arclength parametrization `χ` is twice
differentiable, the billiard map `β` on the space of collision states `AddCircle L × (-1, 1)`
preserves the product of the Haar measure of `AddCircle L`, of total mass `L`, with Lebesgue
measure on `(-1, 1)`. -/
theorem measurePreserving_billiardMap (hχ : Differentiable ℝ (deriv χ)) :
    MeasurePreserving χ.billiardMap (volume.prod (volume.comap Subtype.val))
      (volume.prod (volume.comap Subtype.val)) := by
  refine AddCircle.measurePreserving_of_lift (measurePreserving_nextCollisionEquiv hχ)
    (fun x ↦ ?_) fun x ↦ by simp
  ext
  · simp [χ.nextParam_add_period x.2.property]
  · simp [χ.nextTangential_add_period x.2.property]

/-! ### Poincaré recurrence -/

/-- **Poincaré recurrence for convex billiards.** If the arclength parametrization `χ` is twice
differentiable, every nonempty open set `U` of collision states contains a state that returns to
`U` after a positive number of bounces. -/
theorem exists_mem_iterate_billiardMap_mem (hχ : Differentiable ℝ (deriv χ))
    {U : Set (AddCircle χ.period × Ioo (-1 : ℝ) 1)} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, ∃ m ≠ 0, χ.billiardMap^[m] x ∈ U :=
  (measurePreserving_billiardMap hχ).exists_mem_iterate_mem hU.nullMeasurableSet
    (hU.measure_ne_zero _ hne)

/-- **Poincaré recurrence for convex billiards, almost everywhere.** If the arclength
parametrization `χ` is twice differentiable, almost every collision state returns infinitely often
to each of its neighbourhoods. -/
theorem ae_frequently_iterate_billiardMap_mem (hχ : Differentiable ℝ (deriv χ)) :
    ∀ᵐ x ∂(volume.prod (volume.comap Subtype.val)), ∀ U ∈ 𝓝 x,
      ∃ᶠ n in atTop, χ.billiardMap^[n] x ∈ U :=
  (measurePreserving_billiardMap hχ).conservative.ae_frequently_mem_of_mem_nhds

end StrictConvexBilliardTable

end TauCeti
