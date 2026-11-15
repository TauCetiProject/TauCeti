/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Sard.OutermostStratum
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The Morse--Sard theorem on coordinate orthants and half-spaces

Let `E` and `F` be finite-dimensional real normed spaces, `b : Module.Basis ι ℝ E` a basis of `E`,
and `S : Set ι` a subset of the basis indices. The region
`R = {x : E | ∀ i ∈ S, 0 ≤ b.repr x i}` cut out by the nonnegativity of the `S`-coordinates
includes the full space (`S = ∅`), Euclidean half-spaces (`#S = 1`), the positive quadrant
(`S = univ`), and arbitrary finite products of these. This file proves the Morse--Sard theorem for
maps defined on subsets of `R` whose smoothness and criticality are read *within* `R`, at the same
sharp regularity `n ≥ max 1 (finrank ℝ E - finrank ℝ F + 1)` as on an open set.

The region `R` is partitioned into finitely many open faces indexed by the subset `T ⊆ S` of
`S`-coordinates that vanish at a point. For fixed `T ⊆ S`, let `V` be the linear subspace of `E`
where every `T`-coordinate vanishes, and let `Ω ⊆ V` be the open subset where every remaining
coordinate in `S \ T` is strictly positive. Because `V.subtypeL` maps `Ω` into `R` and `Ω` is open
in `V`, composing `f` with `V.subtypeL` turns `C^n` smoothness within `R` into genuine `C^n`
smoothness at points of `Ω`, and by the chain rule its Fréchet derivative there is
`(fderivWithin ℝ f R x).comp V.subtypeL`. Whenever `fderivWithin ℝ f R x` fails to be surjective,
so does that composite derivative. Since `finrank ℝ V ≤ finrank ℝ E`, Sard's regularity threshold
on `V` is no larger than on `E`, so `TauCeti.addHaar_image_criticalPoints_eq_zero` makes the
critical values coming from each face null, and finite additivity over `T ⊆ S` concludes.

The hypothesis `U ⊆ R` in the set-wise theorems cannot be omitted: outside `closure R` the
derivative within `R` vanishes identically even for the identity map.

## Main results

* `TauCeti.addHaar_image_criticalPoints_within_nonneg_eq_zero`: **the Morse--Sard theorem** on a
  subset of `{x | ∀ i ∈ S, 0 ≤ b.repr x i}`, at the sharp regularity
  `max 1 (finrank ℝ E - finrank ℝ F + 1)`.
* `ContDiffOn.addHaar_image_criticalPoints_within_nonneg_eq_zero`: its global form on the region.
* `TauCeti.interior_image_criticalPoints_within_nonneg_eq_empty`: the measure-free restatement,
  that the critical values have empty interior.
* `ContDiffOn.dense_compl_image_criticalPoints_within_nonneg`: the complement of the critical
  values is dense, without requiring a measurable structure on the target.

## References

* A. Sard, *The measure of the critical values of differentiable maps*, Bull. Amer. Math. Soc.
  48 (1942), 883–890.
* J. Milnor, *Topology from the Differentiable Viewpoint*, The University Press of Virginia,
  1965, Section 3.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 6.10.
-/

public section

open Function MeasureTheory MeasureTheory.Measure Module Set

open scoped ContDiff Topology

namespace TauCeti

section OpenPos

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*}

/-- In a finite-dimensional real normed space, the set where a given subset of basis coordinates
is strictly positive is open, since a basis of a finite-dimensional space has a finite index
type and each coordinate functional is continuous. -/
private theorem isOpen_setOf_forall_pos_repr (b : Module.Basis ι ℝ E) (A : Set ι) :
    IsOpen {x : E | ∀ i ∈ A, 0 < b.repr x i} := by
  let _ : Fintype ι := FiniteDimensional.fintypeBasisIndex b
  have hEq : {x : E | ∀ i ∈ A, 0 < b.repr x i} = ⋂ i ∈ A, (b.coord i) ⁻¹' Ioi 0 := by
    ext x
    simp [Module.Basis.coord_apply]
  rw [hEq]
  exact A.toFinite.isOpen_biInter fun i _ ↦
    isOpen_Ioi.preimage (b.coord i).continuous_of_finiteDimensional

end OpenPos

section FaceSubmodule

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*}

/-- The coordinate subspace where all `T`-coordinates of `b` vanish. -/
private noncomputable def faceSubmodule (b : Module.Basis ι ℝ E) (T : Set ι) : Submodule ℝ E :=
  ⨅ i ∈ T, LinearMap.ker (b.coord i)

private theorem mem_faceSubmodule_iff {b : Module.Basis ι ℝ E} {T : Set ι} {x : E} :
    x ∈ faceSubmodule b T ↔ ∀ i ∈ T, b.repr x i = 0 := by
  simp [faceSubmodule, Module.Basis.coord_apply]

end FaceSubmodule

section MorseSard

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} {b : Module.Basis ι ℝ E} {S : Set ι}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {U : Set E} {f : E → F}

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
/-- Restriction to an open face: at a point `w` of `faceSubmodule b T` whose remaining
`S`-coordinates are strictly positive, smoothness of `f` within `{x | ∀ i ∈ S, 0 ≤ b.repr x i}`
and nonsurjectivity of `fderivWithin` pass to genuine `ContDiffAt` smoothness and nonsurjectivity
of `fderiv` for `f ∘ (faceSubmodule b T).subtypeL`. -/
private theorem contDiffAt_and_not_surjective_fderiv_comp_faceSubmodule {n : ℕ∞ω} (hn : n ≠ 0)
    {T : Set ι} {w : faceSubmodule b T} (hw : ∀ i ∈ S \ T, 0 < b.repr (w : E) i)
    (hf : ContDiffWithinAt ℝ n f {x : E | ∀ i ∈ S, 0 ≤ b.repr x i} (w : E))
    (hcrit : ¬ Surjective (fderivWithin ℝ f {x : E | ∀ i ∈ S, 0 ≤ b.repr x i} (w : E))) :
    ContDiffAt ℝ n (f ∘ (faceSubmodule b T).subtypeL) w ∧
      ¬ Surjective (fderiv ℝ (f ∘ (faceSubmodule b T).subtypeL) w) := by
  let V := faceSubmodule b T
  let R : Set E := {x : E | ∀ i ∈ S, 0 ≤ b.repr x i}
  let Ω : Set V := {u : V | ∀ i ∈ S \ T, 0 < b.repr (u : E) i}
  have hΩopen : IsOpen Ω :=
    (isOpen_setOf_forall_pos_repr b (S \ T)).preimage V.subtypeL.continuous
  have hΩnhds : Ω ∈ 𝓝 w := hΩopen.mem_nhds hw
  have hmaps : MapsTo V.subtypeL Ω R := by
    intro u hu i hi
    by_cases hiT : i ∈ T
    · exact ((mem_faceSubmodule_iff.1 u.2 i hiT).symm).le
    · exact (hu i ⟨hi, hiT⟩).le
  have hcompC : ContDiffAt ℝ n (f ∘ V.subtypeL) w :=
    (hf.comp w V.subtypeL.contDiff.contDiffWithinAt hmaps).contDiffAt hΩnhds
  refine ⟨hcompC, fun hsurj ↦ hcrit ?_⟩
  have hfd : HasFDerivWithinAt f (fderivWithin ℝ f R (w : E)) R (w : E) :=
    (hf.differentiableWithinAt hn).hasFDerivWithinAt
  have hcompD : HasFDerivAt (f ∘ V.subtypeL) ((fderivWithin ℝ f R (w : E)).comp V.subtypeL) w :=
    (hfd.comp w V.subtypeL.hasFDerivWithinAt hmaps).hasFDerivAt hΩnhds
  rw [hcompD.fderiv] at hsurj
  exact Function.Surjective.of_comp hsurj

/-- Each open face `{x ∈ U | ∀ i ∈ S, b.repr x i = 0 ↔ i ∈ T}` (`T ⊆ S`) sends its critical
points within `{x | ∀ i ∈ S, 0 ≤ b.repr x i}` to a Haar-null set in `F`. -/
private theorem addHaar_image_criticalPoints_face_eq_zero (ν : Measure F) [IsAddHaarMeasure ν]
    {n : ℕ∞ω} {T : Set ι} (hTS : T ⊆ S)
    (hU : U ⊆ {x : E | ∀ i ∈ S, 0 ≤ b.repr x i})
    (hf : ∀ x ∈ U, ContDiffWithinAt ℝ n f {x : E | ∀ i ∈ S, 0 ≤ b.repr x i} x)
    (hk : ((finrank ℝ E - finrank ℝ F + 1 : ℕ) : ℕ∞ω) ≤ n) :
    ν (f '' ({x ∈ U | ∀ i ∈ S, b.repr x i = 0 ↔ i ∈ T} ∩
      {x | ¬ Surjective (fderivWithin ℝ f {x : E | ∀ i ∈ S, 0 ≤ b.repr x i} x)})) = 0 := by
  have hn : n ≠ 0 := fun h ↦ by simp [h] at hk
  let V := faceSubmodule b T
  let R : Set E := {x : E | ∀ i ∈ S, 0 ≤ b.repr x i}
  let W : Set V := {w : V | (w : E) ∈ U ∧ (∀ i ∈ S, b.repr (w : E) i = 0 ↔ i ∈ T) ∧
    ¬ Surjective (fderivWithin ℝ f R (w : E))}
  have hkV : ((finrank ℝ V - finrank ℝ F + 1 : ℕ) : ℕ∞ω) ≤ n :=
    le_trans (Nat.cast_le.2 (Nat.add_le_add_right
      (Nat.sub_le_sub_right (Submodule.finrank_le V) _) 1)) hk
  have key : ∀ w ∈ W, ContDiffAt ℝ n (f ∘ V.subtypeL) w ∧
      ¬ Surjective (fderiv ℝ (f ∘ V.subtypeL) w) := by
    rintro w ⟨hwU, hwT, hwcrit⟩
    refine contDiffAt_and_not_surjective_fderiv_comp_faceSubmodule hn (fun i hi ↦ ?_)
      (hf (w : E) hwU) hwcrit
    exact lt_of_le_of_ne (hU hwU i hi.1) fun h0 ↦ hi.2 ((hwT i hi.1).1 h0.symm)
  have hnull := addHaar_image_criticalPoints_eq_zero (U := W) ν
    (fun w hw ↦ (key w hw).1) hkV
  refine measure_mono_null ?_ hnull
  rintro _ ⟨x, ⟨⟨hxU, hxT⟩, hxcrit⟩, rfl⟩
  have hxV : x ∈ V := mem_faceSubmodule_iff.2 fun i hi ↦ (hxT i (hTS hi)).2 hi
  exact ⟨⟨x, hxV⟩, ⟨⟨hxU, hxT, hxcrit⟩, (key ⟨x, hxV⟩ ⟨hxU, hxT, hxcrit⟩).2⟩, rfl⟩

/-- **The Morse--Sard theorem on a coordinate orthant or half-space**, on a set. Let
`R = {x : E | ∀ i ∈ S, 0 ≤ b.repr x i}` be the region cut out by the nonnegativity of the
`S`-coordinates of a basis `b`, and let `U ⊆ R`. If `f` is `C^n` within `R` at every point of `U`,
with `n > finrank ℝ E - finrank ℝ F` and `n ≥ 1`, then the values taken at the points of `U` where
`fderivWithin ℝ f R` is not surjective have additive Haar measure zero. -/
theorem addHaar_image_criticalPoints_within_nonneg_eq_zero (ν : Measure F) [IsAddHaarMeasure ν]
    {n : ℕ∞ω} (hU : U ⊆ {x : E | ∀ i ∈ S, 0 ≤ b.repr x i})
    (hf : ∀ x ∈ U, ContDiffWithinAt ℝ n f {x : E | ∀ i ∈ S, 0 ≤ b.repr x i} x)
    (hk : ((finrank ℝ E - finrank ℝ F + 1 : ℕ) : ℕ∞ω) ≤ n) :
    ν (f '' (U ∩
      {x | ¬ Surjective (fderivWithin ℝ f {x : E | ∀ i ∈ S, 0 ≤ b.repr x i} x)})) = 0 := by
  let _ : Fintype ι := FiniteDimensional.fintypeBasisIndex b
  set R : Set E := {x : E | ∀ i ∈ S, 0 ≤ b.repr x i}
  have hsub : U ∩ {x | ¬ Surjective (fderivWithin ℝ f R x)} ⊆
      ⋃ T : {T : Set ι // T ⊆ S},
        ({x ∈ U | ∀ i ∈ S, b.repr x i = 0 ↔ i ∈ T.1} ∩
          {x | ¬ Surjective (fderivWithin ℝ f R x)}) := by
    rintro x ⟨hxU, hxcrit⟩
    refine mem_iUnion.2 ⟨⟨{i ∈ S | b.repr x i = 0}, fun i hi ↦ hi.1⟩, ⟨hxU, fun i hi ↦ ?_⟩, hxcrit⟩
    exact ⟨fun h0 ↦ ⟨hi, h0⟩, fun h ↦ h.2⟩
  refine measure_mono_null (image_mono hsub) ?_
  rw [image_iUnion]
  exact measure_iUnion_null fun T ↦ addHaar_image_criticalPoints_face_eq_zero ν T.2 hU hf hk

/-- **The Morse--Sard theorem on a coordinate orthant or half-space.** If `f` is `C^n` on
`R = {x : E | ∀ i ∈ S, 0 ≤ b.repr x i}` with `n > finrank ℝ E - finrank ℝ F` and `n ≥ 1`, then the
values it takes at the points of `R` where `fderivWithin ℝ f R` is not surjective form a set of
additive Haar measure zero. -/
theorem _root_.ContDiffOn.addHaar_image_criticalPoints_within_nonneg_eq_zero {n : ℕ∞ω}
    (hf : ContDiffOn ℝ n f {x : E | ∀ i ∈ S, 0 ≤ b.repr x i}) (ν : Measure F) [IsAddHaarMeasure ν]
    (hk : ((finrank ℝ E - finrank ℝ F + 1 : ℕ) : ℕ∞ω) ≤ n) :
    ν (f '' ({x : E | ∀ i ∈ S, 0 ≤ b.repr x i} ∩
      {x | ¬ Surjective (fderivWithin ℝ f {x : E | ∀ i ∈ S, 0 ≤ b.repr x i} x)})) = 0 :=
  TauCeti.addHaar_image_criticalPoints_within_nonneg_eq_zero ν Subset.rfl hf hk

end MorseSard

section EmptyInterior

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} {b : Module.Basis ι ℝ E} {S : Set ι}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {U : Set E} {f : E → F}

/-- **The Morse--Sard theorem on a coordinate orthant or half-space**, without a measurable
structure on the target: for `U ⊆ R = {x : E | ∀ i ∈ S, 0 ≤ b.repr x i}`, if `f` is `C^n` within
`R` at every point of `U` with `n > finrank ℝ E - finrank ℝ F` and `n ≥ 1`, then the critical
values taken on `U` have empty interior. -/
theorem interior_image_criticalPoints_within_nonneg_eq_empty {n : ℕ∞ω}
    (hU : U ⊆ {x : E | ∀ i ∈ S, 0 ≤ b.repr x i})
    (hf : ∀ x ∈ U, ContDiffWithinAt ℝ n f {x : E | ∀ i ∈ S, 0 ≤ b.repr x i} x)
    (hk : ((finrank ℝ E - finrank ℝ F + 1 : ℕ) : ℕ∞ω) ≤ n) :
    interior (f '' (U ∩
      {x | ¬ Surjective (fderivWithin ℝ f {x : E | ∀ i ∈ S, 0 ≤ b.repr x i} x)})) = ∅ := by
  borelize F
  exact Measure.interior_eq_empty_of_null
    (TauCeti.addHaar_image_criticalPoints_within_nonneg_eq_zero addHaar hU hf hk)

/-- For a `C^n` map on `R = {x : E | ∀ i ∈ S, 0 ≤ b.repr x i}` with
`n > finrank ℝ E - finrank ℝ F` and `n ≥ 1`, the complement of the critical values taken on `R` is
dense in `F`, without requiring a measurable structure on `F`. -/
theorem _root_.ContDiffOn.dense_compl_image_criticalPoints_within_nonneg {n : ℕ∞ω}
    (hf : ContDiffOn ℝ n f {x : E | ∀ i ∈ S, 0 ≤ b.repr x i})
    (hk : ((finrank ℝ E - finrank ℝ F + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense (f '' ({x : E | ∀ i ∈ S, 0 ≤ b.repr x i} ∩
      {x | ¬ Surjective (fderivWithin ℝ f {x : E | ∀ i ∈ S, 0 ≤ b.repr x i} x)}))ᶜ := by
  apply interior_eq_empty_iff_dense_compl.1
  exact interior_image_criticalPoints_within_nonneg_eq_empty Subset.rfl hf hk

end EmptyInterior

end TauCeti

end
