/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Euclidean.RadialContraction
public import TauCeti.Geometry.Manifold.SmoothEmbedding.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Basic
import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions

/-!
# Shrinking smooth embeddings near their centre

Positive dilations of the source give a smooth isotopy of an embedding of a real normed
space, fixing the image of the origin. A bounded part of the source can consequently be
moved inside any neighbourhood of that image. For a star-convex source subset, the motion
stays inside its original image throughout the isotopy.

This is the shrinking step used to compare ball embeddings in a common ambient chart.
It gives an isotopy through embeddings; extending it to an ambient isotopy is a separate
assertion. Neither finite dimensionality nor compactness of the source is required.

A dilation moves only bounded parts of the source into a neighbourhood of the centre. When the
source is finite-dimensional, the radial contractions `TauCeti.radialContraction` move all of it:
precomposing with them gives a smooth isotopy from an embedding of `E` to one whose image lies in
any prescribed neighbourhood of the centre (`compRadialContractionIsotopy`). Postcomposing an
embedding into `E` with them gives a smooth isotopy into a Euclidean ball which never leaves a
Euclidean ball about the centre containing the original image (`transRadialContractionIsotopy`).

## Main definitions

* `TauCeti.SmoothEmbedding.shrinkingIsotopy`: shrinking by positive dilations of the source.
* `TauCeti.SmoothEmbedding.compRadialContractionIsotopy`: shrinking by radial contractions of a
  finite-dimensional source.
* `TauCeti.SmoothEmbedding.transRadialContractionIsotopy`: radial contraction of the target of an
  embedding into a finite-dimensional space.

Reference: M. Hirsch, *Differential Topology*, GTM 33, Chapter 4, §6, Theorem 6.6.
The bounded-set shrinking argument uses Mathlib's von Neumann boundedness and small-sets API.
-/

public section

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Pointwise

namespace TauCeti.SmoothEmbedding

variable {E F H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {J : ModelWithCorners ℝ F H} [TopologicalSpace N] [ChartedSpace H N]
  {n : ℕ∞ω}

/-- Reparametrize an embedding by positive source dilations, from scale one to scale `c`.
The image of the origin remains fixed, and every time slice is an embedding. -/
def shrinkingIsotopy (f : SmoothEmbedding 𝓘(ℝ, E) J n E N) {c : ℝ} (hc : 0 < c) :
    SmoothIsotopy f.toContMDiffMap
      (f.toContMDiffMap.comp (c • ContMDiffMap.id)) where
  toContMDiffMap := ⟨fun p => f ((1 - (p.1 : ℝ) + (p.1 : ℝ) * c) • p.2),
    f.contMDiff.comp (((contMDiff_const.sub
      (contMDiff_subtypeVal_Icc.comp contMDiff_fst)).add
        ((contMDiff_subtypeVal_Icc.comp contMDiff_fst).mul contMDiff_const)).smul
          contMDiff_snd)⟩
  map_zero_left x := by simp
  map_one_left x := by
    simp only [ContMDiffMap.comp_apply, ContMDiffMap.coe_smul, Pi.smul_apply]
    dsimp [ContMDiffMap.id]
    simp
  isSmoothEmbedding t := by
    have hpos : 0 < 1 - (t : ℝ) + (t : ℝ) * c := by
      have := t.2.1
      have := t.2.2
      by_cases ht : (t : ℝ) = 0
      · simp [ht]
      · have := mul_pos (lt_of_le_of_ne t.2.1 (Ne.symm ht)) hc
        linarith
    let e : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (Units.mk0 _ hpos.ne')
    simpa [e, Function.comp_def] using
      isSmoothEmbedding_comp_continuousLinearEquiv e f.isSmoothEmbedding

/-- The shrinking motion interpolates linearly between its positive dilation factors. -/
@[simp] theorem shrinkingIsotopy_apply (f : SmoothEmbedding 𝓘(ℝ, E) J n E N)
    {c : ℝ} (hc : 0 < c) (p : unitInterval × E) :
    f.shrinkingIsotopy hc p = f ((1 - (p.1 : ℝ) + (p.1 : ℝ) * c) • p.2) := (rfl)

/-- Shrinking a star-convex subset never leaves its original embedded image. -/
theorem shrinkingIsotopy_mapsTo_image (f : SmoothEmbedding 𝓘(ℝ, E) J n E N)
    {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) {s : Set E} (hs : StarConvex ℝ 0 s)
    (t : unitInterval) : MapsTo (fun x => f.shrinkingIsotopy hc (t, x)) s (f '' s) := by
  intro x hx
  have h₀ : 0 ≤ 1 - (t : ℝ) + (t : ℝ) * c := by
    have := t.2.1
    have := t.2.2
    positivity
  have h₁ : 1 - (t : ℝ) + (t : ℝ) * c ≤ 1 := by
    have := t.2.1
    nlinarith
  exact ⟨_, hs.smul_mem hx h₀ h₁, (f.shrinkingIsotopy_apply hc (t, x)).symm⟩

/-- A bounded part of a smooth embedding can be mapped into any neighbourhood of its
centre at the endpoint of a shrinking isotopy. For a star-convex source subset,
`shrinkingIsotopy_mapsTo_image` gives containment in its original image throughout the motion. -/
theorem exists_shrinkingIsotopy_mapsTo (f : SmoothEmbedding 𝓘(ℝ, E) J n E N)
    {s : Set E} (hs : Bornology.IsBounded s) {U : Set N} (hU : U ∈ 𝓝 (f 0)) :
    ∃ (c : ℝ) (hc : 0 < c), c ≤ 1 ∧
      MapsTo (fun x => f.shrinkingIsotopy hc (1, x)) s U := by
  have hpre : f ⁻¹' U ∈ 𝓝 (0 : E) := f.contMDiff.continuous.continuousAt hU
  have hnear : ∀ᶠ c : ℝ in 𝓝 0, MapsTo (fun x => c • x) s (f ⁻¹' U) := by
    simpa only [mapsTo_iff_image_subset, image_smul] using
      ((NormedSpace.isVonNBounded_iff ℝ).mpr hs).tendsto_smallSets_nhds.eventually
        (eventually_smallSets_subset.mpr hpre)
  obtain ⟨a, b, hab, hsmall⟩ := hnear.exists_Ioo_subset
  obtain ⟨c, hc, hcb⟩ := exists_between (lt_min hab.2 (by norm_num : (0 : ℝ) < 1))
  refine ⟨c, hc, (hcb.trans_le (min_le_right _ _)).le, ?_⟩
  intro x hx
  simp only [shrinkingIsotopy_apply]
  simpa using hsmall ⟨hab.1.trans hc, hcb.trans_le (min_le_left _ _)⟩ hx

end TauCeti.SmoothEmbedding

namespace TauCeti

/-! ### Radial contractions -/

section RadialContraction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ∞ω}

/-- A radial contraction with nonnegative parameter is a local diffeomorphism. -/
theorem isLocalDiffeomorph_radialContraction (c : E) (hn : n ≤ ∞) {κ : ℝ} (hκ : 0 ≤ κ) :
    IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) n (radialContraction c κ) := by
  rcases hκ.eq_or_lt with rfl | hκ
  · have : radialContraction c 0 = id := funext (radialContraction_zero c)
    rw [this]
    exact (Diffeomorph.refl 𝓘(ℝ, E) E n).isLocalDiffeomorph
  obtain ⟨Θ, hsource, hΘ, hΘsymm, hΘeq⟩ := exists_radialContraction_eq_openPartialHomeomorph c hκ
  exact fun y => isLocalDiffeomorphAt_of_eqOn
    (Φ := PartialDiffeomorph.ofOpenPartialHomeomorph Θ (hΘ.of_le hn) (hΘsymm.of_le hn))
    (by simp [hsource])
    fun z _ => by simp [← hΘeq]

/-- A `C^n` family of radial contractions with nonnegative parameters, applied to a `C^n`
family of points, is `C^n` for `n ≤ ∞`. -/
theorem contMDiff_radialContraction {E' H' X : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace X]
    [ChartedSpace H' X] (c : E) (hn : n ≤ ∞) {κ : X → ℝ} {y : X → E} (hκ : ContMDiff J 𝓘(ℝ) n κ)
    (hκ₀ : ∀ x, 0 ≤ κ x) (hy : ContMDiff J 𝓘(ℝ, E) n y) :
    ContMDiff J 𝓘(ℝ, E) n fun x => radialContraction c (κ x) (y x) :=
  ((contDiffOn_radialContraction c).of_le hn).contMDiffOn.comp_contMDiff (hκ.prodMk_space hy)
    fun x => add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (hκ₀ x) (sq_nonneg _))

namespace SmoothEmbedding

variable {F H N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {J : ModelWithCorners ℝ F H} [TopologicalSpace N] [ChartedSpace H N]
  {E₀ H₀ M : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [TopologicalSpace H₀]
  {I : ModelWithCorners ℝ E₀ H₀} [TopologicalSpace M] [ChartedSpace H₀ M]

/-- A smooth embedding of `E` precomposed with the radial contraction about `0` with parameter
`κ ≥ 0`, preserving any regularity `n ≤ ∞`. -/
def compRadialContraction (f : SmoothEmbedding 𝓘(ℝ, E) J n E N) (hn : n ≤ ∞)
    {κ : ℝ}
    (hκ : 0 ≤ κ) :
    SmoothEmbedding 𝓘(ℝ, E) J n E N :=
  f.compLocalDiffeomorph (radialContraction 0 κ) (isLocalDiffeomorph_radialContraction 0 hn hκ)
    (isEmbedding_radialContraction 0 hκ)

theorem coe_compRadialContraction (f : SmoothEmbedding 𝓘(ℝ, E) J n E N) (hn : n ≤ ∞)
    {κ : ℝ} (hκ : 0 ≤ κ) :
    ⇑(f.compRadialContraction hn hκ) = f ∘ radialContraction 0 κ := by
  rw [compRadialContraction, coe_compLocalDiffeomorph]

@[simp]
theorem compRadialContraction_apply (f : SmoothEmbedding 𝓘(ℝ, E) J n E N) (hn : n ≤ ∞)
    {κ : ℝ} (hκ : 0 ≤ κ) (x : E) :
    f.compRadialContraction hn hκ x = f (radialContraction 0 κ x) := by
  rw [coe_compRadialContraction, Function.comp_apply]

/-- The source contraction `t ↦ f ∘ radialContraction 0 (t κ)`, a smooth isotopy from `f` to
`f.compRadialContraction hn hκ` fixing the image of `0`, preserving regularity `n ≤ ∞`. -/
def compRadialContractionIsotopy (f : SmoothEmbedding 𝓘(ℝ, E) J n E N) (hn : n ≤ ∞)
    {κ : ℝ}
    (hκ : 0 ≤ κ) :
    SmoothIsotopy f.toContMDiffMap (f.compRadialContraction hn hκ).toContMDiffMap where
  toContMDiffMap := ⟨fun p => f (radialContraction 0 ((p.1 : ℝ) * κ) p.2),
    f.contMDiff.comp (contMDiff_radialContraction 0 hn
      ((contDiff_id.mul contDiff_const).contMDiff.comp
        (contMDiff_subtypeVal_Icc.comp contMDiff_fst))
      (fun p => mul_nonneg p.1.2.1 hκ) contMDiff_snd)⟩
  map_zero_left x := by simp
  map_one_left x := by simp
  isSmoothEmbedding t := by
    have h := (f.compRadialContraction hn (mul_nonneg t.2.1 hκ)).isSmoothEmbedding
    rwa [coe_compRadialContraction] at h

@[simp]
theorem compRadialContractionIsotopy_apply (f : SmoothEmbedding 𝓘(ℝ, E) J n E N) (hn : n ≤ ∞)
    {κ : ℝ}
    (hκ : 0 ≤ κ) (p : unitInterval × E) :
    f.compRadialContractionIsotopy hn hκ p = f (radialContraction 0 ((p.1 : ℝ) * κ) p.2) := (rfl)

/-- A smooth embedding into `E` followed by the radial contraction about `c` with parameter
`κ ≥ 0`, preserving any regularity `n ≤ ∞`. -/
def transRadialContraction (f : SmoothEmbedding I 𝓘(ℝ, E) n M E)
    (c : E) (hn : n ≤ ∞)
    {κ : ℝ}
    (hκ : 0 ≤ κ) :
    SmoothEmbedding I 𝓘(ℝ, E) n M E :=
  f.transLocalDiffeomorph (radialContraction c κ) (s := univ)
    (fun y _ => isLocalDiffeomorph_iff.1 (isLocalDiffeomorph_radialContraction c hn hκ) y)
    ((isEmbedding_radialContraction c hκ).comp IsEmbedding.subtypeVal) (subset_univ _)

theorem coe_transRadialContraction (f : SmoothEmbedding I 𝓘(ℝ, E) n M E)
    (c : E) (hn : n ≤ ∞)
    {κ : ℝ}
    (hκ : 0 ≤ κ) : ⇑(f.transRadialContraction c hn hκ) = radialContraction c κ ∘ f :=
  f.coe_transLocalDiffeomorph _ _ _ _

@[simp]
theorem transRadialContraction_apply (f : SmoothEmbedding I 𝓘(ℝ, E) n M E)
    (c : E) (hn : n ≤ ∞)
    {κ : ℝ}
    (hκ : 0 ≤ κ) (x : M) : f.transRadialContraction c hn hκ x = radialContraction c κ (f x) := by
  rw [coe_transRadialContraction, Function.comp_apply]

/-- The target contraction `t ↦ radialContraction c (t κ) ∘ f`, a smooth isotopy from `f` to
`f.transRadialContraction c hn hκ`, preserving regularity `n ≤ ∞`. -/
def transRadialContractionIsotopy (f : SmoothEmbedding I 𝓘(ℝ, E) n M E)
    (c : E) (hn : n ≤ ∞)
    {κ : ℝ}
    (hκ : 0 ≤ κ) :
    SmoothIsotopy f.toContMDiffMap (f.transRadialContraction c hn hκ).toContMDiffMap where
  toContMDiffMap := ⟨fun p => radialContraction c ((p.1 : ℝ) * κ) (f p.2),
    contMDiff_radialContraction c hn ((contDiff_id.mul contDiff_const).contMDiff.comp
        (contMDiff_subtypeVal_Icc.comp contMDiff_fst))
      (fun p => mul_nonneg p.1.2.1 hκ) (f.contMDiff.comp contMDiff_snd)⟩
  map_zero_left x := by simp
  map_one_left x := by simp
  isSmoothEmbedding t := by
    have h := (f.transRadialContraction c hn (mul_nonneg t.2.1 hκ)).isSmoothEmbedding
    rwa [coe_transRadialContraction] at h

@[simp]
theorem transRadialContractionIsotopy_apply (f : SmoothEmbedding I 𝓘(ℝ, E) n M E)
    (c : E) (hn : n ≤ ∞)
    {κ : ℝ} (hκ : 0 ≤ κ) (p : unitInterval × M) :
    f.transRadialContractionIsotopy c hn hκ p = radialContraction c ((p.1 : ℝ) * κ) (f p.2) := (rfl)

/-- The target contraction never leaves a Euclidean ball about its centre containing the original
image. -/
theorem transRadialContractionIsotopy_mem_ball (f : SmoothEmbedding I 𝓘(ℝ, E) n M E)
    (hn : n ≤ ∞) {c : E}
    {r κ : ℝ} (hκ : 0 ≤ κ) (hf : ∀ x, f x ∈ Euclidean.ball c r) (p : unitInterval × M) :
    f.transRadialContractionIsotopy c hn hκ p ∈ Euclidean.ball c r :=
  (euclideanDist_radialContraction_le c _ (mul_nonneg p.1.2.1 hκ)).trans_lt (hf p.2)

end SmoothEmbedding

end RadialContraction

end TauCeti
