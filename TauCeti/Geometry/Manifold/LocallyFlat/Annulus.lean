/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.UnitInterval
public import TauCeti.Analysis.Normed.Module.FilledHull
public import TauCeti.Geometry.Manifold.LocallyFlat.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.AlgebraicTopology.Sphere.Zero
import TauCeti.Analysis.Complex.Conformal.Jordan.Annulus
import TauCeti.Analysis.Normed.Module.Ball
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Analysis.Normed.Module.Ball.Radial.Equiv
import TauCeti.Topology.MetricSpace.ProperSpace

/-!
# The annulus conjecture

Two disjoint locally flat `n`-spheres in `ℝⁿ⁺¹`, one inside the region bounded by the other,
cobound a closed region homeomorphic to `Sⁿ × [0, 1]`. This is the **annulus conjecture**, now a
theorem in every dimension. The whole content is that the region between the spheres is a product;
it fails without local flatness, since a wild sphere such as the Alexander horned sphere need not
bound a ball on its wild side, let alone an annulus together with a round sphere.

The regions are read off with `TauCeti.filledHull`, the set together with the bounded components
of its complement. For an embedded sphere `f` in `ℝⁿ⁺¹` the complement has exactly one bounded
component by the Jordan–Brouwer separation theorem, so `filledHull (range f) \ range f` is the open
region the sphere bounds, and `filledHull (range f)` is its closure. The closed region between the
outer sphere `f` and an inner sphere `g` is then
`filledHull (range f) \ (filledHull (range g) \ range g)`: everything enclosed by `f`, minus what
lies strictly inside `g`. No separation theorem is assumed; the definitions make sense for arbitrary
subsets, and the separation is part of what the conjecture's conclusion asserts.

`TauCeti.CoboundAnnulus f g` says that this closed region is the image of an embedding of
`X × [0, 1]` restricting to `f` and `g` at the two ends, up to reparametrization: the end
`X × {0}` is carried onto the image of `f`, and the end `X × {1}` onto the image of `g`. The
conjecture itself, `TauCeti.AnnulusConjecture n`, is recorded as a dimension-indexed proposition in
the manner of `TauCeti.BrownBicollaring`, with the same indexing: `n` is the dimension of the
spheres, which sit in `EuclideanSpace ℝ (Fin (n + 1))`, and local flatness is read in the split
model `EuclideanSpace ℝ (Fin n) × ℝ`. Kirby's theorem is the case `n + 1 ≥ 5`, and Quinn's the case
`n + 1 = 4`.

The round case is proved here, which shows that the hypotheses of the conjecture can hold and that
its conclusion is attained: scaling the unit sphere by `c ≠ 0` is locally flat
(`TauCeti.isLocallyFlat_smul_coe_sphere`), and for `0 < r < R` the two concentric spheres cobound
the closed annulus `{r ≤ ‖x‖ ≤ R}` (`TauCeti.coboundAnnulus_smul_coe_sphere`). The required nesting
condition follows from `TauCeti.range_smul_coe_sphere_subset_filledHull_sdiff` in the
filled-hull API. Both round-sphere results hold in any real seminormed space.

The low-dimensional cases `n = 0` and `n = 1` (`ℝ¹` and `ℝ²`) are also proved here, without any
local flatness hypothesis, in any real normed space of dimension `1` or `2`:
in dimension `1`, two nested `0`-spheres `{a, b}` and `{c, d}` (`a < c < d < b`) cobound
`[a, c] ∪ [d, b] ≅ S⁰ × [0, 1]`; in dimension `2`, continuous injections `S¹ → ℂ` trace nested
Jordan curves, which cobound an annulus by the planar annulus theorem
(`TauCeti.IsJordanCurve.exists_homeomorph_sphere_prod_unitInterval`). Transport along
`ContinuousLinearEquiv.ofFinrankEq` and `TauCeti.sphereHomeomorphOfFinrankEq` yields
`TauCeti.annulusConjecture_zero`, `TauCeti.annulusConjecture_one`, and
`TauCeti.annulusConjecture_of_le_one`.

## Main definitions

* `TauCeti.CoboundAnnulus`: two maps cobound an annulus.
* `TauCeti.AnnulusConjecture`: two nested locally flat `n`-spheres in `ℝⁿ⁺¹` cobound an annulus.

## Main results

* `TauCeti.coboundAnnulus_iff`, `TauCeti.coboundAnnulus_congr`, `TauCeti.annulusConjecture_iff`:
  unfolding and congruence lemmas for `TauCeti.CoboundAnnulus` and `TauCeti.AnnulusConjecture`.
* `TauCeti.CoboundAnnulus.comp_homeomorph`, `TauCeti.coboundAnnulus_comp_homeomorph_iff`:
  cobounding an annulus is invariant under precomposition by a homeomorphism of the domain.
* `TauCeti.CoboundAnnulus.homeomorph_comp`, `TauCeti.coboundAnnulus_homeomorph_comp_iff`:
  cobounding an annulus is invariant under postcomposition by a boundedness-preserving
  homeomorphism of the ambient space.
* `TauCeti.isLocallyFlat_smul_coe_sphere`: a rescaled unit sphere is locally flat, with
  one-dimensional complementary model.
* `TauCeti.coboundAnnulus_smul_coe_sphere`: two concentric round spheres cobound an annulus.
* `TauCeti.coboundAnnulus_of_injective_of_finrank_eq_one`: any two nested injective maps
  `S⁰ → E` in a one-dimensional real normed space cobound an annulus.
* `TauCeti.coboundAnnulus_of_continuous_injective_of_finrank_eq_two`: any two nested continuous
  injections `S¹ → E` in a two-dimensional real normed space cobound an annulus.
* `TauCeti.annulusConjecture_zero`, `TauCeti.annulusConjecture_one`,
  `TauCeti.annulusConjecture_of_le_one`: the annulus conjecture holds for `n ≤ 1`.

## References

* R. C. Kirby, *Stable homeomorphisms and the annulus conjecture*, Annals of Mathematics 89
  (1969), 575–582.
* F. Quinn, *Ends of maps. III: Dimensions 4 and 5*, Journal of Differential Geometry 17 (1982),
  503–521.
* R. J. Daverman and G. A. Venema, *Embeddings in Manifolds*, Graduate Studies in Mathematics
  106, American Mathematical Society (2009).
-/

public section

noncomputable section

namespace TauCeti

open Bornology Metric Set Topology unitInterval

section CoboundAnnulus

variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E] [Bornology E]

/-- The maps `f g : X → E` **cobound an annulus** if the designated region between their images,
the filled hull of `range f` with the part strictly inside `range g` removed, is the image of an
embedding `X × [0, 1] → E` carrying the end `X × {0}` onto `range f` and the end `X × {1}` onto
`range g`. For spheres `f` and `g` this says that the region between them is homeomorphic to the
product of a sphere and an interval, with the two boundary spheres as its two ends. -/
def CoboundAnnulus (f g : X → E) : Prop :=
  ∃ h : X × I → E, IsEmbedding h ∧
    range h = filledHull (range f) \ (filledHull (range g) \ range g) ∧
    h '' (univ ×ˢ {0}) = range f ∧ h '' (univ ×ˢ {1}) = range g

/-- `TauCeti.CoboundAnnulus` spelled out: there is an embedding `X × [0, 1] → E` onto
`filledHull (range f) \ (filledHull (range g) \ range g)` carrying `X × {0}` onto `range f` and
`X × {1}` onto `range g`. Because the module system does not expose the body of
`TauCeti.CoboundAnnulus`, downstream modules introduce and eliminate it via this lemma. -/
theorem coboundAnnulus_iff {f g : X → E} :
    CoboundAnnulus f g ↔
      ∃ h : X × I → E, IsEmbedding h ∧
        range h = filledHull (range f) \ (filledHull (range g) \ range g) ∧
        h '' (univ ×ˢ {0}) = range f ∧ h '' (univ ×ˢ {1}) = range g :=
  Iff.rfl

/-- Cobounding an annulus depends on the two maps only through their ranges. -/
theorem coboundAnnulus_congr {f f' g g' : X → E} (hf : range f = range f')
    (hg : range g = range g') : CoboundAnnulus f g ↔ CoboundAnnulus f' g' := by
  simp only [coboundAnnulus_iff, hf, hg]

/-- Cobounding an annulus is preserved by precomposing both maps with a homeomorphism of the
domain. -/
theorem CoboundAnnulus.comp_homeomorph {Y : Type*} [TopologicalSpace Y] {f g : X → E}
    (h : CoboundAnnulus f g) (e : Y ≃ₜ X) : CoboundAnnulus (f ∘ e) (g ∘ e) := by
  obtain ⟨φ, hφ, hrange, h0, h1⟩ := h
  let ψ : Y × I ≃ₜ X × I := e.prodCongr (Homeomorph.refl I)
  have himg (t : I) : ψ '' (univ ×ˢ {t}) = univ ×ˢ {t} := by
    rw [Homeomorph.coe_prodCongr, Set.prodMap_image_prod, Set.image_univ, e.surjective.range_eq]
    simp
  refine ⟨φ ∘ ψ, hφ.comp ψ.isEmbedding, ?_, ?_, ?_⟩
  · rw [ψ.surjective.range_comp, e.surjective.range_comp, e.surjective.range_comp, hrange]
  · rw [image_comp, himg, h0, e.surjective.range_comp]
  · rw [image_comp, himg, h1, e.surjective.range_comp]

/-- Cobounding an annulus is invariant under precomposition by a homeomorphism of the domain. -/
theorem coboundAnnulus_comp_homeomorph_iff {Y : Type*} [TopologicalSpace Y] {f g : X → E}
    (e : Y ≃ₜ X) : CoboundAnnulus (f ∘ e) (g ∘ e) ↔ CoboundAnnulus f g := by
  refine ⟨fun h => ?_, fun h => h.comp_homeomorph e⟩
  simpa [Function.comp_assoc] using h.comp_homeomorph e.symm

/-- Cobounding an annulus is preserved by postcomposing both maps with a homeomorphism of the
ambient space that preserves boundedness. -/
theorem CoboundAnnulus.homeomorph_comp {F : Type*} [TopologicalSpace F] [Bornology F]
    {f g : X → E} (h : CoboundAnnulus f g) (e : E ≃ₜ F)
    (he : ∀ s : Set E, IsBounded (e '' s) ↔ IsBounded s) :
    CoboundAnnulus (e ∘ f) (e ∘ g) := by
  obtain ⟨φ, hφ, hrange, h0, h1⟩ := h
  refine ⟨e ∘ φ, e.isEmbedding.comp hφ, ?_, ?_, ?_⟩
  · rw [range_comp, hrange, Set.image_sdiff e.injective, Set.image_sdiff e.injective,
      e.image_filledHull he, e.image_filledHull he, range_comp, range_comp]
  · rw [image_comp, h0, range_comp]
  · rw [image_comp, h1, range_comp]

/-- Cobounding an annulus is invariant under postcomposition by a boundedness-preserving
homeomorphism of the ambient space. -/
theorem coboundAnnulus_homeomorph_comp_iff {F : Type*} [TopologicalSpace F] [Bornology F]
    {f g : X → E} (e : E ≃ₜ F) (he : ∀ s : Set E, IsBounded (e '' s) ↔ IsBounded s) :
    CoboundAnnulus (e ∘ f) (e ∘ g) ↔ CoboundAnnulus f g := by
  refine ⟨fun h => ?_, fun h => h.homeomorph_comp e he⟩
  have he' : ∀ s : Set F, IsBounded (e.symm '' s) ↔ IsBounded s := fun s => by
    simpa [image_image] using (he (e.symm '' s)).symm
  simpa [← Function.comp_assoc] using h.homeomorph_comp e.symm he'

end CoboundAnnulus

/-- **The annulus conjecture for `n`-spheres in `ℝⁿ⁺¹`:** if `f` and `g` are locally flat
embeddings of the standard `n`-sphere in `ℝⁿ⁺¹` and the image of `g` lies in the open region
bounded by the image of `f`, then `f` and `g` cobound an annulus.

Local flatness is read in the model `EuclideanSpace ℝ (Fin n) × ℝ`, so each sphere is locally a
codimension-one coordinate slice. The region bounded by `f` is `filledHull (range f) \ range f`,
which also forces the two images to be disjoint. -/
def AnnulusConjecture (n : ℕ) : Prop :=
  ∀ f g : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → EuclideanSpace ℝ (Fin (n + 1)),
    IsLocallyFlat (EuclideanSpace ℝ (Fin n)) ℝ f → IsLocallyFlat (EuclideanSpace ℝ (Fin n)) ℝ g →
      range g ⊆ filledHull (range f) \ range f → CoboundAnnulus f g

/-- `TauCeti.AnnulusConjecture` spelled out: every pair of nested locally flat `n`-spheres in
`ℝⁿ⁺¹` cobound an annulus. Because the module system does not expose the body of
`TauCeti.AnnulusConjecture`, downstream modules introduce and eliminate it via this lemma. -/
theorem annulusConjecture_iff {n : ℕ} :
    AnnulusConjecture n ↔
      ∀ f g : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → EuclideanSpace ℝ (Fin (n + 1)),
        IsLocallyFlat (EuclideanSpace ℝ (Fin n)) ℝ f →
          IsLocallyFlat (EuclideanSpace ℝ (Fin n)) ℝ g →
          range g ⊆ filledHull (range f) \ range f → CoboundAnnulus f g :=
  Iff.rfl

/-! ### Concentric round spheres -/

section Round

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A rescaled unit sphere in a real seminormed space is locally flat**, with one-dimensional
complementary model, for any charted-space structure on the sphere and every nonzero scale. -/
theorem isLocallyFlat_smul_coe_sphere {F : Type*} [TopologicalSpace F]
    [ChartedSpace F (sphere (0 : E) 1)] {c : ℝ} (hc : c ≠ 0) :
    IsLocallyFlat F ℝ (fun u : sphere (0 : E) 1 => c • (u : E)) := by
  have hopen := Real.isOpenEmbedding_exp.smul_coe_sphere (E := E) Real.exp_pos
  have hflat := (isLocallyFlat_prodMkLeft (F := F) (F' := ℝ)).isOpenEmbedding_comp hopen
    |>.homeomorph_comp (Homeomorph.smulOfNeZero c hc)
  convert hflat using 1
  ext u
  simp

/-- **Two concentric round spheres in a real seminormed space cobound an annulus:** for
`0 < r < R`, the spheres of radii `R` and `r` cobound the closed annulus `{x | r ≤ ‖x‖ ≤ R}`,
parametrized by
`(u, t) ↦ (R - (R - r) * t) • u`. -/
theorem coboundAnnulus_smul_coe_sphere {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    CoboundAnnulus (fun u : sphere (0 : E) 1 => R • (u : E)) (fun u => r • (u : E)) := by
  have hR : 0 < R := hr.trans hrR
  have hRr : 0 < R - r := sub_pos.mpr hrR
  -- the radius `R - (R - r) * t` at time `t`, as an embedding `[0, 1] → (0, ∞)`
  have hpos : ∀ t : I, R - (R - r) * t ∈ Ioi (0 : ℝ) := fun t => by
    have := mul_le_of_le_one_right hRr.le t.property.2
    rw [mem_Ioi]
    linarith
  let affine : ℝ ≃ₜ ℝ := (Homeomorph.mulLeft₀ (-(R - r)) (neg_ne_zero.mpr hRr.ne')).trans
    (Homeomorph.addLeft R)
  have hradius : IsEmbedding (codRestrict (fun t : I => R - (R - r) * t) (Ioi 0) hpos) := by
    have hline : IsEmbedding fun t : I => R - (R - r) * t := by
      convert affine.isEmbedding.comp IsEmbedding.subtypeVal using 1
      ext t
      simp [affine]
      ring
    exact hline.codRestrict _ hpos
  refine ⟨fun p => (R - (R - r) * p.2) • (p.1 : E), ?_, ?_, ?_, ?_⟩
  · have hemb := IsEmbedding.subtypeVal.comp
      ((homeomorphUnitSphereProdOfNormPos E).symm.isEmbedding.comp
        (IsEmbedding.id.prodMap hradius))
    convert hemb using 1
    funext p
    simp
  · rw [range_smul_coe_sphere hR, range_smul_coe_sphere hr, filledHull_sphere _ hR.le,
      filledHull_sphere _ hr.le]
    ext x
    simp only [mem_range, Prod.exists, mem_sdiff, mem_closedBall, dist_zero_right, mem_sphere,
      not_and, not_not]
    constructor
    · rintro ⟨u, t, rfl⟩
      rw [norm_smul, norm_eq_of_mem_sphere u, mul_one, Real.norm_of_nonneg (hpos t).out.le]
      have h₀ := t.property.1
      have h₁ := mul_le_of_le_one_right hRr.le t.property.2
      refine ⟨by nlinarith, fun h => ?_⟩
      nlinarith
    · rintro ⟨hxR, hxr⟩
      have hrx : r ≤ ‖x‖ := not_lt.mp fun h => h.ne (hxr h.le)
      have hx : 0 < ‖x‖ := hr.trans_le hrx
      refine ⟨⟨‖x‖⁻¹ • x, ?_⟩, ⟨(R - ‖x‖) / (R - r), ?_, ?_⟩, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hx.ne']
      · exact div_nonneg (by linarith) hRr.le
      · exact (div_le_one hRr).mpr (by linarith)
      · simp only
        rw [mul_div_cancel₀ _ hRr.ne', sub_sub_cancel, smul_inv_smul₀ hx.ne']
  · ext x
    simp
  · ext x
    simp

end Round

/-! ### Low dimensions (`n ≤ 1`) -/

section LowDim

open Function

private theorem coboundAnnulus_of_injective_real {f g : sphere (0 : ℝ) 1 → ℝ}
    (hf : Injective f) (hg : Injective g) (hsub : range g ⊆ filledHull (range f) \ range f) :
    CoboundAnnulus f g := by
  let um : sphere (0 : ℝ) 1 := ⟨-1, by simp⟩
  let up : sphere (0 : ℝ) 1 := ⟨1, by simp⟩
  have hu_eq (u : sphere (0 : ℝ) 1) : u = um ∨ u = up := by
    simpa [Subtype.ext_iff, um, up] using (Real.sphere_eq_pair 0 zero_le_one).subset u.property
  have hu_ne : um ≠ up := by intro h; have := congrArg Subtype.val h; norm_num [um, up] at this
  have huniv : (univ : Set (sphere (0 : ℝ) 1)) = {um, up} := by
    ext u
    simpa [mem_insert_iff, mem_singleton_iff] using hu_eq u
  have hrange_pair (k : sphere (0 : ℝ) 1 → ℝ) :
      range k = {min (k um) (k up), max (k um) (k up)} := by
    rw [← image_univ, huniv, image_pair]
    rcases le_total (k um) (k up) with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h, pair_comm]
  set a : ℝ := min (f um) (f up)
  set b : ℝ := max (f um) (f up)
  set c : ℝ := min (g um) (g up)
  set d : ℝ := max (g um) (g up)
  have hab : a < b := min_lt_max.mpr (hf.ne hu_ne)
  have hcd : c < d := min_lt_max.mpr (hg.ne hu_ne)
  have hrf : range f = {a, b} := hrange_pair f
  have hrg : range g = {c, d} := hrange_pair g
  have hfhf : filledHull (range f) = Icc a b := by
    rw [hrf, filledHull_pair, uIcc_of_le hab.le]
  have hfhg : filledHull (range g) = Icc c d := by
    rw [hrg, filledHull_pair, uIcc_of_le hcd.le]
  have hf_open : filledHull (range f) \ range f = Ioo a b := by
    rw [hfhf, hrf, Icc_sdiff_both]
  have hg_open : filledHull (range g) \ range g = Ioo c d := by
    rw [hfhg, hrg, Icc_sdiff_both]
  have hac : a < c := (hf_open ▸ hsub (hrg ▸ mem_insert c {d})).1
  have hdb : d < b := (hf_open ▸ hsub (hrg ▸ mem_insert_of_mem c (mem_singleton d))).2
  -- Parametrize `[a, c]` on `{um} × I` and `[d, b]` on `{up} × I` via `Path.segment`.
  let h : sphere (0 : ℝ) 1 × I → ℝ := fun p =>
    if (p.1 : ℝ) ≤ 0 then Path.segment a c p.2 else Path.segment b d p.2
  have hh_neg (t : I) : h (um, t) = Path.segment a c t := by simp [h, um]
  have hh_pos (t : I) : h (up, t) = Path.segment b d t := by simp [h, up]
  have := discreteTopology_sphere_of_finrank_eq_one (Module.finrank_self ℝ) (0 : ℝ) 1
  have hh_cont : Continuous h := by
    rw [continuous_prod_of_discrete_left]
    intro u
    rcases hu_eq u with rfl | rfl
    · simpa only [hh_neg] using (Path.segment a c).continuous
    · simpa only [hh_pos] using (Path.segment b d).continuous
  have hrange_ac : range (Path.segment a c) = Icc a c := by
    rw [Path.range_segment, segment_eq_uIcc, uIcc_of_le hac.le]
  have hrange_bd : range (Path.segment b d) = Icc d b := by
    rw [Path.range_segment, segment_eq_uIcc, uIcc_comm, uIcc_of_le hdb.le]
  have hdisj : Disjoint (range (Path.segment a c)) (range (Path.segment b d)) := by
    rw [hrange_ac, hrange_bd]
    exact Set.disjoint_left.mpr fun _ h1 h2 => by linarith [h1.2, h2.1]
  have hh_inj : Injective h := by
    rintro ⟨u₁, t₁⟩ ⟨u₂, t₂⟩ heq
    rcases hu_eq u₁ with rfl | rfl <;> rcases hu_eq u₂ with rfl | rfl
    · rw [hh_neg, hh_neg] at heq
      exact Prod.ext rfl (Path.segment_injective_of_ne hac.ne heq)
    · rw [hh_neg, hh_pos] at heq
      exact (hdisj.ne_of_mem (mem_range_self t₁) (mem_range_self t₂) heq).elim
    · rw [hh_pos, hh_neg] at heq
      exact (hdisj.ne_of_mem (mem_range_self t₂) (mem_range_self t₁) heq.symm).elim
    · rw [hh_pos, hh_pos] at heq
      exact Prod.ext rfl (Path.segment_injective_of_ne hdb.ne' heq)
  have : CompactSpace (sphere (0 : ℝ) 1) := isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  refine ⟨h, (hh_cont.isClosedEmbedding hh_inj).isEmbedding, ?_, ?_, ?_⟩
  · have hrange_h : range h = range (Path.segment a c) ∪ range (Path.segment b d) := by
      refine Subset.antisymm ?_ ?_
      · rintro _ ⟨⟨u, t⟩, rfl⟩
        rcases hu_eq u with rfl | rfl
        · exact Or.inl ⟨t, (hh_neg t).symm⟩
        · exact Or.inr ⟨t, (hh_pos t).symm⟩
      · rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩)
        · exact ⟨(um, t), hh_neg t⟩
        · exact ⟨(up, t), hh_pos t⟩
    rw [hrange_h, hrange_ac, hrange_bd, hfhf, hg_open]
    ext x
    simp only [mem_union, mem_Icc, mem_sdiff, mem_Ioo, not_and, not_lt]
    constructor
    · rintro (⟨hax, hxc⟩ | ⟨hdx, hxb⟩)
      · exact ⟨⟨hax, hxc.trans (hcd.le.trans hdb.le)⟩, fun hc => absurd hc (not_lt.mpr hxc)⟩
      · exact ⟨⟨hac.le.trans (hcd.le.trans hdx), hxb⟩, fun _ => hdx⟩
    · rintro ⟨⟨hax, hxb⟩, hnot⟩
      by_cases hxc : x ≤ c
      · exact Or.inl ⟨hax, hxc⟩
      · exact Or.inr ⟨hnot (not_le.mp hxc), hxb⟩
  · rw [Set.prod_singleton, ← Set.image_comp, Set.image_univ, ← image_univ, huniv, image_pair]
    simp [hh_neg, hh_pos, hrf]
  · rw [Set.prod_singleton, ← Set.image_comp, Set.image_univ, ← image_univ, huniv, image_pair]
    simp [hh_neg, hh_pos, hrg]

/-- **The one-dimensional annulus theorem in any one-dimensional real normed space.** Any two
injective maps `f g : sphere (0 : E) 1 → E` with `range g ⊆ filledHull (range f) \ range f`
cobound an annulus. No continuity or local flatness hypothesis is needed. -/
theorem coboundAnnulus_of_injective_of_finrank_eq_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hE : Module.finrank ℝ E = 1) {f g : sphere (0 : E) 1 → E}
    (hf : Injective f) (hg : Injective g) (hsub : range g ⊆ filledHull (range f) \ range f) :
    CoboundAnnulus f g := by
  have : FiniteDimensional ℝ E := .of_finrank_pos (by omega)
  have hEF : Module.finrank ℝ E = Module.finrank ℝ ℝ := by simp [hE]
  let e : E ≃ₜ ℝ := (ContinuousLinearEquiv.ofFinrankEq hEF).toHomeomorph
  let es : sphere (0 : E) 1 ≃ₜ sphere (0 : ℝ) 1 := sphereHomeomorphOfFinrankEq hEF
  have he : ∀ s : Set E, IsBounded (e '' s) ↔ IsBounded s := fun _ => e.isBounded_image_iff
  rw [← coboundAnnulus_homeomorph_comp_iff e he, ← coboundAnnulus_comp_homeomorph_iff es.symm]
  exact coboundAnnulus_of_injective_real
    (e.injective.comp (hf.comp es.symm.injective))
    (e.injective.comp (hg.comp es.symm.injective))
    (by simpa only [range_comp, es.symm.surjective.range_comp] using
      (e.image_subset_filledHull_sdiff_iff he (range g) (range f)).mpr hsub)

/-- **The annulus conjecture holds in dimension `1` (`n = 0`).** -/
theorem annulusConjecture_zero : AnnulusConjecture 0 := fun _ _ hf hg hsub =>
  coboundAnnulus_of_injective_of_finrank_eq_one (by simp) hf.injective hg.injective hsub

private theorem coboundAnnulus_of_continuous_injective_complex {f g : sphere (0 : ℂ) 1 → ℂ}
    (hfc : Continuous f) (hfi : Injective f) (hgc : Continuous g) (hgi : Injective g)
    (hsub : range g ⊆ filledHull (range f) \ range f) :
    CoboundAnnulus f g := by
  have hC₁ : IsJordanCurve (range f) :=
    isJordanCurve_range (sphereCircleHomeomorph 0 one_pos) hfc hfi
  have hC₂ : IsJordanCurve (range g) :=
    isJordanCurve_range (sphereCircleHomeomorph 0 one_pos) hgc hgi
  obtain ⟨Φ, hΦ0, hΦ1⟩ := hC₁.exists_homeomorph_sphere_prod_unitInterval hC₂ hsub
  refine ⟨Subtype.val ∘ Φ, IsEmbedding.subtypeVal.comp Φ.isEmbedding, ?_, hΦ0, hΦ1⟩
  rw [Φ.surjective.range_comp, Subtype.range_coe]

/-- **The two-dimensional annulus theorem in any two-dimensional real normed space.** Any two
continuous injections `f g : sphere (0 : E) 1 → E` with
`range g ⊆ filledHull (range f) \ range f` cobound an annulus. No local flatness hypothesis is
needed. -/
theorem coboundAnnulus_of_continuous_injective_of_finrank_eq_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hE : Module.finrank ℝ E = 2) {f g : sphere (0 : E) 1 → E}
    (hfc : Continuous f) (hfi : Injective f) (hgc : Continuous g) (hgi : Injective g)
    (hsub : range g ⊆ filledHull (range f) \ range f) :
    CoboundAnnulus f g := by
  have : FiniteDimensional ℝ E := .of_finrank_pos (by omega)
  have hEF : Module.finrank ℝ E = Module.finrank ℝ ℂ := by simp [hE]
  let e : E ≃ₜ ℂ := (ContinuousLinearEquiv.ofFinrankEq hEF).toHomeomorph
  let es : sphere (0 : E) 1 ≃ₜ sphere (0 : ℂ) 1 := sphereHomeomorphOfFinrankEq hEF
  have he : ∀ s : Set E, IsBounded (e '' s) ↔ IsBounded s := fun _ => e.isBounded_image_iff
  rw [← coboundAnnulus_homeomorph_comp_iff e he, ← coboundAnnulus_comp_homeomorph_iff es.symm]
  exact coboundAnnulus_of_continuous_injective_complex
    (e.continuous.comp (hfc.comp es.symm.continuous))
    (e.injective.comp (hfi.comp es.symm.injective))
    (e.continuous.comp (hgc.comp es.symm.continuous))
    (e.injective.comp (hgi.comp es.symm.injective))
    (by simpa only [range_comp, es.symm.surjective.range_comp] using
      (e.image_subset_filledHull_sdiff_iff he (range g) (range f)).mpr hsub)

/-- **The annulus conjecture holds in dimension `2` (`n = 1`).** -/
theorem annulusConjecture_one : AnnulusConjecture 1 := fun _ _ hf hg hsub =>
  coboundAnnulus_of_continuous_injective_of_finrank_eq_two (by simp)
    hf.continuous hf.injective hg.continuous hg.injective hsub

/-- **The annulus conjecture holds in dimensions `1` and `2` (`n ≤ 1`).** -/
theorem annulusConjecture_of_le_one {n : ℕ} (hn : n ≤ 1) : AnnulusConjecture n := by
  match n with
  | 0 => exact annulusConjecture_zero
  | 1 => exact annulusConjecture_one

end LowDim

end TauCeti
