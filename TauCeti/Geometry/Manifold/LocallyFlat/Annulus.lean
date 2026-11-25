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
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Complex.Conformal.Jordan.Annulus
import TauCeti.Analysis.Normed.Module.Ball
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Analysis.Normed.Module.Ball.Radial.Equiv
import TauCeti.Analysis.Normed.Module.FiniteDimension
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
(`TauCeti.isLocallyFlat_smul_coe_sphere`), and two round spheres, the closed ball of the inner one
lying in the open ball of the outer one, cobound the region between them
(`TauCeti.coboundAnnulus_of_range_eq_sphere`). The annulus is swept out by the segments from
`c' + R • u` to `c + r • u`, `u` a unit vector, which lie on the intermediate spheres of centre
`c' + t • (c - c')` and radius `R - t * (R - r)`; these are strictly nested, which makes the sweep
an embedding with Lipschitz inverse. For concentric spheres the annulus is `{r ≤ ‖x‖ ≤ R}`
(`TauCeti.coboundAnnulus_smul_coe_sphere`), and the nesting condition follows from
`TauCeti.range_smul_coe_sphere_subset_filledHull_sdiff` in the filled-hull API. These round-sphere
results hold in any real seminormed space: the seminorm need not separate points.

The low-dimensional cases `n = 0` and `n = 1` (`ℝ¹` and `ℝ²`) are also proved here, without any
local flatness hypothesis, in any real normed space of dimension `1` or `2`:
in dimension `1`, every pair of distinct points is a round sphere, so any two maps of the unit
sphere `{±u}` with the inner one injective and nested images cobound an annulus
(`TauCeti.coboundAnnulus_of_finrank_eq_one`), a pair of closed intervals; in dimension `2`,
continuous injections `S¹ → ℂ` trace nested Jordan curves, which cobound an annulus by the planar
annulus theorem (`TauCeti.IsJordanCurve.exists_homeomorph_sphere_prod_unitInterval`), and transport
along `ContinuousLinearEquiv.ofFinrankEq` and `TauCeti.sphereHomeomorphOfFinrankEq` yields
`TauCeti.coboundAnnulus_of_continuous_injective_of_finrank_eq_two`, `TauCeti.annulusConjecture_one`,
and `TauCeti.annulusConjecture_of_le_one`.

## Main definitions

* `TauCeti.CoboundAnnulus`: two maps cobound an annulus.
* `TauCeti.AnnulusConjecture`: two nested locally flat `n`-spheres in `ℝⁿ⁺¹` cobound an annulus.

## Main results

* `TauCeti.coboundAnnulus_iff`, `TauCeti.coboundAnnulus_iff_exists_homeomorph`,
  `TauCeti.coboundAnnulus_congr`, `TauCeti.annulusConjecture_iff`:
  unfolding, homeomorphism characterization, and congruence lemmas for `TauCeti.CoboundAnnulus` and
  `TauCeti.AnnulusConjecture`.
* `TauCeti.CoboundAnnulus.comp_homeomorph`, `TauCeti.coboundAnnulus_comp_homeomorph_iff`:
  cobounding an annulus is invariant under precomposition by a homeomorphism of the domain.
* `TauCeti.CoboundAnnulus.homeomorph_comp`, `TauCeti.coboundAnnulus_homeomorph_comp_iff`:
  cobounding an annulus is invariant under postcomposition by a boundedness-preserving
  homeomorphism of the ambient space.
* `TauCeti.isLocallyFlat_smul_coe_sphere`: a rescaled unit sphere is locally flat, with
  one-dimensional complementary model.
* `TauCeti.coboundAnnulus_of_range_eq_sphere`: two nested round spheres cobound an annulus.
* `TauCeti.coboundAnnulus_smul_coe_sphere`: two concentric round spheres cobound an annulus.
* `TauCeti.coboundAnnulus_of_finrank_eq_one`: on a line, two nested pairs of points cobound an
  annulus.
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

/-- `TauCeti.CoboundAnnulus` in terms of a homeomorphism from `X × [0, 1]` onto the annular region
`filledHull (range f) \ (filledHull (range g) \ range g)` carrying `X × {0}` onto `range f` and
`X × {1}` onto `range g`. -/
theorem coboundAnnulus_iff_exists_homeomorph {f g : X → E} :
    CoboundAnnulus f g ↔
      ∃ Φ : X × I ≃ₜ ↥(filledHull (range f) \ (filledHull (range g) \ range g)),
        (fun p => (Φ p : E)) '' (univ ×ˢ {0}) = range f ∧
        (fun p => (Φ p : E)) '' (univ ×ˢ {1}) = range g := by
  rw [coboundAnnulus_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨h, hemb, hrange, h0, h1⟩
    exact ⟨hemb.toHomeomorph.trans (Homeomorph.setCongr hrange), h0, h1⟩
  · rintro ⟨Φ, h0, h1⟩
    refine ⟨Subtype.val ∘ Φ, IsEmbedding.subtypeVal.comp Φ.isEmbedding, ?_, h0, h1⟩
    rw [Φ.surjective.range_comp, Subtype.range_coe]

/-- Cobounding an annulus depends on the two maps only through their ranges. -/
theorem coboundAnnulus_congr {f f' g g' : X → E} (hf : range f = range f')
    (hg : range g = range g') : CoboundAnnulus f g ↔ CoboundAnnulus f' g' := by
  simp only [coboundAnnulus_iff, hf, hg]

/-- Cobounding an annulus is preserved by precomposing both maps with a homeomorphism of the
domain. -/
theorem CoboundAnnulus.comp_homeomorph {Y : Type*} [TopologicalSpace Y] {f g : X → E}
    (h : CoboundAnnulus f g) (e : Y ≃ₜ X) : CoboundAnnulus (f ∘ e) (g ∘ e) := by
  rw [coboundAnnulus_iff] at h ⊢
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
  rw [coboundAnnulus_iff] at h ⊢
  obtain ⟨φ, hφ, hrange, h0, h1⟩ := h
  refine ⟨e ∘ φ, e.isEmbedding.comp hφ, ?_, ?_, ?_⟩
  · rw [range_comp, hrange, Set.image_sdiff e.injective, e.image_filledHull he,
      e.image_filledHull_sdiff he, range_comp, range_comp]
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

/-! ### Round spheres -/

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

variable {c c' : E} {r R : ℝ}

/-- The straight-line interpolation from the sphere of radius `R` about `c'` to the sphere of
radius `r` about `c`: at time `t` the point `u` of the unit sphere goes to the point in direction
`u` on the sphere of radius `R - t * (R - r)` about `c' + t • (c - c')`. -/
private def roundAnnulusMap (c c' : E) (r R : ℝ) (p : sphere (0 : E) 1 × I) : E :=
  c' + (p.2 : ℝ) • (c - c') + (R - p.2 * (R - r)) • (p.1 : E)

/-- Along the moving spheres, the signed distance `‖y - (c' + t • (c - c'))‖ - (R - t * (R - r))`
of a fixed point `y` from the sphere at time `t` grows at rate at least
`R - r - dist c c'`. -/
private theorem mul_le_sub_of_le (y : E) {s t : ℝ} (hts : t ≤ s) :
    (s - t) * (R - r - dist c c') ≤
      (‖y - (c' + s • (c - c'))‖ - (R - s * (R - r))) -
        (‖y - (c' + t • (c - c'))‖ - (R - t * (R - r))) := by
  have h : ‖y - (c' + t • (c - c'))‖ ≤ ‖y - (c' + s • (c - c'))‖ + (s - t) * dist c c' := by
    calc ‖y - (c' + t • (c - c'))‖ = ‖(y - (c' + s • (c - c'))) + (s - t) • (c - c')‖ := by
          congr 1; module
      _ ≤ ‖y - (c' + s • (c - c'))‖ + ‖(s - t) • (c - c')‖ := norm_add_le _ _
      _ = ‖y - (c' + s • (c - c'))‖ + (s - t) * dist c c' := by
          rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.2 hts), dist_eq_norm_sub]
  nlinarith

/-- Two points lying on the moving spheres at times `t` and `t'` are at least
`(R - r - dist c c') * |t - t'|` apart. -/
private theorem mul_abs_sub_le_norm_sub {p q : E} {t t' : ℝ}
    (hp : ‖p - (c' + t • (c - c'))‖ = R - t * (R - r))
    (hq : ‖q - (c' + t' • (c - c'))‖ = R - t' * (R - r)) :
    (R - r - dist c c') * |t - t'| ≤ ‖p - q‖ := by
  wlog htt : t ≤ t' generalizing p q t t'
  · rw [abs_sub_comm, norm_sub_rev]
    exact this hq hp (le_of_not_ge htt)
  have h₁ := mul_le_sub_of_le (r := r) (R := R) (c := c) (c' := c') p htt
  have h₂ := norm_sub_norm_le (p - (c' + t' • (c - c'))) (q - (c' + t' • (c - c')))
  rw [sub_sub_sub_cancel_right, hq] at h₂
  rw [abs_of_nonpos (sub_nonpos.2 htt)]
  linarith

omit [NormedSpace ℝ E] in
/-- The inner radius is less than the outer one. -/
private theorem lt_of_dist_add_lt (hcR : dist c c' + r < R) : r < R := by
  linarith [dist_nonneg (x := c) (y := c')]

/-- The radius of the moving sphere stays at least `r`. -/
private theorem le_radius (hrR : r ≤ R) (t : I) : r ≤ R - t * (R - r) := by
  nlinarith [t.property.2, sub_nonneg.2 hrR]

/-- The image of `(u, t)` lies on the moving sphere at time `t`. -/
private theorem norm_roundAnnulusMap_sub (hr : 0 < r) (hrR : r ≤ R) (p : sphere (0 : E) 1 × I) :
    ‖roundAnnulusMap c c' r R p - (c' + (p.2 : ℝ) • (c - c'))‖ = R - p.2 * (R - r) := by
  rw [roundAnnulusMap, add_sub_cancel_left, norm_smul, norm_eq_of_mem_sphere p.1, mul_one,
    Real.norm_of_nonneg (hr.le.trans (le_radius hrR p.2))]

/-- The interpolation sweeps out exactly the closed region between the two spheres. -/
private theorem range_roundAnnulusMap (hr : 0 < r) (hcR : dist c c' + r < R) :
    range (roundAnnulusMap c c' r R) = closedBall c' R \ (closedBall c r \ sphere c r) := by
  have hrR : r ≤ R := (lt_of_dist_add_lt hcR).le
  have hκ : 0 ≤ R - r - dist c c' := by linarith
  ext y
  simp only [mem_sdiff, mem_closedBall, mem_sphere, dist_eq_norm_sub, not_and, not_not]
  constructor
  · rintro ⟨p, rfl⟩
    have hp := norm_roundAnnulusMap_sub (c := c) (c' := c') hr hrR p
    have h₀ := mul_le_sub_of_le (r := r) (R := R) (c := c) (c' := c')
      (roundAnnulusMap c c' r R p) p.2.property.1
    have h₁ := mul_le_sub_of_le (r := r) (R := R) (c := c) (c' := c')
      (roundAnnulusMap c c' r R p) p.2.property.2
    simp only [zero_smul, add_zero, zero_mul, sub_zero, one_smul, add_sub_cancel, one_mul,
      sub_sub_cancel] at h₀ h₁
    refine ⟨by nlinarith [p.2.property.1, hκ], fun _ => le_antisymm ‹_› ?_⟩
    nlinarith [p.2.property.2, hκ]
  · rintro ⟨hyR, hyr⟩
    have hry : r ≤ ‖y - c‖ := not_lt.1 fun h => h.ne (hyr h.le)
    -- the signed distance from the moving sphere changes sign on `[0, 1]`
    let δ : ℝ → ℝ := fun t => ‖y - (c' + t • (c - c'))‖ - (R - t * (R - r))
    have hδ : ContinuousOn δ (Icc 0 1) := by fun_prop
    have hδ₀ : δ 0 ≤ 0 := by simp only [δ, zero_smul, add_zero, zero_mul, sub_zero]; linarith
    have hδ₁ : 0 ≤ δ 1 := by
      simp only [δ, one_smul, add_sub_cancel, one_mul, sub_sub_cancel]; linarith
    obtain ⟨t, ht, hδt⟩ := intermediate_value_Icc zero_le_one hδ ⟨hδ₀, hδ₁⟩
    have hρ : 0 < R - t * (R - r) := hr.trans_le (le_radius hrR ⟨t, ht⟩)
    have hnorm : ‖y - (c' + t • (c - c'))‖ = R - t * (R - r) := by simpa [δ, sub_eq_zero] using hδt
    refine ⟨(⟨(R - t * (R - r))⁻¹ • (y - (c' + t • (c - c'))), ?_⟩, ⟨t, ht⟩), ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Real.norm_of_nonneg hρ.le, hnorm,
        inv_mul_cancel₀ hρ.ne']
    · rw [roundAnnulusMap, smul_inv_smul₀ hρ.ne']
      simp only
      abel

/-- The interpolation is injective. -/
private theorem injective_roundAnnulusMap (hr : 0 < r) (hcR : dist c c' + r < R) :
    Function.Injective (roundAnnulusMap c c' r R) := by
  have hrR : r ≤ R := (lt_of_dist_add_lt hcR).le
  rintro p q hpq
  have h := mul_abs_sub_le_norm_sub (norm_roundAnnulusMap_sub (c := c) (c' := c') hr hrR p)
    (norm_roundAnnulusMap_sub hr hrR q)
  rw [hpq, sub_self, norm_zero] at h
  have ht : (p.2 : ℝ) = q.2 := by
    rw [← sub_eq_zero, ← abs_eq_zero]
    exact le_antisymm (nonpos_of_mul_nonpos_right h (by linarith)) (abs_nonneg _)
  have hρ : R - (p.2 : ℝ) * (R - r) ≠ 0 := (hr.trans_le (le_radius hrR p.2)).ne'
  have hx : (p.1 : E) = q.1 := by
    refine smul_right_injective E hρ ?_
    simpa [roundAnnulusMap, ht] using hpq
  exact Prod.ext (Subtype.ext hx) (Subtype.ext ht)

/-- The interpolation is antilipschitz: its inverse on its range is Lipschitz. -/
private theorem antilipschitzWith_roundAnnulusMap (hr : 0 < r) (hcR : dist c c' + r < R) :
    AntilipschitzWith ((R - r + dist c c' + R) / ((R - r - dist c c') * r)).toNNReal
      (roundAnnulusMap c c' r R) := by
  have hrR : r ≤ R := (lt_of_dist_add_lt hcR).le
  have hκ : 0 < R - r - dist c c' := by linarith
  have hd : dist c c' = ‖c - c'‖ := dist_eq_norm_sub c c'
  have hpos : 0 < (R - r - dist c c') * r := mul_pos hκ hr
  refine AntilipschitzWith.of_le_mul_dist fun p q => ?_
  set D := dist (roundAnnulusMap c c' r R p) (roundAnnulusMap c c' r R q) with hD
  set Δ : ℝ := (p.2 : ℝ) - q.2
  have hρ := le_radius hrR p.2
  -- the times are close
  have ht : (R - r - dist c c') * |Δ| ≤ D :=
    (mul_abs_sub_le_norm_sub (norm_roundAnnulusMap_sub (c := c) (c' := c') hr hrR p)
      (norm_roundAnnulusMap_sub hr hrR q)).trans_eq (dist_eq_norm_sub _ _).symm
  -- and then so are the directions
  have hx : (R - p.2 * (R - r)) * ‖(p.1 : E) - q.1‖ ≤
      D + |Δ| * dist c c' + |Δ| * (R - r) := by
    calc (R - p.2 * (R - r)) * ‖(p.1 : E) - q.1‖ = ‖(R - p.2 * (R - r)) • ((p.1 : E) - q.1)‖ := by
          rw [norm_smul, Real.norm_of_nonneg (hr.le.trans hρ)]
      _ = ‖(roundAnnulusMap c c' r R p - roundAnnulusMap c c' r R q) - Δ • (c - c') +
            (Δ * (R - r)) • (q.1 : E)‖ := by
          congr 1
          simp only [roundAnnulusMap, Δ]
          module
      _ ≤ ‖roundAnnulusMap c c' r R p - roundAnnulusMap c c' r R q‖ + ‖Δ • (c - c')‖ +
            ‖(Δ * (R - r)) • (q.1 : E)‖ := norm_add_le_of_le (norm_sub_le _ _) le_rfl
      _ = D + |Δ| * dist c c' + |Δ| * (R - r) := by
          simp [norm_smul, abs_of_nonneg (sub_nonneg.2 hrR), hd, hD, dist_eq_norm_sub]
  have hD0 : 0 ≤ D := dist_nonneg
  have hd0 : 0 ≤ dist c c' := dist_nonneg
  rw [Real.coe_toNNReal _ (div_nonneg (by linarith) hpos.le)]
  simp only [Prod.dist_eq, Subtype.dist_eq, Real.dist_eq, dist_eq_norm_sub (p.1 : E)]
  have h₁ : (R - r - dist c c') * (r * ‖(p.1 : E) - q.1‖) ≤
      (R - r - dist c c') * (D + |Δ| * dist c c' + |Δ| * (R - r)) :=
    mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right hρ (norm_nonneg _)).trans hx) hκ.le
  have h₂ : (dist c c' + (R - r)) * ((R - r - dist c c') * |Δ|) ≤ (dist c c' + (R - r)) * D :=
    mul_le_mul_of_nonneg_left ht (by linarith)
  have h₃ : r * ((R - r - dist c c') * |Δ|) ≤ r * D := mul_le_mul_of_nonneg_left ht hr.le
  refine max_le ?_ ?_ <;> rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  · nlinarith [mul_nonneg hr.le hD0, mul_nonneg hd0 hD0]
  · nlinarith [mul_nonneg (sub_nonneg.2 hrR) hD0, mul_nonneg hd0 hD0]

/-- **Two nested round spheres in a real seminormed space cobound an annulus**, whether or not
they are concentric: if `f` parametrizes the sphere of radius `R` about `c'`, `g` the sphere of
radius `r > 0` about `c`, and the closed ball of radius `r` about `c` lies in the open ball of
radius `R` about `c'` (`dist c c' + r < R`), then `f` and `g` cobound an annulus. The annulus is
swept out by the segments from `c' + R • u` to `c + r • u`, `u` a unit vector. -/
theorem coboundAnnulus_of_range_eq_sphere {f g : sphere (0 : E) 1 → E}
    (hf : range f = sphere c' R) (hg : range g = sphere c r) (hr : 0 < r)
    (hcR : dist c c' + r < R) : CoboundAnnulus f g := by
  have hR : 0 < R := hr.trans (lt_of_dist_add_lt hcR)
  have hcont : Continuous (roundAnnulusMap c c' r R) := by
    unfold roundAnnulusMap
    fun_prop
  refine ⟨roundAnnulusMap c c' r R,
    ⟨(antilipschitzWith_roundAnnulusMap hr hcR).isInducing hcont,
      injective_roundAnnulusMap hr hcR⟩, ?_, ?_, ?_⟩
  · rw [hf, hg, filledHull_sphere _ hR.le, filledHull_sphere _ hr.le]
    exact range_roundAnnulusMap hr hcR
  · rw [hf, ← range_add_smul_coe_sphere c' hR, ← image_univ]
    ext y
    simp [roundAnnulusMap]
  · rw [hg, ← range_add_smul_coe_sphere c hr, ← image_univ]
    ext y
    simp [roundAnnulusMap, add_sub_cancel]

/-- **Two concentric round spheres in a real seminormed space cobound an annulus:** for
`0 < r < R`, the spheres of radii `R` and `r` cobound the closed annulus `{x | r ≤ ‖x‖ ≤ R}`,
parametrized by
`(u, t) ↦ (R - (R - r) * t) • u`. -/
theorem coboundAnnulus_smul_coe_sphere {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    CoboundAnnulus (fun u : sphere (0 : E) 1 => R • (u : E)) (fun u => r • (u : E)) :=
  coboundAnnulus_of_range_eq_sphere (c := 0) (c' := 0) (range_smul_coe_sphere (hr.trans hrR))
    (range_smul_coe_sphere hr) hr (by simpa using hrR)

end Round

/-! ### Spheres of dimension zero -/

section DimensionZero

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- In a line, identified with `ℝ` by `φ`, the image of any map of the unit sphere `{±φ 1}` is a
round sphere, of positive radius when the map is injective. -/
private theorem exists_range_eq_sphere (hE : Module.finrank ℝ E = 1) (φ : ℝ ≃ₗᵢ[ℝ] E)
    (f : sphere (0 : E) 1 → E) :
    ∃ μ ρ : ℝ, 0 ≤ ρ ∧ (Function.Injective f → 0 < ρ) ∧ range f = sphere (φ μ) ρ := by
  have hu : φ 1 ∈ sphere (0 : E) 1 := by simp
  have hv : φ (-1) ∈ sphere (0 : E) 1 := by simp
  have hsph : ∀ x : sphere (0 : E) 1, x = ⟨φ 1, hu⟩ ∨ x = ⟨φ (-1), hv⟩ := fun x => by
    simpa [Subtype.ext_iff] using
      eq_or_eq_neg_of_norm_eq_of_finrank_eq_one hE (x := (x : E)) (y := φ 1) (by simp)
  set α := φ.symm (f ⟨φ 1, hu⟩)
  set β := φ.symm (f ⟨φ (-1), hv⟩)
  refine ⟨(α + β) / 2, |α - β| / 2, by positivity, fun hf => ?_, ?_⟩
  · have hαβ : α ≠ β := fun h => by
      have := hf (φ.symm.injective h)
      simp only [Subtype.mk.injEq, φ.injective.eq_iff] at this
      norm_num at this
    exact half_pos (abs_pos.2 (sub_ne_zero.2 hαβ))
  ext y
  obtain ⟨s, rfl⟩ := φ.surjective y
  have hα : f ⟨φ 1, hu⟩ = φ α := (φ.apply_symm_apply _).symm
  have hβ : f ⟨φ (-1), hv⟩ = φ β := (φ.apply_symm_apply _).symm
  have hmem : φ s ∈ range f ↔ s = α ∨ s = β := by
    constructor
    · rintro ⟨x, hx⟩
      rcases hsph x with rfl | rfl
      · exact .inl (φ.injective (hx.symm.trans hα))
      · exact .inr (φ.injective (hx.symm.trans hβ))
    · rintro (rfl | rfl)
      · exact ⟨_, hα⟩
      · exact ⟨_, hβ⟩
  rw [hmem, mem_sphere, φ.dist_map, Real.dist_eq,
    show |α - β| / 2 = |(α - β) / 2| by rw [abs_div, abs_two], abs_eq_abs]
  constructor
  · rintro (rfl | rfl)
    · exact .inl (by ring)
    · exact .inr (by ring)
  · rintro (h | h)
    · exact .inl (by linarith)
    · exact .inr (by linarith)

/-- **The annulus theorem on a line:** in a one-dimensional real normed space, two maps `f` and `g`
of the unit sphere `{±u}`, with `g` injective and the image of `g` in the open region bounded by the
image of `f`, cobound an annulus. The two pairs of points are the endpoints of nested intervals,
and the annulus is the pair of closed intervals between them. Injectivity of `f` is not assumed: a
map with a single value bounds no region. -/
theorem coboundAnnulus_of_finrank_eq_one (hE : Module.finrank ℝ E = 1) {f g : sphere (0 : E) 1 → E}
    (hg : Function.Injective g) (hfg : range g ⊆ filledHull (range f) \ range f) :
    CoboundAnnulus f g := by
  -- identify the line with `ℝ` isometrically
  obtain ⟨φ⟩ := nonempty_linearIsometryEquiv_of_finrank_eq_one hE
  obtain ⟨μ, R, hR, -, hfR⟩ := exists_range_eq_sphere hE φ f
  obtain ⟨γ, r, -, hr, hgr⟩ := exists_range_eq_sphere hE φ g
  have hr := hr hg
  refine coboundAnnulus_of_range_eq_sphere hfR hgr hr ?_
  rw [hfR, hgr, filledHull_sphere _ hR] at hfg
  -- both points of the inner sphere lie strictly inside the outer one
  have hlt : ∀ s, |s - γ| = r → |s - μ| < R := fun s hs => by
    have hs' : φ s ∈ sphere (φ γ) r := by rwa [mem_sphere, φ.dist_map, Real.dist_eq]
    obtain ⟨h₁, h₂⟩ := hfg hs'
    rw [mem_closedBall, φ.dist_map, Real.dist_eq] at h₁
    rw [mem_sphere, φ.dist_map, Real.dist_eq] at h₂
    exact lt_of_le_of_ne h₁ h₂
  have h₁ := hlt (γ + r) (by rw [add_sub_cancel_left, abs_of_pos hr])
  have h₂ := hlt (γ - r) (by rw [sub_sub_cancel_left, abs_neg, abs_of_pos hr])
  rw [φ.dist_map, Real.dist_eq]
  rw [abs_lt] at h₁ h₂
  rcases le_total γ μ with h | h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

/-- **The annulus theorem for `0`-spheres:** two nested pairs of points on the real line cobound
an annulus, a pair of closed intervals. Local flatness enters only through the injectivity of the
inner pair. -/
theorem annulusConjecture_zero : AnnulusConjecture 0 := fun _ _ _ hg hfg =>
  coboundAnnulus_of_finrank_eq_one (finrank_euclideanSpace_fin (𝕜 := ℝ)) hg.injective hfg

end DimensionZero

/-! ### Spheres of dimension one -/

section DimensionOne

open Function

private theorem coboundAnnulus_of_continuous_injective_complex {f g : sphere (0 : ℂ) 1 → ℂ}
    (hfc : Continuous f) (hfi : Injective f) (hgc : Continuous g) (hgi : Injective g)
    (hsub : range g ⊆ filledHull (range f) \ range f) :
    CoboundAnnulus f g := by
  have hC₁ : IsJordanCurve (range f) :=
    isJordanCurve_range (sphereCircleHomeomorph 0 one_pos) hfc hfi
  have hC₂ : IsJordanCurve (range g) :=
    isJordanCurve_range (sphereCircleHomeomorph 0 one_pos) hgc hgi
  rw [coboundAnnulus_iff_exists_homeomorph]
  exact hC₁.exists_homeomorph_sphere_prod_unitInterval hC₂ hsub

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
theorem annulusConjecture_one : AnnulusConjecture 1 := by
  rw [annulusConjecture_iff]
  exact fun _ _ hf hg hsub =>
    coboundAnnulus_of_continuous_injective_of_finrank_eq_two (by simp)
      hf.continuous hf.injective hg.continuous hg.injective hsub

/-- **The annulus conjecture holds in dimensions `1` and `2` (`n ≤ 1`).** -/
theorem annulusConjecture_of_le_one {n : ℕ} (hn : n ≤ 1) : AnnulusConjecture n := by
  match n with
  | 0 => exact annulusConjecture_zero
  | 1 => exact annulusConjecture_one

end DimensionOne

end TauCeti
