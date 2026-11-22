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
import Mathlib.Analysis.Normed.Module.Span
import Mathlib.Analysis.SpecialFunctions.Exp
import TauCeti.Analysis.Normed.Module.Ball
import TauCeti.Analysis.Normed.Module.Ball.Radial.Equiv

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

In dimension zero the conjecture holds (`TauCeti.annulusConjecture_zero`). On a line every pair of
distinct points is a round sphere, so any two maps of the unit sphere `{±u}` of a
one-dimensional real normed space, the inner one injective, with nested images, cobound an annulus
(`TauCeti.coboundAnnulus_of_finrank_eq_one`): a pair of closed intervals. Local flatness enters only
through the injectivity of the inner sphere there.

## Main definitions

* `TauCeti.CoboundAnnulus`: two maps cobound an annulus.
* `TauCeti.AnnulusConjecture`: two nested locally flat `n`-spheres in `ℝⁿ⁺¹` cobound an annulus.

## Main results

* `TauCeti.isLocallyFlat_smul_coe_sphere`: a rescaled unit sphere is locally flat, with
  one-dimensional complementary model.
* `TauCeti.coboundAnnulus_of_range_eq_sphere`: two nested round spheres cobound an annulus.
* `TauCeti.coboundAnnulus_smul_coe_sphere`: two concentric round spheres cobound an annulus.
* `TauCeti.coboundAnnulus_of_finrank_eq_one`: on a line, two nested pairs of points cobound an
  annulus.
* `TauCeti.annulusConjecture_zero`: the annulus conjecture for `0`-spheres.

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
  rcases le_total t t' with htt | htt
  · have h₁ := mul_le_sub_of_le (r := r) (R := R) (c := c) (c' := c') p htt
    have h₂ := norm_sub_norm_le (p - (c' + t' • (c - c'))) (q - (c' + t' • (c - c')))
    rw [sub_sub_sub_cancel_right, hq] at h₂
    rw [abs_of_nonpos (sub_nonpos.2 htt)]
    linarith
  · have h₁ := mul_le_sub_of_le (r := r) (R := R) (c := c) (c' := c') q htt
    have h₂ := norm_sub_norm_le (q - (c' + t • (c - c'))) (p - (c' + t • (c - c')))
    rw [sub_sub_sub_cancel_right, hp, norm_sub_rev q p] at h₂
    rw [abs_of_nonneg (sub_nonneg.2 htt)]
    linarith

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
  have hrR : r ≤ R := by linarith [dist_nonneg (x := c) (y := c')]
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
  have hrR : r ≤ R := by linarith [dist_nonneg (x := c) (y := c')]
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
  have hrR : r ≤ R := by linarith [dist_nonneg (x := c) (y := c')]
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
          rw [norm_smul, norm_smul, norm_eq_of_mem_sphere q.1, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_mul, abs_of_nonneg (sub_nonneg.2 hrR), mul_one, hd, hD, dist_eq_norm_sub]
  rw [Real.coe_toNNReal _ (div_nonneg (by linarith [dist_nonneg (x := c) (y := c')]) hpos.le),
    Prod.dist_eq, Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq, dist_eq_norm_sub]
  have hD0 : 0 ≤ D := dist_nonneg
  have hd0 : 0 ≤ dist c c' := dist_nonneg
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
  have hR : 0 < R := by linarith [dist_nonneg (x := c) (y := c')]
  have hcont : Continuous (roundAnnulusMap c c' r R) := by
    unfold roundAnnulusMap
    fun_prop
  -- a translated rescaled unit sphere is a round sphere
  have hsph : ∀ (a : E) {ρ : ℝ}, 0 < ρ →
      range (fun u : sphere (0 : E) 1 => a + ρ • (u : E)) = sphere a ρ := fun a ρ hρ => by
    rw [range_comp' (a + ·) (fun u : sphere (0 : E) 1 => ρ • (u : E)), range_smul_coe_sphere hρ]
    simp
  refine ⟨roundAnnulusMap c c' r R,
    ⟨(antilipschitzWith_roundAnnulusMap hr hcR).isInducing hcont,
      injective_roundAnnulusMap hr hcR⟩, ?_, ?_, ?_⟩
  · rw [hf, hg, filledHull_sphere _ hR.le, filledHull_sphere _ hr.le]
    exact range_roundAnnulusMap hr hcR
  · rw [hf, ← hsph c' hR, ← image_univ]
    ext y
    simp [roundAnnulusMap]
  · rw [hg, ← hsph c hr, ← image_univ]
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
private theorem exists_range_eq_sphere (φ : ℝ ≃ₗᵢ[ℝ] E) (f : sphere (0 : E) 1 → E) :
    ∃ μ ρ : ℝ, 0 ≤ ρ ∧ (Function.Injective f → 0 < ρ) ∧ range f = sphere (φ μ) ρ := by
  have hu : φ 1 ∈ sphere (0 : E) 1 := by simp
  have hv : φ (-1) ∈ sphere (0 : E) 1 := by simp
  have hsph : ∀ x : sphere (0 : E) 1, x = ⟨φ 1, hu⟩ ∨ x = ⟨φ (-1), hv⟩ := by
    intro x
    have hx : |φ.symm x| = 1 := by
      rw [← Real.norm_eq_abs, φ.symm.norm_map, norm_eq_of_mem_sphere x]
    rcases (abs_eq zero_le_one).1 hx with h | h
    · exact .inl (Subtype.ext ((φ.apply_symm_apply _).symm.trans (congrArg φ h)))
    · exact .inr (Subtype.ext ((φ.apply_symm_apply _).symm.trans (congrArg φ h)))
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
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hspan : Submodule.span ℝ {‖v‖⁻¹ • v} = ⊤ :=
    (Submodule.span_singleton_eq_top_iff ℝ _).2 (exists_smul_eq_of_finrank_eq_one hE (by simp [hv]))
  let φ : ℝ ≃ₗᵢ[ℝ] E := (LinearIsometryEquiv.toSpanUnitSingleton (‖v‖⁻¹ • v)
    (by simp [norm_smul, hv])).trans (LinearIsometryEquiv.ofTop _ _ hspan)
  obtain ⟨μ, R, hR, -, hfR⟩ := exists_range_eq_sphere φ f
  obtain ⟨γ, r, -, hr, hgr⟩ := exists_range_eq_sphere φ g
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

end TauCeti
