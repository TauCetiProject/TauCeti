/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.UnitInterval
public import TauCeti.Analysis.Normed.Module.Ball
public import TauCeti.Analysis.Normed.Module.FilledHull
public import TauCeti.Geometry.Manifold.LocallyFlat.Basic
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Order.MonotoneContinuity

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
(`TauCeti.isLocallyFlat_smul_coe_sphere`), for `0 < r < R` the sphere of radius `r` lies inside the
sphere of radius `R` (`TauCeti.range_smul_coe_sphere_subset_filledHull_sdiff`), and the two
concentric spheres cobound the closed annulus `{r ≤ ‖x‖ ≤ R}`
(`TauCeti.coboundAnnulus_smul_coe_sphere`).

## Main definitions

* `TauCeti.CoboundAnnulus`: two maps cobound an annulus.
* `TauCeti.AnnulusConjecture`: two nested locally flat `n`-spheres in `ℝⁿ⁺¹` cobound an annulus.

## Main results

* `TauCeti.isLocallyFlat_smul_coe_sphere`: a rescaled unit sphere is locally flat, with
  one-dimensional complementary model.
* `TauCeti.range_smul_coe_sphere_subset_filledHull_sdiff`: a smaller concentric sphere lies inside
  a larger one.
* `TauCeti.coboundAnnulus_smul_coe_sphere`: two concentric round spheres cobound an annulus.

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

/-! ### Concentric round spheres -/

section Round

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A rescaled unit sphere is locally flat**, with one-dimensional complementary model, for any
charted-space structure on the sphere and every nonzero scale. -/
theorem isLocallyFlat_smul_coe_sphere {F : Type*} [TopologicalSpace F]
    [ChartedSpace F (sphere (0 : E) 1)] {c : ℝ} (hc : c ≠ 0) :
    IsLocallyFlat F ℝ (fun u : sphere (0 : E) 1 => c • (u : E)) := by
  let polar : sphere (0 : E) 1 × ℝ ≃ₜ ({0}ᶜ : Set E) :=
    ((Homeomorph.refl _).prodCongr Real.expOrderIso.toHomeomorph).trans
      (homeomorphUnitSphereProd E).symm
  have hopen : IsOpenEmbedding (Subtype.val ∘ polar) :=
    isOpen_compl_singleton.isOpenEmbedding_subtypeVal.comp polar.isOpenEmbedding
  have hflat := (isLocallyFlat_prodMkLeft (F := F) (F' := ℝ)).isOpenEmbedding_comp hopen
    |>.homeomorph_comp (Homeomorph.smulOfNeZero c hc)
  convert hflat using 1
  ext u
  simp [polar]

/-- **A smaller concentric sphere lies inside a larger one:** for `0 < r < R`, the sphere of
radius `r` lies in the open region bounded by the sphere of radius `R`. -/
theorem range_smul_coe_sphere_subset_filledHull_sdiff {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    range (fun u : sphere (0 : E) 1 => r • (u : E)) ⊆
      filledHull (range fun u : sphere (0 : E) 1 => R • (u : E)) \
        range fun u : sphere (0 : E) 1 => R • (u : E) := by
  rw [range_smul_coe_sphere hr, range_smul_coe_sphere (hr.trans hrR),
    filledHull_sphere _ (hr.trans hrR).le]
  intro x hx
  rw [mem_sphere_zero_iff_norm] at hx
  simp [hx, hrR]

/-- **Two concentric round spheres cobound an annulus:** for `0 < r < R`, the spheres of radii `R`
and `r` cobound the closed annulus `{x | r ≤ ‖x‖ ≤ R}`, parametrized by
`(u, t) ↦ (R - (R - r) * t) • u`. -/
theorem coboundAnnulus_smul_coe_sphere {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    CoboundAnnulus (fun u : sphere (0 : E) 1 => R • (u : E)) (fun u => r • (u : E)) := by
  have hR : 0 < R := hr.trans hrR
  have hRr : 0 < R - r := sub_pos.mpr hrR
  -- the radius `R - (R - r) * t` at time `t`, as an embedding `[0, 1] → (0, ∞)`
  have hpos : ∀ t : I, R - (R - r) * t ∈ Ioi (0 : ℝ) := fun t => by
    have := mul_le_of_le_one_right hRr.le t.2.2
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
      ((homeomorphUnitSphereProd E).symm.isEmbedding.comp (IsEmbedding.id.prodMap hradius))
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
      have h₀ := t.2.1
      have h₁ := mul_le_of_le_one_right hRr.le t.2.2
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

end TauCeti
