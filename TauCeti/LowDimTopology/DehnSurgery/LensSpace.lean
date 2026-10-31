/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.DehnSurgery.Filling
public import TauCeti.LowDimTopology.Heegaard.LensSpace.Splitting
public import TauCeti.LowDimTopology.SolidTorusNeighborhood.Unknot

/-!
# Lens spaces as surgeries on the unknot

For coprime integers `p > 0` and `q`, the `p / q`-surgery on the unknot in `S³` is a lens space
(Rolfsen, *Knots and Links*, Chapter 9): the exterior of the unknot is a solid torus, and gluing a
second solid torus to it so that the meridian of the second goes to the `(p, q)` curve gives the
union of two solid tori glued along their boundary tori by an element of `SL₂(ℤ)`. This file
realizes that filling inside the lens space `L(p; ℓ₀, ℓ₁)` with `ℓ₁ = -q ℓ₀` modulo `p`, as a
`TauCeti.DehnFilling` of the exterior of the unknot along the slope of value `p / q` for the
framing of the standard solid torus neighbourhood `TauCeti.unknotSolidTorus`, which is the
preferred framing (`TauCeti.preferredFramedBoundaryTorus_unknotSolidTorus`). For `ℓ = ![1, q]`,
the lens space `L(p, q)` is thus the `-p / q`-surgery on the unknot. Rolfsen's Section 9G,
Example 1 uses the opposite sign: `p / q` gives `L(p, q)`. The orientation convention accounts
for this difference; as unoriented spaces, `L(p, q)` and `L(p, -q)` are homeomorphic.

The two solid tori are the pieces `‖x 0‖ ≤ ‖x 1‖` and `‖x 1‖ ≤ ‖x 0‖` of the genus-one Heegaard
splitting of the lens space (`TauCeti.LensSpace.heegaardSplitting`). A point `(u, w)` of
`D² × S¹` gives the unit vector of `ℂ²` with coordinates proportional to `u w ^ e` and `w` (in the
two coordinates of the piece), and the rotations of the lens space act on these points through
`w ↦ ζ w`, `ζ ^ p = 1`, as soon as `e ℓⱼ = ℓᵢ` modulo `p`. So the image in the lens space depends
only on `(u, w ^ p)`, and this defines an embedding of the solid torus onto the piece. With
`s p + t q = 1`, the filling solid torus is the piece `‖x 0‖ ≤ ‖x 1‖` with `e = -t`, and the knot
exterior, through `TauCeti.unknotExteriorHomeomorph`, is the piece `‖x 1‖ ≤ ‖x 0‖` with `e = -q`.
On the common boundary torus these coordinates differ by the gluing
`(a, b) ↦ (a ^ p b ^ (-t), a ^ q b ^ s)`, of determinant `s p + t q = 1`, which carries the
meridian `(a, 1)` of the filling solid torus to the `(p, q)` curve of the boundary torus of the
exterior.

## Main definitions

* `TauCeti.unknotLensSpaceDehnFilling`: the lens space `L(p; ℓ₀, ℓ₁)`, with `ℓ₁ = -q ℓ₀`, as the
  Dehn filling of the exterior of the unknot along the slope `p / q`.

## Main results

* `TauCeti.unknotLensSpaceDehnFilling_gluing_apply`: the gluing of the boundary tori.
* `TauCeti.unknotLensSpaceDehnFilling_solidTorusEmbedding_apply`,
  `TauCeti.unknotLensSpaceDehnFilling_exteriorEmbedding_apply`: values of the embeddings on the
  power-map cover of the solid torus.
* `TauCeti.range_unknotLensSpaceDehnFilling_solidTorusEmbedding`,
  `TauCeti.range_unknotLensSpaceDehnFilling_exteriorEmbedding`: the filling solid torus and the
  knot exterior are the two handlebodies of the genus-one Heegaard splitting of the lens space.

## References

* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Chapter 9, Sections 9B and 9G
  (lens spaces as unions of two solid tori, and as surgeries on the unknot).
-/

public section

noncomputable section

open Metric Set Topology Function

namespace TauCeti

/-! ### `p / q`-surgery on the unknot -/

section Surgery

variable (p : ℕ) [NeZero p] (ℓ : Fin 2 → (ZMod p)ˣ) {q s t : ℤ}

omit [NeZero p] in
/-- The exponent `-t` for the filling solid torus `‖x 0‖ ≤ ‖x 1‖`: since `t q ≡ 1` modulo `p`,
`-t ℓ₁ = t q ℓ₀ = ℓ₀`. -/
private theorem exponent_left (hst : s * p + t * q = 1) (hℓ : (ℓ 1 : ZMod p) = -q * ℓ 0) :
    ((-t : ℤ) : ZMod p) * ℓ 1 = ℓ 0 := by
  have h := congrArg (Int.cast : ℤ → ZMod p) hst
  push_cast [ZMod.natCast_self] at h
  rw [hℓ]
  push_cast
  linear_combination (ℓ 0 : ZMod p) * h

omit [NeZero p] in
/-- The exponent `-q` for the knot exterior `‖x 1‖ ≤ ‖x 0‖`. -/
private theorem exponent_right (hℓ : (ℓ 1 : ZMod p) = -q * ℓ 0) :
    ((-q : ℤ) : ZMod p) * ℓ 0 = ℓ 1 := by
  rw [hℓ]
  push_cast
  ring

/-- The two handlebody parametrizations agree on their boundary through the surgery gluing. -/
private theorem lensSpace_boundary_gluing (hst : s * p + t * q = 1)
    (hℓ : (ℓ 1 : ZMod p) = -q * ℓ 0) (r : Circle × Circle) :
    LensSpace.rightEmbedding (exponent_right p ℓ hℓ)
        (SolidTorus.boundaryInclusion (torusGluing p q s t hst r).swap) =
      LensSpace.leftEmbedding (exponent_left p ℓ hst hℓ) (SolidTorus.boundaryInclusion r) := by
  obtain ⟨w, hw⟩ : ∃ w : Circle, w ^ p = r.2 :=
    (Circle.isQuotientCoveringMap_npow p).surjective r.2
  -- In the coordinates `(u, w)` of the two pieces over `(u, w ^ p)`, the point `(r.1, w)` of
  -- the filling solid torus is the point `(r.1 ^ q r.2 ^ s, r.1 w ^ (-t))` of the exterior.
  have hpow : (r.1 * w ^ (-t)) ^ p = r.1 ^ (p : ℤ) * r.2 ^ (-t) := by
    simp only [← hw, ← zpow_natCast, mul_zpow, ← zpow_mul, mul_comm (-t)]
  have hB : SolidTorus.boundaryInclusion (torusGluing p q s t hst r).swap =
      ((SolidTorus.boundaryInclusion (r.1 ^ q * r.2 ^ s, r.1 * w ^ (-t))).1,
        (r.1 * w ^ (-t)) ^ p) := by
    refine Prod.ext (Subtype.ext (by simp [torusGluing_apply])) ?_
    simp only [SolidTorus.boundaryInclusion_snd, Prod.snd_swap,
      torusGluing_apply]
    exact hpow.symm
  have hA : SolidTorus.boundaryInclusion r =
      ((SolidTorus.boundaryInclusion (r.1, w)).1, w ^ p) := by
    refine Prod.ext (Subtype.ext (by simp)) ?_
    simp only [SolidTorus.boundaryInclusion_snd, hw]
  -- `r.1 ^ q (w ^ p) ^ s (r.1 w ^ (-t)) ^ (-q) = w ^ (s p + t q) = w`.
  have hc : r.1 ^ q * r.2 ^ s * (r.1 * w ^ (-t)) ^ (-q) = w := by
    have hexp : (p : ℤ) * s + (-t) * (-q) = 1 := by linear_combination hst
    calc
      _ = r.1 ^ q * w ^ ((p : ℤ) * s) * (r.1 ^ (-q) * w ^ ((-t) * (-q))) := by
        simp only [← hw, ← zpow_natCast, mul_zpow, ← zpow_mul]
      _ = r.1 ^ (q + -q) * w ^ ((p : ℤ) * s + (-t) * (-q)) := by
        rw [mul_mul_mul_comm, zpow_add, zpow_add]
      _ = w := by simp only [add_neg_cancel, hexp, zpow_zero, zpow_one, one_mul]
  rw [hB, hA, LensSpace.rightEmbedding_apply, LensSpace.leftEmbedding_apply]
  refine congrArg _ (Subtype.ext ?_)
  ext k
  fin_cases k
  · simp [LensSpace.coe_rightCover_apply_zero, LensSpace.coe_leftCover_apply_zero]
  · simp only [Fin.mk_one, LensSpace.coe_rightCover_apply_one,
      LensSpace.coe_leftCover_apply_one, SolidTorus.coe_boundaryInclusion_fst,
      Circle.norm_coe]
    rw [← Circle.coe_mul, hc]

/-- **`p / q`-surgery on the unknot is a lens space.** For `s p + t q = 1` and `ℓ₁ = -q ℓ₀` modulo
`p`, the lens space `L(p; ℓ₀, ℓ₁)` is the Dehn filling of the exterior of the unknot along the slope
of value `p / q` in the framing of `TauCeti.unknotSolidTorus`, which is the preferred framing
(`TauCeti.preferredFramedBoundaryTorus_unknotSolidTorus`). The filling solid torus is the
handlebody `‖x 0‖ ≤ ‖x 1‖` of the genus-one Heegaard splitting of the lens space, the exterior is
the handlebody `‖x 1‖ ≤ ‖x 0‖`, and the boundary tori are glued by
`(a, b) ↦ (a ^ p b ^ (-t), a ^ q b ^ s)`. For `ℓ = ![1, q]` this exhibits `L(p, q)` as the
`-p / q`-surgery on the unknot. -/
def unknotLensSpaceDehnFilling (hst : s * p + t * q = 1) (hℓ : (ℓ 1 : ZMod p) = -q * ℓ 0) :
    DehnFilling isSolidTorusNeighborhood_unknotSolidTorus
      (isSolidTorusNeighborhood_unknotSolidTorus.framedBoundaryTorus.slopeEquiv.symm
        (slopeValue (p, q)))
      (LensSpace p ℓ) where
  exteriorEmbedding :=
    LensSpace.rightEmbedding (exponent_right p ℓ hℓ) ∘
      unknotExteriorHomeomorph
  isClosedEmbedding_exteriorEmbedding :=
    (LensSpace.isClosedEmbedding_rightEmbedding _).comp
      unknotExteriorHomeomorph.isClosedEmbedding
  solidTorusEmbedding :=
    LensSpace.leftEmbedding (exponent_left p ℓ hst hℓ)
  isClosedEmbedding_solidTorusEmbedding :=
    LensSpace.isClosedEmbedding_leftEmbedding _
  gluing := torusGluing p q s t hst
  exteriorEmbedding_exteriorBoundaryInclusion r := by
    rw [Function.comp_apply, unknotExteriorHomeomorph_exteriorBoundaryInclusion]
    exact lensSpace_boundary_gluing p ℓ hst hℓ r
  range_union_range := by
    rw [EquivLike.range_comp, LensSpace.range_rightEmbedding, LensSpace.range_leftEmbedding,
      ← LensSpace.heegaardSplitting_left, ← LensSpace.heegaardSplitting_right, union_comm,
      (LensSpace.heegaardSplitting p ℓ).union_eq_univ]
  range_inter_range_subset := by
    intro y hy
    obtain ⟨⟨x, hx⟩, z, hz⟩ := hy
    have hn := LensSpace.norm_eq_one_of_leftEmbedding_eq_rightEmbedding (exponent_left p ℓ hst hℓ)
      (exponent_right p ℓ hℓ) (hz.trans hx.symm)
    refine ⟨(⟨z.1, mem_sphere_zero_iff_norm.2 hn⟩, z.2), ?_⟩
    rw [← hz, Function.comp_apply]
    exact congrArg _ (Prod.ext (Subtype.ext (SolidTorus.coe_boundaryInclusion_fst _))
      (SolidTorus.boundaryInclusion_snd _))
  fillingSlope_gluing := by
    have hpq : IsCoprime (p : ℤ) q := ⟨s, t, hst⟩
    rw [Equiv.eq_symm_apply, FramedBoundaryTorus.slopeEquiv_apply,
      IsSolidTorusNeighborhood.fillingSlope_eq_of_apply_torusCurve _ hpq
        (torusGluing_torusCurve p q s t hst),
      FramedBoundaryTorus.value_mk_torusCurveClass _ hpq]

variable {p ℓ}

/-- The `p / q`-surgery on the unknot glues the boundary tori by
`(a, b) ↦ (a ^ p b ^ (-t), a ^ q b ^ s)`. -/
@[simp]
theorem unknotLensSpaceDehnFilling_gluing_apply (hst : s * p + t * q = 1)
    (hℓ : (ℓ 1 : ZMod p) = -q * ℓ 0) (x : Circle × Circle) :
    (unknotLensSpaceDehnFilling p ℓ hst hℓ).gluing x =
      (x.1 ^ (p : ℤ) * x.2 ^ (-t), x.1 ^ q * x.2 ^ s) :=
  torusGluing_apply _ _ _ _ _ x

/-- The filling embedding evaluated on the power-map cover of the solid torus. The left cover
is the unit vector proportional to `(x.1 * x.2 ^ (-t), x.2)`. -/
@[simp]
theorem unknotLensSpaceDehnFilling_solidTorusEmbedding_apply (hst : s * p + t * q = 1)
    (hℓ : (ℓ 1 : ZMod p) = -q * ℓ 0) (x : SolidTorus) :
    (unknotLensSpaceDehnFilling p ℓ hst hℓ).solidTorusEmbedding (x.1, x.2 ^ p) =
      LensSpace.mk p ℓ (LensSpace.leftCover (-t) x) :=
  LensSpace.leftEmbedding_apply _ x.1 x.2

/-- The exterior embedding evaluated through the unknot exterior coordinates. The right cover
is the unit vector proportional to `(x.2, x.1 * x.2 ^ (-q))`. -/
@[simp]
theorem unknotLensSpaceDehnFilling_exteriorEmbedding_apply (hst : s * p + t * q = 1)
    (hℓ : (ℓ 1 : ZMod p) = -q * ℓ 0) (x : SolidTorus) :
    (unknotLensSpaceDehnFilling p ℓ hst hℓ).exteriorEmbedding
        (unknotExteriorHomeomorph.symm (x.1, x.2 ^ p)) =
      LensSpace.mk p ℓ (LensSpace.rightCover (-q) x) := by
  simp only [unknotLensSpaceDehnFilling, Function.comp_apply, Homeomorph.apply_symm_apply]
  exact LensSpace.rightEmbedding_apply _ x.1 x.2

/-- The filling solid torus of the `p / q`-surgery on the unknot is the handlebody
`‖x 0‖ ≤ ‖x 1‖` of the genus-one Heegaard splitting of the lens space. -/
@[simp]
theorem range_unknotLensSpaceDehnFilling_solidTorusEmbedding (hst : s * p + t * q = 1)
    (hℓ : (ℓ 1 : ZMod p) = -q * ℓ 0) :
    range (unknotLensSpaceDehnFilling p ℓ hst hℓ).solidTorusEmbedding =
      (LensSpace.heegaardSplitting p ℓ).left := by
  exact (LensSpace.range_leftEmbedding _).trans (LensSpace.heegaardSplitting_left p ℓ).symm

/-- The exterior of the unknot in the `p / q`-surgery is the handlebody `‖x 1‖ ≤ ‖x 0‖` of the
genus-one Heegaard splitting of the lens space. -/
@[simp]
theorem range_unknotLensSpaceDehnFilling_exteriorEmbedding (hst : s * p + t * q = 1)
    (hℓ : (ℓ 1 : ZMod p) = -q * ℓ 0) :
    range (unknotLensSpaceDehnFilling p ℓ hst hℓ).exteriorEmbedding =
      (LensSpace.heegaardSplitting p ℓ).right := by
  exact (EquivLike.range_comp _ unknotExteriorHomeomorph).trans
    ((LensSpace.range_rightEmbedding _).trans (LensSpace.heegaardSplitting_right p ℓ).symm)

end Surgery

end TauCeti
