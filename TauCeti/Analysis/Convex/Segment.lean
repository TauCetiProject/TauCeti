/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.Ray
public import Mathlib.Order.Interval.Set.ProjIcc

/-!
# Affine segments and membership criteria

Mathlib describes membership in a segment through the ray predicate `SameRay` by
`mem_segment_iff_sameRay`: `x ∈ [y -[𝕜] z] ↔ SameRay 𝕜 (x - y) (z - x)`. That form is symmetric in
the two endpoints, and the differences `x - y`, `z - x` are exactly what a *metric* consumer does
not want: such a consumer holds a point `m` and an endpoint `w`, and asks whether `m` lies on the
segment `[0, w]` in terms of the two data it can measure — the direction of `m` against `w`, and
the two norms. This file supplies that reading, together with its mirror in which the origin sits
in the *middle* of the segment rather than at an end, and the inner-product form of both.

Each criterion is stated at the generality its proof uses. The origin-at-an-end one compares two
norms, and is stated for a real normed space; the inner-product forms replace `SameRay` by the
equality case of the Cauchy--Schwarz inequality, and are stated for a real inner product space.

The bridge between the ray form and the inner-product forms is Mathlib's pair
`sameRay_iff_norm_smul_eq : SameRay ℝ x y ↔ ‖x‖ • y = ‖y‖ • x` and
`inner_eq_norm_mul_iff_real : ⟪x, y⟫_ℝ = ‖x‖ * ‖y‖ ↔ ‖y‖ • x = ‖x‖ • y`, used directly: together
they say that two vectors lie on a common ray exactly when Cauchy--Schwarz is an equality for them.
No strict convexity is involved: the alternative route through `sameRay_iff_norm_add` would need a
`StrictConvexSpace ℝ E` instance, whereas `sameRay_iff_norm_smul_eq` and
`inner_eq_norm_mul_iff_real` hold in any normed, respectively inner product, space.

The clamped affine segment `Set.convexSegment` joins two points of any convex set, with no
topology or norm required. It agrees with the affine line map on `[0, 1]` and is constant outside
that interval. Its smoothness in convex open subsets is developed in
`TauCeti/Geometry/Manifold/ContMDiff/Subtype.lean`, and its Riemannian length in
`TauCeti/Geometry/Manifold/Riemannian/Convex.lean`.

The affine half-open segment result is also recorded here: in an additive commutative group with a
module structure over a linear ordered field, it identifies the image of a scalar interval under
an affine parametrization with a segment whose terminal endpoint is removed.

## Main results

* `Set.convexSegment` — an affine segment in a convex set, clamped to `[0, 1]`.
* `TauCeti.mem_segment_zero_left_iff_sameRay_and_norm_le` —
  `m ∈ [0 -[ℝ] w] ↔ SameRay ℝ m w ∧ ‖m‖ ≤ ‖w‖`. Both conjuncts are needed.
* `TauCeti.eq_of_mem_segment_zero_left_of_norm_eq` — the norm separates the points of `[0, w]`.
* `TauCeti.mem_segment_zero_left_iff_real_inner_eq_norm_mul_and_norm_le` and
  `TauCeti.zero_mem_segment_iff_real_inner_eq_neg_norm_mul` — the two criteria in a real inner
  product space.
* `TauCeti.image_add_smul_Ico` — the affine image of `Ico 0 D` is a segment with its terminal
  endpoint removed.
* `TauCeti.mem_segment_lineMap_of_one_le` — a point `x` lies on the segment from `a` to any point
  `lineMap a x T` with `1 ≤ T`, at or beyond `x` on the ray from `a` through `x`.
* `TauCeti.exists_lineMap_endpoint` — the overlap of `[0, 1]` with its image under an affine map
  `lineMap a b` of `𝕜`, when nondegenerate, has two ends each given by a point `u ∈ [0, 1]` with
  `u` or `lineMap a b u` an end of `[0, 1]`.

The overlap of `[0, 1]` with an affine image of itself, in a linear ordered field, is a closed
interval whose ends come from ends of the two copies of `[0, 1]`. This is what an argument
comparing two segments through their parameters needs.

The origin-at-an-end and origin-in-the-middle criteria are consumed by
`TauCeti/Analysis/Complex/Conformal/Poincare/Betweenness.lean`, which identifies the hyperbolic
segments of the Poincaré disc issuing from, or straddling, the origin with the Euclidean ones; `ℂ`
is a real inner product space with `⟪w, z⟫_ℝ = (z * conj w).re`
(`Complex.inner`), so the two inner-product criteria translate the ray and norm conditions into
complex-number formulas.
The affine half-open segment result is consumed by
`TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/UnboundedEdge.lean`.
The overlap result is consumed by `TauCeti/Geometry/Polygon/DoublePoint.lean`, which shows that
two distinct edges of a simple polygon contain at most one pair of points with the same image
under an affine regular projection.
-/

public section

namespace Set

section ClampedSegment

variable {𝕜 E : Type*} [Ring 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] (s : Set E)

/-- The affine segment between two points of a convex set, parametrized on `[0, 1]` and
extended constantly outside that interval. No topology is needed for this construction. -/
def convexSegment (hs : Convex 𝕜 s) (x y : s) : 𝕜 → s :=
  IccExtend zero_le_one fun t ↦
    ⟨AffineMap.lineMap (k := 𝕜) (x : E) (y : E) t,
      hs.lineMap_mem x.property y.property t.property⟩

/-- The ambient value of the clamped segment is the affine line map at the clamped parameter. -/
@[simp]
theorem coe_convexSegment_apply (hs : Convex 𝕜 s) (x y : s) (t : 𝕜) :
    (convexSegment s hs x y t : E) =
      AffineMap.lineMap (k := 𝕜) (x : E) (y : E) (projIcc 0 1 zero_le_one t) := (rfl)

/-- On `[0, 1]`, the clamped segment agrees with the ambient affine line map. -/
theorem convexSegment_val_eqOn (hs : Convex 𝕜 s) (x y : s) :
    EqOn (Subtype.val ∘ convexSegment s hs x y)
      (AffineMap.lineMap (k := 𝕜) (x : E) (y : E)) (Icc 0 1) := by
  intro t ht
  simp [projIcc_of_mem zero_le_one ht]

/-- The clamped segment starts at its first endpoint. -/
@[simp]
theorem convexSegment_zero (hs : Convex 𝕜 s) (x y : s) :
    convexSegment s hs x y 0 = x := by
  apply Subtype.ext
  simp

/-- The clamped segment ends at its second endpoint. -/
@[simp]
theorem convexSegment_one (hs : Convex 𝕜 s) (x y : s) :
    convexSegment s hs x y 1 = y := by
  apply Subtype.ext
  simp

end ClampedSegment

end Set

namespace TauCeti

open RealInnerProductSpace Set
open scoped Convex

/-! ### Segments and rays -/

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m w : E}

/-- **Membership in the segment from the origin, read off the direction and the two norms.** A
point `m` lies on `[0, w]` exactly when it points along `w` and is no further from the origin than
`w` is.

Both conjuncts are needed: for `w ≠ 0` the point `(2 : ℝ) • w` satisfies the first without
satisfying the second. -/
theorem mem_segment_zero_left_iff_sameRay_and_norm_le :
    m ∈ [(0 : E) -[ℝ] w] ↔ SameRay ℝ m w ∧ ‖m‖ ≤ ‖w‖ := by
  rw [segment_eq_image' ℝ (0 : E) w]
  simp only [mem_image, mem_Icc, zero_add, sub_zero]
  constructor
  · rintro ⟨t, ⟨ht₀, ht₁⟩, rfl⟩
    refine ⟨SameRay.sameRay_nonneg_smul_left w ht₀, ?_⟩
    rw [norm_smul, Real.norm_of_nonneg ht₀]
    nlinarith [norm_nonneg w]
  · rintro ⟨hray, hle⟩
    rcases eq_or_ne w 0 with rfl | hw
    · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
      simpa using (norm_le_zero_iff.mp (by simpa using hle)).symm
    -- With `w ≠ 0` the ray condition `‖m‖ • w = ‖w‖ • m` solves for `m` as `(‖m‖ / ‖w‖) • w`,
    -- and the norm comparison places that scalar in `[0, 1]`.
    · have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
      refine ⟨‖m‖ / ‖w‖, ⟨by positivity, (div_le_one hwpos).mpr hle⟩, ?_⟩
      rw [div_eq_inv_mul, mul_smul, hray.norm_smul_eq, inv_smul_smul₀ hwpos.ne']

/-- **Two points of a segment from the origin with the same norm coincide.** The segment `[0, w]`
carries no two distinct points at the same distance from `0`: it is contained in a ray, on which
the norm is injective (`norm_injOn_ray_right`). -/
theorem eq_of_mem_segment_zero_left_of_norm_eq {m₁ m₂ : E} (h₁ : m₁ ∈ [(0 : E) -[ℝ] w])
    (h₂ : m₂ ∈ [(0 : E) -[ℝ] w]) (h : ‖m₁‖ = ‖m₂‖) : m₁ = m₂ := by
  rcases eq_or_ne w 0 with rfl | hw
  · rw [segment_same, mem_singleton_iff] at h₁ h₂
    rw [h₁, h₂]
  · exact norm_injOn_ray_right hw (mem_segment_zero_left_iff_sameRay_and_norm_le.mp h₁).1
      (mem_segment_zero_left_iff_sameRay_and_norm_le.mp h₂).1 h

end Normed

/-! ### Half-open affine segments -/

section HalfOpen

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E]

/-- **A nonzero affine ray parametrizes a half-open segment.** If `y - x = D • u` with `D > 0`,
then the points `x + t • u` for `0 ≤ t < D` are exactly the segment from `x` to `y` with `y`
removed. -/
theorem image_add_smul_Ico {x y u : E} {D : 𝕜} (hDpos : 0 < D) (hu : u ≠ 0)
    (hdir : y - x = D • u) :
    (fun t : 𝕜 => x + t • u) '' Ico 0 D = segment 𝕜 x y \ {y} := by
  rw [segment_eq_image' 𝕜]
  apply Subset.antisymm
  · rintro z ⟨t, ⟨ht0, htD⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · refine ⟨t / D, ⟨div_nonneg ht0 hDpos.le, (div_lt_one hDpos).2 htD |>.le⟩, ?_⟩
      rw [hdir]
      simp only [smul_smul, div_mul_cancel₀ t hDpos.ne']
    · intro h
      apply htD.ne
      have hEq : x + t • u = y := by simpa using h
      have hmul : t • u = D • u := by
        calc
          t • u = x + t • u - x := by abel
          _ = y - x := by rw [hEq]
          _ = D • u := hdir
      exact smul_left_injective 𝕜 hu hmul
  · intro z hz
    rcases hz with ⟨hzseg, hzYnot⟩
    rcases hzseg with ⟨t, ht, rfl⟩
    have htD : t < 1 := by
      by_contra hnot
      have hteq : t = 1 := le_antisymm ht.2 (le_of_not_gt hnot)
      apply hzYnot
      simp [hteq]
    refine ⟨t * D, ⟨mul_nonneg ht.1 hDpos.le, ?_⟩, ?_⟩
    · nlinarith [ht.2, hDpos]
    · rw [hdir]
      simp only [smul_smul]

/-- A point `x` lies on the segment from `a` to any point `lineMap a x T` with `1 ≤ T`, that is,
to any point at or beyond `x` on the ray from `a` through `x`. -/
theorem mem_segment_lineMap_of_one_le {a x : E} {T : 𝕜} (hT : 1 ≤ T) :
    x ∈ segment 𝕜 a (AffineMap.lineMap a x T) := by
  rw [segment_eq_image_lineMap]
  refine ⟨T⁻¹, ⟨inv_nonneg.2 (zero_le_one.trans hT), inv_le_one_of_one_le₀ hT⟩, ?_⟩
  rw [AffineMap.lineMap_lineMap_right, inv_mul_cancel₀ (zero_lt_one.trans_le hT).ne',
    AffineMap.lineMap_apply_one]

end HalfOpen

/-! ### Overlaps of affine images of the unit interval -/

section Overlap

open AffineMap

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- **The overlap of `[0, 1]` with an affine image of `[0, 1]`.** Let `f = lineMap a b` be an
affine function on `𝕜` taking distinct values in `[0, 1]` at two points of `[0, 1]`. Then the
overlap of `[0, 1]` with `f '' [0, 1]` is a nondegenerate interval, and its two ends are values
`f u` at points `u ∈ [0, 1]` with `u` or `f u` an end of `[0, 1]`. -/
theorem exists_lineMap_endpoint {a b t t' : 𝕜} (ht : t ∈ Icc 0 1) (ht' : t' ∈ Icc 0 1)
    (hs : lineMap a b t ∈ Icc (0 : 𝕜) 1) (hs' : lineMap a b t' ∈ Icc (0 : 𝕜) 1)
    (hne : lineMap a b t ≠ lineMap a b t') :
    ∃ u₁ u₂ : 𝕜, lineMap a b u₁ ≠ lineMap a b u₂ ∧ ∀ u ∈ ({u₁, u₂} : Set 𝕜),
      u ∈ Icc (0 : 𝕜) 1 ∧ lineMap a b u ∈ Icc (0 : 𝕜) 1 ∧
        (u = 0 ∨ u = 1 ∨ lineMap a b u = 0 ∨ lineMap a b u = 1) := by
  have hab : a ≠ b := by rintro rfl; simp at hne
  have hI : Icc (0 : 𝕜) 1 ∩ lineMap a b '' Icc (0 : 𝕜) 1 = Icc (0 ⊔ (a ⊓ b)) (1 ⊓ (a ⊔ b)) := by
    rw [← segment_eq_image_lineMap, segment_eq_uIcc, uIcc, Icc_inter_Icc]
  have hmem {u : 𝕜} (hu : u ∈ Icc (0 : 𝕜) 1) (hfu : lineMap a b u ∈ Icc (0 : 𝕜) 1) :
      lineMap a b u ∈ Icc (0 ⊔ (a ⊓ b)) (1 ⊓ (a ⊔ b)) :=
    hI ▸ ⟨hfu, mem_image_of_mem _ hu⟩
  have hlt : 0 ⊔ (a ⊓ b) < 1 ⊓ (a ⊔ b) := by
    obtain ⟨h₁, h₂⟩ := hmem ht hs
    obtain ⟨h₃, h₄⟩ := hmem ht' hs'
    by_contra! hle
    exact hne (le_antisymm (h₂.trans (hle.trans h₃)) (h₄.trans (hle.trans h₁)))
  -- Each end of the overlap is `0`, `1`, `f 0 = a` or `f 1 = b`.
  have key (e : 𝕜) (he : e ∈ Icc (0 ⊔ (a ⊓ b)) (1 ⊓ (a ⊔ b)))
      (hcases : e = 0 ∨ e = 1 ∨ e = a ∨ e = b) :
      ∃ u, lineMap a b u = e ∧ u ∈ Icc (0 : 𝕜) 1 ∧ lineMap a b u ∈ Icc (0 : 𝕜) 1 ∧
        (u = 0 ∨ u = 1 ∨ lineMap a b u = 0 ∨ lineMap a b u = 1) := by
    rw [← hI] at he
    obtain ⟨he₁, u, hu, rfl⟩ := he
    refine ⟨u, rfl, hu, he₁, ?_⟩
    rcases hcases with h | h | h | h
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr h))
    · exact .inl ((lineMap_eq_left_iff.1 h).resolve_left hab)
    · exact .inr (.inl ((lineMap_eq_right_iff.1 h).resolve_left hab))
  obtain ⟨u₁, hu₁, h₁⟩ := key _ (left_mem_Icc.2 hlt.le) (by
    rcases max_choice 0 (a ⊓ b) with h | h <;> rw [h]
    · exact .inl rfl
    · rcases min_choice a b with h' | h' <;> rw [h'] <;> simp)
  obtain ⟨u₂, hu₂, h₂⟩ := key _ (right_mem_Icc.2 hlt.le) (by
    rcases min_choice 1 (a ⊔ b) with h | h <;> rw [h]
    · exact .inr (.inl rfl)
    · rcases max_choice a b with h' | h' <;> rw [h'] <;> simp)
  refine ⟨u₁, u₂, hu₁ ▸ hu₂ ▸ hlt.ne, ?_⟩
  rintro u (rfl | rfl)
  exacts [h₁, h₂]

end Overlap

/-! ### The inner-product forms -/

section InnerProduct

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {x y : F}

/-- **Membership in the segment from the origin, read off the inner product.** The inner-product
form of `TauCeti.mem_segment_zero_left_iff_sameRay_and_norm_le`: by `sameRay_iff_norm_smul_eq` and
`inner_eq_norm_mul_iff_real`, two vectors lie on a common ray exactly when Cauchy–Schwarz is an
equality for them. -/
theorem mem_segment_zero_left_iff_real_inner_eq_norm_mul_and_norm_le :
    x ∈ [(0 : F) -[ℝ] y] ↔ ⟪x, y⟫ = ‖x‖ * ‖y‖ ∧ ‖x‖ ≤ ‖y‖ := by
  rw [mem_segment_zero_left_iff_sameRay_and_norm_le, sameRay_iff_norm_smul_eq,
    inner_eq_norm_mul_iff_real, eq_comm]

/-- **The origin lies between two vectors exactly when their inner product is minimal.** The mirror
of `TauCeti.mem_segment_zero_left_iff_real_inner_eq_norm_mul_and_norm_le`, with the origin in the
middle of the segment rather than at an end: `mem_segment_iff_sameRay` at the point `0` says that
`x` and `-y` lie on a common ray, so Cauchy–Schwarz is an equality at the other end of its range,
`⟪x, y⟫_ℝ = -(‖x‖ * ‖y‖)`.

No nondegeneracy is needed: if `x = 0` then `0` is an endpoint of the segment and both sides hold,
and symmetrically for `y`. -/
theorem zero_mem_segment_iff_real_inner_eq_neg_norm_mul :
    (0 : F) ∈ [x -[ℝ] y] ↔ ⟪x, y⟫ = -(‖x‖ * ‖y‖) := by
  rw [mem_segment_iff_sameRay, zero_sub, sub_zero, sameRay_neg_swap, sameRay_iff_norm_smul_eq,
    eq_comm, ← inner_eq_norm_mul_iff_real, inner_neg_right, norm_neg, neg_eq_iff_eq_neg]

end InnerProduct

end TauCeti
