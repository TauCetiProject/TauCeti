/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.NormalForm
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.GaussBonnet
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Height
import TauCeti.Data.Fin.Basic

/-!
# Truncating a convex polygon at its ideal vertices

A convex hyperbolic polygon with ideal vertices is not compact: it runs off to the boundary of `ℍ`
at each ideal vertex. This file proves that this is the only way in which it fails to be compact.
Removing from the carrier an open horodisc at each ideal vertex, of arbitrary height, leaves a
compact set (`ConvexPolygon.isCompact_carrier_diff_iUnion`).

A horodisc at an ideal vertex `ξ` is described by an element `g ∈ PSL(2, ℝ)` with `g • ξ = ∞` and
a height `A`, as the set `{z | A < Im (g • z)}`. For a cusp datum of a Fuchsian group this is the
horodisc `TauCeti.Subgroup.CuspDatum.horodisc` at the cusp, with `g` the scaling of the datum.
This is the compactness of the truncated fundamental polygon that feeds the compactness criterion
`Subgroup.CompactifiedQuotient.compactSpace_of_compact_truncations` for cusp compactifications.

## Proof

The statement is invariant under `PSL(2, ℝ)` and under relabelling the vertices, so either all
vertices lie in `ℍ`, and the carrier is compact already, or `vertex 0` is `∞` and its horodisc is
`{z | A < Im z}`. In the second case the carrier lies in a vertical strip, and is the union of the
triangles `∞, vertex k, vertex (k + 1)` of the fan from `∞`, each of them the region above a
semicircle of centre `m` and radius `ρ` (`ConvexPolygon.exists_carrier_inter_strip_eq`). Above
such a semicircle, between its centre and a finite endpoint `p`, the height is at least `Im p`.
Between its centre and a real endpoint `x` it satisfies `ρ |Re z - x| ≤ (Im z)²`, so that a point
outside a horodisc at `x`, where `Im z ≤ K |z - x|²`, has height at least `min ρ (1 / (2K))`.
Every truncated triangle therefore lies in a compact rectangle of `ℍ`.

## Main result

* `ConvexPolygon.isCompact_carrier_diff_iUnion`: a convex polygon minus open horodiscs at its
  ideal vertices is compact.

## References

* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §4.2 (a fundamental region minus cusp neighbourhoods is compact).
* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §2.4.
-/

public section

open Set UpperHalfPlane
open scoped MatrixGroups Pointwise OnePoint

namespace TauCeti.UpperHalfPlane

/-! ### Heights above a semicircle -/

/-- Above a semicircle of centre `m` through the point `p ∈ ℍ`, the height of a point whose real
part lies between `Re p` and `m` is at least that of `p`. -/
private theorem im_le_im_of_normSq_sub_eq {m ρ : ℝ} {p z : ℍ}
    (hp : Complex.normSq ((p : ℂ) - m) = ρ ^ 2) (hz : ρ ^ 2 ≤ Complex.normSq ((z : ℂ) - m))
    (hre : (z.re - p.re) * (z.re - m) ≤ 0) : p.im ≤ z.im := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero, coe_re, coe_im] at hp hz
  have hp₀ := p.im_pos
  have hz₀ := z.im_pos
  -- `Re z` is at least as close to `m` as `Re p`
  have hsq : (z.re - m) ^ 2 ≤ (p.re - m) ^ 2 := by nlinarith
  nlinarith

/-- Above a semicircle of centre `m` and radius `ρ` ending at the real point `x`, a point `z` whose
real part lies between `x` and `m`, and which lies outside the horodisc `Im z > K |z - x|²` at `x`,
has height at least `min ρ (1 / (2K))`. -/
private theorem min_le_im_of_sq_sub_eq {m ρ x K : ℝ} {z : ℍ} (hρ : 0 < ρ) (hK : 0 < K)
    (hx : (x - m) ^ 2 = ρ ^ 2) (hz : ρ ^ 2 ≤ Complex.normSq ((z : ℂ) - m))
    (hre : (z.re - x) * (z.re - m) ≤ 0) (hh : z.im ≤ K * Complex.normSq ((z : ℂ) - x)) :
    min ρ (1 / (2 * K)) ≤ z.im := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero, coe_re, coe_im] at hz hh
  by_contra hlt
  obtain ⟨hyρ, hyK⟩ := lt_min_iff.1 (not_le.1 hlt)
  set u := z.re - x
  set y := z.im
  have hy := z.im_pos
  -- with `t = m - x`, so that `t² = ρ²`: `u² ≤ u t ≤ y²`
  have h₁ : u ^ 2 ≤ u * (m - x) := by nlinarith
  have h₂ : u * (m - x) ≤ y ^ 2 := by nlinarith
  -- `ρ² u² = (u t)² ≤ y⁴ ≤ ρ² y²`, so `u² ≤ y²`
  have h₃ : (u * (m - x)) ^ 2 ≤ (y ^ 2) ^ 2 :=
    pow_le_pow_left₀ ((sq_nonneg u).trans h₁) h₂ 2
  have h₄ : u ^ 2 ≤ y ^ 2 := by
    have hyρ' : y ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ hy.le hyρ.le 2
    have : ρ ^ 2 * u ^ 2 ≤ ρ ^ 2 * y ^ 2 := by
      calc ρ ^ 2 * u ^ 2 = (u * (m - x)) ^ 2 := by rw [mul_pow, ← hx, sub_sq', sub_sq']; ring
        _ ≤ (y ^ 2) ^ 2 := h₃
        _ = y ^ 2 * y ^ 2 := by ring
        _ ≤ ρ ^ 2 * y ^ 2 := mul_le_mul_of_nonneg_right hyρ' (sq_nonneg y)
    exact le_of_mul_le_mul_left this (by positivity)
  -- outside the horodisc, `y ≤ K (u² + y²) ≤ 2 K y²`, so `1 / (2K) ≤ y`
  have h₅ : 1 ≤ 2 * K * y := by
    have : y ≤ 2 * K * y * y := by nlinarith
    nlinarith
  rw [lt_div_iff₀ (by positivity)] at hyK
  linarith

namespace ConvexPolygon

variable {n : ℕ} [NeZero n] (P : ConvexPolygon n)

/-! ### The truncated carrier -/

/-- The carrier minus open horodiscs at the ideal vertices is closed. -/
private theorem isClosed_carrier_diff_iUnion (g : Fin n → PSL(2, ℝ)) (A : Fin n → ℝ) :
    IsClosed (P.carrier \ ⋃ i, ⋃ (_ : (P.vertex i).isRight), {z : ℍ | A i < (g i • z).im}) :=
  P.isClosed_carrier.sdiff (isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦
    isOpen_lt continuous_const (continuous_im.comp (continuous_const_smul _)))

/-- Membership in the carrier minus open horodiscs at the ideal vertices. -/
private theorem mem_carrier_diff_iUnion_iff (g : Fin n → PSL(2, ℝ)) (A : Fin n → ℝ) (z : ℍ) :
    z ∈ P.carrier \ ⋃ i, ⋃ (_ : (P.vertex i).isRight), {z : ℍ | A i < (g i • z).im} ↔
      z ∈ P.carrier ∧ ∀ i, (P.vertex i).isRight → (g i • z).im ≤ A i := by
  simp only [mem_sdiff, mem_iUnion, mem_ofPred_eq, not_exists, not_lt]

/-! ### A polygon with an ideal vertex at `∞` -/

/-- If `vertex 0` is `∞`, then near any other vertex `k`, above a semicircle through `vertex k`
and between `vertex k` and the centre of the semicircle, the points outside the horodiscs have
heights bounded below. -/
private theorem exists_pos_le_im_of_vertex (h₀ : P.vertex 0 = .inr ∞) {g : Fin n → PSL(2, ℝ)}
    (hg : ∀ i ξ, P.vertex i = .inr ξ → g i • ξ = ∞) (A : Fin n → ℝ) {k : Fin n} (hk : k ≠ 0)
    {m ρ : ℝ} (hρ : 0 < ρ) (hkm : Complex.normSq (toComplex (P.vertex k) - m) = ρ ^ 2) :
    ∃ ε > 0, ∀ z : ℍ, (∀ i, (P.vertex i).isRight → (g i • z).im ≤ A i) →
      ρ ^ 2 ≤ Complex.normSq ((z : ℂ) - m) →
        (z.re - (toComplex (P.vertex k)).re) * (z.re - m) ≤ 0 → ε ≤ z.im := by
  cases hv : P.vertex k with
  | inl p =>
    rw [hv, toComplex_inl] at hkm
    refine ⟨p.im, p.im_pos, fun z _ hz hre ↦ im_le_im_of_normSq_sub_eq hkm hz ?_⟩
    rwa [toComplex_inl, coe_re] at hre
  | inr ξ =>
    obtain ⟨x, rfl⟩ := OnePoint.ne_infty_iff_exists.1 fun h ↦
      P.vertex_ne_inr_infty_of_vertex_zero h₀ hk (hv.trans (congrArg _ h))
    rw [hv, toComplex_inr_coe, ← Complex.ofReal_sub, Complex.normSq_ofReal, ← sq] at hkm
    obtain ⟨c, hc, hgc⟩ := exists_im_smul_eq_div_of_smul_coe_eq_infty (hg k x hv)
    have hK : 0 < max (A k) 1 * c := mul_pos (lt_max_of_lt_right one_pos) hc
    refine ⟨min ρ (1 / (2 * (max (A k) 1 * c))), lt_min hρ (by positivity),
      fun z htr hz hre ↦ min_le_im_of_sq_sub_eq hρ hK hkm hz ?_ ?_⟩
    · rwa [toComplex_inr_coe, Complex.ofReal_re] at hre
    · -- outside the horodisc at `x`: `Im z = Im (g • z) · c |z - x|² ≤ A c |z - x|²`
      have hN : 0 < c * Complex.normSq ((z : ℂ) - x) :=
        mul_pos hc (Complex.normSq_pos.2 (sub_ne_zero.2 fun h ↦
          z.im_pos.ne' (by simpa using congrArg Complex.im h)))
      have h := htr k (by rw [hv]; rfl)
      rw [hgc, div_le_iff₀ hN] at h
      calc z.im ≤ A k * (c * Complex.normSq ((z : ℂ) - x)) := h
        _ ≤ max (A k) 1 * (c * Complex.normSq ((z : ℂ) - x)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hN.le
        _ = max (A k) 1 * c * Complex.normSq ((z : ℂ) - x) := by ring

/-- If `vertex 0` is `∞`, the points of the triangle of the fan from `∞` with vertices `vertex k`
and `vertex (k + 1)` that lie outside the horodiscs have heights bounded below. -/
private theorem exists_pos_le_im_of_strip (h₀ : P.vertex 0 = .inr ∞) {g : Fin n → PSL(2, ℝ)}
    (hg : ∀ i ξ, P.vertex i = .inr ξ → g i • ξ = ∞) (A : Fin n → ℝ) {k : Fin n} (hk : k ≠ 0)
    (hk' : k + 1 ≠ 0) :
    ∃ ε > 0, ∀ z ∈ P.carrier, (∀ i, (P.vertex i).isRight → (g i • z).im ≤ A i) →
      (toComplex (P.vertex k)).re ≤ z.re → z.re ≤ (toComplex (P.vertex (k + 1))).re →
        ε ≤ z.im := by
  obtain ⟨m, ρ, hρ, hk₁, hk₂, heq⟩ := P.exists_carrier_inter_strip_eq h₀ hk hk'
  obtain ⟨ε₁, hε₁, h₁⟩ := P.exists_pos_le_im_of_vertex h₀ hg A hk hρ hk₁
  obtain ⟨ε₂, hε₂, h₂⟩ := P.exists_pos_le_im_of_vertex h₀ hg A hk' hρ hk₂
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun z hz htr hle hle' ↦ ?_⟩
  have hρz : ρ ^ 2 ≤ Complex.normSq ((z : ℂ) - m) :=
    ((mem_idealRegionAbove_iff _ _ _ _ z).1 (heq.subset (mem_inter hz ⟨hle, hle'⟩))).2.2
  rcases le_total z.re m with hm | hm
  · exact (min_le_left _ _).trans
      (h₁ z htr hρz (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hle) (sub_nonpos.2 hm)))
  · exact (min_le_right _ _).trans
      (h₂ z htr hρz (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hle') (sub_nonneg.2 hm)))

open Fin.NatCast in
/-- If `vertex 0` is `∞`, every point of the carrier lies between the verticals through
`vertex k` and `vertex (k + 1)` for some `k` with `k ≠ 0` and `k + 1 ≠ 0`. -/
private theorem exists_re_mem_strip (h₀ : P.vertex 0 = .inr ∞) {z : ℍ} (hz : z ∈ P.carrier) :
    ∃ k : Fin n, k ≠ 0 ∧ k + 1 ≠ 0 ∧ (toComplex (P.vertex k)).re ≤ z.re ∧
      z.re ≤ (toComplex (P.vertex (k + 1))).re := by
  have hn := P.three_le
  set x : ℕ → ℝ := fun k ↦ (toComplex (P.vertex (k : Fin n))).re
  -- the real parts `x 1, …, x (n - 1)` are sorted, so `z.re` lies in one of the gaps
  have key : ∀ b, 1 ≤ b → x 1 ≤ z.re → z.re ≤ x (b + 1) →
      ∃ k, 1 ≤ k ∧ k ≤ b ∧ x k ≤ z.re ∧ z.re ≤ x (k + 1) := by
    intro b hb h₁ h₂
    induction b, hb using Nat.le_induction with
    | base => exact ⟨1, le_rfl, le_rfl, h₁, h₂⟩
    | succ b hb ih =>
      by_cases hb' : z.re ≤ x (b + 1)
      · obtain ⟨k, hk₁, hk₂, hk⟩ := ih hb'
        exact ⟨k, hk₁, hk₂.trans b.le_succ, hk⟩
      · exact ⟨b + 1, by omega, le_rfl, (not_le.1 hb').le, h₂⟩
  have hneg : ((n - 2 + 1 : ℕ) : Fin n) = -1 := eq_neg_of_add_eq_zero_left (by
    rw [← Nat.cast_add_one, show n - 2 + 1 + 1 = n by omega, Fin.natCast_self])
  obtain ⟨k, hk₁, hk₂, hk⟩ := key (n - 2) (by omega)
    (by simpa [x] using P.re_toComplex_vertex_one_le_of_mem_carrier h₀ hz)
    (by simpa [x, hneg] using P.re_le_re_toComplex_vertex_neg_one_of_mem_carrier h₀ hz)
  refine ⟨k, Fin.natCast_ne_zero (by omega) (by omega), ?_, ?_⟩
  · rw [← Nat.cast_add_one]
    exact Fin.natCast_ne_zero (by omega) (by omega)
  · simpa [x] using hk

/-- The truncation theorem for a convex polygon whose `vertex 0` is `∞`, with the horodisc at `∞`
in its standard form `{z | A 0 < Im z}`. -/
private theorem isCompact_carrier_diff_iUnion_of_vertex_zero (h₀ : P.vertex 0 = .inr ∞)
    {g : Fin n → PSL(2, ℝ)} (hg : ∀ i ξ, P.vertex i = .inr ξ → g i • ξ = ∞) (hg₀ : g 0 = 1)
    (A : Fin n → ℝ) :
    IsCompact (P.carrier \ ⋃ i, ⋃ (_ : (P.vertex i).isRight), {z : ℍ | A i < (g i • z).im}) := by
  choose ε hε hεle using fun (k : Fin n) (hk : k ≠ 0 ∧ k + 1 ≠ 0) ↦
    P.exists_pos_le_im_of_strip h₀ hg A hk.1 hk.2
  -- the rectangle of `ℍ` containing the truncated triangle of the fan between `vertex k` and
  -- `vertex (k + 1)`
  set R : ∀ k : Fin n, (k ≠ 0 ∧ k + 1 ≠ 0) → Set ℂ := fun k hk ↦
    Icc (toComplex (P.vertex k)).re (toComplex (P.vertex (k + 1))).re ×ℂ Icc (ε k hk) (A 0)
  have hR : ∀ k hk, IsCompact (((↑) : ℍ → ℂ) ⁻¹' R k hk) := fun k hk ↦
    (isOpenEmbedding_coe.isInducing.isCompact_preimage_iff fun w hw ↦ by
      rw [range_coe]
      exact (hε k hk).trans_le (Complex.mem_reProdIm.1 hw).2.1).2
      (isCompact_Icc.reProdIm isCompact_Icc)
  refine (isCompact_iUnion fun k ↦ isCompact_iUnion fun hk ↦ hR k hk).of_isClosed_subset
    (P.isClosed_carrier_diff_iUnion g A) fun z hz ↦ ?_
  obtain ⟨hzc, htr⟩ := (P.mem_carrier_diff_iUnion_iff g A z).1 hz
  obtain ⟨k, hk, hk', hle, hle'⟩ := P.exists_re_mem_strip h₀ hzc
  have htop : z.im ≤ A 0 := by simpa [hg₀] using htr 0 (by rw [h₀]; rfl)
  refine mem_iUnion₂.2 ⟨k, ⟨hk, hk'⟩, ?_⟩
  rw [mem_preimage, Complex.mem_reProdIm, coe_re, coe_im]
  exact ⟨⟨hle, hle'⟩, hεle k ⟨hk, hk'⟩ z hzc htr hle hle', htop⟩

/-! ### The truncation theorem -/

/-- **A convex polygon truncated at its ideal vertices is compact.** For each ideal vertex
`vertex i = ξ` of a convex polygon `P`, let `g i ∈ PSL(2, ℝ)` carry `ξ` to `∞`, so that
`{z | A i < Im (g i • z)}` is an open horodisc at `ξ`, of arbitrary height `A i`. Then the carrier
of `P` minus these horodiscs is compact. The values of `g i` and `A i` at the vertices in `ℍ` play
no role. -/
theorem isCompact_carrier_diff_iUnion (g : Fin n → PSL(2, ℝ))
    (hg : ∀ i ξ, P.vertex i = .inr ξ → g i • ξ = ∞) (A : Fin n → ℝ) :
    IsCompact (P.carrier \ ⋃ i, ⋃ (_ : (P.vertex i).isRight), {z : ℍ | A i < (g i • z).im}) := by
  by_cases hfin : ∀ i, ∃ z : ℍ, P.vertex i = .inl z
  · -- without ideal vertices the carrier is compact already
    obtain ⟨Q, rfl⟩ := P.exists_eq_toConvexPolygon hfin
    rw [CompactConvexPolygon.carrier_toConvexPolygon]
    exact Q.isCompact_carrier.diff (isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦
      isOpen_lt continuous_const (continuous_im.comp (continuous_const_smul _)))
  -- otherwise move an ideal vertex `vertex i₀` to `vertex 0 = ∞` by `g i₀`
  push Not at hfin
  obtain ⟨i₀, hi₀⟩ := hfin
  obtain ⟨ξ, hξ⟩ : ∃ ξ, P.vertex i₀ = .inr ξ := by
    cases hv : P.vertex i₀ with
    | inl z => exact absurd hv (hi₀ z)
    | inr ξ => exact ⟨ξ, rfl⟩
  set h := g i₀
  set Q := h • P.rotate i₀
  have hQ₀ : Q.vertex 0 = .inr ∞ := by
    simp only [Q, vertex_smul, vertex_rotate, zero_add, hξ, Sum.smul_inr, h, hg i₀ ξ hξ]
  have hQg : ∀ j η, Q.vertex j = .inr η → (g (j + i₀) * h⁻¹) • η = ∞ := by
    intro j η hj
    simp only [Q, vertex_smul, vertex_rotate] at hj
    cases hv : P.vertex (j + i₀) with
    | inl w => simp [hv] at hj
    | inr ζ =>
      rw [hv, Sum.smul_inr, Sum.inr.injEq] at hj
      rw [← hj, mul_smul, inv_smul_smul, hg _ ζ hv]
  have hQ := Q.isCompact_carrier_diff_iUnion_of_vertex_zero hQ₀ hQg (by simp [h])
    fun j ↦ A (j + i₀)
  refine (hQ.image (continuous_const_smul h⁻¹)).of_isClosed_subset
    (P.isClosed_carrier_diff_iUnion g A) fun z hz ↦ ⟨h • z, ?_, inv_smul_smul h z⟩
  obtain ⟨hzc, htr⟩ := (P.mem_carrier_diff_iUnion_iff g A z).1 hz
  refine (Q.mem_carrier_diff_iUnion_iff _ _ _).2 ⟨?_, fun j hj ↦ ?_⟩
  · rw [carrier_smul, carrier_rotate]
    exact smul_mem_smul_set hzc
  · rw [mul_smul, inv_smul_smul]
    refine htr _ ?_
    simp only [Q, vertex_smul, vertex_rotate] at hj
    cases hv : P.vertex (j + i₀) <;> simp_all

end ConvexPolygon

end TauCeti.UpperHalfPlane
