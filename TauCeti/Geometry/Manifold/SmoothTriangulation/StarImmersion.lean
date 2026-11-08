/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothTriangulation.Secant
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Finite
public import TauCeti.Geometry.Manifold.SmoothTriangulation.Edgewise
import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Coordinates
import TauCeti.Analysis.Calculus.FDeriv.Antilipschitz
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.TangentCone.Real
import TauCeti.Geometry.Manifold.SmoothTriangulation.Lipschitz

/-!
# Star immersions of complexes

Munkres calls a map `f : |K| → E` of a complex an *immersion* if it is `C¹` on every closed
simplex and, at every point `b`, its differential is injective on the closed star of `b`: on a
simplex `σ` containing `b`, the differential sends `x` to the derivative of `f` at `b` in the
direction `x - b`, and the condition compares points of different simplices of the star. We call
these maps star immersions, to distinguish them from immersions of a single simplex.

The condition across simplices is what makes an injective immersion of a complex quantitatively
injective. Being an immersion on every closed simplex is not enough: two edges leaving a vertex
in the same direction, say as `t ↦ (t, t ^ 2)` and `t ↦ (t, -t ^ 2)`, give an injective map
whose points at parameter `t` are at distance `2 * t ^ 2` in the plane but at barycentric
distance of order `t`. For star immersions of a finite complex there is no such loss: an
injective star immersion is antilipschitz in barycentric coordinates.

By `AntilipschitzWith.add_sub_lipschitzWith`, this keeps perturbations with small Lipschitz error
antilipschitz, hence injective. The secant maps of `f` on fine edgewise subdivisions are such
perturbations: their difference with `f` is Lipschitz with arbitrarily small constant in
barycentric coordinates, also across different simplices. Hence the
secant maps of an injective star immersion of a finite complex are antilipschitz, with a constant
independent of the subdivision, and are closed embeddings. This is Munkres' secant approximation
of an embedding of a complex (Chapter II, Section 9): an embedding which is linear on every
simplex of a subdivision replaces the smooth one.

By Munkres' Theorem 8.4, a smooth triangulation of a manifold is a star immersion in charts, so
this is the separation input for comparing and fitting together smooth triangulations.

## Main definitions

* `TauCeti.IsStarImmersion n f`: `f` is a `Cⁿ` immersion on every closed simplex, and its
  differential at every point is injective on the closed star of that point.

## Main results

* `TauCeti.IsStarImmersion.exists_antilipschitzWith`: an injective `C¹` star immersion of a
  complex on a finite vertex type is antilipschitz in barycentric coordinates.
* `TauCeti.IsStarImmersion.exists_pos_eventually_norm_sub_le_mul_norm_secantMap_sub`: the secant
  maps of an injective `C¹` star immersion on fine edgewise subdivisions are antilipschitz in
  barycentric coordinates, uniformly in the subdivision.
* `TauCeti.IsStarImmersion.eventually_isClosedEmbedding_secantMap_edgewiseSubdivision`: the
  secant maps of an injective `C¹` star immersion of a finite complex on all sufficiently fine
  edgewise subdivisions are closed embeddings.
* `AbstractSimplicialComplex.isStarImmersion_secantMap`: an injective secant map, linear in
  barycentric coordinates on every closed simplex, is a star immersion.

## Implementation notes

The differential at `b` in the direction of `x` is the derivative from the right at `0` of `f`
along the segment from `b` to `x`, read with `Set.IccExtend` on `[0, 1]`. This needs no choice of
extensions of `f` off its simplices. The proof of the separation bound works in the ambient
coordinates `ι → ℝ`. Near a pair of nearby points `x` and `y` of two simplices it chooses a common
point `z` of the two simplices, compares `f` with its differential at `z`, and bounds the
differential from below by compactness after rescaling the pair from the barycenter of the common
face. For the secant maps, the Lipschitz bound for the secant error is
`TauCeti.eventually_norm_secantMap_sub_sub_le_edgewiseSubdivision` in
`SmoothTriangulation.Lipschitz`.

## References

* J. Munkres, *Elementary Differential Topology*, Annals of Math. Studies 54 (1966), Chapter II,
  Definitions 8.1–8.3 and Theorem 8.4, and Sections 9–10.
* J. H. C. Whitehead, *On C¹-complexes*, Ann. of Math. 41 (1940), 809–824.
-/

public section

noncomputable section

open Set Function AbstractSimplicialComplex Metric TauCeti.SetLike
open scoped Manifold ContDiff

namespace TauCeti

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : AbstractSimplicialComplex ι} {n : WithTop ℕ∞}

variable (n) in
/-- A map `f` from the realization of a complex into a normed space is a `Cⁿ` *star immersion*
(Munkres' immersion of a complex) if it is a `Cⁿ` immersion on every closed simplex, and at every
point `b` its differential is injective on the closed star of `b`. The differential at `b` sends a
point `x` of a closed simplex containing `b` to the derivative at `0`, from the right, of
`t ↦ f (b + t • (x - b))`; it is linear on each closed simplex containing `b`. Injectivity on the
closed star asks that two points `x` and `y` of closed simplices containing `b` with the same
image are equal, also when they lie in different simplices. -/
def IsStarImmersion (f : Realization K → E) : Prop :=
  (∀ σ : Face K, IsSimplexImmersion 𝓘(ℝ, E) n (f ∘ faceInclusion K σ)) ∧
    ∀ (σ τ : Face K) (b x : StandardSimplex σ.1) (b' y : StandardSimplex τ.1) (u : E),
      (b : ι →₀ ℝ) = b' →
      HasDerivWithinAt
        (IccExtend zero_le_one (f ∘ faceInclusion K σ ∘ StandardSimplex.lineMap b x))
        u (Icc 0 1) 0 →
      HasDerivWithinAt
        (IccExtend zero_le_one (f ∘ faceInclusion K τ ∘ StandardSimplex.lineMap b' y))
        u (Icc 0 1) 0 →
      (x : ι →₀ ℝ) = y

/-- Unfold `TauCeti.IsStarImmersion`. -/
theorem isStarImmersion_iff {f : Realization K → E} :
    IsStarImmersion n f ↔
      (∀ σ : Face K, IsSimplexImmersion 𝓘(ℝ, E) n (f ∘ faceInclusion K σ)) ∧
        ∀ (σ τ : Face K) (b x : StandardSimplex σ.1) (b' y : StandardSimplex τ.1) (u : E),
          (b : ι →₀ ℝ) = b' →
          HasDerivWithinAt
            (IccExtend zero_le_one (f ∘ faceInclusion K σ ∘ StandardSimplex.lineMap b x))
            u (Icc 0 1) 0 →
          HasDerivWithinAt
            (IccExtend zero_le_one (f ∘ faceInclusion K τ ∘ StandardSimplex.lineMap b' y))
            u (Icc 0 1) 0 →
          (x : ι →₀ ℝ) = y :=
  Iff.rfl

/-! ### Simplex immersions in ambient barycentric coordinates -/

section Coordinates

variable [Fintype ι] {σ : Finset ι}

/-- The closed simplex on `σ`, as a set of coordinate vectors. -/
private def coordSimplex (σ : Finset ι) : Set (ι → ℝ) :=
  {z | (∀ i, 0 ≤ z i) ∧ (∀ i ∉ σ, z i = 0) ∧ ∑ i, z i = 1}

private theorem range_standardSimplex_coe :
    range (fun x : StandardSimplex σ => (x.1 : ι → ℝ)) = coordSimplex σ :=
  Set.ext fun _ => mem_range_standardSimplex_coe_iff

private theorem convex_coordSimplex : Convex ℝ (coordSimplex σ) := by
  rw [← range_standardSimplex_coe]
  exact convex_range_standardSimplex_coe σ

private theorem isCompact_coordSimplex : IsCompact (coordSimplex σ) := by
  rw [← range_standardSimplex_coe]
  exact isCompact_range continuous_induced_dom

/-- A `Cⁿ` immersion of a simplex, `1 ≤ n`, read in the ambient barycentric coordinates `ι → ℝ`
of a finite vertex type: it is the restriction of a map with a continuous derivative within the
simplex. -/
private theorem exists_coord {g : StandardSimplex σ → E}
    (h : IsSimplexImmersion 𝓘(ℝ, E) n g) (hn : 1 ≤ n) :
    ∃ G : (ι → ℝ) → E, ∃ G' : (ι → ℝ) → (ι → ℝ) →L[ℝ] E,
      (∀ x : StandardSimplex σ, G x.1 = g x) ∧
      (∀ w ∈ coordSimplex σ, HasFDerivWithinAt G (G' w) (coordSimplex σ) w) ∧
      ContinuousOn G' (coordSimplex σ) := by
  obtain ⟨F, F', hFg, hFd, hFc, -⟩ := h.exists_continuousOn_hasFDerivWithinAt hn
  -- Restrict ambient coordinates to the vertices of the simplex.
  let r : (ι → ℝ) →L[ℝ] (σ → ℝ) := ContinuousLinearMap.pi fun a => ContinuousLinearMap.proj a.1
  have hmaps : MapsTo r (coordSimplex σ)
      (range fun t : Convexity.StdSimplex ℝ σ => ⇑t.weights) := by
    intro w hw
    rw [← range_standardSimplex_coe] at hw
    obtain ⟨x, rfl⟩ := hw
    rw [← Finset.range_standardSimplex_coordinates]
    exact ⟨x, rfl⟩
  refine ⟨F ∘ r, fun w => (F' (r w)).comp r, fun x => hFg x,
    fun w hw => (hFd _ (hmaps hw)).comp w r.hasFDerivWithinAt hmaps, ?_⟩
  exact (hFc.comp r.continuous.continuousOn hmaps).clm_comp continuousOn_const

/-- In ambient coordinates, the right derivative at `0` of `g` along the segment from `b` to `x`
is the derivative of a coordinate extension at `b` applied to `x - b`. -/
private theorem hasDerivWithinAt_lineMap {g : StandardSimplex σ → E} {G : (ι → ℝ) → E}
    {G' : (ι → ℝ) → (ι → ℝ) →L[ℝ] E} (hGg : ∀ x : StandardSimplex σ, G x.1 = g x)
    (hG : ∀ w ∈ coordSimplex σ, HasFDerivWithinAt G (G' w) (coordSimplex σ) w)
    (b x : StandardSimplex σ) :
    HasDerivWithinAt (IccExtend zero_le_one (g ∘ StandardSimplex.lineMap b x))
      (G' (b.1 : ι → ℝ) ((x.1 : ι → ℝ) - b.1)) (Icc 0 1) 0 := by
  have hb : (b.1 : ι → ℝ) ∈ coordSimplex σ := by rw [← range_standardSimplex_coe]; exact ⟨b, rfl⟩
  have hx : (x.1 : ι → ℝ) ∈ coordSimplex σ := by rw [← range_standardSimplex_coe]; exact ⟨x, rfl⟩
  have hline : HasDerivWithinAt (G ∘ AffineMap.lineMap (k := ℝ) (b.1 : ι → ℝ) (x.1 : ι → ℝ))
      (G' (b.1 : ι → ℝ) ((x.1 : ι → ℝ) - b.1)) (Icc (0 : ℝ) 1) 0 :=
    (hG _ hb).comp_hasDerivWithinAt_of_eq (0 : ℝ) AffineMap.hasDerivWithinAt_lineMap
      (fun t ht => convex_coordSimplex.lineMap_mem hb hx ht) (by simp)
  refine hline.congr_of_mem (fun t ht => ?_) (left_mem_Icc.2 zero_le_one)
  rw [IccExtend_of_mem _ _ ht, comp_apply, comp_apply, ← hGg, StandardSimplex.coe_lineMap]
  simp [AffineMap.lineMap_apply_module]

/-- Moving from a point `β` of the closed simplex on `σ ∩ τ`, all of whose coordinates on
`σ ∩ τ` are at least `κ`, by `s • (u - z)` with `u` in the simplex on `σ` and `z` in that on
`σ ∩ τ`, stays in the simplex on `σ` as long as `s * ‖u - z‖ ≤ κ`. -/
private theorem add_smul_sub_mem {σ τ : Finset ι} {u z β : ι → ℝ} (hu : u ∈ coordSimplex σ)
    (hz : z ∈ coordSimplex σ ∩ coordSimplex τ) (hβ : β ∈ coordSimplex σ ∩ coordSimplex τ)
    {κ s : ℝ} (hβκ : ∀ i ∈ σ, i ∈ τ → κ ≤ β i) (hs : 0 ≤ s) (hsκ : s * ‖u - z‖ ≤ κ) :
    β + s • (u - z) ∈ coordSimplex σ := by
  refine ⟨fun i => ?_, fun i hi => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    by_cases hi : i ∈ σ ∧ i ∈ τ
    · have h := (abs_le.1 ((Real.norm_eq_abs _).symm.trans_le (norm_le_pi_norm (u - z) i))).1
      simp only [Pi.sub_apply] at h
      nlinarith [hβκ i hi.1 hi.2, mul_le_mul_of_nonneg_left h hs]
    · have hzero : β i = 0 ∧ z i = 0 := by
        by_cases hσ : i ∈ σ
        · have hτ : i ∉ τ := fun hτ => hi ⟨hσ, hτ⟩
          exact ⟨hβ.2.2.1 i hτ, hz.2.2.1 i hτ⟩
        · exact ⟨hβ.1.2.1 i hσ, hz.1.2.1 i hσ⟩
      rw [hzero.1, hzero.2, sub_zero, zero_add]
      exact mul_nonneg hs (hu.1 i)
  · simp [hβ.1.2.1 i hi, hz.1.2.1 i hi, hu.2.1 i hi]
  · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_sub_distrib, hu.2.2, hz.1.2.2, sub_self, mul_zero, add_zero]
    exact hβ.1.2.2

/-- By compactness, jointly injective differentials at the common points of two closed simplices
are bounded below on pairs of points at a fixed distance `r > 0`. -/
private theorem exists_pos_le_norm_differential {σ τ : Finset ι}
    {G'σ G'τ : (ι → ℝ) → (ι → ℝ) →L[ℝ] E}
    (hG'σ : ContinuousOn G'σ (coordSimplex σ)) (hG'τ : ContinuousOn G'τ (coordSimplex τ))
    (hstar : ∀ b ∈ coordSimplex σ ∩ coordSimplex τ, ∀ x ∈ coordSimplex σ, ∀ y ∈ coordSimplex τ,
      G'σ b (x - b) = G'τ b (y - b) → x = y) {r : ℝ} (hr : 0 < r) :
    ∃ c > 0, ∀ b ∈ coordSimplex σ ∩ coordSimplex τ, ∀ x ∈ coordSimplex σ, ∀ y ∈ coordSimplex τ,
      ‖x - y‖ = r → c ≤ ‖G'σ b (x - b) - G'τ b (y - b)‖ := by
  have hσc : IsCompact (coordSimplex σ) := isCompact_coordSimplex
  have hτc : IsCompact (coordSimplex τ) := isCompact_coordSimplex
  set P := (coordSimplex σ ∩ coordSimplex τ) ×ˢ
    ((coordSimplex σ ×ˢ coordSimplex τ) ∩ {q : (ι → ℝ) × (ι → ℝ) | ‖q.1 - q.2‖ = r})
  have hP : IsCompact P := (hσc.inter_right hτc.isClosed).prod ((hσc.prod hτc).inter_right
    (isClosed_eq (continuous_fst.sub continuous_snd).norm continuous_const))
  have hPσ : MapsTo Prod.fst P (coordSimplex σ) := fun p hp => hp.1.1
  have hPτ : MapsTo Prod.fst P (coordSimplex τ) := fun p hp => hp.1.2
  obtain ⟨c, hc, hle⟩ := hP.exists_forall_le' (a := 0)
    (f := fun p => ‖G'σ p.1 (p.2.1 - p.1) - G'τ p.1 (p.2.2 - p.1)‖)
    (((hG'σ.comp continuousOn_fst hPσ).clm_apply
      (continuous_snd.fst.sub continuous_fst).continuousOn).sub
      ((hG'τ.comp continuousOn_fst hPτ).clm_apply
      (continuous_snd.snd.sub continuous_fst).continuousOn)).norm
    (fun p hp => norm_pos_iff.2 fun h => by
      have hdist : ‖p.2.1 - p.2.2‖ = r := hp.2.2
      rw [hstar p.1 hp.1 p.2.1 hp.2.1.1 p.2.2 hp.2.1.2 (sub_eq_zero.1 h), sub_self,
        norm_zero] at hdist
      exact hr.ne hdist)
  exact ⟨c, hc, fun b hb x hx y hy hxy => hle (b, x, y) ⟨hb, ⟨hx, hy⟩, hxy⟩⟩

/-- The differentials at common points of two closed simplices are uniformly bounded below on
nearby pairs. Let `G'σ` and `G'τ` be continuous within the closed simplices on `σ` and on `τ`, and
agree along their intersection. Suppose that at every common point `b`, the differential
`x ↦ G'σ b (x - b)` on the simplex on `σ` and `y ↦ G'τ b (y - b)` on the simplex on `τ` together
are injective. Then nearby points `x` and `y` of the two simplices have a common nearby point `z`
at which the differential separates them. -/
private theorem exists_pos_mul_norm_sub_le_differential {σ τ : Finset ι}
    {G'σ G'τ : (ι → ℝ) → (ι → ℝ) →L[ℝ] E}
    (hG'σ : ContinuousOn G'σ (coordSimplex σ)) (hG'τ : ContinuousOn G'τ (coordSimplex τ))
    (hagree : ∀ b ∈ coordSimplex σ ∩ coordSimplex τ, ∀ w ∈ coordSimplex σ ∩ coordSimplex τ,
      G'σ b (w - b) = G'τ b (w - b))
    (hstar : ∀ b ∈ coordSimplex σ ∩ coordSimplex τ, ∀ x ∈ coordSimplex σ, ∀ y ∈ coordSimplex τ,
      G'σ b (x - b) = G'τ b (y - b) → x = y) :
    ∃ c > 0, ∀ x ∈ coordSimplex σ, ∀ y ∈ coordSimplex τ, (Fintype.card ι : ℝ) * ‖x - y‖ < 1 →
      ∃ z ∈ coordSimplex σ ∩ coordSimplex τ, ‖y - z‖ ≤ Fintype.card ι * ‖x - y‖ ∧
        ‖x - z‖ ≤ (Fintype.card ι + 1) * ‖x - y‖ ∧
        c * ‖x - y‖ ≤ ‖G'σ z (x - z) - G'τ z (y - z)‖ := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun x hx => absurd hx.2.2 (by simp)⟩
  set N : ℝ := (Fintype.card ι : ℝ)
  have hN : 0 < N * (N + 1) := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 Fintype.card_pos
    positivity
  set r : ℝ := (N * (N + 1))⁻¹
  obtain ⟨c₀, hc₀, hcone⟩ := exists_pos_le_norm_differential hG'σ hG'τ hstar (inv_pos.2 hN)
  refine ⟨c₀ / r, by positivity, fun x hx y hy hxy => ?_⟩
  obtain ⟨z, hz, β, hβ, hyz, hβN⟩ := exists_mem_inter_range_standardSimplex_coe
    (by rwa [range_standardSimplex_coe]) (by rwa [range_standardSimplex_coe]) hxy
  rw [range_standardSimplex_coe, range_standardSimplex_coe] at hz hβ
  have hxz : ‖x - z‖ ≤ (N + 1) * ‖x - y‖ := by
    calc ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ := norm_sub_le_norm_sub_add_norm_sub x y z
      _ ≤ (N + 1) * ‖x - y‖ := by linarith
  refine ⟨z, hz, hyz, hxz, ?_⟩
  rcases eq_or_ne x y with rfl | hne
  · simp
  -- Rescale the pair from the barycenter `β` of the common face to distance `r`; by agreement
  -- of the differentials along that face, this rescales the differential.
  have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  set s : ℝ := r / ‖x - y‖
  have hs : 0 ≤ s := by positivity
  have hsr : s * ‖x - y‖ = r := div_mul_cancel₀ _ hpos.ne'
  -- Both moves have size at most `s * (N + 1) * ‖x - y‖ = N⁻¹`.
  have hsN : s * ((N + 1) * ‖x - y‖) = N⁻¹ := by
    rw [mul_left_comm, hsr, ← div_eq_mul_inv, mul_comm, ← div_div, div_self (by positivity),
      one_div]
  have hx' := add_smul_sub_mem hx hz hβ hβN hs
    ((mul_le_mul_of_nonneg_left hxz hs).trans hsN.le)
  have hy' := add_smul_sub_mem (σ := τ) (τ := σ) hy ⟨hz.2, hz.1⟩ ⟨hβ.2, hβ.1⟩
    (fun i hτ hσ => hβN i hσ hτ) hs
    ((mul_le_mul_of_nonneg_left (hyz.trans (by nlinarith)) hs).trans hsN.le)
  have hdist : ‖(β + s • (x - z)) - (β + s • (y - z))‖ = r := by
    rw [add_sub_add_left_eq_sub, ← smul_sub, sub_sub_sub_cancel_right, norm_smul,
      Real.norm_of_nonneg hs, hsr]
  have h := hcone z hz _ hx' _ hy' hdist
  have hscale : G'σ z (β + s • (x - z) - z) - G'τ z (β + s • (y - z) - z) =
      s • (G'σ z (x - z) - G'τ z (y - z)) := by
    rw [show β + s • (x - z) - z = (β - z) + s • (x - z) by abel,
      show β + s • (y - z) - z = (β - z) + s • (y - z) by abel, map_add, map_add, map_smul,
      map_smul, hagree z hz β hβ, smul_sub]
    abel
  simp only [hscale, norm_smul, Real.norm_of_nonneg hs] at h
  rw [div_mul_eq_mul_div, div_le_iff₀ (inv_pos.2 hN)]
  calc c₀ * ‖x - y‖ ≤ s * ‖G'σ z (x - z) - G'τ z (y - z)‖ * ‖x - y‖ :=
        mul_le_mul_of_nonneg_right h hpos.le
    _ = ‖G'σ z (x - z) - G'τ z (y - z)‖ * r := by rw [← hsr]; ring

/-- Local lower bound for a pair of closed simplices, in ambient coordinates. Let `Gσ` and `Gτ` be
maps with continuous derivatives within the closed simplices on `σ` and on `τ`, which agree on
their intersection together with their derivatives along it. If at every common point `b` the
differential is injective on the union of the two simplices, then `Gσ x` and `Gτ y` are uniformly
separated for nearby `x` and `y`. -/
private theorem exists_pos_mul_norm_sub_le {σ τ : Finset ι} {Gσ Gτ : (ι → ℝ) → E}
    {G'σ G'τ : (ι → ℝ) → (ι → ℝ) →L[ℝ] E}
    (hGσ : ∀ w ∈ coordSimplex σ, HasFDerivWithinAt Gσ (G'σ w) (coordSimplex σ) w)
    (hG'σ : ContinuousOn G'σ (coordSimplex σ))
    (hGτ : ∀ w ∈ coordSimplex τ, HasFDerivWithinAt Gτ (G'τ w) (coordSimplex τ) w)
    (hG'τ : ContinuousOn G'τ (coordSimplex τ))
    (heq : ∀ w ∈ coordSimplex σ ∩ coordSimplex τ, Gσ w = Gτ w)
    (hagree : ∀ b ∈ coordSimplex σ ∩ coordSimplex τ, ∀ w ∈ coordSimplex σ ∩ coordSimplex τ,
      G'σ b (w - b) = G'τ b (w - b))
    (hstar : ∀ b ∈ coordSimplex σ ∩ coordSimplex τ, ∀ x ∈ coordSimplex σ, ∀ y ∈ coordSimplex τ,
      G'σ b (x - b) = G'τ b (y - b) → x = y) :
    ∃ c > 0, ∃ δ > 0, ∀ x ∈ coordSimplex σ, ∀ y ∈ coordSimplex τ, ‖x - y‖ < δ →
      c * ‖x - y‖ ≤ ‖Gσ x - Gτ y‖ := by
  set N : ℝ := (Fintype.card ι : ℝ)
  obtain ⟨c, hc, hdiff⟩ := exists_pos_mul_norm_sub_le_differential hG'σ hG'τ hagree hstar
  -- First-order errors of size at most `c / 2` times the distance of the pair.
  set ε : ℝ := c / (2 * (2 * N + 1))
  have hε : 0 < ε := by positivity
  obtain ⟨δσ, hδσ, hTσ⟩ := IsCompact.exists_pos_forall_norm_image_sub_sub_le
    isCompact_coordSimplex convex_coordSimplex hGσ hG'σ hε
  obtain ⟨δτ, hδτ, hTτ⟩ := IsCompact.exists_pos_forall_norm_image_sub_sub_le
    isCompact_coordSimplex convex_coordSimplex hGτ hG'τ hε
  refine ⟨c / 2, by positivity, min (N + 1)⁻¹ (min δσ δτ / (N + 1)), by positivity,
    fun x hx y hy hxy => ?_⟩
  have hnorm : 0 ≤ ‖x - y‖ := norm_nonneg _
  have hxyN : N * ‖x - y‖ < 1 := by
    have h := (mul_lt_mul_of_pos_left (lt_min_iff.1 hxy).1 (by positivity : (0 : ℝ) < N + 1))
    rw [mul_inv_cancel₀ (by positivity)] at h
    nlinarith
  have hxyδ : (N + 1) * ‖x - y‖ < min δσ δτ := by
    have h := (lt_min_iff.1 hxy).2
    rwa [lt_div_iff₀ (by positivity), mul_comm] at h
  obtain ⟨z, hz, hyz, hxz, hlin⟩ := hdiff x hx y hy hxyN
  -- Compare `Gσ` and `Gτ` with their differentials at the common point `z`.
  have h1 := hTσ z hz.1 x hx (hxz.trans_lt (hxyδ.trans_le (min_le_left _ _)))
  have h2 := hTτ z hz.2 y hy (hyz.trans_lt (by nlinarith [min_le_right δσ δτ]))
  have hdecomp : G'σ z (x - z) - G'τ z (y - z) = (Gσ x - Gτ y) -
      (Gσ x - Gσ z - G'σ z (x - z)) + (Gτ y - Gτ z - G'τ z (y - z)) := by
    rw [heq z hz]
    abel
  have hΦ : ‖G'σ z (x - z) - G'τ z (y - z)‖ ≤ ‖Gσ x - Gτ y‖ +
      ‖Gσ x - Gσ z - G'σ z (x - z)‖ + ‖Gτ y - Gτ z - G'τ z (y - z)‖ := by
    rw [hdecomp]
    exact (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
  have herr : ε * ‖x - z‖ + ε * ‖y - z‖ ≤ c / 2 * ‖x - y‖ := by
    have h2N : 2 * N + 1 ≠ 0 := by positivity
    have h : ε * (2 * N + 1) = c / 2 := by
      simp only [ε]
      field_simp
    nlinarith
  linarith

end Coordinates

namespace IsStarImmersion

variable {f : Realization K → E}

/-- A star immersion is an immersion on every closed simplex. -/
theorem isSimplexImmersion (h : IsStarImmersion n f) (σ : Face K) :
    IsSimplexImmersion 𝓘(ℝ, E) n (f ∘ faceInclusion K σ) :=
  h.1 σ

/-- A star immersion of class `Cⁿ` is one of every lower class `Cᵐ`. -/
theorem of_le {m : WithTop ℕ∞} (h : IsStarImmersion n f) (hmn : m ≤ n) : IsStarImmersion m f :=
  ⟨fun σ => (h.1 σ).of_le hmn, h.2⟩

/-- A star immersion is continuous. -/
theorem continuous (h : IsStarImmersion n f) : Continuous f :=
  continuous_iff_faceInclusion.2 fun σ => (h.1 σ).continuous

/-- Points of two closed simplices with the same coordinates are the same point. -/
private theorem faceInclusion_eq {σ τ : Face K} {p : StandardSimplex σ.1}
    {q : StandardSimplex τ.1} (hpq : (p.1 : ι → ℝ) = q.1) :
    faceInclusion K σ p = faceInclusion K τ q :=
  Subtype.ext <| by rw [faceInclusion_val, faceInclusion_val]; exact DFunLike.coe_injective hpq

section Finite

variable [Fintype ι]

private theorem mem_coordSimplex (σ : Face K) (x : StandardSimplex σ.1) :
    (x.1 : ι → ℝ) ∈ coordSimplex σ.1 := by
  rw [← range_standardSimplex_coe]
  exact ⟨x, rfl⟩

private theorem exists_eq_of_mem_coordSimplex (σ : Face K) {w : ι → ℝ}
    (hw : w ∈ coordSimplex σ.1) : ∃ x : StandardSimplex σ.1, (x.1 : ι → ℝ) = w := by
  rw [← range_standardSimplex_coe] at hw
  exact hw

/-- Distances in the coordinate image of `|K|` are distances of barycentric coordinates. -/
private theorem dist_eq_norm_realizationHomeomorphRange_symm
    (p q : range fun x : Realization K => (x.1 : ι → ℝ)) :
    dist p q = ‖(((K.realizationHomeomorphRange (Set.toFinite K.faces)).symm p).1 : ι → ℝ) -
      ((K.realizationHomeomorphRange (Set.toFinite K.faces)).symm q).1‖ := by
  rw [Subtype.dist_eq, dist_eq_norm, coe_realizationHomeomorphRange_symm_apply,
    coe_realizationHomeomorphRange_symm_apply]

/-- The hypotheses of `exists_pos_mul_norm_sub_le` for coordinate extensions of a star immersion
on two closed simplices: the extensions agree on the common face, so do their derivatives along
it, and their differentials at common points are jointly injective. -/
private theorem pair_conditions (h : IsStarImmersion n f) {G : Face K → (ι → ℝ) → E}
    {G' : Face K → (ι → ℝ) → (ι → ℝ) →L[ℝ] E}
    (hGf : ∀ σ (x : StandardSimplex σ.1), G σ x.1 = (f ∘ faceInclusion K σ) x)
    (hGd : ∀ σ, ∀ w ∈ coordSimplex σ.1, HasFDerivWithinAt (G σ) (G' σ w) (coordSimplex σ.1) w)
    (σ τ : Face K) :
    (∀ w ∈ coordSimplex σ.1 ∩ coordSimplex τ.1, G σ w = G τ w) ∧
    (∀ b ∈ coordSimplex σ.1 ∩ coordSimplex τ.1, ∀ w ∈ coordSimplex σ.1 ∩ coordSimplex τ.1,
      G' σ b (w - b) = G' τ b (w - b)) ∧
    ∀ b ∈ coordSimplex σ.1 ∩ coordSimplex τ.1, ∀ x ∈ coordSimplex σ.1, ∀ y ∈ coordSimplex τ.1,
      G' σ b (x - b) = G' τ b (y - b) → x = y := by
  have hseg (σ : Face K) (b x : StandardSimplex σ.1) :=
    hasDerivWithinAt_lineMap (hGf σ) (hGd σ) b x
  refine ⟨?_, ?_, ?_⟩
  · rintro w ⟨hwσ, hwτ⟩
    obtain ⟨p, rfl⟩ := exists_eq_of_mem_coordSimplex σ hwσ
    obtain ⟨q, hq⟩ := exists_eq_of_mem_coordSimplex τ hwτ
    rw [hGf σ p, ← hq, hGf τ q, comp_apply, comp_apply, faceInclusion_eq hq.symm]
  · -- Both are the derivative of `f` along the segment from `b` to `w` in the common face.
    rintro b ⟨hbσ, hbτ⟩ w ⟨hwσ, hwτ⟩
    obtain ⟨pb, rfl⟩ := exists_eq_of_mem_coordSimplex σ hbσ
    obtain ⟨pw, rfl⟩ := exists_eq_of_mem_coordSimplex σ hwσ
    obtain ⟨qb, hqb⟩ := exists_eq_of_mem_coordSimplex τ hbτ
    obtain ⟨qw, hqw⟩ := exists_eq_of_mem_coordSimplex τ hwτ
    have h₂ := hseg τ qb qw
    have hfun : IccExtend zero_le_one ((f ∘ faceInclusion K σ) ∘ StandardSimplex.lineMap pb pw) =
        IccExtend zero_le_one ((f ∘ faceInclusion K τ) ∘ StandardSimplex.lineMap qb qw) := by
      congr 1
      funext t
      simp only [comp_apply]
      congr 1
      refine faceInclusion_eq ?_
      rw [StandardSimplex.coe_lineMap, StandardSimplex.coe_lineMap, DFunLike.coe_injective hqb,
        DFunLike.coe_injective hqw]
    rw [hqb, hqw, ← hfun] at h₂
    exact (uniqueDiffOn_Icc_zero_one 0 (left_mem_Icc.2 zero_le_one)).eq_deriv _
      (hseg σ pb pw) h₂
  · -- This is the star condition at `b`.
    rintro b ⟨hbσ, hbτ⟩ x hx y hy hxy
    obtain ⟨pb, rfl⟩ := exists_eq_of_mem_coordSimplex σ hbσ
    obtain ⟨px, rfl⟩ := exists_eq_of_mem_coordSimplex σ hx
    obtain ⟨qb, hqb⟩ := exists_eq_of_mem_coordSimplex τ hbτ
    obtain ⟨qy, rfl⟩ := exists_eq_of_mem_coordSimplex τ hy
    have h₂ := hseg τ qb qy
    rw [hqb, ← hxy] at h₂
    exact congrArg _ (h.2 σ τ pb px qb qy _ (DFunLike.coe_injective hqb.symm) (hseg σ pb px) h₂)

/-- A `C¹` star immersion of a complex on a finite vertex type separates nearby points uniformly,
in barycentric coordinates. -/
private theorem exists_pos_mul_norm_sub_le_norm_sub (h : IsStarImmersion n f) (hn : 1 ≤ n) :
    ∃ c > 0, ∃ δ > 0, ∀ x y : Realization K, ‖(x.1 : ι → ℝ) - y.1‖ < δ →
      c * ‖(x.1 : ι → ℝ) - y.1‖ ≤ ‖f x - f y‖ := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨1, one_pos, 1, one_pos, fun x => absurd (Realization.sum_eq_one K x) ?_⟩
    rw [Subsingleton.elim x.1 0, Finsupp.sum_zero_index]
    exact zero_ne_one
  choose G G' hGf hGd hGc using fun σ : Face K => exists_coord (h.1 σ) hn
  -- Uniform local bounds for each of the finitely many pairs of faces.
  choose c hc δ hδ hpair using fun p : Face K × Face K =>
    have hp := pair_conditions h hGf hGd p.1 p.2
    exists_pos_mul_norm_sub_le (hGd p.1) (hGc p.1) (hGd p.2) (hGc p.2) hp.1 hp.2.1 hp.2.2
  have : Nonempty (Face K × Face K) :=
    ⟨(⟨{hι.some}, K.singleton_mem _⟩, ⟨{hι.some}, K.singleton_mem _⟩)⟩
  obtain ⟨p₀, hp₀⟩ := Finite.exists_min c
  obtain ⟨p₁, hp₁⟩ := Finite.exists_min δ
  -- Read every point in the closed simplex spanned by its carrier.
  have hcarrier (x : Realization K) : f x = G (carrier K x) (x.1 : ι → ℝ) := by
    rw [hGf (carrier K x) ⟨x.1, mem_convexHull_carrier K x⟩, comp_apply]
    exact congrArg f (Subtype.ext
      (faceInclusion_val K (carrier K x) ⟨x.1, mem_convexHull_carrier K x⟩).symm)
  refine ⟨c p₀, hc p₀, δ p₁, hδ p₁, fun x y hxy => ?_⟩
  rw [hcarrier x, hcarrier y]
  exact (mul_le_mul_of_nonneg_right (hp₀ (carrier K x, carrier K y)) (norm_nonneg _)).trans
    (hpair (carrier K x, carrier K y) _ (mem_coordSimplex _ ⟨x.1, mem_convexHull_carrier K x⟩) _
      (mem_coordSimplex _ ⟨y.1, mem_convexHull_carrier K y⟩) (hxy.trans_le (hp₁ _)))

/-- **Injective star immersions of finite complexes are antilipschitz.** Let `f` be a `Cⁿ` star
immersion, `1 ≤ n`, of the realization of a complex on a finite vertex type into a normed space.
If `f` is injective, it is antilipschitz in barycentric coordinates: there is `C > 0` with
`‖x - y‖ ≤ C * ‖f x - f y‖` for all points `x` and `y`, including points of different simplices
and points close to a common face. -/
theorem exists_antilipschitzWith (h : IsStarImmersion n f) (hn : 1 ≤ n) (hf : Injective f) :
    ∃ C > 0,
      AntilipschitzWith C (f ∘ (K.realizationHomeomorphRange (Set.toFinite K.faces)).symm) := by
  set e := K.realizationHomeomorphRange (Set.toFinite K.faces)
  obtain ⟨c, hc, δ, hδ, hlocal⟩ := exists_pos_mul_norm_sub_le_norm_sub h hn
  let : CompactSpace (range fun x : Realization K => (x.1 : ι → ℝ)) := e.compactSpace
  obtain ⟨C, hC, hanti⟩ := isCompact_univ.exists_antilipschitzWith_of_locally
    (h.continuous.comp e.symm.continuous).continuousOn ((hf.comp e.symm.injective).injOn) hc hδ
    fun p _ q _ hpq => by
      rw [dist_eq_norm_realizationHomeomorphRange_symm] at hpq ⊢
      rw [comp_apply, comp_apply, dist_eq_norm]
      exact hlocal _ _ hpq
  exact ⟨C, hC, fun p q => hanti ⟨p, mem_univ p⟩ ⟨q, mem_univ q⟩⟩


/-! ### Secant maps on fine edgewise subdivisions -/

section Secant

open Filter _root_.PreAbstractSimplicialComplex

variable [LinearOrder ι]

/-- **Secant maps of embeddings are uniformly antilipschitz.** Let `f` be an injective `Cⁿ` star
immersion, `1 ≤ n`, of a complex on a finite vertex type into a normed space. There is a constant
`C` such that for all sufficiently large `k`, the secant map of `f` on the `k`-th edgewise
subdivision satisfies `‖x - y‖ ≤ C * ‖s x - s y‖` for all points `x` and `y` of the subdivision,
where `‖x - y‖` is the distance of their images in the barycentric coordinates of `|K|`. The
constant does not depend on `k`. -/
theorem exists_pos_eventually_norm_sub_le_mul_norm_secantMap_sub (h : IsStarImmersion n f)
    (hn : 1 ≤ n) (hf : Injective f) :
    ∃ C > 0, ∀ᶠ k in atTop, ∀ x y : Realization (K.edgewiseSubdivision k),
      ‖((edgewiseSubdivisionRealizationMap K k x).1 : ι → ℝ) -
          (edgewiseSubdivisionRealizationMap K k y).1‖ ≤
        C * ‖(K.edgewiseSubdivision k).secantMap (f ∘ edgewiseSubdivisionRealizationMap K k) x -
          (K.edgewiseSubdivision k).secantMap (f ∘ edgewiseSubdivisionRealizationMap K k) y‖ := by
  set e := K.realizationHomeomorphRange (Set.toFinite K.faces)
  obtain ⟨C, hC, hanti⟩ := h.exists_antilipschitzWith hn hf
  have hlt : (2 * C)⁻¹ < C⁻¹ := inv_strictAnti₀ hC (lt_two_mul_self hC)
  refine ⟨((C⁻¹ - (2 * C)⁻¹)⁻¹ : NNReal), NNReal.coe_pos.2 (inv_pos.2 (tsub_pos_of_lt hlt)), ?_⟩
  -- On every closed simplex, `f` is the restriction of a `C¹` map in barycentric coordinates.
  have hC1 (σ : Face K) : ∃ F : (σ.1 → ℝ) → E,
      (∀ x : StandardSimplex σ.1, F (fun a => x.1 a) = f (faceInclusion K σ x)) ∧
        ContDiffOn ℝ 1 F (range fun t : Convexity.StdSimplex ℝ σ.1 => ⇑t.weights) := by
    obtain ⟨F, hFg, hF, -⟩ := isSimplexImmersion_iff.mp (h.1 σ)
    exact ⟨F, hFg, (contMDiffOn_iff_contDiffOn.mp hF).of_le hn⟩
  filter_upwards [eventually_ne_atTop 0, eventually_norm_secantMap_sub_sub_le_edgewiseSubdivision
    hC1 (ε := ((2 * C)⁻¹ : NNReal)) (NNReal.coe_pos.2 (inv_pos.2 (by positivity)))]
    with k hk0 hk x y
  -- Move the secant map to the coordinate image of `|K|` and perturb `f` there.
  set Ψ := (edgewiseSubdivisionRealizationHomeomorph K hk0).trans e
  set s := (K.edgewiseSubdivision k).secantMap (f ∘ edgewiseSubdivisionRealizationMap K k)
  have hΨ (x : Realization (K.edgewiseSubdivision k)) :
      e.symm (Ψ x) = edgewiseSubdivisionRealizationMap K k x := by
    rw [Homeomorph.trans_apply, e.symm_apply_apply, edgewiseSubdivisionRealizationHomeomorph_apply]
  have hdist (x y : Realization (K.edgewiseSubdivision k)) : dist (Ψ x) (Ψ y) =
      ‖((edgewiseSubdivisionRealizationMap K k x).1 : ι → ℝ) -
        (edgewiseSubdivisionRealizationMap K k y).1‖ := by
    rw [dist_eq_norm_realizationHomeomorphRange_symm, hΨ, hΨ]
  have hlip : LipschitzWith (2 * C)⁻¹ (s ∘ Ψ.symm - f ∘ e.symm) :=
    LipschitzWith.of_dist_le_mul fun p q => by
      obtain ⟨x, rfl⟩ := Ψ.surjective p
      obtain ⟨y, rfl⟩ := Ψ.surjective q
      simpa only [hdist, dist_eq_norm, Pi.sub_apply, comp_apply, Homeomorph.symm_apply_apply,
        hΨ] using hk x y
  simpa only [hdist, dist_eq_norm, comp_apply, Homeomorph.symm_apply_apply] using
    (hanti.add_sub_lipschitzWith hlip hlt).le_mul_dist (Ψ x) (Ψ y)

omit [Fintype ι] in
/-- **Secant maps of embeddings are embeddings.** Let `f` be an injective `Cⁿ` star immersion,
`1 ≤ n`, of a complex on a finite vertex type into a normed space. For all sufficiently large
`k`, the secant map of `f` on the `k`-th edgewise subdivision, the map which agrees with `f` at
the points `edgewisePoint u` and is linear on every simplex of the subdivision, is a closed
embedding. -/
theorem eventually_isClosedEmbedding_secantMap_edgewiseSubdivision [Finite ι]
    (h : IsStarImmersion n f) (hn : 1 ≤ n) (hf : Injective f) :
    ∀ᶠ k in atTop, Topology.IsClosedEmbedding
      ((K.edgewiseSubdivision k).secantMap (f ∘ edgewiseSubdivisionRealizationMap K k)) := by
  have := Fintype.ofFinite ι
  obtain ⟨C, -, hC⟩ := h.exists_pos_eventually_norm_sub_le_mul_norm_secantMap_sub hn hf
  filter_upwards [hC, eventually_ne_atTop 0] with k hk hk0
  have : CompactSpace (Realization K) := K.compactSpace_realization_of_finite_faces
    (Set.toFinite K.faces)
  have : CompactSpace (Realization (K.edgewiseSubdivision k)) :=
    (edgewiseSubdivisionRealizationHomeomorph K hk0).symm.compactSpace
  refine (continuous_secantMap _).isClosedEmbedding fun x y hxy => ?_
  have hle := hk x y
  rw [hxy, sub_self, norm_zero, mul_zero] at hle
  exact edgewiseSubdivisionRealizationMap_injective
    (Subtype.ext (DFunLike.coe_injective (sub_eq_zero.mp (norm_le_zero_iff.mp hle))))

end Secant

end Finite

end IsStarImmersion

end TauCeti

namespace AbstractSimplicialComplex

open TauCeti

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : AbstractSimplicialComplex ι} {n : WithTop ℕ∞}

/-- An injective secant map is a star immersion of every class `Cⁿ`: it is linear in barycentric
coordinates on every closed simplex, and its differential at `b` sends `x` to `g x - g b`. -/
theorem isStarImmersion_secantMap {f : Realization K → E} (hinj : Injective (K.secantMap f)) :
    IsStarImmersion n (K.secantMap f) := by
  set g := K.secantMap f with hgdef
  have hg (σ : Face K) (x : StandardSimplex σ.1) : g (faceInclusion K σ x) =
      Fintype.linearCombination ℝ (fun a : σ.1 => f (vertex K a)) (fun a => x.1 a) := by
    rw [hgdef, secantMap_faceInclusion, Fintype.linearCombination_apply]
  have hincl {σ τ : Face K} {x : StandardSimplex σ.1} {y : StandardSimplex τ.1}
      (h : g (faceInclusion K σ x) = g (faceInclusion K τ y)) : (x : ι →₀ ℝ) = y := by
    simpa only [faceInclusion_val] using congrArg Subtype.val (hinj h)
  refine ⟨fun σ => ?_, fun σ τ b x b' y u hb hx hy => ?_⟩
  · exact isSimplexImmersion_secantMap_comp_faceInclusion_of_injOn hinj.injOn
  · -- Along a segment in a closed simplex `g` is affine, so its differential at `b` is
    -- `x ↦ g x - g b`.
    have hseg (σ : Face K) (b x : StandardSimplex σ.1) :
        HasDerivWithinAt (IccExtend zero_le_one (g ∘ faceInclusion K σ ∘
          StandardSimplex.lineMap b x))
          (g (faceInclusion K σ x) - g (faceInclusion K σ b)) (Icc 0 1) 0 := by
      refine (AffineMap.hasDerivWithinAt_lineMap (𝕜 := ℝ)).congr_of_mem (fun t ht => ?_)
        (left_mem_Icc.2 zero_le_one)
      rw [IccExtend_of_mem _ _ ht, comp_apply, comp_apply, hg, hg, hg,
        AffineMap.lineMap_apply_module, ← map_smul, ← map_smul, ← map_add]
      congr 1
      funext a
      simp [StandardSimplex.coe_lineMap, AffineMap.lineMap_apply_module]
    have hu := (uniqueDiffOn_Icc_zero_one 0 (left_mem_Icc.2 zero_le_one)).eq_deriv _ hx
      (hseg σ b x)
    have hu' := (uniqueDiffOn_Icc_zero_one 0 (left_mem_Icc.2 zero_le_one)).eq_deriv _ hy
      (hseg τ b' y)
    have hbb : faceInclusion K σ b = faceInclusion K τ b' :=
      Subtype.ext (by rw [faceInclusion_val, faceInclusion_val, hb])
    rw [hbb] at hu
    exact hincl (sub_left_injective (hu.symm.trans hu'))

end AbstractSimplicialComplex
