/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import TauCeti.Geometry.Manifold.CoordinateBall
import TauCeti.Geometry.Manifold.Morse.Deformation

/-!
# Smooth functions with two critical points

Let `M` be a compact boundaryless manifold modelled on `E`, and let `f : M → ℝ` be a smooth
function with exactly two critical points, which may be degenerate. Then `M` is covered by two
open sets, each homeomorphic to `E`
(`TauCeti.exists_twoEuclideanOpenCover_of_two_criticalPoints`). This is the hypothesis of the
two-open-cell lemma of Milnor and Rosen, by which such an `M` is homeomorphic to a sphere; unlike
Reeb's theorem for Morse functions, no normal form at the critical points is used.

When `f` is not constant, the two critical points are its unique minimum point `p`, at value `a`,
and its unique maximum point `q`, at value `b > a`. Given neighbourhoods `B` of `p` and `V` of `q`,
a whole sublevel `{f ≤ a + ε}` lies in `B`, since `p` is the only point with value `a`, and the
compact set `M \ V` lies in a sublevel `{f ≤ b - δ}`, since `q` is the only point with value `b`.
The band `f⁻¹[a + ε, b - δ]` contains no critical point, so a diffeomorphism `Φ` of `M` carries
`{f ≤ b - δ}` onto `{f ≤ a + ε}` (`TauCeti.exists_diffeomorph_sublevel`, built from a flow lowering
`f` across the band), and hence `M \ V` into `B` (`TauCeti.exists_diffeomorph_mapsTo_compl`).
Taking for `B` and `V` coordinate balls, homeomorphic to `E`, the open set `Φ⁻¹(B)` is
homeomorphic to `E` and contains `M \ V`. When `f` is constant every point is critical, so `M`
consists of the two critical points, and coordinate balls about them are the two open sets.

## Main results

* `TauCeti.exists_diffeomorph_mapsTo_compl`: if the only critical points of `f` are `p` and `q`,
  with `f p < f q`, a diffeomorphism of `M` carries the complement of any neighbourhood of `q`
  into any neighbourhood of `p`.
* `TauCeti.exists_twoEuclideanOpenCover_of_two_criticalPoints`: a compact boundaryless manifold
  carrying a smooth function with exactly two critical points is the union of two open sets
  homeomorphic to its model space.

## References

* J. Milnor, *Sommes de variétés différentiables et structures différentiables des sphères*,
  Bull. Soc. Math. France 87 (1959), Theorem 1 (3) and Corollary 1 (p. 442).
* R. H. Rosen, *A weak form of the star conjecture for manifolds*, Notices Amer. Math. Soc. 7
  (1960), abstract 570-28, p. 380, Lemma 1.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.1 and the remark following Theorem 4.1.
-/

public section

open Set Filter Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
  {f : M → ℝ}

/-- **Pushing a manifold into a neighbourhood of the minimum.** Let `f` be a smooth function on a
compact boundaryless manifold `M` whose only critical points are `p` and `q`, with `f p < f q`.
Then for every neighbourhood `B` of `p` and `V` of `q`, some diffeomorphism of `M` carries the
complement of `V` into `B`. -/
theorem exists_diffeomorph_mapsTo_compl (hf : ContMDiff I 𝓘(ℝ) ∞ f) {p q : M}
    (hcrit : criticalPoints I f ⊆ {p, q}) (hpq : f p < f q) {B V : Set M} (hB : B ∈ 𝓝 p)
    (hV : V ∈ 𝓝 q) : ∃ Φ : M ≃ₘ⟮I, I⟯ M, MapsTo Φ Vᶜ B := by
  have hfc : Continuous f := hf.continuous
  have hcrit' {y : M} (hy : y ∈ criticalPoints I f) : y = p ∨ y = q := by simpa using hcrit hy
  -- The extrema are critical points, so `p` is the minimum and `q` the maximum, and they are the
  -- only points with these values.
  have hp : IsMinOn f univ p := by
    obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn ⟨p, mem_univ p⟩ hfc.continuousOn
    obtain rfl | rfl := hcrit' (hx₀.isLocalMin univ_mem).mem_criticalPoints
    · exact hx₀
    · exact absurd (hx₀ (mem_univ p)) hpq.not_ge
  have hq : IsMaxOn f univ q := by
    obtain ⟨x₁, -, hx₁⟩ := isCompact_univ.exists_isMaxOn ⟨p, mem_univ p⟩ hfc.continuousOn
    obtain rfl | rfl := hcrit' (hx₁.isLocalMax univ_mem).mem_criticalPoints
    · exact absurd (hx₁ (mem_univ q)) hpq.not_ge
    · exact hx₁
  have hmin (y : M) (hy : f y = f p) : y = p := by
    have hy' : IsMinOn f univ y := isMinOn_univ_iff.2 fun z ↦ hy ▸ hp (mem_univ z)
    exact (hcrit' (hy'.isLocalMin univ_mem).mem_criticalPoints).resolve_right
      fun h ↦ hpq.ne (h ▸ hy).symm
  have hmax (y : M) (hy : f y = f q) : y = q := by
    have hy' : IsMaxOn f univ y := isMaxOn_univ_iff.2 fun z ↦ hy ▸ hq (mem_univ z)
    exact (hcrit' (hy'.isLocalMax univ_mem).mem_criticalPoints).resolve_left
      fun h ↦ hpq.ne (h ▸ hy)
  -- Off the interior of `B` the function stays above a level `c₀ > f p`; choose `c₁` between
  -- `f p` and `min c₀ (f q)`, so that `{f ≤ c₁}` lies in the interior of `B`.
  obtain ⟨c₀, hc₀, hc₀B⟩ := isOpen_interior.isClosed_compl.isCompact.exists_forall_le'
    hfc.continuousOn fun y hy ↦ (hp (mem_univ y)).lt_of_ne fun h ↦
      hy (hmin y h.symm ▸ mem_interior_iff_mem_nhds.2 hB)
  obtain ⟨c₁, hc₁, hc₁'⟩ := exists_between (lt_min hc₀ hpq)
  have hc₁₀ : c₁ < c₀ := hc₁'.trans_le (min_le_left _ _)
  have hc₁₁ : c₁ < f q := hc₁'.trans_le (min_le_right _ _)
  -- Off the interior of `V` the function stays below a level `-d₀ < f q`.
  obtain ⟨d₀, hd₀, hd₀V⟩ := isOpen_interior.isClosed_compl.isCompact.exists_forall_le'
    hfc.neg.continuousOn fun y hy ↦ neg_lt_neg <| (hq (mem_univ y)).lt_of_ne fun h ↦
      hy (hmax y h ▸ mem_interior_iff_mem_nhds.2 hV)
  have hd₀' : -d₀ < f q := by simpa [neg_lt] using hd₀
  -- The band `f⁻¹[c₁, max c₁ (-d₀)]` is compact and free of critical points, so a
  -- diffeomorphism carries the sublevel `{f ≤ max c₁ (-d₀)}` onto `{f ≤ c₁}`.
  have hreg (x : M) (h₁ : c₁ ≤ f x) (h₂ : f x ≤ max c₁ (-d₀)) : mfderiv I 𝓘(ℝ) f x ≠ 0 :=
    fun h0 ↦ by
      have := max_lt hc₁₁ hd₀'
      rcases hcrit' (mem_criticalPoints_iff_mfderiv_eq_zero.2 h0) with rfl | rfl <;> linarith
  obtain ⟨Φ, hΦ⟩ := exists_diffeomorph_sublevel hf (le_max_left _ _)
    (isClosed_Icc.preimage hfc).isCompact hreg
  refine ⟨Φ, fun x hx ↦ interior_subset (not_not.1 fun hΦx ↦ ?_)⟩
  have hfx : f x ≤ -d₀ := le_neg.2 (hd₀V x fun h ↦ hx (interior_subset h))
  linarith [hc₀B _ hΦx, (hΦ x).1.2 (le_max_of_le_right hfx)]

/-- **Two critical points give a cover by two Euclidean open sets.** If a smooth function on a
compact boundaryless manifold `M` modelled on `E` has exactly two critical points, degenerate or
not, then `M` is the union of two open sets, each homeomorphic to `E`. -/
theorem exists_twoEuclideanOpenCover_of_two_criticalPoints (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (h2 : totalCriticalCount I f = 2) :
    ∃ U V : Set M, IsOpen U ∧ IsOpen V ∧ U ∪ V = univ ∧
      Nonempty (U ≃ₜ E) ∧ Nonempty (V ≃ₜ E) := by
  -- It suffices to find open sets `B` and `V` homeomorphic to `E` and a homeomorphism of `M`
  -- carrying the complement of `V` into `B`; then `U` is the preimage of `B`.
  suffices ∃ B V : Set M, IsOpen B ∧ IsOpen V ∧ Nonempty (B ≃ₜ E) ∧ Nonempty (V ≃ₜ E) ∧
      ∃ Φ : M ≃ₜ M, MapsTo Φ Vᶜ B by
    obtain ⟨B, V, hB, hV, ⟨eB⟩, hVE, Φ, hΦ⟩ := this
    exact ⟨Φ ⁻¹' B, V, hB.preimage Φ.continuous, hV,
      eq_univ_of_forall fun x ↦ (em (x ∈ V)).elim .inr fun hx ↦ .inl (hΦ hx),
      ⟨(Φ.sets rfl).trans eB⟩, hVE⟩
  obtain ⟨p, q, hpq, hcrit⟩ := encard_eq_two.1 ((totalCriticalCount_def (I := I)).symm.trans h2)
  wlog h : f p ≤ f q generalizing p q
  · exact this q p hpq.symm (by rw [hcrit, pair_comm]) (le_of_not_ge h)
  -- Coordinate balls about `p` and `q`, which are homeomorphic to `E`.
  obtain ⟨eB, heB0, heB, -⟩ := exists_isOpenEmbedding_range_subset I (univ_mem : univ ∈ 𝓝 p)
  obtain ⟨eV, heV0, heV, -⟩ := exists_isOpenEmbedding_range_subset I (univ_mem : univ ∈ 𝓝 q)
  have hpB : p ∈ range eB := ⟨0, heB0⟩
  have hqV : q ∈ range eV := ⟨0, heV0⟩
  refine ⟨range eB, range eV, heB.isOpen_range, heV.isOpen_range,
    ⟨heB.toIsEmbedding.toHomeomorph.symm⟩, ⟨heV.toIsEmbedding.toHomeomorph.symm⟩, ?_⟩
  rcases h.lt_or_eq with hlt | heq
  · -- The flow carries the complement of the ball about the maximum `q` into the ball about the
    -- minimum `p`.
    obtain ⟨Φ, hΦ⟩ := exists_diffeomorph_mapsTo_compl hf hcrit.subset hlt
      (heB.isOpen_range.mem_nhds hpB) (heV.isOpen_range.mem_nhds hqV)
    exact ⟨Φ.toHomeomorph, by rwa [Diffeomorph.coe_toHomeomorph]⟩
  -- If `f p = f q`, the extreme values agree, `f` is constant and every point is critical, so
  -- `M = {p, q}` and every point outside the ball about `q` is `p`.
  have hval {x : M} (hx : x ∈ criticalPoints I f) : f x = f p := by
    obtain rfl | rfl : x = p ∨ x = q := by simpa [hcrit] using hx
    exacts [rfl, heq.symm]
  have hfc : Continuous f := hf.continuous
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn ⟨p, mem_univ p⟩ hfc.continuousOn
  obtain ⟨x₁, -, hx₁⟩ := isCompact_univ.exists_isMaxOn ⟨p, mem_univ p⟩ hfc.continuousOn
  have hall (x : M) : x = p ∨ x = q := by
    have hmin : IsLocalMin f x := .of_forall fun y ↦ by
      have h₀ : f x₀ ≤ f y := hx₀ (mem_univ y)
      have h₁ : f x ≤ f x₁ := hx₁ (mem_univ x)
      linarith [hval (hx₀.isLocalMin univ_mem).mem_criticalPoints,
        hval (hx₁.isLocalMax univ_mem).mem_criticalPoints]
    simpa [hcrit] using hmin.mem_criticalPoints (I := I)
  refine ⟨.refl M, fun x hx ↦ ?_⟩
  obtain rfl | rfl := hall x
  exacts [hpB, absurd hqV hx]

end TauCeti
