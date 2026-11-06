/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import TauCeti.Geometry.Manifold.ContMDiff.Parametrization
import TauCeti.Geometry.Manifold.Morse.Deformation

/-!
# Functions with exactly two critical points: a cover by two Euclidean open sets

Let `f` be a smooth real function on a compact boundaryless manifold `M` modelled on a real
vector space of dimension `m`, with exactly two critical points. The critical points may be
arbitrarily degenerate. Then `M` is the union of two open subsets, each homeomorphic to `ℝᵐ`
(`TauCeti.exists_twoEuclideanOpenCover_of_two_criticalPoints`).

If `f` is constant, `M` consists of the two critical points. Otherwise the two critical points
are the global minimum `p` and the global maximum `q` of `f`, and every other point is regular.
Take coordinate balls `B` about `p` and `V` about `q`. Since `p` is the only point with value
`f p`, some whole sublevel `{f ≤ α}` with `α > f p` lies in `B`; since `q` is
the only point with value `f q`, the compact set `M \ V` lies in a sublevel `{f ≤ β}` with
`β < f q`. The band `f⁻¹[α, β]` is compact and free of critical points, so the descending flow
`φ` of `TauCeti.exists_flow_apply_eq_sub`, which lowers `f` at unit speed through that band and
never raises it, carries `M \ V` into `{f ≤ α} ⊆ B` at the single time `T = max 0 (β - α)`. Hence
`U = φ_T⁻¹(B)` together with `V` covers `M`, and `φ_T` identifies `U` with the ball `B`. No
Morse lemma or Hessian enters, so the argument applies to degenerate extrema.

This cover is the analytic input of the topological form of Reeb's theorem for functions with
two arbitrary critical points (Milnor, *Morse Theory*, Remark 1 after Theorem 4.1): a compact
Hausdorff space covered by two open sets homeomorphic to `ℝᵐ`, `m > 0`, is homeomorphic to the
sphere `Sᵐ`. For smooth manifolds covered by two open sets diffeomorphic to `ℝᵐ` this is
Milnor 1959, Corollary 1 of Theorem 1; the topological form rests on Brown's generalized
Schoenflies theorem.

## Main results

* `TauCeti.exists_twoEuclideanOpenCover_of_two_criticalPoints`: a compact boundaryless manifold
  carrying a smooth function with exactly two critical points is covered by two open sets
  homeomorphic to `ℝᵐ`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 4.1 and Remark 1.
* J. Milnor, *Sommes de variétés différentiables et structures différentiables des sphères*,
  Bull. Soc. Math. France 87 (1959), 439–444, Theorem 1 and Corollary 1.
* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76.
-/

public section

open Set Module Filter
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
  {f : M → ℝ}

/-- **Pushing the complement of a ball at the maximum into a ball at the minimum.** Let `f` be
smooth with minimum `x₀` and maximum `x₁`, `f x₀ < f x₁`, and no other critical points. For open
neighbourhoods `B` of `x₀` and `V` of `x₁`, a time-`T` map of the descending flow of
`TauCeti.exists_flow_apply_eq_sub` carries every point outside `V` into `B`. -/
private theorem exists_homeomorph_mapsTo_compl {x₀ x₁ : M} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hx₀ : IsMinOn f univ x₀) (hx₁ : IsMaxOn f univ x₁) (hlt : f x₀ < f x₁)
    (hcrit : ∀ x ∈ criticalPoints I f, x = x₀ ∨ x = x₁) {B V : Set M} (hB : IsOpen B)
    (hx₀B : x₀ ∈ B) (hV : IsOpen V) (hx₁V : x₁ ∈ V) :
    ∃ g : M ≃ₜ M, MapsTo g Vᶜ B := by
  have hfc : Continuous f := hf.continuous
  -- The minimum and the maximum are the only points with their values.
  have hmin (y : M) (hy : f y ≤ f x₀) : y = x₀ := by
    have hy' : IsMinOn f univ y := isMinOn_univ_iff.2 fun z ↦ hy.trans (hx₀ (mem_univ z))
    refine (hcrit y (hy'.isLocalMin univ_mem).mem_criticalPoints).resolve_right ?_
    rintro rfl
    linarith
  have hmax (y : M) (hy : f x₁ ≤ f y) : y = x₁ := by
    have hy' : IsMaxOn f univ y := isMaxOn_univ_iff.2 fun z ↦ (hx₁ (mem_univ z)).trans hy
    refine (hcrit y (hy'.isLocalMax univ_mem).mem_criticalPoints).resolve_left ?_
    rintro rfl
    linarith
  -- A sublevel `{f < α}` strictly above the minimum lies in `B`, and the complement of `V` lies in
  -- a sublevel `{f ≤ β}` strictly below the maximum.
  obtain ⟨α, hα, hαB⟩ := hB.isClosed_compl.isCompact.exists_forall_le' hfc.continuousOn
    fun x hx ↦ (hx₀ (mem_univ x)).lt_of_ne fun h ↦ hx (hmin x h.ge ▸ hx₀B)
  obtain ⟨β', hβ', hβV⟩ := hV.isClosed_compl.isCompact.exists_forall_le' hfc.neg.continuousOn
    fun x hx ↦ neg_lt_neg <| (hx₁ (mem_univ x)).lt_of_ne fun h ↦ hx (hmax x h.ge ▸ hx₁V)
  obtain ⟨β, rfl⟩ : ∃ β, β' = -β := ⟨-β', (neg_neg β').symm⟩
  have hβ : β < f x₁ := by linarith
  have hβV' (y : M) (hy : y ∉ V) : f y ≤ β := by
    have h := hβV y hy
    rw [Pi.neg_apply] at h
    linarith
  -- Shrink `α` so that the whole sublevel `{f ≤ α'}` lies in `B`.
  obtain ⟨α', hα'⟩ : ∃ α', α' = (f x₀ + α) / 2 := ⟨_, rfl⟩
  have hαB' (y : M) (hy : f y ≤ α') : y ∈ B :=
    by_contra fun h ↦ by linarith [hαB y h]
  -- The band `f⁻¹[α', β]` contains neither critical point.
  have hreg (x : M) (ha : α' ≤ f x) (hb : f x ≤ β) : mfderiv I 𝓘(ℝ) f x ≠ 0 := fun h0 ↦ by
    rcases hcrit x (mem_criticalPoints_iff_mfderiv_eq_zero.2 h0) with rfl | rfl <;> linarith
  obtain ⟨φ, -, hanti, -, hunit⟩ :=
    exists_flow_apply_eq_sub hf (isClosed_Icc.preimage hfc).isCompact hreg
  -- At time `T = β - α'` the flow carries the complement of `V` into `{f ≤ α'} ⊆ B`.
  refine ⟨φ.toHomeomorph (max 0 (β - α')), fun y hy ↦ hαB' _ ?_⟩
  rw [Flow.toHomeomorph_apply]
  rcases le_or_gt (f y) α' with h | h
  · calc f (φ (max 0 (β - α')) y) ≤ f (φ 0 y) := hanti y (le_max_left _ _)
      _ ≤ α' := by rwa [φ.map_zero_apply]
  · calc f (φ (max 0 (β - α')) y) ≤ f (φ (f y - α') y) :=
          hanti y (le_max_of_le_right (by linarith [hβV' y hy]))
      _ = α' := by rw [hunit y _ (by linarith) (by linarith) (hβV' y hy)]; ring

/-- **Two critical points give a cover by two Euclidean open sets.** If a smooth function `f` on
a compact boundaryless manifold `M`, modelled on a real vector space of dimension `m`, has
exactly two critical points, then `M` is the union of two open sets, each homeomorphic to `ℝᵐ`.
The critical points may be degenerate. -/
theorem exists_twoEuclideanOpenCover_of_two_criticalPoints (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (h2 : totalCriticalCount I f = 2) :
    ∃ U V : Set M, IsOpen U ∧ IsOpen V ∧ U ∪ V = univ ∧
      Nonempty (U ≃ₜ EuclideanSpace ℝ (Fin (finrank ℝ E))) ∧
      Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin (finrank ℝ E))) := by
  obtain ⟨p, q, -, hcrit⟩ := encard_eq_two.1 ((totalCriticalCount_def (I := I)).symm.trans h2)
  have hfc : Continuous f := hf.continuous
  -- Every point is the centre of a coordinate ball, read on the self-modelled copy of `M`.
  have hball (x : M) : ∃ B : Set M, IsOpen B ∧ x ∈ B ∧
      Nonempty (B ≃ₜ EuclideanSpace ℝ (Fin (finrank ℝ E))) := by
    set e := BoundarylessModel.homeomorph I M
    obtain ⟨c, hcs, hxc, -⟩ := exists_contMDiff_parametrization (E := E) (n := ⊤) (e x)
    have hc := e.symm.isOpenEmbedding.comp (c.isOpenEmbedding hcs)
    exact ⟨range (e.symm ∘ c), hc.isOpen_range, ⟨c.symm (e x), by simp [c.right_inv hxc]⟩,
      ⟨hc.isEmbedding.toHomeomorph.symm⟩⟩
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn ⟨p, mem_univ p⟩ hfc.continuousOn
  obtain ⟨x₁, -, hx₁⟩ := isCompact_univ.exists_isMaxOn ⟨p, mem_univ p⟩ hfc.continuousOn
  rcases (hx₀ (mem_univ x₁)).lt_or_eq with hlt | hconst
  · -- The critical points are the minimum `x₀` and the maximum `x₁`. Pull a ball about `x₀` back
    -- along a homeomorphism carrying the complement of a ball `V` about `x₁` into it.
    have hcrit' (x : M) (hx : x ∈ criticalPoints I f) : x = x₀ ∨ x = x₁ := by
      have h₀ := (hx₀.isLocalMin univ_mem).mem_criticalPoints (I := I)
      have h₁ := (hx₁.isLocalMax univ_mem).mem_criticalPoints (I := I)
      have hne : x₀ ≠ x₁ := fun h ↦ hlt.ne (congrArg f h)
      rw [hcrit, mem_insert_iff, mem_singleton_iff] at hx h₀ h₁
      grind
    obtain ⟨B, hBo, hx₀B, ⟨eB⟩⟩ := hball x₀
    obtain ⟨V, hVo, hx₁V, hV⟩ := hball x₁
    obtain ⟨g, hg⟩ := exists_homeomorph_mapsTo_compl hf hx₀ hx₁ hlt hcrit' hBo hx₀B hVo hx₁V
    exact ⟨g ⁻¹' B, V, hBo.preimage g.continuous, hVo,
      eq_univ_of_forall fun y ↦ (em (y ∈ V)).elim Or.inr fun h ↦ Or.inl (hg h),
      ⟨(g.subtype fun _ ↦ Iff.rfl).trans eB⟩, hV⟩
  -- A constant function: every point is critical, so `M = {p, q}` is covered by balls about `p`
  -- and `q`.
  obtain ⟨B, hBo, hpB, hB⟩ := hball p
  obtain ⟨V, hVo, hqV, hV⟩ := hball q
  refine ⟨B, V, hBo, hVo, eq_univ_of_forall fun x ↦ ?_, hB, hV⟩
  have hmin : IsMinOn f univ x := isMinOn_univ_iff.2 fun y ↦
    (hconst ▸ hx₁ (mem_univ x)).trans (hx₀ (mem_univ y))
  have hx := (hmin.isLocalMin univ_mem).mem_criticalPoints (I := I)
  rw [hcrit, mem_insert_iff, mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  exacts [Or.inl hpB, Or.inr hqV]

end TauCeti
