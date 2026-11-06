/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import TauCeti.Geometry.Manifold.CoordinateBall
import TauCeti.Geometry.Manifold.Morse.Deformation
import TauCeti.Topology.Order.Sublevel

/-!
# Smooth functions with exactly two critical points

Let `f` be a smooth real function on a compact boundaryless manifold `M` modelled on a real vector
space of dimension `m`, with exactly two critical points. The critical points may be degenerate.
Then `M` is the union of two open subsets, each homeomorphic to `ℝᵐ`
(`TauCeti.exists_twoEuclideanOpenCover_of_two_criticalPoints`). This is the input of the
topological recognition of `M` as the sphere `Sᵐ` (Milnor 1959, Theorem 1(3) and Corollary 1;
Rosen 1960, Lemma 1), which does not need `f` to be a Morse function.

When `f` is not constant, its two critical points are the unique global minimum `p` and the unique
global maximum `q`, by Fermat's theorem. Take open coordinate neighbourhoods `B` of `p` and `V` of
`q`, each homeomorphic to `ℝᵐ`. Since `p` is the only minimum point, a small sublevel
`{f ≤ f p + ε}` lies in `B`; since `q` is the only maximum point, `f ≤ f q - δ` on the compact set
`M \ V`. The band `f⁻¹[f p + ε, f q - δ]` is compact and contains no critical point, so there is a
flow along which `f` never increases and decreases at unit speed through the band
(`TauCeti.exists_flow_apply_eq_sub`). After a time `T` at least the width of the band, it carries
`M \ V` into `{f ≤ f p + ε} ⊆ B`. So `M \ V` lies in `U = φ_{-T}(B)`, and the time-`T` map is a
homeomorphism of `U` onto `B`. No nondegenerate normal form is used, and none is available at a
degenerate critical point. When `f` is constant, every point is critical, so `M` consists of the
two critical points and any two coordinate neighbourhoods cover it.

## Main results

* `TauCeti.exists_twoEuclideanOpenCover_of_two_criticalPoints`: a compact boundaryless manifold
  carrying a smooth function with exactly two critical points is covered by two open subsets
  homeomorphic to `ℝᵐ`.

## References

* J. Milnor, *Sommes de variétés différentiables et structures différentiables des sphères*,
  Bull. Soc. Math. France 87 (1959), 439–444, Theorem 1 and Corollary 1.
* R. H. Rosen, *A weak form of the star conjecture for manifolds*, Notices Amer. Math. Soc. 7
  (1960), abstract 570-28, p. 380, Lemma 1.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.1 and Remark 1 after Theorem 4.1.
-/

public section

open Filter Function Set Module Topology
open TopologicalSpace (Opens)
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
  {f : M → ℝ}

omit [T2Space M] [CompactSpace M] in
/-- The open subset `range e` of `M`, for an open embedding `e` of `E`, is homeomorphic to
`ℝᵐ`, for `m` the dimension of `E`. -/
private theorem nonempty_homeomorph_range {e : E → M} (he : IsOpenEmbedding e) :
    Nonempty ((⟨range e, he.isOpen_range⟩ : Opens M) ≃ₜ (Fin (finrank ℝ E) → ℝ)) :=
  ⟨he.toIsEmbedding.toHomeomorph.symm.trans
    (ContinuousLinearEquiv.ofFinrankEq (finrank_fin_fun ℝ).symm).toHomeomorph⟩

/-- The uniform descent estimate when the minimum `x₀` is below the maximum `x₁` and these are
the only critical points: for open neighbourhoods `B` of `x₀` and `V` of `x₁`, there is a
homeomorphism `φ` of `M`, the time-`T` map of a flow along which `f` never increases, with
`φ⁻¹(B) ∪ V = M`. -/
private theorem exists_homeomorph_preimage_union_eq_univ (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {x₀ x₁ : M} (hx₀ : IsMinOn f univ x₀) (hx₁ : IsMaxOn f univ x₁) (hlt : f x₀ < f x₁)
    (hcrit : ∀ x ∈ criticalPoints I f, x = x₀ ∨ x = x₁) {B V : Set M} (hB : IsOpen B)
    (hx₀B : x₀ ∈ B) (hV : IsOpen V) (hx₁V : x₁ ∈ V) :
    ∃ φ : M ≃ₜ M, φ ⁻¹' B ∪ V = univ := by
  have hfc : Continuous f := hf.continuous
  -- `x₀` is the only point where `f` takes a value `≤ f x₀`, and `x₁` the only one `≥ f x₁`.
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
  -- Small sublevels lie in `B`, and small superlevels in `V`.
  obtain ⟨ε, hε, hεB⟩ := exists_pos_sublevel_subset_of_unique_min (isClosed_le hfc
    continuous_const).isCompact hfc.continuousOn hlt hmin hB hx₀B
  obtain ⟨δ, hδ, hδV⟩ := exists_pos_sublevel_subset_of_unique_min (f := -f) (a := -f x₀)
    (isClosed_le hfc.neg continuous_const).isCompact hfc.neg.continuousOn (neg_lt_neg hlt)
    (fun y hy ↦ hmax y (neg_le_neg_iff.1 hy)) hV hx₁V
  have hVc (x : M) (hx : x ∉ V) : f x ≤ f x₁ - δ := by
    by_contra h
    exact hx (hδV (show -f x ≤ -f x₁ + δ by linarith))
  -- The band `f⁻¹[a, b]` lies strictly between the two critical values.
  set a := f x₀ + min ε ((f x₁ - f x₀) / 2)
  set b := max a (f x₁ - δ)
  have hab : a ≤ b := le_max_left _ _
  have ha₀ : f x₀ < a := lt_add_of_pos_right _ (lt_min hε (by linarith))
  have hb₁ : b < f x₁ :=
    max_lt (by linarith [min_le_right ε ((f x₁ - f x₀) / 2)]) (by linarith)
  have hreg (x : M) (hax : a ≤ f x) (hxb : f x ≤ b) : mfderiv I 𝓘(ℝ) f x ≠ 0 := fun h0 ↦ by
    rcases hcrit x (mem_criticalPoints_iff_mfderiv_eq_zero.2 h0) with rfl | rfl <;> linarith
  obtain ⟨φ, -, hanti, -, hφ⟩ := exists_flow_apply_eq_sub hf
    (isClosed_Icc.preimage hfc).isCompact hreg
  refine ⟨φ.toHomeomorph (b - a), eq_univ_of_forall fun x ↦ ?_⟩
  by_cases hxV : x ∈ V
  · exact mem_union_right _ hxV
  refine mem_union_left _ (hεB ?_)
  rw [Flow.toHomeomorph_apply, mem_ofPred_eq]
  -- After time `b - a`, every point of `{f ≤ b}` has reached `{f ≤ a}`.
  calc f (φ (b - a) x) ≤ a :=
        (φ.apply_le_iff_of_apply_eq_sub hfc hab (fun x ↦ (hanti x).antitoneOn _) hφ x).2
          ((hVc x hxV).trans (le_max_right _ _))
    _ ≤ f x₀ + ε := by linarith [min_le_left ε ((f x₁ - f x₀) / 2)]

/-- **Two Euclidean open sets cover a manifold with two critical points.** If a smooth real
function `f` on a compact boundaryless manifold `M`, modelled on a real vector space of dimension
`m`, has exactly two critical points, then `M` is the union of two open subsets, each homeomorphic
to `ℝᵐ`. The critical points may be degenerate. -/
theorem exists_twoEuclideanOpenCover_of_two_criticalPoints (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hcrit : totalCriticalCount I f = 2) :
    ∃ U V : Opens M, (∀ x : M, x ∈ U ∨ x ∈ V) ∧
      Nonempty (U ≃ₜ (Fin (finrank ℝ E) → ℝ)) ∧ Nonempty (V ≃ₜ (Fin (finrank ℝ E) → ℝ)) := by
  obtain ⟨p, q, -, hcrit_eq⟩ :=
    encard_eq_two.1 ((totalCriticalCount_def (I := I)).symm.trans hcrit)
  have hfc : Continuous f := hf.continuous
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn ⟨p, mem_univ p⟩ hfc.continuousOn
  obtain ⟨x₁, -, hx₁⟩ := isCompact_univ.exists_isMaxOn ⟨p, mem_univ p⟩ hfc.continuousOn
  rcases (hx₀ (mem_univ x₁)).lt_or_eq with hlt | hconst
  · -- The minimum and the maximum are the two critical points.
    have hcrit' (x : M) (hx : x ∈ criticalPoints I f) : x = x₀ ∨ x = x₁ := by
      have h₀ := (hx₀.isLocalMin univ_mem).mem_criticalPoints (I := I)
      have h₁ := (hx₁.isLocalMax univ_mem).mem_criticalPoints (I := I)
      have hne : x₀ ≠ x₁ := fun h ↦ hlt.ne (congrArg f h)
      rw [hcrit_eq, mem_insert_iff, mem_singleton_iff] at hx h₀ h₁
      grind
    obtain ⟨e₀, he₀, hx₀e, -⟩ := exists_isOpenEmbedding_range_subset I (x := x₀) univ_mem
    obtain ⟨e₁, he₁, hx₁e, -⟩ := exists_isOpenEmbedding_range_subset I (x := x₁) univ_mem
    obtain ⟨φ, hφ⟩ := exists_homeomorph_preimage_union_eq_univ hf hx₀ hx₁ hlt hcrit'
      he₀.isOpen_range ⟨0, hx₀e⟩ he₁.isOpen_range ⟨0, hx₁e⟩
    -- The open set `φ⁻¹(range e₀)` is the range of the open embedding `φ⁻¹ ∘ e₀`.
    have hU : IsOpenEmbedding (φ.symm ∘ e₀) := φ.symm.isOpenEmbedding.comp he₀
    have hrange : range (φ.symm ∘ e₀) = φ ⁻¹' range e₀ := by
      rw [range_comp, Homeomorph.image_symm]
    refine ⟨⟨_, hU.isOpen_range⟩, ⟨_, he₁.isOpen_range⟩, fun x ↦ ?_,
      nonempty_homeomorph_range hU, nonempty_homeomorph_range he₁⟩
    have hx : x ∈ φ ⁻¹' range e₀ ∪ range e₁ := hφ ▸ mem_univ x
    rwa [← hrange] at hx
  · -- A constant function: every point is critical, so `M` consists of the two critical points.
    have hall (x : M) : x = p ∨ x = q := by
      have hx : IsMinOn f univ x := isMinOn_univ_iff.2 fun y ↦
        le_antisymm (hconst ▸ hx₁ (mem_univ x)) (hx₀ (mem_univ x)) ▸ hx₀ (mem_univ y)
      have hx' := (hx.isLocalMin univ_mem).mem_criticalPoints (I := I)
      rwa [hcrit_eq, mem_insert_iff, mem_singleton_iff] at hx'
    obtain ⟨e₀, he₀, hpe, -⟩ := exists_isOpenEmbedding_range_subset I (x := p) univ_mem
    obtain ⟨e₁, he₁, hqe, -⟩ := exists_isOpenEmbedding_range_subset I (x := q) univ_mem
    refine ⟨⟨_, he₀.isOpen_range⟩, ⟨_, he₁.isOpen_range⟩, fun x ↦ ?_,
      nonempty_homeomorph_range he₀, nonempty_homeomorph_range he₁⟩
    rcases hall x with rfl | rfl
    · exact Or.inl ⟨0, hpe⟩
    · exact Or.inr ⟨0, hqe⟩

end TauCeti
