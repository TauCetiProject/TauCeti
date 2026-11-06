/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import TauCeti.Geometry.Manifold.CoordinateBall
import TauCeti.Geometry.Manifold.Morse.Deformation

/-!
# Functions with two critical points: a cover by two Euclidean open sets

Let `f` be a smooth function with exactly two critical points on a compact boundaryless manifold
`M` modelled on a real vector space of dimension `m`. Then `M` is the union of two open sets, each
homeomorphic to `ℝᵐ` (`TauCeti.exists_twoEuclideanOpenCover_of_two_criticalPoints`). No
nondegeneracy is assumed: both critical points may be degenerate, even with vanishing Hessian, so
the Morse lemma is not available. This is the first step of the Reeb–Milnor–Rosen theorem that
such an `M` is homeomorphic to the sphere `Sᵐ`, which no longer needs `f` to be Morse; the
nondegenerate case is `TauCeti.IsMorse.nonempty_homeomorph_sphere_of_totalCriticalCount_eq_two`.

The proof follows Rosen and Milnor. By Fermat's theorem the two critical points are the global
minimum `x₀` and the global maximum `x₁` of `f`. If `f` is constant, every point is critical and
`M` consists of these two points. Otherwise `x₀` is the only point at the minimum value and `x₁`
the only point at the maximum value. Choose open neighbourhoods `B` of `x₀` and `V` of `x₁`
homeomorphic to `ℝᵐ` (`TauCeti.exists_isOpen_mem_subset_homeomorph`). By compactness some
sublevel `{f ≤ α}` with `α` above the minimum lies in `B`, and `f` stays below some `β` under the
maximum on the compact set `M \ V`. The band `f⁻¹[α, β]` is compact and contains no critical
point, so a diffeomorphism `Φ` of `M` carries `{f ≤ β}` onto `{f ≤ α}`
(`TauCeti.exists_diffeomorph_sublevel`). Hence `U = Φ⁻¹(B)` contains `M \ V`, and `U` is
homeomorphic to `B`.

## Main results

* `TauCeti.exists_twoEuclideanOpenCover_of_two_criticalPoints`: a compact boundaryless manifold
  carrying a smooth function with exactly two critical points is covered by two open sets
  homeomorphic to `ℝᵐ`.

## References

* J. Milnor, *Sommes de variétés différentiables et structures différentiables des sphères*,
  Bull. Soc. Math. France 87 (1959), 439–444, Theorem 1 and Corollary 1.
* R. H. Rosen, *A weak form of the star conjecture for manifolds*, Notices Amer. Math. Soc. 7
  (1960), abstract 570-28, p. 380, Lemma 1.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 4.1 and Remark 1.
-/

public section

open Set Module
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
  {f : M → ℝ}

/-- If the only critical points of `f` are a point `x₀` of minimum value and a point `x₁` of
strictly larger maximum value, then for all open neighbourhoods `B` of `x₀` and `V` of `x₁` some
diffeomorphism of `M` carries the complement of `V` into `B`: the descending flow across the band
between a sublevel inside `B` and a level above `f` on the complement of `V`. -/
private theorem exists_diffeomorph_mapsTo_compl (hf : ContMDiff I 𝓘(ℝ) ∞ f) {x₀ x₁ : M}
    (hx₀ : IsMinOn f univ x₀) (hx₁ : IsMaxOn f univ x₁) (hlt : f x₀ < f x₁)
    (hcrit : criticalPoints I f ⊆ {x₀, x₁}) {B V : Set M} (hB : IsOpen B) (hx₀B : x₀ ∈ B)
    (hV : IsOpen V) (hx₁V : x₁ ∈ V) :
    ∃ Φ : M ≃ₘ⟮I, I⟯ M, MapsTo Φ Vᶜ B := by
  have hfc : Continuous f := hf.continuous
  -- Outside `B`, `f` is bounded below by some `a'` above the minimum, since a point at the
  -- minimum value is critical, hence is `x₀`.
  obtain ⟨a', ha', hBc⟩ := hB.isClosed_compl.isCompact.exists_forall_le' hfc.continuousOn
    fun x (hx : x ∉ B) ↦ (hx₀ (mem_univ x)).lt_of_ne fun h ↦ by
      rcases hcrit ((IsMinOn.isLocalMin (fun y _ ↦ h ▸ hx₀ (mem_univ y))
        Filter.univ_mem).mem_criticalPoints) with rfl | rfl
      exacts [hx hx₀B, hlt.ne' (h ▸ rfl)]
  -- Outside `V`, `f` is bounded above by some `-b'` below the maximum.
  obtain ⟨b', hb', hVc⟩ := hV.isClosed_compl.isCompact.exists_forall_le' hfc.neg.continuousOn
    fun x (hx : x ∉ V) ↦ neg_lt_neg <| (hx₁ (mem_univ x)).lt_of_ne fun h ↦ by
      rcases hcrit ((IsMaxOn.isLocalMax (fun y _ ↦ h ▸ hx₁ (mem_univ y))
        Filter.univ_mem).mem_criticalPoints) with rfl | rfl
      exacts [hlt.ne (h ▸ rfl), hx hx₁V]
  -- The band `f⁻¹[α, β]` contains no critical point, `{f ≤ α} ⊆ B` and `Vᶜ ⊆ {f ≤ β}`.
  obtain ⟨α, hα₀, hα⟩ := exists_between (lt_min ha' hlt)
  have hβ : max α (-b') < f x₁ := max_lt (hα.trans_le (min_le_right _ _)) (by linarith)
  obtain ⟨Φ, hΦ⟩ := exists_diffeomorph_sublevel hf (le_max_left α (-b'))
    (isClosed_Icc.preimage hfc).isCompact fun x hxα hxβ h0 ↦ by
      rcases hcrit (mem_criticalPoints_iff_mfderiv_eq_zero.2 h0) with rfl | rfl <;>
        linarith [hβ]
  refine ⟨Φ, fun x (hxV : x ∉ V) ↦ by_contra fun hn ↦ ?_⟩
  have hΦx : f (Φ x) ≤ α := (hΦ x).1.2 ((le_neg.1 (hVc x hxV)).trans (le_max_right _ _))
  linarith [hBc _ hn, min_le_left a' (f x₁)]

/-- **A cover by two Euclidean open sets** (Rosen, Lemma 1). A compact boundaryless manifold
modelled on a real vector space of dimension `m`, which carries a smooth function with exactly two
critical points, is the union of two open sets each homeomorphic to `ℝᵐ`. The critical points may
be degenerate. -/
theorem exists_twoEuclideanOpenCover_of_two_criticalPoints (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (h2 : totalCriticalCount I f = 2) :
    ∃ U V : Set M, IsOpen U ∧ IsOpen V ∧ U ∪ V = univ ∧
      Nonempty (U ≃ₜ EuclideanSpace ℝ (Fin (finrank ℝ E))) ∧
      Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin (finrank ℝ E))) := by
  obtain ⟨p, q, -, hpq⟩ := encard_eq_two.1 ((totalCriticalCount_def (I := I)).symm.trans h2)
  have hfc : Continuous f := hf.continuous
  -- Every point has an open neighbourhood homeomorphic to `ℝᵐ`.
  have hball (x : M) : ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      Nonempty (U ≃ₜ EuclideanSpace ℝ (Fin (finrank ℝ E))) := by
    obtain ⟨U, hU, hxU, -, ⟨e⟩⟩ :=
      exists_isOpen_mem_subset_homeomorph I (Filter.univ_mem (f := nhds x))
    exact ⟨U, hU, hxU, ⟨e.trans toEuclidean.toHomeomorph⟩⟩
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn ⟨p, mem_univ p⟩ hfc.continuousOn
  obtain ⟨x₁, -, hx₁⟩ := isCompact_univ.exists_isMaxOn ⟨p, mem_univ p⟩ hfc.continuousOn
  rcases (hx₀ (mem_univ x₁)).lt_or_eq with hlt | hconst
  swap
  · -- A constant function: every point is critical, so `M = {p, q}`.
    have hall (x : M) : x ∈ criticalPoints I f :=
      (IsMinOn.isLocalMin (fun y _ ↦ (hconst ▸ hx₁ (mem_univ x)).trans (hx₀ (mem_univ y)))
        Filter.univ_mem).mem_criticalPoints
    obtain ⟨U, hU, hpU, hUe⟩ := hball p
    obtain ⟨V, hV, hqV, hVe⟩ := hball q
    refine ⟨U, V, hU, hV, eq_univ_of_forall fun x ↦ ?_, hUe, hVe⟩
    have hx := hall x
    rw [hpq, mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    exacts [Or.inl hpU, Or.inr hqV]
  -- Otherwise the two critical points are the minimum `x₀` and the maximum `x₁`.
  have hcrit : criticalPoints I f ⊆ {x₀, x₁} := by
    have h₀ := (hx₀.isLocalMin Filter.univ_mem).mem_criticalPoints (I := I)
    have h₁ := (hx₁.isLocalMax Filter.univ_mem).mem_criticalPoints (I := I)
    have hne : x₀ ≠ x₁ := fun h ↦ hlt.ne (congrArg f h)
    intro x hx
    simp only [hpq, mem_insert_iff, mem_singleton_iff] at hx h₀ h₁ ⊢
    grind
  obtain ⟨B, hB, hx₀B, ⟨eB⟩⟩ := hball x₀
  obtain ⟨V, hV, hx₁V, hVe⟩ := hball x₁
  obtain ⟨Φ, hΦ⟩ := exists_diffeomorph_mapsTo_compl hf hx₀ hx₁ hlt hcrit hB hx₀B hV hx₁V
  -- `U = Φ⁻¹(B)` is homeomorphic to `B` and contains the complement of `V`.
  refine ⟨Φ.toHomeomorph.symm '' B, V, Φ.toHomeomorph.symm.isOpenMap B hB, hV,
    eq_univ_of_forall fun x ↦ ?_, ⟨(Φ.toHomeomorph.symm.image B).symm.trans eB⟩, hVe⟩
  by_cases hxV : x ∈ V
  exacts [Or.inr hxV, Or.inl ⟨Φ x, hΦ hxV, by simp⟩]

end TauCeti
