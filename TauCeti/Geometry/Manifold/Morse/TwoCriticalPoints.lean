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
# Functions with exactly two critical points

Let `f` be a smooth function on a compact boundaryless manifold `M` modelled on a
finite-dimensional real vector space `E`, and suppose that `f` has exactly two critical points.
No nondegeneracy is assumed: both critical points may have vanishing Hessian. Then `M` is the
union of two open sets, each homeomorphic to `E`
(`TauCeti.exists_twoEuclideanOpenCover_of_two_criticalPoints`). By the two-open-cell lemma of
Milnor and Rosen, a compact space covered by two open copies of `ℝᵐ`, `m > 0`, is homeomorphic to
the sphere `Sᵐ`, so this is the first half of the topological sphere theorem for functions with
two, possibly degenerate, critical points.

The two critical points are the unique minimum `p` and the unique maximum `q` of `f`, by Fermat's
theorem. Let `B` be a coordinate ball about `p` and `V` one about `q`, both homeomorphic to `E`.
Since `p` is the only point where `f` takes its minimal value `a`, some sublevel
`{f < a + ε}` lies in `B`; since `q` is the only point where `f` takes its maximal value `b`, the
compact set `K = M \ V` lies in some sublevel `{f ≤ b - δ}`. The band between these levels is
compact and contains no critical point, so the descending flow of `f` lowering it at unit speed
through the band (`TauCeti.exists_flow_apply_eq_sub`) carries `K` into `B` after a finite time
`T`. Hence `U = φ_T⁻¹(B)` covers `K`, and it is homeomorphic to `B` because `φ_T` is a
homeomorphism of `M`. The argument uses only compactness and the flow, not a normal form at the
critical points, and no continuity of hitting times.

If `f` is constant, every point is critical, so `M` consists of the two critical points, and the
coordinate balls about them already cover `M`.

## Main results

* `TauCeti.exists_twoEuclideanOpenCover_of_two_criticalPoints`: a compact boundaryless manifold
  carrying a smooth function with exactly two critical points is the union of two open sets
  homeomorphic to its model vector space.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 4.1 and Remark 1.
* J. Milnor, *Sommes de variétés différentiables et structures différentiables des sphères*,
  Bull. Soc. Math. France 87 (1959), 439–444, Theorem 1 and Corollary 1.
* R. H. Rosen, *A weak form of the star conjecture for manifolds*, Notices Amer. Math. Soc. 7
  (1960), abstract 570-28, p. 380, Lemma 1.
-/

public section

open Filter Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
  {f : M → ℝ}

/-- If the only critical points of `f` are a minimum `p` and a maximum `q` with `f p < f q`, and
`B ∋ p` and `V ∋ q` are open, then the descending flow of `f` carries `M \ V` into `B` in finite
time, so `M \ V` lies in the preimage of `B` under a homeomorphism of `M`. -/
private theorem exists_homeomorph_compl_subset_preimage (hf : ContMDiff I 𝓘(ℝ) ∞ f) {p q : M}
    (hp : IsMinOn f univ p) (hq : IsMaxOn f univ q) (hlt : f p < f q)
    (hcrit : ∀ x ∈ criticalPoints I f, x = p ∨ x = q) {B V : Set M} (hB : IsOpen B)
    (hpB : p ∈ B) (hV : IsOpen V) (hqV : q ∈ V) :
    ∃ φ : M ≃ₜ M, Vᶜ ⊆ φ ⁻¹' B := by
  have hfc : Continuous f := hf.continuous
  -- The minimum and the maximum are the only points with their values.
  have hmin (x : M) (hx : f x ≤ f p) : x = p := by
    have hx' : IsMinOn f univ x := isMinOn_univ_iff.2 fun z ↦ hx.trans (hp (mem_univ z))
    refine (hcrit x (hx'.isLocalMin univ_mem).mem_criticalPoints).resolve_right ?_
    rintro rfl
    linarith
  have hmax (x : M) (hx : f q ≤ f x) : x = q := by
    have hx' : IsMaxOn f univ x := isMaxOn_univ_iff.2 fun z ↦ (hq (mem_univ z)).trans hx
    refine (hcrit x (hx'.isLocalMax univ_mem).mem_criticalPoints).resolve_left ?_
    rintro rfl
    linarith
  -- Outside `B` the function stays above a level `a₁ > f p`, and outside `V` below `b₁ < f q`.
  obtain ⟨a₁, ha₁, hBc⟩ := hB.isClosed_compl.isCompact.exists_forall_le' hfc.continuousOn
    fun x hx ↦ (hp (mem_univ x)).lt_of_ne fun h ↦ hx (hmin x h.ge ▸ hpB)
  obtain ⟨b₁, hb₁, hVc⟩ : ∃ b₁ < f q, ∀ x ∈ Vᶜ, f x ≤ b₁ := by
    obtain ⟨b₁, hb₁, hVc⟩ := hV.isClosed_compl.isCompact.exists_forall_le' hfc.neg.continuousOn
      fun x hx ↦ neg_lt_neg <| (hq (mem_univ x)).lt_of_ne fun h ↦ hx (hmax x h.ge ▸ hqV)
    simp only [Pi.neg_apply] at hb₁ hVc
    exact ⟨-b₁, by linarith, fun x hx ↦ by linarith [hVc x hx]⟩
  -- Flow down through the band `f⁻¹[a, b]`, which contains no critical point.
  obtain ⟨a, b, hpa, haa₁, hab, hb₁b, hbq⟩ :
      ∃ a b, f p < a ∧ a < a₁ ∧ a ≤ b ∧ b₁ ≤ b ∧ b < f q := by
    refine ⟨min ((f p + a₁) / 2) ((f p + f q) / 2), max b₁ (min ((f p + a₁) / 2)
      ((f p + f q) / 2)), ?_, ?_, le_max_right _ _, le_max_left _ _, ?_⟩ <;>
    grind
  obtain ⟨φ, -, hanti, -, hφ⟩ := exists_flow_apply_eq_sub hf (a := a) (b := b)
    (isClosed_Icc.preimage hfc).isCompact fun x hxa hxb h0 ↦ by
      rcases hcrit x (mem_criticalPoints_iff_mfderiv_eq_zero.2 h0) with rfl | rfl <;> linarith
  refine ⟨φ.toHomeomorph (b - a), fun x hx ↦ ?_⟩
  have hxb : f x ≤ b := (hVc x hx).trans hb₁b
  -- After time `b - a` the value of `f` is at most `a`, so the point lies in `B`.
  have hle : f (φ (b - a) x) ≤ a := by
    rcases le_or_gt (f x) a with hxa | hxa
    · calc f (φ (b - a) x) ≤ f (φ 0 x) := hanti x (sub_nonneg.2 hab)
        _ = f x := by rw [φ.map_zero_apply]
        _ ≤ a := hxa
    · calc f (φ (b - a) x) ≤ f (φ (f x - a) x) := hanti x (show f x - a ≤ b - a by linarith)
        _ = a := by rw [hφ x _ (by linarith) (by linarith) hxb]; ring
  by_contra hxB
  exact (hle.trans_lt haa₁).not_ge (hBc _ hxB)

/-- **A two-cell open cover from a function with two critical points.** If a compact boundaryless
manifold `M`, modelled on a finite-dimensional real vector space `E`, carries a smooth function
with exactly two critical points, then `M` is the union of two open sets, each homeomorphic to
`E`. The critical points may be degenerate. -/
theorem exists_twoEuclideanOpenCover_of_two_criticalPoints (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (h2 : totalCriticalCount I f = 2) :
    ∃ U V : Set M, IsOpen U ∧ IsOpen V ∧ U ∪ V = univ ∧
      Nonempty (U ≃ₜ E) ∧ Nonempty (V ≃ₜ E) := by
  obtain ⟨p, q, hpq, hpq'⟩ := encard_eq_two.1 ((totalCriticalCount_def (I := I)).symm.trans h2)
  have hfc : Continuous f := hf.continuous
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn ⟨p, mem_univ p⟩ hfc.continuousOn
  obtain ⟨x₁, -, hx₁⟩ := isCompact_univ.exists_isMaxOn ⟨p, mem_univ p⟩ hfc.continuousOn
  rcases (hx₀ (mem_univ x₁)).lt_or_eq with hlt | hconst
  · -- A coordinate ball `V` about the maximum, and one about the minimum pulled back by the flow.
    have hcrit : ∀ x ∈ criticalPoints I f, x = x₀ ∨ x = x₁ := fun x hx ↦ by
      have h₀ := (hx₀.isLocalMin univ_mem).mem_criticalPoints (I := I)
      have h₁ := (hx₁.isLocalMax univ_mem).mem_criticalPoints (I := I)
      have hne : x₀ ≠ x₁ := fun h ↦ hlt.ne (congrArg f h)
      rw [hpq', mem_insert_iff, mem_singleton_iff] at hx h₀ h₁
      grind
    obtain ⟨B, hB, hx₀B, ⟨eB⟩⟩ := exists_isOpen_mem_homeomorph I x₀
    obtain ⟨V, hV, hx₁V, ⟨eV⟩⟩ := exists_isOpen_mem_homeomorph I x₁
    obtain ⟨φ, hφ⟩ :=
      exists_homeomorph_compl_subset_preimage hf hx₀ hx₁ hlt hcrit hB hx₀B hV hx₁V
    refine ⟨φ ⁻¹' B, V, hB.preimage φ.continuous, hV,
      eq_univ_of_forall fun x ↦ (em (x ∈ V)).elim Or.inr fun hx ↦ Or.inl (hφ hx),
      ⟨(φ.subtype fun _ ↦ Iff.rfl).trans eB⟩, ⟨eV⟩⟩
  -- A constant function: every point is critical, so `M = {p, q}`.
  have hall (x : M) : f x = f x₀ :=
    le_antisymm (hconst ▸ hx₁ (mem_univ x)) (hx₀ (mem_univ x))
  have hcrit (x : M) : x ∈ criticalPoints I f :=
    ((isMinOn_univ_iff.2 fun y ↦ by rw [hall x, hall y]).isLocalMin univ_mem).mem_criticalPoints
  obtain ⟨U, hU, hpU, ⟨eU⟩⟩ := exists_isOpen_mem_homeomorph I p
  obtain ⟨V, hV, hqV, ⟨eV⟩⟩ := exists_isOpen_mem_homeomorph I q
  refine ⟨U, V, hU, hV, eq_univ_of_forall fun x ↦ ?_, ⟨eU⟩, ⟨eV⟩⟩
  have hx := hcrit x
  rw [hpq', mem_insert_iff, mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  exacts [Or.inl hpU, Or.inr hqV]

end TauCeti
