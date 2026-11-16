/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import TauCeti.Analysis.Complex.PolynomialHull.Basic
public import TauCeti.Topology.FilledIn
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.Complex.Polynomial.Approximation
import TauCeti.Analysis.Convex.Caratheodory
import TauCeti.Analysis.Normed.Module.Convex
import TauCeti.Topology.ConnectedComponents

/-!
# Holomorphic hulls in complex normed spaces and in the complex plane

Given sets `Ω` and `K` in a complex normed space `V`, the **holomorphic hull**
`TauCeti.holomorphicHull Ω K` (`\widehat{K}_Ω`) consists of those points `z ∈ Ω` such that every
holomorphic function `f : V → ℂ` on `Ω` bounded in norm by `c` on `K` also satisfies `‖f z‖ ≤ c`.
For compact `K ⊆ Ω`, these are the points of `Ω` where `|f(z)| ≤ max_K |f|` for all `f ∈ 𝒪(Ω)`.

Several fundamental properties hold in an arbitrary complex normed space `V`:
* Structural closure properties: containment `K ⊆ holomorphicHull Ω K ⊆ Ω` (when `K ⊆ Ω`),
  monotonicity in both `Ω` and `K`, idempotence `holomorphicHull Ω (holomorphicHull Ω K) =
  holomorphicHull Ω K`, and openness of `Ω \ holomorphicHull Ω K` for open `Ω`.
* Maximum-modulus trapping (`TauCeti.mem_holomorphicHull_of_isBounded_connectedComponentIn`): in a
  nontrivial complex normed space, any bounded connected component of `Ω \ K` (when `Ω \ K` is
  open) whose closure lies in `Ω` is swallowed by `holomorphicHull Ω K`. In particular,
  `holomorphicHull Ω K` is always filled in an open set `Ω` (`IsOpen.isFilledIn_holomorphicHull`),
  with no assumption on `K` (nontriviality of `V` is necessary because on `{0}` the hull
  `holomorphicHull univ ∅ = ∅` is not filled in `univ`).
* Geometric Hahn–Banach bound (`TauCeti.holomorphicHull_subset_closedConvexHull`): testing against
  exponentials `w ↦ exp (L w)` of continuous complex-linear functionals places `holomorphicHull Ω K`
  inside `closedConvexHull ℝ K` (and inside `convexHull ℝ K` when `V` is finite-dimensional and `K`
  is compact).

In one complex variable (`V = ℂ`), testing against simple fractions `w ↦ (w - ζ)⁻¹` with pole
`ζ ∈ Ωᶜ` shows that passing from a nonempty compact `K ⊆ Ω` to `holomorphicHull Ω K` preserves the
distance to every exterior point `ζ ∈ Ωᶜ` (`IsCompact.infDist_holomorphicHull_eq`) and hence the
distance to `Ωᶜ` (`IsCompact.biInf_infEDist_compl_holomorphicHull_eq`). Consequently
`holomorphicHull Ω K` cannot accumulate on `∂Ω`, so for compact `K ⊆ Ω` in an open set `Ω ⊆ ℂ` the
hull `holomorphicHull Ω K` is itself compact (`IsCompact.isCompact_holomorphicHull`). On `Ω = univ`,
uniform Taylor approximation of entire functions identifies `holomorphicHull univ K` with the
one-variable polynomial hull (`IsCompact.mem_holomorphicHull_univ_iff_forall_polynomial`,
`IsCompact.holomorphicHull_univ_eq_preimage_polynomialHull`).

In `TauCeti/Analysis/Complex/Runge/Approximation.lean`, Runge's theorem supplies the reverse
topological inclusion in `ℂ`, identifying `holomorphicHull Ω K` for compact `K ⊆ Ω` with `K` union
the relatively compact connected components of `Ω \ K` in `Ω`.

## Main definitions and results

* `TauCeti.holomorphicHull`: the `𝒪(Ω)`-hull of `K` in `Ω`.
* `IsOpen.isOpen_sdiff_holomorphicHull` and `IsOpen.isFilledIn_holomorphicHull`: `Ω \ K̂_Ω` is open
  and (for nontrivial `V`) `K̂_Ω` is filled in `Ω` for every open `Ω ⊆ V` and every `K ⊆ V`.
* `TauCeti.holomorphicHull_subset_closedConvexHull` and
  `IsCompact.holomorphicHull_subset_convexHull`: convex-hull upper bounds via geometric Hahn–Banach
  separation.
* `IsCompact.infDist_holomorphicHull_eq`, `IsCompact.biInf_infEDist_compl_holomorphicHull_eq`, and
  `IsCompact.isCompact_holomorphicHull`: boundary-distance invariance and compactness of `K̂_Ω` in
  `ℂ`.
* `IsCompact.mem_holomorphicHull_univ_iff_forall_polynomial` and
  `IsCompact.isPolynomiallyConvex_image_const_iff`: equivalence between the entire hull on `ℂ` and
  polynomial convexity.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., §1.3,
  Theorem 1.3.4.
* A. Rainer, *Advanced Complex Analysis*, §11, Lemma 11.3.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., Chapter 13.
-/

public section

open Bornology Complex Metric Polynomial Set
open scoped ENNReal Topology

namespace TauCeti

section NormedSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The **holomorphic hull** `\widehat{K}_Ω` of `K` in `Ω`: the points `z ∈ Ω` at which every
function `f : V → ℂ` holomorphic on `Ω` satisfies `‖f z‖ ≤ c` whenever `‖f w‖ ≤ c` for all
`w ∈ K`. -/
def holomorphicHull (Ω K : Set V) : Set V :=
  {z ∈ Ω | ∀ f : V → ℂ, DifferentiableOn ℂ f Ω → ∀ c : ℝ, (∀ w ∈ K, ‖f w‖ ≤ c) → ‖f z‖ ≤ c}

/-- Unfolding membership in `TauCeti.holomorphicHull`. -/
theorem mem_holomorphicHull_iff {Ω K : Set V} {z : V} :
    z ∈ holomorphicHull Ω K ↔
      z ∈ Ω ∧ ∀ f : V → ℂ, DifferentiableOn ℂ f Ω →
        ∀ c : ℝ, (∀ w ∈ K, ‖f w‖ ≤ c) → ‖f z‖ ≤ c :=
  (Iff.rfl)

/-- The holomorphic hull of `K` in `Ω` is contained in `Ω`. -/
theorem holomorphicHull_subset (Ω K : Set V) : holomorphicHull Ω K ⊆ Ω :=
  fun _ hz ↦ hz.1

/-- Any subset `K ⊆ Ω` is contained in its holomorphic hull in `Ω`. -/
theorem subset_holomorphicHull {Ω K : Set V} (hKΩ : K ⊆ Ω) : K ⊆ holomorphicHull Ω K :=
  fun _ hz ↦ ⟨hKΩ hz, fun _ _ _ hc ↦ hc _ hz⟩

/-- Enlarging `K` enlarges `holomorphicHull Ω K`. -/
@[gcongr]
theorem holomorphicHull_mono {Ω K L : Set V} (h : K ⊆ L) :
    holomorphicHull Ω K ⊆ holomorphicHull Ω L :=
  fun _ hz ↦ ⟨hz.1, fun f hf c hc ↦ hz.2 f hf c fun w hw ↦ hc w (h hw)⟩

/-- Enlarging the ambient set `Ω` shrinks the family of functions holomorphic on `Ω`, hence enlarges
the holomorphic hull. -/
@[gcongr]
theorem holomorphicHull_mono_left {Ω₁ Ω₂ K : Set V} (h : Ω₁ ⊆ Ω₂) :
    holomorphicHull Ω₁ K ⊆ holomorphicHull Ω₂ K :=
  fun _ hz ↦ ⟨h hz.1, fun f hf c hc ↦ hz.2 f (hf.mono h) c hc⟩

@[simp]
theorem holomorphicHull_empty (Ω : Set V) : holomorphicHull Ω ∅ = ∅ :=
  eq_empty_of_forall_notMem fun _ hz ↦
    (hz.2 (fun _ ↦ 1) (differentiableOn_const 1) 0 (by simp)).not_gt (by simp)

/-- Taking the holomorphic hull in `Ω` is idempotent. -/
@[simp]
theorem holomorphicHull_holomorphicHull (Ω K : Set V) :
    holomorphicHull Ω (holomorphicHull Ω K) = holomorphicHull Ω K :=
  (subset_holomorphicHull (holomorphicHull_subset Ω K)).antisymm' fun _ hz ↦
    ⟨hz.1, fun f hf c hc ↦ hz.2 f hf c fun _ hw ↦ hw.2 f hf c hc⟩

/-- A point of `Ω` outside `holomorphicHull Ω K` is separated from `K` by a function holomorphic on
`Ω` of norm `< 1` on `K` and `> 1` at the point. -/
theorem exists_differentiableOn_norm_lt_one_lt_of_notMem_holomorphicHull {Ω K : Set V} {z : V}
    (hzΩ : z ∈ Ω) (hz : z ∉ holomorphicHull Ω K) :
    ∃ f : V → ℂ, DifferentiableOn ℂ f Ω ∧ (∀ w ∈ K, ‖f w‖ < 1) ∧ 1 < ‖f z‖ := by
  have hz' : ¬∀ f : V → ℂ, DifferentiableOn ℂ f Ω → ∀ c : ℝ, (∀ w ∈ K, ‖f w‖ ≤ c) → ‖f z‖ ≤ c :=
    fun h ↦ hz ⟨hzΩ, h⟩
  push Not at hz'
  obtain ⟨f, hf, c, hfK, hcz⟩ := hz'
  set s := ‖f z‖
  rcases (norm_nonneg (f z)).eq_or_lt with hs | hs
  · have hK : ∀ w ∈ K, False := fun w hw ↦
      ((norm_nonneg _).trans (hfK w hw)).not_gt (hs ▸ hcz)
    exact ⟨fun _ ↦ 2, differentiableOn_const 2, fun w hw ↦ (hK w hw).elim, by norm_num⟩
  set a := max c (s / 2)
  have has : a < s := max_lt hcz (half_lt_self hs)
  have hr : 0 < 2 / (a + s) := by positivity
  have hnorm (w : V) : ‖((2 / (a + s) : ℝ) : ℂ) * f w‖ = 2 * ‖f w‖ / (a + s) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le, div_mul_eq_mul_div]
  refine ⟨fun w ↦ ((2 / (a + s) : ℝ) : ℂ) * f w, hf.const_mul _, fun w hw ↦ ?_, ?_⟩
  · rw [hnorm, div_lt_one (by positivity)]
    linarith [(hfK w hw).trans (le_max_left c (s / 2))]
  · rw [hnorm, one_lt_div (by positivity)]
    linarith

/-- If a function holomorphic on `Ω` is strictly smaller in norm at every point of a compact set
`K ⊆ Ω` than at `z`, then `z ∉ holomorphicHull Ω K`. -/
theorem _root_.IsCompact.notMem_holomorphicHull_of_forall_norm_lt {Ω K : Set V} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) {z : V} {f : V → ℂ} (hf : DifferentiableOn ℂ f Ω)
    (hlt : ∀ w ∈ K, ‖f w‖ < ‖f z‖) : z ∉ holomorphicHull Ω K := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨w₀, hw₀, hmax⟩ := hK.exists_isMaxOn hne (hf.continuousOn.mono hKΩ).norm
  exact fun hz ↦ (hz.2 f hf _ fun w hw ↦ hmax hw).not_gt (hlt w₀ hw₀)

/-- For an open set `Ω ⊆ V` and any `K ⊆ V`, the complement `Ω \ holomorphicHull Ω K` is open, so
`holomorphicHull Ω K` is relatively closed in `Ω`. -/
theorem _root_.IsOpen.isOpen_sdiff_holomorphicHull {Ω K : Set V} (hΩ : IsOpen Ω) :
    IsOpen (Ω \ holomorphicHull Ω K) := by
  have heq : Ω \ holomorphicHull Ω K =
      ⋃ (f : V → ℂ) (_ : DifferentiableOn ℂ f Ω) (c : ℝ) (_ : ∀ w ∈ K, ‖f w‖ ≤ c),
        Ω ∩ (fun z ↦ ‖f z‖) ⁻¹' Ioi c := by
    ext z
    simp only [mem_sdiff, mem_holomorphicHull_iff, not_and, not_forall, not_le, exists_prop,
      mem_iUnion, mem_inter_iff, mem_preimage, mem_Ioi]
    exact ⟨fun ⟨hzΩ, h⟩ ↦ let ⟨f, hf, c, hc, hfz⟩ := h hzΩ; ⟨f, hf, c, hc, hzΩ, hfz⟩,
      fun ⟨f, hf, c, hc, hzΩ, hfz⟩ ↦ ⟨hzΩ, fun _ ↦ ⟨f, hf, c, hc, hfz⟩⟩⟩
  rw [heq]
  exact isOpen_iUnion fun f ↦ isOpen_iUnion fun hf ↦ isOpen_iUnion fun c ↦ isOpen_iUnion fun _ ↦
    hf.continuousOn.norm.isOpen_inter_preimage hΩ isOpen_Ioi

/-- **Maximum-modulus trapping in the holomorphic hull.** In a nontrivial complex normed space `V`,
if `Ω \ K` is open, then every point `z ∈ Ω \ K` whose connected component `C` in `Ω \ K` is
bounded and satisfies `closure C ⊆ Ω` belongs to `holomorphicHull Ω K`. -/
theorem mem_holomorphicHull_of_isBounded_connectedComponentIn [Nontrivial V] {Ω K : Set V}
    (hopen : IsOpen (Ω \ K)) {z : V} (hz : z ∈ Ω \ K)
    (hbdd : IsBounded (connectedComponentIn (Ω \ K) z))
    (hsub : closure (connectedComponentIn (Ω \ K) z) ⊆ Ω) :
    z ∈ holomorphicHull Ω K := by
  -- `frontier C` lies in `K`, where the maximum modulus principle bounds every `f ∈ 𝒪(Ω)`.
  set C := connectedComponentIn (Ω \ K) z
  have hfr : frontier C ⊆ K := fun w hw ↦ by
    have hwΩ : w ∈ Ω := hsub (frontier_subset_closure hw)
    have hwnot : w ∉ Ω \ K := frontier_connectedComponentIn_subset_compl hopen z hw
    exact by_contra fun hwK ↦ hwnot ⟨hwΩ, hwK⟩
  refine ⟨hz.1, fun f hf c hc ↦ ?_⟩
  have hd : DiffContOnCl ℂ f C := ⟨hf.mono (subset_closure.trans hsub), hf.continuousOn.mono hsub⟩
  exact Complex.norm_le_of_forall_mem_frontier_norm_le hbdd hd (fun w hw ↦ hc w (hfr hw))
    (subset_closure (mem_connectedComponentIn hz))

/-- For a closed subset `K` of an open set `Ω` in a nontrivial complex normed space `V`, `K`
together with the relatively compact connected components of `Ω \ K` in `Ω` is contained in
`holomorphicHull Ω K`. -/
theorem _root_.IsClosed.union_setOf_isCompact_closure_connectedComponentIn_subset_holomorphicHull
    [Nontrivial V] {Ω K : Set V} (hK : IsClosed K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) :
    K ∪ {z ∈ Ω \ K | IsCompact (closure (connectedComponentIn (Ω \ K) z)) ∧
      closure (connectedComponentIn (Ω \ K) z) ⊆ Ω} ⊆ holomorphicHull Ω K := by
  rintro z (hzK | ⟨hz, hcpt, hsub⟩)
  · exact subset_holomorphicHull hKΩ hzK
  · exact mem_holomorphicHull_of_isBounded_connectedComponentIn (hΩ.sdiff hK) hz
      (hcpt.isBounded.subset subset_closure) hsub

/-- **Every holomorphic hull in an open set is filled in it**, in a nontrivial complex normed space
`V` (with no assumption on `K`). -/
theorem _root_.IsOpen.isFilledIn_holomorphicHull [Nontrivial V] {Ω : Set V} (hΩ : IsOpen Ω)
    (K : Set V) : IsFilledIn (holomorphicHull Ω K) Ω := by
  rw [isFilledIn_iff]
  rintro z hz ⟨hcpt, hsub⟩
  have hmem := mem_holomorphicHull_of_isBounded_connectedComponentIn
    hΩ.isOpen_sdiff_holomorphicHull hz (hcpt.isBounded.subset subset_closure) hsub
  rw [holomorphicHull_holomorphicHull] at hmem
  exact hz.2 hmem

/-- **Closed convex hull bound on the holomorphic hull.** In any complex normed space `V`,
`holomorphicHull Ω K` is contained in the closed real convex hull `closedConvexHull ℝ K`. -/
theorem holomorphicHull_subset_closedConvexHull (Ω K : Set V) :
    holomorphicHull Ω K ⊆ closedConvexHull ℝ K := by
  -- Separate an exterior point from `closedConvexHull ℝ K` by `re ∘ L` and test `exp ∘ L`.
  intro z hz
  by_contra hzC
  obtain ⟨L, u, huK, huz⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
    (convex_closedConvexHull (𝕜 := ℝ) (s := K)) isClosed_closedConvexHull hzC
  simp only [RCLike.re_to_complex] at huK huz
  have hf : DifferentiableOn ℂ (fun w ↦ Complex.exp (L w)) Ω :=
    L.differentiable.cexp.differentiableOn
  have hle := hz.2 (fun w ↦ Complex.exp (L w)) hf (Real.exp u) fun w hw ↦ by
    rw [Complex.norm_exp, Real.exp_le_exp]
    exact (huK w (subset_closedConvexHull hw)).le
  rw [Complex.norm_exp, Real.exp_le_exp] at hle
  linarith

/-- In a finite-dimensional complex normed space, the holomorphic hull of a compact set `K` lies in
`convexHull ℝ K`. -/
theorem _root_.IsCompact.holomorphicHull_subset_convexHull [FiniteDimensional ℝ V] {Ω K : Set V}
    (hK : IsCompact K) : holomorphicHull Ω K ⊆ convexHull ℝ K :=
  (holomorphicHull_subset_closedConvexHull Ω K).trans
    (closedConvexHull_min (subset_convexHull ℝ K) (convex_convexHull ℝ K)
      (hK.convexHull (𝕜 := ℝ)).isClosed)

end NormedSpace

section ComplexPlane

/-- **Exterior-point distance invariance.** For a nonempty compact set `K` inside `Ω ⊆ ℂ` and any
point `ζ ∉ Ω`, `holomorphicHull Ω K` has the same distance to `ζ` as `K`. -/
theorem _root_.IsCompact.infDist_holomorphicHull_eq {Ω K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hKne : K.Nonempty) {ζ : ℂ} (hζ : ζ ∉ Ω) :
    infDist ζ (holomorphicHull Ω K) = infDist ζ K := by
  -- Test `w ↦ (w - ζ)⁻¹`, which is holomorphic on `Ω`.
  refine le_antisymm (infDist_le_infDist_of_subset (subset_holomorphicHull hKΩ) hKne) ?_
  obtain ⟨w₀, hw₀, hw₀d⟩ := hK.exists_infDist_eq_dist hKne ζ
  have hw₀_pos : 0 < dist ζ w₀ := dist_pos.2 fun h ↦ hζ (h ▸ hKΩ hw₀)
  have hf : DifferentiableOn ℂ (fun w : ℂ ↦ (w - ζ)⁻¹) Ω :=
    (differentiableOn_id.sub (differentiableOn_const ζ)).inv fun w hw h0 ↦
      hζ ((sub_eq_zero.1 h0 : w = ζ) ▸ hw)
  refine (le_infDist (hKne.mono (subset_holomorphicHull hKΩ))).2 fun z hz ↦ ?_
  have hz_pos : 0 < dist ζ z := dist_pos.2 fun h ↦ hζ (h ▸ hz.1)
  have hle := hz.2 (fun w : ℂ ↦ (w - ζ)⁻¹) hf (dist ζ w₀)⁻¹ fun w hw ↦ by
    rw [norm_inv, ← dist_eq_norm, dist_comm]
    exact inv_anti₀ hw₀_pos (hw₀d ▸ infDist_le_dist_of_mem hw)
  rw [norm_inv, ← dist_eq_norm, dist_comm] at hle
  exact hw₀d.trans_le ((inv_le_inv₀ hz_pos hw₀_pos).1 hle)

/-- Extended-distance form of `IsCompact.infDist_holomorphicHull_eq`, valid also when `K = ∅`. -/
theorem _root_.IsCompact.infEDist_holomorphicHull_eq {Ω K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {ζ : ℂ} (hζ : ζ ∉ Ω) :
    infEDist ζ (holomorphicHull Ω K) = infEDist ζ K := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · simp
  have hHne : (holomorphicHull Ω K).Nonempty := hKne.mono (subset_holomorphicHull hKΩ)
  rw [← ENNReal.ofReal_toReal (infEDist_ne_top hHne),
    ← ENNReal.ofReal_toReal (infEDist_ne_top hKne)]
  exact congrArg ENNReal.ofReal (hK.infDist_holomorphicHull_eq hKΩ hKne hζ)

/-- **Boundary-distance invariance of the holomorphic hull in `ℂ`.** For any compact `K ⊆ Ω`,
`\operatorname{dist}(\widehat{K}_Ω, Ωᶜ) = \operatorname{dist}(K, Ωᶜ)`. -/
theorem _root_.IsCompact.biInf_infEDist_compl_holomorphicHull_eq {Ω K : Set ℂ} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) :
    (⨅ z ∈ holomorphicHull Ω K, infEDist z Ωᶜ) = ⨅ z ∈ K, infEDist z Ωᶜ := by
  refine le_antisymm (biInf_mono (subset_holomorphicHull hKΩ)) ?_
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · simp
  refine le_iInf₂ fun z hz ↦ le_infEDist.2 fun ζ hζ ↦ ?_
  obtain ⟨w₀, hw₀, hw₀d⟩ := hK.exists_infEDist_eq_edist hKne ζ
  calc (⨅ w ∈ K, infEDist w Ωᶜ)
      ≤ infEDist w₀ Ωᶜ := biInf_le _ hw₀
    _ ≤ edist w₀ ζ := infEDist_le_edist_of_mem hζ
    _ = infEDist ζ (holomorphicHull Ω K) := by
        rw [edist_comm, ← hw₀d, hK.infEDist_holomorphicHull_eq hKΩ hζ]
    _ ≤ edist z ζ := by rw [edist_comm]; exact infEDist_le_edist_of_mem hz

/-- **Compactness of the holomorphic hull in `ℂ`.** For a compact subset `K` of an open set
`Ω ⊆ ℂ`, `holomorphicHull Ω K` is compact. -/
theorem _root_.IsCompact.isCompact_holomorphicHull {Ω K : Set ℂ} (hK : IsCompact K)
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) : IsCompact (holomorphicHull Ω K) := by
  -- Bounded by `closedConvexHull ℝ K`, relatively closed in `Ω`, and bounded away from `Ωᶜ`.
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · simp
  refine Metric.isCompact_iff_isClosed_bounded.2 ⟨?_,
    (isBounded_closedConvexHull.2 hK.isBounded).subset
      (holomorphicHull_subset_closedConvexHull Ω K)⟩
  rw [← closure_subset_iff_isClosed]
  intro ζ hζcl
  by_cases hζΩ : ζ ∈ Ω
  · by_contra hζH
    obtain ⟨w, hwDiff, hwH⟩ :=
      mem_closure_iff.1 hζcl (Ω \ holomorphicHull Ω K) hΩ.isOpen_sdiff_holomorphicHull ⟨hζΩ, hζH⟩
    exact hwDiff.2 hwH
  · exfalso
    obtain ⟨w₀, hw₀, hw₀d⟩ := hK.exists_infDist_eq_dist hKne ζ
    have hpos : 0 < dist ζ w₀ := dist_pos.2 fun h ↦ hζΩ (h ▸ hKΩ hw₀)
    have hzero : infDist ζ (holomorphicHull Ω K) = 0 := infDist_zero_of_mem_closure hζcl
    rw [hK.infDist_holomorphicHull_eq hKΩ hKne hζΩ, hw₀d] at hzero
    exact hpos.ne' hzero

/-- **Entire hull equals one-variable polynomial hull.** For compact `K ⊆ ℂ`, a point `z` belongs to
`holomorphicHull univ K` if and only if every complex polynomial `P : ℂ[X]` bounded by `c` on `K`
satisfies `‖P.eval z‖ ≤ c`. -/
theorem _root_.IsCompact.mem_holomorphicHull_univ_iff_forall_polynomial {K : Set ℂ}
    (hK : IsCompact K) {z : ℂ} :
    z ∈ holomorphicHull univ K ↔
      ∀ (P : ℂ[X]) (c : ℝ), (∀ w ∈ K, ‖P.eval w‖ ≤ c) → ‖P.eval z‖ ≤ c := by
  refine ⟨fun hz P c hc ↦ hz.2 (fun w ↦ P.eval w) P.differentiableOn c hc,
    fun hP ↦ ⟨trivial, fun f hf c hc ↦ le_of_forall_pos_lt_add fun ε hε ↦ ?_⟩⟩
  obtain ⟨P, hPapprox⟩ :=
    (differentiableOn_univ.1 hf).exists_polynomial_norm_sub_lt (hK.insert z) (half_pos hε)
  have hPK : ∀ w ∈ K, ‖P.eval w‖ ≤ c + ε / 2 := fun w hw ↦ by
    have hw' := hPapprox w (mem_insert_of_mem z hw)
    calc ‖P.eval w‖ = ‖f w - (f w - P.eval w)‖ := by ring_nf
      _ ≤ ‖f w‖ + ‖f w - P.eval w‖ := norm_sub_le _ _
      _ ≤ c + ε / 2 := add_le_add (hc w hw) hw'.le
  have hPz : ‖P.eval z‖ ≤ c + ε / 2 := hP P (c + ε / 2) hPK
  have hz' := hPapprox z (mem_insert z K)
  calc ‖f z‖ = ‖P.eval z + (f z - P.eval z)‖ := by ring_nf
    _ ≤ ‖P.eval z‖ + ‖f z - P.eval z‖ := norm_add_le _ _
    _ < (c + ε / 2) + ε / 2 := add_lt_add_of_le_of_lt hPz hz'
    _ = c + ε := by ring

/-- Under the diagonal embedding `Function.const ι : ℂ → (ι → ℂ)` for any nonempty index type `ι`,
the pullback of `TauCeti.polynomialHull (Function.const ι '' K)` is `holomorphicHull univ K`. -/
theorem _root_.IsCompact.holomorphicHull_univ_eq_preimage_polynomialHull {ι : Type*} [Nonempty ι]
    {K : Set ℂ} (hK : IsCompact K) :
    holomorphicHull univ K = Function.const ι ⁻¹' polynomialHull (Function.const ι '' K) := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  ext z
  rw [mem_preimage, mem_polynomialHull_iff, hK.mem_holomorphicHull_univ_iff_forall_polynomial]
  constructor
  · intro h p c hc
    set P : ℂ[X] := MvPolynomial.aeval (fun _ : ι ↦ Polynomial.X) p
    have heval (w : ℂ) : P.eval w = MvPolynomial.eval (Function.const ι w) p := by
      simp [P, ← Polynomial.coe_aeval_eq_eval, MvPolynomial.comp_aeval_apply,
        MvPolynomial.aeval_eq_eval]
      rfl
    rw [← heval]
    refine h P c fun w hw ↦ ?_
    rw [heval]
    exact hc _ (mem_image_of_mem _ hw)
  · intro h P c hc
    set p : MvPolynomial ι ℂ := Polynomial.aeval (MvPolynomial.X i₀) P
    have heval (w : ℂ) : MvPolynomial.eval (Function.const ι w) p = P.eval w := by
      simp [p, ← MvPolynomial.aeval_eq_eval, ← Polynomial.aeval_algHom_apply,
        Polynomial.coe_aeval_eq_eval]
    rw [← heval]
    refine h p c ?_
    rintro _ ⟨w, hw, rfl⟩
    rw [heval]
    exact hc w hw

/-- For a one-element index type `ι`, the image of a compact set `K ⊆ ℂ` in `ι → ℂ` is polynomially
convex (`TauCeti.IsPolynomiallyConvex`) if and only if `holomorphicHull univ K = K`. -/
theorem _root_.IsCompact.isPolynomiallyConvex_image_const_iff {ι : Type*} [Unique ι] {K : Set ℂ}
    (hK : IsCompact K) :
    IsPolynomiallyConvex (Function.const ι '' K) ↔ holomorphicHull univ K = K := by
  have hinj : Function.Injective (Function.const ι : ℂ → ι → ℂ) := Function.const_injective
  have hsurj (u : ι → ℂ) : Function.const ι (u default) = u :=
    funext fun i ↦ congrArg u (Unique.eq_default i).symm
  constructor
  · intro hconv
    refine Subset.antisymm (fun z hz ↦ ?_) (subset_holomorphicHull (subset_univ K))
    rw [hK.holomorphicHull_univ_eq_preimage_polynomialHull (ι := ι)] at hz
    obtain ⟨w, hw, hwz⟩ := isPolynomiallyConvex_iff.1 hconv hz
    exact hinj hwz ▸ hw
  · intro hHull
    refine isPolynomiallyConvex_iff.2 fun u hu ↦ ?_
    have hm : u default ∈ Function.const ι ⁻¹' polynomialHull (Function.const ι '' K) := by
      simpa only [mem_preimage, hsurj u] using hu
    rw [← hK.holomorphicHull_univ_eq_preimage_polynomialHull (ι := ι), hHull] at hm
    exact ⟨u default, hm, hsurj u⟩

end ComplexPlane

end TauCeti
