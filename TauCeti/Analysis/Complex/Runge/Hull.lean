/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Convex.Topology
public import TauCeti.Analysis.Complex.PolynomialHull.Basic
public import TauCeti.Analysis.Normed.Module.Exhaustion
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.LocallyConvex.Separation
import TauCeti.Algebra.MvPolynomial.AevalConstX
import TauCeti.Analysis.Convex.Caratheodory
import TauCeti.Analysis.Normed.Module.HausdorffDistance
import TauCeti.Topology.ConnectedComponents
import TauCeti.Topology.MetricSpace.HausdorffDistance

/-!
# Holomorphic hulls in the complex plane

In complex analysis on an arbitrary open set `Ω ⊆ ℂ`, a compact subset `K ⊆ Ω` forms a *Runge
compact pair* `(Ω, K)` (`TauCeti.IsRungeCompactPair Ω K`, in
`TauCeti.Analysis.Complex.Runge.CompactPair`) when `K` is filled in `Ω`, i.e. no connected component
of `Ω \ K` is relatively compact in `Ω`. These are precisely the compact subsets on which every
function holomorphic in a neighbourhood of `K` can be uniformly approximated by functions
holomorphic on all of `Ω` (Runge's approximation theorem, in
`TauCeti.Analysis.Complex.Runge.Approximation`).

Alongside this topological condition sits the *`Ω`-holomorphic hull* `TauCeti.holomorphicHull Ω K`,
consisting of all points `z ∈ Ω` at which every real upper bound satisfied on `K` by an
`Ω`-holomorphic function remains valid. The hull records the points of `Ω` that cannot be separated
from `K` by the modulus of an `Ω`-holomorphic function. By the maximum modulus principle, every
relatively compact connected component of `Ω \ K` in `Ω` lies in `holomorphicHull Ω K`; the reverse
inclusion (showing that `holomorphicHull Ω K` equals `K` together with the relatively compact
components of `Ω \ K` for compact `K ⊆ Ω`, and hence that `IsRungeCompactPair Ω K` is equivalent
to `holomorphicHull Ω K = K`) depends on Runge approximation and is proved in
`TauCeti.Analysis.Complex.Runge.Approximation`.

Without invoking any approximation theorem, this file establishes the basic geometric, metric, and
topological properties of `holomorphicHull Ω K`:

* **Extensivity, normal forms, monotonicity, and idempotence**: `K ∩ Ω ⊆ holomorphicHull Ω K`,
  `holomorphicHull Ω (K ∩ Ω) = holomorphicHull Ω K`, `holomorphicHull Ω K = ∅ ↔ Disjoint K Ω`,
  monotonicity in both arguments, idempotence, strict modulus separation outside the hull, and the
  compact supremum characterization `IsCompact.mem_holomorphicHull_iff_norm_le_sSup`.
* **Distance preservation, closedness, and compactness**: for `z ∈ holomorphicHull Ω K` and
  `ζ ∉ Ω`, testing against `w ↦ (w - ζ)⁻¹` yields `infEDist ζ K ≤ edist z ζ`, whence
  `holomorphicHull Ω K` and `K` have the same extended and ordinary distances to `Ωᶜ` and
  `frontier Ω` whenever `K ⊆ Ω`. Together with relative closedness
  (`closure (holomorphicHull Ω K) ∩ Ω = holomorphicHull Ω K`) and boundedness via `id`, this shows
  that `holomorphicHull Ω K` is closed whenever `closure K ⊆ Ω` and compact whenever `K` is bounded
  with `closure K ⊆ Ω` (in particular for closed or compact `K ⊆ Ω`).
* **Convex hull bound**: geometric Hahn–Banach separation combined with complex exponentials
  `w ↦ exp (l w)` gives `holomorphicHull Ω K ⊆ closedConvexHull ℝ K` unconditionally, hence
  `holomorphicHull Ω K = K ∩ Ω` for every closed real-convex `K` (`Convex.holomorphicHull_eq_inter`)
  and `holomorphicHull Ω K ⊆ convexHull ℝ K` for compact `K`.
* **Maximum-principle inclusion and filledness**: in an open `Ω`, every connected component of
  `Ω \ K` whose closure is compact and contained in `Ω` has frontier in `closure K` and therefore
  lies inside `holomorphicHull Ω K`. Combined with idempotence, `holomorphicHull Ω K` is always
  filled in `Ω` (`IsOpen.isFilledIn_holomorphicHull`).
* **Comparison with polynomial hulls on `ℂ`**: for `Ω = univ` and bounded `K ⊆ ℂ`, uniform Taylor
  approximation of entire functions on disks identifies `holomorphicHull univ K` with the preimage
  of `TauCeti.polynomialHull (Function.const ι '' K)` under the diagonal embedding
  `Function.const ι : ℂ → (ι → ℂ)` for any nonempty index type `ι` (in particular for `ι = Fin 1`,
  where `Function.const (Fin 1)` is `⇑(ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ).symm`). The
  closed unbounded line `ℝ ⊆ ℂ` has `holomorphicHull univ ℝ = ℝ` whereas its univariate polynomial
  hull is `univ` (`TauCeti.polynomialHull_image_const_range_ofReal`), showing that boundedness is
  essential.

## Main declarations

* `TauCeti.holomorphicHull`: the `Ω`-holomorphic hull of `K ⊆ ℂ`.
* `TauCeti.isClosed_holomorphicHull_of_closure_subset`, `IsClosed.holomorphicHull`,
  `Bornology.IsBounded.holomorphicHull`,
  `Bornology.IsBounded.isCompact_holomorphicHull_of_closure_subset`, and
  `IsCompact.holomorphicHull`: closedness, boundedness, and compactness of the holomorphic hull.
* `TauCeti.biInf_holomorphicHull_edist_compl` and
  `TauCeti.sInf_image_infDist_frontier_holomorphicHull`: preservation of distances to `Ωᶜ` and
  `frontier Ω`.
* `TauCeti.holomorphicHull_subset_closedConvexHull`, `IsCompact.holomorphicHull_subset_convexHull`,
  `Convex.holomorphicHull_eq_inter`, and `Convex.holomorphicHull_eq`: comparison with real convex
  hulls.
* `IsOpen.connectedComponentIn_sdiff_subset_holomorphicHull`,
  `IsOpen.fillIn_subset_holomorphicHull`, and
  `IsOpen.isFilledIn_holomorphicHull`: maximum-principle inclusion of relatively compact
  complementary components and filledness of the hull.
* `Bornology.IsBounded.holomorphicHull_univ_eq_preimage_polynomialHull` and
  `Bornology.IsBounded.holomorphicHull_univ_eq_self_iff_isPolynomiallyConvex`: agreement of
  `holomorphicHull univ K` with `TauCeti.polynomialHull` for bounded `K`.

## References

* A. Rainer, *Advanced Complex Analysis*, Lemma 11.3 and Theorem 12.1.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., §1.3 and §2.7.
-/

public section

open Bornology Filter Metric Set
open scoped Topology ENNReal NNReal

namespace TauCeti

/-! ### Definition and elementary properties of the holomorphic hull -/

/-- The `Ω`-holomorphic hull of `K ⊆ ℂ`: the points `z ∈ Ω` at which every real upper bound
satisfied on `K` by an `Ω`-holomorphic function continues to hold. Quantifying over all real bounds
`B` makes the hull of the empty set empty. -/
def holomorphicHull (Ω K : Set ℂ) : Set ℂ :=
  {z | z ∈ Ω ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f Ω →
    ∀ B : ℝ, (∀ w ∈ K, ‖f w‖ ≤ B) → ‖f z‖ ≤ B}

theorem holomorphicHull_def (Ω K : Set ℂ) :
    holomorphicHull Ω K =
      {z | z ∈ Ω ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f Ω →
        ∀ B : ℝ, (∀ w ∈ K, ‖f w‖ ≤ B) → ‖f z‖ ≤ B} :=
  (rfl)

theorem mem_holomorphicHull_iff {Ω K : Set ℂ} {z : ℂ} :
    z ∈ holomorphicHull Ω K ↔
      z ∈ Ω ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f Ω →
        ∀ B : ℝ, (∀ w ∈ K, ‖f w‖ ≤ B) → ‖f z‖ ≤ B :=
  (Iff.rfl)

/-- The `Ω`-holomorphic hull of any set lies in `Ω`. -/
theorem holomorphicHull_subset_left (Ω K : Set ℂ) : holomorphicHull Ω K ⊆ Ω :=
  fun _ hz ↦ (mem_holomorphicHull_iff.mp hz).1

/-- Every upper bound `B` satisfied on `K` by an `Ω`-holomorphic function `f` holds at every point
of `holomorphicHull Ω K`. -/
theorem norm_le_of_mem_holomorphicHull {Ω K : Set ℂ} {z : ℂ} (hz : z ∈ holomorphicHull Ω K)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω) {B : ℝ} (hB : ∀ w ∈ K, ‖f w‖ ≤ B) :
    ‖f z‖ ≤ B :=
  (mem_holomorphicHull_iff.mp hz).2 f hf B hB

/-- Every point of `K ∩ Ω` lies in `holomorphicHull Ω K`. -/
theorem inter_subset_holomorphicHull (Ω K : Set ℂ) : K ∩ Ω ⊆ holomorphicHull Ω K :=
  fun _ hz ↦ mem_holomorphicHull_iff.mpr ⟨hz.2, fun _ _ _ hB ↦ hB _ hz.1⟩

/-- For `K ⊆ Ω`, `K` lies in its `Ω`-holomorphic hull. -/
theorem subset_holomorphicHull {Ω K : Set ℂ} (hKΩ : K ⊆ Ω) : K ⊆ holomorphicHull Ω K :=
  (subset_inter Subset.rfl hKΩ).trans (inter_subset_holomorphicHull Ω K)

/-- Monotonicity of `holomorphicHull` in the second argument. -/
@[gcongr]
theorem holomorphicHull_mono {Ω K L : Set ℂ} (h : K ⊆ L) :
    holomorphicHull Ω K ⊆ holomorphicHull Ω L :=
  fun _ hz ↦ mem_holomorphicHull_iff.mpr
    ⟨holomorphicHull_subset_left Ω K hz, fun _ hf _ hB ↦
      norm_le_of_mem_holomorphicHull hz hf fun w hw ↦ hB w (h hw)⟩

/-- Monotonicity of `holomorphicHull` in the ambient domain `Ω`. -/
@[gcongr]
theorem holomorphicHull_mono_left {Ω₁ Ω₂ K : Set ℂ} (h : Ω₁ ⊆ Ω₂) :
    holomorphicHull Ω₁ K ⊆ holomorphicHull Ω₂ K :=
  fun _ hz ↦ mem_holomorphicHull_iff.mpr
    ⟨h (holomorphicHull_subset_left Ω₁ K hz), fun _ hf _ hB ↦
      norm_le_of_mem_holomorphicHull hz (hf.mono h) hB⟩

@[simp]
theorem holomorphicHull_empty_left (K : Set ℂ) : holomorphicHull ∅ K = ∅ :=
  subset_empty_iff.mp (holomorphicHull_subset_left ∅ K)

@[simp]
theorem holomorphicHull_empty (Ω : Set ℂ) : holomorphicHull Ω ∅ = ∅ :=
  eq_empty_of_forall_notMem fun _ hz ↦
    (norm_le_of_mem_holomorphicHull hz (differentiableOn_const (0 : ℂ)) (B := -1)
      (by simp)).not_gt (by norm_num)

@[simp]
theorem holomorphicHull_self (Ω : Set ℂ) : holomorphicHull Ω Ω = Ω :=
  Subset.antisymm (holomorphicHull_subset_left Ω Ω) (subset_holomorphicHull Subset.rfl)

@[simp]
theorem holomorphicHull_univ (Ω : Set ℂ) : holomorphicHull Ω univ = Ω :=
  Subset.antisymm (holomorphicHull_subset_left Ω univ)
    (by simpa using inter_subset_holomorphicHull Ω univ)

/-- The `Ω`-holomorphic hull of `K` is empty if and only if `K` is disjoint from `Ω`. -/
@[simp]
theorem holomorphicHull_eq_empty (Ω K : Set ℂ) : holomorphicHull Ω K = ∅ ↔ Disjoint K Ω := by
  refine ⟨fun h ↦ disjoint_iff_inter_eq_empty.mpr
    (subset_empty_iff.mp (h ▸ inter_subset_holomorphicHull Ω K)), fun hdisj ↦ ?_⟩
  classical
  refine eq_empty_of_forall_notMem fun z hz ↦ ?_
  let g : ℂ → ℂ := fun w ↦ if w ∈ Ω then 1 else 0
  have hg : DifferentiableOn ℂ g Ω :=
    (differentiableOn_const 1).congr fun w hw ↦ by simp [g, hw]
  have hle : ‖g z‖ ≤ 0 := norm_le_of_mem_holomorphicHull hz hg fun w hw ↦ by
    simp [g, disjoint_left.mp hdisj hw]
  exact not_le.mpr zero_lt_one (by simpa [g, holomorphicHull_subset_left Ω K hz] using hle)

/-- The `Ω`-holomorphic hull of `K` is nonempty if and only if `K ∩ Ω` is nonempty. -/
@[simp]
theorem holomorphicHull_nonempty_iff (Ω K : Set ℂ) :
    (holomorphicHull Ω K).Nonempty ↔ (K ∩ Ω).Nonempty := by
  rw [← ne_empty_iff_nonempty, ← ne_empty_iff_nonempty, ne_eq, ne_eq, holomorphicHull_eq_empty,
    disjoint_iff_inter_eq_empty]

/-- Points of `K` outside `Ω` do not affect `holomorphicHull Ω K`. -/
@[simp]
theorem holomorphicHull_inter_self (Ω K : Set ℂ) :
    holomorphicHull Ω (K ∩ Ω) = holomorphicHull Ω K := by
  refine Subset.antisymm (holomorphicHull_mono inter_subset_left) fun z hz ↦ ?_
  rw [mem_holomorphicHull_iff]
  refine ⟨holomorphicHull_subset_left Ω K hz, fun f hf B hB ↦ ?_⟩
  rcases (K ∩ Ω).eq_empty_or_nonempty with hempty | ⟨w₀, hw₀⟩
  · have hdisj : Disjoint K Ω := disjoint_iff_inter_eq_empty.mpr hempty
    exact ((holomorphicHull_eq_empty Ω K).mpr hdisj ▸ hz).elim
  · have hB0 : 0 ≤ B := (norm_nonneg (f w₀)).trans (hB w₀ hw₀)
    classical
    let g : ℂ → ℂ := fun w ↦ if w ∈ Ω then f w else 0
    have hg : DifferentiableOn ℂ g Ω := hf.congr fun w hw ↦ by simp [g, hw]
    have hle : ‖g z‖ ≤ B := norm_le_of_mem_holomorphicHull hz hg fun w hw ↦ by
      by_cases hwΩ : w ∈ Ω
      · simpa [g, hwΩ] using hB w ⟨hw, hwΩ⟩
      · simpa [g, hwΩ] using hB0
    simpa [g, holomorphicHull_subset_left Ω K hz] using hle

/-- Taking the `Ω`-holomorphic hull is idempotent. -/
@[simp]
theorem holomorphicHull_holomorphicHull (Ω K : Set ℂ) :
    holomorphicHull Ω (holomorphicHull Ω K) = holomorphicHull Ω K :=
  (subset_holomorphicHull (holomorphicHull_subset_left Ω K)).antisymm' fun _ hz ↦
    mem_holomorphicHull_iff.mpr ⟨holomorphicHull_subset_left Ω _ hz, fun _ hf _ hB ↦
      norm_le_of_mem_holomorphicHull hz hf fun _ hw ↦ norm_le_of_mem_holomorphicHull hw hf hB⟩

/-- A point `z ∈ Ω` outside `holomorphicHull Ω K` is strictly separated from `K` by an
`Ω`-holomorphic function of modulus `< 1` on `K` and `> 1` at `z`. -/
theorem exists_differentiableOn_norm_lt_one_lt_of_notMem_holomorphicHull {Ω K : Set ℂ} {z : ℂ}
    (hzΩ : z ∈ Ω) (hz : z ∉ holomorphicHull Ω K) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Ω ∧ (∀ w ∈ K, ‖f w‖ < 1) ∧ 1 < ‖f z‖ := by
  rw [mem_holomorphicHull_iff] at hz
  push Not at hz
  obtain ⟨f, hf, B, hfK, hBz⟩ := hz hzΩ
  set s := ‖f z‖
  rcases (norm_nonneg (f z)).eq_or_lt with hs | hs
  · have hK : ∀ w ∈ K, False := fun w hw ↦
      ((norm_nonneg _).trans (hfK w hw)).not_gt (hs ▸ hBz)
    exact ⟨fun _ ↦ 2, differentiableOn_const 2, fun w hw ↦ (hK w hw).elim, by norm_num⟩
  set a := max B (s / 2)
  have has : a < s := max_lt hBz (half_lt_self hs)
  have hr : 0 < 2 / (a + s) := by positivity
  have hnorm (w : ℂ) : ‖((2 / (a + s) : ℝ) : ℂ) * f w‖ = 2 * ‖f w‖ / (a + s) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le, div_mul_eq_mul_div]
  refine ⟨fun w ↦ ((2 / (a + s) : ℝ) : ℂ) * f w, hf.const_mul _, fun w hw ↦ ?_, ?_⟩
  · rw [hnorm, div_lt_one (by positivity)]
    linarith [(hfK w hw).trans (le_max_left B (s / 2))]
  · rw [hnorm, one_lt_div (by positivity)]
    linarith

/-- A subset `K ⊆ Ω` equals its `Ω`-holomorphic hull if and only if every point of `Ω \ K` is
strictly separated from `K` by an `Ω`-holomorphic function of modulus `< 1` on `K` and `> 1` at
the point. -/
theorem holomorphicHull_eq_self_iff_forall_mem_sdiff_exists_differentiableOn_norm_lt_one_lt
    {Ω K : Set ℂ} (hKΩ : K ⊆ Ω) :
    holomorphicHull Ω K = K ↔
      ∀ z ∈ Ω \ K, ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Ω ∧ (∀ w ∈ K, ‖f w‖ < 1) ∧ 1 < ‖f z‖ := by
  refine ⟨fun h z hz ↦ exists_differentiableOn_norm_lt_one_lt_of_notMem_holomorphicHull hz.1
    (h.symm ▸ hz.2), fun h ↦ Subset.antisymm (fun z hz ↦ by_contra fun hzK ↦ ?_)
    (subset_holomorphicHull hKΩ)⟩
  obtain ⟨f, hf, hfK, hfz⟩ := h z ⟨holomorphicHull_subset_left Ω K hz, hzK⟩
  exact (norm_le_of_mem_holomorphicHull hz hf fun w hw ↦ (hfK w hw).le).not_gt hfz

/-- For compact `K ⊆ Ω`, membership in `holomorphicHull Ω K` is equivalent to the supremum bound
`‖f z‖ ≤ sSup ((‖f ·‖) '' K)` for every `Ω`-holomorphic `f` (including `K = ∅`, where `sSup ∅ = 0`).
-/
theorem _root_.IsCompact.mem_holomorphicHull_iff_norm_le_sSup {Ω K : Set ℂ}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) {z : ℂ} :
    z ∈ holomorphicHull Ω K ↔
      z ∈ Ω ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f Ω → ‖f z‖ ≤ sSup ((fun w ↦ ‖f w‖) '' K) := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp only [holomorphicHull_empty, mem_empty_iff_false, image_empty, Real.sSup_empty, false_iff,
      not_and, not_forall, not_le]
    exact fun _ ↦ ⟨fun _ ↦ 1, differentiableOn_const 1, by simp⟩
  · refine ⟨fun hz ↦ ⟨holomorphicHull_subset_left Ω K hz, fun f hf ↦ ?_⟩, fun ⟨hzΩ, hz⟩ ↦ ?_⟩
    · have hbdd : BddAbove ((fun w ↦ ‖f w‖) '' K) :=
        (hK.image_of_continuousOn (hf.continuousOn.mono hKΩ).norm).bddAbove
      exact norm_le_of_mem_holomorphicHull hz hf fun w hw ↦ le_csSup hbdd (mem_image_of_mem _ hw)
    · rw [mem_holomorphicHull_iff]
      exact ⟨hzΩ, fun f hf B hB ↦
        (hz f hf).trans (csSup_le (hne.image _) (forall_mem_image.mpr hB))⟩

/-- For compact `K ⊆ Ω`, every `Ω`-holomorphic function `f` satisfies
`‖f z‖ ≤ sSup ((‖f ·‖) '' K)` at each point `z ∈ holomorphicHull Ω K`. -/
theorem _root_.IsCompact.norm_le_sSup_of_mem_holomorphicHull {Ω K : Set ℂ}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) {z : ℂ} (hz : z ∈ holomorphicHull Ω K)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω) :
    ‖f z‖ ≤ sSup ((fun w ↦ ‖f w‖) '' K) :=
  ((hK.mem_holomorphicHull_iff_norm_le_sSup hKΩ).mp hz).2 f hf

/-- If an `Ω`-holomorphic function `f` is strictly smaller in modulus at every point of a compact
set `K ⊆ Ω` than at `z`, then `z` is not in `holomorphicHull Ω K`. -/
theorem _root_.IsCompact.notMem_holomorphicHull_of_forall_norm_lt {Ω K : Set ℂ}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) {z : ℂ} {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω)
    (h : ∀ w ∈ K, ‖f w‖ < ‖f z‖) :
    z ∉ holomorphicHull Ω K := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨w₀, hw₀, hmax⟩ := hK.exists_isMaxOn hne (hf.continuousOn.mono hKΩ).norm
  exact fun hz ↦ (norm_le_of_mem_holomorphicHull hz hf fun w hw ↦ hmax hw).not_gt (h w₀ hw₀)

/-! ### Distance to the complement, relative closedness, and compactness -/

/-- No point of `holomorphicHull Ω K` lies closer in extended distance to `ζ ∉ Ω` than `K` does. -/
theorem infEDist_le_edist_of_mem_holomorphicHull {Ω K : Set ℂ} {z ζ : ℂ}
    (hz : z ∈ holomorphicHull Ω K) (hζ : ζ ∉ Ω) :
    infEDist ζ K ≤ edist z ζ := by
  -- Test against `w ↦ (w - ζ)⁻¹`, which is holomorphic on `Ω`.
  by_contra hlt
  rw [not_le] at hlt
  have hKne : K.Nonempty := ne_empty_iff_nonempty.mp fun h ↦ by simp [h] at hz
  have hzζ : z ≠ ζ := fun h ↦ hζ (h ▸ holomorphicHull_subset_left Ω K hz)
  have hd_pos : 0 < dist z ζ := dist_pos.mpr hzζ
  have hm_ne_top : infEDist ζ K ≠ ∞ := infEDist_ne_top hKne
  set m := (infEDist ζ K).toReal
  have hdm : dist z ζ < m := by
    rw [edist_dist] at hlt
    exact (ENNReal.ofReal_lt_iff_lt_toReal hd_pos.le hm_ne_top).mp hlt
  have hm_pos : 0 < m := hd_pos.trans hdm
  have hf : DifferentiableOn ℂ (fun w : ℂ ↦ (w - ζ)⁻¹) Ω :=
    (differentiableOn_id.sub (differentiableOn_const ζ)).inv fun w hw ↦
      sub_ne_zero.mpr fun h : w = ζ ↦ hζ (h ▸ hw)
  have hbound : ∀ w ∈ K, ‖(w - ζ)⁻¹‖ ≤ m⁻¹ := fun w hw ↦ by
    have hmw : m ≤ ‖w - ζ‖ := by
      rw [← dist_eq_norm, dist_comm]
      exact infDist_le_dist_of_mem hw
    rw [norm_inv]
    exact inv_anti₀ hm_pos hmw
  have hz_le := norm_le_of_mem_holomorphicHull hz hf hbound
  rw [norm_inv, ← dist_eq_norm] at hz_le
  exact hdm.not_ge ((inv_le_inv₀ hd_pos hm_pos).mp hz_le)

/-- Ordinary-distance form of `TauCeti.infEDist_le_edist_of_mem_holomorphicHull`. -/
theorem infDist_le_dist_of_mem_holomorphicHull {Ω K : Set ℂ} {z ζ : ℂ}
    (hz : z ∈ holomorphicHull Ω K) (hζ : ζ ∉ Ω) :
    infDist ζ K ≤ dist z ζ := by
  rw [infDist, dist_edist]
  exact ENNReal.toReal_mono (edist_ne_top z ζ) (infEDist_le_edist_of_mem_holomorphicHull hz hζ)

/-- For `K ⊆ Ω`, `holomorphicHull Ω K` and `K` have the same extended set distance to `Ωᶜ`
(including `∞` when `K = ∅` or `Ω = univ`). -/
theorem biInf_holomorphicHull_edist_compl {Ω K : Set ℂ} (hKΩ : K ⊆ Ω) :
    (⨅ z ∈ holomorphicHull Ω K, ⨅ ζ ∈ Ωᶜ, edist z ζ) = ⨅ z ∈ K, ⨅ ζ ∈ Ωᶜ, edist z ζ := by
  refine le_antisymm (biInf_mono (subset_holomorphicHull hKΩ)) ?_
  refine le_iInf₂ fun z hz ↦ le_iInf₂ fun ζ hζ ↦ ?_
  refine le_trans ?_ (infEDist_le_edist_of_mem_holomorphicHull hz hζ)
  exact le_infEDist.mpr fun w hw ↦
    (iInf₂_le w hw).trans ((iInf₂_le ζ hζ).trans_eq (edist_comm w ζ))

/-- For `K ⊆ Ω`, `holomorphicHull Ω K` and `K` have the same extended set distance to `frontier Ω`.
-/
theorem biInf_holomorphicHull_edist_frontier {Ω K : Set ℂ} (hKΩ : K ⊆ Ω) :
    (⨅ z ∈ holomorphicHull Ω K, ⨅ ζ ∈ frontier Ω, edist z ζ) =
      ⨅ z ∈ K, ⨅ ζ ∈ frontier Ω, edist z ζ := by
  have hpoint {z : ℂ} (hz : z ∈ Ω) :
      (⨅ ζ ∈ frontier Ω, edist z ζ) = ⨅ ζ ∈ Ωᶜ, edist z ζ := by
    simpa only [Metric.infEDist] using
      Metric.infEDist_frontier_of_mem_closure (subset_closure hz)
  calc
    (⨅ z ∈ holomorphicHull Ω K, ⨅ ζ ∈ frontier Ω, edist z ζ)
        = ⨅ z ∈ holomorphicHull Ω K, ⨅ ζ ∈ Ωᶜ, edist z ζ :=
      iInf_congr fun z ↦ iInf_congr fun hz ↦ hpoint (holomorphicHull_subset_left Ω K hz)
    _ = ⨅ z ∈ K, ⨅ ζ ∈ Ωᶜ, edist z ζ := biInf_holomorphicHull_edist_compl hKΩ
    _ = ⨅ z ∈ K, ⨅ ζ ∈ frontier Ω, edist z ζ :=
      iInf_congr fun z ↦ iInf_congr fun hz ↦ (hpoint (hKΩ hz)).symm

/-- For `K ⊆ Ω`, `holomorphicHull Ω K` and `K` have the same ordinary distance to `Ωᶜ`. -/
theorem sInf_image_infDist_compl_holomorphicHull {Ω K : Set ℂ} (hKΩ : K ⊆ Ω) :
    sInf ((fun z ↦ infDist z Ωᶜ) '' holomorphicHull Ω K) =
      sInf ((fun z ↦ infDist z Ωᶜ) '' K) := by
  rw [Metric.sInf_image_infDist_eq_toReal_biInf, Metric.sInf_image_infDist_eq_toReal_biInf,
    biInf_holomorphicHull_edist_compl hKΩ]

/-- For `K ⊆ Ω`, `holomorphicHull Ω K` and `K` have the same ordinary distance to `frontier Ω`. -/
theorem sInf_image_infDist_frontier_holomorphicHull {Ω K : Set ℂ} (hKΩ : K ⊆ Ω) :
    sInf ((fun z ↦ infDist z (frontier Ω)) '' holomorphicHull Ω K) =
      sInf ((fun z ↦ infDist z (frontier Ω)) '' K) := by
  rw [Metric.sInf_image_infDist_eq_toReal_biInf, Metric.sInf_image_infDist_eq_toReal_biInf,
    biInf_holomorphicHull_edist_frontier hKΩ]

/-- The `Ω`-holomorphic hull of any set is relatively closed in `Ω`. -/
theorem closure_holomorphicHull_inter_eq (Ω K : Set ℂ) :
    closure (holomorphicHull Ω K) ∩ Ω = holomorphicHull Ω K := by
  refine Subset.antisymm (fun z ⟨hzcl, hzΩ⟩ ↦ mem_holomorphicHull_iff.mpr
      ⟨hzΩ, fun f hf B hB ↦ ?_⟩)
    (subset_inter subset_closure (holomorphicHull_subset_left Ω K))
  have : (𝓝[holomorphicHull Ω K] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hzcl
  have hcont : Tendsto (fun w ↦ ‖f w‖) (𝓝[holomorphicHull Ω K] z) (𝓝 ‖f z‖) :=
    ((hf.continuousOn z hzΩ).mono (holomorphicHull_subset_left Ω K)).norm
  exact le_of_tendsto hcont
    (eventually_nhdsWithin_of_forall fun _ hw ↦ norm_le_of_mem_holomorphicHull hw hf hB)

/-- If `K` is bounded, then `holomorphicHull Ω K` is bounded. -/
theorem _root_.Bornology.IsBounded.holomorphicHull {Ω K : Set ℂ} (hK : IsBounded K) :
    IsBounded (TauCeti.holomorphicHull Ω K) := by
  obtain ⟨R, hR⟩ := hK.subset_closedBall 0
  refine (isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset fun z hz ↦
    mem_closedBall_zero_iff.mpr ?_
  exact norm_le_of_mem_holomorphicHull hz differentiableOn_id (B := R) fun w hw ↦
    mem_closedBall_zero_iff.mp (hR hw)

/-- If `closure K ⊆ Ω`, then `holomorphicHull Ω K` is closed in `ℂ`. -/
theorem isClosed_holomorphicHull_of_closure_subset {Ω K : Set ℂ} (hKΩ : closure K ⊆ Ω) :
    IsClosed (holomorphicHull Ω K) := by
  -- Relative closedness handles adherence inside `Ω`, while distance preservation keeps the hull
  -- away from every point of `Ωᶜ`.
  refine isClosed_of_closure_subset fun z hzcl ↦ ?_
  suffices hzΩ : z ∈ Ω from (closure_holomorphicHull_inter_eq Ω K).subset ⟨hzcl, hzΩ⟩
  by_contra hzΩ
  have hpos : 0 < infEDist z K :=
    infEDist_pos_iff_notMem_closure.mpr fun h ↦ hzΩ (hKΩ h)
  have h0 : infEDist z (holomorphicHull Ω K) < infEDist z K := by
    rwa [mem_closure_iff_infEDist_zero.mp hzcl]
  obtain ⟨w, hw, hwz⟩ := infEDist_lt_iff.mp h0
  exact hwz.not_ge ((infEDist_le_edist_of_mem_holomorphicHull hw hzΩ).trans_eq (edist_comm w z))

/-- The entire holomorphic hull `holomorphicHull univ K` of any set `K ⊆ ℂ` is closed. -/
theorem isClosed_holomorphicHull_univ (K : Set ℂ) : IsClosed (holomorphicHull univ K) :=
  isClosed_holomorphicHull_of_closure_subset (subset_univ _)

/-- If `K ⊆ Ω` is closed in `ℂ`, then `holomorphicHull Ω K` is closed in `ℂ`. -/
theorem _root_.IsClosed.holomorphicHull {Ω K : Set ℂ} (hK : IsClosed K) (hKΩ : K ⊆ Ω) :
    IsClosed (TauCeti.holomorphicHull Ω K) :=
  isClosed_holomorphicHull_of_closure_subset (hK.closure_eq.symm ▸ hKΩ)

/-- If `K` is bounded and `closure K ⊆ Ω`, then `holomorphicHull Ω K` is compact. -/
theorem _root_.Bornology.IsBounded.isCompact_holomorphicHull_of_closure_subset {Ω K : Set ℂ}
    (hK : IsBounded K) (hKΩ : closure K ⊆ Ω) :
    IsCompact (TauCeti.holomorphicHull Ω K) :=
  Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨isClosed_holomorphicHull_of_closure_subset hKΩ, hK.holomorphicHull⟩

/-- If `K ⊆ ℂ` is bounded, then its entire holomorphic hull `holomorphicHull univ K` is compact. -/
theorem _root_.Bornology.IsBounded.isCompact_holomorphicHull_univ {K : Set ℂ} (hK : IsBounded K) :
    IsCompact (TauCeti.holomorphicHull univ K) :=
  hK.isCompact_holomorphicHull_of_closure_subset (subset_univ _)

/-- If `K ⊆ Ω` is compact, then `holomorphicHull Ω K` is compact. -/
theorem _root_.IsCompact.holomorphicHull {Ω K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsCompact (TauCeti.holomorphicHull Ω K) :=
  hK.isBounded.isCompact_holomorphicHull_of_closure_subset (hK.isClosed.closure_eq.symm ▸ hKΩ)

/-! ### Convex hull comparison -/

/-- The `Ω`-holomorphic hull of any set lies in its closed real convex hull. -/
theorem holomorphicHull_subset_closedConvexHull (Ω K : Set ℂ) :
    holomorphicHull Ω K ⊆ closedConvexHull ℝ K := by
  -- Separate outside points by the real part of `l : StrongDual ℂ ℂ` and test against `exp (l ·)`.
  intro z hz
  by_contra hzK
  obtain ⟨l, u, hlK, hlz⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
    convex_closedConvexHull isClosed_closedConvexHull hzK
  have hf : DifferentiableOn ℂ (fun w ↦ Complex.exp (l w)) Ω :=
    (Complex.differentiable_exp.comp l.differentiable).differentiableOn
  have hbound : ∀ w ∈ K, ‖Complex.exp (l w)‖ ≤ Real.exp u := fun w hw ↦ by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (hlK w (subset_closedConvexHull hw)).le
  have hle := norm_le_of_mem_holomorphicHull hz hf hbound
  rw [Complex.norm_exp, Real.exp_le_exp] at hle
  exact hlz.not_ge hle

/-- For compact `K ⊆ ℂ`, the `Ω`-holomorphic hull of `K` lies in its ordinary convex hull
`convexHull ℝ K`. -/
theorem _root_.IsCompact.holomorphicHull_subset_convexHull {Ω K : Set ℂ} (hK : IsCompact K) :
    holomorphicHull Ω K ⊆ convexHull ℝ K := by
  have hcl : closedConvexHull ℝ K = convexHull ℝ K := by
    rw [closedConvexHull_eq_closure_convexHull, (hK.convexHull (𝕜 := ℝ)).isClosed.closure_eq]
  exact hcl ▸ holomorphicHull_subset_closedConvexHull Ω K

/-- For a closed real-convex set `K ⊆ ℂ`, the `Ω`-holomorphic hull of `K` is `K ∩ Ω`. -/
theorem _root_.Convex.holomorphicHull_eq_inter {Ω K : Set ℂ} (hconv : Convex ℝ K)
    (hcl : IsClosed K) :
    TauCeti.holomorphicHull Ω K = K ∩ Ω :=
  Subset.antisymm
    (subset_inter
      ((holomorphicHull_subset_closedConvexHull Ω K).trans
        (closedConvexHull_min Subset.rfl hconv hcl))
      (holomorphicHull_subset_left Ω K))
    (inter_subset_holomorphicHull Ω K)

/-- For a closed real-convex set `K ⊆ Ω`, the `Ω`-holomorphic hull of `K` is `K` itself. -/
theorem _root_.Convex.holomorphicHull_eq {Ω K : Set ℂ} (hconv : Convex ℝ K) (hcl : IsClosed K)
    (hKΩ : K ⊆ Ω) :
    TauCeti.holomorphicHull Ω K = K := by
  rw [hconv.holomorphicHull_eq_inter hcl, inter_eq_left.mpr hKΩ]

/-! ### Maximum-principle inclusion and filledness -/

end TauCeti

namespace IsOpen

open TauCeti

/-- **Maximum-principle inclusion.** In an open plane set `Ω`, if the connected component `C` of
`z` in `Ω \ K` has compact closure contained in `Ω`, then `closure C` lies in `holomorphicHull Ω K`.
-/
theorem closure_connectedComponentIn_sdiff_subset_holomorphicHull {Ω K : Set ℂ}
    (hΩ : IsOpen Ω) {z : ℂ} (hcpt : IsCompact (closure (connectedComponentIn (Ω \ K) z)))
    (hcl : closure (connectedComponentIn (Ω \ K) z) ⊆ Ω) :
    closure (connectedComponentIn (Ω \ K) z) ⊆ holomorphicHull Ω K := by
  set C := connectedComponentIn (Ω \ K) z
  have hfr : frontier C ⊆ closure K := hΩ.frontier_connectedComponentIn_sdiff_subset_closure hcl
  intro w hw
  refine mem_holomorphicHull_iff.mpr ⟨hcl hw, fun f hf B hB ↦ ?_⟩
  refine Complex.norm_le_of_forall_mem_frontier_norm_le (hcpt.isBounded.subset subset_closure)
    (hf.mono hcl).diffContOnCl (fun ζ hζ ↦ ?_) hw
  have hζH : ζ ∈ holomorphicHull Ω K :=
    (closure_holomorphicHull_inter_eq Ω K).subset
      ⟨closure_mono (inter_subset_holomorphicHull Ω K) (hΩ.closure_inter ⟨hfr hζ, hcl hζ.1⟩),
        hcl hζ.1⟩
  exact norm_le_of_mem_holomorphicHull hζH hf hB

/-- In an open plane set `Ω`, every connected component of `Ω \ K` whose closure is compact and
contained in `Ω` lies in `holomorphicHull Ω K`. -/
theorem connectedComponentIn_sdiff_subset_holomorphicHull {Ω K : Set ℂ}
    (hΩ : IsOpen Ω) {z : ℂ} (hcpt : IsCompact (closure (connectedComponentIn (Ω \ K) z)))
    (hcl : closure (connectedComponentIn (Ω \ K) z) ⊆ Ω) :
    connectedComponentIn (Ω \ K) z ⊆ holomorphicHull Ω K :=
  subset_closure.trans (hΩ.closure_connectedComponentIn_sdiff_subset_holomorphicHull hcpt hcl)

/-- For `K ⊆ Ω` with `Ω` open, the fill-in of `K` in `Ω` (`K` together with all relatively compact
connected components of `Ω \ K` in `Ω`) lies inside `holomorphicHull Ω K`. -/
theorem fillIn_subset_holomorphicHull {Ω K : Set ℂ} (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) :
    fillIn K Ω ⊆ holomorphicHull Ω K := fun z hz ↦ by
  rcases mem_fillIn_iff.mp hz with hzK | ⟨hz, hcpt, hcl⟩
  · exact subset_holomorphicHull hKΩ hzK
  · exact hΩ.connectedComponentIn_sdiff_subset_holomorphicHull hcpt hcl
      (mem_connectedComponentIn hz)

/-- The `Ω`-holomorphic hull of any set is filled in an open set `Ω`. -/
theorem isFilledIn_holomorphicHull {Ω : Set ℂ} (hΩ : IsOpen Ω) (K : Set ℂ) :
    IsFilledIn (holomorphicHull Ω K) Ω := by
  rw [isFilledIn_iff]
  rintro z hz ⟨hcpt, hcl⟩
  have hz' := hΩ.connectedComponentIn_sdiff_subset_holomorphicHull hcpt hcl
    (mem_connectedComponentIn hz)
  rw [holomorphicHull_holomorphicHull] at hz'
  exact hz.2 hz'

end IsOpen

namespace TauCeti

/-! ### Comparison with polynomial hulls on `ℂ` -/

/-- For any index type `ι` and any `K ⊆ ℂ`, `holomorphicHull univ K` lies in the preimage of
`TauCeti.polynomialHull (Function.const ι '' K)` under `Function.const ι`. -/
theorem holomorphicHull_univ_subset_preimage_polynomialHull (ι : Type*) (K : Set ℂ) :
    holomorphicHull univ K ⊆ Function.const ι ⁻¹' polynomialHull (Function.const ι '' K) := by
  intro z hz
  rw [mem_preimage, mem_polynomialHull_iff]
  intro p c hc
  rw [← MvPolynomial.eval_aeval_const_X]
  set q : Polynomial ℂ := MvPolynomial.aeval (Function.const ι Polynomial.X) p
  refine norm_le_of_mem_holomorphicHull hz q.differentiable.differentiableOn fun w hw ↦ ?_
  simpa only [q, MvPolynomial.eval_aeval_const_X] using hc _ (mem_image_of_mem _ hw)

/-- **Holomorphic hull on `ℂ` equals the polynomial hull.** For any nonempty index type `ι` (in
particular `ι = Fin 1`, where `Function.const (Fin 1)` is
`⇑(ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ).symm`) and any bounded set `K ⊆ ℂ`, the entire
holomorphic hull `holomorphicHull univ K` equals the preimage of
`TauCeti.polynomialHull (Function.const ι '' K)` under `Function.const ι`. -/
theorem _root_.Bornology.IsBounded.holomorphicHull_univ_eq_preimage_polynomialHull {ι : Type*}
    [Nonempty ι] {K : Set ℂ} (hK : IsBounded K) :
    TauCeti.holomorphicHull univ K =
      Function.const ι ⁻¹' polynomialHull (Function.const ι '' K) := by
  refine Subset.antisymm (holomorphicHull_univ_subset_preimage_polynomialHull ι K) fun z hz ↦ ?_
  by_contra hzH
  rw [mem_holomorphicHull_iff] at hzH
  push Not at hzH
  obtain ⟨g, hg_on, B, hgK, hBz⟩ := hzH (mem_univ z)
  have hg : Differentiable ℂ g := differentiableOn_univ.mp hg_on
  obtain ⟨R₀, hR₀⟩ := (hK.insert z).subset_ball 0
  set R : ℝ≥0 := ⟨max R₀ 1, by positivity⟩
  have hsub : insert z K ⊆ ball (0 : ℂ) R :=
    hR₀.trans (ball_subset_ball (le_max_left R₀ 1))
  obtain ⟨p, hfps⟩ : ∃ p, HasFPowerSeriesOnBall g p 0 ∞ :=
    ⟨_, hg.hasFPowerSeriesOnBall 0 zero_lt_one⟩
  have htend : TendstoUniformlyOn (fun n y ↦ p.partialSum n y) (fun y ↦ g (0 + y)) atTop
      (ball (0 : ℂ) R) :=
    hfps.tendstoUniformlyOn (ENNReal.coe_lt_top (r := R))
  set ε := (‖g z‖ - B) / 3 with hε_def
  have hε : 0 < ε := by linarith [hε_def]
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformlyOn_iff.mp htend ε hε).exists
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  let P : MvPolynomial ι ℂ :=
    ∑ k ∈ Finset.range n, MvPolynomial.C (p.coeff k) * MvPolynomial.X i₀ ^ k
  have heval (y : ℂ) : MvPolynomial.eval (Function.const ι y) P = p.partialSum n y := by
    rw [FormalMultilinearSeries.partialSum]
    simp only [P, map_sum, map_mul, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X,
      Function.const_apply]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [p.apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm]
  have hPK : ∀ u ∈ Function.const ι '' K, ‖MvPolynomial.eval u P‖ ≤ B + ε := by
    rintro _ ⟨w, hw, rfl⟩
    rw [heval]
    have hdist : ‖g w - p.partialSum n w‖ < ε := by
      simpa only [zero_add, dist_eq_norm] using hn w (hsub (mem_insert_of_mem z hw))
    have htri : ‖p.partialSum n w‖ ≤ ‖g w‖ + ‖g w - p.partialSum n w‖ := by
      simpa only [sub_sub_cancel] using norm_sub_le (g w) (g w - p.partialSum n w)
    linarith [hgK w hw]
  have hPz : ‖p.partialSum n z‖ ≤ B + ε := by
    rw [← heval]
    exact mem_polynomialHull_iff.mp hz P (B + ε) hPK
  have hdistz : ‖g z - p.partialSum n z‖ < ε := by
    simpa only [zero_add, dist_eq_norm] using hn z (hsub (mem_insert z K))
  have htriz : ‖g z‖ ≤ ‖p.partialSum n z‖ + ‖g z - p.partialSum n z‖ := by
    simpa only [add_sub_cancel] using norm_add_le (p.partialSum n z) (g z - p.partialSum n z)
  linarith [hε_def]

/-- For any nonempty index type `ι` and any bounded `K ⊆ ℂ`, `K` equals its entire holomorphic hull
`holomorphicHull univ K` if and only if `Function.const ι '' K` is polynomially convex. -/
theorem _root_.Bornology.IsBounded.holomorphicHull_univ_eq_self_iff_isPolynomiallyConvex
    {ι : Type*} [Nonempty ι] {K : Set ℂ} (hK : IsBounded K) :
    TauCeti.holomorphicHull univ K = K ↔ IsPolynomiallyConvex (Function.const ι '' K) := by
  rw [hK.holomorphicHull_univ_eq_preimage_polynomialHull (ι := ι), isPolynomiallyConvex_iff]
  refine ⟨fun h u hu ↦ ?_, fun h ↦ Subset.antisymm (fun z hz ↦ ?_) ?_⟩
  · obtain ⟨w, rfl⟩ := polynomialHull_image_const_subset_range K hu
    exact mem_image_of_mem _ (h.subset hu)
  · obtain ⟨w, hw, hwz⟩ := h hz
    exact Function.const_injective hwz ▸ hw
  · intro z hz
    exact subset_polynomialHull _ (mem_image_of_mem _ hz)

/-- The entire holomorphic hull of the real axis `ℝ ⊆ ℂ` is `ℝ` itself. -/
@[simp]
theorem holomorphicHull_univ_range_ofReal :
    holomorphicHull univ (range Complex.ofReal) = range Complex.ofReal := by
  have hrange : (LinearMap.range Complex.ofRealLI.toLinearMap : Set ℂ) = range Complex.ofReal := by
    ext z
    simp
  exact Convex.holomorphicHull_eq
    (hrange ▸ (LinearMap.range Complex.ofRealLI.toLinearMap).convex)
    Complex.isometry_ofReal.isClosedEmbedding.isClosed_range (subset_univ _)

end TauCeti
