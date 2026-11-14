/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Differentiability
public import TauCeti.Analysis.Convex.SingularSet.Basic
public import TauCeti.Analysis.Convex.SubgradientImage
public import TauCeti.Analysis.InnerProductSpace.OrthogonalLine.HausdorffDimension
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import TauCeti.Analysis.Convex.Separation

/-!
# Singular sets and effective-domain frontiers of convex functions in finite dimension

Let `E` be a finite-dimensional real inner product space and let `f : E → EReal` have convex real
epigraph and never take the value `⊥`. At an interior point `x` of the effective domain
`D = {x | f x ≠ ⊤}`, the real representative `x' ↦ (f x').toReal` is differentiable at `x`
precisely when the subdifferential `∂f(x)` for the inner product contains at most one vector
(`TauCeti.differentiableAt_toReal_iff_subsingleton_subdifferential`, Rockafellar's Theorem 25.1).
Indeed, any subgradient selection near `x` is continuous at `x` by
`TauCeti.continuousAt_of_subsingleton_subdifferential`, where it is the gradient by
`TauCeti.hasGradientAt_toReal_of_continuousAt_subgradient`.

Points where `∂f(x)` is not a subsingleton have two subgradients differing along some vector `v` of
an orthonormal basis of `E`. Splitting `E` orthogonally along `(ℝ ∙ v)ᗮ` and `v` via
`TauCeti.orthogonalLineEquiv` reduces this to
`TauCeti.exists_lipschitzWith_graphs_cover_subdifferential_vertical_ne`: the multivalued locus of
any `f : E → EReal`, convex or not, is covered by countably many closed globally Lipschitz graphs
`range (fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v)` over hyperplanes orthogonal to unit vectors
(`OrthonormalBasis.exists_lipschitzWith_graphs_cover_not_subsingleton_subdifferential` and
`TauCeti.exists_lipschitzWith_graphs_cover_not_subsingleton_subdifferential`).

Applying this to the indicator `δ` of the closure of a convex set `C ⊆ E` covers `frontier C` by
closed Lipschitz graphs over hyperplanes (`Convex.exists_lipschitzWith_graphs_cover_frontier`):
every frontier point carries the zero subgradient of `δ` together with a nonzero outward normal
given by `Convex.exists_ne_zero_forall_closure_inner_sub_nonpos`. Since a Lipschitz graph over
`(ℝ ∙ v)ᗮ` (`‖v‖ = 1`) has `dimH + 1 ≤ finrank ℝ E` (`TauCeti.dimH_range_add_smul_add_one_le`),
transferring along a continuous linear equivalence to `EuclideanSpace ℝ (Fin (finrank ℝ E))` shows
that in any finite-dimensional real normed space `E`, `dimH (frontier C) ≤ finrank ℝ E - 1`
(`Convex.dimH_frontier_le`) and every measure vanishing on measurable sets with
`dimH A + 1 ≤ finrank ℝ E` or `dimH A ≤ finrank ℝ E - 1`—strengthening `Convex.addHaar_frontier`—
sees `f` finite on a neighbourhood and differentiable almost everywhere on `{x | f x ≠ ⊤}`.

## Main statements

* `TauCeti.differentiableAt_toReal_iff_subsingleton_subdifferential` — **Rockafellar's
  differentiability criterion**: on `interior {x | f x ≠ ⊤}`, `(f ·).toReal` is differentiable at
  `x` if and only if `(subdifferential (innerₗ E) f x).Subsingleton`;
* `OrthonormalBasis.exists_lipschitzWith_graphs_cover_not_subsingleton_subdifferential`,
  `TauCeti.exists_lipschitzWith_graphs_cover_not_subsingleton_subdifferential`, and
  `TauCeti.ae_subsingleton_subdifferential_of_null_lipschitz_graphs` — points where `∂f(x)` has at
  least two elements lie in countably many closed Lipschitz graphs over hyperplanes;
* `Convex.exists_lipschitzWith_graphs_cover_frontier` and
  `Convex.measure_frontier_eq_zero_of_null_lipschitz_graphs` — the frontier of a convex set in a
  finite-dimensional real inner product space is covered by countably many closed Lipschitz graphs
  over hyperplanes;
* `Convex.dimH_frontier_le` and `Convex.dimH_sdiff_interior_le` — the frontier and non-interior
  points `C \ interior C` of a convex set in any finite-dimensional real normed space have
  Hausdorff dimension at most `finrank ℝ E - 1`;
* `TauCeti.ae_eventually_ne_top_and_differentiableAt_toReal_of_null_lipschitz_graphs`,
  `TauCeti.ae_eventually_ne_top_and_differentiableAt_toReal_of_dimH_add_one_le`, and
  `TauCeti.ae_eventually_ne_top_and_differentiableAt_toReal_of_dimH_le` — almost-everywhere
  interiority and differentiability on `{x | f x ≠ ⊤}` for measures vanishing on Lipschitz
  hypersurface graphs or small sets.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton Mathematical Series 28, 1970, Theorem 25.1.
* L. Zajíček, *On the differentiation of convex functions in finite and infinite dimensional
  spaces*, Czechoslovak Mathematical Journal 29 (1979), 340–348.
* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, 2003,
  Theorem 2.12(ii) and §2.4.
* M. Agueh and G. Carlier, *Barycenters in the Wasserstein space*, SIAM J. Math. Anal. 43 (2011),
  904–924, §3.1, Definition 3.2.
-/

public section

noncomputable section

open Filter MeasureTheory Metric Module Set
open scoped ENNReal NNReal Topology

namespace TauCeti

section DifferentiabilityCriterion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-- **Rockafellar's differentiability criterion** (Rockafellar, *Convex Analysis*, Theorem 25.1).
Let `f : E → EReal` have convex real epigraph and never take the value `⊥` on a finite-dimensional
real inner product space `E`. At an interior point `x` of `{x | f x ≠ ⊤}`, the real representative
`x' ↦ (f x').toReal` is differentiable at `x` if and only if the subdifferential
`subdifferential (innerₗ E) f x` contains at most one element. -/
theorem differentiableAt_toReal_iff_subsingleton_subdifferential
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥)
    {x : E} (hx : x ∈ interior {x | f x ≠ ⊤}) :
    DifferentiableAt ℝ (fun x' => (f x').toReal) x ↔
      (subdifferential (innerₗ E) f x).Subsingleton := by
  have hdom : ∀ᶠ x' in 𝓝 x, f x' ≠ ⊤ := mem_interior_iff_mem_nhds.1 hx
  refine ⟨fun hd y₁ hy₁ y₂ hy₂ => ?_, fun hsub => ?_⟩
  · rw [← gradient_toReal_eq_of_mem_subdifferential hy₁ hdom hd,
      ← gradient_toReal_eq_of_mem_subdifferential hy₂ hdom hd]
  · classical
    let T : E → E := fun z =>
      if h : (subdifferential (innerₗ E) f z).Nonempty then h.choose else 0
    have hT : ∀ᶠ z in 𝓝 x, T z ∈ subdifferential (innerₗ E) f z := by
      filter_upwards [eventually_nonempty_subdifferential hf hbot hdom] with z hz
      simp only [T, hz, ↓reduceDIte]
      exact hz.choose_spec
    exact (hasGradientAt_toReal_of_continuousAt_subgradient
      (continuousAt_of_subsingleton_subdifferential hf hbot hx hsub hT) hT).differentiableAt

end DifferentiabilityCriterion

section HyperplaneGraphs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Points where `f : E → EReal` admits two subgradients with different inner products along a unit
vector `v` are covered by countably many globally Lipschitz graphs over `(ℝ ∙ v)ᗮ`. Neither
convexity of `f` nor finite dimensionality of `E` is needed. -/
theorem exists_lipschitzWith_graphs_cover_subdifferential_inner_ne (f : E → EReal)
    {v : E} (hv : ‖v‖ = 1) :
    ∃ (K : ℚ × ℚ × ℕ → ℝ≥0) (g : (ℚ × ℚ × ℕ) → (ℝ ∙ v)ᗮ → ℝ),
      (∀ i, LipschitzWith (K i) (g i)) ∧
      ∀ (x y₁ y₂ : E),
        y₁ ∈ subdifferential (innerₗ E) f x →
        y₂ ∈ subdifferential (innerₗ E) f x →
        inner ℝ y₁ v ≠ inner ℝ y₂ v →
        ∃ i, x ∈ range fun w : (ℝ ∙ v)ᗮ => (w : E) + g i w • v := by
  let Φ : (ℝ ∙ v)ᗮ × ℝ →L[ℝ] E := (orthogonalLineEquiv v hv).toContinuousLinearMap
  obtain ⟨K, g, hg, hcover⟩ :=
    exists_lipschitzWith_graphs_cover_subdifferential_vertical_ne (f ∘ Φ)
  refine ⟨K, g, hg, fun x y₁ y₂ hy₁ hy₂ hne => ?_⟩
  let p : (ℝ ∙ v)ᗮ × ℝ := (orthogonalLineEquiv v hv).symm x
  have hp : Φ p = x := (orthogonalLineEquiv v hv).apply_symm_apply x
  have hpull {y : E} (hy : y ∈ subdifferential (innerₗ E) f x) :
      (innerSL ℝ y).comp Φ ∈
        subdifferential (topDualPairing ℝ ((ℝ ∙ v)ᗮ × ℝ)).flip (f ∘ Φ) p := by
    rw [mem_subdifferential_iff]
    refine ⟨by simpa only [Function.comp_apply, hp] using
        ne_bot_of_mem_subdifferential (innerₗ E) hy,
      by simpa only [Function.comp_apply, hp] using
        ne_top_of_mem_subdifferential (innerₗ E) hy, fun q => ?_⟩
    simp only [Function.comp_apply, hp, LinearMap.flip_apply, topDualPairing_apply,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply]
    rw [map_sub Φ q p, hp, real_inner_comm (Φ q - x) y, ← innerₗ_apply_apply]
    exact add_le_of_mem_subdifferential (innerₗ E) hy (Φ q)
  have hne' : ((innerSL ℝ y₁).comp Φ) (0, 1) ≠ ((innerSL ℝ y₂).comp Φ) (0, 1) := by
    simpa [Φ, innerSL_apply_apply] using hne
  obtain ⟨i, hi⟩ := hcover p _ _ (hpull hy₁) (hpull hy₂) hne'
  refine ⟨i, p.1, ?_⟩
  dsimp only [Φ] at hp
  rwa [ContinuousLinearEquiv.coe_coe, ← Prod.eta (p := p), orthogonalLineEquiv_apply, hi] at hp

/-- Given a finite orthonormal basis `b` of `E`, the points where `f : E → EReal` has at least two
subgradients are covered by countably many globally Lipschitz graphs over `(ℝ ∙ b k)ᗮ`. -/
theorem _root_.OrthonormalBasis.exists_lipschitzWith_graphs_cover_not_subsingleton_subdifferential
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (f : E → EReal) :
    ∃ (K : ι × (ℚ × ℚ × ℕ) → ℝ≥0)
      (g : (p : ι × (ℚ × ℚ × ℕ)) → (ℝ ∙ b p.1)ᗮ → ℝ),
      (∀ p, LipschitzWith (K p) (g p)) ∧
      {x : E | ¬ (subdifferential (innerₗ E) f x).Subsingleton} ⊆
        ⋃ p : ι × (ℚ × ℚ × ℕ),
          range fun w : (ℝ ∙ b p.1)ᗮ => (w : E) + g p w • b p.1 := by
  classical
  have hb (k : ι) : ‖b k‖ = 1 := b.orthonormal.1 k
  choose K g hg hcover using fun k =>
    exists_lipschitzWith_graphs_cover_subdifferential_inner_ne f (hb k)
  refine ⟨fun p => K p.1 p.2, fun p => g p.1 p.2, fun p => hg p.1 p.2, fun x hx => ?_⟩
  simp only [Set.Subsingleton, mem_ofPred_eq, not_forall] at hx
  obtain ⟨y₁, hy₁, y₂, hy₂, hne⟩ := hx
  have hex : ∃ k, inner ℝ y₁ (b k) ≠ inner ℝ y₂ (b k) := by
    by_contra! hall
    apply hne (b.repr.injective ?_)
    ext k
    rw [b.repr_apply_apply, b.repr_apply_apply, real_inner_comm, hall k, real_inner_comm]
  obtain ⟨k, hk⟩ := hex
  obtain ⟨i, hi⟩ := hcover k x y₁ y₂ hy₁ hy₂ hk
  exact mem_iUnion.mpr ⟨(k, i), hi⟩

/-- On a finite-dimensional real inner product space `E`, the points where `f : E → EReal` has at
least two subgradients for the inner product are covered by countably many globally Lipschitz
graphs over hyperplanes orthogonal to unit vectors. No convexity or measurability of `f` is
needed. -/
theorem exists_lipschitzWith_graphs_cover_not_subsingleton_subdifferential
    [FiniteDimensional ℝ E] (f : E → EReal) :
    ∃ (v : Fin (finrank ℝ E) → E)
      (K : Fin (finrank ℝ E) × (ℚ × ℚ × ℕ) → ℝ≥0)
      (g : (p : Fin (finrank ℝ E) × (ℚ × ℚ × ℕ)) → (ℝ ∙ v p.1)ᗮ → ℝ),
      (∀ k, ‖v k‖ = 1) ∧
      (∀ p, LipschitzWith (K p) (g p)) ∧
      {x : E | ¬ (subdifferential (innerₗ E) f x).Subsingleton} ⊆
        ⋃ p : Fin (finrank ℝ E) × (ℚ × ℚ × ℕ),
          range fun w : (ℝ ∙ v p.1)ᗮ => (w : E) + g p w • v p.1 := by
  let b := stdOrthonormalBasis ℝ E
  obtain ⟨K, g, hg, hcover⟩ :=
    b.exists_lipschitzWith_graphs_cover_not_subsingleton_subdifferential f
  exact ⟨b, K, g, b.orthonormal.1, hg, hcover⟩

end HyperplaneGraphs

section ConvexFrontierAndSingularSet

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
/-- Every frontier point of a convex set `C` in a finite-dimensional real inner product space has at
least two subgradients (`0` and a nonzero normal) for the `{0, ⊤}`-valued indicator of
`closure C`. -/
private theorem frontier_subset_not_subsingleton_subdifferential_indicator
    {C : Set E} (hC : Convex ℝ C) :
    frontier C ⊆
      {x : E | ¬ (subdifferential (innerₗ E)
        (fun z => if z ∈ closure C then (0 : EReal) else ⊤) x).Subsingleton} := by
  intro x hx
  obtain ⟨y, hy0, hy⟩ := hC.exists_ne_zero_forall_closure_inner_sub_nonpos hx
  refine fun hsub => hy0 (hsub ?_ ?_)
  · exact (mem_subdifferential_ite_iff (innerₗ E) (u := 0) hx.1).2 fun z hz => by
      simpa only [Pi.zero_apply, zero_add, innerₗ_apply_apply] using hy z hz
  · exact (mem_subdifferential_ite_iff (innerₗ E) (u := 0) hx.1).2 fun _ _ => by simp

/-- The frontier of any convex set in a finite-dimensional real inner product space `E` is covered
by countably many closed globally Lipschitz graphs over hyperplanes orthogonal to unit vectors. -/
theorem _root_.Convex.exists_lipschitzWith_graphs_cover_frontier {C : Set E} (hC : Convex ℝ C) :
    ∃ (v : Fin (finrank ℝ E) → E)
      (K : Fin (finrank ℝ E) × (ℚ × ℚ × ℕ) → ℝ≥0)
      (g : (p : Fin (finrank ℝ E) × (ℚ × ℚ × ℕ)) → (ℝ ∙ v p.1)ᗮ → ℝ),
      (∀ k, ‖v k‖ = 1) ∧
      (∀ p, LipschitzWith (K p) (g p)) ∧
      frontier C ⊆
        ⋃ p : Fin (finrank ℝ E) × (ℚ × ℚ × ℕ),
          range fun w : (ℝ ∙ v p.1)ᗮ => (w : E) + g p w • v p.1 := by
  classical
  obtain ⟨v, K, g, hv, hg, hcover⟩ :=
    exists_lipschitzWith_graphs_cover_not_subsingleton_subdifferential
      (E := E) (fun z => if z ∈ closure C then (0 : EReal) else ⊤)
  exact ⟨v, K, g, hv, hg,
    (frontier_subset_not_subsingleton_subdifferential_indicator hC).trans hcover⟩

end InnerProduct

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Hausdorff dimension of the frontier of a convex set.** In a finite-dimensional real normed
space `E`, the frontier of any convex set has Hausdorff dimension at most `finrank ℝ E - 1`. -/
theorem _root_.Convex.dimH_frontier_le {C : Set E} (hC : Convex ℝ C) :
    dimH (frontier C) ≤ ((finrank ℝ E - 1 : ℕ) : ℝ≥0∞) := by
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)) :=
    ContinuousLinearEquiv.ofFinrankEq (finrank_euclideanSpace_fin (𝕜 := ℝ)).symm
  obtain ⟨v, K, g, hv, hg, hcover⟩ :=
    (hC.linear_image e.toLinearMap).exists_lipschitzWith_graphs_cover_frontier
  rw [← e.dimH_image, ← e.coe_toHomeomorph, e.toHomeomorph.image_frontier, e.coe_toHomeomorph]
  refine (dimH_mono (by simpa using hcover)).trans ?_
  rw [dimH_iUnion]
  refine iSup_le fun p => ?_
  simpa only [finrank_euclideanSpace_fin] using dimH_range_add_smul_le (hv p.1) (hg p)

/-- In a finite-dimensional real normed space `E`, the non-interior points `C \ interior C` of any
convex set `C` have Hausdorff dimension at most `finrank ℝ E - 1`. -/
theorem _root_.Convex.dimH_sdiff_interior_le {C : Set E} (hC : Convex ℝ C) :
    dimH (C \ interior C) ≤ ((finrank ℝ E - 1 : ℕ) : ℝ≥0∞) :=
  (dimH_mono (sdiff_subset_sdiff_left subset_closure)).trans hC.dimH_frontier_le

end Normed

end ConvexFrontierAndSingularSet

section MeasureZeroAndDifferentiabilityAE

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Under a measure vanishing on every globally Lipschitz graph over the orthogonal complement of a
unit vector, the subdifferential of any `f : E → EReal` has at most one element almost everywhere.
Neither convexity nor measurability of `f` is needed. -/
theorem ae_subsingleton_subdifferential_of_null_lipschitz_graphs
    [MeasurableSpace E] (f : E → EReal) {μ : Measure E}
    (hμ : ∀ (v : E), ‖v‖ = 1 → ∀ (K : ℝ≥0) (g : (ℝ ∙ v)ᗮ → ℝ), LipschitzWith K g →
      μ (range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) = 0) :
    ∀ᵐ x ∂μ, (subdifferential (innerₗ E) f x).Subsingleton := by
  obtain ⟨v, K, g, hv, hg, hcover⟩ :=
    exists_lipschitzWith_graphs_cover_not_subsingleton_subdifferential f
  let U : Set E := ⋃ (p : Fin (finrank ℝ E) × (ℚ × ℚ × ℕ)),
    range fun w : (ℝ ∙ v p.1)ᗮ => (w : E) + g p w • v p.1
  have hnull : μ U = 0 :=
    measure_iUnion_null fun p : Fin (finrank ℝ E) × (ℚ × ℚ × ℕ) =>
      hμ (v p.1) (hv p.1) (K p) (g p) (hg p)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx
  by_contra hnot
  exact hx (hcover hnot)

/-- The frontier of any convex set in a finite-dimensional real inner product space has measure zero
for every measure vanishing on globally Lipschitz graphs over hyperplanes, strengthening
`Convex.addHaar_frontier`. -/
theorem _root_.Convex.measure_frontier_eq_zero_of_null_lipschitz_graphs
    [MeasurableSpace E] {C : Set E} (hC : Convex ℝ C) {μ : Measure E}
    (hμ : ∀ (v : E), ‖v‖ = 1 → ∀ (K : ℝ≥0) (g : (ℝ ∙ v)ᗮ → ℝ), LipschitzWith K g →
      μ (range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) = 0) :
    μ (frontier C) = 0 := by
  obtain ⟨v, K, g, hv, hg, hcover⟩ := hC.exists_lipschitzWith_graphs_cover_frontier
  let U : Set E := ⋃ (p : Fin (finrank ℝ E) × (ℚ × ℚ × ℕ)),
    range fun w : (ℝ ∙ v p.1)ᗮ => (w : E) + g p w • v p.1
  have hnull : μ U = 0 :=
    measure_iUnion_null fun p : Fin (finrank ℝ E) × (ℚ × ℚ × ℕ) =>
      hμ (v p.1) (hv p.1) (K p) (g p) (hg p)
  exact measure_mono_null hcover hnull

/-- Almost every point of a convex set belongs to its interior under any measure vanishing on
globally Lipschitz graphs over hyperplanes. -/
theorem _root_.Convex.ae_mem_interior_of_null_lipschitz_graphs
    [MeasurableSpace E] {C : Set E} (hC : Convex ℝ C) {μ : Measure E}
    (hμ : ∀ (v : E), ‖v‖ = 1 → ∀ (K : ℝ≥0) (g : (ℝ ∙ v)ᗮ → ℝ), LipschitzWith K g →
      μ (range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) = 0) :
    ∀ᵐ x ∂μ, x ∈ C → x ∈ interior C :=
  (interior_ae_eq_of_null_frontier
    (hC.measure_frontier_eq_zero_of_null_lipschitz_graphs hμ)).symm.subset

/-- **Almost-everywhere differentiability of convex functions under measures vanishing on Lipschitz
hypersurfaces.** Let `f : E → EReal` have convex real epigraph and never take the value `⊥` on a
finite-dimensional real inner product space `E`, and let `μ` be any measure on `E` that gives mass
`0` to every globally Lipschitz graph over the orthogonal complement of a unit vector. Then at
`μ`-almost every point `x` of `{x | f x ≠ ⊤}`, `f` is finite on a neighbourhood of `x` and its real
representative is differentiable at `x`. -/
theorem ae_eventually_ne_top_and_differentiableAt_toReal_of_null_lipschitz_graphs
    [MeasurableSpace E] {f : E → EReal} {μ : Measure E}
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥)
    (hμ : ∀ (v : E), ‖v‖ = 1 → ∀ (K : ℝ≥0) (g : (ℝ ∙ v)ᗮ → ℝ), LipschitzWith K g →
      μ (range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) = 0) :
    ∀ᵐ x ∂μ, f x ≠ ⊤ →
      (∀ᶠ x' in 𝓝 x, f x' ≠ ⊤) ∧ DifferentiableAt ℝ (fun x' => (f x').toReal) x := by
  filter_upwards [(convex_setOf_ne_top hf).ae_mem_interior_of_null_lipschitz_graphs hμ,
    ae_subsingleton_subdifferential_of_null_lipschitz_graphs f hμ] with x hint hsub hfx
  exact ⟨mem_interior_iff_mem_nhds.1 (hint hfx),
    (differentiableAt_toReal_iff_subsingleton_subdifferential hf hbot (hint hfx)).2 hsub⟩

end InnerProduct

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Almost-everywhere differentiability of convex functions under measures vanishing on measurable
sets with `dimH A + 1 ≤ finrank ℝ E`.** Unlike `dimH A ≤ finrank ℝ E - 1`, the hypothesis `hμ` on a
finite-dimensional real normed space `E` remains satisfiable by nonzero measures when
`finrank ℝ E = 0` (where `dimH A + 1 ≤ 0` is unsatisfiable). -/
theorem ae_eventually_ne_top_and_differentiableAt_toReal_of_dimH_add_one_le
    [MeasurableSpace E] [OpensMeasurableSpace E] {f : E → EReal} {μ : Measure E}
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥)
    (hμ : ∀ A, MeasurableSet A → dimH A + 1 ≤ (finrank ℝ E : ℝ≥0∞) → μ A = 0) :
    ∀ᵐ x ∂μ, f x ≠ ⊤ →
      (∀ᶠ x' in 𝓝 x, f x' ≠ ⊤) ∧ DifferentiableAt ℝ (fun x' => (f x').toReal) x := by
  let E₀ := EuclideanSpace ℝ (Fin (finrank ℝ E))
  let _ : MeasurableSpace E₀ := borel E₀
  have _ : BorelSpace E₀ := ⟨rfl⟩
  let e : E ≃L[ℝ] E₀ :=
    ContinuousLinearEquiv.ofFinrankEq (finrank_euclideanSpace_fin (𝕜 := ℝ)).symm
  have he : Measurable e := e.continuous.measurable
  have hf₀ : Convex ℝ {p : E₀ × ℝ | f (e.symm p.1) ≤ p.2} :=
    hf.linear_preimage (e.symm.toLinearMap.prodMap LinearMap.id)
  have hμ₀ : ∀ A : Set E₀, MeasurableSet A → dimH A + 1 ≤ (finrank ℝ E₀ : ℝ≥0∞) →
      (μ.map e) A = 0 := fun A hA hdim => by
    rw [Measure.map_apply he hA]
    refine hμ (e ⁻¹' A) (he hA) ?_
    simpa only [E₀, e.dimH_preimage, finrank_euclideanSpace_fin] using hdim
  have hae₀ := ae_eventually_ne_top_and_differentiableAt_toReal_of_null_lipschitz_graphs hf₀
    (fun y => hbot (e.symm y)) fun _ hv _ _ hg =>
      measure_range_add_smul_eq_zero_of_dimH_add_one_le hμ₀ hv hg
  filter_upwards [ae_of_ae_map he.aemeasurable hae₀] with x hx hfx
  obtain ⟨hdom, hd⟩ := hx (by simpa only [e.symm_apply_apply] using hfx)
  refine ⟨?_, ?_⟩
  · simpa only [Function.comp_def, e.symm_apply_apply] using
      e.continuous.continuousAt.eventually hdom
  · simpa only [Function.comp_def, e.symm_apply_apply] using hd.comp x e.differentiableAt

/-- **Almost-everywhere differentiability of convex functions under measures vanishing on small
measurable sets (`dimH A ≤ finrank ℝ E - 1` on a finite-dimensional real normed space `E`).** -/
theorem ae_eventually_ne_top_and_differentiableAt_toReal_of_dimH_le
    [MeasurableSpace E] [OpensMeasurableSpace E] {f : E → EReal} {μ : Measure E}
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥)
    (hμ : ∀ A, MeasurableSet A → dimH A ≤ ((finrank ℝ E - 1 : ℕ) : ℝ≥0∞) → μ A = 0) :
    ∀ᵐ x ∂μ, f x ≠ ⊤ →
      (∀ᶠ x' in 𝓝 x, f x' ≠ ⊤) ∧ DifferentiableAt ℝ (fun x' => (f x').toReal) x :=
  ae_eventually_ne_top_and_differentiableAt_toReal_of_dimH_add_one_le hf hbot fun _ hA hdim =>
    hμ _ hA (by
      simpa only [ENNReal.natCast_sub, Nat.cast_one] using
        ENNReal.le_sub_of_add_le_right ENNReal.one_ne_top hdim)

end Normed

end MeasureZeroAndDifferentiabilityAE

end TauCeti
