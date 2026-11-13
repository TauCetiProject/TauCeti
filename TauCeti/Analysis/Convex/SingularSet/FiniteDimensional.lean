/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Differentiability
public import TauCeti.Analysis.Convex.SingularSet.Basic
public import TauCeti.Analysis.Convex.SubgradientImage
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import TauCeti.Analysis.Convex.Separation

/-!
# Singular sets and effective-domain frontiers of convex functions in finite dimension

Let `E` be a finite-dimensional real inner product space and let `f : E → EReal` have convex real
epigraph and never take the value `⊥`. At an interior point `x` of the effective domain
`D = {x | f x ≠ ⊤}`, the real representative `x' ↦ (f x').toReal` is differentiable at `x`
precisely when the subdifferential `∂f(x)` for the inner product contains at most one vector
(`TauCeti.differentiableAt_toReal_iff_subsingleton_subdifferential`, Rockafellar's Theorem 25.1).
Indeed, any subgradient selection near `x` has values in a compact subdifferential graph over a
closed ball inside `interior D`, so single-valuedness at `x` makes the selection continuous at `x`,
where it is the gradient by `TauCeti.hasGradientAt_toReal_of_continuousAt_subgradient`.

Points where `∂f(x)` is not a subsingleton have two subgradients differing along some vector `v` of
an orthonormal basis of `E`. Splitting `E` orthogonally along `(ℝ ∙ v)ᗮ` and `v` reduces this to
`TauCeti.exists_lipschitzWith_graphs_cover_subdifferential_vertical_ne`: the multivalued locus of
any `f : E → EReal`, convex or not, is covered by countably many closed globally Lipschitz graphs
`range (fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v)` over hyperplanes orthogonal to unit vectors
(`OrthonormalBasis.exists_lipschitzWith_graphs_cover_not_subsingleton_subdifferential` and
`TauCeti.exists_lipschitzWith_graphs_cover_not_subsingleton_subdifferential`).

Applying this to the indicator `δ` of the closure of a convex set `C ⊆ E` covers `frontier C` by
closed Lipschitz graphs over hyperplanes (`Convex.exists_lipschitzWith_graphs_cover_frontier`):
every frontier point carries the zero subgradient of `δ` together with a nonzero outward normal
given by `Convex.exists_ne_zero_forall_closure_inner_sub_nonpos`. Since a Lipschitz graph over
`(ℝ ∙ v)ᗮ` (`‖v‖ = 1`) has `dimH + 1 ≤ finrank ℝ E`, it follows that
`dimH (frontier C) ≤ finrank ℝ E - 1` (`Convex.dimH_frontier_le`) and that every measure vanishing
on Lipschitz graphs over hyperplanes—strengthening `Convex.addHaar_frontier` to measures vanishing
on Borel sets with `dimH A + 1 ≤ finrank ℝ E` or `dimH A ≤ finrank ℝ E - 1`—gives zero mass to
`frontier C` and sees `f` finite on a neighbourhood and differentiable almost everywhere on
`{x | f x ≠ ⊤}`.

## Main statements

* `TauCeti.differentiableAt_toReal_iff_subsingleton_subdifferential` — **Rockafellar's
  differentiability criterion**: on `interior {x | f x ≠ ⊤}`, `(f ·).toReal` is differentiable at
  `x` if and only if `(subdifferential (innerₗ E) f x).Subsingleton`;
* `TauCeti.isClosed_range_add_smul_of_lipschitzWith` and
  `TauCeti.dimH_range_add_smul_add_one_le` — a Lipschitz graph over `(ℝ ∙ v)ᗮ` (`‖v‖ = 1`) is
  closed and satisfies `dimH + 1 ≤ finrank ℝ E`;
* `OrthonormalBasis.exists_lipschitzWith_graphs_cover_not_subsingleton_subdifferential`,
  `TauCeti.exists_lipschitzWith_graphs_cover_not_subsingleton_subdifferential`, and
  `TauCeti.ae_subsingleton_subdifferential_of_null_lipschitz_graphs` — points where `∂f(x)` has at
  least two elements lie in countably many closed Lipschitz graphs over hyperplanes;
* `Convex.exists_lipschitzWith_graphs_cover_frontier`, `Convex.dimH_frontier_le`, and
  `Convex.measure_frontier_eq_zero_of_null_lipschitz_graphs` — the frontier of a convex set in `E`
  is covered by countably many closed Lipschitz graphs over hyperplanes and has Hausdorff dimension
  at most `finrank ℝ E - 1`;
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
  904–924, §2.
-/

public section

noncomputable section

open Filter MeasureTheory Metric Module Set
open scoped ENNReal NNReal Topology

namespace TauCeti

section DifferentiabilityCriterion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-- A local selection of subgradients of a convex function on a finite-dimensional real inner
product space is continuous at any interior point of the effective domain where the
subdifferential is a subsingleton. -/
private theorem continuousAt_of_subsingleton_subdifferential
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥)
    {x : E} (hx : x ∈ interior {x | f x ≠ ⊤})
    (hsub : (subdifferential (innerₗ E) f x).Subsingleton)
    {T : E → E} (hT : ∀ᶠ z in 𝓝 x, T z ∈ subdifferential (innerₗ E) f z) :
    ContinuousAt T x := by
  obtain ⟨r, hr, hrD⟩ : ∃ r > 0, closedBall x r ⊆ interior {x | f x ≠ ⊤} :=
    nhds_basis_closedBall.mem_iff.1 (isOpen_interior.mem_nhds hx)
  have hG :
      IsCompact {p : E × E | p.1 ∈ closedBall x r ∧ p.2 ∈ subdifferential (innerₗ E) f p.1} :=
    isCompact_setOf_mem_subdifferential hf hbot (isCompact_closedBall x r) hrD
  have hball : ∀ᶠ z in 𝓝 x, z ∈ closedBall x r := closedBall_mem_nhds x hr
  have hmem : ∀ᶠ z in 𝓝 x,
      (z, T z) ∈ {p : E × E | p.1 ∈ closedBall x r ∧ p.2 ∈ subdifferential (innerₗ E) f p.1} :=
    hball.and hT
  have hpair : Tendsto (fun z => (z, T z)) (𝓝 x) (𝓝 (x, T x)) := by
    refine hG.tendsto_nhds_of_unique_mapClusterPt hmem ?_
    rintro ⟨z, y⟩ ⟨-, hy⟩ hcl
    have hzx : z = x := eq_of_nhds_neBot
      (mapClusterPt_id_iff.mp (hcl.continuousAt_comp continuous_fst.continuousAt))
    subst hzx
    exact Prod.ext rfl (hsub hy hT.self_of_nhds)
  exact continuous_snd.continuousAt.tendsto.comp hpair

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

/-- Subtracting the component along a unit vector `v` lands in `(ℝ ∙ v)ᗮ`. -/
private theorem sub_inner_smul_mem_orthogonal {v : E} (hv : ‖v‖ = 1) (z : E) :
    z - inner ℝ z v • v ∈ (ℝ ∙ v)ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, hv, one_pow, mul_one, sub_self]

/-- The orthogonal projection onto `(ℝ ∙ v)ᗮ` given explicitly by `z ↦ z - ⟪z, v⟫ • v` when
`‖v‖ = 1`. -/
private def orthProjUnit {v : E} (hv : ‖v‖ = 1) : E →L[ℝ] (ℝ ∙ v)ᗮ :=
  (ContinuousLinearMap.id ℝ E -
    ContinuousLinearMap.smulRight (innerSL ℝ v) v).codRestrict (ℝ ∙ v)ᗮ fun z => by
      simpa only [FunLike.coe_sub, Pi.sub_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, real_inner_comm v z] using
        sub_inner_smul_mem_orthogonal hv z

private theorem coe_orthProjUnit_apply {v : E} (hv : ‖v‖ = 1) (z : E) :
    (orthProjUnit hv z : E) = z - inner ℝ z v • v := by
  simp [orthProjUnit, innerSL_apply_apply, real_inner_comm v z]

private theorem orthProjUnit_add_smul {v : E} (hv : ‖v‖ = 1) (w : (ℝ ∙ v)ᗮ) (t : ℝ) :
    orthProjUnit hv ((w : E) + t • v) = w := by
  ext
  have hw : inner ℝ (w : E) v = 0 := Submodule.mem_orthogonal_singleton_iff_inner_left.mp w.2
  rw [coe_orthProjUnit_apply, inner_add_left, hw, zero_add, real_inner_smul_left,
    real_inner_self_eq_norm_sq, hv, one_pow, mul_one, add_sub_cancel_right]

/-- The graph map `w ↦ (w : E) + g w • v` over `(ℝ ∙ v)ᗮ` along a unit vector `v` is
`(1 + K)`-Lipschitz when `g` is `K`-Lipschitz. -/
theorem lipschitzWith_coe_add_smul {v : E} (hv : ‖v‖ = 1) {K : ℝ≥0} {g : (ℝ ∙ v)ᗮ → ℝ}
    (hg : LipschitzWith K g) :
    LipschitzWith (1 + K) (fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) := by
  refine LipschitzWith.of_dist_le_mul fun w₁ w₂ => ?_
  have hsub : ((w₁ : E) + g w₁ • v) - ((w₂ : E) + g w₂ • v) =
      ((w₁ - w₂ : (ℝ ∙ v)ᗮ) : E) + (g w₁ - g w₂) • v := by
    simp only [Submodule.coe_sub, sub_smul]
    abel
  rw [dist_eq_norm, hsub]
  calc
    ‖((w₁ - w₂ : (ℝ ∙ v)ᗮ) : E) + (g w₁ - g w₂) • v‖
      ≤ ‖((w₁ - w₂ : (ℝ ∙ v)ᗮ) : E)‖ + ‖(g w₁ - g w₂) • v‖ := norm_add_le _ _
    _ = dist w₁ w₂ + dist (g w₁) (g w₂) := by
      rw [Submodule.norm_coe, ← dist_eq_norm, norm_smul, hv, mul_one, Real.norm_eq_abs,
        ← Real.dist_eq]
    _ ≤ 1 * dist w₁ w₂ + K * dist w₁ w₂ := by
      gcongr
      · rw [one_mul]
      · exact hg.dist_le_mul w₁ w₂
    _ = ↑(1 + K) * dist w₁ w₂ := by push_cast; ring

/-- The graph `range (fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v)` over the orthogonal complement of a
unit vector `v` is closed whenever `g` is continuous (in particular whenever `g` is Lipschitz). -/
theorem isClosed_range_add_smul_of_continuous {v : E} (hv : ‖v‖ = 1) {g : (ℝ ∙ v)ᗮ → ℝ}
    (hg : Continuous g) :
    IsClosed (range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) := by
  have heq : (range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) =
      {z : E | inner ℝ z v = g (orthProjUnit hv z)} := by
    ext z
    simp only [mem_range, mem_ofPred_eq]
    refine ⟨?_, fun hz => ⟨orthProjUnit hv z, ?_⟩⟩
    · rintro ⟨w, rfl⟩
      have hw : inner ℝ (w : E) v = 0 := Submodule.mem_orthogonal_singleton_iff_inner_left.mp w.2
      rw [orthProjUnit_add_smul hv w (g w), inner_add_left, hw, zero_add, real_inner_smul_left,
        real_inner_self_eq_norm_sq, hv, one_pow, mul_one]
    · rw [← hz, coe_orthProjUnit_apply, sub_add_cancel]
  rw [heq]
  exact isClosed_eq (continuous_id.inner continuous_const) (hg.comp (orthProjUnit hv).continuous)

/-- A globally Lipschitz graph over `(ℝ ∙ v)ᗮ` (`‖v‖ = 1`) is closed. -/
theorem isClosed_range_add_smul_of_lipschitzWith {v : E} (hv : ‖v‖ = 1) {K : ℝ≥0}
    {g : (ℝ ∙ v)ᗮ → ℝ} (hg : LipschitzWith K g) :
    IsClosed (range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) :=
  isClosed_range_add_smul_of_continuous hv hg.continuous

/-- On a finite-dimensional real inner product space `E`, a Lipschitz graph over `(ℝ ∙ v)ᗮ`
(`‖v‖ = 1`) has Hausdorff dimension satisfying `dimH + 1 ≤ finrank ℝ E`. -/
theorem dimH_range_add_smul_add_one_le [FiniteDimensional ℝ E] {v : E} (hv : ‖v‖ = 1)
    {K : ℝ≥0} {g : (ℝ ∙ v)ᗮ → ℝ} (hg : LipschitzWith K g) :
    dimH (range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) + 1 ≤ (finrank ℝ E : ℝ≥0∞) := by
  have hv0 : v ≠ 0 := fun h => by simp [h] at hv
  have hfin : finrank ℝ (ℝ ∙ v)ᗮ + 1 = finrank ℝ E := by
    have h := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (E := E) (ℝ ∙ v)
    rwa [finrank_span_singleton hv0, add_comm] at h
  calc
    dimH (range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) + 1
      ≤ dimH (univ : Set (ℝ ∙ v)ᗮ) + 1 :=
        add_le_add_left (lipschitzWith_coe_add_smul hv hg).dimH_range_le 1
    _ = (finrank ℝ (ℝ ∙ v)ᗮ : ℝ≥0∞) + 1 := by rw [Real.dimH_univ_eq_finrank]
    _ = (finrank ℝ E : ℝ≥0∞) := by exact_mod_cast hfin

/-- On a finite-dimensional real inner product space `E`, a Lipschitz graph over `(ℝ ∙ v)ᗮ`
(`‖v‖ = 1`) has Hausdorff dimension at most `finrank ℝ E - 1`. -/
theorem dimH_range_add_smul_le [FiniteDimensional ℝ E] {v : E} (hv : ‖v‖ = 1)
    {K : ℝ≥0} {g : (ℝ ∙ v)ᗮ → ℝ} (hg : LipschitzWith K g) :
    dimH (range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) ≤ ((finrank ℝ E - 1 : ℕ) : ℝ≥0∞) := by
  have h := dimH_range_add_smul_add_one_le hv hg
  rcases hd : finrank ℝ E with _ | n
  · exact absurd (le_add_self.trans h) (by simp [hd])
  · simpa [hd, ENNReal.add_le_add_iff_right ENNReal.one_ne_top] using h

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
  let Φ : (ℝ ∙ v)ᗮ × ℝ →L[ℝ] E :=
    (Submodule.subtypeL (ℝ ∙ v)ᗮ).coprod (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v)
  have hΦ (p : (ℝ ∙ v)ᗮ × ℝ) : Φ p = (p.1 : E) + p.2 • v := by
    simp [Φ, ContinuousLinearMap.coprod_apply]
  obtain ⟨K, g, hg, hcover⟩ :=
    exists_lipschitzWith_graphs_cover_subdifferential_vertical_ne (f ∘ Φ)
  refine ⟨K, g, hg, fun x y₁ y₂ hy₁ hy₂ hne => ?_⟩
  let p : (ℝ ∙ v)ᗮ × ℝ := (orthProjUnit hv x, inner ℝ x v)
  have hp : Φ p = x := by
    rw [hΦ, coe_orthProjUnit_apply, sub_add_cancel]
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
    simpa [hΦ, innerSL_apply_apply] using hne
  obtain ⟨i, hi⟩ := hcover p _ _ (hpull hy₁) (hpull hy₂) hne'
  refine ⟨i, p.1, ?_⟩
  simpa only [← hi, hΦ] using hp

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
  set δ : E → EReal := fun z => if z ∈ closure C then 0 else ⊤
  intro x hx
  have hx_cl : x ∈ closure C := hx.1
  have hmem_of_le {y : E} (hy : ∀ z ∈ closure C, inner ℝ (z - x) y ≤ 0) :
      y ∈ subdifferential (innerₗ E) δ x := by
    rw [mem_subdifferential_iff]
    refine ⟨by simp [δ, hx_cl], by simp [δ, hx_cl], fun z => ?_⟩
    by_cases hz : z ∈ closure C
    · simp only [δ, hx_cl, hz, ↓reduceIte, zero_add, innerₗ_apply_apply, EReal.coe_nonpos]
      exact hy z hz
    · simp [δ, hz]
  obtain ⟨y, hy0, hy⟩ := hC.exists_ne_zero_forall_closure_inner_sub_nonpos hx
  exact fun hsub => hy0 (hsub (hmem_of_le hy) (hmem_of_le fun _ _ => by simp))

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

/-- **Hausdorff dimension of the frontier of a convex set.** In a finite-dimensional real inner
product space `E`, the frontier of any convex set has Hausdorff dimension at most
`finrank ℝ E - 1`. -/
theorem _root_.Convex.dimH_frontier_le {C : Set E} (hC : Convex ℝ C) :
    dimH (frontier C) ≤ ((finrank ℝ E - 1 : ℕ) : ℝ≥0∞) := by
  obtain ⟨v, K, g, hv, hg, hcover⟩ := hC.exists_lipschitzWith_graphs_cover_frontier
  refine (dimH_mono hcover).trans ?_
  rw [dimH_iUnion]
  exact iSup_le fun p => dimH_range_add_smul_le (hv p.1) (hg p)

/-- In a finite-dimensional real inner product space `E`, the non-interior points `C \ interior C`
of any convex set `C` have Hausdorff dimension at most `finrank ℝ E - 1`. -/
theorem _root_.Convex.dimH_diff_interior_le {C : Set E} (hC : Convex ℝ C) :
    dimH (C \ interior C) ≤ ((finrank ℝ E - 1 : ℕ) : ℝ≥0∞) :=
  (dimH_mono (sdiff_subset_sdiff_left subset_closure)).trans hC.dimH_frontier_le

end ConvexFrontierAndSingularSet

section MeasureZeroAndDifferentiabilityAE

/-- A measure vanishing on Borel sets `A` with `dimH A ≤ finrank ℝ E - 1` also vanishes on Borel
sets `A` with `dimH A + 1 ≤ finrank ℝ E`. The latter condition remains satisfiable when
`finrank ℝ E = 0`. -/
theorem measure_eq_zero_of_dimH_add_one_le_of_forall_dimH_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] {μ : Measure E}
    (hμ : ∀ A, MeasurableSet A → dimH A ≤ ((finrank ℝ E - 1 : ℕ) : ℝ≥0∞) → μ A = 0)
    {A : Set E} (hA : MeasurableSet A) (hdim : dimH A + 1 ≤ (finrank ℝ E : ℝ≥0∞)) :
    μ A = 0 := by
  refine hμ A hA ?_
  rcases hd : finrank ℝ E with _ | n
  · exact absurd (le_add_self.trans hdim) (by simp [hd])
  · simpa [hd, ENNReal.add_le_add_iff_right ENNReal.one_ne_top] using hdim

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A measure on a Borel finite-dimensional real inner product space that vanishes on Borel sets
with `dimH A + 1 ≤ finrank ℝ E` vanishes on every globally Lipschitz graph over the orthogonal
complement of a unit vector. -/
theorem measure_range_add_smul_eq_zero_of_dimH_add_one_le [MeasurableSpace E]
    [OpensMeasurableSpace E] {μ : Measure E}
    (hμ : ∀ A, MeasurableSet A → dimH A + 1 ≤ (finrank ℝ E : ℝ≥0∞) → μ A = 0)
    {v : E} (hv : ‖v‖ = 1) {K : ℝ≥0} {g : (ℝ ∙ v)ᗮ → ℝ} (hg : LipschitzWith K g) :
    μ (range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) = 0 :=
  hμ _ (isClosed_range_add_smul_of_lipschitzWith hv hg).measurableSet
    (dimH_range_add_smul_add_one_le hv hg)

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
    ∀ᵐ x ∂μ, x ∈ C → x ∈ interior C := by
  have hfr : μ (frontier C) = 0 := hC.measure_frontier_eq_zero_of_null_lipschitz_graphs hμ
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hfr] with x hx hxC
  by_contra hx_not_int
  exact hx ⟨subset_closure hxC, hx_not_int⟩

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

/-- **Almost-everywhere differentiability of convex functions under measures vanishing on sets with
`dimH A + 1 ≤ finrank ℝ E`.** This form holds in every finite dimension, including `0`. -/
theorem ae_eventually_ne_top_and_differentiableAt_toReal_of_dimH_add_one_le
    [MeasurableSpace E] [OpensMeasurableSpace E] {f : E → EReal} {μ : Measure E}
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥)
    (hμ : ∀ A, MeasurableSet A → dimH A + 1 ≤ (finrank ℝ E : ℝ≥0∞) → μ A = 0) :
    ∀ᵐ x ∂μ, f x ≠ ⊤ →
      (∀ᶠ x' in 𝓝 x, f x' ≠ ⊤) ∧ DifferentiableAt ℝ (fun x' => (f x').toReal) x :=
  ae_eventually_ne_top_and_differentiableAt_toReal_of_null_lipschitz_graphs hf hbot
    fun _ hv _ _ hg => measure_range_add_smul_eq_zero_of_dimH_add_one_le hμ hv hg

/-- **Almost-everywhere differentiability of convex functions under measures vanishing on small
sets (`dimH A ≤ finrank ℝ E - 1`).** -/
theorem ae_eventually_ne_top_and_differentiableAt_toReal_of_dimH_le
    [MeasurableSpace E] [OpensMeasurableSpace E] {f : E → EReal} {μ : Measure E}
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥)
    (hμ : ∀ A, MeasurableSet A → dimH A ≤ ((finrank ℝ E - 1 : ℕ) : ℝ≥0∞) → μ A = 0) :
    ∀ᵐ x ∂μ, f x ≠ ⊤ →
      (∀ᶠ x' in 𝓝 x, f x' ≠ ⊤) ∧ DifferentiableAt ℝ (fun x' => (f x').toReal) x :=
  ae_eventually_ne_top_and_differentiableAt_toReal_of_dimH_add_one_le hf hbot
    fun _ hA hdim => measure_eq_zero_of_dimH_add_one_le_of_forall_dimH_le hμ hA hdim

end MeasureZeroAndDifferentiabilityAE

end TauCeti
