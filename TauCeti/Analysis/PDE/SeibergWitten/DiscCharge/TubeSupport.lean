/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.DiscCharge.RootSupport
public import TauCeti.Analysis.Polynomial.ContinuityOfRoots.RootGraph

/-!
# The zero set and the root graph over a tube

In Taubes's analysis of Seiberg–Witten solutions near a pseudoholomorphic curve, the fields are
read in the coordinates of a tube about the curve: a point is a pair `(x, w)` of a base point `x`
of the curve, in a chart `X`, and a dilated normal coordinate `w ∈ ℂ`. The normal slice over `x`
is the disc `w ↦ (x, w)`, that is `Prod.mk x`. Over each base point the cutoff current
`Θ = i F_a + d(χ(|α|²) τ)` has a slice density `f_x` (`TauCeti.SeibergWitten.sliceDensity`), and
the moments of its normalized slice on the closed disc of radius `R` define a Newton polynomial
`P_x` of degree `m`. The **root graph** `{(x, V) | x ∈ s, P_x(V) = 0}` over a set `s` of base
points (`Polynomial.rootGraph`) is the candidate position of the limiting curve, a finite closed
multigraph over `s` once the coefficients of `P_x` depend continuously on `x`.

This file compares the root graph with a set `Z ⊆ X × ℂ` playing the role of the zero set of `α`,
on the whole tube and in both directions, with constants chosen before the fields. Distances are
those of the product `X × ℂ`, in which the slices are isometric. Base points may move: the point
of `Z` attached to a root may lie on a neighbouring slice.

* **No root is missed.** If over every base point of `s` the slice has mass `m`, small negative
  mass and small Newton variance, and the off-zero bound of `Z` holds on the tube, every point of
  the root graph lies within `ε + K h` of `Z`
  (`TauCeti.SeibergWitten.exists_forall_mem_rootGraph_exists_dist_le`).
* **No ghost core.** A point `(x, w₀)` enclosed by a vacuum circle of radius `ρ₁` in its slice,
  around which `α` has positive winding number, lies within `ρ₁ + ε` of the root graph
  (`TauCeti.SeibergWitten.exists_forall_exists_mem_rootGraph_dist_lt`).
* **The two-sided estimate.** If every point of `Z` is enclosed in this way by a circle of radius
  at most `ρ`, the Hausdorff distance between `Z` and the root graph is at most
  `max (ε + K h) (ρ + ε)` (`TauCeti.SeibergWitten.exists_hausdorffEDist_rootGraph_le`).

Along a sequence of fields whose negative masses and Newton variances tend to zero uniformly over
`s`, with `r → ∞`, `h → 0` and enclosing radii `ρ → 0`, the sets `Z` therefore approach the root
graphs of their own Newton polynomials
(`TauCeti.SeibergWitten.tendsto_hausdorffEDist_rootGraph_newtonPolynomial`). If moreover `s` is
compact and the coefficients converge uniformly on `s` to those of monic polynomials `q x` with
continuous coefficients, then by the continuity of roots the sets `Z` converge to the root graph
of `q`, a finite closed multigraph
(`TauCeti.SeibergWitten.tendsto_hausdorffEDist_rootGraph_of_tendstoUniformlyOn`), and every limit
of points of the tube at which `|α|² ≤ 1 / 2`, such as marked points of small `|α|`, lies on it
(`TauCeti.SeibergWitten.mem_rootGraph_of_tendsto_of_normSq_le`).

The inputs that the coupled equations have to supply are hypotheses here, as in
`TauCeti.Analysis.PDE.SeibergWitten.DiscCharge.RootSupport`: the smallness of the Newton variance,
the off-zero bound, the positivity of the winding number of the field around its zeros, and the
uniform convergence of the coefficients of the Newton polynomials.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* C. H. Taubes, *GR = SW: counting curves and connections*, J. Differential Geom. 52 (1999),
  453–609.
-/

public section

noncomputable section

open Complex Filter Metric MeasureTheory Polynomial Set Topology
open scoped Real

namespace TauCeti.SeibergWitten

universe u

/-! ### The two-sided estimate on a tube -/

/-- **No root is missed over the tube.** Fix the constants `C`, `c > 0` and `c₀` of Taubes's
off-zero bound. For every accuracy `ε > 0` there are a tolerance `δ > 0` and constants `K` and
`r₀ > 0` with the following property. Let `Θ` be the cutoff current of a pair `(b, α)` on the tube
`X × ℂ`, with `α` of class `C²` and a cutoff `χ` equal to `1` above `1 / 2`. Suppose that over
every base point `x ∈ s` the slice density along `Prod.mk x` is integrable on the closed disc of
radius `R` and its normalized slice has mass `m`, negative mass at most `δ` and Newton variance
at most `δ`, that `r ≥ r₀` and `h > 0`, and that the off-zero bound relative to `Z` holds on
`s × closedBall 0 R`. Then every point of the root graph of the Newton polynomials over `s` lies
within distance `ε + K h` of a point of `Z`. -/
theorem exists_forall_mem_rootGraph_exists_dist_le (m : ℕ) (R : ℝ) {ε : ℝ} (hε : 0 < ε)
    (C c c₀ : ℝ) (hc : 0 < c) :
    ∃ δ > 0, ∃ K r₀ : ℝ, 0 < r₀ ∧ ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
      {χ : ℝ → ℝ} {b : X × ℂ → (X × ℂ) [⋀^Fin 1]→L[ℝ] ℝ} {α : X × ℂ → ℂ} (s : Set X)
      (Z : Set (X × ℂ)) (r h : ℝ),
      ContDiff ℝ 2 α → EqOn χ 1 (Ioi (1 / 2)) → r₀ ≤ r → 0 < h →
      (∀ x ∈ s, IntegrableOn (sliceDensity χ b α (Prod.mk x)) (closedBall 0 R)) →
      (∀ x ∈ s, (posSliceMeasure (sliceDensity χ b α (Prod.mk x)) R).real univ -
        (negSliceMeasure (sliceDensity χ b α (Prod.mk x)) R).real univ = m) →
      (∀ x ∈ s, (negSliceMeasure (sliceDensity χ b α (Prod.mk x)) R).real univ ≤ δ) →
      (∀ x ∈ s, ∫ w, ‖(newtonPolynomial (fun k ↦
          ∫ w, w ^ k ∂posSliceMeasure (sliceDensity χ b α (Prod.mk x)) R -
          ∫ w, w ^ k ∂negSliceMeasure (sliceDensity χ b α (Prod.mk x)) R) m).eval w‖ ^ 2
          ∂posSliceMeasure (sliceDensity χ b α (Prod.mk x)) R ≤ δ) →
      (∀ y ∈ s ×ˢ closedBall (0 : ℂ) R, ∀ R', c₀ * h ≤ R' → (∀ z ∈ Z, R' ≤ dist y z) →
        max (1 - normSq (α y)) 0 ≤
          C / r * max (1 - normSq (α y)) 0 + C / r + C * Real.exp (-(c * R' / h))) →
      ∀ y ∈ rootGraph (fun x ↦ newtonPolynomial (fun k ↦
          ∫ w, w ^ k ∂posSliceMeasure (sliceDensity χ b α (Prod.mk x)) R -
          ∫ w, w ^ k ∂negSliceMeasure (sliceDensity χ b α (Prod.mk x)) R) m) s,
        ∃ z ∈ Z, dist y z ≤ ε + K * h := by
  obtain ⟨δ, hδ, K, r₀, hr₀, hK⟩ :=
    exists_forall_mem_roots_exists_dist_le_add_mul.{u} m R hε C c c₀ hc
  refine ⟨δ, hδ, K, r₀, hr₀, ?_⟩
  intro X _ _ χ b α s Z r h hα hχ hr hh hf hmass hneg hvar hbound y hy
  obtain ⟨hx, hV⟩ := mem_rootGraph.1 hy
  -- The slice `Prod.mk y.1` is an isometric disc, so the single-slice estimate applies with
  -- `L = 1`.
  obtain ⟨z, hz, hdist⟩ := hK Z r h hα hχ hr hh (LipschitzWith.prodMk_left y.1).lipschitzOnWith
    (hf _ hx) (hmass _ hx) (hneg _ hx) (hvar _ hx) (fun w hw ↦ hbound _ (mk_mem_prod hx hw)) y.2
    ((mem_roots (monic_newtonPolynomial _ _).ne_zero).2 hV)
  exact ⟨z, hz, by simpa using hdist⟩

/-- **No ghost core over the tube.** For every accuracy `ε > 0` there is a tolerance `δ > 0`,
depending only on `m`, `R` and `ε`, with the following property. Let `Θ` be the cutoff current of
a `C²` pair `(b, α)` on the tube `X × ℂ`, for a `C¹` cutoff `χ` vanishing near `0`, and suppose
that over every base point of `s` the normalized slice on the closed disc of radius `R` has mass
`m`, negative mass at most `δ` and Newton variance at most `δ`. If `x ∈ s` and a closed subdisc
of radius `ρ₁ ≥ 0` about `w₀` lies in that disc, with boundary circle in the vacuum
`χ(|α|²) = 1` of the slice over `x` and positive winding number of `α` around it, then `(x, w₀)`
lies within distance `ρ₁ + ε` of a point of the root graph of the Newton polynomials over `s`. -/
theorem exists_forall_exists_mem_rootGraph_dist_lt (m : ℕ) (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {χ : ℝ → ℝ}
      {b : X × ℂ → (X × ℂ) [⋀^Fin 1]→L[ℝ] ℝ} {α : X × ℂ → ℂ} (s : Set X),
      ContDiff ℝ 2 α → ContDiff ℝ 1 b → ContDiff ℝ 1 χ → χ =ᶠ[𝓝 0] 0 →
      (∀ x ∈ s, (posSliceMeasure (sliceDensity χ b α (Prod.mk x)) R).real univ -
        (negSliceMeasure (sliceDensity χ b α (Prod.mk x)) R).real univ = m) →
      (∀ x ∈ s, (negSliceMeasure (sliceDensity χ b α (Prod.mk x)) R).real univ ≤ δ) →
      (∀ x ∈ s, ∫ w, ‖(newtonPolynomial (fun k ↦
          ∫ w, w ^ k ∂posSliceMeasure (sliceDensity χ b α (Prod.mk x)) R -
          ∫ w, w ^ k ∂negSliceMeasure (sliceDensity χ b α (Prod.mk x)) R) m).eval w‖ ^ 2
          ∂posSliceMeasure (sliceDensity χ b α (Prod.mk x)) R ≤ δ) →
      ∀ x ∈ s, ∀ (w₀ : ℂ) (ρ₁ : ℝ), 0 ≤ ρ₁ → closedBall w₀ ρ₁ ⊆ closedBall 0 R →
        (∀ θ, χ (normSq (α (x, circleMap w₀ ρ₁ θ))) = 1) →
        0 < (Contour.windingNumber (α ∘ Prod.mk x ∘ circleMap w₀ ρ₁) (-π) π 0).re →
        ∃ y ∈ rootGraph (fun x ↦ newtonPolynomial (fun k ↦
            ∫ w, w ^ k ∂posSliceMeasure (sliceDensity χ b α (Prod.mk x)) R -
            ∫ w, w ^ k ∂negSliceMeasure (sliceDensity χ b α (Prod.mk x)) R) m) s,
          dist (x, w₀) y < ρ₁ + ε := by
  obtain ⟨δ, hδ, hK⟩ := exists_forall_exists_mem_roots_dist_lt_of_windingNumber.{u} m R hε
  refine ⟨δ, hδ, ?_⟩
  intro X _ _ χ b α s hα hb hχ hχ₀ hmass hneg hvar x hx w₀ ρ₁ hρ₁ hsub hvac hwind
  obtain ⟨V, hV, hdist⟩ := hK hα hb hχ hχ₀ (contDiff_const.prodMk contDiff_id) (hmass x hx)
    (hneg x hx) (hvar x hx) w₀ ρ₁ hρ₁ hsub hvac hwind
  refine ⟨(x, V), mem_rootGraph.2 ⟨hx, (mem_roots (monic_newtonPolynomial _ _).ne_zero).1 hV⟩, ?_⟩
  simpa [Prod.dist_eq, dist_comm] using hdist

/-- **The two-sided support estimate on a tube.** Fix the constants `C`, `c > 0` and `c₀` of
Taubes's off-zero bound. For every accuracy `ε > 0` there are a tolerance `δ > 0` and constants
`K` and `r₀ > 0` with the following property. Let `Θ` be the cutoff current of a `C²` pair
`(b, α)` on the tube `X × ℂ`, for a `C¹` cutoff `χ` vanishing near `0` and equal to `1` above
`1 / 2`. Suppose that over every base point of `s` the normalized slice on the closed disc of
radius `R` has mass `m`, negative mass at most `δ` and Newton variance at most `δ`, that `r ≥ r₀`
and `h > 0`, and that the off-zero bound relative to `Z` holds on `s × closedBall 0 R`. Suppose
finally that every point `(x, w₀)` of `Z` has `x ∈ s` and is enclosed, inside that disc, by a
vacuum circle of radius `ρ₁ ∈ [0, ρ]` around which `α` has positive winding number. Then `Z` and
the root graph of the Newton polynomials over `s` are within Hausdorff distance
`max (ε + K h) (ρ + ε)`. -/
theorem exists_hausdorffEDist_rootGraph_le (m : ℕ) (R : ℝ) {ε : ℝ} (hε : 0 < ε)
    (C c c₀ : ℝ) (hc : 0 < c) :
    ∃ δ > 0, ∃ K r₀ : ℝ, 0 < r₀ ∧ ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
      {χ : ℝ → ℝ} {b : X × ℂ → (X × ℂ) [⋀^Fin 1]→L[ℝ] ℝ} {α : X × ℂ → ℂ} (s : Set X)
      (Z : Set (X × ℂ)) (r h ρ : ℝ),
      ContDiff ℝ 2 α → ContDiff ℝ 1 b → ContDiff ℝ 1 χ → χ =ᶠ[𝓝 0] 0 →
      EqOn χ 1 (Ioi (1 / 2)) → r₀ ≤ r → 0 < h →
      (∀ x ∈ s, (posSliceMeasure (sliceDensity χ b α (Prod.mk x)) R).real univ -
        (negSliceMeasure (sliceDensity χ b α (Prod.mk x)) R).real univ = m) →
      (∀ x ∈ s, (negSliceMeasure (sliceDensity χ b α (Prod.mk x)) R).real univ ≤ δ) →
      (∀ x ∈ s, ∫ w, ‖(newtonPolynomial (fun k ↦
          ∫ w, w ^ k ∂posSliceMeasure (sliceDensity χ b α (Prod.mk x)) R -
          ∫ w, w ^ k ∂negSliceMeasure (sliceDensity χ b α (Prod.mk x)) R) m).eval w‖ ^ 2
          ∂posSliceMeasure (sliceDensity χ b α (Prod.mk x)) R ≤ δ) →
      (∀ y ∈ s ×ˢ closedBall (0 : ℂ) R, ∀ R', c₀ * h ≤ R' → (∀ z ∈ Z, R' ≤ dist y z) →
        max (1 - normSq (α y)) 0 ≤
          C / r * max (1 - normSq (α y)) 0 + C / r + C * Real.exp (-(c * R' / h))) →
      (∀ z ∈ Z, z.1 ∈ s ∧ ∃ ρ₁, 0 ≤ ρ₁ ∧ ρ₁ ≤ ρ ∧ closedBall z.2 ρ₁ ⊆ closedBall 0 R ∧
        (∀ θ, χ (normSq (α (z.1, circleMap z.2 ρ₁ θ))) = 1) ∧
        0 < (Contour.windingNumber (α ∘ Prod.mk z.1 ∘ circleMap z.2 ρ₁) (-π) π 0).re) →
      hausdorffEDist Z (rootGraph (fun x ↦ newtonPolynomial (fun k ↦
          ∫ w, w ^ k ∂posSliceMeasure (sliceDensity χ b α (Prod.mk x)) R -
          ∫ w, w ^ k ∂negSliceMeasure (sliceDensity χ b α (Prod.mk x)) R) m) s) ≤
        ENNReal.ofReal (max (ε + K * h) (ρ + ε)) := by
  obtain ⟨δ₁, hδ₁, K, r₀, hr₀, hroot⟩ :=
    exists_forall_mem_rootGraph_exists_dist_le.{u} m R hε C c c₀ hc
  obtain ⟨δ₂, hδ₂, hcore⟩ := exists_forall_exists_mem_rootGraph_dist_lt.{u} m R hε
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, K, r₀, hr₀, ?_⟩
  intro X _ _ χ b α s Z r h ρ hα hb hχ hχ₀ hχ₁ hr hh hmass hneg hvar hbound hZ
  refine hausdorffEDist_le_of_mem_edist (fun z hz ↦ ?_) fun y hy ↦ ?_
  · obtain ⟨hzs, ρ₁, hρ₁, hρ₁ρ, hsub, hvac, hwind⟩ := hZ z hz
    obtain ⟨y, hy, hdist⟩ := hcore s hα hb hχ hχ₀ hmass
      (fun x hx ↦ (hneg x hx).trans (min_le_right _ _))
      (fun x hx ↦ (hvar x hx).trans (min_le_right _ _)) z.1 hzs z.2 ρ₁ hρ₁ hsub hvac hwind
    refine ⟨y, hy, ?_⟩
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (hdist.le.trans (by linarith [le_max_right (ε + K * h) (ρ + ε)]))
  · -- Each slice density is continuous, hence integrable on the closed disc.
    have hf (x : X) : IntegrableOn (sliceDensity χ b α (Prod.mk x)) (closedBall 0 R) :=
      (continuous_sliceDensity hα hb hχ hχ₀ (contDiff_const.prodMk contDiff_id)).continuousOn
        |>.integrableOn_compact (isCompact_closedBall 0 R)
    obtain ⟨z, hz, hdist⟩ := hroot s Z r h hα hχ₁ hr hh (fun x _ ↦ hf x) hmass
      (fun x hx ↦ (hneg x hx).trans (min_le_left _ _))
      (fun x hx ↦ (hvar x hx).trans (min_le_left _ _)) hbound y hy
    refine ⟨z, hz, ?_⟩
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (hdist.trans (le_max_left _ _))

/-! ### Sequences of fields -/

/-- **The support estimate along a sequence.** Along a filter, let `(b i, α i)` be `C²` pairs on
the tube `X × ℂ`, with a common `C¹` cutoff `χ` vanishing near `0` and equal to `1` above
`1 / 2`. Suppose that eventually, over every base point of `s`, the normalized slice on the closed
disc of radius `R` has mass `m`; that the negative masses and the Newton variances tend to zero
uniformly over `s`; that `r i → ∞` and `h i → 0` with `h i > 0`, and the off-zero bound relative
to `Z i`, with fixed constants `C`, `c > 0` and `c₀`, eventually holds on `s × closedBall 0 R`;
and that eventually every point of `Z i` lies over `s` and is enclosed, inside that disc, by a
vacuum circle of radius at most `ρ i` around which `α i` has positive winding number, where
`ρ i → 0`. Then the Hausdorff distance between `Z i` and the root graph of the Newton polynomials
of `(b i, α i)` over `s` tends to zero. -/
theorem tendsto_hausdorffEDist_rootGraph_newtonPolynomial {ι : Type*} {l : Filter ι}
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {m : ℕ} {R C c c₀ : ℝ} (hc : 0 < c)
    {χ : ℝ → ℝ} {b : ι → X × ℂ → (X × ℂ) [⋀^Fin 1]→L[ℝ] ℝ} {α : ι → X × ℂ → ℂ} {s : Set X}
    {Z : ι → Set (X × ℂ)} {r h ρ : ι → ℝ}
    (hα : ∀ i, ContDiff ℝ 2 (α i)) (hb : ∀ i, ContDiff ℝ 1 (b i)) (hχ : ContDiff ℝ 1 χ)
    (hχ₀ : χ =ᶠ[𝓝 0] 0) (hχ₁ : EqOn χ 1 (Ioi (1 / 2)))
    (hr : Tendsto r l atTop) (hh₀ : ∀ᶠ i in l, 0 < h i) (hh : Tendsto h l (𝓝 0))
    (hρ : Tendsto ρ l (𝓝 0))
    (hmass : ∀ᶠ i in l, ∀ x ∈ s,
      (posSliceMeasure (sliceDensity χ (b i) (α i) (Prod.mk x)) R).real univ -
        (negSliceMeasure (sliceDensity χ (b i) (α i) (Prod.mk x)) R).real univ = m)
    (hneg : ∀ δ > 0, ∀ᶠ i in l, ∀ x ∈ s,
      (negSliceMeasure (sliceDensity χ (b i) (α i) (Prod.mk x)) R).real univ ≤ δ)
    (hvar : ∀ δ > 0, ∀ᶠ i in l, ∀ x ∈ s, ∫ w, ‖(newtonPolynomial (fun k ↦
        ∫ w, w ^ k ∂posSliceMeasure (sliceDensity χ (b i) (α i) (Prod.mk x)) R -
        ∫ w, w ^ k ∂negSliceMeasure (sliceDensity χ (b i) (α i) (Prod.mk x)) R) m).eval w‖ ^ 2
        ∂posSliceMeasure (sliceDensity χ (b i) (α i) (Prod.mk x)) R ≤ δ)
    (hbound : ∀ᶠ i in l, ∀ y ∈ s ×ˢ closedBall (0 : ℂ) R, ∀ R', c₀ * h i ≤ R' →
      (∀ z ∈ Z i, R' ≤ dist y z) →
      max (1 - normSq (α i y)) 0 ≤
        C / r i * max (1 - normSq (α i y)) 0 + C / r i + C * Real.exp (-(c * R' / h i)))
    (hZ : ∀ᶠ i in l, ∀ z ∈ Z i, z.1 ∈ s ∧ ∃ ρ₁, 0 ≤ ρ₁ ∧ ρ₁ ≤ ρ i ∧
      closedBall z.2 ρ₁ ⊆ closedBall 0 R ∧
      (∀ θ, χ (normSq (α i (z.1, circleMap z.2 ρ₁ θ))) = 1) ∧
      0 < (Contour.windingNumber (α i ∘ Prod.mk z.1 ∘ circleMap z.2 ρ₁) (-π) π 0).re) :
    Tendsto (fun i ↦ hausdorffEDist (Z i) (rootGraph (fun x ↦ newtonPolynomial (fun k ↦
        ∫ w, w ^ k ∂posSliceMeasure (sliceDensity χ (b i) (α i) (Prod.mk x)) R -
        ∫ w, w ^ k ∂negSliceMeasure (sliceDensity χ (b i) (α i) (Prod.mk x)) R) m) s))
      l (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.2 fun η hη ↦ ?_
  obtain ⟨t, -, ht, htη⟩ := ENNReal.lt_iff_exists_real_btwn.1 hη
  have ht₀ : 0 < t := ENNReal.ofReal_pos.1 ht
  -- Run the two-sided estimate with accuracy `t / 3`; eventually `K h i` and `ρ i` are at most
  -- `t / 3` as well, so the Hausdorff distance is at most `2 t / 3`.
  obtain ⟨δ, hδ, K, r₀, -, hsupp⟩ :=
    exists_hausdorffEDist_rootGraph_le.{u} m R (by positivity : 0 < t / 3) C c c₀ hc
  have hKh : Tendsto (fun i ↦ K * h i) l (𝓝 0) := by simpa using hh.const_mul K
  filter_upwards [hr.eventually_ge_atTop r₀, hh₀, hmass, hneg δ hδ, hvar δ hδ, hbound, hZ,
    hKh.eventually (eventually_le_nhds (by positivity : 0 < t / 3)),
    hρ.eventually (eventually_le_nhds (by positivity : 0 < t / 3))]
    with i hri hhi hmi hni hvi hbi hZi hKhi hρi
  refine (hsupp s (Z i) (r i) (h i) (ρ i) (hα i) (hb i) hχ hχ₀ hχ₁ hri hhi hmi hni hvi hbi
    hZi).trans (le_trans ?_ htη.le)
  exact ENNReal.ofReal_le_ofReal (max_le (by linarith) (by linarith))

/-- **Two-sided convergence to the limiting root multigraph.** Under the hypotheses of
`TauCeti.SeibergWitten.tendsto_hausdorffEDist_rootGraph_newtonPolynomial`, let `s` be compact and
let `q x` be monic polynomials of degree `m` whose lower coefficients are continuous on `s` and
are the uniform limits on `s` of the coefficients of the Newton polynomials of `(b i, α i)`. Then
the sets `Z i` converge, in the Hausdorff distance of `X × ℂ`, to the root graph of `q` over `s`,
a compact multigraph with at most `m` points over each base point. -/
theorem tendsto_hausdorffEDist_rootGraph_of_tendstoUniformlyOn {ι : Type*} {l : Filter ι}
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {m : ℕ} {R C c c₀ : ℝ} (hc : 0 < c)
    {χ : ℝ → ℝ} {b : ι → X × ℂ → (X × ℂ) [⋀^Fin 1]→L[ℝ] ℝ} {α : ι → X × ℂ → ℂ} {s : Set X}
    {Z : ι → Set (X × ℂ)} {r h ρ : ι → ℝ} {q : X → ℂ[X]}
    (hα : ∀ i, ContDiff ℝ 2 (α i)) (hb : ∀ i, ContDiff ℝ 1 (b i)) (hχ : ContDiff ℝ 1 χ)
    (hχ₀ : χ =ᶠ[𝓝 0] 0) (hχ₁ : EqOn χ 1 (Ioi (1 / 2)))
    (hr : Tendsto r l atTop) (hh₀ : ∀ᶠ i in l, 0 < h i) (hh : Tendsto h l (𝓝 0))
    (hρ : Tendsto ρ l (𝓝 0))
    (hmass : ∀ᶠ i in l, ∀ x ∈ s,
      (posSliceMeasure (sliceDensity χ (b i) (α i) (Prod.mk x)) R).real univ -
        (negSliceMeasure (sliceDensity χ (b i) (α i) (Prod.mk x)) R).real univ = m)
    (hneg : ∀ δ > 0, ∀ᶠ i in l, ∀ x ∈ s,
      (negSliceMeasure (sliceDensity χ (b i) (α i) (Prod.mk x)) R).real univ ≤ δ)
    (hvar : ∀ δ > 0, ∀ᶠ i in l, ∀ x ∈ s, ∫ w, ‖(newtonPolynomial (fun k ↦
        ∫ w, w ^ k ∂posSliceMeasure (sliceDensity χ (b i) (α i) (Prod.mk x)) R -
        ∫ w, w ^ k ∂negSliceMeasure (sliceDensity χ (b i) (α i) (Prod.mk x)) R) m).eval w‖ ^ 2
        ∂posSliceMeasure (sliceDensity χ (b i) (α i) (Prod.mk x)) R ≤ δ)
    (hbound : ∀ᶠ i in l, ∀ y ∈ s ×ˢ closedBall (0 : ℂ) R, ∀ R', c₀ * h i ≤ R' →
      (∀ z ∈ Z i, R' ≤ dist y z) →
      max (1 - normSq (α i y)) 0 ≤
        C / r i * max (1 - normSq (α i y)) 0 + C / r i + C * Real.exp (-(c * R' / h i)))
    (hZ : ∀ᶠ i in l, ∀ z ∈ Z i, z.1 ∈ s ∧ ∃ ρ₁, 0 ≤ ρ₁ ∧ ρ₁ ≤ ρ i ∧
      closedBall z.2 ρ₁ ⊆ closedBall 0 R ∧
      (∀ θ, χ (normSq (α i (z.1, circleMap z.2 ρ₁ θ))) = 1) ∧
      0 < (Contour.windingNumber (α i ∘ Prod.mk z.1 ∘ circleMap z.2 ρ₁) (-π) π 0).re)
    (hs : IsCompact s) (hq : ∀ x ∈ s, (q x).Monic ∧ (q x).natDegree = m)
    (hqc : ∀ k < m, ContinuousOn (fun x ↦ (q x).coeff k) s)
    (hpq : ∀ j < m, TendstoUniformlyOn (fun i x ↦ (newtonPolynomial (fun k ↦
        ∫ w, w ^ k ∂posSliceMeasure (sliceDensity χ (b i) (α i) (Prod.mk x)) R -
        ∫ w, w ^ k ∂negSliceMeasure (sliceDensity χ (b i) (α i) (Prod.mk x)) R) m).coeff j)
      (fun x ↦ (q x).coeff j) l s) :
    Tendsto (fun i ↦ hausdorffEDist (Z i) (rootGraph q s)) l (𝓝 0) :=
  Polynomial.tendsto_hausdorffEDist_rootGraph_of_tendsto hs hq
    (Eventually.of_forall fun _ _ _ ↦ ⟨monic_newtonPolynomial _ _, natDegree_newtonPolynomial _ _⟩)
    hqc hpq (tendsto_hausdorffEDist_rootGraph_newtonPolynomial hc hα hb hχ hχ₀ hχ₁ hr hh₀ hh hρ
      hmass hneg hvar hbound hZ)

/-- **Retention of marked points.** Under the hypotheses of
`TauCeti.SeibergWitten.tendsto_hausdorffEDist_rootGraph_of_tendstoUniformlyOn`, let `y i` be
points of the tube `s × closedBall 0 R` at which eventually `|α i (y i)|² ≤ 1 / 2`, such as
marked points at which `α i` is small. If `y i → y₀`, then `y₀` lies on the root graph of `q`
over `s`. -/
theorem mem_rootGraph_of_tendsto_of_normSq_le {ι : Type*} {l : Filter ι} [l.NeBot]
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {m : ℕ} {R C c c₀ : ℝ} (hc : 0 < c)
    {χ : ℝ → ℝ} {b : ι → X × ℂ → (X × ℂ) [⋀^Fin 1]→L[ℝ] ℝ} {α : ι → X × ℂ → ℂ} {s : Set X}
    {Z : ι → Set (X × ℂ)} {r h ρ : ι → ℝ} {q : X → ℂ[X]}
    (hα : ∀ i, ContDiff ℝ 2 (α i)) (hb : ∀ i, ContDiff ℝ 1 (b i)) (hχ : ContDiff ℝ 1 χ)
    (hχ₀ : χ =ᶠ[𝓝 0] 0) (hχ₁ : EqOn χ 1 (Ioi (1 / 2)))
    (hr : Tendsto r l atTop) (hh₀ : ∀ᶠ i in l, 0 < h i) (hh : Tendsto h l (𝓝 0))
    (hρ : Tendsto ρ l (𝓝 0))
    (hmass : ∀ᶠ i in l, ∀ x ∈ s,
      (posSliceMeasure (sliceDensity χ (b i) (α i) (Prod.mk x)) R).real univ -
        (negSliceMeasure (sliceDensity χ (b i) (α i) (Prod.mk x)) R).real univ = m)
    (hneg : ∀ δ > 0, ∀ᶠ i in l, ∀ x ∈ s,
      (negSliceMeasure (sliceDensity χ (b i) (α i) (Prod.mk x)) R).real univ ≤ δ)
    (hvar : ∀ δ > 0, ∀ᶠ i in l, ∀ x ∈ s, ∫ w, ‖(newtonPolynomial (fun k ↦
        ∫ w, w ^ k ∂posSliceMeasure (sliceDensity χ (b i) (α i) (Prod.mk x)) R -
        ∫ w, w ^ k ∂negSliceMeasure (sliceDensity χ (b i) (α i) (Prod.mk x)) R) m).eval w‖ ^ 2
        ∂posSliceMeasure (sliceDensity χ (b i) (α i) (Prod.mk x)) R ≤ δ)
    (hbound : ∀ᶠ i in l, ∀ y ∈ s ×ˢ closedBall (0 : ℂ) R, ∀ R', c₀ * h i ≤ R' →
      (∀ z ∈ Z i, R' ≤ dist y z) →
      max (1 - normSq (α i y)) 0 ≤
        C / r i * max (1 - normSq (α i y)) 0 + C / r i + C * Real.exp (-(c * R' / h i)))
    (hZ : ∀ᶠ i in l, ∀ z ∈ Z i, z.1 ∈ s ∧ ∃ ρ₁, 0 ≤ ρ₁ ∧ ρ₁ ≤ ρ i ∧
      closedBall z.2 ρ₁ ⊆ closedBall 0 R ∧
      (∀ θ, χ (normSq (α i (z.1, circleMap z.2 ρ₁ θ))) = 1) ∧
      0 < (Contour.windingNumber (α i ∘ Prod.mk z.1 ∘ circleMap z.2 ρ₁) (-π) π 0).re)
    (hs : IsCompact s) (hq : ∀ x ∈ s, (q x).Monic ∧ (q x).natDegree = m)
    (hqc : ∀ k < m, ContinuousOn (fun x ↦ (q x).coeff k) s)
    (hpq : ∀ j < m, TendstoUniformlyOn (fun i x ↦ (newtonPolynomial (fun k ↦
        ∫ w, w ^ k ∂posSliceMeasure (sliceDensity χ (b i) (α i) (Prod.mk x)) R -
        ∫ w, w ^ k ∂negSliceMeasure (sliceDensity χ (b i) (α i) (Prod.mk x)) R) m).coeff j)
      (fun x ↦ (q x).coeff j) l s)
    {y : ι → X × ℂ} (hy : ∀ᶠ i in l, y i ∈ s ×ˢ closedBall (0 : ℂ) R ∧ normSq (α i (y i)) ≤ 1 / 2)
    {y₀ : X × ℂ} (hy₀ : Tendsto y l (𝓝 y₀)) :
    y₀ ∈ rootGraph q s := by
  obtain ⟨K, r₀, -, hK⟩ := exists_forall_exists_dist_le_of_le.{u} C c c₀ hc (σ := 1 / 2)
    (by norm_num)
  -- Pick, whenever there is one, a point `z i ∈ Z i` within `K h i` of `y i`.
  have hpick (i : ι) : ∃ z : X × ℂ, (∃ w ∈ Z i, dist (y i) w ≤ K * h i) →
      z ∈ Z i ∧ dist (y i) z ≤ K * h i := by
    by_cases H : ∃ w ∈ Z i, dist (y i) w ≤ K * h i
    · obtain ⟨w, hw, hd⟩ := H
      exact ⟨w, fun _ ↦ ⟨hw, hd⟩⟩
    · exact ⟨y i, fun H' ↦ absurd H' H⟩
  choose z hz using hpick
  have hzZ : ∀ᶠ i in l, z i ∈ Z i ∧ dist (y i) (z i) ≤ K * h i := by
    filter_upwards [hr.eventually_ge_atTop r₀, hh₀, hbound, hy] with i hri hhi hbi hyi
    exact hz i (hK (fun y ↦ normSq (α i y)) (Z i) (r i) (h i) hri hhi (y i) (hbi (y i) hyi.1)
      hyi.2)
  -- The points `z i` converge to `y₀`, since `dist (z i) y₀ ≤ K h i + dist (y i) y₀`.
  have hz₀ : Tendsto z l (𝓝 y₀) := by
    have hlim : Tendsto (fun i ↦ K * h i + dist (y i) y₀) l (𝓝 0) := by
      simpa using (hh.const_mul K).add (tendsto_iff_dist_tendsto_zero.1 hy₀)
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun _ ↦
      dist_nonneg) (hzZ.mono fun i hi ↦ ?_) hlim)
    calc dist (z i) y₀ ≤ dist (z i) (y i) + dist (y i) y₀ := dist_triangle _ _ _
      _ ≤ K * h i + dist (y i) y₀ := by rw [dist_comm]; gcongr; exact hi.2
  exact Polynomial.mem_rootGraph_of_tendsto hs hs.isClosed hq
    (Eventually.of_forall fun _ _ _ ↦ ⟨monic_newtonPolynomial _ _, natDegree_newtonPolynomial _ _⟩)
    hqc hpq (tendsto_hausdorffEDist_rootGraph_newtonPolynomial hc hα hb hχ hχ₀ hχ₁ hr hh₀ hh hρ
      hmass hneg hvar hbound hZ) (hzZ.mono fun _ hi ↦ hi.1) hz₀

end TauCeti.SeibergWitten
