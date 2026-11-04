/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Convergence
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Analysis.Calculus.FDeriv.WithLp
import TauCeti.Geometry.Symplectic.Floer.Graph
import TauCeti.MeasureTheory.Integral.EnergyConcentration
import TauCeti.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Compactness of Floer solutions away from finitely many bubbling points

In local coordinates `z = s + i t ∈ ℂ` on the domain and `x ∈ V` on the target, the
inhomogeneous Cauchy–Riemann equation of Hamiltonian Floer theory reads

`∂ₜu - X(z, u) i = J(z, u) (∂ₛu - X(z, u) 1)`,

where `J(z, x)` is an almost complex structure on `V` depending on the domain point and
`X(z, x) : ℂ →L[ℝ] V` is the Hamiltonian one-form. For a perturbation `K = K_s ds + K_t dt` it is
`ξ ↦ (re ξ) X_{K_s} + (im ξ) X_{K_t}`, the coordinate form of
`TauCeti.SymplecticForm.hamiltonianOneForm`. The equation says that the perturbed derivative
`du - X(z, u)` is complex linear.

Gromov's graph construction (`TauCeti.Geometry.Symplectic.Floer.Graph`) turns solutions into
pseudoholomorphic curves: the graph `U y = (y, u y)` solves the autonomous equation
`∂ₜU = J'(U) ∂ₛU` for the structure

`J'(z, x)(ξ, v) = (i ξ, J(z, x)(v - X(z, x) ξ) + X(z, x)(i ξ))`

on `ℂ × V` (`TauCeti.Floer.fderiv_toLp_prodMk_I_eq_graphStructure_iff`). It is written as a
continuous-linear-map-valued function on the Euclidean product `WithLp 2 (ℂ × V)`
(`TauCeti.Floer.graphStructure`); for Floer data `ω`, `J`, `K_s`, `K_t` it is the structure
`TauCeti.SymplecticForm.floerGraphAlmostComplex` of the graph construction read in complex
coordinates (`TauCeti.Floer.graphStructure_toLp_eq_floerGraphAlmostComplex`). That is the form
in which the local compactness theory of `TauCeti.Geometry.Symplectic.JHolomorphic.Energy`
applies, which needs a `C²` structure on an inner product space: `J'² = -1` wherever `J² = -1`
(`TauCeti.Floer.graphStructure_graphStructure`), and `J'` is as regular as `J` and `X`
(`TauCeti.Floer.contDiffOn_graphStructure`). The graph has energy density
`‖∂ₛU‖² = 1 + ‖∂ₛu‖²` (`TauCeti.norm_fderiv_toLp_prodMk_apply_sq`), so on a domain of finite area
bounded energy of `u` gives bounded energy of its graph. The small-energy estimate for the graph
becomes a mean-value inequality for `u`
(`TauCeti.Floer.exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_of_small_energy`):
on a disc of radius `r` whose graph energy `π r² + ∫ ‖∂ₛu‖²` is below a threshold,
`π r² ‖∂ₛu(z₀)‖² ≤ 7 π r² + 8 ∫ ‖∂ₛu‖²` at the centre.

The main result transfers Gromov compactness off finitely many points to Floer solutions
(`TauCeti.Floer.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset`). Fix a compact
window `D` of the domain and a compact set `K` of the target on which the data are `C²`. There is a
threshold `δ > 0` such that every sequence of solutions on an open `Ω ⊆ D` with image in `K` and
energy `∫_Ω ‖∂ₛu‖² ≤ E` has a subsequence converging locally uniformly off a finite set `Z` of
bubbling points, with derivatives bounded on compact subsets of `Ω \ Z`, `#Z * δ ≤ E`, and energy
at least `δ` concentrating at each point of `Z`. The threshold is half the graph threshold: the
area of a small disc carries the rest of the graph energy. The limit is only shown to be
continuous; its regularity, the rescaled bubbles at the points of `Z` (spheres for the structure
`J(z, ·)` frozen at the bubbling point), and breaking along cylindrical ends are not treated here.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. 82 (1985),
  307–347.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (the graph construction for the
  inhomogeneous equation).
-/

public section

open Complex ContinuousLinearMap Filter MeasureTheory Metric Real Set Topology

namespace TauCeti.Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The graph of `u` has energy density `‖∂ₛU‖² = 1 + ‖∂ₛu‖²`. -/
private theorem norm_fderiv_graph_one_sq {u : ℂ → V} {y : ℂ} (hu : DifferentiableAt ℝ u y) :
    ‖fderiv ℝ (fun w ↦ WithLp.toLp 2 (w, u w)) y 1‖ ^ 2 = 1 + ‖fderiv ℝ u y 1‖ ^ 2 := by
  simpa using norm_fderiv_toLp_prodMk_apply_sq differentiableAt_fun_id hu 1

/-- On a set of finite area, the energy of the graph of `u` is the area plus the energy of `u`. -/
private theorem setIntegral_norm_fderiv_graph_one_sq {u : ℂ → V} {S : Set ℂ}
    (hS : MeasurableSet S) (hSv : volume S ≠ ⊤) (hu : ∀ y ∈ S, DifferentiableAt ℝ u y)
    (hint : IntegrableOn (fun y ↦ ‖fderiv ℝ u y 1‖ ^ 2) S) :
    ∫ y in S, ‖fderiv ℝ (fun w ↦ WithLp.toLp 2 (w, u w)) y 1‖ ^ 2 =
      volume.real S + ∫ y in S, ‖fderiv ℝ u y 1‖ ^ 2 := by
  rw [setIntegral_congr_fun hS fun y hy ↦ norm_fderiv_graph_one_sq (hu y hy),
    integral_add (integrableOn_const hSv) hint, setIntegral_const, smul_eq_mul, mul_one]

/-- If energy at least `δ` of the graphs eventually concentrates in every disc about `z`, then
energy at least `δ / 2` of the maps themselves eventually concentrates in every disc about `z`:
on a disc of area at most `δ / 2`, the area carries the rest of the graph energy. -/
private theorem eventually_half_le_setIntegral_of_graph {ι : Type*} {l : Filter ι}
    {u : ι → ℂ → V} {Ω : Set ℂ} {z : ℂ} {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hΩ : MeasurableSet Ω) (hvol : volume Ω ≠ ⊤) (hdiff : ∀ i, ∀ y ∈ Ω, DifferentiableAt ℝ (u i) y)
    (hint : ∀ i, IntegrableOn (fun y ↦ ‖fderiv ℝ (u i) y 1‖ ^ 2) Ω)
    (hconc : ∀ ρ > 0, ∀ᶠ i in l,
      δ ≤ ∫ y in ball z ρ ∩ Ω, ‖fderiv ℝ (fun w ↦ WithLp.toLp 2 (w, u i w)) y 1‖ ^ 2) :
    ∀ᶠ i in l, δ / 2 ≤ ∫ y in ball z ε ∩ Ω, ‖fderiv ℝ (u i) y 1‖ ^ 2 := by
  set ρ := min ε (Real.sqrt (δ / (2 * π)))
  have hρ : 0 < ρ := lt_min hε (Real.sqrt_pos.2 (by positivity))
  have hρvol : volume.real (ball z ρ ∩ Ω) ≤ δ / 2 := by
    calc volume.real (ball z ρ ∩ Ω) ≤ volume.real (ball z ρ) :=
          measureReal_mono inter_subset_left measure_ball_lt_top.ne
      _ = π * ρ ^ 2 := Complex.volume_real_ball z hρ.le
      _ ≤ π * Real.sqrt (δ / (2 * π)) ^ 2 := by
          gcongr
          exact min_le_right _ _
      _ = δ / 2 := by
          rw [Real.sq_sqrt (by positivity)]
          field_simp
  have hmeas : MeasurableSet (ball z ρ ∩ Ω) := measurableSet_ball.inter hΩ
  filter_upwards [hconc ρ hρ] with i hi
  rw [setIntegral_norm_fderiv_graph_one_sq hmeas
    ((measure_mono inter_subset_right).trans_lt hvol.lt_top).ne (fun y hy ↦ hdiff i y hy.2)
    ((hint i).mono_set inter_subset_right)] at hi
  calc δ / 2 ≤ ∫ y in ball z ρ ∩ Ω, ‖fderiv ℝ (u i) y 1‖ ^ 2 := by linarith
    _ ≤ ∫ y in ball z ε ∩ Ω, ‖fderiv ℝ (u i) y 1‖ ^ 2 :=
      setIntegral_mono_set ((hint i).mono_set inter_subset_right)
        (ae_restrict_of_forall_mem (measurableSet_ball.inter hΩ) fun _ _ ↦ sq_nonneg _)
        (inter_subset_inter_left _ (ball_subset_ball (min_le_left _ _))).eventuallyLE

/-- **The mean-value inequality for Floer solutions.** Let `J` and `X` be `C²` on an open set
`W ⊆ ℂ × V` containing `D × K` for compact `D ⊆ ℂ` and `K ⊆ V`, with `J(z, x)² = -1` on `D × K`.
There is a threshold `δ > 0` with the following property. Let `u` be `C³` on an open disc
`B_r(z₀) ⊆ D`, with `∂ₛu` continuous up to the boundary, and on the disc let it solve
`∂ₜu - X(z, u) i = J(z, u)(∂ₛu - X(z, u) 1)` with image in `K`. If the energy
`π r² + ∫_{B_r(z₀)} ‖∂ₛu‖²` of its graph over the disc is less than `δ`, then
`π r² ‖∂ₛu(z₀)‖² ≤ 7 π r² + 8 ∫_{B_r(z₀)} ‖∂ₛu‖²`. -/
theorem exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_of_small_energy
    {J : ℂ × V → V →L[ℝ] V} {X : ℂ × V → ℂ →L[ℝ] V} {W : Set (ℂ × V)} {D : Set ℂ} {K : Set V}
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hX : ContDiffOn ℝ 2 X W)
    (hD : IsCompact D) (hK : IsCompact K) (hDKW : D ×ˢ K ⊆ W)
    (hJsq : ∀ z ∈ D, ∀ x ∈ K, ∀ v, J (z, x) (J (z, x) v) = -v) :
    ∃ δ > 0, ∀ ⦃u : ℂ → V⦄ ⦃z₀ : ℂ⦄ ⦃r : ℝ⦄, 0 ≤ r → ball z₀ r ⊆ D →
      ContDiffOn ℝ 3 u (ball z₀ r) → ContinuousOn (fun y ↦ fderiv ℝ u y 1) (closedBall z₀ r) →
      (∀ y ∈ ball z₀ r, fderiv ℝ u y I - X (y, u y) I =
        J (y, u y) (fderiv ℝ u y 1 - X (y, u y) 1)) →
      (∀ y ∈ ball z₀ r, u y ∈ K) →
      π * r ^ 2 + ∫ y in ball z₀ r, ‖fderiv ℝ u y 1‖ ^ 2 < δ →
      π * r ^ 2 * ‖fderiv ℝ u z₀ 1‖ ^ 2 ≤
        7 * π * r ^ 2 + 8 * ∫ y in ball z₀ r, ‖fderiv ℝ u y 1‖ ^ 2 := by
  obtain ⟨δ, hδ, hmean⟩ :=
    _root_.TauCeti.exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_eight_mul_setIntegral_ball
      (hW.preimage (WithLp.prod_continuous_ofLp 2 ℂ V)) (contDiffOn_graphStructure hJ hX)
      ((WithLp.prodContinuousLinearEquiv 2 ℝ ℂ V).toHomeomorph.isCompact_preimage.2
        (hD.prod hK)) (preimage_mono hDKW)
      fun p hp ζ ↦ graphStructure_graphStructure (hJsq _ hp.1 _ hp.2) ζ
  refine ⟨δ, hδ, fun u z₀ r hr hrD hu hu' hCR huK hE ↦ ?_⟩
  have hdiff : ∀ y ∈ ball z₀ r, DifferentiableAt ℝ u y := fun y hy ↦
    (hu.differentiableOn (by norm_num)).differentiableAt (isOpen_ball.mem_nhds hy)
  have hint : IntegrableOn (fun y ↦ ‖fderiv ℝ u y 1‖ ^ 2) (ball z₀ r) :=
    (hu'.norm.pow 2).integrableOn_compact (isCompact_closedBall z₀ r)
      |>.mono_set ball_subset_closedBall
  -- The graph need not be differentiable on the boundary circle, so apply the estimate for the
  -- graph on every smaller disc `B_ρ(z₀)`, `ρ < r`, and let `ρ` tend to `r`.
  have hsmall : ∀ ρ, 0 ≤ ρ → ρ < r → π * ρ ^ 2 * ‖fderiv ℝ u z₀ 1‖ ^ 2 ≤
      7 * π * r ^ 2 + 8 * ∫ y in ball z₀ r, ‖fderiv ℝ u y 1‖ ^ 2 := by
    intro ρ hρ hρr
    have hsub : closedBall z₀ ρ ⊆ ball z₀ r := closedBall_subset_ball hρr
    have hsub' : ball z₀ ρ ⊆ ball z₀ r := ball_subset_closedBall.trans hsub
    -- The energy of the graph on `B_ρ(z₀)` is its area `π ρ²` plus the energy of `u`.
    have hgE := setIntegral_norm_fderiv_graph_one_sq measurableSet_ball measure_ball_lt_top.ne
      (fun y hy ↦ hdiff y (hsub' hy)) (hint.mono_set hsub')
    rw [Complex.volume_real_ball z₀ hρ] at hgE
    have hmono : ∫ y in ball z₀ ρ, ‖fderiv ℝ u y 1‖ ^ 2 ≤
        ∫ y in ball z₀ r, ‖fderiv ℝ u y 1‖ ^ 2 :=
      setIntegral_mono_set hint (ae_restrict_of_forall_mem measurableSet_ball
        fun _ _ ↦ sq_nonneg _) (ball_subset_ball hρr.le).eventuallyLE
    have hπ : π * ρ ^ 2 ≤ π * r ^ 2 := by gcongr
    have h := hmean (u := fun w ↦ WithLp.toLp 2 (w, u w)) hρ
      (WithLp.contDiff_toLp.comp_contDiffOn (contDiffOn_id.prodMk (hu.mono
        (ball_subset_closedBall.trans hsub))))
      (((WithLp.prod_continuous_toLp 2 ℂ V).comp_continuousOn
        ((continuousOn_const (c := (1 : ℂ))).prodMk
          (hu'.mono (hsub.trans ball_subset_closedBall)))).congr fun y hy ↦ by
          simp [fderiv_toLp_prodMk_apply differentiableAt_fun_id (hdiff y (hsub hy))])
      (fun y hy ↦ (fderiv_toLp_prodMk_I_eq_graphStructure_iff (hdiff y (hsub' hy))).2
        (hCR y (hsub' hy)))
      (fun y hy ↦ ⟨hrD (hsub' hy), huK y (hsub' hy)⟩)
      (by rw [hgE]; linarith)
    rw [hgE, norm_fderiv_graph_one_sq (hdiff z₀ (mem_ball_self (hρ.trans_lt hρr)))] at h
    linarith
  rcases hr.eq_or_lt with rfl | hr
  · simp
  refine le_of_tendsto (((by fun_prop : Continuous fun ρ : ℝ ↦
    π * ρ ^ 2 * ‖fderiv ℝ u z₀ 1‖ ^ 2).tendsto r).mono_left (nhdsWithin_le_nhds (s := Iio r))) ?_
  filter_upwards [Ioo_mem_nhdsLT hr] with ρ hρr using hsmall ρ hρr.1.le hρr.2

/-- **Floer solutions converge off finitely many bubbling points.** Let `J` and `X` be `C²` on an
open set `W ⊆ ℂ × V` containing `D × K` for compact `D ⊆ ℂ` and `K ⊆ V`, with `J(z, x)² = -1` on
`D × K`. There is a threshold `δ > 0` with the following property. Let `uₖ` be `C³` solutions of
`∂ₜu - X(z, u) i = J(z, u)(∂ₛu - X(z, u) 1)` on an open set `Ω ⊆ D`, with image in `K` and
energy `∫_Ω ‖∂ₛuₖ‖² ≤ E`. Then there are a subsequence `φ`, a finite set `Z ⊆ Ω` with
`#Z * δ ≤ E`, and a continuous `v : Ω \ Z → K` such that along `φ` every disc about a point of `Z`
eventually carries energy at least `δ`, the differentials are uniformly bounded on every compact
subset of `Ω \ Z`, and `u_{φ n} → v` locally uniformly on `Ω \ Z`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset
    {J : ℂ × V → V →L[ℝ] V} {X : ℂ × V → ℂ →L[ℝ] V} {W : Set (ℂ × V)} {D : Set ℂ} {K : Set V}
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hX : ContDiffOn ℝ 2 X W)
    (hD : IsCompact D) (hK : IsCompact K) (hDKW : D ×ˢ K ⊆ W)
    (hJsq : ∀ z ∈ D, ∀ x ∈ K, ∀ v, J (z, x) (J (z, x) v) = -v) :
    ∃ δ > 0, ∀ ⦃Ω : Set ℂ⦄ ⦃u : ℕ → ℂ → V⦄ ⦃E : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, ContDiffOn ℝ 3 (u k) Ω) →
      (∀ k, ∀ y ∈ Ω, fderiv ℝ (u k) y I - X (y, u k y) I =
        J (y, u k y) (fderiv ℝ (u k) y 1 - X (y, u k y) 1)) →
      (∀ k, MapsTo (u k) Ω K) →
      (∀ k, IntegrableOn (fun y ↦ ‖fderiv ℝ (u k) y 1‖ ^ 2) Ω) →
      (∀ k, ∫ y in Ω, ‖fderiv ℝ (u k) y 1‖ ^ 2 ≤ E) →
      ∃ (φ : ℕ → ℕ) (Z : Finset ℂ) (v : ℂ → V), StrictMono φ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z ε ∩ Ω, ‖fderiv ℝ (u (φ n)) y 1‖ ^ 2) ∧
        (∀ C, IsCompact C → C ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C, ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) := by
  classical
  -- Apply the compactness theorem for pseudoholomorphic curves to the graphs, with target the
  -- compact set `D × K` of `WithLp 2 (ℂ × V)`.
  obtain ⟨δ, hδ, hconv⟩ :=
    _root_.TauCeti.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset
    (hW.preimage (WithLp.prod_continuous_ofLp 2 ℂ V)) (contDiffOn_graphStructure hJ hX)
    ((WithLp.prodContinuousLinearEquiv 2 ℝ ℂ V).toHomeomorph.isCompact_preimage.2 (hD.prod hK))
    (preimage_mono hDKW) fun p hp ζ ↦ graphStructure_graphStructure (hJsq _ hp.1 _ hp.2) ζ
  refine ⟨δ / 2, half_pos hδ, fun Ω u E hΩ hΩD hu hCR huK hint hE ↦ ?_⟩
  set g : ℕ → ℂ → WithLp 2 (ℂ × V) := fun k w ↦ WithLp.toLp 2 (w, u k w)
  have hdiff : ∀ k, ∀ y ∈ Ω, DifferentiableAt ℝ (u k) y := fun k y hy ↦
    ((hu k).differentiableOn (by norm_num)).differentiableAt (hΩ.mem_nhds hy)
  have hvol : volume Ω < ⊤ := (measure_mono hΩD).trans_lt hD.measure_lt_top
  have hgint : ∀ k, IntegrableOn (fun y ↦ ‖fderiv ℝ (g k) y 1‖ ^ 2) Ω := fun k ↦
    ((integrableOn_const hvol.ne).add (hint k)).congr_fun
      (fun y hy ↦ (norm_fderiv_graph_one_sq (hdiff k y hy)).symm) hΩ.measurableSet
  have hgE : ∀ k, ∫ y in Ω, ‖fderiv ℝ (g k) y 1‖ ^ 2 ≤ volume.real Ω + E := fun k ↦
    (setIntegral_norm_fderiv_graph_one_sq hΩ.measurableSet hvol.ne (hdiff k) (hint k)).trans_le
      (by linarith [hE k])
  obtain ⟨φ, Z, w, hφ, hZΩ, -, hconc, hbd, hwcont, hwK, hlim⟩ := hconv hΩ
    (u := g) (fun k ↦ WithLp.contDiff_toLp.comp_contDiffOn (contDiffOn_id.prodMk (hu k)))
    (fun k y hy ↦ (fderiv_toLp_prodMk_I_eq_graphStructure_iff (hdiff k y hy)).2 (hCR k y hy))
    (fun k y hy ↦ ⟨hΩD hy, huK k hy⟩) hgint hgE
  -- Energy at least `δ` of the graphs concentrates at `Z`, so energy at least `δ / 2` of the
  -- maps does.
  have hconc' : ∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
      δ / 2 ≤ ∫ y in ball z ε ∩ Ω, ‖fderiv ℝ (u (φ n)) y 1‖ ^ 2 := fun z hz ε hε ↦
    eventually_half_le_setIntegral_of_graph hδ hε hΩ.measurableSet hvol.ne
      (fun n ↦ hdiff (φ n)) (fun n ↦ hint (φ n)) (hconc z hz)
  refine ⟨φ, Z, fun z ↦ (w z).snd, hφ, hZΩ,
    card_mul_le_of_forall_eventually_le_setIntegral_ball (l := atTop) hΩ.measurableSet
      (fun _ _ _ ↦ sq_nonneg _) (fun n ↦ hint (φ n)) (fun n ↦ hE (φ n)) hconc', hconc', ?_,
    (WithLp.sndL 2 ℝ ℂ V).continuous.comp_continuousOn hwcont, fun z hz ↦ (hwK hz).2, ?_⟩
  · intro C hC hCZ
    obtain ⟨M, hM⟩ := hbd C hC hCZ
    exact ⟨M, fun n y hy ↦ (norm_fderiv_le_norm_fderiv_toLp_prodMk_right differentiableAt_fun_id
      (hdiff (φ n) y (hCZ hy).1)).trans (hM n y hy)⟩
  · simpa [Function.comp_def, g] using
      (WithLp.sndL 2 ℝ ℂ V).uniformContinuous.comp_tendstoLocallyUniformlyOn hlim

end TauCeti.Floer
