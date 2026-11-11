/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Geometry.Symplectic.Floer.Energy
public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Convergence
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import TauCeti.Analysis.Calculus.FDeriv.WithLp
import TauCeti.Geometry.Symplectic.Floer.Graph
import TauCeti.MeasureTheory.Integral.EnergyConcentration
import TauCeti.MeasureTheory.Integral.WithLp
import TauCeti.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.Topology.Algebra.Module.BilinearForm

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
area of a small disc carries the rest of the graph energy.

The same statement holds with the Floer energy `∫_Ω ω(∂ₛu - X_{K_s}, ∂ₜu - X_{K_t})` in place of
`∫_Ω ‖∂ₛu‖²`, for the Floer equation `(du - X_K)^{0,1} = 0` of a `C³` perturbation
`K = K_s ds + K_t dt` and a `C²` family `J(z, x)` of `ω`-tame structures on the domain `ℝ × ℝ`
(`TauCeti.SymplecticForm.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset`). Read in
the complex coordinate `Complex.equivRealProdCLM`, these solutions solve the coordinate equation
above. On a compact window the taming constant of `J` and the size of `X_{K_s}` are uniform, so
the Floer energy density bounds `‖∂ₛu‖²` up to an additive constant
(`TauCeti.SymplecticForm.norm_fderiv_stdComplexLineReal_sq_le`). Hence bounded Floer energy gives
bounded energy `∫ ‖∂ₛu‖²`, and since small discs have small area, energy concentrating at a
bubbling point is also Floer energy.

The same holds uniformly over a compact parameter window
(`TauCeti.Floer.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset`): if `J_p`
and `X_p` depend jointly `C²` on a parameter `p` in a real inner product space and the parameters
`pₖ` of the solutions lie in a compact set `C`, a single threshold works for all parameters in `C`,
and the subsequence can be chosen so that its parameters also converge in `C`. This is the
compactness statement needed for the one-parameter families of Floer data `J_p`, `X_p`
(continuation, associativity, comparison) whose boundary counts give chain homotopies. It reduces
to the unparametrized statement by adjoining the parameter to the target as a constant coordinate,
which leaves the energy density unchanged.

The limit is only shown to be continuous; its regularity, the rescaled bubbles at the points of
`Z` (spheres for the structure `J(z, ·)` frozen at the bubbling point), and breaking along
cylindrical ends are not treated here.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. 82 (1985),
  307–347.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points, for sequences of almost complex structures converging in
  `C^∞`) and Section 8.1 (the graph construction for the inhomogeneous equation).
-/

public section

open Complex ContinuousLinearMap Filter MeasureTheory Metric Real Set Topology

namespace TauCeti.Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

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
    have hgE := setIntegral_norm_fderiv_toLp_prodMk_apply_sq (μ := volume) measurableSet_ball
      (fun _ _ ↦ differentiableAt_fun_id) (fun y hy ↦ hdiff y (hsub' hy)) 1
      (by simpa using integrableOn_const (μ := volume) (s := ball z₀ ρ) (C := (1 : ℝ)))
      (hint.mono_set hsub')
    simp only [fderiv_fun_id, ContinuousLinearMap.coe_id', id_eq, norm_one, one_pow,
      setIntegral_const, smul_eq_mul, mul_one, Complex.volume_real_ball z₀ hρ] at hgE
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
    rw [hgE, norm_fderiv_toLp_prodMk_apply_sq differentiableAt_fun_id
      (hdiff z₀ (mem_ball_self (hρ.trans_lt hρr))) 1] at h
    simp only [fderiv_fun_id, ContinuousLinearMap.coe_id', id_eq, norm_one, one_pow] at h
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
    ((integrableOn_const (C := (1 : ℝ)) hvol.ne).add (hint k)).congr_fun (fun y hy ↦ by
      simpa using (norm_fderiv_toLp_prodMk_apply_sq differentiableAt_fun_id (hdiff k y hy) 1).symm)
      hΩ.measurableSet
  -- On a subset of `Ω`, the energy of a graph is the area plus the energy of the map.
  have hsplit : ∀ k, ∀ S ⊆ Ω, MeasurableSet S →
      ∫ y in S, ‖fderiv ℝ (g k) y 1‖ ^ 2 = volume.real S + ∫ y in S, ‖fderiv ℝ (u k) y 1‖ ^ 2 := by
    intro k S hSΩ hS
    rw [setIntegral_norm_fderiv_toLp_prodMk_apply_sq hS (fun _ _ ↦ differentiableAt_fun_id)
      (fun y hy ↦ hdiff k y (hSΩ hy)) 1
      (by simpa using integrableOn_const (C := (1 : ℝ)) ((measure_mono hSΩ).trans_lt hvol).ne)
      ((hint k).mono_set hSΩ)]
    simp
  have hgE : ∀ k, ∫ y in Ω, ‖fderiv ℝ (g k) y 1‖ ^ 2 ≤ volume.real Ω + E := fun k ↦
    (hsplit k Ω subset_rfl hΩ.measurableSet).trans_le (by linarith [hE k])
  obtain ⟨φ, Z, w, hφ, hZΩ, -, hconc, hbd, hwcont, hwK, hlim⟩ := hconv hΩ
    (u := g) (fun k ↦ WithLp.contDiff_toLp.comp_contDiffOn (contDiffOn_id.prodMk (hu k)))
    (fun k y hy ↦ (fderiv_toLp_prodMk_I_eq_graphStructure_iff (hdiff k y hy)).2 (hCR k y hy))
    (fun k y hy ↦ ⟨hΩD hy, huK k hy⟩) hgint hgE
  -- Energy at least `δ` of the graphs concentrates at `Z`, so energy at least `δ / 2` of the
  -- maps does.
  have hconc' : ∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
      δ / 2 ≤ ∫ y in ball z ε ∩ Ω, ‖fderiv ℝ (u (φ n)) y 1‖ ^ 2 := fun z hz ε hε ↦
    eventually_le_setIntegral_ball_of_le_measureReal_add_setIntegral_ball hΩ.measurableSet
      (measure_singleton z) ⟨1, one_pos, measure_ball_lt_top.ne⟩ (fun _ _ _ ↦ sq_nonneg _)
      (fun n ↦ hint (φ n)) (half_lt_self hδ) hε fun ρ hρ ↦ (hconc z hz ρ hρ).mono fun n hn ↦ by
        rwa [hsplit (φ n) _ inter_subset_right (measurableSet_ball.inter hΩ.measurableSet)] at hn
  refine ⟨φ, Z, fun z ↦ (w z).snd, hφ, hZΩ,
    card_mul_le_of_forall_eventually_le_setIntegral_ball (l := atTop) hΩ.measurableSet
      (fun _ _ _ ↦ sq_nonneg _) (fun n ↦ hint (φ n)) (fun n ↦ hE (φ n)) hconc', hconc', ?_,
    (WithLp.sndL 2 ℝ ℂ V).continuous.comp_continuousOn hwcont, fun z hz ↦ (hwK hz).2, ?_⟩
  · intro C hC hCZ
    obtain ⟨M, hM⟩ := hbd C hC hCZ
    exact ⟨M, fun n y hy ↦
      (norm_fderiv_le_norm_fderiv_toLp_prodMk_right differentiableAt_fun_id).trans (hM n y hy)⟩
  · simpa [Function.comp_def, g] using
      (WithLp.sndL 2 ℝ ℂ V).uniformContinuous.comp_tendstoLocallyUniformlyOn hlim

section Parameter

/-! ### Compact parameter windows

Let the data `J_p` and `X_p` depend on a parameter `p` of a real inner product space `P`. Adjoin the
parameter to the target as a constant coordinate: a solution `u` for the parameter `p` is the
second component of the map `z ↦ ((p, 0), u z)` into `(P × P) × V`, and this map solves the Floer
equation for the structure `(a, b) ↦ (-b, a)` on the parameter block, the structure `J_p` on `V`,
and the one-form `X_p` with values in `V`. The parameter block has zero derivative, so the energy
density is unchanged. The parameter block is doubled only so that it carries a linear complex
structure. -/

open Function

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

/-- The standard complex structure `(a, b) ↦ (-b, a)` on `P × P`
(`TauCeti.AlmostComplexStructure.product`), as a continuous linear map of the Euclidean product. -/
private noncomputable def parameterStructure : WithLp 2 (P × P) →L[ℝ] WithLp 2 (P × P) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ P P).symm.toContinuousLinearMap ∘L
    ⟨(AlmostComplexStructure.product P).toLinearMap, continuous_snd.neg.prodMk continuous_fst⟩ ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℝ P P).toContinuousLinearMap

private theorem parameterStructure_apply (ζ : WithLp 2 (P × P)) :
    parameterStructure ζ = WithLp.toLp 2 (AlmostComplexStructure.product P ζ.ofLp) :=
  (rfl)

private theorem parameterStructure_parameterStructure (ζ : WithLp 2 (P × P)) :
    parameterStructure (parameterStructure ζ) = -ζ := by
  rw [parameterStructure_apply, parameterStructure_apply, WithLp.ofLp_toLp,
    AlmostComplexStructure.apply_apply, WithLp.toLp_neg, WithLp.toLp_ofLp]

/-- The point of `P × (ℂ × V)` read off from a point of `ℂ × ((P × P) × V)`: the first parameter
coordinate, the domain point and the target point. -/
private noncomputable def parameterPoint :
    ℂ × WithLp 2 (WithLp 2 (P × P) × V) →L[ℝ] P × (ℂ × V) :=
  (WithLp.fstL 2 ℝ P P ∘L WithLp.fstL 2 ℝ (WithLp 2 (P × P)) V ∘L snd ℝ ℂ _).prod
    ((fst ℝ ℂ _).prod (WithLp.sndL 2 ℝ (WithLp 2 (P × P)) V ∘L snd ℝ ℂ _))

@[simp]
private theorem parameterPoint_apply (z : ℂ) (p q : P) (x : V) :
    parameterPoint (z, WithLp.toLp 2 (WithLp.toLp 2 (p, q), x)) = (p, (z, x)) := by
  simp [parameterPoint]

/-- The almost complex structure on `(P × P) × V` adjoining the parameter. -/
private noncomputable def parameterJ (J : P → ℂ × V → V →L[ℝ] V)
    (q : ℂ × WithLp 2 (WithLp 2 (P × P) × V)) :
    WithLp 2 (WithLp 2 (P × P) × V) →L[ℝ] WithLp 2 (WithLp 2 (P × P) × V) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (WithLp 2 (P × P)) V).symm.toContinuousLinearMap ∘L
    (inl ℝ (WithLp 2 (P × P)) V ∘L parameterStructure ∘L fst ℝ _ V +
      inr ℝ (WithLp 2 (P × P)) V ∘L uncurry J (parameterPoint q) ∘L snd ℝ _ V) ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℝ (WithLp 2 (P × P)) V).toContinuousLinearMap

@[simp]
private theorem parameterJ_apply (J : P → ℂ × V → V →L[ℝ] V)
    (q : ℂ × WithLp 2 (WithLp 2 (P × P) × V)) (ζ : WithLp 2 (WithLp 2 (P × P) × V)) :
    parameterJ J q ζ = WithLp.toLp 2 (parameterStructure ζ.fst,
      uncurry J (parameterPoint q) ζ.snd) := by
  simp [parameterJ, WithLp.ext_iff]

/-- The Hamiltonian one-form on `(P × P) × V` adjoining the parameter. -/
private noncomputable def parameterX (X : P → ℂ × V → ℂ →L[ℝ] V)
    (q : ℂ × WithLp 2 (WithLp 2 (P × P) × V)) : ℂ →L[ℝ] WithLp 2 (WithLp 2 (P × P) × V) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (WithLp 2 (P × P)) V).symm.toContinuousLinearMap ∘L
    inr ℝ (WithLp 2 (P × P)) V ∘L uncurry X (parameterPoint q)

@[simp]
private theorem parameterX_apply (X : P → ℂ × V → ℂ →L[ℝ] V)
    (q : ℂ × WithLp 2 (WithLp 2 (P × P) × V)) (ξ : ℂ) :
    parameterX X q ξ = WithLp.toLp 2 (0, uncurry X (parameterPoint q) ξ) := by
  simp [parameterX]

private theorem contDiffOn_parameterJ {J : P → ℂ × V → V →L[ℝ] V} {W : Set (P × (ℂ × V))}
    (hJ : ContDiffOn ℝ 2 (uncurry J) W) : ContDiffOn ℝ 2 (parameterJ J) (parameterPoint ⁻¹' W) := by
  have hJ' : ContDiffOn ℝ 2 (fun q ↦ uncurry J (parameterPoint q)) (parameterPoint ⁻¹' W) :=
    hJ.comp (parameterPoint (P := P) (V := V)).contDiff.contDiffOn (mapsTo_preimage _ _)
  unfold parameterJ
  exact contDiffOn_const.clm_comp ((contDiffOn_const.add (contDiffOn_const.clm_comp
    (hJ'.clm_comp contDiffOn_const))).clm_comp contDiffOn_const)

private theorem contDiffOn_parameterX {X : P → ℂ × V → ℂ →L[ℝ] V} {W : Set (P × (ℂ × V))}
    (hX : ContDiffOn ℝ 2 (uncurry X) W) : ContDiffOn ℝ 2 (parameterX X) (parameterPoint ⁻¹' W) := by
  have hX' : ContDiffOn ℝ 2 (fun q ↦ uncurry X (parameterPoint q)) (parameterPoint ⁻¹' W) :=
    hX.comp (parameterPoint (P := P) (V := V)).contDiff.contDiffOn (mapsTo_preimage _ _)
  unfold parameterX
  exact contDiffOn_const.clm_comp (contDiffOn_const.clm_comp hX')

/-- **Floer solutions over a compact parameter window converge off finitely many bubbling
points.** Let `J_p` and `X_p` depend on a parameter `p` in a real inner product space `P`, jointly
`C²` on an open set `W ⊆ P × (ℂ × V)` containing `C × D × K` for compact `C ⊆ P`, `D ⊆ ℂ` and
`K ⊆ V`, with `J_p(z, x)² = -1` on `C × D × K`. There is a threshold `δ > 0` with the following
property. Let `uₖ` be `C³` solutions of
`∂ₜu - X_{pₖ}(z, u) i = J_{pₖ}(z, u)(∂ₛu - X_{pₖ}(z, u) 1)` on an open set `Ω ⊆ D`, for parameters
`pₖ ∈ C`, with image in `K` and energy `∫_Ω ‖∂ₛuₖ‖² ≤ E`. Then there are a subsequence `φ`, a
limit parameter `p₀ ∈ C` of `p_{φ n}`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ E`, and a continuous
`v : Ω \ Z → K` such that along `φ` every disc about a point of `Z` eventually carries energy at
least `δ`, the differentials are uniformly bounded on every compact subset of `Ω \ Z`, and
`u_{φ n} → v` locally uniformly on `Ω \ Z`. -/
theorem exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset
    {J : P → ℂ × V → V →L[ℝ] V} {X : P → ℂ × V → ℂ →L[ℝ] V} {W : Set (P × (ℂ × V))}
    {C : Set P} {D : Set ℂ} {K : Set V}
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 (uncurry J) W) (hX : ContDiffOn ℝ 2 (uncurry X) W)
    (hC : IsCompact C) (hD : IsCompact D) (hK : IsCompact K) (hCDKW : C ×ˢ (D ×ˢ K) ⊆ W)
    (hJsq : ∀ p ∈ C, ∀ z ∈ D, ∀ x ∈ K, ∀ v, J p (z, x) (J p (z, x) v) = -v) :
    ∃ δ > 0, ∀ ⦃Ω : Set ℂ⦄ ⦃p : ℕ → P⦄ ⦃u : ℕ → ℂ → V⦄ ⦃E : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, p k ∈ C) → (∀ k, ContDiffOn ℝ 3 (u k) Ω) →
      (∀ k, ∀ y ∈ Ω, fderiv ℝ (u k) y I - X (p k) (y, u k y) I =
        J (p k) (y, u k y) (fderiv ℝ (u k) y 1 - X (p k) (y, u k y) 1)) →
      (∀ k, MapsTo (u k) Ω K) →
      (∀ k, IntegrableOn (fun y ↦ ‖fderiv ℝ (u k) y 1‖ ^ 2) Ω) →
      (∀ k, ∫ y in Ω, ‖fderiv ℝ (u k) y 1‖ ^ 2 ≤ E) →
      ∃ (φ : ℕ → ℕ) (p₀ : P) (Z : Finset ℂ) (v : ℂ → V), StrictMono φ ∧
        p₀ ∈ C ∧ Tendsto (fun n ↦ p (φ n)) atTop (𝓝 p₀) ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z ε ∩ Ω, ‖fderiv ℝ (u (φ n)) y 1‖ ^ 2) ∧
        (∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C', ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) := by
  -- Apply the compactness theorem to the solutions `z ↦ ((p, 0), u z)` with values in the compact
  -- image `K'` of `C × K`.
  set ι : P × V → WithLp 2 (WithLp 2 (P × P) × V) :=
    fun a ↦ WithLp.toLp 2 (WithLp.toLp 2 (a.1, 0), a.2) with hι
  have hιc : Continuous ι := by fun_prop
  obtain ⟨δ, hδ, hconv⟩ := exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset
    (hW.preimage (parameterPoint (P := P) (V := V)).continuous) (contDiffOn_parameterJ hJ)
    (contDiffOn_parameterX hX)
    hD ((hC.prod hK).image hιc) (by
      rintro ⟨z, _⟩ ⟨hz, ⟨a, x⟩, ⟨ha, hx⟩, rfl⟩
      exact hCDKW (by simpa [hι] using ⟨ha, hz, hx⟩))
    (by
      rintro z hz _ ⟨⟨a, x⟩, ⟨ha, hx⟩, rfl⟩ ζ
      simp [hι, WithLp.ext_iff, Prod.ext_iff, parameterStructure_parameterStructure,
        hJsq a ha z hz x hx])
  refine ⟨δ, hδ, fun Ω p u E hΩ hΩD hpC hu hCR huK hint hE ↦ ?_⟩
  obtain ⟨p₀, hp₀, ψ, hψ, hlim⟩ := hC.tendsto_subseq hpC
  set g : ℕ → ℂ → WithLp 2 (WithLp 2 (P × P) × V) :=
    fun k w ↦ WithLp.toLp 2 (WithLp.toLp 2 (p (ψ k), 0), u (ψ k) w) with hg
  have hdiff : ∀ k, ∀ y ∈ Ω, DifferentiableAt ℝ (u k) y := fun k y hy ↦
    ((hu k).differentiableOn (by norm_num)).differentiableAt (hΩ.mem_nhds hy)
  -- The constant parameter coordinate does not change the energy density.
  have hnorm : ∀ k, ∀ y ∈ Ω,
      ‖fderiv ℝ (g k) y 1‖ ^ 2 = ‖fderiv ℝ (u (ψ k)) y 1‖ ^ 2 := fun k y hy ↦ by
    rw [norm_fderiv_toLp_prodMk_apply_sq (differentiableAt_const _) (hdiff _ y hy)]
    simp
  have hint' : ∀ k, ∀ S ⊆ Ω, MeasurableSet S →
      ∫ y in S, ‖fderiv ℝ (g k) y 1‖ ^ 2 = ∫ y in S, ‖fderiv ℝ (u (ψ k)) y 1‖ ^ 2 :=
    fun k S hSΩ hS ↦ setIntegral_congr_fun hS fun y hy ↦ hnorm k y (hSΩ hy)
  obtain ⟨φ, Z, w, hφ, hZΩ, hcard, hconc, hbd, hwcont, hwK, hwlim⟩ := hconv hΩ hΩD
    (u := g) (fun k ↦ WithLp.contDiff_toLp.comp_contDiffOn (contDiffOn_const.prodMk (hu (ψ k))))
    (fun k y hy ↦ by
      simp [hg, fderiv_toLp_prodMk_apply (differentiableAt_const _) (hdiff _ y hy),
        WithLp.ext_iff, hCR (ψ k) y hy])
    (fun k y hy ↦ ⟨(p (ψ k), u (ψ k) y), ⟨hpC _, huK _ hy⟩, rfl⟩)
    (fun k ↦ (hint (ψ k)).congr_fun (fun y hy ↦ (hnorm k y hy).symm) hΩ.measurableSet)
    (fun k ↦ (hint' k Ω subset_rfl hΩ.measurableSet).trans_le (hE (ψ k)))
  refine ⟨ψ ∘ φ, p₀, Z, fun z ↦ (w z).snd, hψ.comp hφ, hp₀, hlim.comp hφ.tendsto_atTop, hZΩ,
    hcard, fun z hz ε hε ↦ (hconc z hz ε hε).mono fun n hn ↦ ?_, fun C' hC' hC'Z ↦ ?_,
    (WithLp.sndL 2 ℝ _ V).continuous.comp_continuousOn hwcont, fun z hz ↦ ?_, ?_⟩
  · rwa [hint' _ _ inter_subset_right (measurableSet_ball.inter hΩ.measurableSet)] at hn
  · obtain ⟨M, hM⟩ := hbd C' hC' hC'Z
    exact ⟨M, fun n y hy ↦ (norm_fderiv_le_norm_fderiv_toLp_prodMk_right
      (differentiableAt_const _)).trans (hM n y hy)⟩
  · obtain ⟨⟨a, x⟩, ⟨-, hx⟩, hax⟩ := hwK hz
    simpa [← hax, hι] using hx
  · simpa [Function.comp_def, g] using
      (WithLp.sndL 2 ℝ _ V).uniformContinuous.comp_tendstoLocallyUniformlyOn hwlim

end Parameter

end TauCeti.Floer

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Ks Kt : ℝ × ℝ → V → ℝ} {J : ℝ × ℝ → V → AlmostComplexStructure V}

/-- In the complex coordinate `equivRealProdCLM`, the Floer equation `(du - X_K)^{0,1} = 0` at
`equivRealProdCLM y` is the coordinate equation `∂ₜu' - X(y, u') i = J(y, u')(∂ₛu' - X(y, u') 1)`
for `u' = u ∘ equivRealProdCLM`, with `X(y, x) = X_K(equivRealProdCLM y, x) ∘ equivRealProdCLM`. -/
theorem fderiv_comp_equivRealProdCLM_I_sub (ω : SymplecticForm V) {u : ℝ × ℝ → V}
    {y : ℂ} (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (equivRealProdCLM y) (u (equivRealProdCLM y)))
      (ω.perturbedFDeriv Ks Kt u (equivRealProdCLM y) : ℝ × ℝ →ₗ[ℝ] V)) :
    fderiv ℝ (u ∘ equivRealProdCLM) y I -
        (ω.hamiltonianOneForm Ks Kt (equivRealProdCLM y) (u (equivRealProdCLM y)) ∘L
          (equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ)) I =
      J (equivRealProdCLM y) (u (equivRealProdCLM y))
        (fderiv ℝ (u ∘ equivRealProdCLM) y 1 -
          (ω.hamiltonianOneForm Ks Kt (equivRealProdCLM y) (u (equivRealProdCLM y)) ∘L
            (equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ)) 1) := by
  have h' := h.apply_stdComplexLineImag
  simp only [perturbedFDeriv_eq_sub, sub_apply,
    ContinuousLinearMap.coe_coe] at h'
  simpa only [fderiv_comp_equivRealProdCLM_one, fderiv_comp_equivRealProdCLM_I,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, equivRealProdCLM_one,
    equivRealProdCLM_I] using h'

/-- **The energy density bounds the derivative uniformly on a compact window.** Let `J(z, x)` be
continuous and tamed by `ω`, and `X_{K_s}(z, x)` continuous, on `D × K` for compact `D ⊆ ℝ × ℝ`
and `K ⊆ V`. There are constants `A, B ≥ 0` such that every solution `u` of the Floer equation
for `J(z, u)` at a point `z ∈ D` with `u(z) ∈ K` satisfies
`‖∂ₛu(z)‖² ≤ A ω(∂ₛu - X_{K_s}, ∂ₜu - X_{K_t}) + B`. -/
theorem exists_forall_norm_fderiv_stdComplexLineReal_sq_le (ω : SymplecticForm V)
    {D : Set (ℝ × ℝ)} {K : Set V} (hD : IsCompact D) (hK : IsCompact K)
    (hJ : ContinuousOn
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (D ×ˢ K))
    (hX : ContinuousOn (fun p : (ℝ × ℝ) × V ↦ ω.hamiltonianVectorField (Ks p.1) p.2) (D ×ˢ K))
    (hJt : ∀ z ∈ D, ∀ x ∈ K, ω.Tames (J z x)) :
    ∃ A ≥ 0, ∃ B ≥ 0, ∀ ⦃u : ℝ × ℝ → V⦄ ⦃z : ℝ × ℝ⦄, z ∈ D → u z ∈ K →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V) →
      ‖fderiv ℝ u z stdComplexLineReal‖ ^ 2 ≤ A * ω.floerEnergyDensity Ks Kt u z + B := by
  set Jc : (ℝ × ℝ) × V → V →L[ℝ] V := fun p ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap
  have hDK : IsCompact (D ×ˢ K) := hD.prod hK
  -- A uniform taming constant for `J`, and a bound for `X_{K_s}`, on `D × K`.
  obtain ⟨c, hc, hJc⟩ := hDK.exists_pos_forall_mul_norm_sq_le
    (b := fun p ↦ ((ContinuousLinearMap.compL ℝ V V ℝ).flip (Jc p)).comp
      ω.toBilinForm.toContinuousBilinearMap)
    (((ContinuousLinearMap.compL ℝ V V ℝ).flip.continuous.comp_continuousOn hJ).clm_comp
      continuousOn_const)
    (fun p hp v hv ↦ by simpa [Jc] using hJt p.1 hp.1 p.2 hp.2 v hv)
  obtain ⟨B, hB⟩ := hDK.exists_bound_of_continuousOn hX
  refine ⟨2 / c, by positivity, 2 * B ^ 2, by positivity, fun u z hz hu h ↦ ?_⟩
  have hp : (z, u z) ∈ D ×ˢ K := ⟨hz, hu⟩
  refine (ω.norm_fderiv_stdComplexLineReal_sq_le hc (fun v ↦ by simpa [Jc] using hJc _ hp v)
    h).trans ?_
  have hXB : ‖ω.hamiltonianVectorField (Ks z) (u z)‖ ≤ B := by simpa using hB _ hp
  gcongr

/-- If `‖∂ₛu‖² ≤ A e + B` on an open set `Ω` of finite measure, where `e` is the Floer energy
density, integrable on `Ω`, and `u` is `C¹` on `Ω`, then `‖∂ₛu‖²` is integrable on `Ω`. -/
private theorem integrableOn_norm_fderiv_stdComplexLineReal_sq (ω : SymplecticForm V)
    {u : ℝ × ℝ → V} {Ω : Set (ℝ × ℝ)} {A B : ℝ} (hΩ : IsOpen Ω) (hΩfin : volume Ω ≠ ⊤)
    (hu : ContDiffOn ℝ 1 u Ω) (hint : IntegrableOn (ω.floerEnergyDensity Ks Kt u) Ω)
    (hle : ∀ z ∈ Ω,
      ‖fderiv ℝ u z stdComplexLineReal‖ ^ 2 ≤ A * ω.floerEnergyDensity Ks Kt u z + B) :
    IntegrableOn (fun z ↦ ‖fderiv ℝ u z stdComplexLineReal‖ ^ 2) Ω :=
  Integrable.mono' ((hint.const_mul A).fun_add (integrableOn_const (C := B) hΩfin))
    ((((hu.continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply
      continuousOn_const).norm.pow 2).aestronglyMeasurable hΩ.measurableSet)
    (ae_restrict_of_forall_mem hΩ.measurableSet fun z hz ↦ by
      rw [Real.norm_of_nonneg (by positivity)]
      exact hle z hz)

/-- If `‖∂ₛu‖² ≤ A e + B` on a measurable set `S` of finite measure, with `A, B ≥ 0` and `e ≥ 0`
the Floer energy density, then `∫_S ‖∂ₛu‖² ≤ (A + B + 1)(|S| + ∫_S e)`. -/
private theorem setIntegral_norm_fderiv_stdComplexLineReal_sq_le (ω : SymplecticForm V)
    {u : ℝ × ℝ → V} {S : Set (ℝ × ℝ)} {A B : ℝ} (hS : MeasurableSet S) (hSfin : volume S ≠ ⊤)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hgint : IntegrableOn (fun z ↦ ‖fderiv ℝ u z stdComplexLineReal‖ ^ 2) S)
    (hint : IntegrableOn (ω.floerEnergyDensity Ks Kt u) S)
    (he0 : ∀ z ∈ S, 0 ≤ ω.floerEnergyDensity Ks Kt u z)
    (hle : ∀ z ∈ S,
      ‖fderiv ℝ u z stdComplexLineReal‖ ^ 2 ≤ A * ω.floerEnergyDensity Ks Kt u z + B) :
    ∫ z in S, ‖fderiv ℝ u z stdComplexLineReal‖ ^ 2 ≤
      (A + B + 1) * (volume.real S + ∫ z in S, ω.floerEnergyDensity Ks Kt u z) := by
  have hint0 : 0 ≤ ∫ z in S, ω.floerEnergyDensity Ks Kt u z := setIntegral_nonneg hS he0
  have hm0 : 0 ≤ volume.real S := measureReal_nonneg
  calc ∫ z in S, ‖fderiv ℝ u z stdComplexLineReal‖ ^ 2
      ≤ ∫ z in S, (A * ω.floerEnergyDensity Ks Kt u z + B) :=
        setIntegral_mono_on hgint ((hint.const_mul A).fun_add (integrableOn_const (C := B) hSfin))
          hS hle
    _ = A * (∫ z in S, ω.floerEnergyDensity Ks Kt u z) + B * volume.real S := by
        rw [integral_add (hint.const_mul A) (integrableOn_const hSfin), integral_const_mul,
          setIntegral_const, smul_eq_mul, mul_comm (volume.real S)]
    _ ≤ (A + B + 1) * (volume.real S + ∫ z in S, ω.floerEnergyDensity Ks Kt u z) := by
        nlinarith [mul_nonneg hA0 hm0, mul_nonneg hB0 hint0]

/-- `TauCeti.Floer.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset` for solutions
of the Floer equation `(du - X_K)^{0,1} = 0` on the domain `ℝ × ℝ`, read through the complex
coordinate `equivRealProdCLM`; the energy is `∫ ‖∂ₛu‖²`. -/
private theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_of_norm
    (ω : SymplecticForm V) {W : Set ((ℝ × ℝ) × V)} {D : Set (ℝ × ℝ)} {K : Set V}
    (hW : IsOpen W) (hX : ContDiffOn ℝ 2
      (fun p : (ℝ × ℝ) × V ↦ ω.hamiltonianOneForm Ks Kt p.1 p.2) W)
    (hJ : ContDiffOn ℝ 2
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hD : IsCompact D) (hK : IsCompact K) (hDKW : D ×ˢ K ⊆ W) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃E : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, ContDiffOn ℝ 3 (u k) Ω) →
      (∀ k, ∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
        (ω.perturbedFDeriv Ks Kt (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, MapsTo (u k) Ω K) →
      (∀ k, IntegrableOn (fun z ↦ ‖fderiv ℝ (u k) z stdComplexLineReal‖ ^ 2) Ω) →
      (∀ k, ∫ z in Ω, ‖fderiv ℝ (u k) z stdComplexLineReal‖ ^ 2 ≤ E) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧ ↑Z ⊆ Ω ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z ε ∩ Ω, ‖fderiv ℝ (u (φ n)) y stdComplexLineReal‖ ^ 2) ∧
        (∀ C, IsCompact C → C ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C, ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) := by
  classical
  set e : ℂ ≃L[ℝ] ℝ × ℝ := equivRealProdCLM with he
  set g : ℂ × V → (ℝ × ℝ) × V := fun q ↦ (e q.1, q.2)
  have hg {n : WithTop ℕ∞} : ContDiff ℝ n g := (e.contDiff.comp contDiff_fst).prodMk contDiff_snd
  obtain ⟨δ, hδ, hconv⟩ := Floer.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset
    (hW.preimage (hg (n := 0)).continuous) (hJ.comp hg.contDiffOn (mapsTo_preimage g W))
    ((hX.comp hg.contDiffOn (mapsTo_preimage g W)).clm_comp
      (contDiffOn_const (c := (e : ℂ →L[ℝ] ℝ × ℝ))))
    (e.toHomeomorph.isCompact_preimage.2 hD) hK (fun q hq ↦ hDKW ⟨hq.1, hq.2⟩)
    (fun y _ x _ v ↦ by simp)
  -- `e` preserves volume, and in the coordinate `e` the density `‖∂ₛu‖²` is `‖∂ₛ(u ∘ e)‖²`.
  have hint_iff (w : ℝ × ℝ → V) (S : Set (ℝ × ℝ)) :
      IntegrableOn (fun y ↦ ‖fderiv ℝ (w ∘ e) y 1‖ ^ 2) (e ⁻¹' S) ↔
        IntegrableOn (fun z ↦ ‖fderiv ℝ w z stdComplexLineReal‖ ^ 2) S := by
    simp only [he, fderiv_comp_equivRealProdCLM_one]
    exact Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
      equivRealProdCLM.toHomeomorph.measurableEmbedding
      (f := fun z ↦ ‖fderiv ℝ w z stdComplexLineReal‖ ^ 2) (s := S)
  have hint_eq (w : ℝ × ℝ → V) (S : Set (ℝ × ℝ)) :
      ∫ y in e ⁻¹' S, ‖fderiv ℝ (w ∘ e) y 1‖ ^ 2 =
        ∫ z in S, ‖fderiv ℝ w z stdComplexLineReal‖ ^ 2 := by
    simp only [he, fderiv_comp_equivRealProdCLM_one]
    exact Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
      equivRealProdCLM.toHomeomorph.measurableEmbedding
      (fun z ↦ ‖fderiv ℝ w z stdComplexLineReal‖ ^ 2) S
  refine ⟨δ, hδ, fun Ω u E hΩ hΩD hu hfl huK hint hE ↦ ?_⟩
  obtain ⟨φ, Z', v', hφ, hZ'Ω, -, hconc', hbd', hvc', hvK', hlim'⟩ :=
    hconv (Ω := e ⁻¹' Ω) (u := fun k ↦ u k ∘ e) (E := E)
      (hΩ.preimage e.continuous) (preimage_mono hΩD)
      (fun k ↦ (hu k).comp e.contDiff.contDiffOn (mapsTo_preimage _ _))
      (fun k y hy ↦ by simpa [he, g] using ω.fderiv_comp_equivRealProdCLM_I_sub (hfl k (e y) hy))
      (fun k y hy ↦ huK k hy)
      (fun k ↦ (hint_iff (u k) Ω).2 (hint k)) (fun k ↦ (hint_eq (u k) Ω).trans_le (hE k))
  -- The bubbling set and the limit in the original coordinates.
  set Z : Finset (ℝ × ℝ) := Z'.image e with hZ_def
  have hpreZ : e ⁻¹' (Ω \ ↑Z) = e ⁻¹' Ω \ ↑Z' := by
    rw [preimage_sdiff, hZ_def, Finset.coe_image, e.injective.preimage_image]
  have hsymm : MapsTo e.symm (Ω \ ↑Z) (e ⁻¹' Ω \ ↑Z') := fun y hy ↦ by
    rw [← hpreZ]
    simpa using hy
  have hu_symm (k : ℕ) : (u k ∘ e) ∘ e.symm = u k := funext fun z ↦ by simp
  refine ⟨φ, Z, v' ∘ e.symm, hφ, ?_, fun z hz ε hε ↦ ?_, fun C hC hCZ ↦ ?_,
    hvc'.comp e.symm.continuous.continuousOn hsymm, fun y hy ↦ hvK' (hsymm hy), ?_⟩
  · rw [hZ_def, Finset.coe_image]
    exact image_subset_iff.2 hZ'Ω
  · -- A disc of `ℂ` lies in the disc of `ℝ × ℝ` of the same radius about the image point.
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.1 hz
    have hsub : ball z' ε ∩ e ⁻¹' Ω ⊆ e ⁻¹' (ball (e z') ε ∩ Ω) := fun y hy ↦
      ⟨(lipschitz_equivRealProd.dist_le_mul y z').trans_lt (by simpa using hy.1), hy.2⟩
    filter_upwards [hconc' z' hz' ε hε] with n hn
    rw [← hint_eq]
    exact hn.trans (setIntegral_mono_set
      ((hint_iff _ _).2 ((hint (φ n)).mono_set inter_subset_right))
      (Eventually.of_forall fun _ ↦ by positivity) hsub.eventuallyLE)
  · obtain ⟨M', hM'⟩ := hbd' (e ⁻¹' C) (e.toHomeomorph.isCompact_preimage.2 hC)
      (hpreZ ▸ preimage_mono hCZ)
    refine ⟨M' * ‖(e.symm : ℝ × ℝ →L[ℝ] ℂ)‖, fun n y hy ↦ ?_⟩
    have hd := e.symm.comp_right_fderiv (f := u (φ n) ∘ e) (x := y)
    rw [hu_symm] at hd
    rw [hd]
    exact (opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hM' n _ (by simpa using hy)) (norm_nonneg _))
  · simpa only [hu_symm] using hlim'.comp e.symm hsymm e.symm.continuous.continuousOn

/-- **Floer solutions of bounded energy converge off finitely many bubbling points.** Let
`K = K_s ds + K_t dt` be `C³` and `J(z, x)` be `C²` on an open set `W ⊆ (ℝ × ℝ) × V` containing
`D × K` for compact `D ⊆ ℝ × ℝ` and `K ⊆ V`, with `J(z, x)` tamed by `ω` on `D × K`. There is a
threshold `δ > 0` with the following property. Let `uₖ` be `C³` solutions of the Floer equation
`(du - X_K)^{0,1} = 0` for `J(z, u)` on an open set `Ω ⊆ D`, with image in `K` and Floer energy
`∫_Ω ω(∂ₛuₖ - X_{K_s}, ∂ₜuₖ - X_{K_t}) ≤ E`. Then there are a subsequence `φ`, a finite set
`Z ⊆ Ω` with `#Z * δ ≤ E`, and a continuous `v : Ω \ Z → K` such that along `φ` every disc about
a point of `Z` eventually carries Floer energy at least `δ`, the differentials are uniformly
bounded on every compact subset of `Ω \ Z`, and `u_{φ n} → v` locally uniformly on `Ω \ Z`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset (ω : SymplecticForm V)
    {W : Set ((ℝ × ℝ) × V)} {D : Set (ℝ × ℝ)} {K : Set V}
    (hW : IsOpen W) (hKs : ContDiffOn ℝ 3 (Function.uncurry Ks) W)
    (hKt : ContDiffOn ℝ 3 (Function.uncurry Kt) W)
    (hJ : ContDiffOn ℝ 2
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hD : IsCompact D) (hK : IsCompact K) (hDKW : D ×ˢ K ⊆ W)
    (hJt : ∀ z ∈ D, ∀ x ∈ K, ω.Tames (J z x)) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃E : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, ContDiffOn ℝ 3 (u k) Ω) →
      (∀ k, ∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
        (ω.perturbedFDeriv Ks Kt (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, MapsTo (u k) Ω K) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity Ks Kt (u k)) Ω) →
      (∀ k, ∫ z in Ω, ω.floerEnergyDensity Ks Kt (u k) z ≤ E) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity Ks Kt (u (φ n)) y) ∧
        (∀ C, IsCompact C → C ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C, ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) := by
  have hX := ω.contDiffOn_hamiltonianOneForm (n := 2) hW hKs hKt
  obtain ⟨A, hA0, B, hB0, hpt⟩ :=
    ω.exists_forall_norm_fderiv_stdComplexLineReal_sq_le (Ks := Ks) (Kt := Kt) hD hK
    (hJ.continuousOn.mono hDKW)
    ((hX.continuousOn.mono hDKW).clm_apply (continuousOn_const (c := stdComplexLineReal)) |>.congr
      fun p _ ↦ by simp)
    hJt
  obtain ⟨δ₀, hδ₀, hconv⟩ :=
    ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_of_norm hW hX hJ hD hK hDKW
  have hC₀0 : 0 < A + B + 1 := by positivity
  refine ⟨δ₀ / (2 * (A + B + 1)), by positivity, fun Ω u E hΩ hΩD hu hfl huK hint hE ↦ ?_⟩
  have hΩm : MeasurableSet Ω := hΩ.measurableSet
  have hΩfin : volume Ω ≠ ⊤ := ((measure_mono hΩD).trans_lt hD.measure_lt_top).ne
  -- On `Ω`, the energy density `f k` is nonnegative and bounds `‖∂ₛuₖ‖²` up to a constant.
  set f : ℕ → ℝ × ℝ → ℝ := fun k ↦ ω.floerEnergyDensity Ks Kt (u k) with hf_def
  have hf0 (k : ℕ) : ∀ z ∈ Ω, 0 ≤ f k z := fun z hz ↦
    ω.floerEnergyDensity_nonneg (hJt z (hΩD hz) _ (huK k hz)) (hfl k z hz)
  have hgle (k : ℕ) : ∀ z ∈ Ω, ‖fderiv ℝ (u k) z stdComplexLineReal‖ ^ 2 ≤ A * f k z + B :=
    fun z hz ↦ hpt (hΩD hz) (huK k hz) (hfl k z hz)
  have hgint (k : ℕ) := ω.integrableOn_norm_fderiv_stdComplexLineReal_sq hΩ hΩfin
    ((hu k).of_le (by norm_num)) (hint k) (hgle k)
  have hgS (k : ℕ) {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) (hSΩ : S ⊆ Ω) :=
    ω.setIntegral_norm_fderiv_stdComplexLineReal_sq_le hS
      (ne_top_of_le_ne_top hΩfin (measure_mono hSΩ)) hA0 hB0 ((hgint k).mono_set hSΩ)
      ((hint k).mono_set hSΩ) (fun z hz ↦ hf0 k z (hSΩ hz)) fun z hz ↦ hgle k z (hSΩ hz)
  obtain ⟨φ, Z, v, hφ, hZΩ, hconc', hbd, hvc, hvK, hlim⟩ :=
    hconv hΩ hΩD hu hfl huK hgint fun k ↦ (hgS k hΩm le_rfl).trans (mul_le_mul_of_nonneg_left
      (add_le_add (measureReal_mono hΩD hD.measure_lt_top.ne) (hE k)) hC₀0.le)
  -- Energy `δ₀` of `∂ₛu` concentrating at a point gives Floer energy `δ₀ / (2 (A + B + 1))`
  -- there, since small discs have small area.
  have hconc : ∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
      δ₀ / (2 * (A + B + 1)) ≤ ∫ y in ball z ε ∩ Ω, f (φ n) y := by
    intro z hz ε hε
    refine eventually_le_setIntegral_ball_of_le_measureReal_add_setIntegral_ball
      (δ := δ₀ / (A + B + 1))
      hΩm (by rw [Measure.volume_eq_prod]; exact measure_singleton _)
      ⟨1, one_pos, measure_ball_lt_top.ne⟩ (fun n ↦ hf0 (φ n))
      (fun n ↦ hint (φ n)) ?_ hε fun ρ hρ ↦ ?_
    · rw [mul_comm, ← div_div]
      exact half_lt_self (by positivity)
    filter_upwards [hconc' z hz ρ hρ] with n hn
    have h := hgS (φ n) (S := ball z ρ ∩ Ω) (measurableSet_ball.inter hΩm) inter_subset_right
    rw [div_le_iff₀ hC₀0]
    simp only [hf_def] at h ⊢
    linarith
  exact ⟨φ, Z, v, hφ, hZΩ, card_mul_le_of_forall_eventually_le_setIntegral_ball hΩm
    (fun n ↦ hf0 (φ n)) (fun n ↦ hint (φ n)) (fun n ↦ hE (φ n)) hconc, hconc, hbd, hvc, hvK,
    hlim⟩

end TauCeti.SymplecticForm
