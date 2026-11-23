/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Energy
public import TauCeti.Analysis.Sobolev.WeakDeriv.Removable
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Analysis.Calculus.FDeriv.WithLp
import TauCeti.Geometry.Symplectic.Floer.Compactness.Basic
import TauCeti.Geometry.Symplectic.Floer.Graph.Basic
import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.HigherIntegrability
import TauCeti.Geometry.Symplectic.JHolomorphic.Line
import TauCeti.Geometry.Symplectic.JHolomorphic.RemovableSingularity
import TauCeti.MeasureTheory.Integral.EnergyConcentration

/-!
# Removal of finite-energy punctures of Floer solutions

A finite-energy solution of the inhomogeneous Floer equation `(du - X_K)^{0,1} = 0` on a punctured
disc, with image in a compact set and tame almost complex structures, extends continuously across
the puncture. In Gromov–Floer compactness, a sequence of Floer solutions of bounded energy
converges off finitely many bubbling points (`TauCeti.Geometry.Symplectic.Floer.Compactness.Basic`);
this is the first step in extending the limit across those points. It is the inhomogeneous
counterpart of `TauCeti.SymplecticForm.exists_continuousOn_update_of_finite_energy` for
pseudoholomorphic curves.

The proof reduces to that case by Gromov's graph construction
(`TauCeti.Geometry.Symplectic.Floer.Graph.Basic`). Rescale the domain coordinate of the graph by a
scale `μ > 0`: the map `U(w) = (μ w, u w)` into `ℂ × V` solves the Cauchy–Riemann equation of
Gromov's structure `graphStructure J' X'` for the rescaled data `J'(ζ, x) = J(μ⁻¹ ζ, x)` and
`X'(ζ, x) = μ⁻¹ X(μ⁻¹ ζ, x)` (`TauCeti.Floer.fderiv_toLp_smul_prodMk_I_eq_graphStructure_iff`).
The split form `σ ⊕ ω` of the standard area form `σ` on `ℂ` and `ω`
tames Gromov's structure as soon as the Hamiltonian term is small compared with the taming
constant of `J` (`TauCeti.Floer.mul_norm_sq_le_prodL2_graphStructure`), which a large `μ`
achieves. The graph has finite energy
`∫ (μ² + ‖∂ₛu‖²)` on the disc, so the removal theorem for pseudoholomorphic curves applies to it,
and the second coordinate of its extension extends `u`. The higher integrability of the
differential of a pseudoholomorphic curve near a puncture
(`TauCeti.SymplecticForm.exists_pos_two_lt_memLp_fderiv_of_finite_energy`) applies to the graph
as well, and the differential of the graph dominates that of `u`.

## Main results

* `TauCeti.Floer.exists_continuousOn_update_of_finite_energy`: the coordinate form, for a
  solution of `∂ₜu - X(z, u) i = J(z, u)(∂ₛu - X(z, u) 1)` on a punctured disc in `ℂ`.
* `TauCeti.Floer.exists_hasWeakFDerivOn_update_of_finite_energy`: the extension of such a
  solution is weakly differentiable on the disc, with weak derivative the classical differential of
  `u`, which lies in `Lᵖ` near the puncture for some `p > 2`.
* `TauCeti.SymplecticForm.exists_continuousOn_update_of_floer`: the Floer form, for a solution of
  `(du - X_K)^{0,1} = 0` on `Ω \ {z₀}` for an open `Ω ⊆ ℝ × ℝ`, with integrable Floer energy
  density and `J` tamed by `ω`.

None of these results asserts differentiability at the puncture; that needs elliptic regularity
of the extension.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Section 4.5 (removal of singularities) and Section 8.1 (the graph construction for the
  inhomogeneous equation).
* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. 82 (1985),
  307–347.
-/

public section

open Complex Filter MeasureTheory Metric Set Topology

namespace TauCeti.Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}

omit [InnerProductSpace ℝ V] in
/-- Updating a map continuous on `s \ {z₀}` at `z₀` to its limit there gives a map continuous on
`s`, with values in `K` if the map and the limit lie in `K`. -/
private theorem continuousOn_update_mapsTo {α : Type*} [TopologicalSpace α] [T1Space α]
    [DecidableEq α] {s : Set α} {z₀ : α} {u : α → V} {K : Set V} {q : V}
    (hu : ContinuousOn u (s \ {z₀})) (huK : MapsTo u (s \ {z₀}) K)
    (hqK : q ∈ K) (hlim : Tendsto u (𝓝[≠] z₀) (𝓝 q)) :
    ContinuousOn (Function.update u z₀ q) s ∧ MapsTo (Function.update u z₀ q) s K := by
  refine ⟨continuousOn_update_iff.2 ⟨hu, fun _ ↦
    hlim.mono_left (nhdsWithin_mono _ (sdiff_subset_compl _ _))⟩, fun y hy ↦ ?_⟩
  rcases eq_or_ne y z₀ with rfl | hyz
  · simpa using hqK
  · simpa [Function.update_of_ne hyz] using huK ⟨hy, hyz⟩

section Euclidean

variable [FiniteDimensional ℝ V] {J : ℂ × V → V →L[ℝ] V} {X : ℂ × V → ℂ →L[ℝ] V}
  {W : Set (ℂ × V)} {K : Set V} {u : ℂ → V} {z₀ : ℂ} {R c : ℝ}

omit [FiniteDimensional ℝ V] in
/-- **Choosing the scale of the graph.** Given a taming constant `c > 0` and bounds `B` for `J`
and `M` for `X`, there is a scale `μ > 0` such that at every point `(z, x)` where these hold, the
split form `σ ⊕ ω` tames Gromov's structure of the rescaled data `J(μ⁻¹ ζ, x)`, `μ⁻¹ X(μ⁻¹ ζ, x)`
at `(μ z, x)`, with constant `min 1 c / 4`. -/
private theorem exists_pos_forall_mul_norm_sq_le_prodL2 (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w)
    (hc : 0 < c) (B M : ℝ) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ ⦃z : ℂ⦄ ⦃x : V⦄, (∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (z, x) v)) →
      ‖J (z, x)‖ ≤ B →
      ‖X (z, x)‖ ≤ M → ∀ ζ, min 1 c / 4 * ‖ζ‖ ^ 2 ≤ stdComplexSymplecticForm.prodL2 ω ζ
        (graphStructure (fun q ↦ J (μ⁻¹ • q.1, q.2)) (fun q ↦ μ⁻¹ • X (μ⁻¹ • q.1, q.2))
          (WithLp.toLp 2 (μ • z, x)) ζ) := by
  have hlim : Tendsto (fun μ : ℝ ↦ μ⁻¹ * |M|) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.mul_const |M|
  have hlim2 : Tendsto (fun μ : ℝ ↦ 2 * (μ⁻¹ * |M| * (B + 1)) ^ 2) atTop (𝓝 0) := by
    simpa using ((hlim.mul_const (B + 1)).pow 2).const_mul 2
  obtain ⟨μ, hμ, hμ1, hμ2⟩ : ∃ μ : ℝ, 0 < μ ∧ μ⁻¹ * |M| ≤ 1 / 2 ∧
      2 * (μ⁻¹ * |M| * (B + 1)) ^ 2 ≤ c :=
    (((eventually_gt_atTop 0).and (hlim.eventually (ge_mem_nhds (by norm_num)))).and
      (hlim2.eventually (ge_mem_nhds hc))).exists.imp fun _ h ↦ ⟨h.1.1, h.1.2, h.2⟩
  refine ⟨μ, hμ, fun z x htame hJ hX ζ ↦ ?_⟩
  have hp : (μ⁻¹ • (WithLp.toLp 2 (μ • z, x)).ofLp.1, (WithLp.toLp 2 (μ • z, x)).ofLp.2) =
      (z, x) := by simp only [inv_smul_smul₀ hμ.ne']
  refine mul_norm_sq_le_prodL2_graphStructure hg hc (by positivity) hμ1 hμ2
    (fun v ↦ by simpa only [hp] using htame v) (by simpa only [hp] using hJ) ?_ ζ
  simp only [hp]
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hμ.le)]
  exact mul_le_mul_of_nonneg_left (hX.trans (le_abs_self M)) (inv_nonneg.2 hμ.le)

omit [FiniteDimensional ℝ V] in
/-- The graph `w ↦ (μ w, u w)` has energy density `‖∂ₛ(μ w, u w)‖² = μ² + ‖∂ₛu‖²`, so it has finite
energy on a disc wherever `u` does. -/
private theorem integrableOn_norm_fderiv_toLp_smul_prodMk_sq (μ : ℝ)
    (hdiff : ∀ z ∈ ball z₀ R \ {z₀}, DifferentiableAt ℝ u z)
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (ball z₀ R)) :
    IntegrableOn (fun z ↦ ‖fderiv ℝ (fun w ↦ WithLp.toLp 2 (μ • w, u w)) z 1‖ ^ 2)
      (ball z₀ R) := by
  have hint : IntegrableOn (fun z ↦ μ ^ 2 + ‖fderiv ℝ u z 1‖ ^ 2) (ball z₀ R \ {z₀}) :=
    ((integrableOn_const measure_ball_lt_top.ne).add henergy).mono_set sdiff_subset
  refine (hint.congr_fun (fun z hz ↦ ?_) (measurableSet_ball.diff
    (measurableSet_singleton _))).congr_set_ae (sdiff_null_ae_eq_self (measure_singleton _)).symm
  have hfd : HasFDerivAt (fun w : ℂ ↦ μ • w) (μ • ContinuousLinearMap.id ℝ ℂ) z :=
    (hasFDerivAt_id z).const_smul μ
  rw [norm_fderiv_toLp_prodMk_apply_sq hfd.differentiableAt (hdiff z hz), hfd.fderiv]
  simp

omit [FiniteDimensional ℝ V] in
/-- Gromov's structure of the data `J(μ⁻¹ ζ, x)`, `μ⁻¹ X(μ⁻¹ ζ, x)` rescaled by `μ ≠ 0` is `C²` on
an open set containing the compact image of `S` under `(z, x) ↦ (μ z, x)`, and squares to `-1` on
that image, when `J` and `X` are `C²` on an open `W ⊇ S` and `J² = -1` on the compact set `S`. -/
private theorem exists_rescaled_graphStructure_data {μ : ℝ} (hμ : μ ≠ 0) {S : Set (ℂ × V)}
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hX : ContDiffOn ℝ 2 X W) (hS : IsCompact S)
    (hSW : S ⊆ W) (hJsq : ∀ p ∈ S, ∀ v, J p (J p v) = -v) :
    ∃ W' : Set (WithLp 2 (ℂ × V)), IsOpen W' ∧
      ContDiffOn ℝ 2
        (graphStructure (fun q ↦ J (μ⁻¹ • q.1, q.2)) (fun q ↦ μ⁻¹ • X (μ⁻¹ • q.1, q.2))) W' ∧
      IsCompact ((fun q ↦ WithLp.toLp 2 (μ • q.1, q.2)) '' S) ∧
      (fun q ↦ WithLp.toLp 2 (μ • q.1, q.2)) '' S ⊆ W' ∧
      ∀ p ∈ (fun q ↦ WithLp.toLp 2 (μ • q.1, q.2)) '' S, ∀ ζ,
        graphStructure (fun q ↦ J (μ⁻¹ • q.1, q.2)) (fun q ↦ μ⁻¹ • X (μ⁻¹ • q.1, q.2)) p
          (graphStructure (fun q ↦ J (μ⁻¹ • q.1, q.2)) (fun q ↦ μ⁻¹ • X (μ⁻¹ • q.1, q.2)) p ζ) =
          -ζ := by
  set g : ℂ × V → ℂ × V := fun q ↦ (μ⁻¹ • q.1, q.2)
  have hgc : ContDiff ℝ ⊤ g := (contDiff_fst.const_smul _).prodMk contDiff_snd
  have hge (q : ℂ × V) : g (WithLp.toLp 2 (μ • q.1, q.2)).ofLp = q := by
    simp only [g, inv_smul_smul₀ hμ]
  refine ⟨WithLp.ofLp ⁻¹' (g ⁻¹' W),
    (hW.preimage hgc.continuous).preimage (WithLp.prod_continuous_ofLp 2 ℂ V),
    contDiffOn_graphStructure (hJ.comp (hgc.of_le le_top).contDiffOn (mapsTo_preimage _ _))
      ((hX.comp (hgc.of_le le_top).contDiffOn (mapsTo_preimage _ _)).const_smul _),
    hS.image ((WithLp.prod_continuous_toLp 2 ℂ V).comp
      ((continuous_fst.const_smul μ).prodMk continuous_snd)), ?_, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    simpa only [mem_preimage, hge] using hSW hq
  · rintro _ ⟨q, hq, rfl⟩ ζ
    exact graphStructure_graphStructure (fun v ↦ by
      simpa only [WithLp.ofLp_toLp, inv_smul_smul₀ hμ] using hJsq q hq v) ζ

/-- **Reduction to the graph.** Under the hypotheses of
`TauCeti.Floer.exists_continuousOn_update_of_finite_energy`, `u` has a limit `q ∈ K` at the
puncture, and its differential lies in `Lᵖ` on a smaller disc about `z₀` for some `p > 2`. Both are
read off the graph `w ↦ (μ w, u w)`, pseudoholomorphic for Gromov's structure of the data rescaled
by a scale `μ` at which the split form `σ ⊕ ω` tames it along the graph. -/
private theorem exists_tendsto_memLp_fderiv_of_finite_energy
    (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w) (hc : 0 < c) (hR : 0 < R)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hX : ContDiffOn ℝ 2 X W) (hK : IsCompact K)
    (hKW : closedBall z₀ R ×ˢ K ⊆ W)
    (hJsq : ∀ p ∈ closedBall z₀ R ×ˢ K, ∀ v, J p (J p v) = -v)
    (hu : ContDiffOn ℝ 3 u (ball z₀ R \ {z₀}))
    (hF : ∀ z ∈ ball z₀ R \ {z₀},
      fderiv ℝ u z I - X (z, u z) I = J (z, u z) (fderiv ℝ u z 1 - X (z, u z) 1))
    (huK : MapsTo u (ball z₀ R \ {z₀}) K)
    (htame : ∀ z ∈ ball z₀ R \ {z₀}, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (z, u z) v))
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (ball z₀ R)) :
    ∃ q ∈ K, Tendsto u (𝓝[≠] z₀) (𝓝 q) ∧ ∃ ε > 0, ε < R ∧ ∃ p : ℝ, 2 < p ∧
      MemLp (fderiv ℝ u) (ENNReal.ofReal p) (volume.restrict (ball z₀ ε)) := by
  -- Pass to the graph `U w = (μ w, u w)`, pseudoholomorphic for Gromov's structure of the data
  -- rescaled by a scale `μ` at which the split form `σ ⊕ ω` tames it along the graph.
  have hBK : IsCompact (closedBall z₀ R ×ˢ K) := (isCompact_closedBall z₀ R).prod hK
  obtain ⟨B, hBd⟩ := hBK.exists_bound_of_continuousOn (hJ.continuousOn.mono hKW)
  obtain ⟨M, hMd⟩ := hBK.exists_bound_of_continuousOn (hX.continuousOn.mono hKW)
  obtain ⟨μ, hμ, htameμ⟩ := exists_pos_forall_mul_norm_sq_le_prodL2 (J := J) (X := X) hg hc B M
  set e : ℂ × V → WithLp 2 (ℂ × V) := fun q ↦ WithLp.toLp 2 (μ • q.1, q.2)
  set U : ℂ → WithLp 2 (ℂ × V) := fun w ↦ WithLp.toLp 2 (μ • w, u w)
  obtain ⟨W', hW', hJ', hK', hK'W', hJsq'⟩ :=
    exists_rescaled_graphStructure_data hμ.ne' hW hJ hX hBK hKW hJsq
  have hdiff : ∀ z ∈ ball z₀ R \ {z₀}, DifferentiableAt ℝ u z := fun z hz ↦
    (hu.differentiableOn (by norm_num)).differentiableAt
      ((isOpen_ball.sdiff isClosed_singleton).mem_nhds hz)
  have hmem : ∀ z ∈ ball z₀ R \ {z₀}, (z, u z) ∈ closedBall z₀ R ×ˢ K := fun z hz ↦
    ⟨ball_subset_closedBall hz.1, huK hz⟩
  -- The remaining hypotheses of the removal theorems for pseudoholomorphic curves, for `U`.
  have hg' := SymplecticForm.prodL2_apply_prodL2_eq_inner
    stdComplexSymplecticForm_apply_ofComplexModule_eq_inner hg
  have hc' : 0 < min 1 c / 4 := by positivity
  have hU : ContDiffOn ℝ 3 U (ball z₀ R \ {z₀}) :=
    WithLp.contDiff_toLp.comp_contDiffOn ((contDiff_id.const_smul μ).contDiffOn.prodMk hu)
  have hCR (z : ℂ) (hz : z ∈ ball z₀ R \ {z₀}) :=
    (fderiv_toLp_smul_prodMk_I_eq_graphStructure_iff hμ.ne' (hdiff z hz)).2 (hF z hz)
  have hUK : MapsTo U (ball z₀ R \ {z₀}) (e '' (closedBall z₀ R ×ˢ K)) := fun z hz ↦
    ⟨(z, u z), hmem z hz, rfl⟩
  have htame' (z : ℂ) (hz : z ∈ ball z₀ R \ {z₀}) :=
    htameμ (htame z hz) (hBd _ (hmem z hz)) (hMd _ (hmem z hz))
  have henergy' := integrableOn_norm_fderiv_toLp_smul_prodMk_sq μ hdiff henergy
  obtain ⟨q', hq'K, hq'lim, -, -⟩ :=
    (stdComplexSymplecticForm.prodL2 ω).exists_continuousOn_update_of_finite_energy hg' hc' hR hW'
      hJ' hK' hK'W' hJsq' hU hCR hUK htame' henergy'
  obtain ⟨ε, hε, hεR, p, hp, hLp⟩ :=
    (stdComplexSymplecticForm.prodL2 ω).exists_pos_two_lt_memLp_fderiv_of_finite_energy hg' hc'
      hR hW' hJ' hK' hK'W' hJsq' hU hCR hUK htame' henergy'
  -- Read off the second coordinate of the graph; its differential dominates that of `u`.
  obtain ⟨⟨z, x⟩, hzx, rfl⟩ := hq'K
  have hsnd : Continuous fun ζ : WithLp 2 (ℂ × V) ↦ ζ.snd :=
    continuous_snd.comp (WithLp.prod_continuous_ofLp 2 ℂ V)
  refine ⟨x, hzx.2, by simpa [U, e, Function.comp_def] using (hsnd.tendsto _).comp hq'lim,
    ε, hε, hεR, p, hp, hLp.of_le (measurable_fderiv ℝ u).aestronglyMeasurable
      (Eventually.of_forall fun y ↦ ?_)⟩
  exact norm_fderiv_le_norm_fderiv_toLp_prodMk_right (differentiableAt_fun_id.const_smul μ)

open Classical in
/-- **Continuous removal of a finite-energy puncture of a Floer solution.** Let `J(z, x)` and
the Hamiltonian one-form `X(z, x)` be `C²` on an open set containing `closedBall z₀ R ×ˢ K` for a
compact `K ⊆ V`, with `J² = -1` on `closedBall z₀ R ×ˢ K`, and let `u` be a `C³` solution of the
inhomogeneous Cauchy–Riemann equation `∂ₜu - X(z, u) i = J(z, u)(∂ₛu - X(z, u) 1)` on the
punctured disc `ball z₀ R \ {z₀}`, with image in `K`, finite energy `∫ ‖∂ₛu‖²` and `J(z, u z)`
uniformly tamed by `ω`. Then `u` has a limit `q ∈ K` at the puncture, and updating `u` at `z₀` to
`q` gives a continuous map on the whole disc with image in `K`.

The fixed structure `J₀` identifies the given inner product with a symplectic metric. No
regularity at the puncture is assumed or concluded beyond continuity. -/
theorem exists_continuousOn_update_of_finite_energy
    (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w) (hc : 0 < c) (hR : 0 < R)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hX : ContDiffOn ℝ 2 X W) (hK : IsCompact K)
    (hKW : closedBall z₀ R ×ˢ K ⊆ W)
    (hJsq : ∀ p ∈ closedBall z₀ R ×ˢ K, ∀ v, J p (J p v) = -v)
    (hu : ContDiffOn ℝ 3 u (ball z₀ R \ {z₀}))
    (hF : ∀ z ∈ ball z₀ R \ {z₀},
      fderiv ℝ u z I - X (z, u z) I = J (z, u z) (fderiv ℝ u z 1 - X (z, u z) 1))
    (huK : MapsTo u (ball z₀ R \ {z₀}) K)
    (htame : ∀ z ∈ ball z₀ R \ {z₀}, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (z, u z) v))
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (ball z₀ R)) :
    ∃ q ∈ K, Tendsto u (𝓝[≠] z₀) (𝓝 q) ∧
      ContinuousOn (Function.update u z₀ q) (ball z₀ R) ∧
      MapsTo (Function.update u z₀ q) (ball z₀ R) K := by
  obtain ⟨q, hqK, hlim, -⟩ := exists_tendsto_memLp_fderiv_of_finite_energy hg hc hR hW hJ hX hK
    hKW hJsq hu hF huK htame henergy
  exact ⟨q, hqK, hlim, continuousOn_update_mapsTo hu.continuousOn huK hqK hlim⟩

open Classical in
/-- **Weak differentiability across a finite-energy puncture of a Floer solution.** Under the
hypotheses of `TauCeti.Floer.exists_continuousOn_update_of_finite_energy`, the continuous extension
of `u` across `z₀` is weakly differentiable on the disc, with weak derivative the classical
differential of `u` off `z₀`, and this differential lies in `Lᵖ` on a smaller disc about `z₀` for
some `p > 2`. No differentiability at `z₀` is asserted. -/
theorem exists_hasWeakFDerivOn_update_of_finite_energy
    (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w) (hc : 0 < c) (hR : 0 < R)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hX : ContDiffOn ℝ 2 X W) (hK : IsCompact K)
    (hKW : closedBall z₀ R ×ˢ K ⊆ W)
    (hJsq : ∀ p ∈ closedBall z₀ R ×ˢ K, ∀ v, J p (J p v) = -v)
    (hu : ContDiffOn ℝ 3 u (ball z₀ R \ {z₀}))
    (hF : ∀ z ∈ ball z₀ R \ {z₀},
      fderiv ℝ u z I - X (z, u z) I = J (z, u z) (fderiv ℝ u z 1 - X (z, u z) 1))
    (huK : MapsTo u (ball z₀ R \ {z₀}) K)
    (htame : ∀ z ∈ ball z₀ R \ {z₀}, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (z, u z) v))
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (ball z₀ R)) :
    ∃ q ∈ K, ContinuousOn (Function.update u z₀ q) (ball z₀ R) ∧
      MapsTo (Function.update u z₀ q) (ball z₀ R) K ∧
      HasWeakFDerivOn volume ⟨ball z₀ R, isOpen_ball⟩ (Function.update u z₀ q) (fderiv ℝ u) ∧
      ∃ ε > 0, ε < R ∧ ∃ p : ℝ, 2 < p ∧
        MemLp (fderiv ℝ u) (ENNReal.ofReal p) (volume.restrict (ball z₀ ε)) := by
  obtain ⟨q, hqK, hlim, ε, hε, hεR, p, hp, hmem⟩ := exists_tendsto_memLp_fderiv_of_finite_energy
    hg hc hR hW hJ hX hK hKW hJsq hu hF huK htame henergy
  obtain ⟨hcont, hmaps⟩ := continuousOn_update_mapsTo hu.continuousOn huK hqK hlim
  have hP : IsOpen (ball z₀ R \ {z₀}) := isOpen_ball.sdiff isClosed_singleton
  -- The differential is integrable near `z₀` by higher integrability, and continuous elsewhere.
  have hloc : LocallyIntegrableOn (fderiv ℝ u) (ball z₀ R) := by
    intro y hy
    rcases eq_or_ne y z₀ with rfl | hyz
    · have : IsFiniteMeasure (volume.restrict (ball y ε)) := ⟨by simpa using measure_ball_lt_top⟩
      exact ⟨ball y ε, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds y hε),
        hmem.integrable (by
          rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith))⟩
    · have h := (hu.continuousOn_fderiv_of_isOpen hP (by norm_num)).integrableAt_nhdsWithin
        (μ := volume) hP.measurableSet ⟨hy, hyz⟩
      rwa [sdiff_eq, nhdsWithin_inter_of_mem'
        (mem_nhdsWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds hyz))] at h
  refine ⟨q, hqK, hcont, hmaps, hasWeakFDerivOn_of_hasFDerivAt_off_countable
    (countable_singleton z₀) hcont hloc fun z hz ↦ ?_, ε, hε, hεR, p, hp, hmem⟩
  have hdu := ((hu.differentiableOn (by norm_num)) z hz).differentiableAt (hP.mem_nhds hz)
  have heq : Function.update u z₀ q =ᶠ[𝓝 z] u := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hz.2] with w hw
    exact Function.update_of_ne hw _ _
  exact hdu.hasFDerivAt.congr_of_eventuallyEq heq

end Euclidean

end TauCeti.Floer

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ}
  {J : ℝ × ℝ → V → AlmostComplexStructure V} {W : Set ((ℝ × ℝ) × V)} {K : Set V}
  {Ω : Set (ℝ × ℝ)} {z₀ : ℝ × ℝ} {u : ℝ × ℝ → V}

/-- The Hamiltonian one-form of a `C³` perturbation, read in the complex coordinate
`equivRealProdCLM`, is `C²`. -/
private theorem contDiffOn_hamiltonianOneForm_equivRealProdCLM (hW : IsOpen W)
    (hKs : ContDiffOn ℝ 3 (Function.uncurry Ks) W) (hKt : ContDiffOn ℝ 3 (Function.uncurry Kt) W) :
    ContDiffOn ℝ 2 (fun q : ℂ × V ↦
        ω.hamiltonianOneForm Ks Kt (equivRealProdCLM q.1) q.2 ∘L (equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ))
      ((fun q : ℂ × V ↦ (equivRealProdCLM q.1, q.2)) ⁻¹' W) := by
  have h := ω.contDiffOn_hamiltonianOneForm (n := 2) (P := ℝ) (Ks := fun _ ↦ Ks)
    (Kt := fun _ ↦ Kt) (isOpen_univ.prod hW)
    (hKs.comp contDiff_snd.contDiffOn fun q hq ↦ hq.2)
    (hKt.comp contDiff_snd.contDiffOn fun q hq ↦ hq.2)
  have he : ContDiff ℝ 2 fun q : ℂ × V ↦ ((0 : ℝ), (equivRealProdCLM q.1, q.2)) :=
    contDiff_const.prodMk ((equivRealProdCLM.contDiff.comp contDiff_fst).prodMk contDiff_snd)
  exact (h.comp he.contDiffOn fun q hq ↦ ⟨trivial, hq⟩).clm_comp contDiffOn_const

/-- The removal of a puncture, read in the complex coordinate `y = equivRealProdCLM⁻¹ z`: a
finite-energy Floer solution on a punctured disc about `y₀` has a limit at `y₀`. -/
private theorem exists_mem_tendsto_comp_equivRealProdCLM (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w)
    (hW : IsOpen W) (hKs : ContDiffOn ℝ 3 (Function.uncurry Ks) W)
    (hKt : ContDiffOn ℝ 3 (Function.uncurry Kt) W)
    (hJ : ContDiffOn ℝ 2
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hK : IsCompact K) {y₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hDW : closedBall y₀ r ×ˢ K ⊆ (fun q : ℂ × V ↦ (equivRealProdCLM q.1, q.2)) ⁻¹' W)
    (hJt : ∀ y ∈ closedBall y₀ r, ∀ x ∈ K, ω.Tames (J (equivRealProdCLM y) x))
    (hu : ContDiffOn ℝ 3 (u ∘ equivRealProdCLM) (ball y₀ r \ {y₀}))
    (hfl : ∀ y ∈ ball y₀ r \ {y₀}, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (equivRealProdCLM y) (u (equivRealProdCLM y)))
      (ω.perturbedFDeriv Ks Kt u (equivRealProdCLM y) : ℝ × ℝ →ₗ[ℝ] V))
    (huK : MapsTo (u ∘ equivRealProdCLM) (ball y₀ r \ {y₀}) K)
    (hint : IntegrableOn (fun y ↦ ω.floerEnergyDensity Ks Kt u (equivRealProdCLM y))
      (ball y₀ r)) :
    ∃ q ∈ K, Tendsto (u ∘ equivRealProdCLM) (𝓝[≠] y₀) (𝓝 q) := by
  set J' : ℂ × V → V →L[ℝ] V := fun q ↦
    (J (equivRealProdCLM q.1) q.2).toLinearMap.toContinuousLinearMap
  set X' : ℂ × V → ℂ →L[ℝ] V := fun q ↦
    ω.hamiltonianOneForm Ks Kt (equivRealProdCLM q.1) q.2 ∘L (equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ)
  have hD : IsCompact (closedBall y₀ r ×ˢ K) := (isCompact_closedBall y₀ r).prod hK
  have hJ' : ContDiffOn ℝ 2 J' ((fun q : ℂ × V ↦ (equivRealProdCLM q.1, q.2)) ⁻¹' W) :=
    hJ.comp ((equivRealProdCLM.contDiff.comp contDiff_fst).prodMk contDiff_snd).contDiffOn
      (mapsTo_preimage _ _)
  have hX' := contDiffOn_hamiltonianOneForm_equivRealProdCLM (ω := ω) hW hKs hKt
  -- A uniform taming constant `c` and a bound `M` for `X` on the compact disc.
  obtain ⟨c, hc, hJc⟩ := hD.exists_pos_forall_mul_norm_sq_le
    (b := fun q ↦ ((ContinuousLinearMap.compL ℝ V V ℝ).flip (J' q)).comp
      ω.toBilinForm.toContinuousBilinearMap)
    (((ContinuousLinearMap.compL ℝ V V ℝ).flip.continuous.comp_continuousOn
      (hJ'.continuousOn.mono hDW)).clm_comp continuousOn_const)
    (fun q hq v hv ↦ by simpa [J'] using hJt _ hq.1 _ hq.2 v hv)
  obtain ⟨M, hM⟩ := hD.exists_bound_of_continuousOn (hX'.continuousOn.mono hDW)
  have hmem : ∀ y ∈ ball y₀ r \ {y₀}, (y, (u ∘ equivRealProdCLM) y) ∈ closedBall y₀ r ×ˢ K :=
    fun y hy ↦ ⟨ball_subset_closedBall hy.1, huK hy⟩
  have htame : ∀ y ∈ ball y₀ r \ {y₀}, ∀ v,
      c * ‖v‖ ^ 2 ≤ ω v (J' (y, (u ∘ equivRealProdCLM) y) v) := fun y hy v ↦ by
    simpa [J'] using hJc _ (hmem y hy) v
  -- The energy density bounds `‖∂ₛu‖²`, so `∫ ‖∂ₛu‖²` is finite on the disc.
  have hS : MeasurableSet (ball y₀ r \ {y₀}) := measurableSet_ball.diff (measurableSet_singleton _)
  have henergy : IntegrableOn (fun y ↦ ‖fderiv ℝ (u ∘ equivRealProdCLM) y 1‖ ^ 2) (ball y₀ r) := by
    refine (integrableOn_of_le_mul_add (g := fun y ↦ ‖fderiv ℝ (u ∘ equivRealProdCLM) y 1‖ ^ 2)
      (A := 2 / c) (B := 2 * M ^ 2) hS
      ((measure_mono sdiff_subset).trans_lt measure_ball_lt_top).ne
      ((((hu.continuousOn_fderiv_of_isOpen (isOpen_ball.sdiff isClosed_singleton)
        (by norm_num)).clm_apply continuousOn_const).norm.pow 2).aestronglyMeasurable hS)
      (hint.mono_set sdiff_subset) (fun _ _ ↦ by positivity) fun y hy ↦ ?_).congr_set_ae
      (sdiff_null_ae_eq_self (measure_singleton _)).symm
    rw [fderiv_comp_equivRealProdCLM_one]
    refine (ω.norm_fderiv_stdComplexLineReal_sq_le hc (htame y hy) (hfl y hy)).trans ?_
    have h := ((X' _).le_opNorm 1).trans (mul_le_mul_of_nonneg_right (hM _ (hmem y hy))
      (norm_nonneg _))
    have hXs : ‖ω.hamiltonianVectorField (Ks (equivRealProdCLM y)) (u (equivRealProdCLM y))‖ ≤
        M := by simpa [X', equivRealProdCLM_one, hamiltonianOneForm_apply] using h
    gcongr
  exact (Floer.exists_continuousOn_update_of_finite_energy hg hc hr
    (hW.preimage ((equivRealProdCLM.continuous.comp continuous_fst).prodMk continuous_snd))
    hJ' hX' hK hDW (fun _ _ v ↦ by simp [J']) hu
    (fun y hy ↦ ω.isComplexLinearMap_perturbedFDeriv_iff_fderiv_comp_equivRealProdCLM_I_sub.1
      (hfl y hy)) huK htame
    henergy).imp fun _ h ↦ ⟨h.1, h.2.1⟩

open Classical in
/-- **A finite-energy Floer solution extends continuously across a puncture.** Let the
Hamiltonian perturbation `(Ks, Kt)` be `C³` and `J(z, x)` be `C²` on an open set
`W ⊆ (ℝ × ℝ) × V` containing `Ω × K`, for an open `Ω ∋ z₀` and a compact `K ⊆ V`, with `J(z, x)`
tamed by `ω` on `Ω × K`. Let `u` be a `C³` solution of the Floer equation `(du - X)^{0,1} = 0`
for the Hamiltonian one-form `X = ds ⊗ X_{Ks} + dt ⊗ X_{Kt}` on `Ω \ {z₀}`, with image in `K` and
integrable Floer energy density `ω(∂ₛu - X_{Ks}, ∂ₜu - X_{Kt})`. Then `u` has a limit `q ∈ K` at
`z₀`, and updating `u` at `z₀` to `q` gives a continuous map on `Ω` with image in `K`.

The fixed structure `J₀` identifies the given inner product with a symplectic metric. No
regularity at `z₀` is assumed or concluded beyond continuity. -/
theorem exists_continuousOn_update_of_floer (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w)
    (hW : IsOpen W) (hKs : ContDiffOn ℝ 3 (Function.uncurry Ks) W)
    (hKt : ContDiffOn ℝ 3 (Function.uncurry Kt) W)
    (hJ : ContDiffOn ℝ 2
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hΩKW : Ω ×ˢ K ⊆ W) (hz₀ : z₀ ∈ Ω)
    (hJt : ∀ z ∈ Ω, ∀ x ∈ K, ω.Tames (J z x)) (hu : ContDiffOn ℝ 3 u (Ω \ {z₀}))
    (hfl : ∀ z ∈ Ω \ {z₀}, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
      (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V))
    (huK : MapsTo u (Ω \ {z₀}) K) (henergy : IntegrableOn (ω.floerEnergyDensity Ks Kt u) Ω) :
    ∃ q ∈ K, Tendsto u (𝓝[≠] z₀) (𝓝 q) ∧ ContinuousOn (Function.update u z₀ q) Ω ∧
      MapsTo (Function.update u z₀ q) Ω K := by
  set L := equivRealProdCLM
  set y₀ := L.symm z₀
  -- A disc about `y₀ = L⁻¹ z₀` inside `L⁻¹ Ω`, in the complex coordinate.
  obtain ⟨r, hr, hrΩ⟩ := Metric.nhds_basis_closedBall.mem_iff.1
    ((hΩ.preimage L.continuous).mem_nhds (show L y₀ ∈ Ω by simpa [y₀] using hz₀))
  have hmaps : MapsTo L (ball y₀ r \ {y₀}) (Ω \ {z₀}) := fun y hy ↦
    ⟨hrΩ (ball_subset_closedBall hy.1), fun h ↦ hy.2 (by
      simpa [y₀] using congrArg L.symm (mem_singleton_iff.1 h))⟩
  have hint : IntegrableOn (fun y ↦ ω.floerEnergyDensity Ks Kt u (L y)) (ball y₀ r) :=
    ((volume_preserving_equiv_real_prod.integrableOn_comp_preimage
      measurableEquivRealProd.measurableEmbedding).2 henergy).mono_set
        fun y hy ↦ hrΩ (ball_subset_closedBall hy)
  obtain ⟨q, hqK, hlim⟩ := exists_mem_tendsto_comp_equivRealProdCLM hg hW hKs hKt hJ hK hr
    (fun q hq ↦ hΩKW ⟨hrΩ hq.1, hq.2⟩) (fun y hy ↦ hJt _ (hrΩ hy))
    (hu.comp L.contDiff.contDiffOn hmaps)
    (fun y hy ↦ hfl _ (hmaps hy)) (huK.comp hmaps) hint
  -- Back to the real coordinates `ℝ × ℝ`.
  have hlimu : Tendsto u (𝓝[≠] z₀) (𝓝 q) := by
    have hmap : map L (𝓝[≠] y₀) = 𝓝[≠] z₀ := by
      simpa [y₀] using L.toHomeomorph.map_punctured_nhds_eq y₀
    rw [← hmap, tendsto_map'_iff]
    exact hlim
  exact ⟨q, hqK, hlimu, continuousOn_update_mapsTo hu.continuousOn huK hqK hlimu⟩

end TauCeti.SymplecticForm
