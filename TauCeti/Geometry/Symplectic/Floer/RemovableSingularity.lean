/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Graph
public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.HigherIntegrability
public import TauCeti.Geometry.Symplectic.JHolomorphic.WeakDerivative
import TauCeti.Analysis.Calculus.FDeriv.WithLp
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.Geometry.Symplectic.CompatibleMetric
import TauCeti.Geometry.Symplectic.Complex.Line
import TauCeti.Geometry.Symplectic.Prod.WithLp
import TauCeti.Geometry.Symplectic.SymplecticTransport
import TauCeti.Geometry.Symplectic.Transport

/-!
# Removal of singularities for Floer solutions

In local coordinates `z = s + i t ∈ ℂ` on the domain and `x ∈ V` on the target, the
inhomogeneous Cauchy–Riemann equation of Hamiltonian Floer theory reads

`∂ₜu - X(z, u) i = J(z, u) (∂ₛu - X(z, u) 1)`,

for a domain-dependent almost complex structure `J(z, x)` and a Hamiltonian one-form
`X(z, x) : ℂ →L[ℝ] V`, as in `TauCeti.Geometry.Symplectic.Floer.Compactness`. This file proves
that an isolated singularity of a finite-energy solution with compact image is removable, in the
three forms already known for pseudoholomorphic curves in
`TauCeti.Geometry.Symplectic.JHolomorphic.RemovableSingularity`,
`TauCeti.Geometry.Symplectic.JHolomorphic.WeakDerivative` and
`TauCeti.Geometry.Symplectic.JHolomorphic.Energy.HigherIntegrability`. Let `u` be a `C³`
solution on the punctured disc `B(z₀, R) \ {z₀}`, with image in a compact set `K`, where `J` and
`X` are `C²` on an open set containing `B(z₀, R) ×ˢ K`, `J` is uniformly tamed by a symplectic
form `ω` along `u`, and `∫ ‖∂ₛu‖²` is finite. Then:

* `u` has a limit `q ∈ K` at `z₀`, and setting `u(z₀) = q` gives a continuous map on the disc
  (`TauCeti.Floer.exists_continuousOn_update_of_finite_energy`);
* the classical differential of `u` is the weak differential of this extension on the whole
  disc (`TauCeti.Floer.exists_hasWeakFDerivOn_update_of_finite_energy`);
* the differential of the extension is in `Lᵖ` near `z₀` for some `p > 2`
  (`TauCeti.Floer.exists_continuousOn_update_memLp_fderiv_of_finite_energy`).

In Gromov–Floer compactness a sequence of solutions with bounded energy converges off finitely
many bubbling points
(`TauCeti.Floer.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset`); these theorems
are what extend a limit that is a smooth solution off those points across them.

## Implementation notes

Gromov's graph construction turns `u` into a pseudoholomorphic curve
(`TauCeti.Floer.graphStructure`). The taming form of the graph built in
`TauCeti.Geometry.Symplectic.Floer.Graph` varies with the point, while the removal theorems for
pseudoholomorphic curves need one symplectic form compatible with the Euclidean inner product.
We therefore rescale the domain factor of the graph: for `λ > 0` the map
`G(z) = (λ z, u(z))` into `WithLp 2 (ℂ × V)` solves `∂ₜG = J'(G) ∂ₛG` for Gromov's structure
`J'` of the rescaled data `J(λ⁻¹ w, x)` and `λ⁻¹ X(λ⁻¹ w, x)`. The direct sum of the area form of
`ℂ` and `ω` tames `J'` with a uniform constant once `λ` is large: on `(ξ, v)` it equals
`‖ξ‖² + ω(v, J v)` up to cross terms of size `λ⁻¹ ‖ξ‖ ‖v‖`. The graph has finite energy
`∫ (λ² + ‖∂ₛu‖²)` on the bounded disc and compact image, so the pseudoholomorphic theorems
apply to it, and `u` is its second component. The bounds on `J` and `X` come from a compact set,
so the graph is used on the smaller disc `B(z₀, R / 2)`; off `z₀` the solution is smooth, which
extends the conclusions back to `B(z₀, R)`.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. 82 (1985),
  307–347.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Section 4.5 (removal of singularities) and Section 8.1 (Gromov's graph construction).
-/

public section

open Complex Filter MeasureTheory Metric Set Topology

namespace TauCeti.Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}

/-- **The rescaled graph structure is uniformly tamed.** If `ω(v, A v) ≥ c ‖v‖²`, `‖A‖ ≤ M` and
`‖Y‖ ≤ ε` with `(M + 1) ε ≤ min 1 c`, then the direct sum `Ω` of the area form of `ℂ` and `ω`
satisfies `Ω(ζ, J' ζ) ≥ (min 1 c / 2) ‖ζ‖²` for Gromov's structure
`J'(ξ, v) = (i ξ, A (v - Y ξ) + Y (i ξ))` of `A` and the one-form `Y`. -/
private theorem mul_norm_sq_le_graph {Ω : SymplecticForm (WithLp 2 (ℂ × V))}
    (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w)
    (hΩ : ∀ p q, Ω p q = stdComplexSymplecticForm p.fst q.fst + ω p.snd q.snd)
    {A : V →L[ℝ] V} {Y : ℂ →L[ℝ] V} {c M ε : ℝ} (hA : ∀ v, c * ‖v‖ ^ 2 ≤ ω v (A v))
    (hAM : ‖A‖ ≤ M) (hY : ‖Y‖ ≤ ε) (hε : (M + 1) * ε ≤ min 1 c) (ζ : WithLp 2 (ℂ × V)) :
    min 1 c / 2 * ‖ζ‖ ^ 2 ≤
      Ω ζ (WithLp.toLp 2 (I * ζ.fst, A (ζ.snd - Y ζ.fst) + Y (I * ζ.fst))) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans hAM
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hY
  have hm0 : 0 ≤ min 1 c := le_trans (by positivity) hε
  -- The two cross terms are bounded by `M ε ‖ξ‖ ‖v‖` and `ε ‖ξ‖ ‖v‖`.
  have h₁ : |ω ζ.snd (A (Y ζ.fst))| ≤ M * ε * (‖ζ.fst‖ * ‖ζ.snd‖) := by
    refine (ω.abs_apply_le_norm_mul_norm hg _ _).trans ?_
    calc ‖ζ.snd‖ * ‖A (Y ζ.fst)‖ ≤ ‖ζ.snd‖ * (M * (ε * ‖ζ.fst‖)) := by
          gcongr
          exact A.le_of_opNorm_le hAM _ |>.trans (by gcongr; exact Y.le_of_opNorm_le hY _)
      _ = M * ε * (‖ζ.fst‖ * ‖ζ.snd‖) := by ring
  have h₂ : |ω ζ.snd (Y (I * ζ.fst))| ≤ ε * (‖ζ.fst‖ * ‖ζ.snd‖) := by
    refine (ω.abs_apply_le_norm_mul_norm hg _ _).trans ?_
    calc ‖ζ.snd‖ * ‖Y (I * ζ.fst)‖ ≤ ‖ζ.snd‖ * (ε * ‖ζ.fst‖) := by
          gcongr
          simpa using Y.le_of_opNorm_le hY (I * ζ.fst)
      _ = ε * (‖ζ.fst‖ * ‖ζ.snd‖) := by ring
  have hstd : stdComplexSymplecticForm ζ.fst (I * ζ.fst) = ‖ζ.fst‖ ^ 2 := by
    simpa [AlmostComplexStructure.ofComplexModule_apply, Complex.normSq_eq_norm_sq] using
      stdComplexSymplecticForm_apply_ofComplexModule ζ.fst
  rw [hΩ]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, hstd, map_sub, map_add]
  rw [WithLp.prod_norm_sq_eq_of_L2]
  have hcross : (M + 1) * ε * (‖ζ.fst‖ * ‖ζ.snd‖) ≤ min 1 c * (‖ζ.fst‖ * ‖ζ.snd‖) :=
    mul_le_mul_of_nonneg_right hε (by positivity)
  nlinarith [hA ζ.snd, abs_le.1 h₁, abs_le.1 h₂, mul_nonneg hm0 (sq_nonneg (‖ζ.fst‖ - ‖ζ.snd‖)),
    mul_le_mul_of_nonneg_right (min_le_left 1 c) (sq_nonneg ‖ζ.fst‖),
    mul_le_mul_of_nonneg_right (min_le_right 1 c) (sq_nonneg ‖ζ.snd‖)]

variable {J : ℂ × V → V →L[ℝ] V} {X : ℂ × V → ℂ →L[ℝ] V} {u : ℂ → V}
  {z₀ : ℂ} {R c : ℝ} {W : Set (ℂ × V)} {K : Set V}

/-- **The rescaled graph of a Floer solution is a pseudoholomorphic curve.** Under the
hypotheses of the removal theorems below, for a suitable `λ > 0` the map `G(z) = (λ z, u(z))`
into `WithLp 2 (ℂ × V)` satisfies, on the smaller disc `B(z₀, R / 2)`, all hypotheses of the
removal theorems for pseudoholomorphic curves in
`TauCeti.Geometry.Symplectic.JHolomorphic.RemovableSingularity`, for Gromov's structure `J'` of
the rescaled data and the direct sum `Ω` of the area form of `ℂ` and `ω`. -/
private theorem exists_graph (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w) (hc : 0 < c) (hR : 0 < R)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hX : ContDiffOn ℝ 2 X W) (hK : IsCompact K)
    (hKW : ball z₀ R ×ˢ K ⊆ W)
    (hJsq : ∀ z ∈ ball z₀ R, ∀ x ∈ K, ∀ v, J (z, x) (J (z, x) v) = -v)
    (hu : ContDiffOn ℝ 3 u (ball z₀ R \ {z₀}))
    (hF : ∀ z ∈ ball z₀ R \ {z₀},
      fderiv ℝ u z I - X (z, u z) I = J (z, u z) (fderiv ℝ u z 1 - X (z, u z) 1))
    (huK : MapsTo u (ball z₀ R \ {z₀}) K)
    (htame : ∀ z ∈ ball z₀ R \ {z₀}, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (z, u z) v))
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (ball z₀ R)) :
    ∃ (Ω : SymplecticForm (WithLp 2 (ℂ × V))) (J₁ : AlmostComplexStructure (WithLp 2 (ℂ × V)))
      (c' : ℝ) (J' : WithLp 2 (ℂ × V) → WithLp 2 (ℂ × V) →L[ℝ] WithLp 2 (ℂ × V))
      (W' K' : Set (WithLp 2 (ℂ × V))) (G : ℂ → WithLp 2 (ℂ × V)),
      (∀ p q, Ω p (J₁ q) = inner ℝ p q) ∧ 0 < c' ∧ IsOpen W' ∧ ContDiffOn ℝ 2 J' W' ∧
      IsCompact K' ∧ K' ⊆ W' ∧ (∀ p ∈ K', ∀ ζ, J' p (J' p ζ) = -ζ) ∧
      ContDiffOn ℝ 3 G (ball z₀ (R / 2) \ {z₀}) ∧
      (∀ z ∈ ball z₀ (R / 2) \ {z₀}, fderiv ℝ G z I = J' (G z) (fderiv ℝ G z 1)) ∧
      MapsTo G (ball z₀ (R / 2) \ {z₀}) K' ∧
      (∀ z ∈ ball z₀ (R / 2) \ {z₀}, ∀ ζ, c' * ‖ζ‖ ^ 2 ≤ Ω ζ (J' (G z) ζ)) ∧
      IntegrableOn (fun z ↦ ‖fderiv ℝ G z 1‖ ^ 2) (ball z₀ (R / 2)) ∧
      (∀ z, (G z).snd = u z) ∧ ∀ p ∈ K', p.snd ∈ K := by
  -- Structure of the proof: restrict to the disc `B(z₀, R / 2)`, whose closure lies in
  -- `B(z₀, R)`; build the compatible form `Ω`; bound `J` and `X` on the compact set
  -- `closedBall z₀ (R / 2) ×ˢ K` and choose the scale `l`; define the rescaled data, Gromov's
  -- structure `J'` and the graph `G z = (l z, u z)`; then check the hypotheses one bullet at a
  -- time.
  have hr : closedBall z₀ (R / 2) ⊆ ball z₀ R := closedBall_subset_ball (half_lt_self hR)
  have hs : ball z₀ (R / 2) \ {z₀} ⊆ ball z₀ R \ {z₀} :=
    sdiff_subset_sdiff_left (ball_subset_ball (half_le_self hR.le))
  replace hKW : closedBall z₀ (R / 2) ×ˢ K ⊆ W := (prod_mono hr subset_rfl).trans hKW
  replace hu := hu.mono hs
  replace huK := huK.mono_left hs
  replace henergy := henergy.mono_set (ball_subset_ball (half_le_self hR.le))
  -- The direct sum `Ω` of the area form of `ℂ` and `ω` on `WithLp 2 (ℂ × V)`, compatible with
  -- its inner product through the direct sum `J₁` of `i` and `J₀`.
  set e : (ℂ × V) ≃ₗ[ℝ] WithLp 2 (ℂ × V) := (WithLp.linearEquiv 2 ℝ (ℂ × V)).symm
  set Ω := (stdComplexSymplecticForm.prod ω).transport e
  set J₁ := ((AlmostComplexStructure.ofComplexModule ℂ).prod J₀).transport e
  have hΩ (p q : WithLp 2 (ℂ × V)) :
      Ω p q = stdComplexSymplecticForm p.fst q.fst + ω p.snd q.snd := by
    simp [Ω, e]
  have hΩJ (p q : WithLp 2 (ℂ × V)) : Ω p (J₁ q) = inner ℝ p q :=
    SymplecticForm.prod_transport_withLpLinearEquiv_symm_apply_prod_transport_eq_inner
      stdComplexSymplecticForm_apply_ofComplexModule_eq_inner hg p q
  have hD : IsCompact (closedBall z₀ (R / 2) ×ˢ K) := (isCompact_closedBall z₀ (R / 2)).prod hK
  obtain ⟨M, hM⟩ := hD.exists_bound_of_continuousOn (hJ.continuousOn.mono hKW)
  obtain ⟨B, hB⟩ := hD.exists_bound_of_continuousOn (hX.continuousOn.mono hKW)
  have hm : 0 < min 1 c := lt_min one_pos hc
  -- The scale `l`: the rescaled one-form `l⁻¹ X` has norm at most `l⁻¹ B₀`, small enough for the
  -- direct-sum form to tame Gromov's structure.
  set M₀ := max M 0
  set B₀ := max B 0
  set l : ℝ := (M₀ + 1) * B₀ / min 1 c + 1 with hl
  have hl0 : 0 < l := by positivity
  have hlε : (M₀ + 1) * (l⁻¹ * B₀) ≤ min 1 c := by
    have h : (M₀ + 1) * (l⁻¹ * B₀) = (M₀ + 1) * B₀ / l := by field_simp
    rw [h, div_le_iff₀ hl0, hl, mul_add, mul_div_cancel₀ _ hm.ne', mul_one]
    linarith
  set S : ℂ × V → ℂ × V := fun q ↦ (l⁻¹ • q.1, q.2)
  have hS {n : WithTop ℕ∞} : ContDiff ℝ n S := (contDiff_fst.const_smul l⁻¹).prodMk contDiff_snd
  set T : ℂ × V → WithLp 2 (ℂ × V) := fun q ↦ WithLp.toLp 2 (l • q.1, q.2)
  have hT : Continuous T := (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ V).symm.continuous.comp
    ((continuous_fst.const_smul l).prodMk continuous_snd)
  have hST (q : ℂ × V) : S (T q).ofLp = q := by
    simp only [S, T, inv_smul_smul₀ hl0.ne']
  set J' := graphStructure (fun q ↦ J (S q)) (fun q ↦ l⁻¹ • X (S q))
  set G : ℂ → WithLp 2 (ℂ × V) := fun z ↦ T (z, u z)
  have hGS (z : ℂ) : S (G z).ofLp = (z, u z) := hST (z, u z)
  have hdiff (z : ℂ) (hz : z ∈ ball z₀ (R / 2) \ {z₀}) : DifferentiableAt ℝ u z :=
    (hu.differentiableOn (by norm_num) z hz).differentiableAt
      ((isOpen_ball.sdiff isClosed_singleton).mem_nhds hz)
  have hsmul (z : ℂ) : DifferentiableAt ℝ (fun w : ℂ ↦ l • w) z :=
    differentiableAt_id.const_smul l
  have hsmul' (z : ℂ) : fderiv ℝ (fun w : ℂ ↦ l • w) z = l • ContinuousLinearMap.id ℝ ℂ :=
    ((hasFDerivAt_id z).const_smul l).fderiv
  have hGd (z : ℂ) (hz : z ∈ ball z₀ (R / 2) \ {z₀}) (v : ℂ) :
      fderiv ℝ G z v = WithLp.toLp 2 (l • v, fderiv ℝ u z v) := by
    rw [show G = fun w ↦ WithLp.toLp 2 (l • w, u w) from rfl,
      fderiv_toLp_prodMk_apply (hsmul z) (hdiff z hz), hsmul']
    simp
  refine ⟨Ω, J₁, min 1 c / 2, J', WithLp.ofLp ⁻¹' (S ⁻¹' W), T '' (closedBall z₀ (R / 2) ×ˢ K), G,
    hΩJ, half_pos hm,
    (hW.preimage (hS (n := 0)).continuous).preimage (WithLp.prod_continuous_ofLp 2 ℂ V),
    contDiffOn_graphStructure (hJ.comp hS.contDiffOn (mapsTo_preimage _ _))
      ((hX.comp hS.contDiffOn (mapsTo_preimage _ _)).const_smul l⁻¹),
    hD.image hT, ?_, ?_, ?_, fun z hz ↦ ?_, fun z hz ↦ ⟨(z, u z),
      ⟨ball_subset_closedBall hz.1, huK hz⟩, rfl⟩, fun z hz ζ ↦ ?_, ?_, fun z ↦ rfl, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    simpa [hST] using hKW hq
  · rintro _ ⟨q, hq, rfl⟩ ζ
    exact graphStructure_graphStructure (fun v ↦ by simpa [hST] using hJsq _ (hr hq.1) _ hq.2 v) ζ
  · exact (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ V).symm.contDiff.comp_contDiffOn
      ((contDiffOn_id.const_smul l).prodMk hu)
  · -- The graph equation is the Floer equation, after the rescaling cancels.
    rw [hGd z hz, hGd z hz, graphStructure_apply, WithLp.ext_iff, Prod.ext_iff]
    have hX1 : (l⁻¹ • X (z, u z)) (l • 1) = X (z, u z) 1 := by
      rw [smul_apply, map_smul, inv_smul_smul₀ hl0.ne']
    have hXI : (l⁻¹ • X (z, u z)) (I * (l • 1)) = X (z, u z) I := by
      rw [show I * (l • (1 : ℂ)) = l • I by simp [mul_comm], smul_apply,
        map_smul, inv_smul_smul₀ hl0.ne']
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, hGS, hX1, hXI]
    refine ⟨by simp [mul_comm], ?_⟩
    exact sub_eq_iff_eq_add.1 (hF z (hs hz))
  · have hp : (z, u z) ∈ closedBall z₀ (R / 2) ×ˢ K := ⟨ball_subset_closedBall hz.1, huK hz⟩
    have h := mul_norm_sq_le_graph hg hΩ (A := J (z, u z)) (Y := l⁻¹ • X (z, u z)) (M := M₀)
      (ε := l⁻¹ * B₀) (htame z (hs hz)) ((hM _ hp).trans (le_max_left _ _)) ?_ hlε ζ
    · simpa [J', graphStructure_apply, hGS] using h
    · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hl0.le)]
      exact mul_le_mul_of_nonneg_left ((hB _ hp).trans (le_max_left _ _)) (inv_nonneg.2 hl0.le)
  · -- The graph has energy density `l² + ‖∂ₛu‖²`, integrable on the bounded disc.
    have hi : IntegrableOn (fun z ↦ l ^ 2 + ‖fderiv ℝ u z 1‖ ^ 2) (ball z₀ (R / 2) \ {z₀}) :=
      ((integrableOn_const (C := l ^ 2) measure_ball_lt_top.ne).add henergy).mono_set
        sdiff_subset
    refine (hi.congr_fun (fun z hz ↦ ?_)
      (measurableSet_ball.diff (measurableSet_singleton _))).congr_set_ae
      (sdiff_null_ae_eq_self (measure_singleton z₀)).symm
    rw [show G = fun w ↦ WithLp.toLp 2 (l • w, u w) from rfl,
      norm_fderiv_toLp_prodMk_apply_sq (hsmul z) (hdiff z hz), hsmul']
    simp [abs_of_pos hl0]
  · rintro _ ⟨q, hq, rfl⟩
    simpa [T] using hq.2

/-- Off the puncture, the differential of `u` is the second component of the differential of a
graph `G` of `u`. -/
private theorem fderiv_eq_sndL_comp {G : ℂ → WithLp 2 (ℂ × V)}
    (hG : ContDiffOn ℝ 3 G (ball z₀ R \ {z₀})) (hGu : ∀ z, (G z).snd = u z) {z : ℂ}
    (hz : z ∈ ball z₀ R \ {z₀}) :
    fderiv ℝ u z = (WithLp.sndL 2 ℝ ℂ V).comp (fderiv ℝ G z) := by
  have hGd := (hG.differentiableOn (by norm_num) z hz).differentiableAt
    ((isOpen_ball.sdiff isClosed_singleton).mem_nhds hz)
  simpa only [hGu] using hGd.fderiv_withLp_snd

variable [FiniteDimensional ℝ V]

open Classical in
/-- **Continuous removal of an isolated singularity of a Floer solution.** Let `u` be a `C³`
solution of `∂ₜu - X(z, u) i = J(z, u) (∂ₛu - X(z, u) 1)` on the punctured disc
`B(z₀, R) \ {z₀}`, with image in a compact set `K`, where `J` and `X` are `C²` on an open set
containing `B(z₀, R) ×ˢ K` and `J² = -1` there. Suppose that `ω` tames `J(z, u(z))`
with a uniform constant `c > 0`, that `ω` is compatible with the inner product through a fixed
complex structure `J₀`, and that `∫ ‖∂ₛu‖²` is finite. Then `u` has a limit `q ∈ K` at `z₀`, and
setting `u(z₀) = q` gives a continuous map on the disc with image in `K`. -/
theorem exists_continuousOn_update_of_finite_energy (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w)
    (hc : 0 < c) (hR : 0 < R) (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W)
    (hX : ContDiffOn ℝ 2 X W) (hK : IsCompact K) (hKW : ball z₀ R ×ˢ K ⊆ W)
    (hJsq : ∀ z ∈ ball z₀ R, ∀ x ∈ K, ∀ v, J (z, x) (J (z, x) v) = -v)
    (hu : ContDiffOn ℝ 3 u (ball z₀ R \ {z₀}))
    (hF : ∀ z ∈ ball z₀ R \ {z₀},
      fderiv ℝ u z I - X (z, u z) I = J (z, u z) (fderiv ℝ u z 1 - X (z, u z) 1))
    (huK : MapsTo u (ball z₀ R \ {z₀}) K)
    (htame : ∀ z ∈ ball z₀ R \ {z₀}, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (z, u z) v))
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (ball z₀ R)) :
    ∃ q ∈ K, Tendsto u (𝓝[≠] z₀) (𝓝 q) ∧
      ContinuousOn (Function.update u z₀ q) (ball z₀ R) ∧
      MapsTo (Function.update u z₀ q) (ball z₀ R) K := by
  obtain ⟨Ω, J₁, c', J', W', K', G, hΩJ, hc', hW', hJ', hK', hK'W, hJsq', hG, hCR, hGK, htame',
    henergy', hGu, hK'K⟩ := exists_graph hg hc hR hW hJ hX hK hKW hJsq hu hF huK htame henergy
  obtain ⟨q', hq', hlim, -, -⟩ := Ω.exists_continuousOn_update_of_finite_energy hΩJ hc'
    (half_pos hR) hW' hJ' hK' hK'W hJsq' hG hCR hGK htame' henergy'
  -- `u` is the second component of its graph. The graph only lives on `B(z₀, R / 2)`, so
  -- continuity on `B(z₀, R)` comes from the limit at `z₀` and the smoothness of `u` off `z₀`.
  have hlim_u : Tendsto u (𝓝[≠] z₀) (𝓝 q'.snd) := by
    have h := ((WithLp.sndL 2 ℝ ℂ V).continuous.tendsto q').comp hlim
    simpa [Function.comp_def, hGu] using h
  refine ⟨q'.snd, hK'K _ hq', hlim_u,
    continuousOn_update_iff.mpr ⟨hu.continuousOn, fun _ ↦ ?_⟩, fun z hz ↦ ?_⟩
  · exact hlim_u.mono_left (nhdsWithin_mono _ (sdiff_subset_compl _ _))
  · by_cases hzz : z = z₀
    · subst z
      simpa using hK'K _ hq'
    · simpa [Function.update_of_ne hzz] using huK ⟨hz, hzz⟩

open Classical in
/-- **The filled Floer solution is weakly differentiable across the singularity.** Under the
hypotheses of `TauCeti.Floer.exists_continuousOn_update_of_finite_energy`, the continuous
extension of `u` across `z₀` has the classical differential of `u` as its weak differential on
the whole disc: no distribution concentrates at `z₀`. No differentiability at `z₀` is asserted.
-/
theorem exists_hasWeakFDerivOn_update_of_finite_energy (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w)
    (hc : 0 < c) (hR : 0 < R) (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W)
    (hX : ContDiffOn ℝ 2 X W) (hK : IsCompact K) (hKW : ball z₀ R ×ˢ K ⊆ W)
    (hJsq : ∀ z ∈ ball z₀ R, ∀ x ∈ K, ∀ v, J (z, x) (J (z, x) v) = -v)
    (hu : ContDiffOn ℝ 3 u (ball z₀ R \ {z₀}))
    (hF : ∀ z ∈ ball z₀ R \ {z₀},
      fderiv ℝ u z I - X (z, u z) I = J (z, u z) (fderiv ℝ u z 1 - X (z, u z) 1))
    (huK : MapsTo u (ball z₀ R \ {z₀}) K)
    (htame : ∀ z ∈ ball z₀ R \ {z₀}, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (z, u z) v))
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (ball z₀ R)) :
    ∃ q ∈ K, ContinuousOn (Function.update u z₀ q) (ball z₀ R) ∧
      MapsTo (Function.update u z₀ q) (ball z₀ R) K ∧
      HasWeakFDerivOn volume ⟨ball z₀ R, isOpen_ball⟩ (Function.update u z₀ q)
        (fderiv ℝ u) := by
  obtain ⟨q, hq, -, hcont, hmaps⟩ := exists_continuousOn_update_of_finite_energy hg hc hR hW hJ
    hX hK hKW hJsq hu hF huK htame henergy
  obtain ⟨Ω, J₁, c', J', W', K', G, hΩJ, hc', hW', hJ', hK', hK'W, hJsq', hG, hCR, hGK, htame',
    henergy', hGu, -⟩ := exists_graph hg hc hR hW hJ hX hK hKW hJsq hu hF huK htame henergy
  obtain ⟨q', -, -, -, hweak⟩ := Ω.exists_hasWeakFDerivOn_update_of_finite_energy hΩJ hc'
    (half_pos hR) hW' hJ' hK' hK'W hJsq' hG hCR hGK htame' henergy'
  refine ⟨q, hq, hcont, hmaps, ?_⟩
  -- On `B(z₀, R / 2)`, `u` is the second component of its graph, so the two fillings and the two
  -- differentials agree off `z₀`.
  have hne : ∀ᵐ z ∂volume.restrict (ball z₀ (R / 2)), z ∈ ball z₀ (R / 2) \ {z₀} := by
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (volume.ae_ne z₀)] with z hz hzne
    exact ⟨hz, hzne⟩
  have h₁ : HasWeakFDerivOn volume ⟨ball z₀ (R / 2), isOpen_ball⟩ (Function.update u z₀ q)
      (fderiv ℝ u) := by
    refine ((hweak.clm_comp (WithLp.sndL 2 ℝ ℂ V)).congr_ae ?_).congr_ae_deriv ?_
    · filter_upwards [hne] with z hz
      simp [Function.update_of_ne hz.2, hGu]
    · filter_upwards [hne] with z hz
      exact (fderiv_eq_sndL_comp hG hGu hz).symm
  -- Off `z₀`, `u` is `C¹`, so its classical differential is a weak one; the two pieces glue.
  have hB : IsOpen (ball z₀ R \ {z₀}) := isOpen_ball.sdiff isClosed_singleton
  have h₂ : HasWeakFDerivOn volume ⟨ball z₀ R \ {z₀}, hB⟩ (Function.update u z₀ q)
      (fderiv ℝ u) := by
    refine (hasWeakFDerivOn_of_differentiableOn ?_ fun z hz ↦ ?_).congr_ae ?_
    · exact (hu.continuousOn_fderiv_of_isOpen hB (by norm_num)).locallyIntegrableOn
        hB.measurableSet
    · exact (hu.differentiableOn (by norm_num) z hz).differentiableAt (hB.mem_nhds hz)
    · filter_upwards [ae_restrict_mem hB.measurableSet] with z hz
      exact (Function.update_of_ne hz.2 _ _).symm
  refine (h₁.sup h₂).mono fun z hz ↦ ?_
  by_cases hzz : z = z₀
  · exact Or.inl (hzz ▸ mem_ball_self (half_pos hR))
  · exact Or.inr ⟨hz, hzz⟩

open Classical in
/-- **Higher integrability across the singularity of a Floer solution.** Under the hypotheses of
`TauCeti.Floer.exists_continuousOn_update_of_finite_energy`, the differential of the continuous
extension of `u` across `z₀` belongs to `Lᵖ` on a smaller disc about `z₀` for some `p > 2`.
No differentiability at `z₀` is asserted. -/
theorem exists_continuousOn_update_memLp_fderiv_of_finite_energy
    (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w) (hc : 0 < c) (hR : 0 < R) (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 2 J W) (hX : ContDiffOn ℝ 2 X W) (hK : IsCompact K)
    (hKW : ball z₀ R ×ˢ K ⊆ W)
    (hJsq : ∀ z ∈ ball z₀ R, ∀ x ∈ K, ∀ v, J (z, x) (J (z, x) v) = -v)
    (hu : ContDiffOn ℝ 3 u (ball z₀ R \ {z₀}))
    (hF : ∀ z ∈ ball z₀ R \ {z₀},
      fderiv ℝ u z I - X (z, u z) I = J (z, u z) (fderiv ℝ u z 1 - X (z, u z) 1))
    (huK : MapsTo u (ball z₀ R \ {z₀}) K)
    (htame : ∀ z ∈ ball z₀ R \ {z₀}, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (z, u z) v))
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (ball z₀ R)) :
    ∃ q ∈ K, ContinuousOn (Function.update u z₀ q) (ball z₀ R) ∧
      MapsTo (Function.update u z₀ q) (ball z₀ R) K ∧
      ∃ ε > 0, ε < R ∧ ∃ p : ℝ, 2 < p ∧
        MemLp (fderiv ℝ (Function.update u z₀ q)) (ENNReal.ofReal p)
          (volume.restrict (ball z₀ ε)) := by
  obtain ⟨q, hq, -, hcont, hmaps⟩ := exists_continuousOn_update_of_finite_energy hg hc hR hW hJ
    hX hK hKW hJsq hu hF huK htame henergy
  obtain ⟨Ω, J₁, c', J', W', K', G, hΩJ, hc', hW', hJ', hK', hK'W, hJsq', hG, hCR, hGK, htame',
    henergy', hGu, -⟩ := exists_graph hg hc hR hW hJ hX hK hKW hJsq hu hF huK htame henergy
  obtain ⟨q', -, -, -, ε, hε, hεR, p, hp, hmem⟩ :=
    Ω.exists_continuousOn_update_memLp_fderiv_of_finite_energy hΩJ hc' (half_pos hR) hW' hJ'
      hK' hK'W hJsq' hG hCR hGK htame' henergy'
  refine ⟨q, hq, hcont, hmaps, ε, hε, hεR.trans (half_lt_self hR), p, hp, ?_⟩
  -- Off `z₀`, the differential of `u` is the second component of the differential of its graph.
  refine (((ContinuousLinearMap.compL ℝ ℂ (WithLp 2 (ℂ × V)) V)
    (WithLp.sndL 2 ℝ ℂ V)).comp_memLp' hmem).ae_eq ?_
  filter_upwards [ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae (volume.ae_ne z₀)] with z hzε hzne
  have hz : z ∈ ball z₀ (R / 2) \ {z₀} := ⟨ball_subset_ball hεR.le hzε, hzne⟩
  have hupd : ∀ᶠ w in 𝓝 z, w ≠ z₀ := isOpen_compl_singleton.mem_nhds hzne
  have hG' : fderiv ℝ (Function.update G z₀ q') z = fderiv ℝ G z :=
    Filter.EventuallyEq.fderiv_eq (hupd.mono fun w hw ↦ Function.update_of_ne hw _ _)
  have hu' : fderiv ℝ (Function.update u z₀ q) z = fderiv ℝ u z :=
    Filter.EventuallyEq.fderiv_eq (hupd.mono fun w hw ↦ Function.update_of_ne hw _ _)
  rw [Function.comp_apply, hG', hu', fderiv_eq_sndL_comp hG hGu hz,
    ContinuousLinearMap.compL_apply]

end TauCeti.Floer
