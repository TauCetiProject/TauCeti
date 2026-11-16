/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Basic
public import TauCeti.Geometry.Symplectic.Floer.DerivativeConvergence
public import TauCeti.Geometry.Symplectic.Floer.Rescaling.Basic
import TauCeti.Geometry.Symplectic.Hamiltonian.Variation
import TauCeti.Topology.ContinuousMap.Ascoli

/-!
# The bubble at a point where Floer solutions blow up

Let `(V, ω)` be a finite-dimensional symplectic vector space, and let `uᵢ` be smooth solutions of
the Floer equation `(du - X_H)^{0,1} = 0` on an open set `U ⊆ ℝ × ℝ`, for a `C²` perturbation
`H = K_s ds + K_t dt` and a `C¹` family `J(z, x)` of almost complex structures, with values in a
compact set `K ⊆ V`. Suppose that their derivatives blow up along points
`zᵢ → z₀ ∈ U`. Hofer's lemma
(`TauCeti.SymplecticForm.exists_rescale_isComplexLinearMap_perturbedFDeriv`) gives centres
`cᵢ → z₀`, scales `εᵢ → 0` and radii `Rᵢ → ∞` such that the rescaled maps
`vᵢ(w) = uᵢ(cᵢ + εᵢ w)` solve the rescaled Floer equation on the squares `‖w‖ ≤ Rᵢ`, with
`‖dvᵢ‖ ≤ 2` there and `‖dvᵢ(0)‖ = 1`.

This file extracts the bubble from these rescaled maps
(`TauCeti.SymplecticForm.exists_rescale_tendstoLocallyUniformly_isJHolomorphicAt`). Along a
subsequence the rescaled maps converge in `C¹`, locally uniformly on the whole plane, to a `C¹` map
`v : ℝ × ℝ → K` which is holomorphic for the structure `J(z₀, ·)` frozen at the bubbling point. It
satisfies `‖dv(0)‖ = 1`, so it is not constant, and `‖dv‖ ≤ 2`. Its symplectic area is at most the
Floer energy concentrating at `z₀`. This is the plane of a sphere bubble at an interior point of a
Floer domain: the bubble of a sequence of Floer solutions is a pseudoholomorphic plane for a frozen
structure, not a solution of the Floer equation.

The convergence comes in two steps.

* **Values.** The rescaled maps are `2`-Lipschitz on the squares `‖w‖ ≤ Rᵢ` and take values in the
  compact set `K`, so the Arzelà–Ascoli theorem gives a subsequence converging locally uniformly on
  the plane (`TauCeti.exists_subseq_tendstoLocallyUniformly_of_lipschitzOnWith_closedBall`).
* **Derivatives.** In the complex coordinate `Complex.equivRealProdCLM` the rescaled maps solve the
  coordinate Floer equation for data depending on the parameter `(εᵢ, cᵢ)`: the structure
  `J(c + ε w, x)` and the Hamiltonian one-form of `ε H(c + ε w)`. These data are jointly `C¹` in the
  parameter, the domain point and the target point, and the parameters converge to `(0, z₀)`. So
  the derivatives converge on every disc
  (`TauCeti.Floer.tendstoLocallyUniformlyOn_fderiv_of_floer_of_tendsto`), and hence locally
  uniformly on the plane.

The limit is holomorphic for `J(z₀, ·)` by
`TauCeti.SymplecticForm.isComplexLinearMap_of_tendsto_rescale` and its area is bounded by
`TauCeti.SymplecticForm.lintegral_symplecticForm_le_liminf_of_tendsto_rescale`. The removal of the
singularity of the plane at infinity, and the identification of the blow-up points with the
bubbling points of the compactness theorem
`TauCeti.SymplecticForm.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset`, are not
treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications **52**, 2012, Section 4.2 (rescaling) and Section 4.6 (bubbling), and Section 8.1
  (bubbles of the inhomogeneous equation are holomorphic for the frozen structure).
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Ks Kt : ℝ × ℝ → V → ℝ} {J : ℝ × ℝ → V → AlmostComplexStructure V} {U : Set (ℝ × ℝ)}
  {K : Set V} {z₀ : ℝ × ℝ} {u : ℕ → ℝ × ℝ → V} {c : ℕ → ℝ × ℝ} {ε R : ℕ → ℝ}

omit [FiniteDimensional ℝ V] in
/-- **The values of rescaled maps converge along a subsequence.** Let `uᵢ` be `C¹` on an open
set `U` with values in a compact set `K`, and let the rescaled maps `w ↦ uᵢ(cᵢ + εᵢ w)` be defined
on the squares `‖w‖ ≤ Rᵢ` (with `cᵢ + εᵢ w ∈ U`) with derivatives of norm at most two there,
where `Rᵢ ≥ 0` and `Rᵢ → ∞`. Then a subsequence of the rescaled maps converges locally uniformly on
the whole plane. -/
private theorem exists_strictMono_tendstoLocallyUniformly_rescale (hU : IsOpen U)
    (hK : IsCompact K) (hu : ∀ i, ContDiffOn ℝ 1 (u i) U) (huK : ∀ i, MapsTo (u i) U K)
    (hR : Tendsto R atTop atTop) (hR0 : ∀ i, 0 ≤ R i)
    (hRw : ∀ i w, ‖w‖ ≤ R i →
      c i + ε i • w ∈ U ∧ ‖fderiv ℝ (fun w ↦ u i (c i + ε i • w)) w‖ ≤ 2) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℝ × ℝ → V,
      TendstoLocallyUniformly (fun n w ↦ u (φ n) (c (φ n) + ε (φ n) • w)) g atTop := by
  set v : ℕ → ℝ × ℝ → V := fun i w ↦ u i (c i + ε i • w)
  -- The rescaled maps are `2`-Lipschitz on the squares `‖w‖ ≤ R i`.
  have hlip (i : ℕ) : LipschitzOnWith 2 (v i) (closedBall 0 (R i)) :=
    (convex_closedBall 0 (R i)).lipschitzOnWith_of_nnNorm_fderiv_le
      (fun w hw ↦ (((hu i).differentiableOn one_ne_zero _ (hRw i w
        (mem_closedBall_zero_iff.1 hw)).1).differentiableAt (hU.mem_nhds (hRw i w
          (mem_closedBall_zero_iff.1 hw)).1)).comp w (by fun_prop)) fun w hw ↦ by
        rw [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_ofNat]
        exact (hRw i w (mem_closedBall_zero_iff.1 hw)).2
  obtain ⟨φ, hφ, g, hg⟩ := exists_subseq_tendstoLocallyUniformly_of_lipschitzOnWith_closedBall hK
    hR0 hR hlip fun i w hw ↦ huK i (hRw i w (mem_closedBall_zero_iff.1 hw)).1
  exact ⟨φ, hφ, g, hg⟩

/-- In the complex coordinate the rescaled maps solve, on a disc of radius `ρ`, the coordinate
Floer equation for data depending jointly `C¹` on the parameter `(εᵢ, cᵢ) → (0, z₀)`. So if they
converge pointwise to `g`, then `g` is `C¹` on the disc and their derivatives converge locally
uniformly there. -/
private theorem contDiffOn_and_tendstoLocallyUniformlyOn_fderiv_rescale (ω : SymplecticForm V)
    (hU : IsOpen U) (hz₀ : z₀ ∈ U)
    (hJ : ContDiffOn ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (U ×ˢ univ))
    (hKs : ContDiffOn ℝ 2 (uncurry Ks) (U ×ˢ univ)) (hKt : ContDiffOn ℝ 2 (uncurry Kt) (U ×ˢ univ))
    (hu : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (u i) U)
    (hsol : ∀ i, ∀ y ∈ U, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J y (u i y))
      (ω.perturbedFDeriv Ks Kt (u i) y : ℝ × ℝ →ₗ[ℝ] V))
    (hc : Tendsto c atTop (𝓝 z₀)) (hε : Tendsto ε atTop (𝓝 0)) (hε0 : ∀ i, ε i ≠ 0)
    {g : ℝ × ℝ → V} (hg : ∀ w, Tendsto (fun i ↦ u i (c i + ε i • w)) atTop (𝓝 (g w)))
    {ρ : ℝ} (hρ : ∀ i w, ‖w‖ < ρ →
      c i + ε i • w ∈ U ∧ ‖fderiv ℝ (fun w ↦ u i (c i + ε i • w)) w‖ ≤ 2) :
    ContDiffOn ℝ 1 (g ∘ equivRealProdCLM) (ball 0 ρ) ∧
      TendstoLocallyUniformlyOn
        (fun i ↦ fderiv ℝ ((fun w ↦ u i (c i + ε i • w)) ∘ equivRealProdCLM))
        (fderiv ℝ (g ∘ equivRealProdCLM)) atTop (ball 0 ρ) := by
  set e : ℂ ≃L[ℝ] ℝ × ℝ := equivRealProdCLM with he
  have hball {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) ρ) : ‖e ζ‖ < ρ := by
    refine lt_of_le_of_lt ?_ (mem_ball_zero_iff.1 hζ)
    simpa [he, Prod.norm_def] using max_le (abs_re_le_norm ζ) (abs_im_le_norm ζ)
  -- The data of the rescaled equation, as functions of the parameter `(ε, c)`.
  set m : (ℝ × (ℝ × ℝ)) × (ℂ × V) → (ℝ × ℝ) × V := fun q ↦ (q.1.2 + q.1.1 • e q.2.1, q.2.2)
  set m' : (ℝ × (ℝ × ℝ)) × ((ℝ × ℝ) × V) → (ℝ × ℝ) × V := fun q ↦ (q.1.2 + q.1.1 • q.2.1, q.2.2)
  have hm : ContDiff ℝ 1 m := by fun_prop
  have hm' : ContDiff ℝ 2 m' := by fun_prop
  have hresc {K' : ℝ × ℝ → V → ℝ} (hK' : ContDiffOn ℝ 2 (uncurry K') (U ×ˢ univ)) :
      ContDiffOn ℝ (1 + 1) (fun q : (ℝ × (ℝ × ℝ)) × ((ℝ × ℝ) × V) ↦
        q.1.1 * K' (q.1.2 + q.1.1 • q.2.1) q.2.2) (m' ⁻¹' (U ×ˢ univ)) :=
    contDiff_fst.fst.contDiffOn.mul (hK'.comp hm'.contDiffOn (mapsTo_preimage _ _))
  have hX := ω.contDiffOn_hamiltonianOneForm (P := ℝ × (ℝ × ℝ)) (n := 1)
    (Ks := fun p w x ↦ p.1 * Ks (p.2 + p.1 • w) x) (Kt := fun p w x ↦ p.1 * Kt (p.2 + p.1 • w) x)
    ((hU.prod isOpen_univ).preimage hm'.continuous) (hresc hKs) (hresc hKt)
  have hg' : ContDiff ℝ 1
      (fun q : (ℝ × (ℝ × ℝ)) × (ℂ × V) ↦ (q.1, (e q.2.1, q.2.2))) := by fun_prop
  obtain ⟨h1, h2, -⟩ := tendstoLocallyUniformlyOn_fderiv_of_floer_of_tendsto
    (P := ℝ × (ℝ × ℝ)) (W := m ⁻¹' (U ×ˢ univ))
    (J := fun p q ↦ (J (p.2 + p.1 • e q.1) q.2).toLinearMap.toContinuousLinearMap)
    (X := fun p q ↦ ω.hamiltonianOneForm (fun w x ↦ p.1 * Ks (p.2 + p.1 • w) x)
      (fun w x ↦ p.1 * Kt (p.2 + p.1 • w) x) (e q.1) q.2 ∘L (e : ℂ →L[ℝ] ℝ × ℝ))
    ((hU.prod isOpen_univ).preimage hm.continuous) (hJ.comp hm.contDiffOn (mapsTo_preimage _ _))
    ((hX.comp hg'.contDiffOn fun q hq ↦ hq).clm_comp contDiffOn_const) isOpen_ball
    (p := fun i ↦ (ε i, c i)) (p₀ := (0, z₀)) (hε.prodMk_nhds hc)
    (u := fun i ↦ (fun w ↦ u i (c i + ε i • w)) ∘ e) (v := g ∘ e)
    (fun y _ ↦ by simpa [m] using hz₀)
    (fun i ↦ (hu i).comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) fun ζ ↦ c i + ε i • e ζ).contDiffOn
      fun ζ hζ ↦ (hρ i _ (hball hζ)).1)
    (fun i y _ w ↦ by simp)
    (fun i y hy ↦ by
      simpa [he] using ω.fderiv_comp_equivRealProdCLM_I_sub (J := fun w x ↦ J (c i + ε i • w) x)
        (Ks := fun w x ↦ ε i * Ks (c i + ε i • w) x)
        (Kt := fun w x ↦ ε i * Kt (c i + ε i • w) x) (u := fun w ↦ u i (c i + ε i • w)) (y := y)
        ((ω.isComplexLinearMap_perturbedFDeriv_rescale_iff (hε0 i)).2
          (hsol i _ (hρ i _ (hball hy)).1)))
    (fun C _ hC ↦ ⟨2 * ‖(e : ℂ →L[ℝ] ℝ × ℝ)‖, fun i y hy ↦ by
      rw [e.comp_right_fderiv]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right
        (hρ i _ (hball (hC hy))).2 (norm_nonneg _))⟩)
    (fun y _ ↦ hg (e y))
  exact ⟨h1, h2⟩

/-- **The derivatives of rescaled maps converge on the plane.** If the rescaled maps
`w ↦ uᵢ(cᵢ + εᵢ w)` of solutions of the Floer equation, defined on squares `‖w‖ ≤ Rᵢ` with
`Rᵢ → ∞` and with derivatives of norm at most two there, converge pointwise to `g`, for centres
`cᵢ → z₀` and nonzero scales `εᵢ → 0`, then `g` is `C¹` and their derivatives converge to that of
`g` locally uniformly on the plane. -/
private theorem contDiff_and_tendstoLocallyUniformly_fderiv_rescale (ω : SymplecticForm V)
    (hU : IsOpen U) (hz₀ : z₀ ∈ U)
    (hJ : ContDiffOn ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (U ×ˢ univ))
    (hKs : ContDiffOn ℝ 2 (uncurry Ks) (U ×ˢ univ)) (hKt : ContDiffOn ℝ 2 (uncurry Kt) (U ×ˢ univ))
    (hu : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (u i) U)
    (hsol : ∀ i, ∀ y ∈ U, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J y (u i y))
      (ω.perturbedFDeriv Ks Kt (u i) y : ℝ × ℝ →ₗ[ℝ] V))
    (hc : Tendsto c atTop (𝓝 z₀)) (hε : Tendsto ε atTop (𝓝 0)) (hε0 : ∀ i, ε i ≠ 0)
    (hR : Tendsto R atTop atTop)
    (hRw : ∀ i w, ‖w‖ ≤ R i →
      c i + ε i • w ∈ U ∧ ‖fderiv ℝ (fun w ↦ u i (c i + ε i • w)) w‖ ≤ 2)
    {g : ℝ × ℝ → V} (hg : ∀ w, Tendsto (fun i ↦ u i (c i + ε i • w)) atTop (𝓝 (g w))) :
    ContDiff ℝ 1 g ∧
      TendstoLocallyUniformly (fun i ↦ fderiv ℝ (fun w ↦ u i (c i + ε i • w))) (fderiv ℝ g)
        atTop := by
  set e : ℂ ≃L[ℝ] ℝ × ℝ := equivRealProdCLM
  set v : ℕ → ℝ × ℝ → V := fun i w ↦ u i (c i + ε i • w)
  -- On the disc of radius `ρ`, apply the disc statement to the sequence from the index `M` on,
  -- with its first `M` terms replaced by the term `M`.
  have hdisc (ρ : ℕ) : ContDiffOn ℝ 1 (g ∘ e) (ball 0 ρ) ∧
      TendstoLocallyUniformlyOn (fun i ↦ fderiv ℝ (v i ∘ e)) (fderiv ℝ (g ∘ e)) atTop
        (ball 0 ρ) := by
    obtain ⟨M, hM⟩ := eventually_atTop.1 (hR.eventually_ge_atTop (ρ : ℝ))
    have hmax : Tendsto (fun i : ℕ ↦ max i M) atTop atTop :=
      tendsto_atTop_mono (fun i ↦ le_max_left i M) tendsto_id
    obtain ⟨h1, h2⟩ := ω.contDiffOn_and_tendstoLocallyUniformlyOn_fderiv_rescale
      (u := fun i ↦ u (max i M)) (c := fun i ↦ c (max i M)) (ε := fun i ↦ ε (max i M)) hU hz₀ hJ
      hKs hKt (fun i ↦ hu _) (fun i ↦ hsol _) (hc.comp hmax) (hε.comp hmax) (fun i ↦ hε0 _)
      (fun w ↦ (hg w).comp hmax)
      (fun i w hw ↦ hRw _ w (hw.le.trans (hM _ (le_max_right _ _))))
    refine ⟨h1, h2.congr_inseparable ((eventually_ge_atTop M).mono fun i hi _ _ ↦ ?_)⟩
    simp only [max_eq_left hi]
    rfl
  have hge : ContDiff ℝ 1 (g ∘ e) := contDiff_iff_contDiffAt.2 fun ζ ↦ by
    obtain ⟨ρ, hρ⟩ := exists_nat_gt ‖ζ‖
    exact (hdisc ρ).1.contDiffAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hρ))
  have hdC : TendstoLocallyUniformly (fun i ↦ fderiv ℝ (v i ∘ e)) (fderiv ℝ (g ∘ e)) atTop := by
    rw [← tendstoLocallyUniformlyOn_univ, ← iUnion_ball_nat (0 : ℂ)]
    exact tendstoLocallyUniformlyOn_iUnion (fun _ ↦ isOpen_ball) fun ρ ↦ (hdisc ρ).2
  -- Back in the coordinates `ℝ × ℝ`.
  have hback (f : ℝ × ℝ → V) (w : ℝ × ℝ) :
      fderiv ℝ f w = (fderiv ℝ (f ∘ e) (e.symm w)).comp (e.symm : ℝ × ℝ →L[ℝ] ℂ) := by
    have h := e.symm.comp_right_fderiv (f := f ∘ e) (x := w)
    rwa [show (f ∘ e) ∘ e.symm = f from funext fun w ↦ by simp] at h
  refine ⟨by simpa [comp_def] using hge.comp e.symm.contDiff, ?_⟩
  have h := ((ContinuousLinearMap.compL ℝ (ℝ × ℝ) ℂ V).flip
    (e.symm : ℝ × ℝ →L[ℝ] ℂ)).uniformContinuous.comp_tendstoLocallyUniformly
      (hdC.comp e.symm e.symm.continuous)
  simp only [comp_def, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply] at h
  rw [show (fun i ↦ fderiv ℝ (v i)) = fun i w ↦
      (fderiv ℝ (v i ∘ e) (e.symm w)).comp (e.symm : ℝ × ℝ →L[ℝ] ℂ) from
        funext fun i ↦ funext (hback _), funext (hback g)]
  simpa only [comp_def] using h

/-- **The bubble at a point where Floer solutions blow up.** Let `uᵢ` be smooth solutions of the
Floer equation `(du - X_H)^{0,1} = 0` on an open set `U ⊆ ℝ × ℝ`, for a `C²` perturbation
`H = K_s ds + K_t dt` and a `C¹` family `J(z, x)` of almost complex structures, with values in a
compact set `K`, and let
their derivatives blow up along points `zᵢ → z₀ ∈ U`. There are a subsequence `φ`, centres
`cₙ → z₀` and positive scales `εₙ → 0`, and a `C¹` map `v` from the plane to `K`, such that:

* `v` is holomorphic for the structure `J(z₀, ·)` frozen at `z₀`, with `‖dv(0)‖ = 1`, so that `v`
  is not constant, and `‖dv‖ ≤ 2`;
* the rescaled maps `w ↦ u_{φ n}(cₙ + εₙ w)` converge to `v` locally uniformly on the plane,
  and so do their derivatives;
* for every `δ > 0`, the symplectic area `∫ ω(∂_s v, ∂_t v)` of `v`, with the area density
  truncated at zero, is at most the lower limit of the Floer energies of `u_{φ n}` over the
  square `ball z₀ δ` (sup norm) of radius `δ` about `z₀`. -/
theorem exists_rescale_tendstoLocallyUniformly_isJHolomorphicAt (ω : SymplecticForm V)
    (hU : IsOpen U) (hz₀ : z₀ ∈ U) (hK : IsCompact K)
    (hJ : ContDiffOn ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (U ×ˢ univ))
    (hKs : ContDiffOn ℝ 2 (uncurry Ks) (U ×ˢ univ)) (hKt : ContDiffOn ℝ 2 (uncurry Kt) (U ×ˢ univ))
    (hu : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (u i) U) (huK : ∀ i, MapsTo (u i) U K)
    (hsol : ∀ i, ∀ y ∈ U, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J y (u i y))
      (ω.perturbedFDeriv Ks Kt (u i) y : ℝ × ℝ →ₗ[ℝ] V))
    {z : ℕ → ℝ × ℝ} (hz : Tendsto z atTop (𝓝 z₀))
    (hblow : Tendsto (fun i ↦ ‖fderiv ℝ (u i) (z i)‖) atTop atTop) :
    ∃ (φ : ℕ → ℕ) (c : ℕ → ℝ × ℝ) (ε : ℕ → ℝ) (v : ℝ × ℝ → V), StrictMono φ ∧
      (∀ n, 0 < ε n) ∧ Tendsto c atTop (𝓝 z₀) ∧ Tendsto ε atTop (𝓝 0) ∧
      ContDiff ℝ 1 v ∧ (∀ w, v w ∈ K) ∧ ‖fderiv ℝ v 0‖ = 1 ∧ (∀ w, ‖fderiv ℝ v w‖ ≤ 2) ∧
      (∀ w, IsJHolomorphicAt (fun _ ↦ AlmostComplexStructure.product ℝ) (J z₀) v w) ∧
      TendstoLocallyUniformly (fun n w ↦ u (φ n) (c n + ε n • w)) v atTop ∧
      TendstoLocallyUniformly (fun n ↦ fderiv ℝ (fun w ↦ u (φ n) (c n + ε n • w)))
        (fderiv ℝ v) atTop ∧
      ∀ δ > 0, ∫⁻ w, ENNReal.ofReal (ω (fderiv ℝ v w stdComplexLineReal)
          (fderiv ℝ v w stdComplexLineImag)) ≤
        liminf (fun n ↦ ∫⁻ y in ball z₀ δ,
          ENNReal.ofReal (ω.floerEnergyDensity Ks Kt (u (φ n)) y)) atTop := by
  have hu1 (i : ℕ) : ContDiffOn ℝ 1 (u i) U := (hu i).of_le (by simp)
  -- Hofer's rescaling at the blow-up points; from the index `N` on, the rescaled equation and the
  -- derivative bounds hold on the squares `‖w‖ ≤ R i`, and `R i ≥ 0`.
  obtain ⟨c, ε, R, hε, hc, hε0, hR, -, hev⟩ := ω.exists_rescale_isComplexLinearMap_perturbedFDeriv
    (l := atTop) (J := J) hU hz₀ hu1 (Eventually.of_forall hsol) hz hblow
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hev.and (hR.eventually_ge_atTop 0))
  have hRw (i : ℕ) (w : ℝ × ℝ) (hw : ‖w‖ ≤ R (i + N)) := ((hN _ (Nat.le_add_left N i)).1.2 w hw)
  -- The values, then the derivatives, converge along a subsequence `ψ`.
  obtain ⟨φ₁, hφ₁, g, hC0⟩ := exists_strictMono_tendstoLocallyUniformly_rescale
    (u := fun i ↦ u (i + N)) (c := fun i ↦ c (i + N)) (ε := fun i ↦ ε (i + N))
    (R := fun i ↦ R (i + N)) hU hK (fun i ↦ hu1 _) (fun i ↦ huK _)
    (hR.comp (tendsto_add_atTop_nat N)) (fun i ↦ (hN _ (Nat.le_add_left N i)).2)
    fun i w hw ↦ ⟨(hRw i w hw).1, (hRw i w hw).2.1⟩
  set ψ : ℕ → ℕ := fun n ↦ φ₁ n + N
  have hψ : StrictMono ψ := fun a b h ↦ Nat.add_lt_add_right (hφ₁ h) N
  have hcψ : Tendsto (fun n ↦ c (ψ n)) atTop (𝓝 z₀) := hc.comp hψ.tendsto_atTop
  have hεψ : Tendsto (fun n ↦ ε (ψ n)) atTop (𝓝 0) := hε0.comp hψ.tendsto_atTop
  have hRψ : Tendsto (fun n ↦ R (ψ n)) atTop atTop := hR.comp hψ.tendsto_atTop
  have hpt (w : ℝ × ℝ) : Tendsto (fun n ↦ u (ψ n) (c (ψ n) + ε (ψ n) • w)) atTop (𝓝 (g w)) :=
    (hC0.tendstoLocallyUniformlyOn (s := univ)).tendsto_at (mem_univ w)
  obtain ⟨hg1, hdR⟩ := ω.contDiff_and_tendstoLocallyUniformly_fderiv_rescale
    (u := fun n ↦ u (ψ n)) (c := fun n ↦ c (ψ n)) (ε := fun n ↦ ε (ψ n)) hU hz₀ hJ hKs hKt
    (fun n ↦ hu _) (fun n ↦ hsol _) hcψ hεψ (fun n ↦ (hε _).ne') hRψ
    (fun n w hw ↦ ⟨(hRw (φ₁ n) w hw).1, (hRw (φ₁ n) w hw).2.1⟩) hpt
  have hdpt (w : ℝ × ℝ) := (hdR.tendstoLocallyUniformlyOn (s := univ)).tendsto_at (mem_univ w)
  -- Eventually every point lies in the squares where the rescaled equation holds.
  have hevw (w : ℝ × ℝ) : ∀ᶠ n in atTop, ‖w‖ ≤ R (ψ n) := hRψ.eventually_ge_atTop _
  refine ⟨ψ, fun n ↦ c (ψ n), fun n ↦ ε (ψ n), g, hψ, fun n ↦ hε _, hcψ, hεψ, hg1,
    fun w ↦ hK.isClosed.mem_of_tendsto (hpt w)
      ((hevw w).mono fun n hn ↦ huK _ (hRw (φ₁ n) w hn).1), ?_, fun w ↦ ?_, fun w ↦ ?_, hC0,
    hdR, fun δ hδ ↦ ?_⟩
  · refine tendsto_nhds_unique ((continuous_norm.tendsto _).comp (hdpt 0)) ?_
    exact tendsto_const_nhds.congr fun n ↦ (hN _ (Nat.le_add_left N (φ₁ n))).1.1.symm
  · exact le_of_tendsto ((continuous_norm.tendsto _).comp (hdpt w))
      ((hevw w).mono fun n hn ↦ (hRw (φ₁ n) w hn).2.1)
  · -- The limit equation at `w`, for the structure frozen at `z₀`.
    have hmem : (z₀, g w) ∈ U ×ˢ (univ : Set V) := ⟨hz₀, mem_univ _⟩
    have hXc {K' : ℝ × ℝ → V → ℝ} (hK' : ContDiffOn ℝ 2 (uncurry K') (U ×ˢ univ)) :
        ContinuousAt (uncurry fun z ↦ ω.hamiltonianVectorField (K' z)) (z₀, g w) :=
      (ω.contDiffAt_hamiltonianVectorField_uncurry (n := 1)
        (hK'.contDiffAt ((hU.prod isOpen_univ).mem_nhds hmem))).continuousAt
    exact isJHolomorphicAt_of_hasFDerivAt (hg1.differentiable one_ne_zero w).hasFDerivAt
      (ω.isComplexLinearMap_of_tendsto_rescale (u := fun n ↦ u (ψ n)) hcψ hεψ (hpt w) (hdpt w)
        (hJ.continuousOn.continuousAt ((hU.prod isOpen_univ).mem_nhds hmem)) (hXc hKs) (hXc hKt)
        ((hevw w).mono fun n hn ↦ hsol _ _ (hRw (φ₁ n) w hn).1))
  · exact ω.lintegral_symplecticForm_le_liminf_of_tendsto_rescale (u := fun n ↦ u (ψ n)) hU hz₀
      (fun n ↦ hu1 _) (hKs.of_le (by norm_num)) (hKt.of_le (by norm_num)) hcψ hεψ hpt hdpt hδ

end TauCeti.SymplecticForm
