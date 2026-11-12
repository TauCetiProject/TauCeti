/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Equicontinuity
public import TauCeti.Analysis.Complex.Wirtinger.SecondDerivative
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Geometry.Symplectic.Complex.Module.Conjugacy

/-!
# Convergence of the derivatives of Floer solutions

In local coordinates `z = s + i t ∈ ℂ` on the domain and `x` on the target, the inhomogeneous
Cauchy–Riemann equation of Hamiltonian Floer theory reads

`∂ₜu - X(z, u) i = J(z, u) (∂ₛu - X(z, u) 1)`,

for a domain-dependent almost complex structure `J` and the Hamiltonian one-form `X`, as in
`TauCeti.Geometry.Symplectic.Floer.Compactness`. The compactness theorem there extracts from a
sequence of solutions of bounded energy a subsequence converging locally uniformly off finitely
many bubbling points, with derivatives bounded on compact subsets of the complement, and
`TauCeti.Geometry.Symplectic.Floer.WeakLimit` shows that the limit solves the equation almost
everywhere. This file upgrades such convergence to convergence of the derivatives. The target
coordinates range over an arbitrary finite-dimensional real normed space `F`, such as the model
space of a chart of the target manifold, and `J` is only assumed to square to `-1`.

Let `J` and `X` be `C¹` near `Ω × K`, for an open `Ω ⊆ ℂ` and a compact `K ⊆ F`, with `J² = -1` on
`Ω × K`.

* A family of smooth solutions on `Ω` with values in `K`, with derivatives bounded on each compact
  subset of `Ω` uniformly in the family, has equicontinuous derivatives on `Ω`
  (`TauCeti.Floer.equicontinuousOn_fderiv`).
* If a sequence `uₙ` of such solutions converges pointwise to `v`, then `v` is `C¹` on `Ω`, a
  subsequence of `Duₙ` converges to `Dv` locally uniformly on `Ω`, and `v` solves the equation at
  every point of `Ω` (`TauCeti.Floer.exists_strictMono_tendstoLocallyUniformlyOn_fderiv`).

Since `J² = -1`, the equation is `∂ₛu + J(z, u) ∂ₜu = X(z, u) 1 + J(z, u) X(z, u) i`. The interior
second-derivative estimates of `TauCeti.Analysis.Complex.Wirtinger.SecondDerivative` apply to such
an equation in complex coordinates in which `J` is uniformly close to multiplication by `i`. Near
`(z₀, y₀) ∈ Ω × K` these coordinates are obtained by a real-linear isomorphism `Φ` of `F` onto
`EuclideanSpace ℂ (Fin m)` with `Φ J(z₀, y₀) = i Φ`
(`ContinuousLinearMap.exists_continuousLinearEquiv_euclideanSpace_apply_eq_I_smul`): by
continuity, `Φ J(z, y) Φ⁻¹` stays close to `i` for `(z, y)` near `(z₀, y₀)`. A solution with
`u(z₀)` near `y₀` keeps its values near `y₀` on a disc around `z₀` whose radius depends only on
the derivative bound, so on that disc `Φ ∘ u` solves an equation of the required form. Covering
the compact set `K` by finitely many such neighbourhoods of points `y₀` splits any family of
solutions into finitely many subfamilies according to the value at `z₀`, each with
equicontinuous derivatives at `z₀`. The Arzelà–Ascoli theorem in `C¹`
(`TauCeti.exists_strictMono_tendstoLocallyUniformlyOn_fderiv`) then gives the convergent
subsequence, and the equation passes to the limit pointwise.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications **52**, 2012, Appendix B.4 (elliptic bootstrapping) and Section 8.1
  (inhomogeneous equations).
-/

public section

open Complex Filter Metric Set Topology
open scoped NNReal ContDiff

namespace TauCeti.Floer

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The Floer equation `∂ₜu - X(z, u) i = J(z, u)(∂ₛu - X(z, u) 1)` for `J² = -1` is the
equation `∂ₛu + J(z, u) ∂ₜu = X(z, u) 1 + J(z, u) X(z, u) i`. -/
private theorem fderiv_one_add_eq_of_fderiv_I_sub_eq {J : F →L[ℝ] F} {L X : ℂ →L[ℝ] F}
    (hJ : ∀ w, J (J w) = -w) (h : L I - X I = J (L 1 - X 1)) :
    L 1 + J (L I) = X 1 + J (X I) := by
  have h' := congrArg J h
  rw [map_sub, hJ] at h'
  rw [← sub_eq_zero] at h' ⊢
  rw [← h']
  abel

/-- The Floer equation at a point `y` passes to limits of derivatives and values: if
`Lₙ I - X(y, xₙ) I = J(y, xₙ)(Lₙ 1 - X(y, xₙ) 1)` with `Lₙ → L` and `xₙ → x`, and `J`, `X` are
continuous near `(y, x)`, then `L I - X(y, x) I = J(y, x)(L 1 - X(y, x) 1)`. -/
private theorem fderiv_I_sub_eq_of_tendsto {J : ℂ × F → F →L[ℝ] F} {X : ℂ × F → ℂ →L[ℝ] F}
    {W : Set (ℂ × F)} {y : ℂ} {L : ℕ → ℂ →L[ℝ] F} {L₀ : ℂ →L[ℝ] F} {x : ℕ → F} {x₀ : F}
    (hW : IsOpen W) (hJ : ContinuousOn J W) (hX : ContinuousOn X W) (hmem : (y, x₀) ∈ W)
    (hL : Tendsto L atTop (𝓝 L₀)) (hx : Tendsto x atTop (𝓝 x₀))
    (h : ∀ n, L n I - X (y, x n) I = J (y, x n) (L n 1 - X (y, x n) 1)) :
    L₀ I - X (y, x₀) I = J (y, x₀) (L₀ 1 - X (y, x₀) 1) := by
  -- The defect of the equation is continuous at `(L₀, x₀)` and vanishes along the sequence.
  set Ψ : (ℂ →L[ℝ] F) × F → F := fun p ↦ p.1 I - X (y, p.2) I - J (y, p.2) (p.1 1 - X (y, p.2) 1)
  have hX' : ContinuousAt (fun p : (ℂ →L[ℝ] F) × F ↦ X (y, p.2)) (L₀, x₀) :=
    (hX.continuousAt (hW.mem_nhds hmem)).comp_of_eq
      (continuousAt_const.prodMk continuousAt_snd) rfl
  have hJ' : ContinuousAt (fun p : (ℂ →L[ℝ] F) × F ↦ J (y, p.2)) (L₀, x₀) :=
    (hJ.continuousAt (hW.mem_nhds hmem)).comp_of_eq
      (continuousAt_const.prodMk continuousAt_snd) rfl
  have hΨ : ContinuousAt Ψ (L₀, x₀) :=
    ((continuousAt_fst.clm_apply continuousAt_const).sub (hX'.clm_apply continuousAt_const)).sub
      (hJ'.clm_apply ((continuousAt_fst.clm_apply continuousAt_const).sub
        (hX'.clm_apply continuousAt_const)))
  have hzero : Ψ (L₀, x₀) = 0 :=
    tendsto_nhds_unique (hΨ.tendsto.comp (hL.prodMk_nhds hx))
      (tendsto_const_nhds.congr fun n ↦ by simp only [Function.comp_apply, Ψ, h n, sub_self])
  simpa only [Ψ, sub_eq_zero] using hzero

/-- **Equicontinuity near the standard complex structure.** On a complex inner product space `G`
there is `δ > 0` with the following property. Let `J` and `h` be `C¹` on an open set
`W ⊆ ℂ × G` containing `U × K`, for an open `U ⊆ ℂ` and a compact `K ⊆ G`, with
`‖J(z, x) w - i w‖ ≤ δ ‖w‖` on `U × K`. Then every family of smooth solutions of
`∂ₛu + J(z, u) ∂ₜu = h(z, u)` on `U` with values in `K`, whose derivatives are bounded on each
compact subset of `U` uniformly in the family, has equicontinuous derivatives on `U`. -/
private theorem exists_pos_forall_equicontinuousOn_fderiv_comp_graph {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G] :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ ⦃ι : Type*⦄ ⦃J : ℂ × G → G →L[ℝ] G⦄ ⦃h : ℂ × G → G⦄ ⦃W : Set (ℂ × G)⦄
      ⦃U : Set ℂ⦄ ⦃K : Set G⦄, IsOpen W → ContDiffOn ℝ 1 J W → ContDiffOn ℝ 1 h W → IsOpen U →
      IsCompact K → U ×ˢ K ⊆ W → (∀ z ∈ U, ∀ x ∈ K, ∀ w, ‖J (z, x) w - I • w‖ ≤ δ * ‖w‖) →
      ∀ ⦃u : ι → ℂ → G⦄, (∀ i, ContDiffOn ℝ ∞ (u i) U) →
      (∀ i, ∀ y ∈ U, fderiv ℝ (u i) y 1 + J (y, u i y) (fderiv ℝ (u i) y I) = h (y, u i y)) →
      (∀ i, MapsTo (u i) U K) →
      (∀ C, IsCompact C → C ⊆ U → ∃ M, ∀ i, ∀ y ∈ C, ‖fderiv ℝ (u i) y‖ ≤ M) →
      EquicontinuousOn (fun i ↦ fderiv ℝ (u i)) U := by
  obtain ⟨δ, hδ0, hδ⟩ := exists_pos_forall_equicontinuousOn_fderiv (F := G)
  refine ⟨δ, hδ0, fun ι J h W U K hW hJ hh hU hK hUKW hJI u hu heq huK hbd ↦ ?_⟩
  have hmem : ∀ i, ∀ y ∈ U, (y, u i y) ∈ W := fun i y hy ↦ hUKW ⟨hy, huK i hy⟩
  have hdu : ∀ i, ∀ y ∈ U, DifferentiableAt ℝ (u i) y := fun i y hy ↦
    ((hu i).differentiableOn (by simp) y hy).differentiableAt (hU.mem_nhds hy)
  refine hδ (A := fun i z ↦ J (z, u i z)) (f := fun i z ↦ h (z, u i z)) hU hu
    (fun i y hy ↦ (((hJ.differentiableOn one_ne_zero).differentiableAt
      (hW.mem_nhds (hmem i y hy))).comp y
        (differentiableAt_id.prodMk (hdu i y hy))).differentiableWithinAt)
    (fun i z hz ↦ hJI z hz (u i z) (huK i hz)) (fun C hC hCU ↦ ?_) heq
  -- Along the solutions, the coefficients `J(z, uᵢ z)` and `h(z, uᵢ z)` have derivatives bounded
  -- on `C` by the chain rule.
  obtain ⟨M, hM⟩ := hbd C hC hCU
  have hCKW : C ×ˢ K ⊆ W := (prod_mono hCU subset_rfl).trans hUKW
  have hCK : ∀ i, MapsTo (u i) C K := fun i ↦ (huK i).mono_left hCU
  have hdC : ∀ i, ∀ y ∈ C, DifferentiableAt ℝ (u i) y := fun i y hy ↦ hdu i y (hCU hy)
  obtain ⟨BJ, hBJ⟩ := exists_bound_norm_fderiv_comp_graph hW hJ hC hK hCKW hCK hdC hM
  obtain ⟨Bh, hBh⟩ := exists_bound_norm_fderiv_comp_graph hW hh hC hK hCKW hCK hdC hM
  exact ⟨max (max BJ Bh) M, fun i y hy ↦ ⟨(hBJ i y hy).trans (by simp),
    (hBh i y hy).trans (by simp), (hM i y hy).trans (by simp)⟩⟩

/-- **Equicontinuity in adapted coordinates near one point.** Let `J` and `h` be `C¹` on an open
`W ⊆ ℂ × F` containing `(z₀, y₀)`, with `z₀` in the open set `Ω` and `J(z₀, y₀)² = -1`. There is
`η > 0` such that every family of smooth solutions of `∂ₛu + J(z, u) ∂ₜu = h(z, u)` on `Ω`, with
derivatives bounded on each compact subset of `Ω` uniformly in the family and with `u(z₀)` within
`η` of `y₀`, has derivatives equicontinuous at `z₀` within `Ω`. -/
private theorem exists_pos_forall_equicontinuousWithinAt_fderiv [FiniteDimensional ℝ F]
    {J : ℂ × F → F →L[ℝ] F} {h : ℂ × F → F} {W : Set (ℂ × F)} {Ω : Set ℂ} (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 1 J W) (hh : ContDiffOn ℝ 1 h W) (hΩ : IsOpen Ω) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    {y₀ : F} (hq₀ : (z₀, y₀) ∈ W) (hJ₀ : ∀ w, J (z₀, y₀) (J (z₀, y₀) w) = -w) :
    ∃ η > 0, ∀ ⦃ι : Type*⦄ ⦃u : ι → ℂ → F⦄, (∀ i, ContDiffOn ℝ ∞ (u i) Ω) →
      (∀ i, ∀ y ∈ Ω, fderiv ℝ (u i) y 1 + J (y, u i y) (fderiv ℝ (u i) y I) = h (y, u i y)) →
      (∀ C, IsCompact C → C ⊆ Ω → ∃ M, ∀ i, ∀ y ∈ C, ‖fderiv ℝ (u i) y‖ ≤ M) →
      (∀ i, dist (u i z₀) y₀ < η) → EquicontinuousWithinAt (fun i ↦ fderiv ℝ (u i)) Ω z₀ := by
  -- Complex coordinates `Φ` on `F` in which `J(z₀, y₀)` is multiplication by `i`.
  obtain ⟨m, Φ, hΦ⟩ :=
    (J (z₀, y₀)).exists_continuousLinearEquiv_euclideanSpace_apply_eq_I_smul hJ₀
  set G := EuclideanSpace ℂ (Fin m)
  obtain ⟨δ, hδ0, hδ⟩ := exists_pos_forall_equicontinuousOn_fderiv_comp_graph (G := G)
  -- The coefficients `J' = Φ J Φ⁻¹` and `h' = Φ h` in these coordinates.
  let e : ℂ × G → ℂ × F := fun q ↦ (q.1, Φ.symm q.2)
  have he : ContDiff ℝ 1 e := contDiff_fst.prodMk (Φ.symm.contDiff.comp contDiff_snd)
  let J' : ℂ × G → G →L[ℝ] G := fun q ↦ (Φ : F →L[ℝ] G) ∘L J (e q) ∘L (Φ.symm : G →L[ℝ] F)
  let h' : ℂ × G → G := fun q ↦ Φ (h (e q))
  have hW' : IsOpen (e ⁻¹' W) := hW.preimage he.continuous
  have hJ' : ContDiffOn ℝ 1 J' (e ⁻¹' W) :=
    contDiffOn_const.clm_comp ((hJ.comp he.contDiffOn (mapsTo_preimage e W)).clm_comp
      contDiffOn_const)
  have hh' : ContDiffOn ℝ 1 h' (e ⁻¹' W) :=
    Φ.contDiff.comp_contDiffOn (hh.comp he.contDiffOn (mapsTo_preimage e W))
  set q₀ : ℂ × G := (z₀, Φ y₀)
  have hq₀' : q₀ ∈ e ⁻¹' W := by simpa [e, q₀] using hq₀
  -- `J'` is multiplication by `i` at `q₀`, and within `δ` of it on a ball around `q₀`.
  obtain ⟨ε, hε, hεW⟩ : ∃ ε > 0, ball q₀ ε ⊆ e ⁻¹' W ∩ {q | dist (J' q) (J' q₀) < δ} :=
    Metric.mem_nhds_iff.1 (inter_mem (hW'.mem_nhds hq₀')
      ((hJ'.continuousOn.continuousAt (hW'.mem_nhds hq₀')).preimage_mem_nhds
        (ball_mem_nhds _ (by exact_mod_cast hδ0))))
  have hJ'I : ∀ q ∈ ball q₀ ε, ∀ w, ‖J' q w - I • w‖ ≤ δ * ‖w‖ := by
    intro q hq w
    have hq₀w : J' q₀ w = I • w := by simp [J', e, q₀, hΦ]
    have hdist : ‖J' q - J' q₀‖ ≤ δ := by
      have hq' : dist (J' q) (J' q₀) < δ := (hεW hq).2
      rw [dist_eq_norm] at hq'
      exact hq'.le
    rw [← hq₀w, ← sub_apply]
    exact ((J' q - J' q₀).le_opNorm w).trans (by gcongr)
  -- `a ε / (4 (a + 1)) ≤ ε / 4` for `a ≥ 0`.
  have hquarter : ∀ a : ℝ, 0 ≤ a → a * (ε / (4 * (a + 1))) ≤ ε / 4 := fun a ha ↦ by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  set N := ‖(Φ : F →L[ℝ] G)‖
  refine ⟨ε / (4 * (N + 1)), by positivity, fun ι u hu heq hbd hclose ↦ ?_⟩
  have hdu : ∀ i, ∀ y ∈ Ω, DifferentiableAt ℝ (u i) y := fun i y hy ↦
    ((hu i).differentiableOn (by simp) y hy).differentiableAt (hΩ.mem_nhds hy)
  -- A disc `ball z₀ r` on which every `Φ ∘ uᵢ` stays within `ε / 2` of `Φ y₀`: its radius only
  -- depends on a bound `M` for the derivatives near `z₀`, by the mean-value inequality.
  obtain ⟨r₀, hr₀, hr₀Ω⟩ := nhds_basis_closedBall.mem_iff.1 (hΩ.mem_nhds hz₀)
  obtain ⟨M, hM⟩ := hbd _ (isCompact_closedBall z₀ r₀) hr₀Ω
  set M' := max M 0
  set r := min r₀ (min ε (ε / (4 * (N * M' + 1))))
  have hr : 0 < r := lt_min hr₀ (lt_min hε (by positivity))
  have hUΩ : ball z₀ r ⊆ Ω :=
    ball_subset_closedBall.trans ((closedBall_subset_closedBall (min_le_left _ _)).trans hr₀Ω)
  have hval : ∀ i, MapsTo (Φ ∘ u i) (ball z₀ r) (closedBall (Φ y₀) (ε / 2)) := by
    intro i z hz
    have hzr : dist z z₀ ≤ ε / (4 * (N * M' + 1)) :=
      (mem_ball.1 hz).le.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hz' : z ∈ closedBall z₀ r₀ :=
      ball_subset_closedBall (ball_subset_ball (min_le_left _ _) hz)
    have hmv : dist (u i z) (u i z₀) ≤ M' * dist z z₀ := by
      simpa [dist_eq_norm] using (convex_closedBall z₀ r₀).norm_image_sub_le_of_norm_fderiv_le
        (fun x hx ↦ hdu i x (hr₀Ω hx)) (fun x hx ↦ (hM i x hx).trans (le_max_left _ _))
        (mem_closedBall_self hr₀.le) hz'
    have h₁ : dist (Φ (u i z)) (Φ (u i z₀)) ≤ ε / 4 :=
      ((Φ : F →L[ℝ] G).dist_le_opNorm _ _).trans <|
        (mul_le_mul_of_nonneg_left hmv (norm_nonneg _)).trans <| by
          rw [← mul_assoc]
          exact (mul_le_mul_of_nonneg_left hzr (by positivity)).trans
            (hquarter _ (by positivity))
    have h₂ : dist (Φ (u i z₀)) (Φ y₀) ≤ ε / 4 :=
      ((Φ : F →L[ℝ] G).dist_le_opNorm _ _).trans <|
        (mul_le_mul_of_nonneg_left (hclose i).le (norm_nonneg _)).trans
          (hquarter _ (norm_nonneg _))
    rw [mem_closedBall, Function.comp_apply]
    linarith [dist_triangle (Φ (u i z)) (Φ (u i z₀)) (Φ y₀)]
  have hball : ball z₀ r ×ˢ closedBall (Φ y₀) (ε / 2) ⊆ ball q₀ ε := fun q hq ↦ by
    rw [mem_ball, Prod.dist_eq]
    exact max_lt ((mem_ball.1 hq.1).trans_le ((min_le_right _ _).trans (min_le_left _ _)))
      ((mem_closedBall.1 hq.2).trans_lt (by linarith))
  -- On the disc, `Φ ∘ uᵢ` solves `∂ₛw + J'(z, w) ∂ₜw = h'(z, w)` with `J'` close to `i`.
  have hequi : EquicontinuousOn (fun i ↦ fderiv ℝ (Φ ∘ u i)) (ball z₀ r) := by
    refine hδ hW' hJ' hh' isOpen_ball (isCompact_closedBall _ _)
      (hball.trans fun q hq ↦ (hεW hq).1) (fun z hz x hx ↦ hJ'I _ (hball ⟨hz, hx⟩))
      (fun i ↦ Φ.contDiff.comp_contDiffOn ((hu i).mono hUΩ)) (fun i y hy ↦ ?_) hval
      (fun C hC hCU ↦ ?_)
    · simp only [Φ.comp_fderiv, J', h', e, Function.comp_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply, ← map_add,
        heq i y (hUΩ hy)]
    · obtain ⟨MC, hMC⟩ := hbd C hC (hCU.trans hUΩ)
      exact ⟨N * MC, fun i y hy ↦ by
        rw [Φ.comp_fderiv]
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (hMC i y hy) (norm_nonneg _))⟩
  rw [Φ.equicontinuousOn_fderiv_comp_iff] at hequi
  have hU : EquicontinuousAt (fun i ↦ fderiv ℝ (u i)) z₀ := fun V hV ↦ by
    simpa [nhdsWithin_eq_nhds.2 (ball_mem_nhds z₀ hr)] using hequi z₀ (mem_ball_self hr) V hV
  exact hU.equicontinuousWithinAt Ω

/-- **The derivatives of Floer solutions are equicontinuous.** Let `J` and `X` be `C¹` on an open
set `W ⊆ ℂ × F` containing `Ω × K`, for an open `Ω ⊆ ℂ` and a compact `K ⊆ F`, with
`J(z, x)² = -1` on `Ω × K`. Let `uᵢ` be smooth solutions of
`∂ₜu - X(z, u) i = J(z, u)(∂ₛu - X(z, u) 1)` on `Ω` with values in `K`, whose derivatives are
bounded on each compact subset of `Ω` uniformly in `i`. Then the derivatives `Duᵢ` are
equicontinuous on `Ω`. -/
theorem equicontinuousOn_fderiv [FiniteDimensional ℝ F] {ι : Type*} {J : ℂ × F → F →L[ℝ] F}
    {X : ℂ × F → ℂ →L[ℝ] F} {W : Set (ℂ × F)} {Ω : Set ℂ} {K : Set F} (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 1 J W) (hX : ContDiffOn ℝ 1 X W) (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hΩKW : Ω ×ˢ K ⊆ W) (hJsq : ∀ z ∈ Ω, ∀ x ∈ K, ∀ w, J (z, x) (J (z, x) w) = -w)
    {u : ι → ℂ → F} (hu : ∀ i, ContDiffOn ℝ ∞ (u i) Ω)
    (hCR : ∀ i, ∀ y ∈ Ω, fderiv ℝ (u i) y I - X (y, u i y) I =
      J (y, u i y) (fderiv ℝ (u i) y 1 - X (y, u i y) 1))
    (huK : ∀ i, MapsTo (u i) Ω K)
    (hbd : ∀ C, IsCompact C → C ⊆ Ω → ∃ M, ∀ i, ∀ y ∈ C, ‖fderiv ℝ (u i) y‖ ≤ M) :
    EquicontinuousOn (fun i ↦ fderiv ℝ (u i)) Ω := by
  intro z₀ hz₀
  -- The right-hand side `h(z, x) = X(z, x) 1 + J(z, x) X(z, x) i` of the equation
  -- `∂ₛu + J(z, u) ∂ₜu = h(z, u)`.
  set h : ℂ × F → F := fun q ↦ X q 1 + J q (X q I)
  have hh : ContDiffOn ℝ 1 h W :=
    (hX.clm_apply contDiffOn_const).add (hJ.clm_apply (hX.clm_apply contDiffOn_const))
  have heq : ∀ i, ∀ y ∈ Ω, fderiv ℝ (u i) y 1 + J (y, u i y) (fderiv ℝ (u i) y I) = h (y, u i y) :=
    fun i y hy ↦ fderiv_one_add_eq_of_fderiv_I_sub_eq (hJsq y hy _ (huK i hy)) (hCR i y hy)
  -- Cover `K` by finitely many balls around points `y₀` where the local statement applies.
  choose! η hη hloc using fun y (hy : y ∈ K) ↦ exists_pos_forall_equicontinuousWithinAt_fderiv
    hW hJ hh hΩ hz₀ (hΩKW ⟨hz₀, hy⟩) (hJsq z₀ hz₀ y hy)
  obtain ⟨t, htK, htfin, hKt⟩ := hK.elim_finite_subcover_image (c := fun y ↦ ball y (η y))
    (fun _ _ ↦ isOpen_ball) fun y hy ↦ mem_biUnion hy (mem_ball_self (hη y hy))
  intro V hV
  -- Each subfamily with `uᵢ(z₀)` in one of the balls has equicontinuous derivatives at `z₀`.
  have hfin : ∀ᶠ z in 𝓝[Ω] z₀, ∀ y ∈ t, ∀ i, u i z₀ ∈ ball y (η y) →
      (fderiv ℝ (u i) z₀, fderiv ℝ (u i) z) ∈ V := by
    refine (eventually_all_finite htfin).2 fun y hy ↦ ?_
    have hsub := hloc y (htK hy) (ι := {i // u i z₀ ∈ ball y (η y)}) (u := fun i ↦ u i)
      (fun i ↦ hu i) (fun i ↦ heq i) (fun C hC hCΩ ↦ (hbd C hC hCΩ).imp fun M hM i ↦ hM i)
      (fun i ↦ mem_ball.1 i.2) V hV
    filter_upwards [hsub] with z hz i hi using hz ⟨i, hi⟩
  filter_upwards [hfin] with z hz i
  obtain ⟨y, hy, hiy⟩ := mem_iUnion₂.1 (hKt (huK i hz₀))
  exact hz y hy i hiy

/-- **The derivatives of Floer solutions converge.** Let `J` and `X` be `C¹` on an open set
`W ⊆ ℂ × F` containing `Ω × K`, for an open `Ω ⊆ ℂ` and a compact `K ⊆ F`, with `J(z, x)² = -1`
on `Ω × K`. Let `uₙ` be smooth solutions of `∂ₜu - X(z, u) i = J(z, u)(∂ₛu - X(z, u) 1)` on `Ω`
with values in `K`, whose derivatives are bounded on each compact subset of `Ω` uniformly in `n`,
and which converge pointwise on `Ω` to `v`. Then `v` is `C¹` on `Ω`, along a subsequence
`Duₙ → Dv` locally uniformly on `Ω`, and `v` solves the equation on `Ω`. -/
theorem exists_strictMono_tendstoLocallyUniformlyOn_fderiv [FiniteDimensional ℝ F]
    {J : ℂ × F → F →L[ℝ] F} {X : ℂ × F → ℂ →L[ℝ] F} {W : Set (ℂ × F)} {Ω : Set ℂ} {K : Set F}
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 1 J W) (hX : ContDiffOn ℝ 1 X W) (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hΩKW : Ω ×ˢ K ⊆ W)
    (hJsq : ∀ z ∈ Ω, ∀ x ∈ K, ∀ w, J (z, x) (J (z, x) w) = -w) {u : ℕ → ℂ → F} {v : ℂ → F}
    (hu : ∀ n, ContDiffOn ℝ ∞ (u n) Ω)
    (hCR : ∀ n, ∀ y ∈ Ω, fderiv ℝ (u n) y I - X (y, u n y) I =
      J (y, u n y) (fderiv ℝ (u n) y 1 - X (y, u n y) 1))
    (huK : ∀ n, MapsTo (u n) Ω K)
    (hbd : ∀ C, IsCompact C → C ⊆ Ω → ∃ M, ∀ n, ∀ y ∈ C, ‖fderiv ℝ (u n) y‖ ≤ M)
    (hlim : ∀ y ∈ Ω, Tendsto (fun n ↦ u n y) atTop (𝓝 (v y))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ContDiffOn ℝ 1 v Ω ∧
      TendstoLocallyUniformlyOn (fun n ↦ fderiv ℝ (u (φ n))) (fderiv ℝ v) atTop Ω ∧
      ∀ y ∈ Ω, fderiv ℝ v y I - X (y, v y) I = J (y, v y) (fderiv ℝ v y 1 - X (y, v y) 1) := by
  have hdu : ∀ n, ∀ y ∈ Ω, DifferentiableAt ℝ (u n) y := fun n y hy ↦
    ((hu n).differentiableOn (by simp) y hy).differentiableAt (hΩ.mem_nhds hy)
  obtain ⟨φ, hφ, hv, hconv⟩ := TauCeti.exists_strictMono_tendstoLocallyUniformlyOn_fderiv hΩ
    (fun n y hy ↦ (hdu n y hy).differentiableWithinAt)
    (equicontinuousOn_fderiv hW hJ hX hΩ hK hΩKW hJsq hu hCR huK hbd)
    (fun y hy ↦ (hbd {y} isCompact_singleton (singleton_subset_iff.2 hy)).imp
      fun M hM n ↦ hM n y rfl) hlim
  refine ⟨φ, hφ, hv, hconv, fun y hy ↦ ?_⟩
  -- Pass to the limit in the equation at `y`.
  have hvK : v y ∈ K := hK.isClosed.mem_of_tendsto (hlim y hy)
    (Eventually.of_forall fun n ↦ huK n hy)
  exact fderiv_I_sub_eq_of_tendsto hW hJ.continuousOn hX.continuousOn (hΩKW ⟨hy, hvK⟩)
    (hconv.tendsto_at hy) ((hlim y hy).comp hφ.tendsto_atTop) fun n ↦ hCR (φ n) y hy

end TauCeti.Floer
