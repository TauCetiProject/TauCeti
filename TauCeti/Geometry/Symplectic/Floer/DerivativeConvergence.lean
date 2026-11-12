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
import TauCeti.Topology.UniformSpace.Equicontinuity

/-!
# Convergence of the derivatives of Floer solutions

In local coordinates `z = s + i t ∈ ℂ` on the domain and `x` in a finite-dimensional real normed
space `V` on the target, the inhomogeneous Cauchy–Riemann equation of Hamiltonian Floer theory
reads

`∂ₜu - X(z, u) i = J(z, u) (∂ₛu - X(z, u) 1)`,

for a domain-dependent almost complex structure `J` and the Hamiltonian one-form `X`, as in
`TauCeti.Geometry.Symplectic.Floer.Compactness`. The compactness theorem there extracts from a
sequence of solutions of bounded energy a subsequence converging locally uniformly off finitely
many bubbling points, with derivatives bounded on compact subsets of the complement, and
`TauCeti.Geometry.Symplectic.Floer.WeakLimit` shows that the limit solves the equation almost
everywhere. This file upgrades such convergence to convergence of the derivatives.

Let `J` and `X` be `C¹` near `Ω × K`, for an open `Ω ⊆ ℂ` and a closed `K ⊆ V`, with `J² = -1` on
`Ω × K`. Let `uₙ` be smooth solutions on `Ω` with values in `K`, with derivatives bounded on each
compact subset of `Ω` uniformly in `n`, converging pointwise to `v`. Then `v` is `C¹` on `Ω`, a
subsequence of `Duₙ` converges to `Dv` locally uniformly on `Ω`, and `v` solves the equation at
every point of `Ω` (`TauCeti.Floer.exists_strictMono_tendstoLocallyUniformlyOn_fderiv_of_floer`).

Since `J² = -1`, the equation is `∂ₛu + J(z, u) ∂ₜu = X(z, u) 1 + J(z, u) X(z, u) i`. The
interior second-derivative estimates of `TauCeti.Analysis.Complex.Wirtinger.SecondDerivative` apply
to this equation on a complex inner product space when the structure is uniformly close to
multiplication by `i`. To reach that form near a point `y ∈ Ω`, choose a real-linear frame
`Φ : ℂᵐ → V` in which `J(y, v y)` is multiplication by `i`
(`ContinuousLinearMap.exists_continuousLinearEquiv_euclideanSpace_comp_eq_comp_I_smul`). By
continuity, `Φ⁻¹ J(z, x) Φ` stays close to `i` for `(z, x)` near `(y, v y)`, and from some index on
the solutions stay near `v y` on a small disc about `y`. There the coefficients of the equation for
`Φ⁻¹ ∘ uₙ` have derivatives bounded by the chain rule, so the derivatives of the tail of the
sequence are equicontinuous at `y`; the remaining finitely many are continuous, so the whole
sequence of derivatives is equicontinuous on `Ω` (`equicontinuousAt_of_equicontinuousAt_add`). The
Arzelà–Ascoli theorem in `C¹` (`TauCeti.exists_strictMono_tendstoLocallyUniformlyOn_fderiv`) gives
the convergent subsequence, and the equation passes to the limit pointwise.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications **52**, 2012, Appendix B.4 (elliptic bootstrapping) and Section 8.1
  (inhomogeneous equations).
-/

public section

open Complex Filter Metric Set Topology
open scoped NNReal ContDiff

namespace TauCeti.Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The Floer equation `∂ₜu - X(z, u) i = J(z, u)(∂ₛu - X(z, u) 1)` for `J² = -1` is the
equation `∂ₛu + J(z, u) ∂ₜu = X(z, u) 1 + J(z, u) X(z, u) i`. -/
private theorem fderiv_one_add_eq_of_fderiv_I_sub_eq {J : V →L[ℝ] V} {L X : ℂ →L[ℝ] V}
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
private theorem fderiv_I_sub_eq_of_tendsto {J : ℂ × V → V →L[ℝ] V} {X : ℂ × V → ℂ →L[ℝ] V}
    {W : Set (ℂ × V)} {y : ℂ} {L : ℕ → ℂ →L[ℝ] V} {L₀ : ℂ →L[ℝ] V} {x : ℕ → V} {x₀ : V}
    (hW : IsOpen W) (hJ : ContinuousOn J W) (hX : ContinuousOn X W) (hmem : (y, x₀) ∈ W)
    (hL : Tendsto L atTop (𝓝 L₀)) (hx : Tendsto x atTop (𝓝 x₀))
    (h : ∀ n, L n I - X (y, x n) I = J (y, x n) (L n 1 - X (y, x n) 1)) :
    L₀ I - X (y, x₀) I = J (y, x₀) (L₀ 1 - X (y, x₀) 1) := by
  -- The defect of the equation is continuous at `(L₀, x₀)` and vanishes along the sequence.
  set Ψ : (ℂ →L[ℝ] V) × V → V := fun p ↦ p.1 I - X (y, p.2) I - J (y, p.2) (p.1 1 - X (y, p.2) 1)
  have hX' : ContinuousAt (fun p : (ℂ →L[ℝ] V) × V ↦ X (y, p.2)) (L₀, x₀) :=
    (hX.continuousAt (hW.mem_nhds hmem)).comp_of_eq
      (continuousAt_const.prodMk continuousAt_snd) rfl
  have hJ' : ContinuousAt (fun p : (ℂ →L[ℝ] V) × V ↦ J (y, p.2)) (L₀, x₀) :=
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

variable [FiniteDimensional ℝ V]

/-- **Local equicontinuity of the derivatives.** Under the hypotheses of
`TauCeti.Floer.exists_strictMono_tendstoLocallyUniformlyOn_fderiv_of_floer`, the derivatives
`Duₙ` are equicontinuous at every point `y` of `Ω`. In a real-linear frame `Φ : ℂᵐ → V` in which
`J(y, v y)` is multiplication by `i`, the structure `Φ⁻¹ J(z, x) Φ` is close to `i` for `(z, x)`
near `(y, v y)`. From some index on, the solutions stay near `v y` on a small disc about `y`, where
the interior estimates apply to `Φ⁻¹ ∘ uₙ`. -/
private theorem equicontinuousAt_fderiv_of_floer {J : ℂ × V → V →L[ℝ] V}
    {X : ℂ × V → ℂ →L[ℝ] V} {W : Set (ℂ × V)} {Ω : Set ℂ} {K : Set V} (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 1 J W) (hX : ContDiffOn ℝ 1 X W) (hΩ : IsOpen Ω) (hK : IsClosed K)
    (hΩKW : Ω ×ˢ K ⊆ W) (hJsq : ∀ z ∈ Ω, ∀ x ∈ K, ∀ w, J (z, x) (J (z, x) w) = -w)
    {u : ℕ → ℂ → V} {v : ℂ → V} (hu : ∀ n, ContDiffOn ℝ ∞ (u n) Ω)
    (hCR : ∀ n, ∀ y ∈ Ω, fderiv ℝ (u n) y I - X (y, u n y) I =
      J (y, u n y) (fderiv ℝ (u n) y 1 - X (y, u n y) 1))
    (huK : ∀ n, MapsTo (u n) Ω K)
    (hbd : ∀ C, IsCompact C → C ⊆ Ω → ∃ M, ∀ n, ∀ y ∈ C, ‖fderiv ℝ (u n) y‖ ≤ M)
    (hlim : ∀ y ∈ Ω, Tendsto (fun n ↦ u n y) atTop (𝓝 (v y))) {y : ℂ} (hy : y ∈ Ω) :
    EquicontinuousAt (fun n ↦ fderiv ℝ (u n)) y := by
  have hvK : v y ∈ K := hK.mem_of_tendsto (hlim y hy) (Eventually.of_forall fun n ↦ huK n hy)
  have hyW : (y, v y) ∈ W := hΩKW ⟨hy, hvK⟩
  have hmem : ∀ n, ∀ z ∈ Ω, (z, u n z) ∈ W := fun n z hz ↦ hΩKW ⟨hz, huK n hz⟩
  have hdu : ∀ n, ∀ z ∈ Ω, DifferentiableAt ℝ (u n) z := fun n z hz ↦
    ((hu n).differentiableOn (by simp) z hz).differentiableAt (hΩ.mem_nhds hz)
  -- A frame `Φ : ℂᵐ → V` in which `J (y, v y)` is multiplication by `i`, and the conjugation
  -- `C A = Φ⁻¹ A Φ` it induces on endomorphisms.
  obtain ⟨m, Φ, hΦ⟩ :=
    (J (y, v y)).exists_continuousLinearEquiv_euclideanSpace_comp_eq_comp_I_smul
      (ContinuousLinearMap.ext fun w ↦ by simpa using hJsq y hy _ hvK w)
  let C : (V →L[ℝ] V) ≃L[ℝ] (EuclideanSpace ℂ (Fin m) →L[ℝ] EuclideanSpace ℂ (Fin m)) :=
    Φ.symm.arrowCongr Φ.symm
  have hC (A : V →L[ℝ] V) (w : EuclideanSpace ℂ (Fin m)) : C A w = Φ.symm (A (Φ w)) := by
    simp [C]
  have hCy (w : EuclideanSpace ℂ (Fin m)) : C (J (y, v y)) w = I • w := by
    rw [hC, show J (y, v y) (Φ w) = Φ (I • w) by simpa using congr($hΦ w)]
    simp
  obtain ⟨δ, hδ0, hδ⟩ :=
    exists_pos_forall_equicontinuousOn_fderiv (F := EuclideanSpace ℂ (Fin m)) (ι := ℕ)
  -- A ball of radius `ε` about `(y, v y)`, inside `W`, on which `C (J q)` is `δ`-close to `i`.
  have hJy : ContinuousAt (fun q ↦ C (J q)) (y, v y) :=
    C.continuous.continuousAt.comp (hJ.continuousOn.continuousAt (hW.mem_nhds hyW))
  obtain ⟨ε, hε, hεW⟩ := Metric.eventually_nhds_iff.1
    ((hJy.eventually_mem (ball_mem_nhds _ (NNReal.coe_pos.2 hδ0))).and (hW.eventually_mem hyW))
  have hclose : ∀ z x, dist (z, x) (y, v y) < ε →
      ∀ w, ‖C (J (z, x)) w - I • w‖ ≤ δ * ‖w‖ := by
    intro z x hzx w
    rw [← hCy w, ← sub_apply]
    exact ((C (J (z, x)) - C (J (y, v y))).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (mem_ball_iff_norm.1 (hεW hzx).1).le (norm_nonneg w))
  -- A disc of radius `r` about `y` on which, from the index `N` on, the solutions stay within
  -- `ε / 2` of `v y`.
  obtain ⟨r₀, hr₀, hr₀Ω⟩ := Metric.isOpen_iff.1 hΩ y hy
  have hsΩ : closedBall y (r₀ / 2) ⊆ Ω := (closedBall_subset_ball (by linarith)).trans hr₀Ω
  obtain ⟨M, hM⟩ := hbd _ (isCompact_closedBall y (r₀ / 2)) hsΩ
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 y (mem_closedBall_self (by linarith)))
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hlim y hy) (ε / 4) (by positivity)
  set r := min (r₀ / 2) (min (ε / 2) (ε / (4 * (M + 1))))
  have hr : 0 < r := lt_min (by linarith) (lt_min (by linarith) (by positivity))
  have hrΩ : ball y r ⊆ Ω :=
    (ball_subset_ball (min_le_left _ _)).trans (ball_subset_closedBall.trans hsΩ)
  have hnear : ∀ n, N ≤ n → ∀ z ∈ ball y r, u n z ∈ closedBall (v y) (ε / 2) := by
    intro n hn z hz
    have hzs : z ∈ closedBall y (r₀ / 2) :=
      ball_subset_closedBall (ball_subset_ball (min_le_left _ _) hz)
    have h₁ : ‖u n z - u n y‖ ≤ M * ‖z - y‖ :=
      (convex_closedBall y (r₀ / 2)).norm_image_sub_le_of_norm_fderiv_le
        (fun x hx ↦ hdu n x (hsΩ hx)) (fun x hx ↦ hM n x hx)
        (mem_closedBall_self (by linarith)) hzs
    have hzy : ‖z - y‖ ≤ ε / (4 * (M + 1)) :=
      (mem_ball_iff_norm.1 hz).le.trans ((min_le_right _ _).trans (min_le_right _ _))
    have h₂ : M * ‖z - y‖ ≤ ε / 4 := by
      calc M * ‖z - y‖ ≤ M * (ε / (4 * (M + 1))) := by gcongr
        _ ≤ ε / 4 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
    rw [mem_closedBall, dist_eq_norm]
    have h₃ := hN n hn
    rw [dist_eq_norm] at h₃
    linarith [norm_sub_le_norm_sub_add_norm_sub (u n z) (u n y) (v y)]
  have hwin : ∀ z ∈ ball y r, ∀ x ∈ closedBall (v y) (ε / 2), dist (z, x) (y, v y) < ε := by
    intro z hz x hx
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨(mem_ball.1 hz).trans_le ((min_le_right _ _).trans (min_le_left _ _)) |>.trans
      (by linarith), (mem_closedBall.1 hx).trans_lt (by linarith)⟩
  -- On the disc, the tail of the solutions read in the frame `Φ` solves an equation whose
  -- complex structure is `δ`-close to `i`.
  set h : ℂ × V → V := fun q ↦ X q 1 + J q (X q I)
  have hh : ContDiffOn ℝ 1 h W :=
    (hX.clm_apply contDiffOn_const).add (hJ.clm_apply (hX.clm_apply contDiffOn_const))
  have hequi : EquicontinuousOn (fun n ↦ fderiv ℝ (Φ.symm ∘ u (n + N))) (ball y r) := by
    refine hδ (Ω := ball y r) (u := fun n ↦ Φ.symm ∘ u (n + N))
      (f := fun n ↦ Φ.symm ∘ fun z ↦ h (z, u (n + N) z))
      (A := fun n ↦ C ∘ fun z ↦ J (z, u (n + N) z)) isOpen_ball
      (fun n ↦ Φ.symm.contDiff.comp_contDiffOn ((hu _).mono hrΩ))
      (fun n z hz ↦ (C.differentiableAt.comp z
        (((hJ.differentiableOn one_ne_zero).differentiableAt
          (hW.mem_nhds (hmem _ z (hrΩ hz)))).comp z
            (differentiableAt_id.prodMk (hdu _ z (hrΩ hz))))).differentiableWithinAt)
      (fun n z hz w ↦ hclose z _ (hwin z hz _ (hnear _ (Nat.le_add_left N n) z hz)) w)
      (fun C' hC' hC'r ↦ ?_) (fun n z hz ↦ ?_)
    · -- Uniform bounds on a compact `C' ⊆ ball y r`, through the bounds along the graphs.
      have hC'Ω : C' ⊆ Ω := hC'r.trans hrΩ
      have hC'W : C' ×ˢ closedBall (v y) (ε / 2) ⊆ W := fun q hq ↦
        (hεW (hwin q.1 (hC'r hq.1) q.2 hq.2)).2
      have hmaps : ∀ n, MapsTo (u (n + N)) C' (closedBall (v y) (ε / 2)) := fun n z hz ↦
        hnear _ (Nat.le_add_left N n) z (hC'r hz)
      have hdC : ∀ n, ∀ z ∈ C', DifferentiableAt ℝ (u (n + N)) z := fun n z hz ↦
        hdu _ z (hC'Ω hz)
      have hMC : ∀ n, ∀ z ∈ C', ‖fderiv ℝ (u (n + N)) z‖ ≤ M := fun n z hz ↦
        hM _ z (ball_subset_closedBall (ball_subset_ball (min_le_left _ _) (hC'r hz)))
      obtain ⟨BJ, hBJ⟩ := exists_bound_norm_fderiv_comp_graph (u := fun n ↦ u (n + N)) hW hJ hC'
        (isCompact_closedBall (v y) (ε / 2)) hC'W hmaps hdC hMC
      obtain ⟨Bh, hBh⟩ := exists_bound_norm_fderiv_comp_graph (u := fun n ↦ u (n + N)) hW hh hC'
        (isCompact_closedBall (v y) (ε / 2)) hC'W hmaps hdC hMC
      refine ⟨max (‖(C : (V →L[ℝ] V) →L[ℝ]
          EuclideanSpace ℂ (Fin m) →L[ℝ] EuclideanSpace ℂ (Fin m))‖ * BJ)
        (max (‖(Φ.symm : V →L[ℝ] EuclideanSpace ℂ (Fin m))‖ * Bh)
          (‖(Φ.symm : V →L[ℝ] EuclideanSpace ℂ (Fin m))‖ * M)), fun n z hz ↦ ⟨?_, ?_, ?_⟩⟩
      · rw [C.comp_fderiv]
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          ((mul_le_mul_of_nonneg_left (hBJ n z hz) (norm_nonneg _)).trans (le_max_left _ _))
      · rw [Φ.symm.comp_fderiv]
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          ((mul_le_mul_of_nonneg_left (hBh n z hz) (norm_nonneg _)).trans
            ((le_max_left _ _).trans (le_max_right _ _)))
      · rw [Φ.symm.comp_fderiv]
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          ((mul_le_mul_of_nonneg_left (hMC n z hz) (norm_nonneg _)).trans
            ((le_max_right _ _).trans (le_max_right _ _)))
    · -- The equation in the frame `Φ`.
      have hz' := hrΩ hz
      simp only [Φ.symm.comp_fderiv, Function.comp_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe, hC, ContinuousLinearEquiv.apply_symm_apply, ← map_add]
      exact congrArg Φ.symm (fderiv_one_add_eq_of_fderiv_I_sub_eq
        (hJsq z hz' _ (huK _ hz')) (hCR _ z hz'))
  -- Back in `V`, the tail of the derivatives is equicontinuous at `y`, hence so is the sequence.
  have hat : EquicontinuousAt (fun n ↦ fderiv ℝ (Φ.symm ∘ u (n + N))) y := by
    have h' := hequi y (mem_ball_self hr)
    rwa [EquicontinuousWithinAt, nhdsWithin_eq_nhds.2 (ball_mem_nhds y hr)] at h'
  let P : (ℂ →L[ℝ] EuclideanSpace ℂ (Fin m)) ≃L[ℝ] (ℂ →L[ℝ] V) :=
    (ContinuousLinearEquiv.refl ℝ ℂ).arrowCongr Φ
  have htail : EquicontinuousAt (fun n ↦ fderiv ℝ (u (n + N))) y := by
    have hfun : (fun n ↦ fderiv ℝ (u (n + N))) =
        (P ∘ ·) ∘ fun n ↦ fderiv ℝ (Φ.symm ∘ u (n + N)) := by
      funext n z
      refine ContinuousLinearMap.ext fun w ↦ ?_
      simp [P, Φ.symm.comp_fderiv]
    rw [hfun]
    exact P.isUniformEmbedding.isUniformInducing.equicontinuousAt_iff.1 hat
  exact equicontinuousAt_of_equicontinuousAt_add N htail fun n _ ↦
    ((hu n).continuousOn_fderiv_of_isOpen hΩ (by simp)).continuousAt (hΩ.mem_nhds hy)

/-- **The derivatives of Floer solutions converge.** Let `J` and `X` be `C¹` on an open set
`W ⊆ ℂ × V` containing `Ω × K`, for an open `Ω ⊆ ℂ` and a closed `K ⊆ V`, with `J(z, x)² = -1`
on `Ω × K`. Let `uₙ` be smooth solutions of `∂ₜu - X(z, u) i = J(z, u)(∂ₛu - X(z, u) 1)` on `Ω`
with values in `K`, whose derivatives are bounded on each compact subset of `Ω` uniformly in `n`,
and which converge pointwise on `Ω` to `v`. Then `v` is `C¹` on `Ω`, along a subsequence
`Duₙ → Dv` locally uniformly on `Ω`, and `v` solves the equation on `Ω`. -/
theorem exists_strictMono_tendstoLocallyUniformlyOn_fderiv_of_floer {J : ℂ × V → V →L[ℝ] V}
    {X : ℂ × V → ℂ →L[ℝ] V} {W : Set (ℂ × V)} {Ω : Set ℂ} {K : Set V} (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 1 J W) (hX : ContDiffOn ℝ 1 X W) (hΩ : IsOpen Ω) (hK : IsClosed K)
    (hΩKW : Ω ×ˢ K ⊆ W) (hJsq : ∀ z ∈ Ω, ∀ x ∈ K, ∀ w, J (z, x) (J (z, x) w) = -w)
    {u : ℕ → ℂ → V} {v : ℂ → V} (hu : ∀ n, ContDiffOn ℝ ∞ (u n) Ω)
    (hCR : ∀ n, ∀ y ∈ Ω, fderiv ℝ (u n) y I - X (y, u n y) I =
      J (y, u n y) (fderiv ℝ (u n) y 1 - X (y, u n y) 1))
    (huK : ∀ n, MapsTo (u n) Ω K)
    (hbd : ∀ C, IsCompact C → C ⊆ Ω → ∃ M, ∀ n, ∀ y ∈ C, ‖fderiv ℝ (u n) y‖ ≤ M)
    (hlim : ∀ y ∈ Ω, Tendsto (fun n ↦ u n y) atTop (𝓝 (v y))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ContDiffOn ℝ 1 v Ω ∧
      TendstoLocallyUniformlyOn (fun n ↦ fderiv ℝ (u (φ n))) (fderiv ℝ v) atTop Ω ∧
      ∀ y ∈ Ω, fderiv ℝ v y I - X (y, v y) I = J (y, v y) (fderiv ℝ v y 1 - X (y, v y) 1) := by
  have hequi : EquicontinuousOn (fun n ↦ fderiv ℝ (u n)) Ω := fun y hy ↦
    (equicontinuousAt_fderiv_of_floer hW hJ hX hΩ hK hΩKW hJsq hu hCR huK hbd hlim
      hy).equicontinuousWithinAt Ω
  obtain ⟨φ, hφ, hv, hconv⟩ := exists_strictMono_tendstoLocallyUniformlyOn_fderiv hΩ
    (fun n ↦ (hu n).differentiableOn (by simp)) hequi
    (fun y hy ↦ (hbd {y} isCompact_singleton (singleton_subset_iff.2 hy)).imp
      fun M hM n ↦ hM n y rfl) hlim
  refine ⟨φ, hφ, hv, hconv, fun y hy ↦ ?_⟩
  -- Pass to the limit in the equation at `y`.
  have hvK : v y ∈ K := hK.mem_of_tendsto (hlim y hy) (Eventually.of_forall fun n ↦ huK n hy)
  exact fderiv_I_sub_eq_of_tendsto hW hJ.continuousOn hX.continuousOn (hΩKW ⟨hy, hvK⟩)
    (hconv.tendsto_at hy) ((hlim y hy).comp hφ.tendsto_atTop) fun n ↦ hCR (φ n) y hy

end TauCeti.Floer
