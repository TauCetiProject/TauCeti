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

Let `J` and `X` be `C¹` on an open `W ⊆ ℂ × V`, and let `Ω ⊆ ℂ` be open. Let `uₙ` be smooth
solutions on `Ω` along which `J² = -1`, with derivatives bounded on each compact subset of `Ω`
uniformly in `n`, converging pointwise to a `v` whose graph over `Ω` lies in `W`. Then `v` is `C¹`
on `Ω`, `Duₙ → Dv` locally uniformly on `Ω`, and `v` solves the equation at every point of `Ω`
(`TauCeti.Floer.tendstoLocallyUniformlyOn_fderiv_of_floer`).

Since `J² = -1`, the equation is `∂ₛu + J(z, u) ∂ₜu = X(z, u) 1 + J(z, u) X(z, u) i`. The
interior second-derivative estimates of `TauCeti.Analysis.Complex.Wirtinger.SecondDerivative` apply
to this equation on a complex inner product space when the structure is uniformly close to
multiplication by `i`. To reach that form near a point `y ∈ Ω`, where `J(y, v y)² = -1` by
continuity, choose a real-linear frame `Φ : ℂᵐ → V` in which `J(y, v y)` is multiplication by `i`
(`ContinuousLinearMap.exists_continuousLinearEquiv_euclideanSpace_comp_eq_comp_I_smul`). By
continuity, `Φ⁻¹ J(z, x) Φ` stays close to `i` for `(z, x)` near `(y, v y)`, and from some index on
the solutions stay near `v y` on a small disc about `y`. There the coefficients of the equation for
`Φ⁻¹ ∘ uₙ` have derivatives bounded by the chain rule, so the derivatives of the tail of the
sequence are equicontinuous at `y`; the remaining finitely many are continuous, so the whole
sequence of derivatives is equicontinuous on `Ω`
(`TauCeti.equicontinuousAt_of_equicontinuousAt_add`).
The Arzelà–Ascoli theorem in `C¹` (`TauCeti.exists_strictMono_tendstoLocallyUniformlyOn_fderiv`)
gives a subsequence of every subsequence along which `Duₙ → Dv`; as the limit `Dv` is the same each
time, the whole sequence converges. The equation passes to the limit pointwise.

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

/-- **Equicontinuity of the derivatives near a point.** Let `J` and `X` be `C¹` on an open
`W ⊆ ℂ × V`, and let `(y₀, x₀) ∈ W` with `J(y₀, x₀)² = -1`. For some `ε > 0`, any family of smooth
solutions on an open `U ⊆ ball y₀ ε` with values in `closedBall x₀ ε`, along which `J² = -1`, and
whose derivatives are bounded on each compact subset of `U` uniformly in the family, has
equicontinuous derivatives on `U`. In a real-linear frame `Φ : ℂᵐ → V` in which `J(y₀, x₀)` is
multiplication by `i`, the structure `Φ⁻¹ J(z, x) Φ` is close to `i` for `(z, x)` near
`(y₀, x₀)`, and the interior estimates apply to the solutions `Φ⁻¹ ∘ uᵢ` read in that frame. -/
private theorem exists_pos_forall_equicontinuousOn_fderiv_of_floer {ι : Type*}
    {J : ℂ × V → V →L[ℝ] V} {X : ℂ × V → ℂ →L[ℝ] V} {W : Set (ℂ × V)} (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 1 J W) (hX : ContDiffOn ℝ 1 X W) {y₀ : ℂ} {x₀ : V} (hmem : (y₀, x₀) ∈ W)
    (hJsq : ∀ w, J (y₀, x₀) (J (y₀, x₀) w) = -w) :
    ∃ ε > 0, ∀ ⦃U : Set ℂ⦄ ⦃u : ι → ℂ → V⦄, IsOpen U → U ⊆ ball y₀ ε →
      (∀ i, MapsTo (u i) U (closedBall x₀ ε)) → (∀ i, ContDiffOn ℝ ∞ (u i) U) →
      (∀ i, ∀ z ∈ U, ∀ w, J (z, u i z) (J (z, u i z) w) = -w) →
      (∀ i, ∀ z ∈ U, fderiv ℝ (u i) z I - X (z, u i z) I =
        J (z, u i z) (fderiv ℝ (u i) z 1 - X (z, u i z) 1)) →
      (∀ C, IsCompact C → C ⊆ U → ∃ M, ∀ i, ∀ z ∈ C, ‖fderiv ℝ (u i) z‖ ≤ M) →
      EquicontinuousOn (fun i ↦ fderiv ℝ (u i)) U := by
  -- A frame `Φ : ℂᵐ → V` in which `J (y₀, x₀)` is multiplication by `i`, and the conjugation
  -- `C A = Φ⁻¹ A Φ` it induces on endomorphisms.
  obtain ⟨m, Φ, hΦ⟩ :=
    (J (y₀, x₀)).exists_continuousLinearEquiv_euclideanSpace_comp_eq_comp_I_smul
      (ContinuousLinearMap.ext fun w ↦ by simpa using hJsq w)
  let C : (V →L[ℝ] V) ≃L[ℝ] (EuclideanSpace ℂ (Fin m) →L[ℝ] EuclideanSpace ℂ (Fin m)) :=
    Φ.symm.arrowCongr Φ.symm
  have hC (A : V →L[ℝ] V) (w : EuclideanSpace ℂ (Fin m)) : C A w = Φ.symm (A (Φ w)) := by
    simp [C]
  have hCy (w : EuclideanSpace ℂ (Fin m)) : C (J (y₀, x₀)) w = I • w := by
    rw [hC, show J (y₀, x₀) (Φ w) = Φ (I • w) by simpa using congr($hΦ w)]
    simp
  obtain ⟨δ, hδ0, hδ⟩ :=
    exists_pos_forall_equicontinuousOn_fderiv (F := EuclideanSpace ℂ (Fin m)) (ι := ι)
  -- A ball of radius `ε` about `(y₀, x₀)`, inside `W`, on which `C (J q)` is `δ`-close to `i`.
  have hJy : ContinuousAt (fun q ↦ C (J q)) (y₀, x₀) :=
    C.continuous.continuousAt.comp (hJ.continuousOn.continuousAt (hW.mem_nhds hmem))
  obtain ⟨ε, hε, hεW⟩ := Metric.eventually_nhds_iff.1
    ((hJy.eventually_mem (ball_mem_nhds _ (NNReal.coe_pos.2 hδ0))).and (hW.eventually_mem hmem))
  have hwin : ∀ z ∈ ball y₀ (ε / 2), ∀ x ∈ closedBall x₀ (ε / 2), dist (z, x) (y₀, x₀) < ε := by
    intro z hz x hx
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨(mem_ball.1 hz).trans (by linarith), (mem_closedBall.1 hx).trans_lt (by linarith)⟩
  have hclose : ∀ z x, dist (z, x) (y₀, x₀) < ε →
      ∀ w, ‖C (J (z, x)) w - I • w‖ ≤ δ * ‖w‖ := by
    intro z x hzx w
    rw [← hCy w, ← sub_apply]
    exact ((C (J (z, x)) - C (J (y₀, x₀))).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (mem_ball_iff_norm.1 (hεW hzx).1).le (norm_nonneg w))
  set h : ℂ × V → V := fun q ↦ X q 1 + J q (X q I)
  have hh : ContDiffOn ℝ 1 h W :=
    (hX.clm_apply contDiffOn_const).add (hJ.clm_apply (hX.clm_apply contDiffOn_const))
  refine ⟨ε / 2, by positivity, fun U u hU hUy hUx hu hJsq hCR hbd ↦ ?_⟩
  have hdu : ∀ i, ∀ z ∈ U, DifferentiableAt ℝ (u i) z := fun i z hz ↦
    ((hu i).differentiableOn (by simp) z hz).differentiableAt (hU.mem_nhds hz)
  have hgr : ∀ i, ∀ z ∈ U, dist (z, u i z) (y₀, x₀) < ε := fun i z hz ↦
    hwin z (hUy hz) _ (hUx i hz)
  -- The solutions read in the frame `Φ` solve an equation whose complex structure is `δ`-close
  -- to `i`.
  have hequi : EquicontinuousOn (fun i ↦ fderiv ℝ (Φ.symm ∘ u i)) U := by
    refine hδ (Ω := U) (u := fun i ↦ Φ.symm ∘ u i) (f := fun i ↦ Φ.symm ∘ fun z ↦ h (z, u i z))
      (A := fun i ↦ C ∘ fun z ↦ J (z, u i z)) hU
      (fun i ↦ Φ.symm.contDiff.comp_contDiffOn (hu i))
      (fun i z hz ↦ (C.differentiableAt.comp z
        (((hJ.differentiableOn one_ne_zero).differentiableAt
          (hW.mem_nhds (hεW (hgr i z hz)).2)).comp z
            (differentiableAt_id.prodMk (hdu i z hz)))).differentiableWithinAt)
      (fun i z hz w ↦ hclose z _ (hgr i z hz) w) (fun C' hC' hC'U ↦ ?_) (fun i z hz ↦ ?_)
    · -- Uniform bounds on a compact `C' ⊆ U`, through the bounds along the graphs.
      obtain ⟨M, hM⟩ := hbd C' hC' hC'U
      have hC'W : C' ×ˢ closedBall x₀ (ε / 2) ⊆ W := fun q hq ↦
        (hεW (hwin q.1 (hUy (hC'U hq.1)) q.2 hq.2)).2
      have hmaps : ∀ i, MapsTo (u i) C' (closedBall x₀ (ε / 2)) := fun i ↦ (hUx i).mono_left hC'U
      have hdC : ∀ i, ∀ z ∈ C', DifferentiableAt ℝ (u i) z := fun i z hz ↦ hdu i z (hC'U hz)
      obtain ⟨BJ, hBJ⟩ := exists_bound_norm_fderiv_comp_graph hW hJ hC'
        (isCompact_closedBall x₀ (ε / 2)) hC'W hmaps hdC hM
      obtain ⟨Bh, hBh⟩ := exists_bound_norm_fderiv_comp_graph hW hh hC'
        (isCompact_closedBall x₀ (ε / 2)) hC'W hmaps hdC hM
      refine ⟨max (‖(C : (V →L[ℝ] V) →L[ℝ]
          EuclideanSpace ℂ (Fin m) →L[ℝ] EuclideanSpace ℂ (Fin m))‖ * BJ)
        (max (‖(Φ.symm : V →L[ℝ] EuclideanSpace ℂ (Fin m))‖ * Bh)
          (‖(Φ.symm : V →L[ℝ] EuclideanSpace ℂ (Fin m))‖ * M)), fun i z hz ↦ ⟨?_, ?_, ?_⟩⟩
      · rw [C.comp_fderiv]
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          ((mul_le_mul_of_nonneg_left (hBJ i z hz) (norm_nonneg _)).trans (le_max_left _ _))
      · rw [Φ.symm.comp_fderiv]
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          ((mul_le_mul_of_nonneg_left (hBh i z hz) (norm_nonneg _)).trans
            ((le_max_left _ _).trans (le_max_right _ _)))
      · rw [Φ.symm.comp_fderiv]
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          ((mul_le_mul_of_nonneg_left (hM i z hz) (norm_nonneg _)).trans
            ((le_max_right _ _).trans (le_max_right _ _)))
    · -- The equation in the frame `Φ`.
      simp only [Φ.symm.comp_fderiv, Function.comp_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe, hC, ContinuousLinearEquiv.apply_symm_apply, ← map_add]
      exact congrArg Φ.symm (fderiv_one_add_eq_of_fderiv_I_sub_eq (hJsq i z hz) (hCR i z hz))
  -- Back in `V`.
  let P : (ℂ →L[ℝ] EuclideanSpace ℂ (Fin m)) ≃L[ℝ] (ℂ →L[ℝ] V) :=
    (ContinuousLinearEquiv.refl ℝ ℂ).arrowCongr Φ
  have hfun : (fun i ↦ fderiv ℝ (u i)) = (P ∘ ·) ∘ fun i ↦ fderiv ℝ (Φ.symm ∘ u i) := by
    funext i z
    refine ContinuousLinearMap.ext fun w ↦ ?_
    simp [P, Φ.symm.comp_fderiv]
  rw [hfun]
  exact P.isUniformEmbedding.isUniformInducing.equicontinuousOn_iff.1 hequi

/-- **Equicontinuity of the derivatives at a point.** Let `uₙ` be smooth solutions on an open
`Ω`, along which `J² = -1`, with derivatives bounded on each compact subset of `Ω` uniformly in
`n`, and let `uₙ(y) → x₀` for some `y ∈ Ω` with `(y, x₀) ∈ W`. Then the derivatives `Duₙ` are
equicontinuous at `y`. In the limit `J(y, x₀)² = -1`, and from some index on the solutions stay
near `x₀` on a small disc about `y`, where
`exists_pos_forall_equicontinuousOn_fderiv_of_floer` applies; the remaining finitely many
derivatives are continuous at `y`. -/
private theorem equicontinuousAt_fderiv_of_floer {J : ℂ × V → V →L[ℝ] V}
    {X : ℂ × V → ℂ →L[ℝ] V} {W : Set (ℂ × V)} {Ω : Set ℂ} (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 1 J W) (hX : ContDiffOn ℝ 1 X W) (hΩ : IsOpen Ω) {u : ℕ → ℂ → V}
    (hu : ∀ n, ContDiffOn ℝ ∞ (u n) Ω)
    (hJsq : ∀ n, ∀ y ∈ Ω, ∀ w, J (y, u n y) (J (y, u n y) w) = -w)
    (hCR : ∀ n, ∀ y ∈ Ω, fderiv ℝ (u n) y I - X (y, u n y) I =
      J (y, u n y) (fderiv ℝ (u n) y 1 - X (y, u n y) 1))
    (hbd : ∀ C, IsCompact C → C ⊆ Ω → ∃ M, ∀ n, ∀ y ∈ C, ‖fderiv ℝ (u n) y‖ ≤ M)
    {y : ℂ} (hy : y ∈ Ω) {x₀ : V} (hmem : (y, x₀) ∈ W)
    (hlim : Tendsto (fun n ↦ u n y) atTop (𝓝 x₀)) :
    EquicontinuousAt (fun n ↦ fderiv ℝ (u n)) y := by
  -- `J(y, x₀)² = -1`, as a limit along `(y, uₙ y)`.
  have hJc : ContinuousAt J (y, x₀) := hJ.continuousOn.continuousAt (hW.mem_nhds hmem)
  have hJ₀ (w : V) : J (y, x₀) (J (y, x₀) w) = -w :=
    tendsto_nhds_unique ((hJc.clm_apply (hJc.clm_apply continuousAt_const)).tendsto.comp
      (tendsto_const_nhds.prodMk_nhds hlim))
      (tendsto_const_nhds.congr fun n ↦ (hJsq n y hy w).symm)
  obtain ⟨ε, hε, hloc⟩ :=
    exists_pos_forall_equicontinuousOn_fderiv_of_floer (ι := ℕ) hW hJ hX hmem hJ₀
  -- A disc of radius `r` about `y` on which, from the index `N` on, the solutions stay within
  -- `ε` of `x₀`.
  have hequ : EquicontinuousAt u y :=
    (equicontinuousOn_of_forall_isCompact_norm_fderiv_le hΩ
      (fun n ↦ (hu n).differentiableOn (by simp)) hbd y hy).equicontinuousAt (hΩ.mem_nhds hy)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim (ε / 2) (by positivity)
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.1 (inter_mem (inter_mem (hΩ.mem_nhds hy)
    (ball_mem_nhds y hε)) (Metric.equicontinuousAt_iff_right.1 hequ (ε / 2) (by positivity)))
  have hrΩ : ball y r ⊆ Ω := fun z hz ↦ (hrsub hz).1.1
  have htail : EquicontinuousOn (fun n ↦ fderiv ℝ (u (n + N))) (ball y r) :=
    hloc isOpen_ball (fun z hz ↦ (hrsub hz).1.2)
      (fun n z hz ↦ by
        have h₁ := (hrsub hz).2 (n + N)
        have h₂ := hN (n + N) (Nat.le_add_left N n)
        rw [mem_closedBall]
        linarith [dist_triangle (u (n + N) z) (u (n + N) y) x₀,
          dist_comm (u (n + N) z) (u (n + N) y)])
      (fun n ↦ (hu _).mono hrΩ) (fun n z hz ↦ hJsq _ z (hrΩ hz))
      (fun n z hz ↦ hCR _ z (hrΩ hz))
      (fun C hC hCr ↦ (hbd C hC (hCr.trans hrΩ)).imp fun M hM n ↦ hM (n + N))
  exact equicontinuousAt_of_equicontinuousAt_add N
    ((htail y (mem_ball_self hr)).equicontinuousAt (ball_mem_nhds y hr)) fun n _ ↦
      ((hu n).continuousOn_fderiv_of_isOpen hΩ (by simp)).continuousAt (hΩ.mem_nhds hy)

/-- **The derivatives of Floer solutions converge.** Let `J` and `X` be `C¹` on an open set
`W ⊆ ℂ × V`, and let `Ω ⊆ ℂ` be open. Let `uₙ` be smooth solutions of
`∂ₜu - X(z, u) i = J(z, u)(∂ₛu - X(z, u) 1)` on `Ω`, along which `J² = -1`, whose derivatives are
bounded on each compact subset of `Ω` uniformly in `n`, and which converge pointwise on `Ω` to a
`v` whose graph over `Ω` lies in `W`. Then `v` is `C¹` on `Ω`, `Duₙ → Dv` locally uniformly on
`Ω`, and `v` solves the equation on `Ω`. -/
theorem tendstoLocallyUniformlyOn_fderiv_of_floer {J : ℂ × V → V →L[ℝ] V}
    {X : ℂ × V → ℂ →L[ℝ] V} {W : Set (ℂ × V)} {Ω : Set ℂ} (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 1 J W) (hX : ContDiffOn ℝ 1 X W) (hΩ : IsOpen Ω) {u : ℕ → ℂ → V}
    {v : ℂ → V} (hvW : ∀ y ∈ Ω, (y, v y) ∈ W) (hu : ∀ n, ContDiffOn ℝ ∞ (u n) Ω)
    (hJsq : ∀ n, ∀ y ∈ Ω, ∀ w, J (y, u n y) (J (y, u n y) w) = -w)
    (hCR : ∀ n, ∀ y ∈ Ω, fderiv ℝ (u n) y I - X (y, u n y) I =
      J (y, u n y) (fderiv ℝ (u n) y 1 - X (y, u n y) 1))
    (hbd : ∀ C, IsCompact C → C ⊆ Ω → ∃ M, ∀ n, ∀ y ∈ C, ‖fderiv ℝ (u n) y‖ ≤ M)
    (hlim : ∀ y ∈ Ω, Tendsto (fun n ↦ u n y) atTop (𝓝 (v y))) :
    ContDiffOn ℝ 1 v Ω ∧ TendstoLocallyUniformlyOn (fun n ↦ fderiv ℝ (u n)) (fderiv ℝ v) atTop Ω ∧
      ∀ y ∈ Ω, fderiv ℝ v y I - X (y, v y) I = J (y, v y) (fderiv ℝ v y 1 - X (y, v y) 1) := by
  have hequi : EquicontinuousOn (fun n ↦ fderiv ℝ (u n)) Ω := fun y hy ↦
    (equicontinuousAt_fderiv_of_floer hW hJ hX hΩ hu hJsq hCR hbd hy (hvW y hy)
      (hlim y hy)).equicontinuousWithinAt Ω
  -- Along every subsequence, a further subsequence of `Duₙ` converges to `Dv`.
  have hsub (ψ : ℕ → ℕ) (hψ : StrictMono ψ) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ContDiffOn ℝ 1 v Ω ∧
      TendstoLocallyUniformlyOn (fun n ↦ fderiv ℝ (u (ψ (φ n)))) (fderiv ℝ v) atTop Ω :=
    exists_strictMono_tendstoLocallyUniformlyOn_fderiv hΩ
      (fun n ↦ (hu (ψ n)).differentiableOn (by simp)) (hequi.comp ψ)
      (fun y hy ↦ (hbd {y} isCompact_singleton (singleton_subset_iff.2 hy)).imp
        fun M hM n ↦ hM (ψ n) y rfl) fun y hy ↦ (hlim y hy).comp hψ.tendsto_atTop
  obtain ⟨-, -, hv, -⟩ := hsub id strictMono_id
  -- Hence the whole sequence converges uniformly on each compact subset of `Ω`.
  have hconv : TendstoLocallyUniformlyOn (fun n ↦ fderiv ℝ (u n)) (fderiv ℝ v) atTop Ω := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ]
    intro C hCΩ hC U hU
    by_contra hne
    obtain ⟨ψ, hψ, hψU⟩ := extraction_of_frequently_atTop (not_eventually.1 hne)
    obtain ⟨φ, -, -, hφ⟩ := hsub ψ hψ
    obtain ⟨n, hn⟩ :=
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).1 hφ C hCΩ hC U hU).exists
    exact hψU (φ n) hn
  -- Pass to the limit in the equation.
  exact ⟨hv, hconv, fun y hy ↦ fderiv_I_sub_eq_of_tendsto hW hJ.continuousOn hX.continuousOn
    (hvW y hy) (hconv.tendsto_at hy) (hlim y hy) fun n ↦ hCR n y hy⟩

end TauCeti.Floer
