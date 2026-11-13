/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Equicontinuity
public import TauCeti.Analysis.Complex.Wirtinger.SecondDerivative
public import TauCeti.Geometry.Symplectic.Floer.Compactness
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Geometry.Symplectic.Complex.Module.Conjugacy
import TauCeti.Topology.UniformSpace.Ascoli

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
everywhere. This file upgrades such convergence to convergence of the derivatives, for a target
`V` that is any finite-dimensional real normed space.

**Coordinates in which `J` is close to `i`.** Let the target be a finite-dimensional complex inner
product space `F`, and let `J` and `X` be `C¹` near `Ω × K`, for an open `Ω ⊆ ℂ` and a compact
`K ⊆ F`, with `J² = -1` and `‖J(z, x) w - i w‖ ≤ δ ‖w‖` on `Ω × K`, where `δ > 0` depends only
on `F`. Since `J² = -1`, the equation is `∂ₛu + J(z, u) ∂ₜu = X(z, u) 1 + J(z, u) X(z, u) i`.
Along a solution `u` its coefficients `J(z, u z)` and `X(z, u z) 1 + J(z, u z) X(z, u z) i` have
derivatives bounded by the chain rule, so the interior second-derivative estimates of
`TauCeti.Analysis.Complex.Wirtinger.SecondDerivative` show that the derivatives of smooth
solutions with values in `K`, and with derivatives bounded on compact sets, are equicontinuous
(`TauCeti.Floer.exists_pos_forall_equicontinuousOn_fderiv_of_floer`).

**General targets.** The closeness of `J` to `i` is a hypothesis on the coordinates, not on `J`.
At a point `(y₀, x₀)` the structure `J(y₀, x₀)` is multiplication by `i` in real-linear
coordinates `T : V ≃L[ℝ] ℂᵐ`
(`ContinuousLinearMap.exists_continuousLinearEquiv_euclideanSpace_comp_eq_I_smul_comp`), so near
`(y₀, x₀)` the structure `T J T⁻¹` is close to `i`. Solutions with derivatives bounded on compact
sets that converge pointwise to `v` converge locally uniformly, so a tail of them maps a small disc
about `y₀` close to `v y₀`, and the coordinate statement gives equicontinuity of their derivatives
at `y₀`. This holds at every point of `Ω`, so the Arzelà–Ascoli theorem in `C¹`
(`TauCeti.exists_strictMono_tendstoLocallyUniformlyOn_fderiv`) applies on `Ω`: when `J` and `X` are
`C¹` with `J² = -1` on `Ω × K`, the limit `v` is `C¹`, a subsequence of the derivatives converges
to `Dv` locally uniformly, and the equation passes to the limit pointwise
(`TauCeti.Floer.exists_strictMono_tendstoLocallyUniformlyOn_fderiv_of_floer`).

**Off the bubbling points.** Combined with the compactness theorem
`TauCeti.Floer.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset`, this shows that
smooth Floer solutions of bounded energy converge in `C¹` off finitely many bubbling points, to a
`C¹` solution of the same equation there
(`TauCeti.Floer.exists_pos_forall_tendstoLocallyUniformlyOn_fderiv_subseq_off_finset`).

## Main results

* `TauCeti.Floer.exists_pos_forall_equicontinuousOn_fderiv_of_floer`: the derivatives of
  solutions are equicontinuous in coordinates where `J` is close to `i`.
* `TauCeti.Floer.exists_strictMono_tendstoLocallyUniformlyOn_fderiv_of_floer`: `C¹` convergence
  of a subsequence of pointwise convergent solutions, for any finite-dimensional real target.
* `TauCeti.Floer.exists_pos_forall_tendstoLocallyUniformlyOn_fderiv_subseq_off_finset`: `C¹`
  convergence of Floer solutions of bounded energy off finitely many bubbling points.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications **52**, 2012, Appendix B.4 (elliptic bootstrapping) and Section 8.1
  (inhomogeneous equations).
-/

public section

open Complex Filter MeasureTheory Metric Set Topology
open scoped NNReal ContDiff

namespace TauCeti.Floer

section Equation

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

end Equation

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- **The derivatives of Floer solutions are equicontinuous.** There is `δ > 0`, depending only on
`F`, with the following property. Let `J` and `X` be `C¹` on an open set `W ⊆ ℂ × F` containing
`Ω × K`, for an open `Ω ⊆ ℂ` and a compact `K ⊆ F`, with `J(z, x)² = -1` and
`‖J(z, x) w - i w‖ ≤ δ ‖w‖` on `Ω × K`. Let `uₙ`, indexed by `n` in any type `ι`, be smooth
solutions of `∂ₜu - X(z, u) i = J(z, u)(∂ₛu - X(z, u) 1)` on `Ω` with values in `K`, whose
derivatives are bounded on each compact subset of `Ω` uniformly in `n`. Then the derivatives `Duₙ`
are equicontinuous on `Ω`. -/
theorem exists_pos_forall_equicontinuousOn_fderiv_of_floer {ι : Type*} [FiniteDimensional ℂ F] :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ ⦃J : ℂ × F → F →L[ℝ] F⦄ ⦃X : ℂ × F → ℂ →L[ℝ] F⦄ ⦃W : Set (ℂ × F)⦄
      ⦃Ω : Set ℂ⦄ ⦃K : Set F⦄, IsOpen W → ContDiffOn ℝ 1 J W → ContDiffOn ℝ 1 X W →
      IsOpen Ω → IsCompact K → Ω ×ˢ K ⊆ W →
      (∀ z ∈ Ω, ∀ x ∈ K, ∀ w, J (z, x) (J (z, x) w) = -w) →
      (∀ z ∈ Ω, ∀ x ∈ K, ∀ w, ‖J (z, x) w - I • w‖ ≤ δ * ‖w‖) →
      ∀ ⦃u : ι → ℂ → F⦄, (∀ n, ContDiffOn ℝ ∞ (u n) Ω) →
      (∀ n, ∀ y ∈ Ω, fderiv ℝ (u n) y I - X (y, u n y) I =
        J (y, u n y) (fderiv ℝ (u n) y 1 - X (y, u n y) 1)) →
      (∀ n, MapsTo (u n) Ω K) →
      (∀ C, IsCompact C → C ⊆ Ω → ∃ M, ∀ n, ∀ y ∈ C, ‖fderiv ℝ (u n) y‖ ≤ M) →
      EquicontinuousOn (fun n ↦ fderiv ℝ (u n)) Ω := by
  obtain ⟨δ, hδ0, hδ⟩ := exists_pos_forall_equicontinuousOn_fderiv (F := F) (ι := ι)
  refine ⟨δ, hδ0, fun J X W Ω K hW hJ hX hΩ hK hΩKW hJsq hJI u hu hCR huK hbd ↦ ?_⟩
  -- The right-hand side `h(z, x) = X(z, x) 1 + J(z, x) X(z, x) i` of the equation
  -- `∂ₛu + J(z, u) ∂ₜu = h(z, u)`.
  set h : ℂ × F → F := fun q ↦ X q 1 + J q (X q I)
  have hh : ContDiffOn ℝ 1 h W :=
    (hX.clm_apply contDiffOn_const).add (hJ.clm_apply (hX.clm_apply contDiffOn_const))
  have hmem : ∀ n, ∀ y ∈ Ω, (y, u n y) ∈ W := fun n y hy ↦ hΩKW ⟨hy, huK n hy⟩
  have hdu : ∀ n, ∀ y ∈ Ω, DifferentiableAt ℝ (u n) y := fun n y hy ↦
    ((hu n).differentiableOn (by simp) y hy).differentiableAt (hΩ.mem_nhds hy)
  refine hδ (A := fun n z ↦ J (z, u n z)) (f := fun n z ↦ h (z, u n z)) hΩ hu
    (fun n y hy ↦ (((hJ.differentiableOn one_ne_zero).differentiableAt
      (hW.mem_nhds (hmem n y hy))).comp y
        (differentiableAt_id.prodMk (hdu n y hy))).differentiableWithinAt)
    (fun n z hz ↦ hJI z hz (u n z) (huK n hz)) (fun C hC hCΩ ↦ ?_)
    (fun n y hy ↦ fderiv_one_add_eq_of_fderiv_I_sub_eq (hJsq y hy _ (huK n hy)) (hCR n y hy))
  obtain ⟨M, hM⟩ := hbd C hC hCΩ
  have hCKW : C ×ˢ K ⊆ W := (prod_mono hCΩ subset_rfl).trans hΩKW
  have hCK : ∀ n, MapsTo (u n) C K := fun n ↦ (huK n).mono_left hCΩ
  have hdC : ∀ n, ∀ y ∈ C, DifferentiableAt ℝ (u n) y := fun n y hy ↦ hdu n y (hCΩ hy)
  obtain ⟨BJ, hBJ⟩ := exists_bound_norm_fderiv_comp_graph hW hJ hC hK hCKW hCK hdC hM
  obtain ⟨Bh, hBh⟩ := exists_bound_norm_fderiv_comp_graph hW hh hC hK hCKW hCK hdC hM
  exact ⟨max (max BJ Bh) M, fun n y hy ↦ ⟨(hBJ n y hy).trans (by simp),
    (hBh n y hy).trans (by simp), (hM n y hy).trans (by simp)⟩⟩

section GeneralTarget

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The derivatives of smooth Floer solutions with values in a compact set `K` of a general
finite-dimensional target, with derivatives bounded on compact sets and converging locally
uniformly, are equicontinuous at each point of `Ω`. -/
private theorem equicontinuousAt_fderiv_of_floer {J : ℂ × V → V →L[ℝ] V}
    {X : ℂ × V → ℂ →L[ℝ] V} {W : Set (ℂ × V)} {Ω : Set ℂ} {K : Set V} (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 1 J W) (hX : ContDiffOn ℝ 1 X W) (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hΩKW : Ω ×ˢ K ⊆ W) (hJsq : ∀ z ∈ Ω, ∀ x ∈ K, ∀ w, J (z, x) (J (z, x) w) = -w)
    {u : ℕ → ℂ → V} {v : ℂ → V} (hu : ∀ n, ContDiffOn ℝ ∞ (u n) Ω)
    (hCR : ∀ n, ∀ y ∈ Ω, fderiv ℝ (u n) y I - X (y, u n y) I =
      J (y, u n y) (fderiv ℝ (u n) y 1 - X (y, u n y) 1))
    (huK : ∀ n, MapsTo (u n) Ω K)
    (hbd : ∀ C, IsCompact C → C ⊆ Ω → ∃ M, ∀ n, ∀ y ∈ C, ‖fderiv ℝ (u n) y‖ ≤ M)
    (hlim : TendstoLocallyUniformlyOn u v atTop Ω) {y₀ : ℂ} (hy₀ : y₀ ∈ Ω) :
    EquicontinuousAt (fun n ↦ fderiv ℝ (u n)) y₀ := by
  -- Choose coordinates `T` adapted to `J(y₀, v y₀)` and a ball `B_r(y₀)` on which a tail
  -- `T ∘ u (k + N)` satisfies the hypotheses of the coordinate statement, transfer the resulting
  -- equicontinuity back through `T`, and add the finitely many terms `k < N`.
  have hv : ContinuousOn v Ω := hlim.continuousOn (Frequently.of_forall fun n ↦ (hu n).continuousOn)
  have hx₀ : v y₀ ∈ K := hK.isClosed.mem_of_tendsto (hlim.tendsto_at hy₀)
    (Eventually.of_forall fun n ↦ huK n hy₀)
  -- Coordinates `T` in which `J(y₀, v y₀)` is multiplication by `i`.
  obtain ⟨m, T, hT⟩ :=
    (J (y₀, v y₀)).exists_continuousLinearEquiv_euclideanSpace_comp_eq_I_smul_comp
      (ContinuousLinearMap.ext (hJsq y₀ hy₀ _ hx₀))
  have hTJ (w : V) : T (J (y₀, v y₀) w) = I • T w := congr($hT w)
  obtain ⟨δ, hδ0, hδ⟩ := exists_pos_forall_equicontinuousOn_fderiv_of_floer
    (F := EuclideanSpace ℂ (Fin m)) (ι := ℕ)
  -- The data `J' = T J T⁻¹` and `X' = T X` read in these coordinates.
  set Φ : ℂ × EuclideanSpace ℂ (Fin m) → ℂ × V := fun q ↦ (q.1, T.symm q.2)
  have hΦ : ContDiff ℝ 1 Φ := contDiff_fst.prodMk (T.symm.contDiff.comp contDiff_snd)
  set J' : ℂ × EuclideanSpace ℂ (Fin m) → _ := fun q ↦
    (T : V →L[ℝ] EuclideanSpace ℂ (Fin m)) ∘L J (Φ q) ∘L (T.symm : EuclideanSpace ℂ (Fin m) →L[ℝ] V)
  set X' : ℂ × EuclideanSpace ℂ (Fin m) → _ := fun q ↦
    (T : V →L[ℝ] EuclideanSpace ℂ (Fin m)) ∘L X (Φ q)
  have hW' : IsOpen (Φ ⁻¹' W) := hW.preimage hΦ.continuous
  have hJ' : ContDiffOn ℝ 1 J' (Φ ⁻¹' W) := contDiffOn_const.clm_comp
    ((hJ.comp hΦ.contDiffOn (mapsTo_preimage _ _)).clm_comp contDiffOn_const)
  have hX' : ContDiffOn ℝ 1 X' (Φ ⁻¹' W) :=
    contDiffOn_const.clm_comp (hX.comp hΦ.contDiffOn (mapsTo_preimage _ _))
  set q₀ : ℂ × EuclideanSpace ℂ (Fin m) := (y₀, T (v y₀))
  have hΦq₀ : Φ q₀ = (y₀, v y₀) := by simp [Φ, q₀]
  have hJ'q₀ (w) : J' q₀ w = I • w := by simp [J', hΦq₀, hTJ]
  have hq₀ : q₀ ∈ Φ ⁻¹' W := by rw [mem_preimage, hΦq₀]; exact hΩKW ⟨hy₀, hx₀⟩
  -- On a ball about `q₀` the data are defined and `J'` is within `δ` of `i`.
  obtain ⟨ε, hε, hεsub⟩ : ∃ ε > 0, ball q₀ ε ⊆ Φ ⁻¹' W ∩ J' ⁻¹' ball (J' q₀) δ :=
    Metric.mem_nhds_iff.1 (inter_mem (hW'.mem_nhds hq₀)
      ((hJ'.continuousOn.continuousAt (hW'.mem_nhds hq₀)).preimage_mem_nhds
        (ball_mem_nhds _ (by exact_mod_cast hδ0))))
  -- Eventually the solutions map a ball about `y₀` to within `ε / 2` of `T (v y₀)`.
  obtain ⟨t, ht, htev⟩ := Metric.tendstoLocallyUniformlyOn_iff.1
    (T.isUniformEmbedding.uniformContinuous.comp_tendstoLocallyUniformlyOn hlim) (ε / 4)
    (by positivity) y₀ hy₀
  rw [hΩ.nhdsWithin_eq hy₀] at ht
  have hTv : ContinuousAt (T ∘ v) y₀ :=
    T.continuous.continuousAt.comp (hv.continuousAt (hΩ.mem_nhds hy₀))
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.1 (inter_mem (inter_mem (inter_mem ht
    (hΩ.mem_nhds hy₀)) (ball_mem_nhds y₀ hε)) (hTv.preimage_mem_nhds (ball_mem_nhds _
      (by positivity : 0 < ε / 4))))
  obtain ⟨N, hN⟩ := eventually_atTop.1 htev
  have hrΩ : ball y₀ r ⊆ Ω := fun z hz ↦ (hrsub hz).1.1.2
  set K₀ := T '' K ∩ closedBall (T (v y₀)) (ε / 2)
  have hK₀ : IsCompact K₀ := (hK.image T.continuous).inter_right isClosed_closedBall
  have hmaps : ∀ k, MapsTo (T ∘ u (k + N)) (ball y₀ r) K₀ := by
    intro k z hz
    have h₁ : dist (T (v z)) (T (u (k + N) z)) < ε / 4 := hN (k + N) (by omega) z (hrsub hz).1.1.1
    have h₂ : dist (T (v z)) (T (v y₀)) < ε / 4 := (hrsub hz).2
    refine ⟨mem_image_of_mem T (huK _ (hrΩ hz)), mem_closedBall.2 ?_⟩
    rw [Function.comp_apply]
    linarith [dist_triangle_left (T (u (k + N) z)) (T (v y₀)) (T (v z))]
  have hsub : ball y₀ r ×ˢ K₀ ⊆ ball q₀ ε := by
    rintro ⟨z, y⟩ ⟨hz, hy⟩
    rw [mem_ball, Prod.dist_eq]
    exact max_lt (hrsub hz).1.2 ((mem_closedBall.1 hy.2).trans_lt (half_lt_self hε))
  -- Read in the coordinates `T`, the tail `T ∘ u (k + N)` satisfies the hypotheses of
  -- `exists_pos_forall_equicontinuousOn_fderiv_of_floer` on the ball `B_r(y₀)`.
  have hfd (n : ℕ) (y : ℂ) :
      fderiv ℝ (T ∘ u n) y = (T : V →L[ℝ] EuclideanSpace ℂ (Fin m)) ∘L fderiv ℝ (u n) y :=
    T.comp_fderiv
  have hJsq' : ∀ z ∈ ball y₀ r, ∀ y ∈ K₀, ∀ w, J' (z, y) (J' (z, y) w) = -w := by
    rintro z hz _ ⟨⟨x, hx, rfl⟩, -⟩ w
    simp [J', Φ, hJsq z (hrΩ hz) x hx]
  have hJI' : ∀ z ∈ ball y₀ r, ∀ y ∈ K₀, ∀ w, ‖J' (z, y) w - I • w‖ ≤ δ * ‖w‖ := by
    intro z hz y hy w
    have hd : ‖J' (z, y) - J' q₀‖ < δ := by
      rw [← dist_eq_norm]
      exact (hεsub (hsub ⟨hz, hy⟩)).2
    calc ‖J' (z, y) w - I • w‖ = ‖(J' (z, y) - J' q₀) w‖ := by
          rw [sub_apply, hJ'q₀]
      _ ≤ ‖J' (z, y) - J' q₀‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ δ * ‖w‖ := by gcongr
  have hCR' : ∀ k, ∀ y ∈ ball y₀ r, fderiv ℝ (T ∘ u (k + N)) y I - X' (y, (T ∘ u (k + N)) y) I =
      J' (y, (T ∘ u (k + N)) y) (fderiv ℝ (T ∘ u (k + N)) y 1 - X' (y, (T ∘ u (k + N)) y) 1) := by
    intro k y hy
    simp only [hfd, J', X', Φ, Function.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
    rw [← map_sub, ← map_sub, ContinuousLinearEquiv.symm_apply_apply, hCR _ y (hrΩ hy)]
  have hbd' : ∀ C, IsCompact C → C ⊆ ball y₀ r →
      ∃ M, ∀ k, ∀ y ∈ C, ‖fderiv ℝ (T ∘ u (k + N)) y‖ ≤ M := by
    intro C hC hCr
    obtain ⟨M, hM⟩ := hbd C hC (hCr.trans hrΩ)
    exact ⟨‖(T : V →L[ℝ] EuclideanSpace ℂ (Fin m))‖ * M, fun k y hy ↦ by
      rw [hfd]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by gcongr; exact hM _ y hy)⟩
  have hequi := hδ hW' hJ' hX' isOpen_ball hK₀ (hsub.trans fun q hq ↦ (hεsub hq).1) hJsq' hJI'
    (u := fun k ↦ T ∘ u (k + N)) (fun k ↦ T.contDiff.comp_contDiffOn ((hu _).mono hrΩ)) hCR'
    hmaps hbd'
  -- Equicontinuity of the tail at `y₀`, back in the original coordinates.
  have htail : EquicontinuousAt (fun k ↦ fderiv ℝ (u (k + N))) y₀ := by
    have h := (equicontinuousWithinAt_iff_continuousWithinAt.1
      (hequi y₀ (mem_ball_self hr))).continuousAt (ball_mem_nhds y₀ hr)
    set e := (ContinuousLinearEquiv.refl ℝ ℂ).arrowCongr T
    have heq : ((e ∘ ·) ∘ fun k ↦ fderiv ℝ (u (k + N))) = fun k ↦ fderiv ℝ (T ∘ u (k + N)) := by
      funext k y
      rw [hfd]
      ext w
      simp [e]
    rw [e.isUniformEmbedding.isUniformInducing.equicontinuousAt_iff, heq]
    exact equicontinuousAt_iff_continuousAt.2 h
  -- The finitely many remaining derivatives are continuous at `y₀`.
  have hfin : EquicontinuousAt (fun k : Fin N ↦ fderiv ℝ (u k)) y₀ :=
    equicontinuousAt_finite.2 fun k ↦
      ((hu k).continuousOn_fderiv_of_isOpen hΩ (by simp)).continuousAt (hΩ.mem_nhds hy₀)
  intro U hU
  filter_upwards [htail U hU, hfin U hU] with y h₁ h₂ n
  obtain hn | hn := lt_or_ge n N
  · exact h₂ ⟨n, hn⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    exact h₁ k

/-- **The derivatives of Floer solutions converge, in a general target.** Let `V` be a
finite-dimensional real normed space and let `J` and `X` be `C¹` on an open set `W ⊆ ℂ × V`
containing `Ω × K`, for an open `Ω ⊆ ℂ` and a compact `K ⊆ V`, with `J(z, x)² = -1` on `Ω × K`.
Let `uₙ` be smooth solutions of `∂ₜu - X(z, u) i = J(z, u)(∂ₛu - X(z, u) 1)` on `Ω` with values
in `K`, whose derivatives are bounded on each compact subset of `Ω` uniformly in `n`, and which
converge pointwise on `Ω` to `v`. Then `v` is `C¹` on `Ω`, along a subsequence `Duₙ → Dv`
locally uniformly on `Ω`, and `v` solves the equation on `Ω`. -/
theorem exists_strictMono_tendstoLocallyUniformlyOn_fderiv_of_floer {J : ℂ × V → V →L[ℝ] V}
    {X : ℂ × V → ℂ →L[ℝ] V} {W : Set (ℂ × V)} {Ω : Set ℂ} {K : Set V} (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 1 J W) (hX : ContDiffOn ℝ 1 X W) (hΩ : IsOpen Ω) (hK : IsCompact K)
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
  have hdu : ∀ n, DifferentiableOn ℝ (u n) Ω := fun n ↦ (hu n).differentiableOn (by simp)
  -- The derivative bounds make the solutions equicontinuous, so they converge locally uniformly.
  have hlim' : TendstoLocallyUniformlyOn u v atTop Ω :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).2 fun C hCΩ hC ↦
      EquicontinuousOn.tendstoUniformlyOn_of_tendsto
        ((equicontinuousOn_of_forall_isCompact_norm_fderiv_le hΩ hdu hbd).mono hCΩ) hC
        fun y hy ↦ hlim y (hCΩ hy)
  obtain ⟨φ, hφ, hv, hconv⟩ := exists_strictMono_tendstoLocallyUniformlyOn_fderiv hΩ hdu
    (fun y hy ↦ (equicontinuousAt_fderiv_of_floer hW hJ hX hΩ hK hΩKW hJsq hu hCR huK hbd hlim'
      hy).equicontinuousWithinAt Ω)
    (fun y hy ↦ (hbd {y} isCompact_singleton (singleton_subset_iff.2 hy)).imp
      fun M hM n ↦ hM n y rfl) hlim
  refine ⟨φ, hφ, hv, hconv, fun y hy ↦ ?_⟩
  -- Pass to the limit in the equation at `y`.
  have hvK : v y ∈ K := hK.isClosed.mem_of_tendsto (hlim y hy)
    (Eventually.of_forall fun n ↦ huK n hy)
  exact fderiv_I_sub_eq_of_tendsto hW hJ.continuousOn hX.continuousOn (hΩKW ⟨hy, hvK⟩)
    (hconv.tendsto_at hy) ((hlim y hy).comp hφ.tendsto_atTop) fun n ↦ hCR (φ n) y hy

end GeneralTarget

section OffBubbling

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Floer solutions converge in `C¹` off finitely many bubbling points.** Let `J` and `X` be
`C²` on an open set `W ⊆ ℂ × V` containing `D × K` for compact `D ⊆ ℂ` and `K ⊆ V`, with
`J(z, x)² = -1` on `D × K`, where `V` is a finite-dimensional real inner product space. There is
a threshold `δ > 0` with the following property. Let `uₖ` be smooth solutions of
`∂ₜu - X(z, u) i = J(z, u)(∂ₛu - X(z, u) 1)` on an open set `Ω ⊆ D`, with image in `K` and
energy `∫_Ω ‖∂ₛuₖ‖² ≤ E`. Then there are a subsequence `φ`, a finite set `Z ⊆ Ω` with
`#Z * δ ≤ E`, and a map `v` with values in `K` on `Ω \ Z`, such that along `φ` every disc about a
point of `Z` eventually carries energy at least `δ`, the differentials are uniformly bounded on
every compact subset of `Ω \ Z`, `u_{φ n} → v` and `Du_{φ n} → Dv` locally uniformly on `Ω \ Z`,
and `v` is a `C¹` solution of the equation on `Ω \ Z`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_fderiv_subseq_off_finset
    {J : ℂ × V → V →L[ℝ] V} {X : ℂ × V → ℂ →L[ℝ] V} {W : Set (ℂ × V)} {D : Set ℂ} {K : Set V}
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hX : ContDiffOn ℝ 2 X W)
    (hD : IsCompact D) (hK : IsCompact K) (hDKW : D ×ˢ K ⊆ W)
    (hJsq : ∀ z ∈ D, ∀ x ∈ K, ∀ v, J (z, x) (J (z, x) v) = -v) :
    ∃ δ > 0, ∀ ⦃Ω : Set ℂ⦄ ⦃u : ℕ → ℂ → V⦄ ⦃E : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, ContDiffOn ℝ ∞ (u k) Ω) →
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
        MapsTo v (Ω \ ↑Z) K ∧ ContDiffOn ℝ 1 v (Ω \ ↑Z) ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) ∧
        TendstoLocallyUniformlyOn (fun n ↦ fderiv ℝ (u (φ n))) (fderiv ℝ v) atTop (Ω \ ↑Z) ∧
        ∀ y ∈ Ω \ ↑Z,
          fderiv ℝ v y I - X (y, v y) I = J (y, v y) (fderiv ℝ v y 1 - X (y, v y) 1) := by
  obtain ⟨δ, hδ, hconv⟩ := exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset hW hJ hX
    hD hK hDKW hJsq
  refine ⟨δ, hδ, fun Ω u E hΩ hΩD hu hCR huK hint hE ↦ ?_⟩
  obtain ⟨φ, Z, v, hφ, hZΩ, hcard, hconc, hbd, -, hvK, hlim⟩ := hconv hΩ hΩD
    (fun k ↦ (hu k).of_le (WithTop.coe_le_coe.2 le_top)) hCR huK hint hE
  -- Upgrade the convergence off `Z` to `C¹` convergence along a further subsequence `ψ`.
  have hΩZ : IsOpen (Ω \ ↑Z) := hΩ.sdiff Z.finite_toSet.isClosed
  obtain ⟨ψ, hψ, hv, hdconv, hveq⟩ := exists_strictMono_tendstoLocallyUniformlyOn_fderiv_of_floer
    hW (hJ.of_le one_le_two) (hX.of_le one_le_two) hΩZ hK
    ((prod_mono (sdiff_subset.trans hΩD) subset_rfl).trans hDKW)
    (fun z hz ↦ hJsq z (hΩD hz.1)) (u := fun n ↦ u (φ n)) (fun n ↦ (hu _).mono sdiff_subset)
    (fun n y hy ↦ hCR _ y hy.1) (fun n ↦ (huK _).mono_left sdiff_subset) hbd
    fun y hy ↦ hlim.tendsto_at hy
  refine ⟨φ ∘ ψ, Z, v, hφ.comp hψ, hZΩ, hcard,
    fun z hz ε hε ↦ hψ.tendsto_atTop.eventually (hconc z hz ε hε), fun C hC hCZ ↦ ?_, hvK, hv,
    fun U hU y hy ↦ ?_, hdconv, hveq⟩
  · obtain ⟨M, hM⟩ := hbd C hC hCZ
    exact ⟨M, fun n ↦ hM (ψ n)⟩
  · obtain ⟨t, ht, hev⟩ := hlim U hU y hy
    exact ⟨t, ht, hψ.tendsto_atTop.eventually hev⟩

end OffBubbling

end TauCeti.Floer
