/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Equicontinuity
public import TauCeti.Analysis.Complex.Wirtinger.SecondDerivative
import TauCeti.Analysis.Calculus.FDeriv.Prod

/-!
# Convergence of the derivatives of Floer solutions

In local coordinates `z = s + i t ∈ ℂ` on the domain and `x` on the target, the inhomogeneous
Cauchy–Riemann equation of Hamiltonian Floer theory reads

`∂ₜu - X(z, u) i = J(z, u) (∂ₛu - X(z, u) 1)`,

for a domain-dependent almost complex structure `J` and the Hamiltonian one-form `X`, as in
`TauCeti.Geometry.Symplectic.Floer.Compactness.Basic`. The compactness theorem there extracts
from a sequence of solutions of bounded energy a subsequence converging locally uniformly off
finitely many bubbling points, with derivatives bounded on compact subsets of the complement, and
`TauCeti.Geometry.Symplectic.Floer.WeakLimit` shows that the limit solves the equation almost
everywhere. This file upgrades such convergence to convergence of the derivatives, in
coordinates where the target is a finite-dimensional complex inner product space `F` and `J` is
uniformly close to multiplication by `i`.

Let `J` and `X` be `C¹` near `Ω × K`, for an open `Ω ⊆ ℂ` and a compact `K ⊆ F`, with `J² = -1`
and `‖J(z, x) w - i w‖ ≤ δ ‖w‖` on `Ω × K`, where `δ > 0` depends only on `F`. Let `uₙ` be
smooth solutions on `Ω` with values in `K`, with derivatives bounded on each compact subset of
`Ω` uniformly in `n`, converging pointwise to `v`. Then `v` is `C¹` on `Ω`, a subsequence of
`Duₙ` converges to `Dv` locally uniformly on `Ω`, and `v` solves the equation at every point of
`Ω` (`TauCeti.Floer.exists_pos_forall_exists_strictMono_tendstoLocallyUniformlyOn_fderiv`).

Since `J² = -1`, the equation is `∂ₛu + J(z, u) ∂ₜu = X(z, u) 1 + J(z, u) X(z, u) i`. Along
`uₙ` its coefficients `J(z, uₙ z)` and `X(z, uₙ z) 1 + J(z, uₙ z) X(z, uₙ z) i` have derivatives
bounded by the chain rule, so the interior second-derivative estimates of
`TauCeti.Analysis.Complex.Wirtinger.SecondDerivative` make the derivatives `Duₙ` equicontinuous,
and the Arzelà–Ascoli theorem in `C¹` (`TauCeti.exists_strictMono_tendstoLocallyUniformlyOn_fderiv`)
gives the convergent subsequence. The equation passes to the limit pointwise.

The closeness of `J` to `i` is a hypothesis on the coordinates, not on `J`: it is the form in
which the interior estimates apply. Choosing such coordinates near each point of a general
target, by a linear change of coordinates making `J` equal to `i` at that point and shrinking the
neighbourhood, is not carried out here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications **52**, 2012, Appendix B.4 (elliptic bootstrapping) and Section 8.1
  (inhomogeneous equations).
-/

public section

open Complex Filter Metric Set Topology
open scoped NNReal ContDiff

namespace TauCeti.Floer

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

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

/-- **The derivatives of Floer solutions converge.** There is `δ > 0`, depending only on `F`, with
the following property. Let `J` and `X` be `C¹` on an open set `W ⊆ ℂ × F` containing `Ω × K`,
for an open `Ω ⊆ ℂ` and a compact `K ⊆ F`, with `J(z, x)² = -1` and `‖J(z, x) w - i w‖ ≤ δ ‖w‖`
on `Ω × K`. Let `uₙ` be smooth solutions of `∂ₜu - X(z, u) i = J(z, u)(∂ₛu - X(z, u) 1)` on `Ω`
with values in `K`, whose derivatives are bounded on each compact subset of `Ω` uniformly in `n`,
and which converge pointwise on `Ω` to `v`. Then `v` is `C¹` on `Ω`, along a subsequence
`Duₙ → Dv` locally uniformly on `Ω`, and `v` solves the equation on `Ω`. -/
theorem exists_pos_forall_exists_strictMono_tendstoLocallyUniformlyOn_fderiv
    [FiniteDimensional ℂ F] :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ ⦃J : ℂ × F → F →L[ℝ] F⦄ ⦃X : ℂ × F → ℂ →L[ℝ] F⦄ ⦃W : Set (ℂ × F)⦄
      ⦃Ω : Set ℂ⦄ ⦃K : Set F⦄, IsOpen W → ContDiffOn ℝ 1 J W → ContDiffOn ℝ 1 X W →
      IsOpen Ω → IsCompact K → Ω ×ˢ K ⊆ W →
      (∀ z ∈ Ω, ∀ x ∈ K, ∀ w, J (z, x) (J (z, x) w) = -w) →
      (∀ z ∈ Ω, ∀ x ∈ K, ∀ w, ‖J (z, x) w - I • w‖ ≤ δ * ‖w‖) →
      ∀ ⦃u : ℕ → ℂ → F⦄ ⦃v : ℂ → F⦄, (∀ n, ContDiffOn ℝ ∞ (u n) Ω) →
      (∀ n, ∀ y ∈ Ω, fderiv ℝ (u n) y I - X (y, u n y) I =
        J (y, u n y) (fderiv ℝ (u n) y 1 - X (y, u n y) 1)) →
      (∀ n, MapsTo (u n) Ω K) →
      (∀ C, IsCompact C → C ⊆ Ω → ∃ M, ∀ n, ∀ y ∈ C, ‖fderiv ℝ (u n) y‖ ≤ M) →
      (∀ y ∈ Ω, Tendsto (fun n ↦ u n y) atTop (𝓝 (v y))) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ContDiffOn ℝ 1 v Ω ∧
        TendstoLocallyUniformlyOn (fun n ↦ fderiv ℝ (u (φ n))) (fderiv ℝ v) atTop Ω ∧
        ∀ y ∈ Ω, fderiv ℝ v y I - X (y, v y) I = J (y, v y) (fderiv ℝ v y 1 - X (y, v y) 1) := by
  obtain ⟨δ, hδ0, hδ⟩ := exists_pos_forall_equicontinuousOn_fderiv (F := F) (ι := ℕ)
  refine ⟨δ, hδ0, fun J X W Ω K hW hJ hX hΩ hK hΩKW hJsq hJI u v hu hCR huK hbd hlim ↦ ?_⟩
  -- The right-hand side `h(z, x) = X(z, x) 1 + J(z, x) X(z, x) i` of the equation
  -- `∂ₛu + J(z, u) ∂ₜu = h(z, u)`.
  set h : ℂ × F → F := fun q ↦ X q 1 + J q (X q I)
  have hh : ContDiffOn ℝ 1 h W :=
    (hX.clm_apply contDiffOn_const).add (hJ.clm_apply (hX.clm_apply contDiffOn_const))
  have hmem : ∀ n, ∀ y ∈ Ω, (y, u n y) ∈ W := fun n y hy ↦ hΩKW ⟨hy, huK n hy⟩
  have hdu : ∀ n, ∀ y ∈ Ω, DifferentiableAt ℝ (u n) y := fun n y hy ↦
    ((hu n).differentiableOn (by simp) y hy).differentiableAt (hΩ.mem_nhds hy)
  have hequi : EquicontinuousOn (fun n ↦ fderiv ℝ (u n)) Ω := by
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
  obtain ⟨φ, hφ, hv, hconv⟩ := exists_strictMono_tendstoLocallyUniformlyOn_fderiv hΩ
    (fun n y hy ↦ (hdu n y hy).differentiableWithinAt) hequi
    (fun y hy ↦ (hbd {y} isCompact_singleton (singleton_subset_iff.2 hy)).imp
      fun M hM n ↦ hM n y rfl) hlim
  refine ⟨φ, hφ, hv, hconv, fun y hy ↦ ?_⟩
  -- Pass to the limit in the equation at `y`.
  have hvK : v y ∈ K := hK.isClosed.mem_of_tendsto (hlim y hy)
    (Eventually.of_forall fun n ↦ huK n hy)
  exact fderiv_I_sub_eq_of_tendsto hW hJ.continuousOn hX.continuousOn (hΩKW ⟨hy, hvK⟩)
    (hconv.tendsto_at hy) ((hlim y hy).comp hφ.tendsto_atTop) fun n ↦ hCR (φ n) y hy

end TauCeti.Floer
