/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Basic
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.SpecialFunctions.Exp
import TauCeti.Analysis.PDE.ClassicalSolution
import TauCeti.Analysis.PDE.Regularity.Hessian.Classical
import TauCeti.Analysis.PDE.Regularity.Inhomogeneous
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Sobolev.W1p.BoundedMeanOscillation
import TauCeti.Analysis.Sobolev.W1p.MeasurePreserving
import TauCeti.Analysis.Sobolev.W1p.PreciseRepresentative
import TauCeti.Analysis.Sobolev.W1p.Restriction

/-!
# Regularity of weak solutions of the reduced vortex equation

Taubes constructs a plane vortex with prescribed zeros from a solution `w` of the reduced
equation

`Δw = h (exp (2w) - 1) / 8 + k`,

where, for a polynomial `P` with the prescribed zeros, `h = TauCeti.Vortex.backgroundWeight P.eval`
and `k = TauCeti.Vortex.backgroundSource P.eval` are the coefficients of Taubes's functional
`TauCeti.Vortex.taubesFunctional`. He obtains `w` as a minimizer of this functional on `H¹(ℂ)`
(`TauCeti.Vortex.sobolevReducedFunctional`). Such a minimizer is a priori only a weak solution:
an element `w ∈ H¹(ℂ)` with

`∫ ⟪∇w, ∇φ⟫ + ∫ (h (exp (2w) - 1) / 8 + k) φ = 0`

for every compactly supported `C¹` function `φ`. This file proves that, for `C¹` coefficients `h`
and `k`, such a `w` agrees almost everywhere with a `C²` function which solves the equation at
every point (`TauCeti.Vortex.exists_contDiff_ae_eq_and_laplacian_eq`). No sign of `h` and no
growth condition on `h` or `k` at infinity is needed, and the solution is not assumed bounded.

The exponential nonlinearity is controlled in two dimensions by the borderline embedding
`H¹ ⊆ BMO` and the John–Nirenberg inequality, in the form
`TauCeti.W1p.locallyIntegrableOn_exp_mul_value`: `exp (σ w)` is locally integrable for every
`w ∈ H¹` and every `σ`. So the right-hand side lies in `L²` on every disc, and the
regularity theory of the Poisson equation applies on each disc:

* De Giorgi's theorem with a right-hand side
  (`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_memLp`) makes the precise
  representative of `w` Hölder continuous;
* hence the right-hand side, a `C¹` function of the point and of the value of `w`, is Hölder
  continuous, and the precise representative is a classical `C²` solution
  (`TauCeti.PDE.contDiffOn_preciseRepresentative_and_neg_laplacian_eq`).

These theorems are stated on `EuclideanSpace ℝ (Fin 2)`; the orthonormal coordinates `1, I`
transport the result to `ℂ`.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, Section 4.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 7.21, 8.24 and 4.6.
-/

public section

noncomputable section

open Filter InnerProductSpace Laplacian MeasureTheory Metric Set TopologicalSpace
open TauCeti.MeasureTheory
open scoped ContDiff Distributions Gradient InnerProductSpace NNReal Topology

namespace TauCeti.Vortex

section Euclidean

/-- A `C¹` function of the point and of the value of a Hölder function `P` is Hölder, with any
exponent `β ≤ 1` smaller than that of `P`, on a closed ball of radius at most `1 / 2`, where all
distances are at most one. -/
private theorem exists_holderOnWith_comp_prodMk {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] {G : E × ℝ → ℝ} (hG : ContDiff ℝ 1 G) {P : E → ℝ}
    {C α β : ℝ≥0} {x : E} {r : ℝ} (hr : r ≤ 1 / 2) (hP : HolderOnWith C α P (closedBall x r))
    (hβ : 0 < β) (hβα : β ≤ α) (hβ1 : β ≤ 1) :
    ∃ K, HolderOnWith K β (fun y => G (y, P y)) (closedBall x r) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall x r).exists_bound_of_continuousOn
    (hP.continuousOn (hβ.trans_le hβα))
  obtain ⟨L, hL⟩ := hG.contDiffOn.exists_lipschitzOnWith one_ne_zero
    ((convex_closedBall x r).prod (convex_closedBall (0 : ℝ) M))
    ((isCompact_closedBall x r).prod (isCompact_closedBall (0 : ℝ) M))
  -- The graph map `y ↦ (y, P y)` is `β`-Hölder: distances are at most one on the ball.
  have hgraph : HolderOnWith (max 1 C) β (fun y => (y, P y)) (closedBall x r) := by
    intro y hy y' hy'
    have hd : edist y y' ≤ 1 := by
      rw [edist_dist, ENNReal.ofReal_le_one]
      linarith [dist_triangle_right y y' x, mem_closedBall.1 hy, mem_closedBall.1 hy']
    have h1 : edist y y' ≤ edist y y' ^ (β : ℝ) := by
      simpa using ENNReal.rpow_le_rpow_of_exponent_ge hd (NNReal.coe_le_one.2 hβ1)
    have h2 : edist y y' ^ (α : ℝ) ≤ edist y y' ^ (β : ℝ) :=
      ENNReal.rpow_le_rpow_of_exponent_ge hd (NNReal.coe_le_coe.2 hβα)
    rw [Prod.edist_eq, max_le_iff]
    constructor
    · calc edist y y' ≤ 1 * edist y y' ^ (β : ℝ) := by rwa [one_mul]
        _ ≤ _ := by gcongr; exact_mod_cast le_max_left 1 C
    · calc edist (P y) (P y') ≤ C * edist y y' ^ (α : ℝ) := hP y hy y' hy'
        _ ≤ _ := by gcongr; exact_mod_cast le_max_right 1 C
  refine ⟨L * max 1 C ^ ((1 : ℝ≥0) : ℝ), ?_⟩
  simpa [Function.comp_def] using (holderOnWith_one.2 hL).comp hgraph fun y hy =>
    ⟨hy, mem_closedBall_zero_iff.2 (hM y hy)⟩

/-- For `w ∈ H¹(ℝ²)` and continuous `h`, `k`, the right-hand side `h (exp (2w) - 1) / 8 + k` is
square integrable on every ball. -/
private theorem memLp_rhs {h k : EuclideanSpace ℝ (Fin 2) → ℝ} (hh : Continuous h)
    (hk : Continuous k) (u : W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) ⊤ 2)
    (x : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ) :
    MemLp (fun y => h y * (Real.exp (2 * W1p.value u y) - 1) / 8 + k y) 2
      (volume.restrict (ball x ρ)) := by
  have : IsFiniteMeasure (volume.restrict (ball x ρ)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  obtain ⟨Mh, hMh⟩ := (isCompact_closedBall x ρ).exists_bound_of_continuousOn hh.continuousOn
  obtain ⟨Mk, hMk⟩ := (isCompact_closedBall x ρ).exists_bound_of_continuousOn hk.continuousOn
  have hw : AEStronglyMeasurable (W1p.value u) (volume.restrict (ball x ρ)) :=
    (Lp.aestronglyMeasurable _).mono_measure (Measure.restrict_mono (subset_univ _) le_rfl)
  have hE : AEStronglyMeasurable (fun y => Real.exp (2 * W1p.value u y))
      (volume.restrict (ball x ρ)) :=
    Real.continuous_exp.comp_aestronglyMeasurable (hw.const_mul 2)
  -- `exp (2w)` is square integrable on the ball, since `exp (4w)` is locally integrable.
  have hE2 : MemLp (fun y => Real.exp (2 * W1p.value u y)) 2 (volume.restrict (ball x ρ)) := by
    refine (memLp_two_iff_integrable_sq hE).2 ?_
    have hloc := W1p.locallyIntegrableOn_exp_mul_value (by simp) u 4
    refine ((hloc.integrableOn_compact_subset (subset_univ _) (isCompact_closedBall x ρ)).mono_set
      ball_subset_closedBall).congr (ae_of_all _ fun y => ?_)
    simp only [sq, ← Real.exp_add]
    ring_nf
  refine ((hE2.const_mul (Mh / 8)).add (memLp_const (Mh / 8 + Mk))).of_le
    ((show Continuous fun q : EuclideanSpace ℝ (Fin 2) × ℝ =>
        h q.1 * (Real.exp (2 * q.2) - 1) / 8 + k q.1 by fun_prop).comp_aestronglyMeasurable
      (aestronglyMeasurable_id.prodMk hw)) ?_
  filter_upwards [self_mem_ae_restrict measurableSet_ball] with y hy
  have h1 := hMh y (ball_subset_closedBall hy)
  have h2 := hMk y (ball_subset_closedBall hy)
  rw [Real.norm_eq_abs] at h1 h2
  have hpos := Real.exp_pos (2 * W1p.value u y)
  have h3 : |Real.exp (2 * W1p.value u y) - 1| ≤ Real.exp (2 * W1p.value u y) + 1 :=
    abs_le.2 ⟨by linarith, by linarith⟩
  have h0 : 0 ≤ Mh := (abs_nonneg _).trans h1
  have h0' : 0 ≤ Mk := (abs_nonneg _).trans h2
  simp only [Real.norm_eq_abs, Pi.add_apply]
  calc |h y * (Real.exp (2 * W1p.value u y) - 1) / 8 + k y|
      ≤ |h y| * |Real.exp (2 * W1p.value u y) - 1| / 8 + |k y| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
    _ ≤ Mh * (Real.exp (2 * W1p.value u y) + 1) / 8 + Mk := by gcongr
    _ ≤ |Mh / 8 * Real.exp (2 * W1p.value u y) + (Mh / 8 + Mk)| := by
        refine le_of_eq_of_le (by ring) (le_abs_self _)

/-- The weak equation in the whole plane, tested against compactly supported `C¹` functions,
restricts to the weak formulation of `-Δv = f` on a ball, tested against `H¹₀`. -/
private theorem energyFormH1_restrictL_eq {h k : EuclideanSpace ℝ (Fin 2) → ℝ}
    (u : W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) ⊤ 2)
    (hu : ∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫ y, ⟪W1p.gradient u y, ∇ φ y⟫_ℝ) +
        ∫ y, (h y * (Real.exp (2 * W1p.value u y) - 1) / 8 + k y) * φ y = 0)
    {B : Opens (EuclideanSpace ℝ (Fin 2))}
    (hF : MemLp (fun y => h y * (Real.exp (2 * W1p.value u y) - 1) / 8 + k y) 2
      (volume.restrict B))
    (v : W1p0 volume B 2) :
    PDE.energyFormH1 (fun _ => 1) 0 0 (W1p.restrictL le_top u) (v : W1p volume B 2) =
      ∫ y in B, -(h y * (Real.exp (2 * W1p.value u y) - 1) / 8 + k y) *
        W1p.value (v : W1p volume B 2) y := by
  have h1 := PDE.uniformlyEllipticOn_const_one_one (n := Fin 2)
    (B : Set (EuclideanSpace ℝ (Fin 2)))
  have hcoeff := PDE.memLp_energyIntegrand_of_bounds (mu := volume) (b := 0) (c := 0)
    (beta := 0) (gamma := 0) h1.upper_nonneg aestronglyMeasurable_const aestronglyMeasurable_const
    aestronglyMeasurable_const (fun _x hx eta xi => h1.upper_bound hx eta xi) (fun _ _ => by simp)
    (fun _ _ => by simp)
  have hf := hF.neg.coeFn_toLp
  refine ((PDE.forall_energyFormH1_eq_setIntegral_iff_forall_testFunction hcoeff
    (hF.neg.toLp _) _).2 (fun φ => ?_) v).trans (integral_congr_ae ?_)
  · -- Against a test function `φ` on `B`, both sides are integrals over the whole plane.
    have hgrad : PDE.energyFormH1 (fun _ => 1) 0 0 (W1p.restrictL le_top u)
        (W1p.ofTestFunctionₗ volume B 2 φ) =
        ∫ y, ⟪W1p.gradient u y, ∇ (φ : EuclideanSpace ℝ (Fin 2) → ℝ) y⟫_ℝ := by
      rw [PDE.energyFormH1_zero_zero_eq_setIntegral]
      refine (integral_congr_ae ?_).trans
        (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_)
      · filter_upwards [gradientTestFunctionLp_apply_ae (mu := volume) 2 φ,
          W1p.gradient_restrictL_ae (le_top : B ≤ ⊤) u] with y hy hy'
        rw [W1p.gradient_ofTestFunctionₗ, hy, hy', PDE.matrixBilinearForm_one_apply,
          real_inner_comm]
        exact ((EuclideanSpace.inner_eq_star_dotProduct _ _).trans (dotProduct_comm _ _)).symm
      · have hφ : fderiv ℝ (φ : EuclideanSpace ℝ (Fin 2) → ℝ) y = 0 :=
          fderiv_of_notMem_tsupport ℝ fun hy' => hy (φ.tsupport_subset hy')
        simp [gradient, hφ]
    have hrhs : ∫ y in B, (hF.neg.toLp _) y * φ y =
        ∫ y, -(h y * (Real.exp (2 * W1p.value u y) - 1) / 8 + k y) * φ y := by
      refine (integral_congr_ae ?_).trans
        (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_)
      · filter_upwards [hf] with y hy
        rw [hy, Pi.neg_apply]
      · simp [φ.zero_on_compl hy]
    have hweak := hu φ (φ.contDiff.of_le (by simp)) φ.hasCompactSupport
    rw [hgrad, hrhs]
    simp only [neg_mul, integral_neg]
    linarith
  · filter_upwards [hf] with y hy
    rw [hy, Pi.neg_apply]

/-- The Euclidean form of `TauCeti.Vortex.exists_contDiff_ae_eq_and_laplacian_eq`. -/
private theorem exists_contDiff_ae_eq_and_laplacian_eq_euclidean
    {h k : EuclideanSpace ℝ (Fin 2) → ℝ} (hh : ContDiff ℝ 1 h) (hk : ContDiff ℝ 1 k)
    (u : W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) ⊤ 2)
    (hu : ∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫ y, ⟪W1p.gradient u y, ∇ φ y⟫_ℝ) +
        ∫ y, (h y * (Real.exp (2 * W1p.value u y) - 1) / 8 + k y) * φ y = 0) :
    ∃ g : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ 2 g ∧ W1p.value u =ᵐ[volume] g ∧
      ∀ y, Δ g y = h y * (Real.exp (2 * g y) - 1) / 8 + k y := by
  set P := preciseRepresentative volume (W1p.value u)
  have hwP : W1p.value u =ᵐ[volume] P := by
    simpa using W1p.ae_eq_preciseRepresentative u
  -- De Giorgi's exponent for `-Δ` with an `L²` right-hand side in the plane.
  obtain ⟨α, C, hα, -, -, hDG⟩ := PDE.exists_holderOnWith_preciseRepresentative_of_memLp
    (ι := Fin 2) (mu := volume) (lam := 1) (Lam := 1) (r := 2) one_lt_two (by norm_num)
  set β : ℝ≥0 := min α (1 / 2)
  have hβ : 0 < β := lt_min hα (by norm_num)
  have hβ1 : β < 1 := (min_le_right _ _).trans_lt (by norm_num)
  -- The right-hand side `-Δw = G(y, w)`, a `C¹` function of the point and the value.
  set G : EuclideanSpace ℝ (Fin 2) × ℝ → ℝ :=
    fun q => -(h q.1 * (Real.exp (2 * q.2) - 1) / 8 + k q.1)
  have hG : ContDiff ℝ 1 G := by fun_prop
  -- Near every point, `P` is a classical solution.
  have hloc : ∀ x, ContDiffAt ℝ 2 P x ∧ Δ P x = h x * (Real.exp (2 * P x) - 1) / 8 + k x := by
    intro x
    let B : Opens (EuclideanSpace ℝ (Fin 2)) := ⟨ball x 1, isOpen_ball⟩
    let v := W1p.restrictL (le_top : B ≤ ⊤) u
    let f := fun y => G (y, P y)
    have hFw : MemLp (fun y => h y * (Real.exp (2 * W1p.value u y) - 1) / 8 + k y) 2
        (volume.restrict (B : Set (EuclideanSpace ℝ (Fin 2)))) :=
      memLp_rhs hh.continuous hk.continuous u x 1
    have hFf : ∀ᵐ y ∂volume.restrict (B : Set (EuclideanSpace ℝ (Fin 2))),
        -(h y * (Real.exp (2 * W1p.value u y) - 1) / 8 + k y) = f y := by
      filter_upwards [ae_restrict_of_ae hwP] with y hy
      simp only [f, G, hy]
    have hf : MemLp f 2 (volume.restrict (B : Set (EuclideanSpace ℝ (Fin 2)))) :=
      hFw.neg.ae_eq hFf
    have hv : ∀ V : W1p0 volume B 2, PDE.energyFormH1 (fun _ => 1) 0 0 v (V : W1p volume B 2) =
        ∫ y in B, f y * W1p.value (V : W1p volume B 2) y := by
      intro V
      rw [energyFormH1_restrictL_eq u hu hFw V]
      refine integral_congr_ae ?_
      filter_upwards [hFf] with y hy
      rw [hy]
    -- De Giorgi: the precise representative of `v`, which is `P` on `B`, is Hölder continuous.
    have hsub : closedBall x (1 / 4) ⊆ (B : Set (EuclideanSpace ℝ (Fin 2))) :=
      closedBall_subset_ball (by norm_num)
    have hK : cthickening (1 / 2) (closedBall x (1 / 4)) ⊆
        (B : Set (EuclideanSpace ℝ (Fin 2))) := by
      rw [cthickening_closedBall (by norm_num) (by norm_num)]
      exact closedBall_subset_ball (by norm_num)
    have hHol := hDG (PDE.uniformlyEllipticOn_const_one_one _) aestronglyMeasurable_const
      (by exact_mod_cast hf) hv (by norm_num : (0 : ℝ) < 1 / 2) hK
    have hPv : ∀ y ∈ (B : Set (EuclideanSpace ℝ (Fin 2))),
        preciseRepresentative volume (W1p.value v) y = P y := fun y hy =>
      preciseRepresentative_congr_ae_nhds (B.isOpen.mem_nhds hy)
        (W1p.value_restrictL_ae (le_top : B ≤ ⊤) u)
    have hPHol : HolderOnWith _ α P (closedBall x (1 / 4)) := fun y hy y' hy' => by
      rw [← hPv y (hsub hy), ← hPv y' (hsub hy')]
      exact hHol y hy y' hy'
    -- Hence the right-hand side is `β`-Hölder, and `P` is a classical solution near `x`.
    obtain ⟨Kf, hKf⟩ := exists_holderOnWith_comp_prodMk hG (by norm_num) hPHol hβ
      (min_le_left _ _) hβ1.le
    let U : Opens (EuclideanSpace ℝ (Fin 2)) := ⟨ball x (1 / 4), isOpen_ball⟩
    have hUB : U ≤ B := ball_subset_ball (by norm_num)
    obtain ⟨hC2, hΔ⟩ := PDE.contDiffOn_preciseRepresentative_and_neg_laplacian_eq (n := 1) hβ hβ1
      hf hv hUB fun y hy => ⟨ball x (1 / 4), isOpen_ball.mem_nhds hy, Kf,
        hKf.mono ball_subset_closedBall⟩
    have hxU : x ∈ (U : Set (EuclideanSpace ℝ (Fin 2))) := mem_ball_self (by norm_num)
    have heq : preciseRepresentative volume (W1p.value v) =ᶠ[𝓝 x] P :=
      eventually_of_mem (B.isOpen.mem_nhds (hUB hxU)) hPv
    refine ⟨(hC2.contDiffAt (U.isOpen.mem_nhds hxU)).congr_of_eventuallyEq heq.symm, ?_⟩
    rw [← (laplacian_congr_nhds heq).self_of_nhds]
    have := hΔ x hxU
    simp only [f, G] at this
    linarith
  exact ⟨P, contDiff_iff_contDiffAt.2 fun x => (hloc x).1, hwP, fun x => (hloc x).2⟩

end Euclidean

/-- **Regularity of weak solutions of the reduced vortex equation.** Let `h` and `k` be `C¹`
functions on `ℂ`, and let `w ∈ H¹(ℂ)` be a weak solution of `Δw = h (exp (2w) - 1) / 8 + k`:

`∫ ⟪∇w, ∇φ⟫ + ∫ (h (exp (2w) - 1) / 8 + k) φ = 0`

for every compactly supported `C¹` function `φ`. Then `w` agrees almost everywhere with a `C²`
function `g` which solves `Δg = h (exp (2g) - 1) / 8 + k` at every point. -/
theorem exists_contDiff_ae_eq_and_laplacian_eq {h k : ℂ → ℝ} (hh : ContDiff ℝ 1 h)
    (hk : ContDiff ℝ 1 k) (u : W1p (volume : Measure ℂ) ⊤ 2)
    (hu : ∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫ z, ⟪W1p.gradient u z, ∇ φ z⟫_ℝ) +
        ∫ z, (h z * (Real.exp (2 * W1p.value u z) - 1) / 8 + k z) * φ z = 0) :
    ∃ g : ℂ → ℝ, ContDiff ℝ 2 g ∧ W1p.value u =ᵐ[volume] g ∧
      ∀ z, Δ g z = h z * (Real.exp (2 * g z) - 1) / 8 + k z := by
  -- Transport `u` to `ℝ²` through the orthonormal coordinates `1, I`.
  let e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr
  have hmp : MeasurePreserving e := e.measurePreserving
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hUV : ((⊤ : Opens (EuclideanSpace ℝ (Fin 2))) : Set (EuclideanSpace ℝ (Fin 2))) =
      e.symm.toAffineIsometryEquiv ⁻¹' (⊤ : Opens ℂ) := by
    simp
  let v := W1p.compAffineIsometryEquivL e.symm.toAffineIsometryEquiv hUV u
  have hval : W1p.value v =ᵐ[volume] fun y => W1p.value u (e.symm y) := by
    simpa using W1p.value_compAffineIsometryEquivL_ae e.symm.toAffineIsometryEquiv hUV u
  have hgrad : W1p.gradient v =ᵐ[volume] fun y => e (W1p.gradient u (e.symm y)) := by
    simpa using W1p.gradient_compAffineIsometryEquivL_ae e.symm.toAffineIsometryEquiv hUV u
  -- The weak equation in the new coordinates.
  have hv : ∀ ψ : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ y, ⟪W1p.gradient v y, ∇ ψ y⟫_ℝ) +
        ∫ y, ((h ∘ e.symm) y * (Real.exp (2 * W1p.value v y) - 1) / 8 + (k ∘ e.symm) y) *
          ψ y = 0 := by
    intro ψ hψ hψc
    have hweak := hu (ψ ∘ e) (hψ.comp e.contDiff) (hψc.comp_homeomorph e.toHomeomorph)
    -- `∇(ψ ∘ e)(z)` pairs with `a` as `∇ψ(e z)` pairs with `e a`.
    have hinner : ∀ z a, ⟪a, ∇ (ψ ∘ e) z⟫_ℝ = ⟪e a, ∇ ψ (e z)⟫_ℝ := fun z a => by
      have hd : fderiv ℝ (ψ ∘ e) z = (fderiv ℝ ψ (e z)).comp (e : ℂ →L[ℝ] _) :=
        ((hψ.differentiable one_ne_zero (e z)).hasFDerivAt.comp z
          e.toContinuousLinearEquiv.hasFDerivAt).fderiv
      rw [real_inner_comm (∇ (ψ ∘ e) z) a, real_inner_comm (∇ ψ (e z)) (e a), gradient,
        gradient, toDual_symm_apply, toDual_symm_apply, hd, ContinuousLinearMap.comp_apply,
        LinearIsometryEquiv.coe_coe'']
    have h1 : ∫ y, ⟪W1p.gradient v y, ∇ ψ y⟫_ℝ = ∫ z, ⟪W1p.gradient u z, ∇ (ψ ∘ e) z⟫_ℝ := by
      rw [integral_congr_ae (hgrad.mono fun y hy => by rw [hy]),
        ← hmp.integral_comp hemb]
      simp [hinner]
    have h2 : ∫ y, ((h ∘ e.symm) y * (Real.exp (2 * W1p.value v y) - 1) / 8 + (k ∘ e.symm) y) *
          ψ y = ∫ z, (h z * (Real.exp (2 * W1p.value u z) - 1) / 8 + k z) * (ψ ∘ e) z := by
      rw [integral_congr_ae (hval.mono fun y hy => by rw [hy]), ← hmp.integral_comp hemb]
      simp
    rw [h1, h2]
    exact hweak
  obtain ⟨P, hP, hvP, hΔP⟩ := exists_contDiff_ae_eq_and_laplacian_eq_euclidean
    (hh.comp e.symm.contDiff) (hk.comp e.symm.contDiff) v hv
  refine ⟨P ∘ e, hP.comp e.contDiff, ?_, fun z => ?_⟩
  · have hP' : (fun y => W1p.value u (e.symm y)) =ᵐ[volume] P := hval.symm.trans hvP
    filter_upwards [hmp.quasiMeasurePreserving.ae_eq_comp hP'] with z hz
    simpa using hz
  · rw [laplacian_comp_linearIsometryEquiv_right, Function.comp_apply, hΔP]
    simp

end TauCeti.Vortex
