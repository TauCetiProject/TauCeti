/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Inhomogeneous
public import TauCeti.Analysis.PDE.Vortex.Variational
public import TauCeti.Analysis.Sobolev.W1p.Basic
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.Analysis.PDE.Regularity.Hessian.Classical
import TauCeti.Analysis.Sobolev.Trudinger
import TauCeti.Analysis.Sobolev.W1p.MeasurePreserving
import TauCeti.Topology.MetricSpace.Holder
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Regularity of weak solutions of Taubes's equation

Let `E` be a real inner product space of dimension two, such as `ℂ`, and let `h`, `k` be `C¹`
functions on `E`. **Taubes's equation**

`Δu = h (exp (2u) - 1) / 8 + k`

is the Euler–Lagrange equation of Taubes's functional `TauCeti.Vortex.taubesFunctional`
(`TauCeti.Vortex.forall_hasDerivAt_taubesFunctional_add_smul_iff`). For the background
coefficients `h = TauCeti.Vortex.backgroundWeight f` and `k = TauCeti.Vortex.backgroundSource f`
of an entire function `f`, it is the reduced equation of a plane vortex with section `f`, and
Taubes constructs the vortex with prescribed zeros from a minimizer of his functional on `H¹(ℂ)`,
which is a weak solution. This file proves that weak solutions are continuous, and that they are
classical:

* `TauCeti.Vortex.exists_continuousOn_ae_eq_of_forall_integral_inner_gradient_eq_neg`: a weak
  solution `w ∈ H¹(Ω)` on an open `Ω ⊆ E` with continuous coefficients, tested against test
  functions on `Ω`, agrees almost everywhere on `Ω` with a function continuous on `Ω`;
* `TauCeti.Vortex.exists_contDiff_two_ae_eq_and_laplacian_eq`: a weak solution `u ∈ H¹(E)`, tested
  against compactly supported smooth functions, agrees almost everywhere with a `C²` function
  that solves the equation at every point;
* `TauCeti.Vortex.exists_contDiff_two_ae_eq_and_equation_amplitudeField_eq_zero`: for the
  background coefficients of an entire `f`, the field reconstructed from the amplitude `u₀ + w`
  and the section `f` solves the vortex equations at every point.

The nonlinearity is exponential and `H¹` functions on the plane need not be bounded, so the
equation is not a priori a Poisson equation with bounded data. The proof is a bootstrap on balls.

1. In the borderline case of the Sobolev embedding, Trudinger's inequality makes `exp (c |u|)`
   locally integrable for every `c` (`TauCeti.W1p.integrableOn_exp_mul_abs_value`). So `u` is a
   weak solution of Poisson's equation `-Δu = F` with `F = -(h (exp (2u) - 1) / 8 + k)` in `L²`
   of every ball.
2. De Giorgi's theorem with a right-hand side in `L^r`, `r > n / 2`
   (`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_memLp`), makes the precise
   representative of `u` locally Hölder continuous.
3. Then `F`, computed from the precise representative, is locally Hölder, and the precise
   representative is `C²` and solves `-Δu = F` classically
   (`TauCeti.PDE.contDiffOn_preciseRepresentative_and_neg_laplacian_eq`).

These steps are carried out on `EuclideanSpace ℝ (Fin 2)`, the setting of the elliptic regularity
theory, and transported to `E` along a linear isometry, under which the weak equation and the
Laplacian are invariant.

The decay `u → 0` at infinity, which gives the vortex its degree-`m` end framing, is not treated
here.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, Section 4.
* N. S. Trudinger, *On imbeddings into Orlicz spaces and some applications*, J. Math. Mech. 17
  (1967), 473–483.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 7.15, 8.24 and 4.6.
-/

public section

noncomputable section

open InnerProductSpace Laplacian MeasureTheory Metric Module Set TopologicalSpace
open TauCeti.MeasureTheory TauCeti.PDE
open scoped ContDiff Distributions ENNReal Gradient NNReal RealInnerProductSpace Topology

namespace TauCeti.Vortex

/-! ### Continuity -/

section Continuity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Weak solutions of the reduced vortex equation are continuous.** Let `E` be a real inner
product space of dimension two, `Ω ⊆ E` open, and `h, k` continuous on `Ω`. If `w ∈ H¹(Ω)` solves
`Δw = h (exp (2w) - 1) / 8 + k` weakly in `Ω`, that is

`∫_Ω ⟪∇w, ∇φ⟫ = -∫_Ω (h (exp (2w) - 1) / 8 + k) φ`

for every test function `φ` on `Ω`, then `w` agrees almost everywhere on `Ω` with a function that
is continuous on `Ω`. No sign of `h` and no boundary condition on `w` is assumed. -/
theorem exists_continuousOn_ae_eq_of_forall_integral_inner_gradient_eq_neg (hE : finrank ℝ E = 2)
    {Omega : Opens E} {h k : E → ℝ} (hh : ContinuousOn h Omega) (hk : ContinuousOn k Omega)
    {w : W1p volume Omega 2}
    (hw : ∀ φ : 𝓓(Omega, ℝ),
      ∫ x in Omega, ⟪W1p.gradient w x, ∇ (φ : E → ℝ) x⟫_ℝ =
        -∫ x in Omega, (h x * (Real.exp (2 * W1p.value w x) - 1) / 8 + k x) * φ x) :
    ∃ g : E → ℝ, ContinuousOn g Omega ∧ W1p.value w =ᵐ[volume.restrict Omega] g := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < finrank ℝ E)
  set f : E → ℝ := fun x => -(h x * (Real.exp (2 * W1p.value w x) - 1) / 8 + k x)
  refine PDE.exists_continuousOn_ae_eq_of_forall_integral_inner_gradient_eq (f := f)
    (r := 2) le_rfl (by rw [hE]; norm_num) (fun K hK hKO => ?_)
    (fun φ => by simp only [f, neg_mul, integral_neg, hw])
  -- On a compact `K ⊆ Ω`, `|f| ≤ M exp (2 w) / 8 + 9 M / 8`, and `exp (2 w) ∈ L²(K)`.
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    ((hh.mono hKO).prodMk (hk.mono hKO) : ContinuousOn (fun x => (h x, k x)) K)
  have hwK : AEStronglyMeasurable (W1p.value w : E → ℝ) (volume.restrict K) :=
    (Lp.aestronglyMeasurable _).mono_measure (Measure.restrict_mono hKO le_rfl)
  have hexp : AEStronglyMeasurable (fun x => Real.exp (2 * W1p.value w x)) (volume.restrict K) :=
    Real.continuous_exp.comp_aestronglyMeasurable (hwK.const_mul 2)
  have hexp2 : MemLp (fun x => Real.exp (2 * W1p.value w x)) 2 (volume.restrict K) := by
    refine (memLp_two_iff_integrable_sq hexp).2 ?_
    refine Integrable.mono
      (W1p.integrableOn_exp_mul_abs_value (by rw [hE]; norm_cast) (by omega) w hK hKO 4)
      (hexp.pow 2) (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
      ← Real.exp_nat_mul]
    exact Real.exp_le_exp.2 (by push_cast; linarith [le_abs_self (W1p.value w x)])
  have hfK : AEStronglyMeasurable f (volume.restrict K) := by
    have h1 := (hh.mono hKO).aestronglyMeasurable (μ := volume) hK.measurableSet
    have h2 := (hk.mono hKO).aestronglyMeasurable (μ := volume) hK.measurableSet
    fun_prop
  refine ((hexp2.const_mul (M / 8)).add (memLp_const (9 * M / 8))).of_le hfK
    ((ae_restrict_mem hK.measurableSet).mono fun x hx => ?_)
  have hhx : |h x| ≤ M := (norm_fst_le _).trans (hM x hx)
  have hkx : |k x| ≤ M := (norm_snd_le _).trans (hM x hx)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hhx
  have he : 0 < Real.exp (2 * W1p.value w x) := Real.exp_pos _
  simp only [f, Pi.add_apply, Real.norm_eq_abs, abs_neg]
  rw [abs_of_nonneg (by positivity : 0 ≤ M / 8 * Real.exp (2 * W1p.value w x) + 9 * M / 8)]
  calc |h x * (Real.exp (2 * W1p.value w x) - 1) / 8 + k x|
      ≤ |h x| * (Real.exp (2 * W1p.value w x) + 1) / 8 + |k x| := by
        refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
        rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
        gcongr
        exact (abs_sub _ _).trans (by rw [abs_of_pos he, abs_one])
    _ ≤ M * (Real.exp (2 * W1p.value w x) + 1) / 8 + M := by gcongr
    _ = M / 8 * Real.exp (2 * W1p.value w x) + 9 * M / 8 := by ring

end Continuity

/-! ### The equation on the Euclidean plane -/

section Euclidean

variable {h k : EuclideanSpace ℝ (Fin 2) → ℝ}

/-- On a ball, the nonlinearity `-(h (exp (2u) - 1) / 8 + k)` of a bounded `β`-Hölder function `u`
with `C¹` coefficients is `β`-Hölder. -/
private theorem exists_holderOnWith_nonlinearity (hh : ContDiff ℝ 1 h) (hk : ContDiff ℝ 1 k)
    {u : EuclideanSpace ℝ (Fin 2) → ℝ} {c : EuclideanSpace ℝ (Fin 2)} {ρ : ℝ} {C β : ℝ≥0}
    (hβ : β ≤ 1) (hu : HolderOnWith C β u (ball c ρ)) {M : ℝ}
    (huM : ∀ x ∈ ball c ρ, |u x| ≤ M) :
    ∃ K, HolderOnWith K β (fun x => -(h x * (Real.exp (2 * u x) - 1) / 8 + k x)) (ball c ρ) := by
  have hball : ∀ f : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ 1 f →
      ∃ K M : ℝ≥0, HolderOnWith K β f (ball c ρ) ∧ ∀ x ∈ ball c ρ, ‖f x‖ ≤ M := fun f hf => by
    obtain ⟨L, hL⟩ := hf.contDiffOn.exists_lipschitzOnWith one_ne_zero (convex_closedBall c ρ)
      (isCompact_closedBall c ρ)
    obtain ⟨M, hM⟩ :=
      (isCompact_closedBall c ρ).exists_bound_of_continuousOn hf.continuous.continuousOn
    have hMb : ∀ x ∈ ball c ρ, ‖f x‖ ≤ M.toNNReal := fun x hx =>
      (hM x (ball_subset_closedBall hx)).trans (Real.le_coe_toNNReal M)
    exact ⟨_, _, (hL.mono ball_subset_closedBall).holderOnWith_of_norm_le hMb hβ, hMb⟩
  obtain ⟨Kh, Mh, hHh, hMh⟩ := hball h hh
  obtain ⟨Kk, -, hHk, -⟩ := hball k hk
  have hΦ : ContDiff ℝ 1 fun t : ℝ => -(Real.exp (2 * t) - 1) / 8 := by fun_prop
  obtain ⟨LΦ, hLΦ⟩ := hΦ.contDiffOn.exists_lipschitzOnWith one_ne_zero (convex_Icc (-M) M)
    isCompact_Icc
  obtain ⟨MΦ, hMΦ⟩ := isCompact_Icc.exists_bound_of_continuousOn hΦ.continuous.continuousOn
  have hmaps : MapsTo u (ball c ρ) (Icc (-M) M) := fun x hx => abs_le.1 (huM x hx)
  have hE := hLΦ.holderOnWith.comp hu hmaps
  rw [one_mul] at hE
  have hprod := (ContinuousLinearMap.mul ℝ ℝ).holderOnWith_comp₂ hHh hE hMh
    (Mg := MΦ.toNNReal) fun x hx => (hMΦ _ (hmaps hx)).trans (Real.le_coe_toNNReal MΦ)
  have hneg : HolderOnWith Kk β (fun x => -k x) (ball c ρ) :=
    HolderOnWith.of_dist_le fun x hx y hy => by
      rw [dist_neg_neg]
      exact hHk.dist_le hx hy
  have hfun : (fun x => -(h x * (Real.exp (2 * u x) - 1) / 8 + k x)) =
      (fun x => ContinuousLinearMap.mul ℝ ℝ (h x)
        (((fun t : ℝ => -(Real.exp (2 * t) - 1) / 8) ∘ u) x)) + fun x => -k x := by
    funext x
    simp only [ContinuousLinearMap.mul_apply', Function.comp_apply, Pi.add_apply]
    ring
  rw [hfun]
  exact ⟨_, hprod.add hneg⟩

/-- On a ball, the nonlinearity `-(h (exp (2u) - 1) / 8 + k)` with continuous coefficients is
square integrable as soon as `exp (4 |u|)` is integrable. -/
private theorem memLp_nonlinearity (hh : Continuous h) (hk : Continuous k)
    {u : EuclideanSpace ℝ (Fin 2) → ℝ} {c : EuclideanSpace ℝ (Fin 2)} {ρ : ℝ}
    (hu : AEStronglyMeasurable u (volume.restrict (ball c ρ)))
    (hexp : IntegrableOn (fun x => Real.exp (4 * |u x|)) (ball c ρ)) :
    MemLp (fun x => -(h x * (Real.exp (2 * u x) - 1) / 8 + k x)) 2
      (volume.restrict (ball c ρ)) := by
  obtain ⟨Mh, hMh⟩ := (isCompact_closedBall c ρ).exists_bound_of_continuousOn hh.continuousOn
  obtain ⟨Mk, hMk⟩ := (isCompact_closedBall c ρ).exists_bound_of_continuousOn hk.continuousOn
  have : IsFiniteMeasure (volume.restrict (ball c ρ)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have he : AEStronglyMeasurable (fun x => Real.exp (2 * |u x|)) (volume.restrict (ball c ρ)) :=
    Real.continuous_exp.comp_aestronglyMeasurable (hu.norm.const_mul 2)
  have hE : MemLp (fun x => Real.exp (2 * |u x|)) 2 (volume.restrict (ball c ρ)) := by
    refine (memLp_two_iff_integrable_sq he).2 (hexp.congr_fun_ae (ae_of_all _ fun x => ?_))
    simp only
    rw [← Real.exp_nat_mul]
    ring_nf
  have hG : MemLp (fun x => |Mh| / 8 * (Real.exp (2 * |u x|) + 1) + |Mk|) 2
      (volume.restrict (ball c ρ)) :=
    ((hE.add (memLp_const 1)).const_mul (|Mh| / 8)).add (memLp_const _)
  refine hG.of_le (by fun_prop) ?_
  rw [ae_restrict_iff' measurableSet_ball]
  refine ae_of_all _ fun x hx => ?_
  have hhx : |h x| ≤ |Mh| := (hMh x (ball_subset_closedBall hx)).trans (le_abs_self _)
  have hkx : |k x| ≤ |Mk| := (hMk x (ball_subset_closedBall hx)).trans (le_abs_self _)
  have hex : |Real.exp (2 * u x) - 1| ≤ Real.exp (2 * |u x|) + 1 := by
    refine (abs_sub _ _).trans ?_
    rw [abs_of_pos (Real.exp_pos _), abs_one]
    gcongr
    exact le_abs_self _
  have hG0 : 0 ≤ |Mh| / 8 * (Real.exp (2 * |u x|) + 1) + |Mk| := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hG0, abs_neg]
  calc |h x * (Real.exp (2 * u x) - 1) / 8 + k x|
      ≤ |h x| * |Real.exp (2 * u x) - 1| / 8 + |k x| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
    _ ≤ |Mh| / 8 * (Real.exp (2 * |u x|) + 1) + |Mk| := by
        rw [div_mul_eq_mul_div]
        gcongr

/-- **The equation on a ball as a Poisson equation with `L²` data.** Let `v ∈ H¹` be a weak solution
of `Δv = h (exp (2v) - 1) / 8 + k` on the plane with continuous coefficients, let `Ω` be the ball
of radius `2` about `c`, and let `u` be the precise representative of the restriction of `v` to `Ω`.
By Trudinger's inequality `exp (2u)` is square integrable on `Ω`, so the restriction is a weak
solution of `-Δu = F` on `Ω`, tested against `H¹₀(Ω)`, with `F = -(h (exp (2u) - 1) / 8 + k)`
in `L²(Ω)`. -/
private theorem memLp_and_forall_energyFormH1_eq (hh : Continuous h) (hk : Continuous k)
    {v : W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) ⊤ 2}
    (hv : ∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, ⟪W1p.gradient v x, ∇ φ x⟫) +
        ∫ x, (h x * (Real.exp (2 * W1p.value v x) - 1) / 8 + k x) * φ x = 0)
    {c : EuclideanSpace ℝ (Fin 2)} {Ω : Opens (EuclideanSpace ℝ (Fin 2))}
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin 2))) = ball c 2) {u : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hu : preciseRepresentative volume
      (W1p.value (W1p.restrictL (show Ω ≤ ⊤ from le_top) v) : EuclideanSpace ℝ (Fin 2) → ℝ) = u) :
    (W1p.value v : EuclideanSpace ℝ (Fin 2) → ℝ) =ᵐ[volume.restrict Ω] u ∧
      MemLp (fun x => -(h x * (Real.exp (2 * u x) - 1) / 8 + k x)) 2 (volume.restrict Ω) ∧
      ∀ w : W1p0 volume Ω 2, energyFormH1 (fun _ => 1) 0 0 (W1p.restrictL le_top v)
        (w : W1p volume Ω 2) = ∫ x in Ω, -(h x * (Real.exp (2 * u x) - 1) / 8 + k x) *
          W1p.value (w : W1p volume Ω 2) x := by
  have hvu : (W1p.value v : EuclideanSpace ℝ (Fin 2) → ℝ) =ᵐ[volume.restrict Ω] u :=
    hu ▸ (W1p.value_restrictL_ae _ v).symm.trans (ae_eq_restrict_preciseRepresentative Ω.isOpen
      (W1p.hasWeakFDerivOn _).locallyIntegrableOn)
  -- By Trudinger's inequality, `exp (4 |u|)` is integrable on `Ω`.
  have hexp : IntegrableOn (fun x => Real.exp (4 * |u x|)) (ball c 2) := by
    have h4 := (W1p.integrableOn_exp_mul_abs_value (by simp) (by simp) v
      (isCompact_closedBall c 2) (by simp) 4).mono_set ball_subset_closedBall
    refine h4.congr_fun_ae ?_
    rw [← hΩ]
    filter_upwards [hvu] with x hx
    rw [hx]
  have hum : AEStronglyMeasurable u (volume.restrict (ball c 2)) := by
    rw [← hΩ]
    exact ((Lp.aestronglyMeasurable (W1p.value v)).mono_measure
      (by simpa using Measure.restrict_le_self)).congr hvu
  have hF : MemLp (fun x => -(h x * (Real.exp (2 * u x) - 1) / 8 + k x)) 2
      (volume.restrict Ω) := by
    rw [hΩ]
    exact memLp_nonlinearity hh hk hum hexp
  exact ⟨hvu, hF, forall_energyFormH1_restrictL_top_eq_setIntegral hF
    (by filter_upwards [hvu] with x hx; simp [hx]) hv⟩

/-- **Local regularity on a ball.** A weak `H¹` solution of `Δv = h (exp (2v) - 1) / 8 + k` on the
plane with `C¹` coefficients agrees almost everywhere on each unit ball with a `C²` function that
solves the equation classically there. -/
private theorem exists_contDiffOn_ball (hh : ContDiff ℝ 1 h) (hk : ContDiff ℝ 1 k)
    {v : W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) ⊤ 2}
    (hv : ∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, ⟪W1p.gradient v x, ∇ φ x⟫) +
        ∫ x, (h x * (Real.exp (2 * W1p.value v x) - 1) / 8 + k x) * φ x = 0)
    (c : EuclideanSpace ℝ (Fin 2)) :
    ∃ g : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiffOn ℝ 2 g (ball c 1) ∧
      W1p.value v =ᵐ[volume.restrict (ball c 1)] g ∧
      ∀ x ∈ ball c 1, Δ g x = h x * (Real.exp (2 * g x) - 1) / 8 + k x := by
  -- The balls and the representative are introduced through equations, which keeps the
  -- elaboration of the regularity theorems below from unfolding them.
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : Opens (EuclideanSpace ℝ (Fin 2)), (Ω : Set _) = ball c 2 :=
    ⟨⟨ball c 2, isOpen_ball⟩, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Opens (EuclideanSpace ℝ (Fin 2)), (B : Set _) = ball c 1 :=
    ⟨⟨ball c 1, isOpen_ball⟩, rfl⟩
  have hBΩ : B ≤ Ω := by
    rw [← SetLike.coe_subset_coe, hΩ, hB]
    exact ball_subset_ball one_le_two
  obtain ⟨u, hu⟩ : ∃ u, preciseRepresentative volume
      (W1p.value (W1p.restrictL (show Ω ≤ ⊤ from le_top) v) : EuclideanSpace ℝ (Fin 2) → ℝ) = u :=
    ⟨_, rfl⟩
  -- On the ball `Ω` of radius `2` the solution solves Poisson's equation with `L²` data.
  obtain ⟨hvu, hF, hweak⟩ := memLp_and_forall_energyFormH1_eq hh.continuous hk.continuous hv hΩ hu
  -- De Giorgi's theorem makes `u` Hölder continuous on `B`, with an exponent `α / 2 < 1`.
  obtain ⟨α, C, hα, hα1, -, hdg⟩ := exists_holderOnWith_preciseRepresentative_of_memLp
    (ι := Fin 2) (mu := volume) (lam := 1) (Lam := 1) (r := 2) (by norm_num) (by norm_num)
  have hthick : cthickening (1 / 2) (ball c 1) ⊆ (Ω : Set (EuclideanSpace ℝ (Fin 2))) := by
    rw [cthickening_ball (by norm_num) one_pos, hΩ]
    exact closedBall_subset_ball (by norm_num)
  have hHα := hdg (uniformlyEllipticOn_const_one_one _) aestronglyMeasurable_const
    (by simpa using hF) hweak (by norm_num : (0 : ℝ) < 1 / 2) hthick
  rw [hu] at hHα
  have hβ0 : 0 < α / 2 := half_pos hα
  have hβ1 : α / 2 < 1 := (half_lt_self hα).trans_le hα1
  obtain ⟨Cβ, hHβ⟩ := HolderOnWith.exists_holderOnWith_of_le ⟨_, hHα⟩ (half_le_self α.2)
    isBounded_ball
  have huM : ∀ x ∈ ball c 1, |u x| ≤ |u c| + Cβ := fun x hx => by
    have hd := hHβ.dist_le_mul_rpow_of_mem_ball hx
    rw [Real.one_rpow, mul_one, Real.dist_eq] at hd
    exact sub_le_iff_le_add'.1 ((abs_sub_abs_le_abs_sub (u x) (u c)).trans hd)
  -- The data is then Hölder on `B`, and the precise representative is a classical solution.
  obtain ⟨K, hK⟩ := exists_holderOnWith_nonlinearity hh hk hβ1.le hHβ huM
  obtain ⟨hcd, hΔ⟩ := contDiffOn_preciseRepresentative_and_neg_laplacian_eq (n := 1) hβ0
    hβ1 hF hweak hBΩ fun x hx => ⟨ball c 1, isOpen_ball.mem_nhds (hB ▸ hx), K, hK⟩
  rw [hu, hB] at hcd
  rw [hu] at hΔ
  refine ⟨u, hcd, ?_, fun x hx => ?_⟩
  · rw [← hB]
    exact ae_restrict_of_ae_restrict_of_subset hBΩ hvu
  · have hx' := hΔ x (by rw [← SetLike.mem_coe, hB]; exact hx)
    linarith

/-- **Regularity on the Euclidean plane.** The precise representative of a weak `H¹` solution of
`Δv = h (exp (2v) - 1) / 8 + k` with `C¹` coefficients is a `C²` classical solution. -/
private theorem exists_contDiff_two_ae_eq_and_laplacian_eq_euclidean (hh : ContDiff ℝ 1 h)
    (hk : ContDiff ℝ 1 k) {v : W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) ⊤ 2}
    (hv : ∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, ⟪W1p.gradient v x, ∇ φ x⟫) +
        ∫ x, (h x * (Real.exp (2 * W1p.value v x) - 1) / 8 + k x) * φ x = 0) :
    ∃ w : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ 2 w ∧ W1p.value v =ᵐ[volume] w ∧
      ∀ x, Δ w x = h x * (Real.exp (2 * w x) - 1) / 8 + k x := by
  have hloc : LocallyIntegrableOn (W1p.value v : EuclideanSpace ℝ (Fin 2) → ℝ) univ volume := by
    simpa using (W1p.hasWeakFDerivOn v).locallyIntegrableOn
  -- On each unit ball the precise representative agrees with the local classical solution.
  have key : ∀ c, ∃ g : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiffOn ℝ 2 g (ball c 1) ∧
      preciseRepresentative volume (W1p.value v : EuclideanSpace ℝ (Fin 2) → ℝ) =ᶠ[𝓝 c] g ∧
      ∀ x ∈ ball c 1, Δ g x = h x * (Real.exp (2 * g x) - 1) / 8 + k x := fun c => by
    obtain ⟨g, hg, hvg, hΔ⟩ := exists_contDiffOn_ball hh hk hv c
    have heq := eqOn_preciseRepresentative_of_continuousOn isOpen_ball
      (hloc.mono_set (subset_univ _)) hvg hg.continuousOn
    exact ⟨g, hg, Filter.eventually_of_mem (ball_mem_nhds c one_pos) heq, hΔ⟩
  refine ⟨preciseRepresentative volume (W1p.value v : EuclideanSpace ℝ (Fin 2) → ℝ),
    contDiff_iff_contDiffAt.2 fun c => ?_, ?_, fun c => ?_⟩
  · obtain ⟨g, hg, hwg, -⟩ := key c
    exact (hg.contDiffAt (ball_mem_nhds c one_pos)).congr_of_eventuallyEq hwg
  · simpa using ae_eq_restrict_preciseRepresentative isOpen_univ hloc
  · obtain ⟨g, -, hwg, hΔ⟩ := key c
    rw [(laplacian_congr_nhds hwg).self_of_nhds, hwg.self_of_nhds]
    exact hΔ c (mem_ball_self one_pos)

end Euclidean

/-! ### Transfer to a plane -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {h k : E → ℝ}

/-- The weak form of Taubes's equation is invariant under linear isometries: if `u ∈ H¹(E)` is a
weak solution with coefficients `h`, `k`, then `u ∘ g⁻¹ ∈ H¹(F)` is a weak solution with
coefficients `h ∘ g⁻¹`, `k ∘ g⁻¹`, for every linear isometry `g : E ≃ F`. -/
private theorem weak_compAffineIsometryEquivL {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (g : E ≃ₗᵢ[ℝ] F) {u : W1p (volume : Measure E) ⊤ 2}
    (hu : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, ⟪W1p.gradient u x, ∇ φ x⟫) +
        ∫ x, (h x * (Real.exp (2 * W1p.value u x) - 1) / 8 + k x) * φ x = 0)
    (hUV : ((⊤ : Opens F) : Set F) = g.symm.toAffineIsometryEquiv ⁻¹' ((⊤ : Opens E) : Set E))
    (φ : F → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ x, ⟪W1p.gradient (W1p.compAffineIsometryEquivL g.symm.toAffineIsometryEquiv hUV u) x,
        ∇ φ x⟫) +
      ∫ x, ((h ∘ g.symm) x * (Real.exp (2 *
        W1p.value (W1p.compAffineIsometryEquivL g.symm.toAffineIsometryEquiv hUV u) x) - 1) / 8 +
          (k ∘ g.symm) x) * φ x = 0 := by
  have hval := W1p.value_compAffineIsometryEquivL_ae g.symm.toAffineIsometryEquiv hUV u
  have hgrad := W1p.gradient_compAffineIsometryEquivL_ae g.symm.toAffineIsometryEquiv hUV u
  simp only [Opens.coe_top, Measure.restrict_univ] at hval hgrad
  have hmp : MeasurePreserving g.symm volume volume := g.symm.measurePreserving
  have hemb : MeasurableEmbedding g.symm := g.symm.toHomeomorph.measurableEmbedding
  -- The gradient of `φ ∘ g` at `z` is `g⁻¹ (∇φ (g z))`.
  have hinner : ∀ z a, ⟪∇ (φ ∘ g) z, a⟫ = ⟪∇ φ (g z), g a⟫ := fun z a => by
    rw [gradient_comp_linearIsometryEquiv_right, ← g.inner_map_map, g.apply_symm_apply]
  -- Test the equation for `u` against `φ ∘ g`, and change variables by `g⁻¹`.
  have hψ := hu (φ ∘ g) (hφ.comp g.contDiff) (hφc.comp_homeomorph g.toHomeomorph)
  rw [← hmp.integral_comp hemb, ← hmp.integral_comp hemb] at hψ
  rw [← hψ]
  congr 1
  · refine integral_congr_ae ?_
    filter_upwards [hgrad] with x hx
    rw [hx, real_inner_comm (∇ (φ ∘ g) _), hinner, g.apply_symm_apply, real_inner_comm]
    simp
  · refine integral_congr_ae ?_
    filter_upwards [hval] with x hx
    simp [hx]

/-- **Weak solutions of Taubes's equation are classical.** Let `E` be a real inner product space
of dimension two, such as `ℂ`, and let `h`, `k` be `C¹` coefficients. If `u ∈ H¹(E)` solves
Taubes's equation `Δu = h (exp (2u) - 1) / 8 + k` weakly, that is

`∫ ⟪∇u, ∇φ⟫ + ∫ (h (exp (2u) - 1) / 8 + k) φ = 0`

for every compactly supported smooth `φ`, then `u` agrees almost everywhere with a `C²` function
`w` that solves the equation at every point. No sign, decay or integrability is assumed of the
coefficients, and nothing beyond `H¹(E)` of `u`. By Trudinger's inequality the second integrand
is integrable for every such `φ`, so the hypothesis is the weak equation in the usual sense. -/
theorem exists_contDiff_two_ae_eq_and_laplacian_eq (hE : finrank ℝ E = 2) (hh : ContDiff ℝ 1 h)
    (hk : ContDiff ℝ 1 k) {u : W1p (volume : Measure E) ⊤ 2}
    (hu : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, ⟪W1p.gradient u x, ∇ φ x⟫) +
        ∫ x, (h x * (Real.exp (2 * W1p.value u x) - 1) / 8 + k x) * φ x = 0) :
    ∃ w : E → ℝ, ContDiff ℝ 2 w ∧ W1p.value u =ᵐ[volume] w ∧
      ∀ x, Δ w x = h x * (Real.exp (2 * w x) - 1) / 8 + k x := by
  -- Transport `u` to the Euclidean plane along a linear isometry `g`.
  let g : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    ((stdOrthonormalBasis ℝ E).reindex (finCongr hE)).repr
  have hUV : ((⊤ : Opens (EuclideanSpace ℝ (Fin 2))) : Set (EuclideanSpace ℝ (Fin 2))) =
      g.symm.toAffineIsometryEquiv ⁻¹' ((⊤ : Opens E) : Set E) := by simp
  obtain ⟨w, hw, hvw, hΔ⟩ := exists_contDiff_two_ae_eq_and_laplacian_eq_euclidean
    (hh.comp g.symm.contDiff) (hk.comp g.symm.contDiff)
    (weak_compAffineIsometryEquivL g hu hUV)
  refine ⟨w ∘ g, hw.comp g.contDiff, ?_, fun x => ?_⟩
  · have hval := W1p.value_compAffineIsometryEquivL_ae g.symm.toAffineIsometryEquiv hUV u
    simp only [Opens.coe_top, Measure.restrict_univ] at hval
    simpa [Function.comp_def] using
      g.measurePreserving.quasiMeasurePreserving.ae_eq_comp (hval.symm.trans hvw)
  · rw [laplacian_comp_linearIsometryEquiv_right, Function.comp_apply, hΔ]
    simp

/-! ### The prescribed-zero vortex problem -/

/-- **A weak solution of the reduced vortex equation gives a vortex.** Let `f` be entire, and let
`u ∈ H¹(ℂ)` solve weakly the Euler–Lagrange equation `Δu = h (exp (2u) - 1) / 8 + k` of Taubes's
functional for the background coefficients `h = TauCeti.Vortex.backgroundWeight f` and
`k = TauCeti.Vortex.backgroundSource f`. Then `u` agrees almost everywhere with a `C²` function
`w` such that the field reconstructed from the amplitude `u₀ + w` and the section `f`, with `u₀`
the background amplitude, solves the vortex equations at every point. The degree-`m` end framing
of this field, which is equivalent to `w → 0` at infinity when `f` is a monic polynomial of degree
`m ≥ 1`, is not asserted. -/
theorem exists_contDiff_two_ae_eq_and_equation_amplitudeField_eq_zero {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ z, ⟪W1p.gradient u z, ∇ φ z⟫) +
        ∫ z, (backgroundWeight f z * (Real.exp (2 * W1p.value u z) - 1) / 8 +
          backgroundSource f z) * φ z = 0) :
    ∃ w : ℂ → ℝ, ContDiff ℝ 2 w ∧ W1p.value u =ᵐ[volume] w ∧
      ∀ z, equation (amplitudeField (fun z ↦ backgroundAmplitude f z + w z) f) z = 0 := by
  obtain ⟨w, hw, huw, hΔ⟩ := exists_contDiff_two_ae_eq_and_laplacian_eq Complex.finrank_real_complex
    (contDiff_backgroundWeight (hf.contDiff.restrict_scalars ℝ)) (contDiff_backgroundSource hf) hu
  exact ⟨w, hw, huw, fun z =>
    (laplacian_eq_iff_equation_amplitudeField_backgroundAmplitude_add_eq_zero (hf.analyticAt z)
      hw.contDiffAt).1 (hΔ z)⟩

end TauCeti.Vortex
