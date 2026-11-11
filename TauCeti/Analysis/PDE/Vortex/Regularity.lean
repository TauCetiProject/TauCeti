/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Inhomogeneous
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import TauCeti.Analysis.PDE.Regularity.Hessian.Classical
import TauCeti.Analysis.Sobolev.Trudinger

/-!
# Regularity of weak solutions of Taubes's reduced vortex equation

Let `E` be a real inner product space of dimension two and let `h, k` be continuous on an open set
`Ω ⊆ E`. The Euler–Lagrange equation of Taubes's functional `TauCeti.Vortex.taubesFunctional` is

`Δw = h (exp (2w) - 1) / 8 + k`

(`TauCeti.Vortex.forall_hasDerivAt_taubesFunctional_add_smul_iff`). For the background
coefficients of an entire function it is the reduced vortex equation, whose solutions decaying at
infinity give the plane vortices with prescribed zeros. Taubes obtains such a solution by minimizing
the functional over `H¹`, and the minimizer is a priori only a weak solution in `H¹`:

`∫_Ω ⟪∇w, ∇φ⟫ = -∫_Ω (h (exp (2w) - 1) / 8 + k) φ` for every test function `φ` on `Ω`.

This file proves that such a weak solution agrees almost everywhere with a function that is
continuous on `Ω`, so in particular it is locally bounded
(`TauCeti.Vortex.exists_continuousOn_ae_eq_of_forall_integral_inner_gradient_eq_neg`), and that it
is a classical `C²` solution when `h` and `k` are locally Hölder continuous, for instance smooth
(`exists_contDiffOn_two_ae_eq_and_laplacian_eq_of_forall_integral_inner_gradient_eq_neg`).

The difficulty is the exponential nonlinearity: in dimension two an `H¹` function need not be
bounded, so a priori `exp (2w)` is not even known to be locally integrable. Trudinger's inequality
resolves this. In its local form `TauCeti.W1p.integrableOn_exp_mul_abs_value`, `exp (c |w|)` is
integrable on every compact subset of `Ω` for every `c`, so the right-hand side lies in `L²` on
compact subsets of `Ω`. Since `2 > n / 2 = 1`, De Giorgi's theorem with a right-hand side then
applies, in the form
`TauCeti.PDE.exists_locally_holderOnWith_ae_eq_of_forall_integral_inner_gradient_eq` for weak
solutions of Poisson's equation with a locally integrable right-hand side: `w` has a locally Hölder
continuous representative `g₀`.

For the classical regularity, the right-hand side evaluated at `g₀` is the composite of the locally
Hölder map `x ↦ (h x, k x, g₀ x)` with the smooth, hence locally Lipschitz, map
`(a, b, t) ↦ a (exp (2t) - 1) / 8 + b`, so it is locally Hölder as well. The interior Schauder
theory for Poisson's equation with Hölder data,
`TauCeti.PDE.exists_contDiffOn_two_ae_eq_and_neg_laplacian_eq_of_forall_integral_inner_gradient_eq`,
then gives a `C²` representative solving the equation pointwise. The decay at infinity is not
treated here.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, Section 4.
* N. S. Trudinger, *On imbeddings into Orlicz spaces and some applications*, J. Math. Mech. 17
  (1967), 473–483.
-/

public section

noncomputable section

open InnerProductSpace Laplacian Metric MeasureTheory Module Set TopologicalSpace
open scoped Distributions ENNReal Gradient InnerProductSpace NNReal Topology

namespace TauCeti.Vortex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- On a compact subset of `Ω`, the right-hand side `h (exp (2w) - 1) / 8 + k` of the reduced
vortex equation is square integrable for every `w ∈ H¹(Ω)` in dimension two: `h` and `k` are
bounded there, and `exp (2w)` is square integrable by Trudinger's inequality. -/
private theorem memLp_neg_mul_exp_sub_one_div_eight_add (hE : finrank ℝ E = 2) {Omega : Opens E}
    {h k : E → ℝ} (hh : ContinuousOn h Omega) (hk : ContinuousOn k Omega) (w : W1p volume Omega 2)
    {K : Set E} (hK : IsCompact K) (hKO : K ⊆ Omega) :
    MemLp (fun x => -(h x * (Real.exp (2 * W1p.value w x) - 1) / 8 + k x)) 2
      (volume.restrict K) := by
  set f : E → ℝ := fun x => -(h x * (Real.exp (2 * W1p.value w x) - 1) / 8 + k x)
  -- On `K`, `|f| ≤ M exp (2 w) / 8 + 9 M / 8`, and `exp (2 w) ∈ L²(K)`.
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
  exact PDE.exists_continuousOn_ae_eq_of_forall_integral_inner_gradient_eq (r := 2) le_rfl
    (by rw [hE]; norm_num)
    (fun K hK hKO => memLp_neg_mul_exp_sub_one_div_eight_add hE hh hk w hK hKO)
    (fun φ => by simp only [neg_mul, integral_neg, hw])

/-- **Weak solutions of the reduced vortex equation are classical solutions.** Let `E` be a real
inner product space of dimension two, `Ω ⊆ E` open, and `h, k` locally `β`-Hölder on `Ω` for some
`β > 0`; smooth coefficients qualify. If `w ∈ H¹(Ω)` solves `Δw = h (exp (2w) - 1) / 8 + k` weakly
in `Ω`, that is

`∫_Ω ⟪∇w, ∇φ⟫ = -∫_Ω (h (exp (2w) - 1) / 8 + k) φ`

for every test function `φ` on `Ω`, then `w` agrees almost everywhere on `Ω` with a function `g`
of class `C²` on `Ω` which solves `Δg = h (exp (2g) - 1) / 8 + k` at every point of `Ω`. No sign
of `h` and no boundary condition on `w` is assumed. -/
theorem exists_contDiffOn_two_ae_eq_and_laplacian_eq_of_forall_integral_inner_gradient_eq_neg
    (hE : finrank ℝ E = 2) {Omega : Opens E} {h k : E → ℝ} {β : ℝ≥0} (hβ : 0 < β)
    (hh : ∀ x ∈ Omega, ∃ T ∈ 𝓝 x, ∃ K : ℝ≥0, HolderOnWith K β h T)
    (hk : ∀ x ∈ Omega, ∃ T ∈ 𝓝 x, ∃ K : ℝ≥0, HolderOnWith K β k T)
    {w : W1p volume Omega 2}
    (hw : ∀ φ : 𝓓(Omega, ℝ),
      ∫ x in Omega, ⟪W1p.gradient w x, ∇ (φ : E → ℝ) x⟫_ℝ =
        -∫ x in Omega, (h x * (Real.exp (2 * W1p.value w x) - 1) / 8 + k x) * φ x) :
    ∃ g : E → ℝ, ContDiffOn ℝ 2 g Omega ∧ W1p.value w =ᵐ[volume.restrict Omega] g ∧
      ∀ x ∈ Omega, Δ g x = h x * (Real.exp (2 * g x) - 1) / 8 + k x := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < finrank ℝ E)
  have hhc := continuousOn_of_locally_holderOnWith hβ hh
  have hkc := continuousOn_of_locally_holderOnWith hβ hk
  -- De Giorgi's theorem: `w` has a locally Hölder representative `g₀`.
  obtain ⟨α, hα, g₀, hg₀, hwg₀⟩ :=
    PDE.exists_locally_holderOnWith_ae_eq_of_forall_integral_inner_gradient_eq (r := 2) (u := w)
      le_rfl
      (by rw [hE]; norm_num)
      (fun K hK hKO => memLp_neg_mul_exp_sub_one_div_eight_add hE hhc hkc w hK hKO)
      (fun φ => by simp only [neg_mul, integral_neg, hw])
  -- The right-hand side, evaluated at `g₀`, is then locally Hölder with a common exponent `γ < 1`.
  set γ : ℝ≥0 := min (min α β) 2⁻¹
  have hγ : 0 < γ := lt_min (lt_min hα hβ) (by norm_num)
  have hγ1 : γ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hγα : γ ≤ α := (min_le_left _ _).trans (min_le_left _ _)
  have hγβ : γ ≤ β := (min_le_left _ _).trans (min_le_right _ _)
  set F : E → ℝ := fun x => -(h x * (Real.exp (2 * g₀ x) - 1) / 8 + k x)
  have hF : ∀ x ∈ Omega, ∃ T ∈ 𝓝 x, ∃ K : ℝ≥0, HolderOnWith K γ F T := by
    intro x hx
    obtain ⟨T₁, hT₁, K₁, h₁⟩ := hh x hx
    obtain ⟨T₂, hT₂, K₂, h₂⟩ := hk x hx
    obtain ⟨T₃, hT₃, K₃, h₃⟩ := hg₀ x hx
    obtain ⟨ε, hε, hεT⟩ := nhds_basis_closedBall.mem_iff.1
      (Filter.inter_mem (Filter.inter_mem hT₁ hT₂) hT₃)
    -- On the closed ball of radius `ε` about `x` the functions `h`, `k` and `g₀` are `γ`-Hölder.
    have hD : ∀ y ∈ closedBall x ε, ∀ z ∈ closedBall x ε,
        edist y z ≤ (((2 * ε).toNNReal : ℝ≥0) : ℝ≥0∞) := fun y hy z hz =>
      (edist_le_ofReal (by positivity)).2 <| (dist_triangle_right y z x).trans <| by
        rw [two_mul]
        exact add_le_add (mem_closedBall.1 hy) (mem_closedBall.1 hz)
    have h₁' := (h₁.mono (hεT.trans (inter_subset_left.trans inter_subset_left))).of_le hD hγβ
    have h₂' := (h₂.mono (hεT.trans (inter_subset_left.trans inter_subset_right))).of_le hD hγβ
    have h₃' := (h₃.mono (hεT.trans inter_subset_right)).of_le hD hγα
    have hP := h₁'.prodMk (h₂'.prodMk h₃')
    -- `Φ (a, b, t) = -(a (exp (2t) - 1) / 8 + b)` is Lipschitz on a ball containing the image.
    obtain ⟨R, hR⟩ := (isCompact_closedBall x ε).exists_bound_of_continuousOn
      (hP.continuousOn hγ)
    let Φ : ℝ × ℝ × ℝ → ℝ := fun p => -(p.1 * (Real.exp (2 * p.2.2) - 1) / 8 + p.2.1)
    have hΦ : ContDiff ℝ 1 Φ := by fun_prop
    obtain ⟨L, hL⟩ := hΦ.contDiffOn.exists_lipschitzOnWith one_ne_zero (convex_closedBall 0 R)
      (isCompact_closedBall 0 R)
    have hFS := (holderOnWith_one.2 hL).comp hP fun y hy => mem_closedBall_zero_iff.2 (hR y hy)
    rw [one_mul] at hFS
    exact ⟨closedBall x ε, closedBall_mem_nhds x hε, _, hFS⟩
  -- The weak equation holds with `g₀` in place of `w`, so Schauder theory makes it classical.
  have hwF : ∀ φ : 𝓓(Omega, ℝ),
      ∫ x in Omega, ⟪W1p.gradient w x, ∇ (φ : E → ℝ) x⟫_ℝ = ∫ x in Omega, F x * φ x := by
    intro φ
    rw [hw φ, ← integral_neg]
    refine integral_congr_ae (hwg₀.mono fun x hx => ?_)
    simp only [F, hx, neg_mul]
  obtain ⟨g, hg, hwg, hΔ⟩ :=
    PDE.exists_contDiffOn_two_ae_eq_and_neg_laplacian_eq_of_forall_integral_inner_gradient_eq
      hγ hγ1 hF hwF
  -- The two continuous representatives agree on `Ω`.
  have heq : EqOn g₀ g Omega := Measure.eqOn_open_of_ae_eq (hwg₀.symm.trans hwg) Omega.isOpen
    (continuousOn_of_locally_holderOnWith hα hg₀) hg.continuousOn
  refine ⟨g, hg, hwg, fun x hx => ?_⟩
  have := hΔ x hx
  simp only [F, heq hx] at this
  linarith

end TauCeti.Vortex
