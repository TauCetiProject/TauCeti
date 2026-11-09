/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Inhomogeneous
import TauCeti.Analysis.Sobolev.Trudinger

/-!
# Continuity of weak solutions of Taubes's reduced vortex equation

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
(`TauCeti.Vortex.exists_continuousOn_ae_eq_of_forall_integral_inner_gradient_eq_neg`).

The difficulty is the exponential nonlinearity: in dimension two an `H¹` function need not be
bounded, so a priori `exp (2w)` is not even known to be locally integrable. Trudinger's inequality
resolves this. In its local form `TauCeti.W1p.integrableOn_exp_mul_abs_value`, `exp (c |w|)` is
integrable on every compact subset of `Ω` for every `c`, so the right-hand side lies in `L²` on
compact subsets of `Ω`. Since `2 > n / 2 = 1`, De Giorgi's theorem with a right-hand side then
applies, in the form `TauCeti.PDE.exists_continuousOn_ae_eq_of_forall_integral_inner_gradient_eq`
for weak solutions of Poisson's equation with a locally integrable right-hand side.

Continuity makes the right-hand side locally bounded, which is the starting point of the bootstrap
to a smooth classical solution. That bootstrap and the decay at infinity are not treated here.

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

open InnerProductSpace MeasureTheory Module Set TopologicalSpace
open scoped Distributions Gradient InnerProductSpace NNReal

namespace TauCeti.Vortex

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

end TauCeti.Vortex
