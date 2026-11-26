/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import TauCeti.Analysis.Fourier.SineCosineSeries
public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
public import TauCeti.Analysis.PDE.ClassicalSolution
public import TauCeti.Analysis.PDE.IntervalDomain
public import TauCeti.Analysis.PDE.Spectrum.Basic
public import TauCeti.Analysis.PDE.Spectrum.Operator.Mixed
public import TauCeti.Analysis.Sobolev.W1p.BoundaryPart
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.Sobolev.W1p.MeasurePreserving
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Sobolev.W1p.Lipschitz
import TauCeti.Analysis.Sobolev.LipschitzDomain.RellichKondrachov
import TauCeti.Analysis.PDE.Neumann.SecondEigenvalue

/-!
# The Dirichlet, Neumann and mixed eigenvalues of `-Δ` on an interval

On a bounded open interval `(a, b)` the Dirichlet eigenvalue problem for `-Δ = -d²/dx²` can be
solved explicitly: its eigenvalues are exactly the numbers `(k π / (b - a))²`, `k ≥ 1`, with
eigenfunctions `x ↦ sin (k π (x - a) / (b - a))`. This is the model Sturm--Liouville problem, the
case of the general Dirichlet spectral theory of `TauCeti.PDE.IsDirichletEigenvalue` in which
the whole spectrum is explicit. In particular the first Dirichlet eigenvalue
is `(π / (b - a))²`, and by the Rayleigh principle this is the optimal constant in the Poincaré
inequality `C ∫_a^b u² ≤ ∫_a^b |u'|²` on `H¹₀(a, b)`.

The interval is realized as the open subset `TauCeti.PDE.intervalDomain a b` of the Euclidean line
`EuclideanSpace ℝ (Fin 1)`, the setting of the Sobolev spaces and the energy forms.

Each sine mode is `C^∞`, vanishes at `a` and `b` and satisfies `-Δw = (k π / (b - a))² w`
classically, so it is a weak Dirichlet eigenfunction
(`TauCeti.PDE.exists_value_ae_eq_and_energyFormH1_eq_of_laplacian_eq`). Conversely, the energy
form is symmetric, so an eigenfunction for any other `κ` is orthogonal in `L²(a, b)` to every
sine mode, and it vanishes by completeness of the sine system
(`TauCeti.ae_eq_zero_of_forall_integral_mul_sin_eq_zero`).

The same explicit description holds for the other boundary conditions of the mixed problem, posed
on the space `H¹_Γ(a, b)` of Sobolev functions vanishing on a boundary part `Γ`
(`TauCeti.w1pVanishingOnSubmodule`), with the weak eigenvalue problem `∫ ∇u · ∇v = κ ∫ u v` for
every `v ∈ H¹_Γ(a, b)`. On a domain with the Rellich property, the `κ` for which this problem has
a nonzero solution are the eigenvalues of the mixed Laplacian `-Δ_Γ`
(`TauCeti.PDE.spectrum_mixedOperator_laplacian`). The value map `W^{1,p}(a, b) → Lᵖ(a, b)` is
compact (Rellich), since the interval is a ball of the line, so for `Γ = ∅` these numbers are the
spectrum of the Neumann Laplacian `-Δ_∅`.

* With no Dirichlet part, `Γ = ∅`, the Neumann eigenvalues are the numbers `(k π / (b - a))²`,
  `k ≥ 0`, with eigenfunctions `cos (k π (x - a) / (b - a))`; the constants are the case `k = 0`.
* With the Dirichlet part `Γ = {a}`, the mixed eigenvalues are the numbers
  `((2k + 1) π / (2 (b - a)))²`, `k ≥ 0`, with eigenfunctions
  `sin ((2k + 1) π (x - a) / (2 (b - a)))`. The least one, `(π / (2 (b - a)))²`, lies between the
  least Neumann eigenvalue `0` and the least Dirichlet eigenvalue `(π / (b - a))²`.

Each mode `g` satisfies `g'' = -κ g` on the whole line. Integrating by parts against a generator `φ`
of `H¹_Γ(a, b)`, a test function on the line whose support misses `closure Γ`, leaves the boundary
term `g'(b) φ(b) - g'(a) φ(a)`, which vanishes: `g'` vanishes at each Neumann endpoint and `φ` at
each Dirichlet one. By density the mode is a weak eigenfunction. The Neumann modes are generators
themselves after multiplication by a bump equal to one near `[a, b]`; the mixed modes are
restrictions of the Dirichlet modes of the doubled interval `(a, 2b - a)`, symmetric about `b`.
Completeness of the cosines (`TauCeti.ae_eq_zero_of_forall_integral_mul_cos_eq_zero`) and of the
quarter-wave sines (`TauCeti.ae_eq_zero_of_forall_integral_mul_sin_two_mul_add_one_eq_zero`)
excludes every other eigenvalue.

For finite `p` the space `H¹_∅(a, b)` is all of `H¹(a, b)`
(`TauCeti.PDE.w1pVanishingOnSubmodule_empty_intervalDomain_eq_top`), so the Neumann eigenvalues are
also those of the weak problem tested on `H¹(a, b)`. On the connected interval the eigenvalue `0`
is simple, and the next one, the second Neumann eigenvalue `(π / (b - a))²`, is the minimum of the
Rayleigh quotient `‖∇u‖² / ‖u‖²` over the nonzero `u ∈ H¹(a, b)` of mean zero
(`TauCeti.PDE.exists_isLeast_neumannEigenvalue_pos_rayleigh_meanZero`). Its eigenfunctions are
exactly the minimizers, and the cosine `cos (π (x - a) / (b - a))` is one of them.

## Main declarations

* `TauCeti.PDE.exists_value_ae_eq_sin_and_energyFormH1_eq`: the sine modes are weak Dirichlet
  eigenfunctions.
* `TauCeti.PDE.energyFormH1_eq_of_value_ae_eq_sin`, `TauCeti.PDE.norm_value_sq_of_value_ae_eq_sin`
  and `TauCeti.PDE.energyFormH1_self_eq_of_value_ae_eq_sin`: every element of `H¹₀(a, b)` with a
  sine mode as value is an eigenfunction, with `L²` norm `√((b - a) / 2)` and the corresponding
  Dirichlet energy.
* `TauCeti.PDE.exists_lt_sq_natCast_mul_pi_div` and
  `TauCeti.PDE.exists_lt_and_energyFormH1_eq_intervalDomain`: the Dirichlet eigenvalues of `-Δ`
  on `(a, b)` are unbounded.
* `TauCeti.PDE.eq_zero_of_forall_setIntegral_mul_sin_eq_zero`: the sine modes are complete in
  `L²(a, b)`.
* `TauCeti.PDE.isDirichletEigenvalue_laplacian_intervalDomain_iff`: the Dirichlet spectrum of
  `-Δ` on `(a, b)` is `{(k π / (b - a))² | k ≥ 1}`.
* `TauCeti.PDE.isLeast_isDirichletEigenvalue_laplacian_intervalDomain` and
  `TauCeti.PDE.firstDirichletEigenvalue_laplacian_intervalDomain`: the first Dirichlet
  eigenvalue is `(π / (b - a))²`.
* `TauCeti.PDE.isGreatest_mul_norm_value_sq_le_energyFormH1_intervalDomain`: the sharp Poincaré
  inequality on `H¹₀(a, b)`, with constant `(π / (b - a))²`.
* `TauCeti.W1p.norm_value_le_div_pi_mul_norm_gradient_of_mem_w1p0Submodule`: the same inequality,
  `‖u‖_{L²} ≤ (b - a) / π ‖u'‖_{L²}`, for the Sobolev classes on the interval `(a, b)` of the real
  line, transported along the isometry `x ↦ x 0` of the Euclidean line onto `ℝ`.
* `TauCeti.PDE.exists_value_ae_eq_cos_and_inner_gradient_eq` and
  `TauCeti.PDE.exists_value_ae_eq_sin_two_mul_add_one_and_inner_gradient_eq`: the cosine modes are
  weak Neumann eigenfunctions, and the quarter-wave sine modes weak mixed eigenfunctions for the
  Dirichlet part `{a}`.
* `TauCeti.PDE.eq_zero_of_forall_setIntegral_mul_cos_eq_zero` and
  `TauCeti.PDE.eq_zero_of_forall_setIntegral_mul_sin_two_mul_add_one_eq_zero`: both systems are
  complete in `L²(a, b)`.
* `TauCeti.PDE.exists_ne_zero_forall_inner_gradient_eq_iff_intervalDomain_empty`: the weak
  Neumann eigenvalues of `-Δ` on `(a, b)`, tested on `H¹_∅(a, b)`, are
  `{(k π / (b - a))² | k ≥ 0}`.
* `TauCeti.PDE.exists_ne_zero_forall_inner_gradient_eq_iff_intervalDomain_left` and
  `TauCeti.PDE.isLeast_exists_ne_zero_forall_inner_gradient_eq_intervalDomain_left`: the weak
  mixed eigenvalues of `-Δ` on `(a, b)` with Dirichlet part `Γ = {a}`, tested on `H¹_Γ(a, b)`, are
  `{((2k + 1) π / (2 (b - a)))² | k ≥ 0}`, with least element `(π / (2 (b - a)))²`.
* `TauCeti.PDE.isCompactOperator_valueL_intervalDomain`: Rellich compactness of
  `W^{1,p}(a, b) → Lᵖ(a, b)`.
* `TauCeti.PDE.spectrum_mixedOperator_laplacian_empty_intervalDomain`: the spectrum of the
  Neumann Laplacian `-Δ_∅` on `(a, b)` is `{(k π / (b - a))² | k ≥ 0}`.
* `TauCeti.PDE.isLeast_neumannEigenvalue_pos_intervalDomain` and
  `TauCeti.PDE.isLeast_rayleigh_meanZero_intervalDomain`: the second Neumann eigenvalue
  `(π / (b - a))²` is the least positive one and the least Rayleigh quotient of mean zero.
* `TauCeti.PDE.forall_inner_gradient_eq_iff_intervalDomain` and
  `TauCeti.PDE.exists_value_ae_eq_cos_and_setIntegral_eq_zero_and_rayleigh_eq`: its
  eigenfunctions are the Rayleigh minimizers of mean zero, among them the first cosine mode.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Section 8.6
  (the Sturm--Liouville problem), §8.4, Example 5 (a boundary condition at one endpoint), and
  Section 9.8.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 6.5.1.
* R. Courant and D. Hilbert, *Methods of Mathematical Physics*, Vol. I, Chapter VI, §1 (the
  eigenvalues as minima of the Rayleigh quotient under orthogonality constraints, with natural
  boundary conditions when no boundary condition is imposed).
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Bornology InnerProductSpace Laplacian MeasureTheory Set TopologicalSpace
open scoped Real InnerProductSpace

variable {a b : ℝ}

attribute [local instance] W1p0.instNormedAddCommGroup

/-- The `k`-th Dirichlet mode `t ↦ sin (k π (t - a) / (b - a))` of the interval `(a, b)`. -/
private abbrev sineMode (a b : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  Real.sin (k * π * (t - a) / (b - a))

private theorem contDiff_sineMode (k : ℕ) : ContDiff ℝ ⊤ (sineMode a b k) := by
  unfold sineMode
  fun_prop

private theorem laplacian_sineMode (k : ℕ) (t : ℝ) :
    Δ (sineMode a b k) t = -(k * π / (b - a)) ^ 2 * sineMode a b k t := by
  have hd : ∀ s, HasDerivAt (sineMode a b k)
      (Real.cos (k * π * (s - a) / (b - a)) * (k * π / (b - a))) s := fun s => by
    have := (((hasDerivAt_id' s).sub_const a).const_mul (k * π)).div_const (b - a)
    convert this.sin using 1
    ring
  have hd2 : HasDerivAt (fun s => Real.cos (k * π * (s - a) / (b - a)) * (k * π / (b - a)))
      (-(k * π / (b - a)) ^ 2 * sineMode a b k t) t := by
    have := ((((hasDerivAt_id' t).sub_const a).const_mul (k * π)).div_const (b - a)).cos
    convert this.mul_const (k * π / (b - a)) using 1
    simp only [sineMode]
    ring
  rw [laplacian_eq_iteratedDeriv_real, iteratedDeriv_succ, iteratedDeriv_one,
    funext fun s => (hd s).deriv, hd2.deriv]

private theorem sineMode_left (k : ℕ) : sineMode a b k a = 0 := by
  simp [sineMode]

private theorem sineMode_right (hab : a < b) (k : ℕ) : sineMode a b k b = 0 := by
  rw [sineMode, mul_div_assoc, div_self (sub_pos.2 hab).ne', mul_one]
  exact Real.sin_nat_mul_pi k

/-- For `k ≥ 1`, the square of the `k`-th sine mode has integral `(b - a) / 2` over `(a, b)`. -/
private theorem integral_sineMode_sq {k : ℕ} (hk : 0 < k) :
    ∫ t in a..b, sineMode a b k t ^ 2 = (b - a) / 2 := by
  rcases eq_or_ne b a with rfl | hba
  · simp
  have hba : b - a ≠ 0 := sub_ne_zero.2 hba
  set c : ℝ := k * π / (b - a) with hc_def
  have hc : c ≠ 0 := div_ne_zero (mul_ne_zero (Nat.cast_ne_zero.2 hk.ne') Real.pi_ne_zero) hba
  have harg (t : ℝ) : sineMode a b k t ^ 2 = Real.sin (c * t - c * a) ^ 2 := by
    rw [sineMode, hc_def]
    congr 2
    field_simp
  simp_rw [harg]
  -- Substituting `y = c t - c a`, the integral is `∫₀^{kπ} sin² y dy / c = kπ / (2c)`.
  rw [intervalIntegral.integral_comp_mul_sub (fun y => Real.sin y ^ 2) hc, integral_sin_sq,
    sub_self, show c * b - c * a = k * π by rw [hc_def]; field_simp, Real.sin_nat_mul_pi,
    Real.sin_zero, smul_eq_mul, hc_def]
  field_simp
  ring

private theorem frontier_intervalDomain_subset (hab : a < b) :
    frontier (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))) ⊆ lineEquiv.symm ⁻¹' {a, b} := by
  rw [coe_intervalDomain_eq_preimage]
  exact (lineEquiv.symm.continuous.frontier_preimage_subset _).trans
    (preimage_mono (frontier_Ioo hab).subset)

/-- **The sine modes are weak Dirichlet eigenfunctions of `-Δ` on an interval.** For every
`k : ℕ`, the function `x ↦ sin (k π (x - a) / (b - a))` is the value of some `u ∈ H¹₀(a, b)` with

`∫ ∇u · ∇v = (k π / (b - a))² ∫ u v` for every `v ∈ H¹₀(a, b)`. -/
theorem exists_value_ae_eq_sin_and_energyFormH1_eq (hab : a < b) (k : ℕ) :
    ∃ u : W1p0 volume (intervalDomain a b) 2,
      W1p.value (u : W1p volume (intervalDomain a b) 2)
          =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
        (fun x => Real.sin (k * π * (x 0 - a) / (b - a))) ∧
      ∀ v : W1p0 volume (intervalDomain a b) 2,
        energyFormH1 (fun _ => 1) 0 0 (u : W1p volume (intervalDomain a b) 2)
            (v : W1p volume (intervalDomain a b) 2) =
          (k * π / (b - a)) ^ 2 * ⟪W1p.value (u : W1p volume (intervalDomain a b) 2),
            W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ := by
  obtain ⟨w, hw⟩ : ∃ w : EuclideanSpace ℝ (Fin 1) → ℝ, w = sineMode a b k ∘ lineEquiv.symm :=
    ⟨_, rfl⟩
  have hwc : ContDiff ℝ ⊤ w := hw ▸ (contDiff_sineMode k).comp lineEquiv.symm.contDiff
  have hw0 : ∀ x ∈ frontier (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))), w x = 0 := by
    intro x hx
    rcases frontier_intervalDomain_subset hab hx with h | h
    · simp only [hw, Function.comp_apply, h, sineMode_left]
    · simp only [hw, Function.comp_apply, mem_singleton_iff.1 h, sineMode_right hab]
  have hΔ : ∀ x ∈ (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))),
      Δ w x = -(k * π / (b - a)) ^ 2 * w x := fun x _ => by
    rw [hw, laplacian_comp_linearIsometryEquiv_right, Function.comp_apply, Function.comp_apply,
      laplacian_sineMode]
  obtain ⟨u, hu, heq⟩ := exists_value_ae_eq_and_energyFormH1_eq_of_laplacian_eq (mu := volume)
    isBounded_intervalDomain (hwc.of_le le_top).contDiffOn hwc.continuous.continuousOn hw0 hΔ
  refine ⟨u, hu.trans (Filter.EventuallyEq.of_eq ?_), heq⟩
  funext x
  simp only [hw, Function.comp_apply, lineEquiv_symm_apply]

/-- Every element of `H¹₀(a, b)` whose value is the sine mode `x ↦ sin (k π (x - a) / (b - a))`
is a weak Dirichlet eigenfunction of `-Δ`:

`∫ ∇u · ∇v = (k π / (b - a))² ∫ u v` for every `v ∈ H¹₀(a, b)`.

An element of `H¹₀(a, b)` is determined by its value, so this is the element of
`TauCeti.PDE.exists_value_ae_eq_sin_and_energyFormH1_eq`. -/
theorem energyFormH1_eq_of_value_ae_eq_sin (hab : a < b) (k : ℕ)
    {u : W1p0 volume (intervalDomain a b) 2}
    (hu : W1p.value (u : W1p volume (intervalDomain a b) 2)
      =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
        (fun x => Real.sin (k * π * (x 0 - a) / (b - a))))
    (v : W1p0 volume (intervalDomain a b) 2) :
    energyFormH1 (fun _ => 1) 0 0 (u : W1p volume (intervalDomain a b) 2)
        (v : W1p volume (intervalDomain a b) 2) =
      (k * π / (b - a)) ^ 2 * ⟪W1p0.valueL u, W1p0.valueL v⟫_ℝ := by
  -- `Exists.elim` rather than `obtain`, whose dependent eliminator has to abstract this goal.
  refine (exists_value_ae_eq_sin_and_energyFormH1_eq hab k).elim fun w hw => ?_
  have : u = w := Subtype.ext (W1p.ext_value (Lp.ext (hu.trans hw.1.symm)))
  rw [this, W1p0.valueL_apply, W1p0.valueL_apply]
  exact hw.2 v

/-- **The `L²` norm of a sine mode.** For `k ≥ 1`, an element of `H¹(a, b)` whose value is
`x ↦ sin (k π (x - a) / (b - a))` has `‖u‖²_{L²(a, b)} = (b - a) / 2`. -/
theorem norm_value_sq_of_value_ae_eq_sin (hab : a < b) {k : ℕ} (hk : 0 < k)
    {u : W1p volume (intervalDomain a b) 2}
    (hu : W1p.value u =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
      (fun x => Real.sin (k * π * (x 0 - a) / (b - a)))) :
    ‖W1p.value u‖ ^ 2 = (b - a) / 2 := by
  rw [← real_inner_self_eq_norm_sq, W1p.inner_value_eq_setIntegral,
    integral_congr_ae (g := fun x => sineMode a b k (x 0) ^ 2) (by
      filter_upwards [hu] with x hx
      rw [hx, sq]),
    setIntegral_intervalDomain (fun t => sineMode a b k t ^ 2), ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hab.le, integral_sineMode_sq hk]

/-- **The Dirichlet energy of a sine mode.** For `k ≥ 1`, an element of `H¹₀(a, b)` whose value
is `x ↦ sin (k π (x - a) / (b - a))` has `∫_a^b |u'|² = (k π / (b - a))² (b - a) / 2`. -/
theorem energyFormH1_self_eq_of_value_ae_eq_sin (hab : a < b) {k : ℕ} (hk : 0 < k)
    {u : W1p0 volume (intervalDomain a b) 2}
    (hu : W1p.value (u : W1p volume (intervalDomain a b) 2)
      =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
        (fun x => Real.sin (k * π * (x 0 - a) / (b - a)))) :
    energyFormH1 (fun _ => 1) 0 0 (u : W1p volume (intervalDomain a b) 2)
        (u : W1p volume (intervalDomain a b) 2) =
      (k * π / (b - a)) ^ 2 * ((b - a) / 2) := by
  rw [energyFormH1_eq_of_value_ae_eq_sin hab k hu u, real_inner_self_eq_norm_sq,
    W1p0.valueL_apply, norm_value_sq_of_value_ae_eq_sin hab hk hu]

/-- The Dirichlet eigenvalues `(k π / (b - a))²`, `k ≥ 1`, of `-Δ` on `(a, b)` are unbounded:
some of them exceed any given `C`. -/
theorem exists_lt_sq_natCast_mul_pi_div (hab : a ≠ b) (C : ℝ) :
    ∃ k : ℕ, 0 < k ∧ C < (k * π / (b - a)) ^ 2 := by
  have hq : 0 < π ^ 2 / (b - a) ^ 2 := by
    have := sub_ne_zero.2 hab.symm
    positivity
  obtain ⟨k, hk⟩ := exists_nat_gt (max 1 (C / (π ^ 2 / (b - a) ^ 2)))
  have hk1 : (1 : ℝ) < k := (le_max_left _ _).trans_lt hk
  have hkC : C / (π ^ 2 / (b - a) ^ 2) < k := (le_max_right _ _).trans_lt hk
  refine ⟨k, Nat.cast_pos.1 (zero_lt_one.trans hk1), ?_⟩
  rw [div_lt_iff₀ hq] at hkC
  have hsq : (k * π / (b - a)) ^ 2 = π ^ 2 / (b - a) ^ 2 * k ^ 2 := by
    rw [div_pow, mul_pow]
    ring
  rw [hsq]
  have hkk : (k : ℝ) ≤ k ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hkk hq.le]

/-- **The Dirichlet eigenvalues of `-Δ` on `(a, b)` are unbounded.** For every `C` there is a
weak Dirichlet eigenfunction `s ∈ H¹₀(a, b)` of `-Δ`, `s ≠ 0` in `L²(a, b)`, whose eigenvalue
`κ` exceeds `C`: a sine mode `x ↦ sin (k π (x - a) / (b - a))` with `(k π / (b - a))² > C`. -/
theorem exists_lt_and_energyFormH1_eq_intervalDomain (hab : a < b) (C : ℝ) :
    ∃ κ : ℝ, ∃ s : W1p0 volume (intervalDomain a b) 2, C < κ ∧ 0 < ‖W1p0.valueL s‖ ∧
      ∀ v : W1p0 volume (intervalDomain a b) 2,
        energyFormH1 (fun _ => 1) 0 0 (s : W1p volume (intervalDomain a b) 2)
            (v : W1p volume (intervalDomain a b) 2) =
          κ * ⟪W1p0.valueL s, W1p0.valueL v⟫_ℝ := by
  -- `Exists.elim` rather than `obtain`, whose dependent eliminator has to abstract this goal.
  refine (exists_lt_sq_natCast_mul_pi_div hab.ne C).elim fun k hk => ?_
  refine (exists_value_ae_eq_sin_and_energyFormH1_eq hab k).elim fun s hs => ?_
  have hnorm := norm_value_sq_of_value_ae_eq_sin hab hk.1 hs.1
  refine ⟨_, s, hk.2, ?_, energyFormH1_eq_of_value_ae_eq_sin hab k hs.1⟩
  rw [W1p0.valueL_apply]
  refine (norm_nonneg _).lt_of_ne fun h => ?_
  rw [← h] at hnorm
  linarith

/-- A class whose value is `x ↦ F (x 0)`, for a continuous `F` that does not vanish at some point
of `[a, b]`, has nonzero value. -/
private theorem value_ne_zero_of_value_ae_eq (hab : a < b) {F : ℝ → ℝ} (hF : Continuous F)
    {t : ℝ} (ht : t ∈ Icc a b) (hFt : F t ≠ 0) {u : W1p volume (intervalDomain a b) 2}
    (hu : W1p.value u =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
      fun x => F (x 0)) :
    W1p.value u ≠ 0 := by
  intro h0
  have hzero : EqOn (fun x : EuclideanSpace ℝ (Fin 1) => F (x 0)) 0 (intervalDomain a b) := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ (intervalDomain a b).isOpen
      (hF.comp (contDiff_piLp_apply 2 (𝕜 := ℝ) (n := 0)).continuous).continuousOn
      continuousOn_const
    filter_upwards [hu, Lp.coeFn_zero ℝ 2
      (volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))))] with x h1 h2
    rw [← h1, h0, h2]
  have hIoo : EqOn F 0 (Ioo a b) := fun s hs => by
    have := hzero (show lineEquiv s ∈ intervalDomain a b by
      rwa [mem_intervalDomain, lineEquiv_apply_zero])
    simpa [lineEquiv_apply_zero] using this
  exact hFt (hIoo.closure hF continuous_const (by rwa [closure_Ioo hab.ne]))

/-- `(k π / (b - a))²` is a Dirichlet eigenvalue of `-Δ` on `(a, b)` for every `k ≥ 1`, with
eigenfunction `x ↦ sin (k π (x - a) / (b - a))`. -/
theorem isDirichletEigenvalue_laplacian_intervalDomain (hab : a < b) {k : ℕ} (hk : 0 < k) :
    IsDirichletEigenvalue volume (intervalDomain a b) (fun _ => 1) 0 0
      ((k * π / (b - a)) ^ 2) := by
  obtain ⟨u, hu, heq⟩ := exists_value_ae_eq_sin_and_energyFormH1_eq hab k
  refine (isDirichletEigenvalue_iff_setIntegral _).2
    ⟨u, fun h0 => ?_, fun v => by rw [heq v, W1p.inner_value_eq_setIntegral]⟩
  have hba : 0 < b - a := sub_pos.2 hab
  -- The sine mode equals `1` at `a + (b - a) / (2k)`.
  refine value_ne_zero_of_value_ae_eq hab
    (F := fun t => Real.sin (k * π * (t - a) / (b - a))) (by fun_prop)
    (t := a + (b - a) / (2 * k)) ⟨?_, ?_⟩ ?_ hu (by rw [← W1p0.valueL_apply, h0, map_zero])
  · have : 0 ≤ (b - a) / (2 * k) := by positivity
    linarith
  · have hk1 : (1 : ℝ) ≤ k := Nat.one_le_cast.2 hk
    have : (b - a) / (2 * k) ≤ (b - a) / 2 :=
      div_le_div_of_nonneg_left hba.le two_pos (by linarith)
    linarith
  · rw [show k * π * (a + (b - a) / (2 * k) - a) / (b - a) = π / 2 by field_simp; ring,
      Real.sin_pi_div_two]
    exact one_ne_zero

/-- An element of `L²(a, b)` whose integrals against every `F i (x 0)` vanish is zero, when the
functions `F i` form a complete system among the integrable functions on `(a, b]`. -/
private theorem eq_zero_of_forall_setIntegral_mul_eq_zero_of_complete {ι : Type*} (hab : a < b)
    (F : ι → ℝ → ℝ)
    (hF : ∀ g : ℝ → ℝ, IntegrableOn g (Ioc a b) → (∀ i, ∫ t in a..b, g t * F i t = 0) →
      g =ᵐ[volume.restrict (Ioc a b)] 0)
    (f : Lp ℝ 2 (volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))))
    (h : ∀ i, ∫ x in intervalDomain a b, f x * F i (x 0) = 0) :
    f = 0 := by
  have hmp := measurePreserving_lineEquiv
  have hmpΩ : MeasurePreserving lineEquiv (volume.restrict (Ioo a b))
      (volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))) := by
    have := hmp.restrict_preimage (intervalDomain a b).isOpen.measurableSet
    rwa [preimage_lineEquiv_intervalDomain] at this
  have hmpΩ' : MeasurePreserving lineEquiv.symm
      (volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))))
      (volume.restrict (Ioo a b)) := by
    have := measurePreserving_lineEquiv_symm.restrict_preimage
      (measurableSet_Ioo (a := a) (b := b))
    rwa [← coe_intervalDomain_eq_preimage] at this
  -- Read `f` on the real line, where the system is complete.
  have hg : MemLp (fun t => f (lineEquiv t)) 2 (volume.restrict (Ioc a b)) := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact (Lp.memLp f).comp_measurePreserving hmpΩ
  have hg0 := hF _ (hg.integrable one_le_two) fun i => by
    rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo, ← h i,
      ← setIntegral_intervalDomain]
    simp only [← lineEquiv_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc] at hg0
  refine Lp.ext ?_
  filter_upwards [hmpΩ'.quasiMeasurePreserving.ae_eq_comp hg0, Lp.coeFn_zero ℝ 2
    (volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))))] with x h1 h2
  rw [h2]
  simpa using h1

/-- The sine modes are complete in `L²(a, b)`: an element of `L²(a, b)` orthogonal to every
`x ↦ sin (k π (x - a) / (b - a))`, `k ≥ 1`, is zero. -/
theorem eq_zero_of_forall_setIntegral_mul_sin_eq_zero (hab : a < b)
    (f : Lp ℝ 2 (volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))))
    (h : ∀ k : ℕ, 0 < k → ∫ x in intervalDomain a b,
      f x * Real.sin (k * π * (x 0 - a) / (b - a)) = 0) :
    f = 0 :=
  eq_zero_of_forall_setIntegral_mul_eq_zero_of_complete hab
    (fun (k : {k : ℕ // 0 < k}) t => Real.sin (k * π * (t - a) / (b - a)))
    (fun _ hg hgF => ae_eq_zero_of_forall_integral_mul_sin_eq_zero hg fun k hk => hgF ⟨k, hk⟩) f
    fun k => h k k.property

/-- **The Dirichlet spectrum of `-Δ` on an interval.** The Dirichlet eigenvalues of `-Δ` on
`(a, b)` are exactly the numbers `(k π / (b - a))²` with `k ≥ 1`: the homogeneous Dirichlet
problem `-Δu = κ u` in `(a, b)`, `u = 0` at `a` and `b`, has a nonzero weak solution in
`H¹₀(a, b)` exactly for these `κ`. -/
theorem isDirichletEigenvalue_laplacian_intervalDomain_iff (hab : a < b) {kappa : ℝ} :
    IsDirichletEigenvalue volume (intervalDomain a b) (fun _ => 1) 0 0 kappa ↔
      ∃ k : ℕ, 0 < k ∧ kappa = (k * π / (b - a)) ^ 2 := by
  refine ⟨fun hkappa => ?_, fun ⟨k, hk, hkappa⟩ => ?_⟩
  swap
  · rw [hkappa]
    exact isDirichletEigenvalue_laplacian_intervalDomain hab hk
  by_contra hne
  push Not at hne
  obtain ⟨u, hu0, hu⟩ := (isDirichletEigenvalue_iff kappa).1 hkappa
  refine hu0 (Subtype.ext (W1p.ext_value ?_))
  rw [ZeroMemClass.coe_zero, W1p.value_zero]
  -- `u` is orthogonal to every sine mode, since `κ` differs from each of their eigenvalues.
  refine eq_zero_of_forall_setIntegral_mul_sin_eq_zero hab _ fun k hk => ?_
  obtain ⟨s, hs, hseq⟩ := exists_value_ae_eq_sin_and_energyFormH1_eq hab k
  have hint := inner_value_eq_zero_of_energyFormH1_eq_of_ne
    (ae_of_all _ fun _ => Matrix.isSymm_one) (hne k hk) hu hseq
  rw [W1p.inner_value_eq_setIntegral] at hint
  refine (integral_congr_ae ?_).trans hint
  filter_upwards [hs] with x hx
  rw [hx]

/-- The first Dirichlet eigenvalue of `-Δ` on `(a, b)` is `(π / (b - a))²`, the least element of
the Dirichlet spectrum. -/
theorem isLeast_isDirichletEigenvalue_laplacian_intervalDomain (hab : a < b) :
    IsLeast {kappa | IsDirichletEigenvalue volume (intervalDomain a b) (fun _ => 1) 0 0 kappa}
      ((π / (b - a)) ^ 2) := by
  refine ⟨by simpa using isDirichletEigenvalue_laplacian_intervalDomain hab one_pos,
    fun kappa hkappa => ?_⟩
  obtain ⟨k, hk, rfl⟩ := (isDirichletEigenvalue_laplacian_intervalDomain_iff hab).1 hkappa
  gcongr
  exact le_mul_of_one_le_left Real.pi_pos.le (Nat.one_le_cast.2 hk)

/-- The interval domain `(a, b)` is nonempty exactly when `a < b`. -/
theorem nonempty_intervalDomain_iff :
    (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))).Nonempty ↔ a < b := by
  refine ⟨fun ⟨x, hx⟩ => (mem_intervalDomain.1 hx).1.trans (mem_intervalDomain.1 hx).2,
    fun hab => ⟨lineEquiv ((a + b) / 2), ?_⟩⟩
  rw [SetLike.mem_coe, mem_intervalDomain, ← lineEquiv_symm_apply,
    LinearIsometryEquiv.symm_apply_apply]
  constructor <;> linarith

/-- **The first Dirichlet eigenvalue of `-Δ` on an interval** `(a, b)` is `(π / (b - a))²`, for
any choice of the boundedness and coercivity data defining it. -/
theorem firstDirichletEigenvalue_laplacian_intervalDomain (hab : a < b)
    (hcoeff : MemLp (fun x ↦ energyIntegrand ((fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) x)
        ((0 : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) x)
        ((0 : EuclideanSpace ℝ (Fin 1) → ℝ) x)) ⊤
        (volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) :
    firstDirichletEigenvalue hcoeff hcoercive = (π / (b - a)) ^ 2 :=
  le_antisymm
    (firstDirichletEigenvalue_le hcoeff hcoercive
      (isLeast_isDirichletEigenvalue_laplacian_intervalDomain hab).1)
    ((isLeast_isDirichletEigenvalue_laplacian_intervalDomain hab).2
      (isDirichletEigenvalue_first hcoeff hcoercive isBounded_intervalDomain
        (fun _ _ => energyFormH1_one_zero_zero_comm _ _) (nonempty_intervalDomain_iff.2 hab)))

/-- **The sharp Poincaré inequality on an interval.** For every `u ∈ H¹₀(a, b)`,

`(π / (b - a))² ∫_a^b u² ≤ ∫_a^b |u'|²`,

and `(π / (b - a))²` is the largest constant for which this holds: it is the first Dirichlet
eigenvalue (`TauCeti.PDE.firstDirichletEigenvalue_laplacian_intervalDomain`). -/
theorem isGreatest_mul_norm_value_sq_le_energyFormH1_intervalDomain (hab : a < b) :
    IsGreatest {C : ℝ | ∀ u : W1p0 volume (intervalDomain a b) 2,
        C * ‖W1p.value (u : W1p volume (intervalDomain a b) 2)‖ ^ 2 ≤
          energyFormH1 (fun _ => 1) 0 0 (u : W1p volume (intervalDomain a b) 2)
            (u : W1p volume (intervalDomain a b) 2)}
      ((π / (b - a)) ^ 2) := by
  obtain ⟨hcoeff, hcoercive⟩ := exists_isCoercive_laplacian_of_isBounded (n := 0)
    isBounded_intervalDomain
  rw [← firstDirichletEigenvalue_laplacian_intervalDomain hab hcoeff hcoercive]
  exact isGreatest_firstDirichletEigenvalue hcoeff hcoercive
    (fun _ _ => energyFormH1_one_zero_zero_comm _ _)
    (nonempty_intervalDomain_iff.2 hab)

/-! ### The weak Neumann and mixed eigenvalues

The test space is `H¹_Γ(a, b)`, with `Γ = ∅` for the Neumann problem and `Γ = {a}` for the mixed
problem with a Dirichlet condition at `a` and a Neumann condition at `b`. -/

section Mixed

open scoped Distributions Gradient ContDiff ENNReal

attribute [local instance] W1pVanishingOn.instNormedAddCommGroup

/-- The cosine modes are complete in `L²(a, b)`: an element of `L²(a, b)` orthogonal to every
`x ↦ cos (k π (x - a) / (b - a))`, `k ≥ 0`, is zero. -/
theorem eq_zero_of_forall_setIntegral_mul_cos_eq_zero (hab : a < b)
    (f : Lp ℝ 2 (volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))))
    (h : ∀ k : ℕ, ∫ x in intervalDomain a b,
      f x * Real.cos (k * π * (x 0 - a) / (b - a)) = 0) :
    f = 0 :=
  eq_zero_of_forall_setIntegral_mul_eq_zero_of_complete hab
    (fun (k : ℕ) t => Real.cos (k * π * (t - a) / (b - a)))
    (fun _ hg hgF => ae_eq_zero_of_forall_integral_mul_cos_eq_zero hg hgF) f h

/-- The quarter-wave sine modes are complete in `L²(a, b)`: an element of `L²(a, b)` orthogonal
to every `x ↦ sin ((2k + 1) π (x - a) / (2 (b - a)))`, `k ≥ 0`, is zero. -/
theorem eq_zero_of_forall_setIntegral_mul_sin_two_mul_add_one_eq_zero (hab : a < b)
    (f : Lp ℝ 2 (volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))))
    (h : ∀ k : ℕ, ∫ x in intervalDomain a b,
      f x * Real.sin ((2 * k + 1) * π * (x 0 - a) / (2 * (b - a))) = 0) :
    f = 0 :=
  eq_zero_of_forall_setIntegral_mul_eq_zero_of_complete hab
    (fun (k : ℕ) t => Real.sin ((2 * k + 1) * π * (t - a) / (2 * (b - a))))
    (fun _ hg hgF => ae_eq_zero_of_forall_integral_mul_sin_two_mul_add_one_eq_zero hg hgF) f h

/-- The gradient of `x ↦ g (x 0)` on the Euclidean line is `g' (x 0)` along the unit vector. -/
private theorem gradient_comp_apply_zero (g : ℝ → ℝ) (x : EuclideanSpace ℝ (Fin 1)) :
    ∇ (fun y : EuclideanSpace ℝ (Fin 1) => g (y 0)) x = lineEquiv (deriv g (x 0)) := by
  have h : (fun y : EuclideanSpace ℝ (Fin 1) => g (y 0)) = g ∘ lineEquiv.symm := by
    funext y
    simp [lineEquiv_symm_apply]
  rw [h, gradient_comp_linearIsometryEquiv_right, LinearIsometryEquiv.symm_symm,
    gradient_eq_deriv', lineEquiv_symm_apply]

/-- **Integration by parts against a mode.** Let `g` satisfy `g'' = -κ g` on the line and let
`u ∈ H¹(a, b)` have value `x ↦ g (x 0)`. For a test function `φ` on the line, restricted to
`(a, b)`, `∫ ∇u · ∇φ = g'(b) φ(b) - g'(a) φ(a) + κ ∫ u φ`. -/
private theorem inner_gradient_restrictL_ofTestFunctionₗ_eq (hab : a ≤ b) {g g' : ℝ → ℝ}
    {kappa : ℝ} (hg : ∀ t, HasDerivAt g (g' t) t) (hg' : ∀ t, HasDerivAt g' (-kappa * g t) t)
    {u : W1p volume (intervalDomain a b) 2}
    (hu : W1p.value u =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
      fun x => g (x 0))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin 1))), ℝ)) :
    ⟪W1p.gradient u, W1p.gradient (W1p.restrictL le_top (W1p.ofTestFunctionₗ volume ⊤ 2 φ))⟫_ℝ =
      g' b * φ (lineEquiv b) - g' a * φ (lineEquiv a) + kappa *
        ⟪W1p.value u, W1p.value (W1p.restrictL le_top (W1p.ofTestFunctionₗ volume ⊤ 2 φ))⟫_ℝ := by
  set f : ℝ → ℝ := fun t => φ (lineEquiv t) with hf_def
  have hf : ContDiff ℝ 1 f :=
    (φ.contDiff.of_le (by exact_mod_cast le_top)).comp lineEquiv.contDiff
  have hφ : (φ : EuclideanSpace ℝ (Fin 1) → ℝ) = fun y => f (y 0) := by
    funext y
    simp [hf_def, ← lineEquiv_symm_apply]
  have hderiv : deriv g = g' := funext fun t => (hg t).deriv
  have hgc : ContDiff ℝ 1 g := contDiff_one_iff_deriv.2 ⟨fun t => (hg t).differentiableAt,
    hderiv ▸ continuous_iff_continuousAt.2 fun t => (hg' t).continuousAt⟩
  have hgrad := W1p.gradient_ae_eq_of_locallyLipschitzOn u hu
    (ContDiff.locallyLipschitz (hgc.comp (contDiff_piLp_apply 2))).locallyLipschitzOn
  have hgφ := W1p.gradient_restrictL_ofTestFunctionₗ_ae (mu := volume) (p := 2)
    (le_top : intervalDomain a b ≤ ⊤) φ
  have hvφ := W1p.value_restrictL_ofTestFunctionₗ_ae (mu := volume) (p := 2)
    (le_top : intervalDomain a b ≤ ⊤) φ
  -- Both pairings are integrals over the real interval.
  have hgrad_int : ⟪W1p.gradient u,
      W1p.gradient (W1p.restrictL le_top (W1p.ofTestFunctionₗ volume ⊤ 2 φ))⟫_ℝ =
        ∫ t in a..b, g' t * deriv f t := by
    rw [L2.inner_def, intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
      ← setIntegral_intervalDomain]
    refine integral_congr_ae ?_
    filter_upwards [hgrad, hgφ] with x h1 h2
    rw [h1, h2, hφ, gradient_comp_apply_zero, gradient_comp_apply_zero, hderiv,
      LinearIsometryEquiv.inner_map_map]
    simp [mul_comm]
  have hval_int : ⟪W1p.value u,
      W1p.value (W1p.restrictL le_top (W1p.ofTestFunctionₗ volume ⊤ 2 φ))⟫_ℝ =
        ∫ t in a..b, g t * f t := by
    rw [W1p.inner_value_eq_setIntegral, intervalIntegral.integral_of_le hab,
      integral_Ioc_eq_integral_Ioo, ← setIntegral_intervalDomain]
    refine integral_congr_ae ?_
    filter_upwards [hu, hvφ] with x h1 h2
    rw [h1, h2, hφ]
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun t _ => hg' t)
    (fun t _ => (hf.differentiable one_ne_zero t).hasDerivAt)
    (((hgc.continuous).const_mul (-kappa)).intervalIntegrable a b)
    ((hf.continuous_deriv le_rfl).intervalIntegrable a b)
  rw [hgrad_int, hval_int, hibp]
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- A mode `g` with `g'' = -κ g` on the line, read on `(a, b)`, is a weak eigenfunction tested
against all of `W^{1,2}_Γ(a, b)`, as soon as the boundary term `g'(b) φ(b) - g'(a) φ(a)` vanishes
for every generator `φ` of `W^{1,2}_Γ(a, b)`. -/
private theorem inner_gradient_eq_of_mem_w1pVanishingOnSubmodule (hab : a ≤ b) {g g' : ℝ → ℝ}
    {kappa : ℝ} (hg : ∀ t, HasDerivAt g (g' t) t) (hg' : ∀ t, HasDerivAt g' (-kappa * g t) t)
    {u : W1p volume (intervalDomain a b) 2}
    (hu : W1p.value u =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
      fun x => g (x 0))
    {Γ : Set (EuclideanSpace ℝ (Fin 1))}
    (hbd : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin 1))), ℝ),
      Disjoint (tsupport φ) (closure Γ) → g' b * φ (lineEquiv b) = g' a * φ (lineEquiv a))
    {v : W1p volume (intervalDomain a b) 2}
    (hv : v ∈ w1pVanishingOnSubmodule volume (intervalDomain a b) 2 Γ) :
    ⟪W1p.gradient u, W1p.gradient v⟫_ℝ = kappa * ⟪W1p.value u, W1p.value v⟫_ℝ := by
  refine w1pVanishingOnSubmodule_subset_of_isClosed (s := {v | ⟪W1p.gradient u,
      W1p.gradient v⟫_ℝ = kappa * ⟪W1p.value u, W1p.value v⟫_ℝ})
    (isClosed_eq (continuous_const.inner (W1p.gradientL.continuous.congr W1p.gradientL_apply))
      (continuous_const.mul (continuous_const.inner
        (W1p.valueL.continuous.congr W1p.valueL_apply)))) (fun φ hφ => ?_) hv
  rw [mem_ofPred_eq, inner_gradient_restrictL_ofTestFunctionₗ_eq hab hg hg' hu φ, hbd φ hφ,
    sub_self, zero_add]

/-- `t ↦ cos (c (t - a))` has derivative `-c sin (c (t - a))`. -/
private theorem hasDerivAt_cos_mul_sub (c t : ℝ) :
    HasDerivAt (fun s => Real.cos (c * (s - a))) (-c * Real.sin (c * (t - a))) t := by
  have := (((hasDerivAt_id' t).sub_const a).const_mul c).cos
  convert this using 1
  ring

/-- `t ↦ sin (c (t - a))` has derivative `c cos (c (t - a))`. -/
private theorem hasDerivAt_sin_mul_sub (c t : ℝ) :
    HasDerivAt (fun s => Real.sin (c * (s - a))) (c * Real.cos (c * (t - a))) t := by
  have := (((hasDerivAt_id' t).sub_const a).const_mul c).sin
  convert this using 1
  ring

/-- **The cosine modes are weak Neumann eigenfunctions of `-Δ` on an interval.** For every
`k : ℕ`, the function `x ↦ cos (k π (x - a) / (b - a))` is the value of some `u ∈ H¹_∅(a, b)`,
the closure in `H¹(a, b)` of the restrictions of test functions on the line, with

`∫ ∇u · ∇v = (k π / (b - a))² ∫ u v` for every `v ∈ H¹_∅(a, b)`. -/
theorem exists_value_ae_eq_cos_and_inner_gradient_eq (hab : a < b) (k : ℕ) :
    ∃ u : W1pVanishingOn volume (intervalDomain a b) 2 ∅,
      W1p.value (u : W1p volume (intervalDomain a b) 2)
          =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
        (fun x => Real.cos (k * π * (x 0 - a) / (b - a))) ∧
      ∀ v : W1pVanishingOn volume (intervalDomain a b) 2 ∅,
        ⟪W1p.gradient (u : W1p volume (intervalDomain a b) 2),
            W1p.gradient (v : W1p volume (intervalDomain a b) 2)⟫_ℝ =
          (k * π / (b - a)) ^ 2 * ⟪W1p.value (u : W1p volume (intervalDomain a b) 2),
            W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ := by
  set c : ℝ := k * π / (b - a) with hc
  have hmode (t : ℝ) : Real.cos (k * π * (t - a) / (b - a)) = Real.cos (c * (t - a)) := by
    rw [hc]
    ring_nf
  -- A bump equal to one on a ball containing `(a, b)` makes the mode a test function.
  let χ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 1)) :=
    ⟨|a| + |b| + 1, |a| + |b| + 2, by positivity, by linarith⟩
  have hχ : ∀ x ∈ (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))), χ x = 1 := fun x hx => by
    refine χ.one_of_mem_closedBall ?_
    rw [mem_closedBall_zero_iff, ← lineEquiv.symm.norm_map, lineEquiv_symm_apply,
      Real.norm_eq_abs, abs_le]
    obtain ⟨h1, h2⟩ := mem_intervalDomain.1 hx
    constructor <;> linarith [neg_abs_le a, le_abs_self b, abs_nonneg a, abs_nonneg b]
  let φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin 1))), ℝ) :=
    ⟨fun x => Real.cos (c * (x 0 - a)) * χ x, (Real.contDiff_cos.comp
      (((contDiff_piLp_apply 2).sub contDiff_const).const_smul c)).mul χ.contDiff,
      χ.hasCompactSupport.mul_left, subset_univ _⟩
  have hval := (W1p.value_restrictL_ofTestFunctionₗ_ae (mu := volume) (p := 2)
    (le_top : intervalDomain a b ≤ ⊤) φ).trans ((ae_restrict_iff'
      (intervalDomain a b).isOpen.measurableSet).2 (ae_of_all _ fun x hx => by
        rw [TestFunction.coe_mk, hχ x hx, mul_one]))
  refine ⟨⟨_, W1p.restrictL_ofTestFunctionₗ_mem_w1pVanishingOnSubmodule (φ := φ) (by simp)⟩,
    hval.trans (Filter.EventuallyEq.of_eq (funext fun x => (hmode (x 0)).symm)), fun v => ?_⟩
  refine inner_gradient_eq_of_mem_w1pVanishingOnSubmodule hab.le (hasDerivAt_cos_mul_sub c)
    (fun t => by
      convert (hasDerivAt_sin_mul_sub (a := a) c t).const_mul (-c) using 1
      ring) hval
    (fun ψ _ => ?_) v.property
  -- `g'` vanishes at both endpoints, since `c (b - a) = k π`.
  rw [show c * (b - a) = k * π by rw [hc]; field_simp [(sub_pos.2 hab).ne'],
    Real.sin_nat_mul_pi]
  simp

/-- **The quarter-wave sine modes are weak mixed eigenfunctions of `-Δ` on an interval**, with a
Dirichlet condition at `a` and a Neumann condition at `b`. For every `k : ℕ`, the function
`x ↦ sin ((2k + 1) π (x - a) / (2 (b - a)))` is the value of some `u ∈ H¹_Γ(a, b)`,
`Γ = {a}`, with

`∫ ∇u · ∇v = ((2k + 1) π / (2 (b - a)))² ∫ u v` for every `v ∈ H¹_Γ(a, b)`.

The mode is the restriction of the `(2k + 1)`-th Dirichlet mode of the doubled interval
`(a, 2b - a)`, symmetric about `b`. -/
theorem exists_value_ae_eq_sin_two_mul_add_one_and_inner_gradient_eq (hab : a < b) (k : ℕ) :
    ∃ u : W1pVanishingOn volume (intervalDomain a b) 2 {x | x 0 = a},
      W1p.value (u : W1p volume (intervalDomain a b) 2)
          =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
        (fun x => Real.sin ((2 * k + 1) * π * (x 0 - a) / (2 * (b - a)))) ∧
      ∀ v : W1pVanishingOn volume (intervalDomain a b) 2 {x | x 0 = a},
        ⟪W1p.gradient (u : W1p volume (intervalDomain a b) 2),
            W1p.gradient (v : W1p volume (intervalDomain a b) 2)⟫_ℝ =
          ((2 * k + 1) * π / (2 * (b - a))) ^ 2 *
            ⟪W1p.value (u : W1p volume (intervalDomain a b) 2),
              W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ := by
  set c : ℝ := (2 * k + 1) * π / (2 * (b - a)) with hc
  have hab' : a < 2 * b - a := by linarith
  have hle : intervalDomain a b ≤ intervalDomain a (2 * b - a) := fun x hx =>
    mem_intervalDomain.2
      ⟨(mem_intervalDomain.1 hx).1, (mem_intervalDomain.1 hx).2.trans (by linarith)⟩
  have hΓ : Disjoint {x : EuclideanSpace ℝ (Fin 1) | x 0 = a}
      (intervalDomain a (2 * b - a) : Set (EuclideanSpace ℝ (Fin 1))) :=
    disjoint_left.2 fun x hx hx' => (mem_intervalDomain.1 hx').1.ne' hx
  obtain ⟨s, hs, -⟩ := exists_value_ae_eq_sin_and_energyFormH1_eq hab' (2 * k + 1)
  have hval : W1p.value (W1p.restrictL hle (s : W1p volume (intervalDomain a (2 * b - a)) 2))
      =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
        fun x => Real.sin (c * (x 0 - a)) := by
    filter_upwards [W1p.value_restrictL_ae hle (s : W1p volume (intervalDomain a (2 * b - a)) 2),
      ae_restrict_of_ae_restrict_of_subset hle hs]
      with x h1 h2
    rw [h1, h2, hc]
    push_cast
    congr 1
    field_simp
    ring
  refine ⟨⟨_, W1p.restrictL_mem_w1pVanishingOnSubmodule hle hΓ s.property⟩,
    hval.trans (Filter.EventuallyEq.of_eq (funext fun x => by rw [hc]; ring_nf)), fun v => ?_⟩
  refine inner_gradient_eq_of_mem_w1pVanishingOnSubmodule hab.le (hasDerivAt_sin_mul_sub c)
    (fun t => by
      convert (hasDerivAt_cos_mul_sub (a := a) c t).const_mul c using 1
      ring) hval (fun ψ hψ => ?_) v.property
  -- `g'` vanishes at `b`, since `c (b - a) = k π + π / 2`, and `ψ` vanishes at `a`.
  have hψa : ψ (lineEquiv a) = 0 := image_eq_zero_of_notMem_tsupport fun h =>
    hψ.notMem_of_mem_left h (subset_closure (by simp [lineEquiv_apply_zero]))
  rw [hψa, show c * (b - a) = k * π + π / 2 by rw [hc]; field_simp,
    Real.cos_add_pi_div_two, Real.sin_nat_mul_pi]
  simp

/-- The weak eigenvalues of `-Δ` on `W^{1,2}_Γ(a, b)` are the eigenvalues of a family of weak
eigenfunctions, with values `x ↦ F k (x 0)`, that is complete in `L²(a, b)`: any other `κ` would
have its eigenfunctions orthogonal to the whole family, since the form `∫ ∇u · ∇v` is
symmetric. -/
private theorem exists_ne_zero_forall_inner_gradient_eq_iff_of_complete
    {Γ : Set (EuclideanSpace ℝ (Fin 1))} {kappas : ℕ → ℝ} (F : ℕ → ℝ → ℝ)
    (w : ℕ → W1pVanishingOn volume (intervalDomain a b) 2 Γ)
    (hwv : ∀ k, W1p.value (w k : W1p volume (intervalDomain a b) 2)
      =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
        fun x => F k (x 0))
    (hw0 : ∀ k, W1p.value (w k : W1p volume (intervalDomain a b) 2) ≠ 0)
    (hw : ∀ k, ∀ v : W1pVanishingOn volume (intervalDomain a b) 2 Γ,
      ⟪W1p.gradient (w k : W1p volume (intervalDomain a b) 2),
          W1p.gradient (v : W1p volume (intervalDomain a b) 2)⟫_ℝ =
        kappas k * ⟪W1p.value (w k : W1p volume (intervalDomain a b) 2),
          W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ)
    (hc : ∀ f : Lp ℝ 2 (volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))),
      (∀ k, ∫ x in intervalDomain a b, f x * F k (x 0) = 0) → f = 0)
    {kappa : ℝ} :
    (∃ u : W1pVanishingOn volume (intervalDomain a b) 2 Γ, u ≠ 0 ∧
      ∀ v : W1pVanishingOn volume (intervalDomain a b) 2 Γ,
        ⟪W1p.gradient (u : W1p volume (intervalDomain a b) 2),
            W1p.gradient (v : W1p volume (intervalDomain a b) 2)⟫_ℝ =
          kappa * ⟪W1p.value (u : W1p volume (intervalDomain a b) 2),
            W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ) ↔
      ∃ k, kappa = kappas k := by
  constructor
  · rintro ⟨u, hu0, hu⟩
    by_contra hne
    push Not at hne
    refine hu0 (W1pVanishingOn.valueL_injective ?_)
    rw [map_zero, W1pVanishingOn.valueL_apply]
    refine hc _ fun k => ?_
    -- `κ ⟪u, w k⟫ = ∫ ∇u · ∇(w k) = κₖ ⟪u, w k⟫`, and `κ ≠ κₖ`.
    have h1 := hu (w k)
    rw [real_inner_comm, hw k u, real_inner_comm (W1p.value _)] at h1
    have h2 : (kappa - kappas k) * ⟪W1p.value (u : W1p volume (intervalDomain a b) 2),
        W1p.value (w k : W1p volume (intervalDomain a b) 2)⟫_ℝ = 0 := by
      linarith
    rw [← (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (hne k)), L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hwv k] with x hx
    simp [hx, mul_comm]
  · rintro ⟨k, rfl⟩
    refine ⟨w k, fun h => hw0 k ?_, hw k⟩
    rw [← W1pVanishingOn.valueL_apply, h, map_zero]

/-- **The weak Neumann eigenvalues of `-Δ` on an interval.** On `(a, b)` they are exactly the
numbers `(k π / (b - a))²` with `k ≥ 0`: the problem
`∫ ∇u · ∇v = κ ∫ u v` for every `v ∈ H¹_∅(a, b)` has a nonzero solution `u ∈ H¹_∅(a, b)`,
imposing `u'(a) = u'(b) = 0` weakly, exactly for these `κ`. Here `H¹_∅(a, b)` is the space of the
mixed problem with no Dirichlet part, as in the spectrum of the mixed Laplacian
(`TauCeti.PDE.spectrum_mixedOperator_laplacian`): the closure in `H¹(a, b)` of the restrictions of
test functions on the line. It is all of `H¹(a, b)`
(`TauCeti.PDE.w1pVanishingOnSubmodule_empty_intervalDomain_eq_top`), so these are also the weak
Neumann eigenvalues tested on `H¹(a, b)`. These numbers are the spectrum of the Neumann Laplacian
(`TauCeti.PDE.spectrum_mixedOperator_laplacian_empty_intervalDomain`). -/
theorem exists_ne_zero_forall_inner_gradient_eq_iff_intervalDomain_empty (hab : a < b)
    {kappa : ℝ} :
    (∃ u : W1pVanishingOn volume (intervalDomain a b) 2 ∅, u ≠ 0 ∧
      ∀ v : W1pVanishingOn volume (intervalDomain a b) 2 ∅,
        ⟪W1p.gradient (u : W1p volume (intervalDomain a b) 2),
            W1p.gradient (v : W1p volume (intervalDomain a b) 2)⟫_ℝ =
          kappa * ⟪W1p.value (u : W1p volume (intervalDomain a b) 2),
            W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ) ↔
      ∃ k : ℕ, kappa = (k * π / (b - a)) ^ 2 := by
  choose w hwv hw using exists_value_ae_eq_cos_and_inner_gradient_eq hab
  refine exists_ne_zero_forall_inner_gradient_eq_iff_of_complete
    (fun k t => Real.cos (k * π * (t - a) / (b - a))) w hwv (fun k => ?_) hw
    (eq_zero_of_forall_setIntegral_mul_cos_eq_zero hab)
  exact value_ne_zero_of_value_ae_eq hab (F := fun t => Real.cos (k * π * (t - a) / (b - a)))
    (by fun_prop) (left_mem_Icc.2 hab.le) (by simp) (hwv k)

/-- **The weak mixed eigenvalues of `-Δ` on an interval with one Dirichlet endpoint.** With the
Dirichlet part `Γ = {a}`, the weak mixed eigenvalues of `-Δ` on `(a, b)` are exactly the numbers
`((2k + 1) π / (2 (b - a)))²` with `k ≥ 0`: the problem `∫ ∇u · ∇v = κ ∫ u v` for every
`v ∈ H¹_Γ(a, b)` has a nonzero solution `u ∈ H¹_Γ(a, b)`, imposing `u(a) = 0` and `u'(b) = 0`,
exactly for these `κ`. -/
theorem exists_ne_zero_forall_inner_gradient_eq_iff_intervalDomain_left (hab : a < b)
    {kappa : ℝ} :
    (∃ u : W1pVanishingOn volume (intervalDomain a b) 2 {x | x 0 = a}, u ≠ 0 ∧
      ∀ v : W1pVanishingOn volume (intervalDomain a b) 2 {x | x 0 = a},
        ⟪W1p.gradient (u : W1p volume (intervalDomain a b) 2),
            W1p.gradient (v : W1p volume (intervalDomain a b) 2)⟫_ℝ =
          kappa * ⟪W1p.value (u : W1p volume (intervalDomain a b) 2),
            W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ) ↔
      ∃ k : ℕ, kappa = ((2 * k + 1) * π / (2 * (b - a))) ^ 2 := by
  choose w hwv hw using exists_value_ae_eq_sin_two_mul_add_one_and_inner_gradient_eq hab
  refine exists_ne_zero_forall_inner_gradient_eq_iff_of_complete
    (fun k t => Real.sin ((2 * k + 1) * π * (t - a) / (2 * (b - a)))) w hwv (fun k => ?_) hw
    (eq_zero_of_forall_setIntegral_mul_sin_two_mul_add_one_eq_zero hab)
  -- At `b` the mode is `sin (k π + π / 2) = ± 1`.
  refine value_ne_zero_of_value_ae_eq hab
    (F := fun t => Real.sin ((2 * k + 1) * π * (t - a) / (2 * (b - a)))) (by fun_prop)
    (right_mem_Icc.2 hab.le) ?_ (hwv k)
  rw [show (2 * k + 1) * π * (b - a) / (2 * (b - a)) = k * π + π / 2 by
    field_simp [(sub_pos.2 hab).ne'], Real.sin_add_pi_div_two, Real.cos_nat_mul_pi]
  exact pow_ne_zero _ (by norm_num)

/-- The least weak mixed eigenvalue of `-Δ` on `(a, b)` with the Dirichlet part `{a}` is
`(π / (2 (b - a)))²`. It lies strictly between the least Neumann eigenvalue `0` and the least
Dirichlet eigenvalue `(π / (b - a))²`. -/
theorem isLeast_exists_ne_zero_forall_inner_gradient_eq_intervalDomain_left (hab : a < b) :
    IsLeast {kappa | ∃ u : W1pVanishingOn volume (intervalDomain a b) 2 {x | x 0 = a}, u ≠ 0 ∧
      ∀ v : W1pVanishingOn volume (intervalDomain a b) 2 {x | x 0 = a},
        ⟪W1p.gradient (u : W1p volume (intervalDomain a b) 2),
            W1p.gradient (v : W1p volume (intervalDomain a b) 2)⟫_ℝ =
          kappa * ⟪W1p.value (u : W1p volume (intervalDomain a b) 2),
            W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ}
      ((π / (2 * (b - a))) ^ 2) := by
  refine ⟨(exists_ne_zero_forall_inner_gradient_eq_iff_intervalDomain_left hab).2
    ⟨0, by simp⟩, fun kappa hkappa => ?_⟩
  obtain ⟨k, rfl⟩ := (exists_ne_zero_forall_inner_gradient_eq_iff_intervalDomain_left hab).1 hkappa
  gcongr
  nlinarith [Real.pi_pos, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- **Rellich compactness on an interval.** For `1 ≤ p ≤ ∞`, the value map
`W^{1,p}(a, b) → Lᵖ(a, b)` is a compact operator, since the interval is a ball of the line
(`TauCeti.PDE.coe_intervalDomain_eq_ball`). -/
theorem isCompactOperator_valueL_intervalDomain {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    IsCompactOperator (W1p.valueL (mu := volume) (Omega := intervalDomain a b) (p := p)) := by
  have h : intervalDomain a b =
      ⟨Metric.ball (lineEquiv ((a + b) / 2)) ((b - a) / 2), Metric.isOpen_ball⟩ :=
    Opens.ext coe_intervalDomain_eq_ball
  rw [h]
  exact W1p.isCompactOperator_valueL_ball _ _

/-- **The spectrum of the Neumann Laplacian on an interval.** The mixed Laplacian `-Δ_∅` on
`(a, b)`, the self-adjoint realization of `-d²/dx²` with the Neumann condition `u' = 0` at both
ends, has spectrum `{(k π / (b - a))² | k ≥ 0}`. Each cosine mode is an eigenfunction
(`TauCeti.PDE.exists_value_ae_eq_cos_and_inner_gradient_eq`). -/
theorem spectrum_mixedOperator_laplacian_empty_intervalDomain (hab : a < b) :
    (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := volume)
      (Omega := intervalDomain a b) (1 : Matrix (Fin 1) (Fin 1) ℝ)) ∅).spectrum =
      {kappa | ∃ k : ℕ, kappa = (k * π / (b - a)) ^ 2} := by
  rw [spectrum_mixedOperator_laplacian (empty_disjoint _)
    isCompactOperator_valueL_intervalDomain]
  ext kappa
  exact exists_ne_zero_forall_inner_gradient_eq_iff_intervalDomain_empty hab

/-! ### The Neumann spectrum tested on `H¹(a, b)` and the second Neumann eigenvalue -/

/-- The weak Neumann eigenvalues of `-Δ` on `(a, b)` tested on `H¹(a, b)` are those tested on
`H¹_∅(a, b)`, the numbers `(k π / (b - a))²`, since the two spaces agree. -/
private theorem exists_ne_zero_forall_inner_gradient_eq_iff_intervalDomain (hab : a < b)
    {kappa : ℝ} :
    (∃ u : W1p volume (intervalDomain a b) 2, u ≠ 0 ∧ ∀ v : W1p volume (intervalDomain a b) 2,
        ⟪W1p.gradient u, W1p.gradient v⟫_ℝ = kappa * ⟪W1p.value u, W1p.value v⟫_ℝ) ↔
      ∃ k : ℕ, kappa = (k * π / (b - a)) ^ 2 := by
  rw [← exists_ne_zero_forall_inner_gradient_eq_iff_intervalDomain_empty hab]
  constructor
  · rintro ⟨u, hu, h⟩
    exact ⟨⟨u, mem_w1pVanishingOnSubmodule_empty_intervalDomain ENNReal.ofNat_ne_top u⟩,
      fun h0 => hu (congrArg Subtype.val h0), fun v => h v⟩
  · rintro ⟨u, hu, h⟩
    exact ⟨u, fun h0 => hu (Subtype.ext h0),
      fun v => h ⟨v, mem_w1pVanishingOnSubmodule_empty_intervalDomain ENNReal.ofNat_ne_top v⟩⟩

/-- **The second Neumann eigenvalue of an interval.** The least positive weak Neumann eigenvalue of
`-Δ` on `(a, b)`, tested on `H¹(a, b)`, is `(π / (b - a))²`. Counted with multiplicity it is the
second one, after the simple eigenvalue `0` of the constants. -/
theorem isLeast_neumannEigenvalue_pos_intervalDomain (hab : a < b) :
    IsLeast {kappa | 0 < kappa ∧ ∃ u : W1p volume (intervalDomain a b) 2, u ≠ 0 ∧
      ∀ v : W1p volume (intervalDomain a b) 2,
        ⟪W1p.gradient u, W1p.gradient v⟫_ℝ = kappa * ⟪W1p.value u, W1p.value v⟫_ℝ}
      ((π / (b - a)) ^ 2) := by
  refine ⟨⟨pow_pos (div_pos Real.pi_pos (sub_pos.2 hab)) 2,
    (exists_ne_zero_forall_inner_gradient_eq_iff_intervalDomain hab).2 ⟨1, by simp⟩⟩, ?_⟩
  rintro kappa ⟨hpos, hkappa⟩
  obtain ⟨k, rfl⟩ := (exists_ne_zero_forall_inner_gradient_eq_iff_intervalDomain hab).1 hkappa
  have hk : k ≠ 0 := by
    rintro rfl
    simp at hpos
  gcongr
  exact le_mul_of_one_le_left Real.pi_pos.le (Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 hk))

/-- **The second Neumann eigenvalue of an interval is the least Rayleigh quotient of mean zero.**
The minimum of `‖∇u‖² / ‖u‖²` over the `u ∈ H¹(a, b)` with `u ≠ 0` and `∫_a^b u = 0` is
`(π / (b - a))²`, the least positive weak Neumann eigenvalue
(`TauCeti.PDE.isLeast_neumannEigenvalue_pos_intervalDomain`). The lower bound is the sharp
inequality `∫_a^b u² ≤ ((b - a) / π)² ∫_a^b u'²` for `u ∈ H¹(a, b)` of mean zero, the Neumann
case of Wirtinger's inequality for arcs (`TauCeti.exists_mem_integral_norm_sub_sq_le`), and the
first cosine mode attains it. -/
theorem isLeast_rayleigh_meanZero_intervalDomain (hab : a < b) :
    IsLeast {r | ∃ u : W1p volume (intervalDomain a b) 2, W1p.value u ≠ 0 ∧
        ∫ x in intervalDomain a b, W1p.value u x = 0 ∧
        r = ‖W1p.gradient u‖ ^ 2 / ‖W1p.value u‖ ^ 2}
      ((π / (b - a)) ^ 2) := by
  obtain ⟨kappa, h1, h2⟩ := exists_isLeast_neumannEigenvalue_pos_rayleigh_meanZero
    isCompactOperator_valueL_intervalDomain (isPreconnected_intervalDomain a b)
    (nonempty_intervalDomain_iff.2 hab)
  rwa [h1.unique (isLeast_neumannEigenvalue_pos_intervalDomain hab)] at h2

/-- **The eigenfunctions of the second Neumann eigenvalue of an interval are the Rayleigh
minimizers of mean zero.** A class `u ∈ H¹(a, b)` satisfies
`∫ ∇u · ∇v = (π / (b - a))² ∫ u v` for every `v ∈ H¹(a, b)` exactly when `∫_a^b u = 0` and
`‖∇u‖² = (π / (b - a))² ‖u‖²`. -/
theorem forall_inner_gradient_eq_iff_intervalDomain (u : W1p volume (intervalDomain a b) 2) :
    (∀ v : W1p volume (intervalDomain a b) 2,
        ⟪W1p.gradient u, W1p.gradient v⟫_ℝ =
          (π / (b - a)) ^ 2 * ⟪W1p.value u, W1p.value v⟫_ℝ) ↔
      ∫ x in intervalDomain a b, W1p.value u x = 0 ∧
        ‖W1p.gradient u‖ ^ 2 = (π / (b - a)) ^ 2 * ‖W1p.value u‖ ^ 2 := by
  rcases le_or_gt b a with hba | hab
  · -- On an empty interval every class is zero, and both sides hold.
    have h0 : volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))) = 0 := by
      rw [Measure.restrict_eq_zero, Set.not_nonempty_iff_eq_empty.1
        (mt nonempty_intervalDomain_iff.1 (not_lt.2 hba)), measure_empty]
    obtain rfl : u = 0 := W1p.ext_value <| Lp.ext <| by simp [h0, Filter.EventuallyEq]
    simp [h0]
  exact forall_inner_gradient_eq_iff_of_isLeast_neumannEigenvalue_pos
    isCompactOperator_valueL_intervalDomain (isPreconnected_intervalDomain a b)
    (isLeast_neumannEigenvalue_pos_intervalDomain hab) u

/-- **The second Neumann eigenvalue of an interval is attained by the first cosine mode.** Some
`u ∈ H¹(a, b)` with value `x ↦ cos (π (x - a) / (b - a))` has mean zero and Rayleigh quotient
`‖∇u‖² / ‖u‖² = (π / (b - a))²`. -/
theorem exists_value_ae_eq_cos_and_setIntegral_eq_zero_and_rayleigh_eq (hab : a < b) :
    ∃ u : W1p volume (intervalDomain a b) 2,
      W1p.value u =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
        (fun x => Real.cos (π * (x 0 - a) / (b - a))) ∧
      ∫ x in intervalDomain a b, W1p.value u x = 0 ∧
      ‖W1p.gradient u‖ ^ 2 / ‖W1p.value u‖ ^ 2 = (π / (b - a)) ^ 2 := by
  obtain ⟨w, hwv, hw⟩ := exists_value_ae_eq_cos_and_inner_gradient_eq hab 1
  have hv : W1p.value (w : W1p volume (intervalDomain a b) 2)
      =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
        (fun x => Real.cos (π * (x 0 - a) / (b - a))) := by
    simpa only [Nat.cast_one, one_mul] using hwv
  obtain ⟨hmean, hnorm⟩ := (forall_inner_gradient_eq_iff_intervalDomain w).1 fun v => by
    simpa only [Nat.cast_one, one_mul] using
      hw ⟨v, mem_w1pVanishingOnSubmodule_empty_intervalDomain ENNReal.ofNat_ne_top v⟩
  have hne : W1p.value (w : W1p volume (intervalDomain a b) 2) ≠ 0 :=
    value_ne_zero_of_value_ae_eq hab (F := fun t => Real.cos (π * (t - a) / (b - a)))
      (by fun_prop) (left_mem_Icc.2 hab.le) (by simp) hv
  refine ⟨w, hv, hmean, ?_⟩
  rw [hnorm]
  field_simp [norm_ne_zero_iff.2 hne]

end Mixed

end PDE

open MeasureTheory Set TopologicalSpace
open scoped Real

variable {a b : ℝ}

/-- **The sharp Poincaré inequality on `H¹₀(a, b)` of the real line.** A class of
`W^{1,2}_0(a, b)`, for the interval `(a, b)` of `ℝ`, satisfies
`‖u‖_{L²(a,b)} ≤ (b - a) / π ‖u'‖_{L²(a,b)}`: the isometry `x ↦ x 0` carries it to a class of
`H¹₀` of `TauCeti.PDE.intervalDomain a b` with the same norms, to which
`TauCeti.PDE.isGreatest_mul_norm_value_sq_le_energyFormH1_intervalDomain` applies. -/
theorem W1p.norm_value_le_div_pi_mul_norm_gradient_of_mem_w1p0Submodule (hab : a < b)
    {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2}
    (hu : u ∈ w1p0Submodule volume ⟨Ioo a b, isOpen_Ioo⟩ 2) :
    ‖W1p.value u‖ ≤ (b - a) / π * ‖W1p.gradient u‖ := by
  set g := PDE.lineEquiv.symm.toAffineIsometryEquiv
  have hUV : (PDE.intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))) =
      g ⁻¹' ((⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ) :=
    PDE.coe_intervalDomain_eq_preimage
  set v := W1p.compAffineIsometryEquivL g hUV u
  have hv : v ∈ w1p0Submodule volume (PDE.intervalDomain a b) 2 :=
    (W1p.compAffineIsometryEquivL_mem_w1p0Submodule_iff g hUV).2 hu
  have h := (PDE.isGreatest_mul_norm_value_sq_le_energyFormH1_intervalDomain hab).1 ⟨v, hv⟩
  rw [PDE.energyFormH1_one_zero_zero_eq_inner, real_inner_self_eq_norm_sq] at h
  simp only [v, W1p.norm_value_compAffineIsometryEquivL, W1p.norm_gradient_compAffineIsometryEquivL]
    at h
  have := sub_pos.2 hab
  rw [← inv_div]
  exact (le_inv_mul_iff₀ (by positivity)).2 (le_of_sq_le_sq (by rwa [mul_pow]) (norm_nonneg _))

end TauCeti
