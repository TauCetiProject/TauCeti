/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import TauCeti.Analysis.Fourier.SineSeries
public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
public import TauCeti.Analysis.PDE.ClassicalSolution
public import TauCeti.Analysis.PDE.Spectrum.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.Sobolev.W1p.MeasurePreserving

/-!
# The Dirichlet spectrum of `-Δ` on an interval

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

## Main declarations

* `TauCeti.PDE.intervalDomain`: the interval `(a, b)` as an open subset of the Euclidean line.
* `TauCeti.PDE.exists_value_ae_eq_sin_and_energyFormH1_eq`: the sine modes are weak Dirichlet
  eigenfunctions.
* `TauCeti.PDE.energyFormH1_eq_of_value_ae_eq_sin`, `TauCeti.PDE.norm_value_sq_of_value_ae_eq_sin`
  and `TauCeti.PDE.energyFormH1_self_eq_of_value_ae_eq_sin`: every element of `H¹₀(a, b)` with a
  sine mode as value is an eigenfunction, with `L²` norm `√((b - a) / 2)` and the corresponding
  Dirichlet energy.
* `TauCeti.PDE.setIntegral_intervalDomain`: integrals over the interval domain are integrals over
  the real interval.
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

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Section 8.6
  (the Sturm--Liouville problem) and Section 9.8.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 6.5.1.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Bornology InnerProductSpace Laplacian MeasureTheory Set TopologicalSpace
open scoped Real InnerProductSpace

/-- The open interval `(a, b)`, as an open subset of the Euclidean line `EuclideanSpace ℝ (Fin 1)`.
-/
def intervalDomain (a b : ℝ) : Opens (EuclideanSpace ℝ (Fin 1)) :=
  ⟨{x | x 0 ∈ Ioo a b}, isOpen_Ioo.preimage (by fun_prop)⟩

@[simp]
theorem mem_intervalDomain {a b : ℝ} {x : EuclideanSpace ℝ (Fin 1)} :
    x ∈ intervalDomain a b ↔ x 0 ∈ Ioo a b :=
  Iff.rfl

/-- As a set, the interval domain consists of the points of the line whose coordinate lies in
`(a, b)`. -/
theorem coe_intervalDomain (a b : ℝ) :
    (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))) = {x | x 0 ∈ Ioo a b} := by
  ext x
  exact mem_intervalDomain

/-- The interval domain `(a, b)` is preconnected. -/
theorem isPreconnected_intervalDomain (a b : ℝ) :
    IsPreconnected (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))) :=
  ((convex_Ioo a b).linear_preimage (EuclideanSpace.projₗ (0 : Fin 1))).isPreconnected

variable {a b : ℝ}

attribute [local instance] W1p0.instNormedAddCommGroup

/-- The Euclidean line is isometric to `ℝ`, with inverse `x ↦ x 0`. -/
private def lineEquiv : ℝ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).repr

private theorem lineEquiv_symm_apply (x : EuclideanSpace ℝ (Fin 1)) : lineEquiv.symm x = x 0 := by
  rw [LinearIsometryEquiv.symm_apply_eq]
  ext i
  fin_cases i
  exact (OrthonormalBasis.singleton_repr (ι := Fin 1) (𝕜 := ℝ) (x 0) 0).symm

private theorem measurePreserving_lineEquiv : MeasurePreserving lineEquiv volume volume :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).measurePreserving_repr

private theorem measurePreserving_lineEquiv_symm :
    MeasurePreserving lineEquiv.symm volume volume :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).measurePreserving_repr_symm

private theorem lineEquiv_apply_zero (t : ℝ) : lineEquiv t 0 = t := by
  rw [← lineEquiv_symm_apply, LinearIsometryEquiv.symm_apply_apply]

private theorem coe_intervalDomain_eq_preimage :
    (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))) = lineEquiv.symm ⁻¹' Ioo a b := by
  ext x
  simp [lineEquiv_symm_apply]

private theorem preimage_lineEquiv_intervalDomain :
    lineEquiv ⁻¹' (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))) = Ioo a b := by
  rw [coe_intervalDomain_eq_preimage, ← preimage_comp]
  simp

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

/-- The interval domain `(a, b)` is bounded. -/
theorem isBounded_intervalDomain :
    IsBounded (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))) := by
  rw [coe_intervalDomain_eq_preimage]
  exact lineEquiv.symm.antilipschitzWith.isBounded_preimage (Metric.isBounded_Ioo a b)

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

/-- Integrals over the interval domain are integrals over the real interval: for `f : ℝ → E`,
the integral of `x ↦ f (x 0)` over `TauCeti.PDE.intervalDomain a b` is `∫ t in Ioo a b, f t`. -/
theorem setIntegral_intervalDomain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) :
    ∫ x in (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))), f (x 0) =
      ∫ t in Ioo a b, f t := by
  have h := measurePreserving_lineEquiv.setIntegral_preimage_emb
    lineEquiv.toHomeomorph.measurableEmbedding (fun x => f (x 0))
    (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))
  rw [preimage_lineEquiv_intervalDomain] at h
  simp only [lineEquiv_apply_zero] at h
  exact h.symm

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

/-- `(k π / (b - a))²` is a Dirichlet eigenvalue of `-Δ` on `(a, b)` for every `k ≥ 1`, with
eigenfunction `x ↦ sin (k π (x - a) / (b - a))`. -/
theorem isDirichletEigenvalue_laplacian_intervalDomain (hab : a < b) {k : ℕ} (hk : 0 < k) :
    IsDirichletEigenvalue volume (intervalDomain a b) (fun _ => 1) 0 0
      ((k * π / (b - a)) ^ 2) := by
  obtain ⟨u, hu, heq⟩ := exists_value_ae_eq_sin_and_energyFormH1_eq hab k
  refine (isDirichletEigenvalue_iff_setIntegral _).2
    ⟨u, fun h0 => ?_, fun v => by rw [heq v, W1p.inner_value_eq_setIntegral]⟩
  have hval : W1p.value (u : W1p volume (intervalDomain a b) 2) = 0 := by
    rw [← W1p0.valueL_apply, h0, map_zero]
  -- The sine mode would vanish on `(a, b)`, but it equals `1` at `a + (b - a) / (2k)`.
  have hzero : EqOn (fun x : EuclideanSpace ℝ (Fin 1) => Real.sin (k * π * (x 0 - a) / (b - a)))
      0 (intervalDomain a b) := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ (intervalDomain a b).isOpen
      (Continuous.continuousOn (by fun_prop)) continuousOn_const
    filter_upwards [hu, Lp.coeFn_zero ℝ 2
      (volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))))] with x h1 h2
    rw [← h1, hval, h2]
  have hba : 0 < b - a := sub_pos.2 hab
  have hmem : lineEquiv (a + (b - a) / (2 * k)) ∈ intervalDomain a b := by
    rw [mem_intervalDomain, ← lineEquiv_symm_apply, LinearIsometryEquiv.symm_apply_apply]
    constructor
    · have : 0 < (b - a) / (2 * k) := by positivity
      linarith
    · have hk1 : (1 : ℝ) ≤ k := Nat.one_le_cast.2 hk
      have : (b - a) / (2 * k) ≤ (b - a) / 2 :=
        div_le_div_of_nonneg_left hba.le two_pos (by linarith)
      linarith
  have h1 := hzero hmem
  simp only [Pi.zero_apply] at h1
  rw [← lineEquiv_symm_apply, LinearIsometryEquiv.symm_apply_apply,
    show k * π * (a + (b - a) / (2 * k) - a) / (b - a) = π / 2 by field_simp; ring,
    Real.sin_pi_div_two] at h1
  exact one_ne_zero h1

/-- The sine modes are complete in `L²(a, b)`: an element of `L²(a, b)` orthogonal to every
`x ↦ sin (k π (x - a) / (b - a))`, `k ≥ 1`, is zero. -/
theorem eq_zero_of_forall_setIntegral_mul_sin_eq_zero (hab : a < b)
    (f : Lp ℝ 2 (volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))))
    (h : ∀ k : ℕ, 0 < k → ∫ x in intervalDomain a b,
      f x * Real.sin (k * π * (x 0 - a) / (b - a)) = 0) :
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
  -- Read `f` on the real line, where the sine system is complete.
  have hg : MemLp (fun t => f (lineEquiv t)) 2 (volume.restrict (Ioc a b)) := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact (Lp.memLp f).comp_measurePreserving hmpΩ
  have hg0 := ae_eq_zero_of_forall_integral_mul_sin_eq_zero (hg.integrable one_le_two)
    fun k hk => by
    rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo, ← h k hk,
      ← setIntegral_intervalDomain]
    simp only [← lineEquiv_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc] at hg0
  refine Lp.ext ?_
  filter_upwards [hmpΩ'.quasiMeasurePreserving.ae_eq_comp hg0, Lp.coeFn_zero ℝ 2
    (volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))))] with x h1 h2
  rw [h2]
  simpa using h1

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

/-- The energy form of `-Δ` is symmetric. -/
private theorem energyFormH1_laplacian_comm (u v : W1p0 volume (intervalDomain a b) 2) :
    energyFormH1 (fun _ => 1) 0 0 (u : W1p volume (intervalDomain a b) 2)
        (v : W1p volume (intervalDomain a b) 2) =
      energyFormH1 (fun _ => 1) 0 0 (v : W1p volume (intervalDomain a b) 2)
        (u : W1p volume (intervalDomain a b) 2) :=
  energyFormH1_comm_of_isSymm_ae (ae_of_all _ fun _ => Matrix.isSymm_one) _ _

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
        energyFormH1_laplacian_comm (nonempty_intervalDomain_iff.2 hab)))

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
  exact isGreatest_firstDirichletEigenvalue hcoeff hcoercive energyFormH1_laplacian_comm
    (nonempty_intervalDomain_iff.2 hab)

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
      g ⁻¹' ((⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ) := by
    ext x
    simp [g, PDE.lineEquiv_symm_apply]
  set v := W1p.compAffineIsometryEquivL g hUV u
  have hv : v ∈ w1p0Submodule volume (PDE.intervalDomain a b) 2 :=
    (W1p.compAffineIsometryEquivL_mem_w1p0Submodule_iff g hUV).2 hu
  have h := (PDE.isGreatest_mul_norm_value_sq_le_energyFormH1_intervalDomain hab).1 ⟨v, hv⟩
  rw [PDE.energyFormH1_one_zero_zero_eq_inner, real_inner_self_eq_norm_sq] at h
  simp only [v, W1p.norm_value_compAffineIsometryEquivL, W1p.norm_gradient_compAffineIsometryEquivL]
    at h
  rw [← mul_pow, pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero] at h
  calc ‖W1p.value u‖ = (b - a) / π * (π / (b - a) * ‖W1p.value u‖) := by
        field_simp [(sub_pos.2 hab).ne']
    _ ≤ (b - a) / π * ‖W1p.gradient u‖ := by gcongr

end TauCeti
