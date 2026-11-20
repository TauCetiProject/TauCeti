/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FredholmAlternative
public import TauCeti.Analysis.PDE.Spectrum.Interval
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The Fredholm alternative for `-u'' - κ u` on an interval

On a bounded interval `(a, b)` consider the Dirichlet problem for the operator `-u'' - κ u` with a
constant `κ ∈ ℝ`,

`-u'' - κ u = f` in `(a, b)`, `u(a) = u(b) = 0`,

whose weak form is `∫ u' v' - κ ∫ u v = ℓ v` for every `v ∈ H¹₀(a, b)`. For `κ > 0` the energy
form need not be coercive, and the problem is governed by the Fredholm alternative
(`TauCeti.PDE.UniformlyEllipticOn.exists_forall_energyFormH1_eq_iff`). On an interval everything
in it is explicit, because the Dirichlet spectrum of `-Δ` is the set of numbers
`κ_k = (k π / (b - a))²`, `k ≥ 1`, with eigenfunctions the sine modes
`s_k(x) = sin (k π (x - a) / (b - a))`
(`TauCeti.PDE.isDirichletEigenvalue_laplacian_intervalDomain_iff`).

* **Away from resonance**, when `κ` is none of the `κ_k`, the problem has exactly one weak
  solution for every `ℓ ∈ H⁻¹(a, b)`, and at an eigenvalue uniqueness fails
  (`TauCeti.PDE.forall_existsUnique_forall_energyFormH1_eq_iff`). This holds although the form is
  not coercive once `κ ≥ κ₁` (`TauCeti.PDE.not_isCoercive_energyFormH1L0_of_le`).
* **At resonance**, `κ = κ_k`, the homogeneous problem has the one-dimensional solution space
  spanned by `s_k` (`TauCeti.PDE.forall_energyFormH1_eq_zero_iff_exists_value_ae_eq`). The form is
  symmetric, so this is also the adjoint kernel, and the problem with forcing `f ∈ L²(a, b)` is
  solvable exactly when `∫ f s_k = 0`
  (`TauCeti.PDE.exists_isWeakSolutionDirichlet_iff_setIntegral_mul_sin_eq_zero`).
* **Forcing by another mode** `f = s_m`, `m ≠ k`, at resonance `κ = κ_k`: the problem is solvable
  (`TauCeti.PDE.exists_isWeakSolutionDirichlet_of_ae_eq_sin`), and its weak solutions are exactly
  `s_m / (κ_m - κ_k) + t s_k`, `t ∈ ℝ`
  (`TauCeti.PDE.isWeakSolutionDirichlet_iff_exists_value_ae_eq_of_ae_eq_sin`).

The interval `(0, π)` with `κ = 1` gives the standard examples: `-u'' - u = 1` has no weak
solution, since `∫_0^π sin x dx = 2`
(`TauCeti.PDE.not_exists_isWeakSolutionDirichlet_neg_one_of_ae_eq_one`), while the weak solutions
of `-u'' - u = sin 2x` are exactly the functions `sin (2x) / 3 + t sin x`
(`TauCeti.PDE.isWeakSolutionDirichlet_neg_one_iff_of_ae_eq_sin_two_mul`). With `κ = 2`, which is
not a square of an integer, the problem `-u'' - 2u = ℓ` is uniquely solvable for every `ℓ`
(`TauCeti.PDE.existsUnique_forall_energyFormH1_neg_two_eq`), although its form is not coercive.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 6.2.3.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.6.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Bornology MeasureTheory Set TopologicalSpace
open scoped Real InnerProductSpace

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

variable {a b : ℝ}

/-- The coefficients of `-u'' + c u` with a constant `c` are essentially bounded on `(a, b)`. -/
private theorem memLp_energyIntegrand_one_zero_const (c : ℝ) :
    MemLp (fun x ↦ energyIntegrand ((fun _ ↦ (1 : Matrix (Fin 1) (Fin 1) ℝ)) x)
      ((0 : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) x)
      ((fun _ ↦ c : EuclideanSpace ℝ (Fin 1) → ℝ) x)) ⊤
      (volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))) :=
  memLp_energyIntegrand_of_bounds (beta := 0) (gamma := ‖c‖)
    (uniformlyEllipticOn_const_one_one (n := Fin 1)
      (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))).upper_nonneg
    aestronglyMeasurable_const aestronglyMeasurable_const aestronglyMeasurable_const
    (fun _x hx eta xi ↦ (uniformlyEllipticOn_const_one_one (n := Fin 1)
      (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))).upper_bound hx eta xi)
    (fun _ _ ↦ by simp) (fun _ _ ↦ le_rfl)

/-- The energy form of `-u'' - κ u` is the energy form of `-u''` minus `κ` times the `L²` inner
product. -/
private theorem energyFormH1_one_zero_neg (κ : ℝ) (u v : W1p volume (intervalDomain a b) 2) :
    energyFormH1 (fun _ ↦ 1) 0 (fun _ ↦ -κ) u v =
      energyFormH1 (fun _ ↦ 1) 0 0 u v - κ * ⟪W1p.value u, W1p.value v⟫_ℝ := by
  simpa only [Pi.zero_apply, zero_sub] using
    energyFormH1_mass_sub_const (c := 0) (memLp_energyIntegrand_one_zero_const 0) κ u v

/-- The sine modes are weak Dirichlet eigenfunctions
(`TauCeti.PDE.exists_value_ae_eq_sin_and_energyFormH1_eq`). Restating this here fixes the
instances of `W1p0` to those of this file once, so that rewriting with the eigenfunction identity
does not compare two instance paths. -/
private theorem exists_value_ae_eq_sin (hab : a < b) (k : ℕ) :
    ∃ s : W1p0 volume (intervalDomain a b) 2,
      W1p.value (s : W1p volume (intervalDomain a b) 2)
          =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
        (fun x ↦ Real.sin (k * π * (x 0 - a) / (b - a))) ∧
      ∀ v : W1p0 volume (intervalDomain a b) 2,
        energyFormH1 (fun _ ↦ 1) 0 0 (s : W1p volume (intervalDomain a b) 2)
            (v : W1p volume (intervalDomain a b) 2) =
          (k * π / (b - a)) ^ 2 * ⟪W1p.value (s : W1p volume (intervalDomain a b) 2),
            W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ :=
  exists_value_ae_eq_sin_and_energyFormH1_eq hab k

/-- Being a weak solution of `-u'' + c u = f`, with the `W1p0` instances of this file (see
`TauCeti.PDE.isWeakSolutionDirichlet_iff_inner`). -/
private theorem isWeakSolutionDirichlet_one_zero_const_iff (c : ℝ)
    (f : Lp ℝ 2 (volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))))
    (u : W1p0 volume (intervalDomain a b) 2) :
    IsWeakSolutionDirichlet (fun _ ↦ 1) 0 (fun _ ↦ c) f u ↔
      ∀ v : W1p0 volume (intervalDomain a b) 2,
        energyFormH1 (fun _ ↦ 1) 0 (fun _ ↦ c) (u : W1p volume (intervalDomain a b) 2)
            (v : W1p volume (intervalDomain a b) 2) =
          ⟪f, W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ :=
  isWeakSolutionDirichlet_iff_inner f u

/-- The `L²` pairing of values is homogeneous in the left argument. -/
private theorem inner_value_smul_left (t : ℝ) (u v : W1p volume (intervalDomain a b) 2) :
    ⟪W1p.value (t • u), W1p.value v⟫_ℝ = t * ⟪W1p.value u, W1p.value v⟫_ℝ := by
  rw [W1p.value_smul, real_inner_smul_left]

/-- Distinct sine modes of `(a, b)` have distinct Dirichlet eigenvalues. -/
private theorem sq_natCast_mul_pi_div_ne (hab : a < b) {j k : ℕ} (h : j ≠ k) :
    (j * π / (b - a)) ^ 2 ≠ (k * π / (b - a)) ^ 2 := by
  have hba : 0 < b - a := sub_pos.2 hab
  rw [Ne, pow_left_inj₀ (by positivity) (by positivity) two_ne_zero,
    div_left_inj₀ hba.ne', mul_left_inj' Real.pi_ne_zero, Nat.cast_inj]
  exact h

/-- Integrating against the `j`-th sine mode is the `L²` pairing with its `H¹₀` representative. -/
private theorem setIntegral_mul_sin_eq_inner
    (F : Lp ℝ 2 (volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))))
    {s : W1p0 volume (intervalDomain a b) 2} {j : ℕ}
    (hs : W1p.value (s : W1p volume (intervalDomain a b) 2)
      =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
        fun x ↦ Real.sin (j * π * (x 0 - a) / (b - a))) :
    ∫ x in intervalDomain a b, F x * Real.sin (j * π * (x 0 - a) / (b - a)) =
      ⟪F, W1p.value (s : W1p volume (intervalDomain a b) 2)⟫_ℝ := by
  rw [← dirichletForcing_apply, dirichletForcing_apply_eq_setIntegral]
  refine integral_congr_ae ?_
  filter_upwards [hs] with x hx
  rw [hx]

/-- An eigenfunction `u` for the `k`-th eigenvalue with `⟪u, s_k⟫ = t ⟪s_k, s_k⟫` is `t s_k`: their
difference is orthogonal to every sine mode. -/
private theorem value_eq_smul_of_inner_eq (hab : a < b) {k : ℕ}
    {u s : W1p0 volume (intervalDomain a b) 2}
    (hs : W1p.value (s : W1p volume (intervalDomain a b) 2)
      =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
        fun x ↦ Real.sin (k * π * (x 0 - a) / (b - a)))
    (hseq : ∀ v : W1p0 volume (intervalDomain a b) 2,
      energyFormH1 (fun _ ↦ 1) 0 0 (s : W1p volume (intervalDomain a b) 2)
          (v : W1p volume (intervalDomain a b) 2) =
        (k * π / (b - a)) ^ 2 * ⟪W1p.value (s : W1p volume (intervalDomain a b) 2),
          W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ)
    (hu : ∀ v : W1p0 volume (intervalDomain a b) 2,
      energyFormH1 (fun _ ↦ 1) 0 0 (u : W1p volume (intervalDomain a b) 2)
          (v : W1p volume (intervalDomain a b) 2) =
        (k * π / (b - a)) ^ 2 * ⟪W1p.value (u : W1p volume (intervalDomain a b) 2),
          W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ)
    {t : ℝ} (ht : ⟪W1p.value (u : W1p volume (intervalDomain a b) 2),
        W1p.value (s : W1p volume (intervalDomain a b) 2)⟫_ℝ =
      t * ⟪W1p.value (s : W1p volume (intervalDomain a b) 2),
        W1p.value (s : W1p volume (intervalDomain a b) 2)⟫_ℝ) :
    W1p.value (u : W1p volume (intervalDomain a b) 2) =
      t • W1p.value (s : W1p volume (intervalDomain a b) 2) := by
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_setIntegral_mul_sin_eq_zero hab _ fun j _ ↦ ?_
  obtain ⟨sj, hsj, hsjeq⟩ := exists_value_ae_eq_sin hab j
  rw [setIntegral_mul_sin_eq_inner _ hsj, inner_sub_left, real_inner_smul_left]
  by_cases hjk : j = k
  · subst hjk
    rw [show W1p.value (sj : W1p volume (intervalDomain a b) 2) =
      W1p.value (s : W1p volume (intervalDomain a b) 2) from Lp.ext (hsj.trans hs.symm), ht,
      sub_self]
  · have hsymm : ∀ᵐ x ∂volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))),
        ((fun _ ↦ (1 : Matrix (Fin 1) (Fin 1) ℝ)) x).IsSymm :=
      ae_of_all _ fun _ ↦ Matrix.isSymm_one
    have hne := (sq_natCast_mul_pi_div_ne hab hjk).symm
    rw [inner_value_eq_zero_of_energyFormH1_eq_of_ne hsymm hne hu hsjeq,
      inner_value_eq_zero_of_energyFormH1_eq_of_ne hsymm hne hseq hsjeq, mul_zero, sub_zero]

/-- A multiple `t s_k` of the `k`-th sine mode solves the homogeneous eigenvalue equation. -/
private theorem energyFormH1_eq_of_value_ae_eq_mul_sin {k : ℕ}
    {u s : W1p0 volume (intervalDomain a b) 2}
    (hs : W1p.value (s : W1p volume (intervalDomain a b) 2)
      =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
        fun x ↦ Real.sin (k * π * (x 0 - a) / (b - a)))
    (hseq : ∀ v : W1p0 volume (intervalDomain a b) 2,
      energyFormH1 (fun _ ↦ 1) 0 0 (s : W1p volume (intervalDomain a b) 2)
          (v : W1p volume (intervalDomain a b) 2) =
        (k * π / (b - a)) ^ 2 * ⟪W1p.value (s : W1p volume (intervalDomain a b) 2),
          W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ)
    {t : ℝ} (ht : W1p.value (u : W1p volume (intervalDomain a b) 2)
      =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
        fun x ↦ t * Real.sin (k * π * (x 0 - a) / (b - a)))
    (v : W1p0 volume (intervalDomain a b) 2) :
    energyFormH1 (fun _ ↦ 1) 0 0 (u : W1p volume (intervalDomain a b) 2)
        (v : W1p volume (intervalDomain a b) 2) =
      (k * π / (b - a)) ^ 2 * ⟪W1p.value (u : W1p volume (intervalDomain a b) 2),
        W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ := by
  have hus : (u : W1p volume (intervalDomain a b) 2) =
      t • (s : W1p volume (intervalDomain a b) 2) :=
    W1p.ext_value <| Lp.ext <| by
      filter_upwards [ht, W1p.value_smul_ae t (s : W1p volume (intervalDomain a b) 2), hs]
        with x h1 h2 h3
      rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul]
  rw [hus, energyFormH1_smul_left, hseq v, W1p.value_smul, real_inner_smul_left]
  ring

/-- The equation `⟪U, S⟫ = t ⟪S, S⟫` has a solution `t`: if `⟪S, S⟫ = 0`, then `S = 0`. -/
private theorem exists_inner_eq_mul_inner_self
    (U S : Lp ℝ 2 (volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))))) :
    ∃ t : ℝ, ⟪U, S⟫_ℝ = t * ⟪S, S⟫_ℝ := by
  by_cases h0 : ⟪S, S⟫_ℝ = 0
  · refine ⟨0, ?_⟩
    rw [zero_mul, (inner_self_eq_zero (𝕜 := ℝ)).1 h0, inner_zero_right]
  · exact ⟨_, (div_mul_cancel₀ _ h0).symm⟩

/-- **The kernel at resonance.** At the Dirichlet eigenvalue `κ = (k π / (b - a))²`, the weak
solutions `u ∈ H¹₀(a, b)` of the homogeneous problem `-u'' - κ u = 0` are exactly the multiples of
the sine mode `x ↦ sin (k π (x - a) / (b - a))`. For `k = 0` the sine mode vanishes and the
statement says that `-u'' = 0` has only the trivial solution. -/
theorem forall_energyFormH1_eq_zero_iff_exists_value_ae_eq (hab : a < b) (k : ℕ)
    (u : W1p0 volume (intervalDomain a b) 2) :
    (∀ v : W1p0 volume (intervalDomain a b) 2,
        energyFormH1 (fun _ ↦ 1) 0 (fun _ ↦ -(k * π / (b - a)) ^ 2)
          (u : W1p volume (intervalDomain a b) 2) (v : W1p volume (intervalDomain a b) 2) = 0) ↔
      ∃ t : ℝ, W1p.value (u : W1p volume (intervalDomain a b) 2)
        =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
          fun x ↦ t * Real.sin (k * π * (x 0 - a) / (b - a)) := by
  obtain ⟨s, hs, hseq⟩ := exists_value_ae_eq_sin hab k
  simp only [energyFormH1_one_zero_neg, sub_eq_zero]
  refine ⟨fun hu ↦ ?_, fun ⟨t, ht⟩ ↦ energyFormH1_eq_of_value_ae_eq_mul_sin hs hseq ht⟩
  obtain ⟨t, ht⟩ := exists_inner_eq_mul_inner_self
    (W1p.value (u : W1p volume (intervalDomain a b) 2))
    (W1p.value (s : W1p volume (intervalDomain a b) 2))
  refine ⟨t, ?_⟩
  rw [value_eq_smul_of_inner_eq hab hs hseq hu ht]
  filter_upwards [Lp.coeFn_smul t (W1p.value (s : W1p volume (intervalDomain a b) 2)), hs]
    with x h1 h2
  rw [h1, Pi.smul_apply, h2, smul_eq_mul]

/-- The compatibility condition for `-u'' + c u` with a constant `c` and `L²` forcing, from the
Fredholm alternative for uniformly elliptic operators; the form is symmetric, so the adjoint
kernel is the kernel. -/
private theorem exists_isWeakSolutionDirichlet_one_zero_const_iff (c : ℝ)
    (f : Lp ℝ 2 (volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))))) :
    (∃ u : W1p0 volume (intervalDomain a b) 2,
        IsWeakSolutionDirichlet (fun _ ↦ 1) 0 (fun _ ↦ c) f u) ↔
      ∀ w : W1p0 volume (intervalDomain a b) 2,
        (∀ v : W1p0 volume (intervalDomain a b) 2,
          energyFormH1 (fun _ ↦ 1) 0 (fun _ ↦ c) (w : W1p volume (intervalDomain a b) 2)
            (v : W1p volume (intervalDomain a b) 2) = 0) →
        ∫ x in intervalDomain a b, f x * W1p.value (w : W1p volume (intervalDomain a b) 2) x =
          0 := by
  have h := (uniformlyEllipticOn_const_one_one (n := Fin 1)
    (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))).exists_forall_energyFormH1_eq_iff
      (b := 0) (c := fun _ ↦ c) aestronglyMeasurable_const aestronglyMeasurable_const
      aestronglyMeasurable_const (beta := 0) (fun _ _ ↦ by simp) (gamma := ‖c‖)
      (fun _ _ ↦ le_rfl) isBounded_intervalDomain (dirichletForcing f)
  simp only [dirichletForcing_apply_eq_setIntegral,
    energyFormH1_comm_of_isSymm_ae (ae_of_all _ fun _ ↦ Matrix.isSymm_one) _
      (_ : W1p volume (intervalDomain a b) 2)] at h
  simpa only [isWeakSolutionDirichlet_iff] using h

/-- Unique solvability for `-u'' + c u` with a constant `c` when the homogeneous problem has only
the trivial solution. -/
private theorem existsUnique_forall_energyFormH1_one_zero_const_eq (c : ℝ)
    (hker : ∀ u : W1p0 volume (intervalDomain a b) 2,
      (∀ v : W1p0 volume (intervalDomain a b) 2,
        energyFormH1 (fun _ ↦ 1) 0 (fun _ ↦ c) (u : W1p volume (intervalDomain a b) 2)
          (v : W1p volume (intervalDomain a b) 2) = 0) → u = 0)
    (ℓ : StrongDual ℝ (W1p0 volume (intervalDomain a b) 2)) :
    ∃! u : W1p0 volume (intervalDomain a b) 2, ∀ v : W1p0 volume (intervalDomain a b) 2,
      energyFormH1 (fun _ ↦ 1) 0 (fun _ ↦ c) (u : W1p volume (intervalDomain a b) 2)
        (v : W1p volume (intervalDomain a b) 2) = ℓ v :=
  (uniformlyEllipticOn_const_one_one (n := Fin 1)
    (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))).existsUnique_forall_energyFormH1_eq
      (b := 0) (c := fun _ ↦ c) aestronglyMeasurable_const aestronglyMeasurable_const
      aestronglyMeasurable_const (beta := 0) (fun _ _ ↦ by simp) (gamma := ‖c‖)
      (fun _ _ ↦ le_rfl) isBounded_intervalDomain hker ℓ

/-- Integrating against an element `t s_k` of the resonant kernel is `t` times integrating against
the sine mode. -/
private theorem setIntegral_mul_value_eq_mul_setIntegral {k : ℕ}
    (f : Lp ℝ 2 (volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))))
    {w : W1p0 volume (intervalDomain a b) 2} {t : ℝ}
    (ht : W1p.value (w : W1p volume (intervalDomain a b) 2)
      =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
        fun x ↦ t * Real.sin (k * π * (x 0 - a) / (b - a))) :
    ∫ x in intervalDomain a b, f x * W1p.value (w : W1p volume (intervalDomain a b) 2) x =
      t * ∫ x in intervalDomain a b, f x * Real.sin (k * π * (x 0 - a) / (b - a)) := by
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [ht] with x hx
  rw [hx]
  ring

/-- **The Fredholm compatibility condition at resonance.** At the Dirichlet eigenvalue
`κ = (k π / (b - a))²`, the problem `-u'' - κ u = f` in `(a, b)`, `u(a) = u(b) = 0`, with
`f ∈ L²(a, b)` has a weak solution exactly when `f` is orthogonal to the sine mode
`x ↦ sin (k π (x - a) / (b - a))`, which spans the adjoint kernel. -/
theorem exists_isWeakSolutionDirichlet_iff_setIntegral_mul_sin_eq_zero (hab : a < b) (k : ℕ)
    (f : Lp ℝ 2 (volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))))) :
    (∃ u : W1p0 volume (intervalDomain a b) 2,
        IsWeakSolutionDirichlet (fun _ ↦ 1) 0 (fun _ ↦ -(k * π / (b - a)) ^ 2) f u) ↔
      ∫ x in intervalDomain a b, f x * Real.sin (k * π * (x 0 - a) / (b - a)) = 0 := by
  rw [exists_isWeakSolutionDirichlet_one_zero_const_iff]
  obtain ⟨s, hs, -⟩ := exists_value_ae_eq_sin hab k
  have hs1 : W1p.value (s : W1p volume (intervalDomain a b) 2)
      =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
        fun x ↦ 1 * Real.sin (k * π * (x 0 - a) / (b - a)) := by
    filter_upwards [hs] with x hx
    rw [hx, one_mul]
  refine ⟨fun h ↦ ?_, fun h w hw ↦ ?_⟩
  · have h1 := h s ((forall_energyFormH1_eq_zero_iff_exists_value_ae_eq hab k s).2 ⟨1, hs1⟩)
    rwa [setIntegral_mul_value_eq_mul_setIntegral f hs1, one_mul] at h1
  · obtain ⟨t, ht⟩ := (forall_energyFormH1_eq_zero_iff_exists_value_ae_eq hab k w).1 hw
    rw [setIntegral_mul_value_eq_mul_setIntegral f ht, h, mul_zero]

/-- The `k`-th Dirichlet eigenfunction of `-Δ` on `(a, b)`. Restating
`TauCeti.PDE.isDirichletEigenvalue_laplacian_intervalDomain` here fixes the instances of `W1p0` to
those of this file once, so that rewriting with the eigenfunction identity does not compare two
instance paths. -/
private theorem exists_ne_zero_energyFormH1_eq (hab : a < b) {k : ℕ} (hk : 0 < k) :
    ∃ s : W1p0 volume (intervalDomain a b) 2, s ≠ 0 ∧ ∀ v : W1p0 volume (intervalDomain a b) 2,
      energyFormH1 (fun _ ↦ 1) 0 0 (s : W1p volume (intervalDomain a b) 2)
          (v : W1p volume (intervalDomain a b) 2) =
        (k * π / (b - a)) ^ 2 * ⟪W1p.value (s : W1p volume (intervalDomain a b) 2),
          W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ :=
  (isDirichletEigenvalue_iff _).1 (isDirichletEigenvalue_laplacian_intervalDomain hab hk)

/-- At a Dirichlet eigenvalue, the homogeneous problem has a nonzero solution. -/
private theorem exists_ne_zero_forall_energyFormH1_eq_zero (hab : a < b) {k : ℕ} (hk : 0 < k) :
    ∃ s : W1p0 volume (intervalDomain a b) 2, s ≠ 0 ∧ ∀ v : W1p0 volume (intervalDomain a b) 2,
      energyFormH1 (fun _ ↦ 1) 0 (fun _ ↦ -(k * π / (b - a)) ^ 2)
        (s : W1p volume (intervalDomain a b) 2) (v : W1p volume (intervalDomain a b) 2) = 0 := by
  obtain ⟨s, hs0, hs⟩ := exists_ne_zero_energyFormH1_eq hab hk
  exact ⟨s, hs0, fun v ↦ by rw [energyFormH1_one_zero_neg, hs v, sub_self]⟩

/-- At an eigenvalue, both `0` and an eigenfunction solve the homogeneous problem. -/
private theorem not_forall_existsUnique_forall_energyFormH1_eq (hab : a < b) {k : ℕ}
    (hk : 0 < k) :
    ¬∀ ℓ : StrongDual ℝ (W1p0 volume (intervalDomain a b) 2),
      ∃! u : W1p0 volume (intervalDomain a b) 2, ∀ v : W1p0 volume (intervalDomain a b) 2,
        energyFormH1 (fun _ ↦ 1) 0 (fun _ ↦ -(k * π / (b - a)) ^ 2)
          (u : W1p volume (intervalDomain a b) 2) (v : W1p volume (intervalDomain a b) 2) =
            ℓ v := by
  intro h
  obtain ⟨s, hs0, hs⟩ := exists_ne_zero_forall_energyFormH1_eq_zero hab hk
  obtain ⟨u, -, huniq⟩ := h 0
  refine hs0 ((huniq s fun v ↦ ?_).trans (huniq 0 fun v ↦ ?_).symm)
  · rw [hs v, zero_apply]
  · exact (energyFormH1_zero_left _ _ _ _).trans (zero_apply _).symm

/-- A nonzero solution of the homogeneous problem for `-u'' - κ u` makes `κ` a Dirichlet
eigenvalue of `-Δ`. -/
private theorem isDirichletEigenvalue_of_ne_zero (κ : ℝ) {u : W1p0 volume (intervalDomain a b) 2}
    (hu0 : u ≠ 0)
    (hu : ∀ v : W1p0 volume (intervalDomain a b) 2,
      energyFormH1 (fun _ ↦ 1) 0 (fun _ ↦ -κ) (u : W1p volume (intervalDomain a b) 2)
        (v : W1p volume (intervalDomain a b) 2) = 0) :
    IsDirichletEigenvalue volume (intervalDomain a b) (fun _ ↦ 1) 0 0 κ := by
  have h : ∀ v : W1p0 volume (intervalDomain a b) 2,
      energyFormH1 (fun _ ↦ 1) 0 0 (u : W1p volume (intervalDomain a b) 2)
          (v : W1p volume (intervalDomain a b) 2) =
        κ * ⟪W1p.value (u : W1p volume (intervalDomain a b) 2),
          W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ := fun v ↦ by
    rw [← sub_eq_zero, ← energyFormH1_one_zero_neg]
    exact hu v
  exact (isDirichletEigenvalue_iff κ).2 ⟨u, hu0, h⟩

/-- **The Fredholm alternative for `-u'' - κ u` on an interval.** The Dirichlet problem
`-u'' - κ u = ℓ` in `(a, b)`, `u(a) = u(b) = 0`, has exactly one weak solution `u ∈ H¹₀(a, b)` for
every `ℓ ∈ H⁻¹(a, b)` if and only if `κ` is not a Dirichlet eigenvalue `(k π / (b - a))²`,
`k ≥ 1`. -/
theorem forall_existsUnique_forall_energyFormH1_eq_iff (hab : a < b) (κ : ℝ) :
    (∀ ℓ : StrongDual ℝ (W1p0 volume (intervalDomain a b) 2),
      ∃! u : W1p0 volume (intervalDomain a b) 2, ∀ v : W1p0 volume (intervalDomain a b) 2,
        energyFormH1 (fun _ ↦ 1) 0 (fun _ ↦ -κ) (u : W1p volume (intervalDomain a b) 2)
          (v : W1p volume (intervalDomain a b) 2) = ℓ v) ↔
      ∀ k : ℕ, 0 < k → κ ≠ (k * π / (b - a)) ^ 2 := by
  refine ⟨?_, fun h ↦ existsUnique_forall_energyFormH1_one_zero_const_eq _ fun u hu ↦ ?_⟩
  · rintro h k hk rfl
    exact not_forall_existsUnique_forall_energyFormH1_eq hab hk h
  by_contra hu0
  obtain ⟨k, hk, hκ⟩ := (isDirichletEigenvalue_laplacian_intervalDomain_iff hab).1
    (isDirichletEigenvalue_of_ne_zero κ hu0 hu)
  exact h k hk hκ

/-- **The form of `-u'' - κ u` is not coercive from the first eigenvalue on.** If
`κ ≥ (π / (b - a))²`, the first Dirichlet eigenvalue of `-Δ` on `(a, b)`, the energy form of
`-u'' - κ u` is not coercive on `H¹₀(a, b)`: it is nonpositive on the first sine mode. So
Lax–Milgram does not apply, and away from the eigenvalues unique solvability comes from the
Fredholm alternative instead (`TauCeti.PDE.forall_existsUnique_forall_energyFormH1_eq_iff`). -/
theorem not_isCoercive_energyFormH1L0_of_le (hab : a < b) {κ : ℝ} (hκ : (π / (b - a)) ^ 2 ≤ κ)
    (hcoeff : MemLp (fun x ↦ energyIntegrand ((fun _ ↦ (1 : Matrix (Fin 1) (Fin 1) ℝ)) x)
      ((0 : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) x)
      ((fun _ ↦ -κ : EuclideanSpace ℝ (Fin 1) → ℝ) x)) ⊤
      (volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))))) :
    ¬IsCoercive (energyFormH1L0 hcoeff) := by
  intro hcoercive
  -- The first sine mode is an eigenfunction of the form, with eigenvalue `(π / (b - a))² - κ`.
  obtain ⟨s, hs0, hs⟩ := exists_ne_zero_energyFormH1_eq hab one_pos
  have heig : IsDirichletEigenvalue volume (intervalDomain a b) (fun _ ↦ 1) 0 (fun _ ↦ -κ)
      ((π / (b - a)) ^ 2 - κ) :=
    (isDirichletEigenvalue_iff _).2 ⟨s, hs0, fun v ↦ by
      rw [energyFormH1_one_zero_neg, hs v, Nat.cast_one, one_mul, sub_mul]⟩
  linarith [pos_of_isDirichletEigenvalue hcoeff hcoercive heig]

/-! ### Resonant forcing by another sine mode -/

/-- Two representatives of the same function pair the same way with the values of `H¹₀(a, b)`. -/
private theorem inner_eq_inner_value_of_ae_eq
    (f : Lp ℝ 2 (volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))))
    {g : EuclideanSpace ℝ (Fin 1) → ℝ}
    (hf : f =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))] g)
    {s : W1p0 volume (intervalDomain a b) 2}
    (hs : W1p.value (s : W1p volume (intervalDomain a b) 2)
      =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))] g)
    (v : W1p0 volume (intervalDomain a b) 2) :
    ⟪f, W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ =
      ⟪W1p.value (s : W1p volume (intervalDomain a b) 2),
        W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ := by
  rw [← dirichletForcing_apply, dirichletForcing_apply_eq_setIntegral,
    W1p.inner_value_eq_setIntegral]
  refine integral_congr_ae ?_
  filter_upwards [hf, hs] with x h1 h2
  rw [h1, h2]

/-- Testing a weak solution of `-u'' - κ_k u = s_m` against the `j`-th sine mode `s_j`, whose
eigenvalue is `κ_j`: `(κ_j - κ_k) ⟪u, s_j⟫ = ⟪s_m, s_j⟫`. -/
private theorem mul_inner_value_eq_of_isWeakSolutionDirichlet {k j : ℕ}
    {u sm sj : W1p0 volume (intervalDomain a b) 2}
    (hu : ∀ v : W1p0 volume (intervalDomain a b) 2,
      energyFormH1 (fun _ ↦ 1) 0 (fun _ ↦ -(k * π / (b - a)) ^ 2)
          (u : W1p volume (intervalDomain a b) 2) (v : W1p volume (intervalDomain a b) 2) =
        ⟪W1p.value (sm : W1p volume (intervalDomain a b) 2),
          W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ)
    (hsj : ∀ v : W1p0 volume (intervalDomain a b) 2,
      energyFormH1 (fun _ ↦ 1) 0 0 (sj : W1p volume (intervalDomain a b) 2)
          (v : W1p volume (intervalDomain a b) 2) =
        (j * π / (b - a)) ^ 2 * ⟪W1p.value (sj : W1p volume (intervalDomain a b) 2),
          W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ) :
    ((j * π / (b - a)) ^ 2 - (k * π / (b - a)) ^ 2) *
        ⟪W1p.value (u : W1p volume (intervalDomain a b) 2),
          W1p.value (sj : W1p volume (intervalDomain a b) 2)⟫_ℝ =
      ⟪W1p.value (sm : W1p volume (intervalDomain a b) 2),
        W1p.value (sj : W1p volume (intervalDomain a b) 2)⟫_ℝ := by
  have h := hu sj
  rw [energyFormH1_one_zero_neg,
    energyFormH1_comm_of_isSymm_ae (ae_of_all _ fun _ ↦ Matrix.isSymm_one), hsj u,
    real_inner_comm (W1p.value (u : W1p volume (intervalDomain a b) 2))] at h
  linarith

/-- The pairing of `u - s_m / (κ_m - κ_k) - t s_k` with `s_k` vanishes when
`⟪u, s_k⟫ = t ⟪s_k, s_k⟫`, since `s_m ⊥ s_k`. -/
private theorem inner_value_sub_eq_zero_left (hab : a < b) {k m : ℕ} (hmk : m ≠ k)
    {u sk sm : W1p0 volume (intervalDomain a b) 2}
    (hskeq : ∀ v : W1p0 volume (intervalDomain a b) 2,
      energyFormH1 (fun _ ↦ 1) 0 0 (sk : W1p volume (intervalDomain a b) 2)
          (v : W1p volume (intervalDomain a b) 2) =
        (k * π / (b - a)) ^ 2 * ⟪W1p.value (sk : W1p volume (intervalDomain a b) 2),
          W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ)
    (hsmeq : ∀ v : W1p0 volume (intervalDomain a b) 2,
      energyFormH1 (fun _ ↦ 1) 0 0 (sm : W1p volume (intervalDomain a b) 2)
          (v : W1p volume (intervalDomain a b) 2) =
        (m * π / (b - a)) ^ 2 * ⟪W1p.value (sm : W1p volume (intervalDomain a b) 2),
          W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ)
    {t : ℝ} (ht : ⟪W1p.value (u : W1p volume (intervalDomain a b) 2),
        W1p.value (sk : W1p volume (intervalDomain a b) 2)⟫_ℝ =
      t * ⟪W1p.value (sk : W1p volume (intervalDomain a b) 2),
        W1p.value (sk : W1p volume (intervalDomain a b) 2)⟫_ℝ) :
    ⟪W1p.value (u : W1p volume (intervalDomain a b) 2),
        W1p.value (sk : W1p volume (intervalDomain a b) 2)⟫_ℝ -
      (((m * π / (b - a)) ^ 2 - (k * π / (b - a)) ^ 2)⁻¹ *
          ⟪W1p.value (sm : W1p volume (intervalDomain a b) 2),
            W1p.value (sk : W1p volume (intervalDomain a b) 2)⟫_ℝ +
        t * ⟪W1p.value (sk : W1p volume (intervalDomain a b) 2),
          W1p.value (sk : W1p volume (intervalDomain a b) 2)⟫_ℝ) = 0 := by
  have hsymm : ∀ᵐ x ∂volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))),
      ((fun _ ↦ (1 : Matrix (Fin 1) (Fin 1) ℝ)) x).IsSymm :=
    ae_of_all _ fun _ ↦ Matrix.isSymm_one
  rw [ht, inner_value_eq_zero_of_energyFormH1_eq_of_ne hsymm (sq_natCast_mul_pi_div_ne hab hmk)
    hsmeq hskeq]
  ring

/-- The pairing of `u - s_m / (κ_m - κ_k) - t s_k` with `s_m` vanishes, for a weak solution `u`
of `-u'' - κ_k u = s_m`, since `s_k ⊥ s_m`. -/
private theorem inner_value_sub_eq_zero_right (hab : a < b) {k m : ℕ} (hmk : m ≠ k)
    {u sk sm : W1p0 volume (intervalDomain a b) 2}
    (hskeq : ∀ v : W1p0 volume (intervalDomain a b) 2,
      energyFormH1 (fun _ ↦ 1) 0 0 (sk : W1p volume (intervalDomain a b) 2)
          (v : W1p volume (intervalDomain a b) 2) =
        (k * π / (b - a)) ^ 2 * ⟪W1p.value (sk : W1p volume (intervalDomain a b) 2),
          W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ)
    (hsmeq : ∀ v : W1p0 volume (intervalDomain a b) 2,
      energyFormH1 (fun _ ↦ 1) 0 0 (sm : W1p volume (intervalDomain a b) 2)
          (v : W1p volume (intervalDomain a b) 2) =
        (m * π / (b - a)) ^ 2 * ⟪W1p.value (sm : W1p volume (intervalDomain a b) 2),
          W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ)
    (hu : ∀ v : W1p0 volume (intervalDomain a b) 2,
      energyFormH1 (fun _ ↦ 1) 0 (fun _ ↦ -(k * π / (b - a)) ^ 2)
          (u : W1p volume (intervalDomain a b) 2) (v : W1p volume (intervalDomain a b) 2) =
        ⟪W1p.value (sm : W1p volume (intervalDomain a b) 2),
          W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ)
    (t : ℝ) :
    ⟪W1p.value (u : W1p volume (intervalDomain a b) 2),
        W1p.value (sm : W1p volume (intervalDomain a b) 2)⟫_ℝ -
      (((m * π / (b - a)) ^ 2 - (k * π / (b - a)) ^ 2)⁻¹ *
          ⟪W1p.value (sm : W1p volume (intervalDomain a b) 2),
            W1p.value (sm : W1p volume (intervalDomain a b) 2)⟫_ℝ +
        t * ⟪W1p.value (sk : W1p volume (intervalDomain a b) 2),
          W1p.value (sm : W1p volume (intervalDomain a b) 2)⟫_ℝ) = 0 := by
  have hsymm : ∀ᵐ x ∂volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))),
      ((fun _ ↦ (1 : Matrix (Fin 1) (Fin 1) ℝ)) x).IsSymm :=
    ae_of_all _ fun _ ↦ Matrix.isSymm_one
  have hne := sub_ne_zero.2 (sq_natCast_mul_pi_div_ne hab hmk)
  rw [inner_value_eq_zero_of_energyFormH1_eq_of_ne hsymm (sq_natCast_mul_pi_div_ne hab hmk).symm
    hskeq hsmeq, ← mul_inner_value_eq_of_isWeakSolutionDirichlet hu hsmeq,
    inv_mul_cancel_left₀ hne]
  ring

/-- The pairing of `u - s_m / (κ_m - κ_k) - t s_k` with `s_j`, `j ∉ {k, m}`, vanishes for a weak
solution `u` of `-u'' - κ_k u = s_m`: all three terms are orthogonal to `s_j`. -/
private theorem inner_value_sub_eq_zero_of_ne (hab : a < b) {k m j : ℕ} (hjk : j ≠ k)
    (hjm : j ≠ m) {u sk sm sj : W1p0 volume (intervalDomain a b) 2}
    (hskeq : ∀ v : W1p0 volume (intervalDomain a b) 2,
      energyFormH1 (fun _ ↦ 1) 0 0 (sk : W1p volume (intervalDomain a b) 2)
          (v : W1p volume (intervalDomain a b) 2) =
        (k * π / (b - a)) ^ 2 * ⟪W1p.value (sk : W1p volume (intervalDomain a b) 2),
          W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ)
    (hsmeq : ∀ v : W1p0 volume (intervalDomain a b) 2,
      energyFormH1 (fun _ ↦ 1) 0 0 (sm : W1p volume (intervalDomain a b) 2)
          (v : W1p volume (intervalDomain a b) 2) =
        (m * π / (b - a)) ^ 2 * ⟪W1p.value (sm : W1p volume (intervalDomain a b) 2),
          W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ)
    (hsjeq : ∀ v : W1p0 volume (intervalDomain a b) 2,
      energyFormH1 (fun _ ↦ 1) 0 0 (sj : W1p volume (intervalDomain a b) 2)
          (v : W1p volume (intervalDomain a b) 2) =
        (j * π / (b - a)) ^ 2 * ⟪W1p.value (sj : W1p volume (intervalDomain a b) 2),
          W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ)
    (hu : ∀ v : W1p0 volume (intervalDomain a b) 2,
      energyFormH1 (fun _ ↦ 1) 0 (fun _ ↦ -(k * π / (b - a)) ^ 2)
          (u : W1p volume (intervalDomain a b) 2) (v : W1p volume (intervalDomain a b) 2) =
        ⟪W1p.value (sm : W1p volume (intervalDomain a b) 2),
          W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ)
    (t : ℝ) :
    ⟪W1p.value (u : W1p volume (intervalDomain a b) 2),
        W1p.value (sj : W1p volume (intervalDomain a b) 2)⟫_ℝ -
      (((m * π / (b - a)) ^ 2 - (k * π / (b - a)) ^ 2)⁻¹ *
          ⟪W1p.value (sm : W1p volume (intervalDomain a b) 2),
            W1p.value (sj : W1p volume (intervalDomain a b) 2)⟫_ℝ +
        t * ⟪W1p.value (sk : W1p volume (intervalDomain a b) 2),
          W1p.value (sj : W1p volume (intervalDomain a b) 2)⟫_ℝ) = 0 := by
  have hsymm : ∀ᵐ x ∂volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))),
      ((fun _ ↦ (1 : Matrix (Fin 1) (Fin 1) ℝ)) x).IsSymm :=
    ae_of_all _ fun _ ↦ Matrix.isSymm_one
  have key := mul_inner_value_eq_of_isWeakSolutionDirichlet hu hsjeq
  rw [inner_value_eq_zero_of_energyFormH1_eq_of_ne hsymm (sq_natCast_mul_pi_div_ne hab hjm).symm
    hsmeq hsjeq] at key ⊢
  rw [inner_value_eq_zero_of_energyFormH1_eq_of_ne hsymm (sq_natCast_mul_pi_div_ne hab hjk).symm
      hskeq hsjeq,
    (mul_eq_zero.1 key).resolve_left (sub_ne_zero.2 (sq_natCast_mul_pi_div_ne hab hjk))]
  ring

/-- The pairing of `u - s_m / (κ_m - κ_k) - t s_k` with every sine mode `s_j` vanishes, for a weak
solution `u` of `-u'' - κ_k u = s_m`, `m ≠ k`, with `⟪u, s_k⟫ = t ⟪s_k, s_k⟫`. -/
private theorem inner_value_sub_eq_zero (hab : a < b) {k m j : ℕ} (hmk : m ≠ k)
    {u sk sm sj : W1p0 volume (intervalDomain a b) 2}
    (hsk : W1p.value (sk : W1p volume (intervalDomain a b) 2)
      =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
        fun x ↦ Real.sin (k * π * (x 0 - a) / (b - a)))
    (hskeq : ∀ v : W1p0 volume (intervalDomain a b) 2,
      energyFormH1 (fun _ ↦ 1) 0 0 (sk : W1p volume (intervalDomain a b) 2)
          (v : W1p volume (intervalDomain a b) 2) =
        (k * π / (b - a)) ^ 2 * ⟪W1p.value (sk : W1p volume (intervalDomain a b) 2),
          W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ)
    (hsm : W1p.value (sm : W1p volume (intervalDomain a b) 2)
      =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
        fun x ↦ Real.sin (m * π * (x 0 - a) / (b - a)))
    (hsmeq : ∀ v : W1p0 volume (intervalDomain a b) 2,
      energyFormH1 (fun _ ↦ 1) 0 0 (sm : W1p volume (intervalDomain a b) 2)
          (v : W1p volume (intervalDomain a b) 2) =
        (m * π / (b - a)) ^ 2 * ⟪W1p.value (sm : W1p volume (intervalDomain a b) 2),
          W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ)
    (hu : ∀ v : W1p0 volume (intervalDomain a b) 2,
      energyFormH1 (fun _ ↦ 1) 0 (fun _ ↦ -(k * π / (b - a)) ^ 2)
          (u : W1p volume (intervalDomain a b) 2) (v : W1p volume (intervalDomain a b) 2) =
        ⟪W1p.value (sm : W1p volume (intervalDomain a b) 2),
          W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ)
    {t : ℝ} (ht : ⟪W1p.value (u : W1p volume (intervalDomain a b) 2),
        W1p.value (sk : W1p volume (intervalDomain a b) 2)⟫_ℝ =
      t * ⟪W1p.value (sk : W1p volume (intervalDomain a b) 2),
        W1p.value (sk : W1p volume (intervalDomain a b) 2)⟫_ℝ)
    (hsj : W1p.value (sj : W1p volume (intervalDomain a b) 2)
      =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
        fun x ↦ Real.sin (j * π * (x 0 - a) / (b - a)))
    (hsjeq : ∀ v : W1p0 volume (intervalDomain a b) 2,
      energyFormH1 (fun _ ↦ 1) 0 0 (sj : W1p volume (intervalDomain a b) 2)
          (v : W1p volume (intervalDomain a b) 2) =
        (j * π / (b - a)) ^ 2 * ⟪W1p.value (sj : W1p volume (intervalDomain a b) 2),
          W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ) :
    ⟪W1p.value (u : W1p volume (intervalDomain a b) 2),
        W1p.value (sj : W1p volume (intervalDomain a b) 2)⟫_ℝ -
      (((m * π / (b - a)) ^ 2 - (k * π / (b - a)) ^ 2)⁻¹ *
          ⟪W1p.value (sm : W1p volume (intervalDomain a b) 2),
            W1p.value (sj : W1p volume (intervalDomain a b) 2)⟫_ℝ +
        t * ⟪W1p.value (sk : W1p volume (intervalDomain a b) 2),
          W1p.value (sj : W1p volume (intervalDomain a b) 2)⟫_ℝ) = 0 := by
  by_cases hjk : j = k
  · subst hjk
    rw [show W1p.value (sj : W1p volume (intervalDomain a b) 2) =
      W1p.value (sk : W1p volume (intervalDomain a b) 2) from Lp.ext (hsj.trans hsk.symm)]
    exact inner_value_sub_eq_zero_left hab hmk hskeq hsmeq ht
  by_cases hjm : j = m
  · subst hjm
    rw [show W1p.value (sj : W1p volume (intervalDomain a b) 2) =
      W1p.value (sm : W1p volume (intervalDomain a b) 2) from Lp.ext (hsj.trans hsm.symm)]
    exact inner_value_sub_eq_zero_right hab hmk hskeq hsmeq hu t
  · exact inner_value_sub_eq_zero_of_ne hab hjk hjm hskeq hsmeq hsjeq hu t

/-- A weak solution `u` of `-u'' - κ_k u = s_m`, `m ≠ k`, with `⟪u, s_k⟫ = t ⟪s_k, s_k⟫` is
`s_m / (κ_m - κ_k) + t s_k`: their difference is orthogonal to every sine mode. -/
private theorem value_eq_of_isWeakSolutionDirichlet (hab : a < b) {k m : ℕ} (hmk : m ≠ k)
    {u sk sm : W1p0 volume (intervalDomain a b) 2}
    (hsk : W1p.value (sk : W1p volume (intervalDomain a b) 2)
      =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
        fun x ↦ Real.sin (k * π * (x 0 - a) / (b - a)))
    (hskeq : ∀ v : W1p0 volume (intervalDomain a b) 2,
      energyFormH1 (fun _ ↦ 1) 0 0 (sk : W1p volume (intervalDomain a b) 2)
          (v : W1p volume (intervalDomain a b) 2) =
        (k * π / (b - a)) ^ 2 * ⟪W1p.value (sk : W1p volume (intervalDomain a b) 2),
          W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ)
    (hsm : W1p.value (sm : W1p volume (intervalDomain a b) 2)
      =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
        fun x ↦ Real.sin (m * π * (x 0 - a) / (b - a)))
    (hsmeq : ∀ v : W1p0 volume (intervalDomain a b) 2,
      energyFormH1 (fun _ ↦ 1) 0 0 (sm : W1p volume (intervalDomain a b) 2)
          (v : W1p volume (intervalDomain a b) 2) =
        (m * π / (b - a)) ^ 2 * ⟪W1p.value (sm : W1p volume (intervalDomain a b) 2),
          W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ)
    (hu : ∀ v : W1p0 volume (intervalDomain a b) 2,
      energyFormH1 (fun _ ↦ 1) 0 (fun _ ↦ -(k * π / (b - a)) ^ 2)
          (u : W1p volume (intervalDomain a b) 2) (v : W1p volume (intervalDomain a b) 2) =
        ⟪W1p.value (sm : W1p volume (intervalDomain a b) 2),
          W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ)
    {t : ℝ} (ht : ⟪W1p.value (u : W1p volume (intervalDomain a b) 2),
        W1p.value (sk : W1p volume (intervalDomain a b) 2)⟫_ℝ =
      t * ⟪W1p.value (sk : W1p volume (intervalDomain a b) 2),
        W1p.value (sk : W1p volume (intervalDomain a b) 2)⟫_ℝ) :
    W1p.value (u : W1p volume (intervalDomain a b) 2) =
      ((m * π / (b - a)) ^ 2 - (k * π / (b - a)) ^ 2)⁻¹ •
          W1p.value (sm : W1p volume (intervalDomain a b) 2) +
        t • W1p.value (sk : W1p volume (intervalDomain a b) 2) := by
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_setIntegral_mul_sin_eq_zero hab _ fun j _ ↦ ?_
  obtain ⟨sj, hsj, hsjeq⟩ := exists_value_ae_eq_sin hab j
  rw [setIntegral_mul_sin_eq_inner _ hsj, inner_sub_left, inner_add_left, real_inner_smul_left,
    real_inner_smul_left]
  exact inner_value_sub_eq_zero hab hmk hsk hskeq hsm hsmeq hu ht hsj hsjeq

/-- A function whose value is `c s_m + t s_k` is `c s_m + t s_k` in `H¹(a, b)`. -/
private theorem coe_eq_smul_add_smul_of_value_ae_eq {k m : ℕ} (c t : ℝ)
    {u sk sm : W1p0 volume (intervalDomain a b) 2}
    (hsk : W1p.value (sk : W1p volume (intervalDomain a b) 2)
      =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
        fun x ↦ Real.sin (k * π * (x 0 - a) / (b - a)))
    (hsm : W1p.value (sm : W1p volume (intervalDomain a b) 2)
      =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
        fun x ↦ Real.sin (m * π * (x 0 - a) / (b - a)))
    (hu : W1p.value (u : W1p volume (intervalDomain a b) 2)
      =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
        fun x ↦ c * Real.sin (m * π * (x 0 - a) / (b - a)) +
          t * Real.sin (k * π * (x 0 - a) / (b - a))) :
    (u : W1p volume (intervalDomain a b) 2) =
      c • (sm : W1p volume (intervalDomain a b) 2) +
        t • (sk : W1p volume (intervalDomain a b) 2) :=
  W1p.ext_value <| Lp.ext <| by
    filter_upwards [hu, W1p.value_add_ae (c • (sm : W1p volume (intervalDomain a b) 2))
      (t • (sk : W1p volume (intervalDomain a b) 2)),
      W1p.value_smul_ae c (sm : W1p volume (intervalDomain a b) 2),
      W1p.value_smul_ae t (sk : W1p volume (intervalDomain a b) 2), hsm, hsk]
      with x h1 h2 h3 h4 h5 h6
    rw [h1, h2, Pi.add_apply, h3, h4, Pi.smul_apply, Pi.smul_apply, h5, h6, smul_eq_mul,
      smul_eq_mul]

/-- The energy form of `-u''` is linear in its left argument. -/
private theorem energyFormH1_add_smul_smul_left (c t : ℝ)
    (u w v : W1p volume (intervalDomain a b) 2) :
    energyFormH1 (fun _ ↦ 1) 0 0 (c • u + t • w) v =
      c * energyFormH1 (fun _ ↦ 1) 0 0 u v + t * energyFormH1 (fun _ ↦ 1) 0 0 w v := by
  rw [energyFormH1_add_left (c := 0) (memLp_energyIntegrand_one_zero_const 0),
    energyFormH1_smul_left, energyFormH1_smul_left]

/-- The `L²` pairing of values is linear in its left argument. -/
private theorem inner_value_add_smul_smul_left (c t : ℝ)
    (u w v : W1p volume (intervalDomain a b) 2) :
    ⟪W1p.value (c • u + t • w), W1p.value v⟫_ℝ =
      c * ⟪W1p.value u, W1p.value v⟫_ℝ + t * ⟪W1p.value w, W1p.value v⟫_ℝ := by
  rw [W1p.value_add, inner_add_left, inner_value_smul_left, inner_value_smul_left]

/-- Conversely, `s_m / (κ_m - κ_k) + t s_k` is a weak solution of `-u'' - κ_k u = s_m`. -/
private theorem isWeakSolutionDirichlet_of_coe_eq (hab : a < b) {k m : ℕ} (hmk : m ≠ k)
    {u : W1p0 volume (intervalDomain a b) 2} {sk sm : W1p0 volume (intervalDomain a b) 2}
    (hskeq : ∀ v : W1p0 volume (intervalDomain a b) 2,
      energyFormH1 (fun _ ↦ 1) 0 0 (sk : W1p volume (intervalDomain a b) 2)
          (v : W1p volume (intervalDomain a b) 2) =
        (k * π / (b - a)) ^ 2 * ⟪W1p.value (sk : W1p volume (intervalDomain a b) 2),
          W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ)
    (hsmeq : ∀ v : W1p0 volume (intervalDomain a b) 2,
      energyFormH1 (fun _ ↦ 1) 0 0 (sm : W1p volume (intervalDomain a b) 2)
          (v : W1p volume (intervalDomain a b) 2) =
        (m * π / (b - a)) ^ 2 * ⟪W1p.value (sm : W1p volume (intervalDomain a b) 2),
          W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ)
    {t : ℝ} (hus : (u : W1p volume (intervalDomain a b) 2) =
      ((m * π / (b - a)) ^ 2 - (k * π / (b - a)) ^ 2)⁻¹ •
          (sm : W1p volume (intervalDomain a b) 2) +
        t • (sk : W1p volume (intervalDomain a b) 2))
    (v : W1p0 volume (intervalDomain a b) 2) :
    energyFormH1 (fun _ ↦ 1) 0 (fun _ ↦ -(k * π / (b - a)) ^ 2)
        (u : W1p volume (intervalDomain a b) 2) (v : W1p volume (intervalDomain a b) 2) =
      ⟪W1p.value (sm : W1p volume (intervalDomain a b) 2),
        W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ := by
  have hc : ((m * π / (b - a)) ^ 2 - (k * π / (b - a)) ^ 2)⁻¹ *
      ((m * π / (b - a)) ^ 2 - (k * π / (b - a)) ^ 2) = 1 :=
    inv_mul_cancel₀ (sub_ne_zero.2 (sq_natCast_mul_pi_div_ne hab hmk))
  have e1 := energyFormH1_one_zero_neg ((k * π / (b - a)) ^ 2)
    (u : W1p volume (intervalDomain a b) 2) (v : W1p volume (intervalDomain a b) 2)
  have e2 := energyFormH1_add_smul_smul_left (((m * π / (b - a)) ^ 2 - (k * π / (b - a)) ^ 2)⁻¹)
    t (sm : W1p volume (intervalDomain a b) 2) (sk : W1p volume (intervalDomain a b) 2)
    (v : W1p volume (intervalDomain a b) 2)
  have e3 := inner_value_add_smul_smul_left (((m * π / (b - a)) ^ 2 - (k * π / (b - a)) ^ 2)⁻¹)
    t (sm : W1p volume (intervalDomain a b) 2) (sk : W1p volume (intervalDomain a b) 2)
    (v : W1p volume (intervalDomain a b) 2)
  rw [← hus] at e2 e3
  linear_combination e1 + e2 - (k * π / (b - a)) ^ 2 * e3 +
    ((m * π / (b - a)) ^ 2 - (k * π / (b - a)) ^ 2)⁻¹ * hsmeq v + t * hskeq v +
    ⟪W1p.value (sm : W1p volume (intervalDomain a b) 2),
      W1p.value (v : W1p volume (intervalDomain a b) 2)⟫_ℝ * hc

/-- **The resonant problem with forcing by another sine mode.** At the Dirichlet eigenvalue
`κ_k = (k π / (b - a))²` of `(a, b)`, let `f` be the sine mode
`s_m(x) = sin (m π (x - a) / (b - a))` with `m ≠ k`. The weak solutions of `-u'' - κ_k u = f`
with `u(a) = u(b) = 0` are exactly the functions `s_m / (κ_m - κ_k) + t s_k`, `t ∈ ℝ`: the
solution is unique only modulo the kernel `span s_k`. Such solutions exist
(`TauCeti.PDE.exists_isWeakSolutionDirichlet_of_ae_eq_sin`). -/
theorem isWeakSolutionDirichlet_iff_exists_value_ae_eq_of_ae_eq_sin (hab : a < b) {k m : ℕ}
    (hmk : m ≠ k)
    (f : Lp ℝ 2 (volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))))
    (hf : f =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
      fun x ↦ Real.sin (m * π * (x 0 - a) / (b - a)))
    (u : W1p0 volume (intervalDomain a b) 2) :
    IsWeakSolutionDirichlet (fun _ ↦ 1) 0 (fun _ ↦ -(k * π / (b - a)) ^ 2) f u ↔
      ∃ t : ℝ, W1p.value (u : W1p volume (intervalDomain a b) 2)
        =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
          fun x ↦ Real.sin (m * π * (x 0 - a) / (b - a)) /
              ((m * π / (b - a)) ^ 2 - (k * π / (b - a)) ^ 2) +
            t * Real.sin (k * π * (x 0 - a) / (b - a)) := by
  obtain ⟨sk, hsk, hskeq⟩ := exists_value_ae_eq_sin hab k
  obtain ⟨sm, hsm, hsmeq⟩ := exists_value_ae_eq_sin hab m
  rw [isWeakSolutionDirichlet_one_zero_const_iff]
  simp only [inner_eq_inner_value_of_ae_eq f hf hsm]
  refine ⟨fun hu ↦ ?_, fun ⟨t, ht⟩ ↦ isWeakSolutionDirichlet_of_coe_eq hab hmk hskeq hsmeq
    (coe_eq_smul_add_smul_of_value_ae_eq _ t hsk hsm (ht.trans (ae_of_all _ fun x ↦ by
      simp only [div_eq_inv_mul]))) ⟩
  obtain ⟨t, ht⟩ := exists_inner_eq_mul_inner_self
    (W1p.value (u : W1p volume (intervalDomain a b) 2))
    (W1p.value (sk : W1p volume (intervalDomain a b) 2))
  refine ⟨t, ?_⟩
  rw [value_eq_of_isWeakSolutionDirichlet hab hmk hsk hskeq hsm hsmeq hu ht]
  filter_upwards [Lp.coeFn_add (((m * π / (b - a)) ^ 2 - (k * π / (b - a)) ^ 2)⁻¹ •
      W1p.value (sm : W1p volume (intervalDomain a b) 2))
      (t • W1p.value (sk : W1p volume (intervalDomain a b) 2)),
    Lp.coeFn_smul (((m * π / (b - a)) ^ 2 - (k * π / (b - a)) ^ 2)⁻¹)
      (W1p.value (sm : W1p volume (intervalDomain a b) 2)),
    Lp.coeFn_smul t (W1p.value (sk : W1p volume (intervalDomain a b) 2)), hsm, hsk]
    with x h1 h2 h3 h4 h5
  rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.smul_apply, h4, h5, smul_eq_mul, smul_eq_mul]
  ring

/-- At the Dirichlet eigenvalue `κ_k`, the problem `-u'' - κ_k u = s_m` with a sine mode `s_m`,
`m ≠ k`, has a weak solution, since `s_m` is orthogonal to the kernel `span s_k`. -/
theorem exists_isWeakSolutionDirichlet_of_ae_eq_sin (hab : a < b) {k m : ℕ} (hmk : m ≠ k)
    (f : Lp ℝ 2 (volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))))
    (hf : f =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
      fun x ↦ Real.sin (m * π * (x 0 - a) / (b - a))) :
    ∃ u : W1p0 volume (intervalDomain a b) 2,
      IsWeakSolutionDirichlet (fun _ ↦ 1) 0 (fun _ ↦ -(k * π / (b - a)) ^ 2) f u := by
  obtain ⟨sk, hsk, hskeq⟩ := exists_value_ae_eq_sin hab k
  obtain ⟨sm, hsm, hsmeq⟩ := exists_value_ae_eq_sin hab m
  rw [exists_isWeakSolutionDirichlet_iff_setIntegral_mul_sin_eq_zero hab,
    setIntegral_mul_sin_eq_inner _ hsk, show f = W1p.value (sm : W1p volume (intervalDomain a b) 2)
      from Lp.ext (hf.trans hsm.symm)]
  exact inner_value_eq_zero_of_energyFormH1_eq_of_ne (ae_of_all _ fun _ ↦ Matrix.isSymm_one)
    (sq_natCast_mul_pi_div_ne hab hmk) hsmeq hskeq

/-! ### The examples on `(0, π)` -/

/-- The first sine mode of `(0, π)` is `sin x`. -/
private theorem sin_one_mul_pi_div (x : ℝ) :
    Real.sin (((1 : ℕ) : ℝ) * π * (x - 0) / (π - 0)) = Real.sin x := by
  rw [Nat.cast_one, one_mul, sub_zero, sub_zero, mul_div_cancel_left₀ _ Real.pi_ne_zero]

/-- The first Dirichlet eigenvalue of `(0, π)` is `1`. -/
private theorem sq_one_mul_pi_div : (((1 : ℕ) : ℝ) * π / (π - 0)) ^ 2 = 1 := by
  rw [Nat.cast_one, one_mul, sub_zero, div_self Real.pi_ne_zero, one_pow]

/-- **`-u'' - u = 1` has no weak solution on `(0, π)`.** The constant forcing `1` is not
orthogonal to the kernel `span (sin x)`, since `∫_0^π sin x dx = 2`. -/
theorem not_exists_isWeakSolutionDirichlet_neg_one_of_ae_eq_one
    (f : Lp ℝ 2 (volume.restrict (intervalDomain 0 π : Set (EuclideanSpace ℝ (Fin 1)))))
    (hf : f =ᵐ[volume.restrict (intervalDomain 0 π : Set (EuclideanSpace ℝ (Fin 1)))]
      fun _ ↦ 1) :
    ¬∃ u : W1p0 volume (intervalDomain 0 π) 2,
      IsWeakSolutionDirichlet (fun _ ↦ 1) 0 (fun _ ↦ -1) f u := by
  have h := exists_isWeakSolutionDirichlet_iff_setIntegral_mul_sin_eq_zero Real.pi_pos 1 f
  simp only [sq_one_mul_pi_div, sin_one_mul_pi_div] at h
  rw [h, integral_congr_ae (g := fun x ↦ Real.sin (x 0)),
    setIntegral_intervalDomain Real.pi_pos.le Real.sin, integral_sin]
  · norm_num
  · filter_upwards [hf] with x hx
    rw [hx, one_mul]

/-- The second sine mode of `(0, π)` is `sin 2x`. -/
private theorem sin_two_mul_pi_div (x : ℝ) :
    Real.sin (((2 : ℕ) : ℝ) * π * (x - 0) / (π - 0)) = Real.sin (2 * x) := by
  rw [Nat.cast_ofNat, sub_zero, sub_zero, mul_assoc, mul_comm π, ← mul_assoc,
    mul_div_cancel_right₀ _ Real.pi_ne_zero]

/-- The second Dirichlet eigenvalue of `(0, π)` is `4`. -/
private theorem sq_two_mul_pi_div : (((2 : ℕ) : ℝ) * π / (π - 0)) ^ 2 = 4 := by
  rw [Nat.cast_ofNat, sub_zero, mul_div_cancel_right₀ _ Real.pi_ne_zero]
  norm_num

/-- **The resonant problem `-u'' - u = sin 2x` on `(0, π)`.** The forcing `sin 2x` is orthogonal
to the kernel `span (sin x)`, so the problem is solvable
(`TauCeti.PDE.exists_isWeakSolutionDirichlet_of_ae_eq_sin`), and its weak solutions are exactly
the functions `sin (2x) / 3 + t sin x`, `t ∈ ℝ`: uniqueness holds only modulo the kernel. -/
theorem isWeakSolutionDirichlet_neg_one_iff_of_ae_eq_sin_two_mul
    (f : Lp ℝ 2 (volume.restrict (intervalDomain 0 π : Set (EuclideanSpace ℝ (Fin 1)))))
    (hf : f =ᵐ[volume.restrict (intervalDomain 0 π : Set (EuclideanSpace ℝ (Fin 1)))]
      fun x ↦ Real.sin (2 * x 0))
    (u : W1p0 volume (intervalDomain 0 π) 2) :
    IsWeakSolutionDirichlet (fun _ ↦ 1) 0 (fun _ ↦ -1) f u ↔
      ∃ t : ℝ, W1p.value (u : W1p volume (intervalDomain 0 π) 2)
        =ᵐ[volume.restrict (intervalDomain 0 π : Set (EuclideanSpace ℝ (Fin 1)))]
          fun x ↦ Real.sin (2 * x 0) / 3 + t * Real.sin (x 0) := by
  have h := isWeakSolutionDirichlet_iff_exists_value_ae_eq_of_ae_eq_sin Real.pi_pos
    (k := 1) (m := 2) (by norm_num) f (by simpa only [sin_two_mul_pi_div] using hf) u
  simp only [sq_one_mul_pi_div, sq_two_mul_pi_div, sin_one_mul_pi_div, sin_two_mul_pi_div] at h
  rwa [show (4 : ℝ) - 1 = 3 by norm_num] at h

/-- **`-u'' - 2u = ℓ` is uniquely solvable on `(0, π)`.** The Dirichlet eigenvalues of `(0, π)` are
the squares `k²`, and `2` is not one of them, so the homogeneous problem has only the trivial
solution and the problem has exactly one weak solution for every `ℓ ∈ H⁻¹(0, π)`. This holds
although the form is not coercive, since `2` exceeds the first eigenvalue `1`
(`TauCeti.PDE.not_isCoercive_energyFormH1L0_of_le`). -/
theorem existsUnique_forall_energyFormH1_neg_two_eq
    (ℓ : StrongDual ℝ (W1p0 volume (intervalDomain 0 π) 2)) :
    ∃! u : W1p0 volume (intervalDomain 0 π) 2, ∀ v : W1p0 volume (intervalDomain 0 π) 2,
      energyFormH1 (fun _ ↦ 1) 0 (fun _ ↦ -2) (u : W1p volume (intervalDomain 0 π) 2)
        (v : W1p volume (intervalDomain 0 π) 2) = ℓ v := by
  refine (forall_existsUnique_forall_energyFormH1_eq_iff Real.pi_pos 2).2 (fun k hk0 hk ↦ ?_) ℓ
  rw [sub_zero, mul_div_cancel_right₀ _ Real.pi_ne_zero] at hk
  have hk' : k ^ 2 = 2 := by exact_mod_cast hk.symm
  have : k ≤ 1 := by nlinarith
  interval_cases k
  norm_num at hk'

end PDE

end TauCeti
