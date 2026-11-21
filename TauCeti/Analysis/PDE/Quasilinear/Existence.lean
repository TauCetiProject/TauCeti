/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.DirichletProblem
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.Analysis.Convex.SchauderFixedPoint
import TauCeti.Analysis.PDE.DirichletProblem.ContinuousDependence
import TauCeti.Analysis.Sobolev.RellichKondrachov
import TauCeti.MeasureTheory.Function.StronglyMeasurable.Caratheodory
import TauCeti.Topology.Instances.Matrix

/-!
# Existence for quasilinear divergence-form equations

Let `Ω ⊆ ℝⁿ⁺¹` be a bounded open set, contained in a ball `B(z, R)`, and let
`A : Ω × ℝ → Mat(n + 1, ℝ)` be a Carathéodory coefficient: `x ↦ A(x, s)` is measurable for every
`s`, and `s ↦ A(x, s)` is continuous for almost every `x`. Suppose that every `A(·, s)` is
uniformly elliptic and bounded with the same constants `0 < λ ≤ Λ`
(`TauCeti.PDE.UniformlyEllipticOn`). For boundary values `g ∈ H¹(Ω)` and a forcing
`ℓ ∈ H⁻¹(Ω) = (H¹₀(Ω))*` consider the quasilinear Dirichlet problem

`-div (A(x, u) ∇u) = ℓ` in `Ω`, `u - g ∈ H¹₀(Ω)`,

whose weak form is `∫_Ω ⟨A(x, u) ∇u, ∇φ⟩ = ℓ φ` for every `φ ∈ H¹₀(Ω)`, that is
`energyFormH1 (fun x ↦ A x (W1p.value u x)) 0 0 u φ = ℓ φ`. For `ℓ φ = ∫ f φ - ∫ ⟪F, ∇φ⟫` with
`f ∈ L²(Ω)` and `F ∈ L²(Ω; ℝⁿ⁺¹)` (`TauCeti.PDE.dirichletForcing`,
`TauCeti.PDE.divergenceForcing`) this is `-div (A(x, u) ∇u) = f + div F`.

This file proves that the problem has a weak solution on every bounded open set
(`TauCeti.PDE.exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq`), in every
dimension and with no regularity of `∂Ω`, and that every weak solution satisfies the energy bound
`‖u - g‖_{H¹} ≤ 2 ((2R)² + 1) (‖ℓ‖ + Λ ‖g‖) / λ`
(`TauCeti.PDE.norm_sub_le_of_forall_energyFormH1_quasilinear_eq_of_subset_ball`), which depends
on `A` only through `λ` and `Λ`. No uniqueness is claimed. Since a weak solution `u` solves the
linear equation with the measurable coefficient `a = A(·, u)`, `λ ≤ a ≤ Λ`, every regularity
theorem for linear equations with bounded measurable coefficients applies to it.

## The argument

The proof is Schauder's compact-map argument, run in `L²(Ω)`. For `v ∈ L²(Ω)`, freezing the
coefficient at `v` gives the linear problem `-div (A(x, v) ∇u) = ℓ`, `u - g ∈ H¹₀(Ω)`, whose
coefficient `x ↦ A(x, v(x))` is measurable
(`MeasureTheory.AEStronglyMeasurable.apply_of_forall_of_continuousAt`) and uniformly elliptic
with the constants `λ, Λ`. By Lax–Milgram it has exactly one weak solution `S v`, and the energy
estimate bounds `‖S v - g‖` by a constant `K` that does not depend on `v`.
Let `T v ∈ L²(Ω)` be the value of `S v`. The map `S` is `TauCeti.PDE.frozenSolution`, and its
bound, the continuity of `T` and the compactness of its range are public
(`TauCeti.PDE.norm_frozenSolution_sub_le`, `TauCeti.PDE.continuous_value_frozenSolution`,
`TauCeti.PDE.isCompact_closure_range_value_frozenSolution`).

* `T` is continuous. If `vₖ → v` in `L²(Ω)`, every subsequence has a further subsequence along
  which `vₖ → v` almost everywhere, so `A(x, vₖ(x)) → A(x, v(x))` almost everywhere. The frozen
  coefficients are bounded by `Λ` uniformly, so the solutions converge in `H¹(Ω)` by dominated
  convergence (`TauCeti.PDE.tendsto_of_forall_energyFormH1_eq_of_tendsto_ae`). More generally,
  the frozen solution depends continuously on the coefficient, the boundary values and the
  forcing together (`TauCeti.PDE.tendsto_frozenSolution`).
* `T` has relatively compact range. Its values lie in the translate by the value of `g` of the
  image of the ball of radius `K + 1` of `H¹₀(Ω)` under the value map, which is relatively compact
  by the Rellich–Kondrachov theorem (`TauCeti.W1p0.isCompactOperator_valueL`); no boundary
  regularity is needed, because `S v - g` lies in `H¹₀(Ω)`.

Schauder's theorem (`TauCeti.schauderFixedPoint_closedConvex_continuousOn`), applied to `T` on
all of `L²(Ω)`, gives a fixed point `v = T v`, and `u = S v` is a weak solution, since the value of
`u` is `v`.

## References

* M. Chipot, *Elliptic Equations: An Introductory Course*, Birkhäuser, 2009, Section 11.2
  (quasilinear equations). This is the `L²` argument followed here: freeze the coefficient,
  solve the linear problem, prove continuity of `T` through almost everywhere convergent
  subsequences and dominated convergence, compactness by Rellich, and conclude by Schauder.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 11.1 (Schauder's fixed-point theorem), Theorem 8.3 (the linear Dirichlet problem) and
  Theorem 7.22 (the Rellich–Kondrachov theorem). Their quasilinear application, Section 11.3,
  takes a different route, through Hölder spaces.
-/

public section

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped Matrix Topology

namespace TauCeti

namespace PDE

attribute [local instance] instSeminormedAddCommGroupW1p instNormedSpaceW1p

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
  {A : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {lam Lam : ℝ} {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}

/-- The coefficient frozen at a measurable function is measurable. -/
private theorem aestronglyMeasurable_comp
    (hAm : ∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega))
    (hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x))
    {v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hv : AEStronglyMeasurable v (volume.restrict Omega)) :
    AEStronglyMeasurable (fun x => A x (v x)) (volume.restrict Omega) :=
  hv.apply_of_forall_of_continuousAt hAm (hAc.mono fun _ hx => hx.continuousAt)

/-- The energy integrand of a frozen coefficient is essentially bounded. -/
private theorem memLp_energyIntegrand_comp
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAm : ∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega))
    (hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x))
    {v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hv : AEStronglyMeasurable v (volume.restrict Omega)) :
    MemLp (fun x => energyIntegrand (A x (v x)) 0 0) ⊤ (volume.restrict Omega) :=
  memLp_energyIntegrand_of_bounds (UniformlyEllipticOn.apply_of_forall hA v).upper_nonneg
    (aestronglyMeasurable_comp hAm hAc hv) aestronglyMeasurable_const aestronglyMeasurable_const
    (fun _ hx η ξ => (UniformlyEllipticOn.apply_of_forall hA v).upper_bound hx η ξ) (beta := 0)
    (fun _ _ => by simp) (gamma := 0) (fun _ _ => by simp)

/-- The energy form of a frozen coefficient is coercive on `H¹₀(Ω)` with the constant
`λ / (2 ((2R)² + 1))`, which does not depend on the function the coefficient is frozen at. -/
private theorem mul_norm_sq_le_energyFormH1_comp
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAm : ∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega))
    (hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x))
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ ball z R)
    {v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hv : AEStronglyMeasurable v (volume.restrict Omega))
    (w : W1p0 volume Omega 2) :
    lam / (2 * ((2 * R) ^ 2 + 1)) * ‖w‖ ^ 2 ≤
      energyFormH1 (fun x => A x (v x)) 0 0 (w : W1p volume Omega 2) w := by
  have h := UniformlyEllipticOn.mul_norm_sq_le_energyFormH1_self_of_subset_ball
    (UniformlyEllipticOn.apply_of_forall hA v)
    (aestronglyMeasurable_comp hAm hAc hv) (b := 0) (c := 0) aestronglyMeasurable_const
    aestronglyMeasurable_const (beta := 0) (gamma := 0) (fun _ _ => by simp) (fun _ _ => by simp)
    (fun _ _ => by simp) hball w.property
  have hlam := (hA 0).pos.ne'
  rwa [show (lam ^ 2 - 0 ^ 2 * (2 * R) ^ 2) / (2 * lam * ((2 * R) ^ 2 + 1)) =
    lam / (2 * ((2 * R) ^ 2 + 1)) by field_simp; ring] at h

/-- The frozen-coefficient solution map `S` of the quasilinear Dirichlet problem: for
`v : ℝⁿ⁺¹ → ℝ`, the weak solution `u = S v` of the linear Dirichlet problem
`-div (A(x, v) ∇u) = ℓ`, `u - g ∈ H¹₀(Ω)`, whose coefficient is `A` frozen at `v`.

Under the hypotheses of
`TauCeti.PDE.exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq` and for
measurable `v`, this problem has exactly one solution, and `frozenSolution A g ℓ v` is it
(`TauCeti.PDE.frozenSolution_sub_mem_w1p0Submodule`,
`TauCeti.PDE.forall_energyFormH1_frozenSolution_eq`,
`TauCeti.PDE.eq_frozenSolution_of_sub_mem_w1p0Submodule_of_forall_energyFormH1_eq`). -/
noncomputable def frozenSolution
    (A : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (g : W1p volume Omega 2) (ℓ : StrongDual ℝ (W1p0 volume Omega 2))
    (v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) : W1p volume Omega 2 :=
  Classical.epsilon fun u => u - g ∈ w1p0Submodule volume Omega 2 ∧
    ∀ φ : W1p0 volume Omega 2, energyFormH1 (fun x => A x (v x)) 0 0 u φ = ℓ φ

/-- Lax–Milgram for the frozen problem: it has exactly one weak solution. -/
private theorem existsUnique_frozen
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAm : ∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega))
    (hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x))
    (hΩ : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (g : W1p volume Omega 2) (ℓ : StrongDual ℝ (W1p0 volume Omega 2))
    {v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hv : AEStronglyMeasurable v (volume.restrict Omega)) :
    ∃! u : W1p volume Omega 2, u - g ∈ w1p0Submodule volume Omega 2 ∧
      ∀ φ : W1p0 volume Omega 2, energyFormH1 (fun x => A x (v x)) 0 0 u φ = ℓ φ := by
  have hR := hΩ.subset_ball (0 : EuclideanSpace ℝ (Fin (n + 1)))
  obtain ⟨R, hball⟩ := hR
  exact UniformlyEllipticOn.existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_of_subset_ball
    (UniformlyEllipticOn.apply_of_forall hA v) (aestronglyMeasurable_comp hAm hAc hv)
    (b := 0) (c := 0) aestronglyMeasurable_const aestronglyMeasurable_const (beta := 0)
    (gamma := 0) (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => by simp) hball
    (by rw [zero_mul]; exact (hA 0).pos) ℓ g

private theorem frozenSolution_spec
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAm : ∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega))
    (hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x))
    (hΩ : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (g : W1p volume Omega 2) (ℓ : StrongDual ℝ (W1p0 volume Omega 2))
    {v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hv : AEStronglyMeasurable v (volume.restrict Omega)) :
    frozenSolution A g ℓ v - g ∈ w1p0Submodule volume Omega 2 ∧
      ∀ φ : W1p0 volume Omega 2,
        energyFormH1 (fun x => A x (v x)) 0 0 (frozenSolution A g ℓ v) φ = ℓ φ :=
  Classical.epsilon_spec (existsUnique_frozen hA hAm hAc hΩ g ℓ hv).exists

/-- The frozen solution has the boundary values `g`: `S v - g ∈ H¹₀(Ω)`. -/
theorem frozenSolution_sub_mem_w1p0Submodule
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAm : ∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega))
    (hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x))
    (hΩ : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (g : W1p volume Omega 2) (ℓ : StrongDual ℝ (W1p0 volume Omega 2))
    {v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hv : AEStronglyMeasurable v (volume.restrict Omega)) :
    frozenSolution A g ℓ v - g ∈ w1p0Submodule volume Omega 2 :=
  (frozenSolution_spec hA hAm hAc hΩ g ℓ hv).1

/-- The frozen solution solves `-div (A(x, v) ∇u) = ℓ` weakly. -/
theorem forall_energyFormH1_frozenSolution_eq
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAm : ∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega))
    (hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x))
    (hΩ : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (g : W1p volume Omega 2) (ℓ : StrongDual ℝ (W1p0 volume Omega 2))
    {v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hv : AEStronglyMeasurable v (volume.restrict Omega))
    (φ : W1p0 volume Omega 2) :
    energyFormH1 (fun x => A x (v x)) 0 0 (frozenSolution A g ℓ v) φ = ℓ φ :=
  (frozenSolution_spec hA hAm hAc hΩ g ℓ hv).2 φ

/-- Uniqueness for the frozen problem: every `u` with `u - g ∈ H¹₀(Ω)` solving
`-div (A(x, v) ∇u) = ℓ` weakly is the frozen solution `S v`. -/
theorem eq_frozenSolution_of_sub_mem_w1p0Submodule_of_forall_energyFormH1_eq
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAm : ∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega))
    (hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x))
    (hΩ : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    {g u : W1p volume Omega 2} {ℓ : StrongDual ℝ (W1p0 volume Omega 2)}
    {v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hv : AEStronglyMeasurable v (volume.restrict Omega))
    (hug : u - g ∈ w1p0Submodule volume Omega 2)
    (hu : ∀ φ : W1p0 volume Omega 2, energyFormH1 (fun x => A x (v x)) 0 0 u φ = ℓ φ) :
    u = frozenSolution A g ℓ v :=
  (existsUnique_frozen hA hAm hAc hΩ g ℓ hv).unique ⟨hug, hu⟩
    (frozenSolution_spec hA hAm hAc hΩ g ℓ hv)

/-- The energy form of a frozen coefficient has norm at most `Λ` as a bilinear form on `H¹(Ω)`. -/
private theorem norm_energyFormH1L_comp_le
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAm : ∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega))
    (hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x))
    {v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hv : AEStronglyMeasurable v (volume.restrict Omega)) :
    ‖energyFormH1L (memLp_energyIntegrand_comp hA hAm hAc hv)‖ ≤ Lam := by
  simpa using norm_energyFormH1L_le_of_bounds (memLp_energyIntegrand_comp hA hAm hAc hv)
    (hA 0).upper_nonneg ((ae_restrict_mem Omega.isOpen.measurableSet).mono fun x hx η ξ =>
      (UniformlyEllipticOn.apply_of_forall hA v).upper_bound hx η ξ)
    le_rfl le_rfl (beta := 0) (gamma := 0) (by simp) (by simp)

/-- The energy bound for the linear problem with a frozen coefficient: if `u - g ∈ H¹₀(Ω)` and
`-div (A(x, v) ∇u) = ℓ` weakly, then `‖u - g‖ ≤ 2 ((2R)² + 1) (‖ℓ‖ + Λ ‖g‖) / λ`, whatever `v`. -/
private theorem norm_sub_le_of_forall_energyFormH1_comp_eq
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAm : ∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega))
    (hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x))
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ ball z R)
    {g u : W1p volume Omega 2} {ℓ : StrongDual ℝ (W1p0 volume Omega 2)}
    {v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hv : AEStronglyMeasurable v (volume.restrict Omega))
    (hug : u - g ∈ w1p0Submodule volume Omega 2)
    (hu : ∀ φ : W1p0 volume Omega 2, energyFormH1 (fun x => A x (v x)) 0 0 u φ = ℓ φ) :
    ‖u - g‖ ≤ 2 * ((2 * R) ^ 2 + 1) * (‖ℓ‖ + Lam * ‖g‖) / lam := by
  have hlam := (hA 0).pos
  have hcoeff := memLp_energyIntegrand_comp hA hAm hAc hv
  have h := norm_sub_le_of_sub_mem_w1p0Submodule_of_forall_energyFormH1_eq hcoeff
    (by positivity) (mul_norm_sq_le_energyFormH1_comp hA hAm hAc hball hv) hug hu
  calc ‖u - g‖ ≤ (‖ℓ‖ + ‖energyFormH1L hcoeff‖ * ‖g‖) / (lam / (2 * ((2 * R) ^ 2 + 1))) := h
    _ ≤ (‖ℓ‖ + Lam * ‖g‖) / (lam / (2 * ((2 * R) ^ 2 + 1))) := by
      gcongr
      exact norm_energyFormH1L_comp_le hA hAm hAc hv
    _ = 2 * ((2 * R) ^ 2 + 1) * (‖ℓ‖ + Lam * ‖g‖) / lam := by field_simp

/-- The bound `‖S v - g‖ ≤ 2 ((2R)² + 1) (‖ℓ‖ + Λ ‖g‖) / λ` on the frozen solutions, uniform in
the function `v` the coefficient is frozen at. -/
theorem norm_frozenSolution_sub_le
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAm : ∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega))
    (hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x))
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ ball z R)
    (g : W1p volume Omega 2) (ℓ : StrongDual ℝ (W1p0 volume Omega 2))
    {v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hv : AEStronglyMeasurable v (volume.restrict Omega)) :
    ‖frozenSolution A g ℓ v - g‖ ≤ 2 * ((2 * R) ^ 2 + 1) * (‖ℓ‖ + Lam * ‖g‖) / lam :=
  have hspec := frozenSolution_spec hA hAm hAc (isBounded_ball.subset hball) g ℓ hv
  norm_sub_le_of_forall_energyFormH1_comp_eq hA hAm hAc hball hv hspec.1 hspec.2

/-- For one frozen coefficient the solution depends Lipschitz continuously on the data: with
`C = λ / (2 ((2R)² + 1))`, `‖S' - S‖ ≤ ‖g' - g‖ + (‖ℓ' - ℓ‖ + Λ ‖g' - g‖) / C` for the frozen
solutions `S'` and `S` with data `(g', ℓ')` and `(g, ℓ)`. -/
private theorem norm_frozenSolution_sub_frozenSolution_le
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAm : ∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega))
    (hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x))
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ ball z R)
    (g g' : W1p volume Omega 2) (ℓ ℓ' : StrongDual ℝ (W1p0 volume Omega 2))
    {v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hv : AEStronglyMeasurable v (volume.restrict Omega)) :
    ‖frozenSolution A g' ℓ' v - frozenSolution A g ℓ v‖ ≤
      ‖g' - g‖ + (‖ℓ' - ℓ‖ + Lam * ‖g' - g‖) / (lam / (2 * ((2 * R) ^ 2 + 1))) := by
  have hΩ := isBounded_ball.subset hball
  have hspec := frozenSolution_spec hA hAm hAc hΩ g ℓ hv
  have hspec' := frozenSolution_spec hA hAm hAc hΩ g' ℓ' hv
  have hcoeff := memLp_energyIntegrand_comp hA hAm hAc hv
  -- The functional `B(g' - g, ·)` has norm at most `Λ ‖g' - g‖`.
  have hN (w : W1p0 volume Omega 2) :
      |energyFormH1 (fun x => A x (v x)) 0 0 (g' - g) (w : W1p volume Omega 2)| ≤
        Lam * ‖g' - g‖ * ‖w‖ := by
    rw [← Submodule.norm_coe w]
    refine (abs_energyFormH1_le_norm_energyFormH1L_mul hcoeff _ _).trans ?_
    gcongr
    exact norm_energyFormH1L_comp_le hA hAm hAc hv
  have hmem : frozenSolution A g' ℓ' v - frozenSolution A g ℓ v - (g' - g) ∈
      w1p0Submodule volume Omega 2 := by
    rw [← sub_sub_sub_comm, ← ClosedSubmodule.mem_toSubmodule_iff]
    exact sub_mem ((ClosedSubmodule.mem_toSubmodule_iff _ _).2 hspec'.1)
      ((ClosedSubmodule.mem_toSubmodule_iff _ _).2 hspec.1)
  simpa only [add_zero] using norm_sub_le_of_sub_sub_mem_w1p0Submodule_of_forall_energyFormH1_eq
    (b := 0) (c := 0) (a' := fun x => A x (v x)) (b' := 0) (c' := 0) (ℓ := ℓ') (ℓ' := ℓ)
    (u := frozenSolution A g' ℓ' v) (u' := frozenSolution A g ℓ v) (h := g' - g)
    (N := Lam * ‖g' - g‖) (D := 0) hcoeff (by have := (hA 0).pos; positivity)
    (mul_norm_sq_le_energyFormH1_comp hA hAm hAc hball hv)
    (mul_nonneg (hA 0).upper_nonneg (norm_nonneg _)) hN le_rfl
    (fun w => by rw [sub_self, abs_zero, zero_mul]) hmem hspec'.2 hspec.2

/-- **Continuity of the frozen solution in the coefficient, the data and the frozen function.**
Let `Ω ⊆ ℝⁿ⁺¹` be bounded and let `Aᵢ` and `A` be Carathéodory coefficients satisfying the
hypotheses of `TauCeti.PDE.exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq` with
common constants `λ, Λ`. Let `vᵢ` and `v` be measurable on `Ω`, and suppose that the frozen
coefficients converge almost everywhere on `Ω`, `Aᵢ(x, vᵢ(x)) → A(x, v(x))`, along a countably
generated filter. If the boundary values `gᵢ → g` in `H¹(Ω)` and the forcings `ℓᵢ → ℓ` in
`H⁻¹(Ω)`, then the frozen solutions converge in `H¹(Ω)`:
`frozenSolution Aᵢ gᵢ ℓᵢ vᵢ → frozenSolution A g ℓ v`.

For instance, the almost everywhere convergence holds when `vᵢ → v` almost everywhere and, for
almost every `x`, `Aᵢ(x, ·) → A(x, ·)` locally uniformly. -/
theorem tendsto_frozenSolution {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    {A' : α → EuclideanSpace ℝ (Fin (n + 1)) → ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAm : ∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega))
    (hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x))
    (hA' : ∀ i s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A' i x s) lam Lam)
    (hAm' : ∀ i s, AEStronglyMeasurable (fun x => A' i x s) (volume.restrict Omega))
    (hAc' : ∀ i, ∀ᵐ x ∂volume.restrict Omega, Continuous (A' i x))
    (hΩ : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    {v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {v' : α → EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hv : AEStronglyMeasurable v (volume.restrict Omega))
    (hv' : ∀ i, AEStronglyMeasurable (v' i) (volume.restrict Omega))
    (hlim : ∀ᵐ x ∂volume.restrict Omega, Tendsto (fun i => A' i x (v' i x)) l (𝓝 (A x (v x))))
    {g : W1p volume Omega 2} {g' : α → W1p volume Omega 2} (hg : Tendsto g' l (𝓝 g))
    {ℓ : StrongDual ℝ (W1p0 volume Omega 2)} {ℓ' : α → StrongDual ℝ (W1p0 volume Omega 2)}
    (hℓ : Tendsto ℓ' l (𝓝 ℓ)) :
    Tendsto (fun i => frozenSolution (A' i) (g' i) (ℓ' i) (v' i)) l
      (𝓝 (frozenSolution A g ℓ v)) := by
  obtain ⟨R, hball⟩ := hΩ.subset_ball (0 : EuclideanSpace ℝ (Fin (n + 1)))
  have hspec := frozenSolution_spec hA hAm hAc hΩ g ℓ hv
  have hspec' (i : α) := frozenSolution_spec (hA' i) (hAm' i) (hAc' i) hΩ g ℓ (hv' i)
  -- With the limit data `(g, ℓ)`, the frozen solutions converge by dominated convergence, since
  -- the frozen coefficients converge almost everywhere and differ by at most `2Λ`.
  have h₁ : Tendsto (fun i => frozenSolution (A' i) g ℓ (v' i)) l
      (𝓝 (frozenSolution A g ℓ v)) := by
    refine tendsto_of_forall_energyFormH1_eq_of_tendsto_ae (Lam := Lam + Lam)
      (a' := fun i x => A' i x (v' i x)) (memLp_energyIntegrand_comp hA hAm hAc hv)
      (fun i => memLp_energyIntegrand_comp (hA' i) (hAm' i) (hAc' i) (hv' i))
      (by have := (hA 0).pos; positivity)
      (fun i => mul_norm_sq_le_energyFormH1_comp (hA' i) (hAm' i) (hAc' i) hball (hv' i))
      (fun i => aestronglyMeasurable_comp (hAm' i) (hAc' i) (hv' i))
      (fun i => (ae_restrict_mem Omega.isOpen.measurableSet).mono fun x hx =>
        abs_dotProduct_sub_mulVec_le ((hA (v x)).upper_bound hx) ((hA' i (v' i x)).upper_bound hx))
      hlim hspec.2 (fun i => (hspec' i).2) (fun i => ?_)
    have h := Submodule.sub_mem _ ((ClosedSubmodule.mem_toSubmodule_iff _ _).2 (hspec' i).1)
      ((ClosedSubmodule.mem_toSubmodule_iff _ _).2 hspec.1)
    rwa [sub_sub_sub_cancel_right, ClosedSubmodule.mem_toSubmodule_iff] at h
  -- For each coefficient, changing the data from `(g, ℓ)` to `(gᵢ, ℓᵢ)` moves the frozen solution
  -- by `O(‖gᵢ - g‖ + ‖ℓᵢ - ℓ‖)`, uniformly in `i`.
  have h₂ : Tendsto (fun i => frozenSolution (A' i) (g' i) (ℓ' i) (v' i) -
      frozenSolution (A' i) g ℓ (v' i)) l (𝓝 0) := by
    have hg0 := tendsto_iff_norm_sub_tendsto_zero.1 hg
    -- The type is given explicitly so that the dual's norm topology is found.
    have hℓ0 := (tendsto_iff_norm_sub_tendsto_zero
      (E := StrongDual ℝ (W1p0 volume Omega 2))).1 hℓ
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun i =>
      norm_frozenSolution_sub_frozenSolution_le (hA' i) (hAm' i) (hAc' i) hball g (g' i) ℓ (ℓ' i)
        (hv' i)) ?_
    simpa using hg0.add ((hℓ0.add (hg0.const_mul Lam)).div_const _)
  simpa using h₂.add h₁

/-- The map `T : v ↦ S v`, the value of the frozen solution, is continuous on `L²(Ω)`. -/
theorem continuous_value_frozenSolution
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAm : ∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega))
    (hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x))
    (hΩ : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (g : W1p volume Omega 2) (ℓ : StrongDual ℝ (W1p0 volume Omega 2)) :
    Continuous fun v : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) =>
      W1p.value (frozenSolution A g ℓ v) := by
  rw [continuous_iff_seqContinuous]
  intro vs v hv
  -- Along a further subsequence of any subsequence, `vₖ → v` almost everywhere.
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, -, hms⟩ := (tendstoInMeasure_of_tendsto_Lp (hv.comp hns)).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  simp only [Function.comp_def, ← W1p.valueL_apply]
  refine (W1p.valueL.continuous.tendsto _).comp (tendsto_frozenSolution (A' := fun _ => A)
    (g' := fun _ => g) (ℓ' := fun _ => ℓ) hA hAm hAc (fun _ => hA) (fun _ => hAm) (fun _ => hAc)
    hΩ (Lp.aestronglyMeasurable v) (fun _ => Lp.aestronglyMeasurable _) ?_ tendsto_const_nhds
    tendsto_const_nhds)
  filter_upwards [hms, hAc] with x hx hcx
  exact (hcx.tendsto _).comp hx

/-- The map `T : v ↦ S v`, the value of the frozen solution, has relatively compact range in
`L²(Ω)`. -/
theorem isCompact_closure_range_value_frozenSolution
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAm : ∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega))
    (hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x))
    (hΩ : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (g : W1p volume Omega 2) (ℓ : StrongDual ℝ (W1p0 volume Omega 2)) :
    IsCompact (closure (range fun v : Lp ℝ 2
      (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) =>
        W1p.value (frozenSolution A g ℓ v))) := by
  have hR := hΩ.subset_ball (0 : EuclideanSpace ℝ (Fin (n + 1)))
  obtain ⟨R, hball⟩ := hR
  have hK : 0 ≤ 2 * ((2 * R) ^ 2 + 1) * (‖ℓ‖ + Lam * ‖g‖) / lam := by
    have := (hA 0).pos
    have := (hA 0).upper_nonneg
    positivity
  -- Rellich: the value map sends the ball of radius `K + 1` of `H¹₀(Ω)`, where `K` is the bound
  -- on the frozen solutions, to a relatively compact set.
  have hcpt := (isCompactOperator_iff_isCompact_closure_image_ball
    (W1p0.valueL (mu := volume) (Omega := Omega) (p := 2)).toLinearMap
      (r := 2 * ((2 * R) ^ 2 + 1) * (‖ℓ‖ + Lam * ‖g‖) / lam + 1) (by linarith)).1
    (W1p0.isCompactOperator_valueL ENNReal.ofNat_ne_top hΩ)
  have hS := hcpt.image (continuous_const_add (W1p.value g))
  refine hS.of_isClosed_subset isClosed_closure (closure_minimal ?_ hS.isClosed)
  rintro _ ⟨v, rfl⟩
  have hspec := frozenSolution_spec hA hAm hAc hΩ g ℓ (Lp.aestronglyMeasurable v)
  let w : W1p0 volume Omega 2 :=
    ⟨frozenSolution A g ℓ v - g, (ClosedSubmodule.mem_toSubmodule_iff _ _).2 hspec.1⟩
  have hw : ‖w‖ < 2 * ((2 * R) ^ 2 + 1) * (‖ℓ‖ + Lam * ‖g‖) / lam + 1 := by
    rw [← Submodule.norm_coe w]
    exact (norm_frozenSolution_sub_le hA hAm hAc hball g ℓ (Lp.aestronglyMeasurable v)).trans_lt
      (lt_add_one _)
  refine ⟨W1p0.valueL w, subset_closure ⟨w, mem_ball_zero_iff.2 hw, rfl⟩, ?_⟩
  rw [W1p0.valueL_apply, Submodule.coe_mk, W1p.value_sub]
  exact add_sub_cancel _ _

/-- **Existence for the quasilinear Dirichlet problem.** Let `Ω ⊆ ℝⁿ⁺¹` be a bounded open set and
let `A : ℝⁿ⁺¹ × ℝ → Mat(n + 1, ℝ)` be a Carathéodory coefficient on `Ω`: `x ↦ A x s` is almost
everywhere strongly measurable on `Ω` for every `s`, and `A x` is continuous for almost every
`x ∈ Ω`. Suppose every `A(·, s)` is uniformly elliptic and bounded on `Ω` with the constants
`λ, Λ`. Then for every `g ∈ H¹(Ω)` and every `ℓ ∈ H⁻¹(Ω)` there is `u ∈ H¹(Ω)` with
`u - g ∈ H¹₀(Ω)` solving `-div (A(x, u) ∇u) = ℓ` weakly:

`∫_Ω ⟨A(x, u) ∇u, ∇φ⟩ = ℓ φ` for every `φ ∈ H¹₀(Ω)`.

No regularity of `∂Ω` is assumed, and no uniqueness is claimed. Every solution obeys the bound
of `TauCeti.PDE.norm_sub_le_of_forall_energyFormH1_quasilinear_eq_of_subset_ball`. -/
theorem exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAm : ∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega))
    (hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x))
    (hΩ : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (g : W1p volume Omega 2) (ℓ : StrongDual ℝ (W1p0 volume Omega 2)) :
    ∃ u : W1p volume Omega 2, u - g ∈ w1p0Submodule volume Omega 2 ∧
      ∀ φ : W1p0 volume Omega 2,
        energyFormH1 (fun x => A x (W1p.value u x)) 0 0 u φ = ℓ φ := by
  have hK := isCompact_closure_range_value_frozenSolution hA hAm hAc hΩ g ℓ
  rw [← image_univ] at hK
  have hfix := schauderFixedPoint_closedConvex_continuousOn
    (E := Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (f := fun v => W1p.value (frozenSolution A g ℓ v)) isClosed_univ convex_univ univ_nonempty
    (continuous_value_frozenSolution hA hAm hAc hΩ g ℓ).continuousOn (mapsTo_univ _ _) hK
  obtain ⟨v, -, hv⟩ := hfix
  -- At the fixed point `v`, the value of `u = S v` is `v` itself.
  have hv' : W1p.value (frozenSolution A g ℓ v) = v := hv.eq
  have hspec := frozenSolution_spec hA hAm hAc hΩ g ℓ (Lp.aestronglyMeasurable v)
  refine ⟨frozenSolution A g ℓ v, hspec.1, fun φ => ?_⟩
  rw [hv']
  exact hspec.2 φ

/-- **The energy bound for the quasilinear Dirichlet problem.** Under the hypotheses of
`TauCeti.PDE.exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq`, with
`Ω ⊆ B(z, R)`, every `u ∈ H¹(Ω)` with `u - g ∈ H¹₀(Ω)` solving `-div (A(x, u) ∇u) = ℓ` weakly
satisfies

`‖u - g‖_{H¹} ≤ 2 ((2R)² + 1) (‖ℓ‖ + Λ ‖g‖) / λ`.

The bound depends on `A` only through `λ` and `Λ`, and on `Ω` only through the radius `R` of a
ball containing it. -/
theorem norm_sub_le_of_forall_energyFormH1_quasilinear_eq_of_subset_ball
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAm : ∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega))
    (hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x))
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ ball z R)
    {g u : W1p volume Omega 2} {ℓ : StrongDual ℝ (W1p0 volume Omega 2)}
    (hug : u - g ∈ w1p0Submodule volume Omega 2)
    (hu : ∀ φ : W1p0 volume Omega 2,
      energyFormH1 (fun x => A x (W1p.value u x)) 0 0 u φ = ℓ φ) :
    ‖u - g‖ ≤ 2 * ((2 * R) ^ 2 + 1) * (‖ℓ‖ + Lam * ‖g‖) / lam :=
  norm_sub_le_of_forall_energyFormH1_comp_eq hA hAm hAc hball (Lp.aestronglyMeasurable _) hug hu

end PDE

end TauCeti
