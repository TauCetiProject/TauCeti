/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import TauCeti.Analysis.PDE.DirichletProblem
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import TauCeti.Analysis.Convex.SchauderFixedPoint
import TauCeti.Analysis.PDE.DirichletProblem.ContinuousDependence
import TauCeti.Analysis.Sobolev.RellichKondrachov
import TauCeti.MeasureTheory.Function.StronglyMeasurable.Caratheodory
import TauCeti.Topology.Algebra.Module.ClosedSubmodule
import TauCeti.Topology.Instances.Matrix
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence

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
(`PDE.norm_sub_le_of_sub_mem_w1p0Submodule_of_forall_energyFormH1_quasilinear_eq_of_subset_ball`),
which depends on `A` only through `λ` and `Λ`. No uniqueness is claimed. Since a weak solution
`u` solves the linear equation with the measurable coefficient `a = A(·, u)`, `λ ≤ a ≤ Λ`, every
regularity theorem for linear equations with bounded measurable coefficients applies to it.

Without uniqueness, the solutions are described as a set, and that set behaves well under
perturbation of the data. Let `Aₖ(x, ·) → A(x, ·)` locally uniformly for almost every `x ∈ Ω`, with
common constants `λ, Λ`, and let `gₖ → g` in `H¹(Ω)` and `ℓₖ → ℓ` in `H⁻¹(Ω)`. Then every sequence
of solutions `uₖ` of the problems with data `(Aₖ, gₖ, ℓₖ)` has a subsequence converging in `H¹(Ω)`
to a solution of the limit problem
(`TauCeti.PDE.exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq_and_tendsto_subseq`).
Hence the solutions of one problem form a compact subset of `H¹(Ω)`
(`TauCeti.PDE.isCompact_setOf_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq`), and
the solution set depends upper semicontinuously on the data: every open subset of `H¹(Ω)`
containing the solutions of the limit problem contains those of the `k`-th problem for all large
`k`
(`TauCeti.PDE.eventually_setOf_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq_subset`).

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
  convergence (`TauCeti.PDE.tendsto_of_forall_energyFormH1_eq_of_tendsto_ae`).
* `T` has relatively compact range. Its values lie in the translate by the value of `g` of the
  image of the ball of radius `K + 1` of `H¹₀(Ω)` under the value map, which is relatively compact
  by the Rellich–Kondrachov theorem (`TauCeti.W1p0.isCompactOperator_valueL`); no boundary
  regularity is needed, because `S v - g` lies in `H¹₀(Ω)`.

Schauder's theorem (`TauCeti.schauderFixedPoint_closedConvex_continuousOn`), applied to `T` on
all of `L²(Ω)`, gives a fixed point `v = T v`, and `u = S v` is a weak solution, since the value of
`u` is `v`.

For the stability theorem, let `Sₖ` solve the linear problem with the coefficient `Aₖ(·, uₖ)` of
`uₖ` and the limit data `(g, ℓ)`. The linear energy estimate, uniform in the coefficient, gives
`uₖ - Sₖ → 0` in `H¹(Ω)`, and the `Sₖ - g` are bounded in `H¹₀(Ω)`. By Rellich a subsequence of the
values of the `Sₖ`, hence of the `uₖ`, converges in `L²(Ω)` to some `v`, and a further subsequence
converges almost everywhere. Along it `Aₖ(x, uₖ(x)) → A(x, v(x))` almost everywhere, so the `Sₖ`,
hence the `uₖ`, converge in `H¹(Ω)` to the solution `S∞` of the linear problem with the
coefficient `A(·, v)`, as in the continuity of `T`. The value of `S∞` is the `L²` limit `v`, so
`S∞` solves the quasilinear limit problem.

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
    (fun _ _ => by simp) hball w.2
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

/-- The energy form of a frozen coefficient has norm at most `Λ` as a bilinear form on
`H¹(Ω)`. -/
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
  have hnorm : ‖energyFormH1L hcoeff‖ ≤ Lam := norm_energyFormH1L_comp_le hA hAm hAc hv
  calc ‖u - g‖ ≤ (‖ℓ‖ + ‖energyFormH1L hcoeff‖ * ‖g‖) / (lam / (2 * ((2 * R) ^ 2 + 1))) := h
    _ ≤ (‖ℓ‖ + Lam * ‖g‖) / (lam / (2 * ((2 * R) ^ 2 + 1))) := by gcongr
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

/-- Two coefficients bounded by `Λ` differ by at most `2Λ` as bilinear forms. -/
private theorem abs_dotProduct_sub_mulVec_le
    {a a' : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam' : ℝ}
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    (ha' : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a' lam' Lam)
    {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (η ξ : EuclideanSpace ℝ (Fin (n + 1))) :
    |η ⬝ᵥ ((a x - a' x) *ᵥ ξ)| ≤ 2 * Lam * ‖η‖ * ‖ξ‖ := by
  rw [Matrix.sub_mulVec, dotProduct_sub]
  linarith [abs_sub (η ⬝ᵥ (a x *ᵥ ξ)) (η ⬝ᵥ (a' x *ᵥ ξ)), ha.upper_bound hx η ξ,
    ha'.upper_bound hx η ξ]

/-- Continuity of the frozen solutions in the coefficient and the freezing function: if
`Aₖ(x, ·) → A(x, ·)` locally uniformly and `vₖ → v` for almost every `x ∈ Ω`, then the solution
with the coefficient `Aₖ` frozen at `vₖ` tends in `H¹(Ω)` to the one with `A` frozen at `v`. -/
private theorem tendsto_frozenSolution_of_tendsto_ae
    {An : ℕ → EuclideanSpace ℝ (Fin (n + 1)) → ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hAn : ∀ k s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => An k x s) lam Lam)
    (hAnm : ∀ k s, AEStronglyMeasurable (fun x => An k x s) (volume.restrict Omega))
    (hAnc : ∀ k, ∀ᵐ x ∂volume.restrict Omega, Continuous (An k x))
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAm : ∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega))
    (hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x))
    (hAlim : ∀ᵐ x ∂volume.restrict Omega, TendstoLocallyUniformly (fun k => An k x) (A x) atTop)
    (hΩ : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (g : W1p volume Omega 2) (ℓ : StrongDual ℝ (W1p0 volume Omega 2))
    {vs : ℕ → EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hvs : ∀ k, AEStronglyMeasurable (vs k) (volume.restrict Omega))
    (hv : AEStronglyMeasurable v (volume.restrict Omega))
    (hlim : ∀ᵐ x ∂volume.restrict Omega, Tendsto (fun k => vs k x) atTop (𝓝 (v x))) :
    Tendsto (fun k => frozenSolution (An k) g ℓ (vs k)) atTop (𝓝 (frozenSolution A g ℓ v)) := by
  have hR := hΩ.subset_ball (0 : EuclideanSpace ℝ (Fin (n + 1)))
  obtain ⟨R, hball⟩ := hR
  have hlam := (hA 0).pos
  have hspec := frozenSolution_spec hA hAm hAc hΩ g ℓ hv
  have hspec' (k : ℕ) := frozenSolution_spec (hAn k) (hAnm k) (hAnc k) hΩ g ℓ (hvs k)
  -- The frozen coefficients converge almost everywhere, and dominated convergence applies.
  refine tendsto_of_forall_energyFormH1_eq_of_tendsto_ae (Lam := 2 * Lam)
    (memLp_energyIntegrand_comp hA hAm hAc hv)
    (fun k => memLp_energyIntegrand_comp (hAn k) (hAnm k) (hAnc k) (hvs k))
    (by positivity : 0 < lam / (2 * ((2 * R) ^ 2 + 1)))
    (fun k => mul_norm_sq_le_energyFormH1_comp (hAn k) (hAnm k) (hAnc k) hball (hvs k))
    (fun k => aestronglyMeasurable_comp (hAnm k) (hAnc k) (hvs k))
    (fun k => (ae_restrict_mem Omega.isOpen.measurableSet).mono fun x hx =>
      abs_dotProduct_sub_mulVec_le (UniformlyEllipticOn.apply_of_forall hA _)
        (UniformlyEllipticOn.apply_of_forall (hAn k) _) hx) ?_ hspec.2 (fun k => (hspec' k).2)
    fun k => by simpa using sub_mem (hspec' k).1 hspec.1
  filter_upwards [hlim, hAlim, hAc] with x hx hlu hcx
  exact hlu.tendsto_comp hcx.continuousAt hx

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
  exact (W1p.valueL.continuous.tendsto _).comp (tendsto_frozenSolution_of_tendsto_ae
    (fun _ => hA) (fun _ => hAm) (fun _ => hAc) hA hAm hAc
    (ae_of_all _ fun x => tendstoLocallyUniformly_const (A x)) hΩ g ℓ
    (fun _ => Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable v) hms)

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

No regularity of `∂Ω` is assumed, and no uniqueness is claimed. Every solution obeys the bound of
`PDE.norm_sub_le_of_sub_mem_w1p0Submodule_of_forall_energyFormH1_quasilinear_eq_of_subset_ball`. -/
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
theorem norm_sub_le_of_sub_mem_w1p0Submodule_of_forall_energyFormH1_quasilinear_eq_of_subset_ball
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

/-! ### Stability and compactness of the solution set -/

/-- Continuous dependence on the data for one frozen coefficient: if `u - g, u' - g' ∈ H¹₀(Ω)`
and `-div (A(x, v) ∇u) = ℓ`, `-div (A(x, v) ∇u') = ℓ'` weakly, then
`‖u - u'‖ ≤ ‖g - g'‖ + 2 ((2R)² + 1) (‖ℓ - ℓ'‖ + Λ ‖g - g'‖) / λ`, whatever `v`. -/
private theorem norm_sub_le_of_forall_energyFormH1_comp_eq_of_forall_energyFormH1_comp_eq
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAm : ∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega))
    (hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x))
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ ball z R)
    {g g' u u' : W1p volume Omega 2} {ℓ ℓ' : StrongDual ℝ (W1p0 volume Omega 2)}
    {v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hv : AEStronglyMeasurable v (volume.restrict Omega))
    (hug : u - g ∈ w1p0Submodule volume Omega 2) (hug' : u' - g' ∈ w1p0Submodule volume Omega 2)
    (hu : ∀ φ : W1p0 volume Omega 2, energyFormH1 (fun x => A x (v x)) 0 0 u φ = ℓ φ)
    (hu' : ∀ φ : W1p0 volume Omega 2, energyFormH1 (fun x => A x (v x)) 0 0 u' φ = ℓ' φ) :
    ‖u - u'‖ ≤ ‖g - g'‖ + 2 * ((2 * R) ^ 2 + 1) * (‖ℓ - ℓ'‖ + Lam * ‖g - g'‖) / lam := by
  have hlam := (hA 0).pos
  have hLam := (hA 0).upper_nonneg
  have hcoeff := memLp_energyIntegrand_comp hA hAm hAc hv
  -- The same coefficient on both sides: the coefficient defect `D` of the stability estimate
  -- is `0`.
  have hN (w : W1p0 volume Omega 2) :
      |energyFormH1 (fun x => A x (v x)) 0 0 (g - g') (w : W1p volume Omega 2)| ≤
        Lam * ‖g - g'‖ * ‖w‖ := by
    rw [← Submodule.norm_coe w]
    refine (abs_energyFormH1_le_norm_energyFormH1L_mul hcoeff _ _).trans ?_
    gcongr
    exact norm_energyFormH1L_comp_le hA hAm hAc hv
  have hD (w : W1p0 volume Omega 2) :
      |energyFormH1 (fun x => A x (v x)) 0 0 u' (w : W1p volume Omega 2) -
        energyFormH1 (fun x => A x (v x)) 0 0 u' (w : W1p volume Omega 2)| ≤ 0 * ‖w‖ := by
    simp
  calc ‖u - u'‖ ≤ ‖g - g'‖ + (‖ℓ - ℓ'‖ + Lam * ‖g - g'‖ + 0) /
        (lam / (2 * ((2 * R) ^ 2 + 1))) :=
      norm_sub_le_of_sub_sub_mem_w1p0Submodule_of_forall_energyFormH1_eq hcoeff (by positivity)
        (mul_norm_sq_le_energyFormH1_comp hA hAm hAc hball hv) (by positivity) hN le_rfl hD
        (sub_sub_sub_comm u g _ _ ▸ sub_mem hug hug') hu hu'
    _ = ‖g - g'‖ + 2 * ((2 * R) ^ 2 + 1) * (‖ℓ - ℓ'‖ + Lam * ‖g - g'‖) / lam := by
      simp only [add_zero, div_div_eq_mul_div]
      ring

/-- Solutions `uₖ` of linear problems with coefficients `Aₖ(·, uₖ)` and data `gₖ → g`,
`ℓₖ → ℓ` are asymptotically equal in `H¹(Ω)` to the solutions of the linear problems with the same
coefficients and the limit data `(g, ℓ)`. -/
private theorem tendsto_sub_frozenSolution
    {An : ℕ → EuclideanSpace ℝ (Fin (n + 1)) → ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hAn : ∀ k s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => An k x s) lam Lam)
    (hAnm : ∀ k s, AEStronglyMeasurable (fun x => An k x s) (volume.restrict Omega))
    (hAnc : ∀ k, ∀ᵐ x ∂volume.restrict Omega, Continuous (An k x))
    (hΩ : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    {gn : ℕ → W1p volume Omega 2} {g : W1p volume Omega 2} (hglim : Tendsto gn atTop (𝓝 g))
    {ℓn : ℕ → StrongDual ℝ (W1p0 volume Omega 2)} {ℓ : StrongDual ℝ (W1p0 volume Omega 2)}
    (hℓlim : Tendsto (fun k => ‖ℓn k - ℓ‖) atTop (𝓝 0)) {un : ℕ → W1p volume Omega 2}
    (hun : ∀ k, un k - gn k ∈ w1p0Submodule volume Omega 2 ∧
      ∀ φ : W1p0 volume Omega 2,
        energyFormH1 (fun x => An k x (W1p.value (un k) x)) 0 0 (un k) φ = ℓn k φ) :
    Tendsto (fun k => un k - frozenSolution (An k) g ℓ (W1p.value (un k))) atTop (𝓝 0) := by
  have hR := hΩ.subset_ball (0 : EuclideanSpace ℝ (Fin (n + 1)))
  obtain ⟨R, hball⟩ := hR
  have hS (k : ℕ) := frozenSolution_spec (hAn k) (hAnm k) (hAnc k) hΩ g ℓ
    (Lp.aestronglyMeasurable (W1p.value (un k)))
  have hg := tendsto_iff_norm_sub_tendsto_zero.1 hglim
  have hbound := hg.add
    (((hℓlim.add (hg.const_mul Lam)).const_mul (2 * ((2 * R) ^ 2 + 1))).div_const lam)
  simp only [mul_zero, add_zero, zero_div] at hbound
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) (fun k =>
    norm_sub_le_of_forall_energyFormH1_comp_eq_of_forall_energyFormH1_comp_eq (hAn k) (hAnm k)
      (hAnc k) hball (Lp.aestronglyMeasurable _) (hun k).1 (hS k).1 (hun k).2 (hS k).2) hbound

/-- Rellich's theorem for frozen solutions: for coefficients `Aₖ` with common constants `λ, Λ` and
measurable functions `vₖ`, the values of the solutions of the linear problems with `Aₖ` frozen at
`vₖ` have a subsequence converging in `L²(Ω)`. -/
private theorem exists_strictMono_tendsto_value_frozenSolution
    {An : ℕ → EuclideanSpace ℝ (Fin (n + 1)) → ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hAn : ∀ k s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => An k x s) lam Lam)
    (hAnm : ∀ k s, AEStronglyMeasurable (fun x => An k x s) (volume.restrict Omega))
    (hAnc : ∀ k, ∀ᵐ x ∂volume.restrict Omega, Continuous (An k x))
    (hΩ : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (g : W1p volume Omega 2) (ℓ : StrongDual ℝ (W1p0 volume Omega 2))
    {vs : ℕ → EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hvs : ∀ k, AEStronglyMeasurable (vs k) (volume.restrict Omega)) :
    ∃ v : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))),
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        Tendsto (fun k => W1p.value (frozenSolution (An (ψ k)) g ℓ (vs (ψ k)))) atTop (𝓝 v) := by
  have hR := hΩ.subset_ball (0 : EuclideanSpace ℝ (Fin (n + 1)))
  obtain ⟨R, hball⟩ := hR
  have hlam := (hAn 0 0).pos
  have hLam := (hAn 0 0).upper_nonneg
  -- The energy bound puts the `Sₖ - g` in one ball of `H¹₀(Ω)`, whose image in `L²(Ω)` is
  -- relatively compact by Rellich.
  let K := 2 * ((2 * R) ^ 2 + 1) * (‖ℓ‖ + Lam * ‖g‖) / lam
  have hK : 0 < K + 1 := by positivity
  let w : ℕ → W1p0 volume Omega 2 := fun k => ⟨frozenSolution (An k) g ℓ (vs k) - g,
    (ClosedSubmodule.mem_toSubmodule_iff _ _).2
      (frozenSolution_sub_mem_w1p0Submodule (hAn k) (hAnm k) (hAnc k) hΩ g ℓ (hvs k))⟩
  have hw (k : ℕ) : w k ∈ ball (0 : W1p0 volume Omega 2) (K + 1) := by
    rw [mem_ball_zero_iff, ← Submodule.norm_coe]
    exact (norm_frozenSolution_sub_le (hAn k) (hAnm k) (hAnc k) hball g ℓ (hvs k)).trans_lt
      (lt_add_one K)
  have hcpt := (isCompactOperator_iff_isCompact_closure_image_ball
    (W1p0.valueL (mu := volume) (Omega := Omega) (p := 2)).toLinearMap hK).1
    (W1p0.isCompactOperator_valueL ENNReal.ofNat_ne_top hΩ)
  have hmem (k : ℕ) : W1p0.valueL (w k) ∈ closure ((W1p0.valueL (mu := volume) (Omega := Omega)
      (p := 2)).toLinearMap '' ball 0 (K + 1)) :=
    subset_closure ⟨w k, hw k, rfl⟩
  have hseq := hcpt.isSeqCompact hmem
  obtain ⟨v₀, -, ψ, hψ, hv₀⟩ := hseq
  refine ⟨v₀ + W1p.value g, ψ, hψ, (hv₀.add_const (W1p.value g)).congr fun k => ?_⟩
  simp only [Function.comp_apply, w, W1p0.valueL_apply, W1p.value_sub, sub_add_cancel]

/-- **Stability of the quasilinear Dirichlet problem.** Let `Ω ⊆ ℝⁿ⁺¹` be a bounded open set and
let `Aₖ` be Carathéodory coefficients on `Ω` such that every `Aₖ(·, s)` is uniformly elliptic and
bounded on `Ω` with the same constants `λ, Λ`. Suppose that for almost every `x ∈ Ω` the
functions `Aₖ(x, ·)` converge locally uniformly to `A(x, ·)`, where every `A(·, s)` is uniformly
elliptic and bounded on `Ω` with the constants `λ, Λ`, and that the boundary values `gₖ → g` in
`H¹(Ω)` and the forcings `ℓₖ → ℓ` in `H⁻¹(Ω)`. Let `uₖ ∈ H¹(Ω)`, with `uₖ - gₖ ∈ H¹₀(Ω)`, solve
`-div (Aₖ(x, uₖ) ∇uₖ) = ℓₖ` weakly. Then a subsequence of the `uₖ` converges in `H¹(Ω)` to a
solution `u` of the limit problem: `u - g ∈ H¹₀(Ω)` and `-div (A(x, u) ∇u) = ℓ` weakly.

No regularity of `∂Ω` is assumed. Without uniqueness the whole sequence need not converge; the
consequences for the set of all solutions are
`TauCeti.PDE.isCompact_setOf_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq` and
`TauCeti.PDE.eventually_setOf_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq_subset`. -/
theorem exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq_and_tendsto_subseq
    {An : ℕ → EuclideanSpace ℝ (Fin (n + 1)) → ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hAn : ∀ k s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => An k x s) lam Lam)
    (hAnm : ∀ k s, AEStronglyMeasurable (fun x => An k x s) (volume.restrict Omega))
    (hAnc : ∀ k, ∀ᵐ x ∂volume.restrict Omega, Continuous (An k x))
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAlim : ∀ᵐ x ∂volume.restrict Omega, TendstoLocallyUniformly (fun k => An k x) (A x) atTop)
    (hΩ : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    {gn : ℕ → W1p volume Omega 2} {g : W1p volume Omega 2} (hglim : Tendsto gn atTop (𝓝 g))
    {ℓn : ℕ → StrongDual ℝ (W1p0 volume Omega 2)} {ℓ : StrongDual ℝ (W1p0 volume Omega 2)}
    (hℓlim : Tendsto (fun k => ‖ℓn k - ℓ‖) atTop (𝓝 0)) {un : ℕ → W1p volume Omega 2}
    (hun : ∀ k, un k - gn k ∈ w1p0Submodule volume Omega 2 ∧
      ∀ φ : W1p0 volume Omega 2,
        energyFormH1 (fun x => An k x (W1p.value (un k) x)) 0 0 (un k) φ = ℓn k φ) :
    ∃ u : W1p volume Omega 2, (u - g ∈ w1p0Submodule volume Omega 2 ∧
        ∀ φ : W1p0 volume Omega 2,
          energyFormH1 (fun x => A x (W1p.value u x)) 0 0 u φ = ℓ φ) ∧
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (fun k => un (ψ k)) atTop (𝓝 u) := by
  -- The limit coefficient is again a Carathéodory coefficient.
  have hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x) := by
    filter_upwards [hAlim, ae_all_iff.2 hAnc] with x hx hcx
    exact hx.continuous (Frequently.of_forall hcx)
  have hAm (s : ℝ) : AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega) :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => hAnm k s) <| by
      filter_upwards [hAlim, hAc] with x hx hcx
      exact hx.tendsto_comp hcx.continuousAt tendsto_const_nhds
  -- Step 1: compare `uₖ` with the solution `Sₖ` of the linear problem with the same frozen
  -- coefficient `Aₖ(·, uₖ)` and the limit data `(g, ℓ)`. By continuous dependence on the data,
  -- `uₖ - Sₖ → 0` in `H¹(Ω)`.
  let S : ℕ → W1p volume Omega 2 := fun k => frozenSolution (An k) g ℓ (W1p.value (un k))
  have huS : Tendsto (fun k => un k - S k) atTop (𝓝 0) :=
    tendsto_sub_frozenSolution hAn hAnm hAnc hΩ hglim hℓlim hun
  -- Step 2: by Rellich, along a subsequence `ψ₁` the values of the `Sₖ`, hence those of the `uₖ`,
  -- converge in `L²(Ω)`, to some `v`.
  have hsub := exists_strictMono_tendsto_value_frozenSolution hAn hAnm hAnc hΩ g ℓ
    fun k => Lp.aestronglyMeasurable (W1p.value (un k))
  obtain ⟨v, ψ₁, hψ₁, hSv⟩ := hsub
  have hv : Tendsto (fun k => W1p.value (un (ψ₁ k))) atTop (𝓝 v) := by
    have h := ((W1p.valueL.continuous.tendsto' 0 0 (map_zero _)).comp
      (huS.comp hψ₁.tendsto_atTop)).add hSv
    simp only [zero_add] at h
    refine h.congr fun k => ?_
    simp only [Function.comp_apply, S, W1p.valueL_apply, W1p.value_sub, sub_add_cancel]
  -- Step 3: along a further subsequence `ψ` the values converge almost everywhere, so the `Sₖ`
  -- converge in `H¹(Ω)` to the solution `S∞` of the linear problem with `A` frozen at `v`, and so
  -- do the `uₖ`.
  have hae := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  obtain ⟨ms, hms, hmsae⟩ := hae
  let ψ := ψ₁ ∘ ms
  have hψ : StrictMono ψ := hψ₁.comp hms
  have hspec := frozenSolution_spec hA hAm hAc hΩ g ℓ (Lp.aestronglyMeasurable v)
  have hSlim : Tendsto (fun k => S (ψ k)) atTop (𝓝 (frozenSolution A g ℓ v)) :=
    tendsto_frozenSolution_of_tendsto_ae (fun k => hAn (ψ k)) (fun k => hAnm (ψ k))
      (fun k => hAnc (ψ k)) hA hAm hAc (hAlim.mono fun _ hx => hx.comp_tendsto hψ.tendsto_atTop)
      hΩ g ℓ (fun k => Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable v) hmsae
  have hulim : Tendsto (fun k => un (ψ k)) atTop (𝓝 (frozenSolution A g ℓ v)) := by
    simpa using (huS.comp hψ.tendsto_atTop).add hSlim
  -- Step 4: the value of `S∞` is `v`, so `S∞` solves the quasilinear limit problem.
  have hvS : W1p.value (frozenSolution A g ℓ v) = v := by
    have h := (W1p.valueL.continuous.tendsto _).comp hulim
    simp only [Function.comp_def, W1p.valueL_apply] at h
    exact tendsto_nhds_unique h (hv.comp hms.tendsto_atTop)
  have hcoef : (fun x => A x (W1p.value (frozenSolution A g ℓ v) x)) = fun x => A x (v x) := by
    rw [hvS]
  refine ⟨frozenSolution A g ℓ v, ⟨hspec.1, fun φ => ?_⟩, ψ, hψ, hulim⟩
  simpa only [hcoef] using hspec.2 φ

/-- **The solution set is compact.** Under the hypotheses of the existence theorem
`TauCeti.PDE.exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq`, the weak solutions
`u ∈ H¹(Ω)` of the quasilinear Dirichlet problem `-div (A(x, u) ∇u) = ℓ`, `u - g ∈ H¹₀(Ω)`, form a
compact subset of `H¹(Ω)`. It is nonempty by that theorem. -/
theorem isCompact_setOf_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAm : ∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega))
    (hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x))
    (hΩ : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (g : W1p volume Omega 2) (ℓ : StrongDual ℝ (W1p0 volume Omega 2)) :
    IsCompact {u : W1p volume Omega 2 | u - g ∈ w1p0Submodule volume Omega 2 ∧
      ∀ φ : W1p0 volume Omega 2, energyFormH1 (fun x => A x (W1p.value u x)) 0 0 u φ = ℓ φ} := by
  refine IsSeqCompact.isCompact fun u hu => ?_
  -- The constant family of problems converges to the problem itself.
  -- `ℓ - ℓ = 0` is proved pointwise: the generic `sub_self` does not unify with the subtraction of
  -- `H⁻¹(Ω)`, whose instance path runs through the unexposed definition of `H¹₀(Ω)`.
  have hℓℓ : ℓ - ℓ = 0 := ContinuousLinearMap.ext fun _ => sub_self _
  have hℓ : Tendsto (fun _ : ℕ => ‖ℓ - ℓ‖) atTop (𝓝 0) := by
    simp only [hℓℓ, ContinuousLinearMap.opNorm_zero, tendsto_const_nhds_iff]
  have h := exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq_and_tendsto_subseq
    (fun _ => hA) (fun _ => hAm) (fun _ => hAc) hA
    (ae_of_all _ fun x => tendstoLocallyUniformly_const (A x)) hΩ tendsto_const_nhds hℓ hu
  obtain ⟨u', hu', ψ, hψ, hlim⟩ := h
  exact ⟨u', hu', ψ, hψ, hlim⟩

/-- **Upper semicontinuity of the solution set.** Under the hypotheses of
`TauCeti.PDE.exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq_and_tendsto_subseq`,
let `U` be an open subset of `H¹(Ω)` containing all weak solutions of the limit problem
`-div (A(x, u) ∇u) = ℓ`, `u - g ∈ H¹₀(Ω)`. Then for all large `k`, `U` also contains all weak
solutions of the problem `-div (Aₖ(x, u) ∇u) = ℓₖ`, `u - gₖ ∈ H¹₀(Ω)`. -/
theorem eventually_setOf_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq_subset
    {An : ℕ → EuclideanSpace ℝ (Fin (n + 1)) → ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hAn : ∀ k s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => An k x s) lam Lam)
    (hAnm : ∀ k s, AEStronglyMeasurable (fun x => An k x s) (volume.restrict Omega))
    (hAnc : ∀ k, ∀ᵐ x ∂volume.restrict Omega, Continuous (An k x))
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAlim : ∀ᵐ x ∂volume.restrict Omega, TendstoLocallyUniformly (fun k => An k x) (A x) atTop)
    (hΩ : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    {gn : ℕ → W1p volume Omega 2} {g : W1p volume Omega 2} (hglim : Tendsto gn atTop (𝓝 g))
    {ℓn : ℕ → StrongDual ℝ (W1p0 volume Omega 2)} {ℓ : StrongDual ℝ (W1p0 volume Omega 2)}
    (hℓlim : Tendsto (fun k => ‖ℓn k - ℓ‖) atTop (𝓝 0)) {U : Set (W1p volume Omega 2)}
    (hU : IsOpen U)
    (hSU : {u : W1p volume Omega 2 | u - g ∈ w1p0Submodule volume Omega 2 ∧
      ∀ φ : W1p0 volume Omega 2, energyFormH1 (fun x => A x (W1p.value u x)) 0 0 u φ = ℓ φ} ⊆ U) :
    ∀ᶠ k in atTop, {u : W1p volume Omega 2 | u - gn k ∈ w1p0Submodule volume Omega 2 ∧
      ∀ φ : W1p0 volume Omega 2,
        energyFormH1 (fun x => An k x (W1p.value u x)) 0 0 u φ = ℓn k φ} ⊆ U := by
  by_contra h
  -- Otherwise a subsequence of problems has solutions `uₖ ∉ U`.
  obtain ⟨ψ, hψ, hψU⟩ := extraction_of_frequently_atTop (not_eventually.1 h)
  choose un hun hunU using fun k => not_subset.1 (hψU k)
  have hψt := hψ.tendsto_atTop
  obtain ⟨u, hu, ψ', -, hlim⟩ :=
    exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq_and_tendsto_subseq
      (fun k => hAn (ψ k)) (fun k => hAnm (ψ k)) (fun k => hAnc (ψ k)) hA
      (hAlim.mono fun _ hx => hx.comp_tendsto hψt) hΩ (hglim.comp hψt) (hℓlim.comp hψt) hun
  -- Their limit lies in `U`, which is open, so the `uₖ` eventually do too.
  obtain ⟨k, hk⟩ := (hlim.eventually (hU.mem_nhds (hSU hu))).exists
  exact hunU (ψ' k) hk

end PDE

end TauCeti
