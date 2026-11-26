/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Variational.FormOperator
public import TauCeti.Analysis.PDE.MixedProblem
public import TauCeti.Analysis.PDE.Spectrum.Operator.Basic
import TauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent
import TauCeti.Analysis.Sobolev.LipschitzDomain.RellichKondrachov

/-!
# The mixed realization of a divergence-form operator

Let `L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` be a divergence-form operator with essentially bounded
coefficients on an open set `Ω ⊆ ℝⁿ`, and let `Γ` be a set disjoint from `Ω`, typically a part of
its boundary. Write `H¹_Γ(Ω)` for the space `TauCeti.W1pVanishingOn mu Ω 2 Γ` of Sobolev
functions vanishing on `Γ` and `a(u, v)` for the energy form of `L`. This file realizes `L` with
the Dirichlet condition on `Γ` and the natural (conormal) condition on the rest of the boundary as
an unbounded operator on `L²(Ω)`, the partial linear map `TauCeti.PDE.mixedOperator`. Its graph
consists of the pairs `(u, f)` with `u ∈ H¹_Γ(Ω)` and

`a(u, v) = ∫_Ω f v` for every `v ∈ H¹_Γ(Ω)`

(`TauCeti.PDE.mem_graph_mixedOperator_iff`): `u` is a weak solution of `L u = f` for the mixed
boundary condition. The test functions `v` are free off `Γ`, which is what imposes the conormal
condition there. For `Γ = ∂Ω` this is the Dirichlet realization
(`TauCeti.PDE.mixedOperator_frontier`), and for `Γ = ∅` on a domain where `H¹_∅(Ω) = H¹(Ω)`, as
on bounded Lipschitz domains, it is the Neumann realization.

These pairs form the graph of an operator because the value map `H¹_Γ(Ω) → L²(Ω)` is injective
and has dense range, the latter since `H¹_Γ(Ω)` contains `H¹₀(Ω)` when `Γ` misses `Ω`; no
hypothesis on the energy form is needed. Unlike the Dirichlet case, the energy form need not be
coercive on `H¹_Γ(Ω)`: for `-Δ` and `Γ = ∅` the constants have zero energy. Under a **Gårding
inequality**

`θ ‖v‖²_{H¹} ≤ a(v, v) + ω ‖v‖²_{L²}` for every `v ∈ H¹_Γ(Ω)`, with `θ > 0`,

the mixed form `a + ω ⟪·, ·⟫_{L²}` (`TauCeti.PDE.mixedForm`), the energy form on `H¹_Γ(Ω)`
(`TauCeti.PDE.energyFormH1LVanishingOn`) of the shifted operator `L + ω`, is coercive on `H¹_Γ(Ω)`
(`TauCeti.PDE.isCoercive_mixedForm`), and the realization is the operator of the form `a` along the
value map shifted by `ω` (`TauCeti.PDE.mixedOperator_eq_formOperator`); the shift does not change
it. Its operator theory follows from that construction:

* `-ω` is a resolvent point (`TauCeti.PDE.neg_mem_resolventSet_mixedOperator`), where the
  resolvent is minus the solution operator `TauCeti.PDE.mixedSolutionOperator` of the shifted
  problem (`TauCeti.PDE.resolvent_mixedOperator_neg`), and at every resolvent point `κ` the
  resolvent sends `f` to `-u` for a weak solution `u` of `L u - κ u = f`
  (`TauCeti.PDE.resolvent_mixedOperator_apply`);
* `a(u, v) = ⟪A u, v⟫` on the domain (`TauCeti.PDE.energyFormH1_eq_inner_mixedOperator`), in
  particular `⟪A u, u⟫ = a(u, u)` (`TauCeti.PDE.inner_mixedOperator_eq_energyFormH1`), so the
  realization is bounded below by `-ω`
  (`TauCeti.PDE.neg_mul_norm_sq_le_inner_mixedOperator`);
* for a symmetric energy form it is self-adjoint (`TauCeti.PDE.isSelfAdjoint_mixedOperator`);
* when `Ω` has the **Rellich property**, that the value map `H¹(Ω) → L²(Ω)` is compact, as on a
  bounded Lipschitz domain, the resolvent is compact
  (`TauCeti.PDE.hasCompactResolvent_mixedOperator`) and the spectrum consists of the mixed
  eigenvalues, the `κ` for which `a(u, v) = κ ∫_Ω u v` has a nonzero solution `u ∈ H¹_Γ(Ω)`
  (`TauCeti.PDE.mem_spectrum_mixedOperator_iff`);
* under a lower bound `C ‖v‖²_{L²} ≤ a(v, v)` on `H¹_Γ(Ω)`, every `κ < C` is a resolvent point
  (`TauCeti.PDE.mem_resolventSet_mixedOperator_of_lt`), so the spectrum lies in `[C, ∞)`
  (`TauCeti.PDE.le_of_mem_spectrum_mixedOperator`).

For `-Δ`, with energy form `∫_Ω ∇u · ∇v`, the Gårding inequality holds with `θ = ω = 1` and every
hypothesis but the Rellich property holds outright: the mixed Laplacian `-Δ_Γ` is self-adjoint and
nonnegative, every negative number is a resolvent point, and on a domain with the Rellich property
it has compact resolvent and spectrum its mixed eigenvalues, all nonnegative. Its kernel consists
of the values of the `u ∈ H¹_Γ(Ω)` with vanishing gradient
(`TauCeti.PDE.mixedOperator_laplacian_apply_eq_zero_iff`), so `0` is a spectral value as soon as
`H¹_Γ(Ω)` contains such a `u` with nonzero value. This happens for the mixed Laplacian `-Δ_∅` (the
Neumann Laplacian where `H¹_∅(Ω) = H¹(Ω)`) on every nonempty bounded open set, where the constant
`1` lies in `H¹_∅(Ω)`: `0` is the least point of its spectrum and `-Δ_∅` has no inverse
(`TauCeti.PDE.isLeast_spectrum_mixedOperator_laplacian_empty`). A
Poincaré–Friedrichs inequality `‖u‖_{L²} ≤ P ‖∇u‖_{L²}` on `H¹_Γ(Ω)` pushes the spectrum up to
`[P⁻², ∞)` (`TauCeti.PDE.inv_sq_le_of_mem_spectrum_mixedOperator_laplacian`). On a bounded
connected Lipschitz domain this inequality holds as soon as `Γ` meets the frontier in a set of
positive surface measure, and then the bottom of the spectrum is positive, `0` is a resolvent point
and the inverse of `-Δ_Γ` is compact and self-adjoint, as for the Dirichlet Laplacian.

## The first mixed eigenvalue

On a nonempty domain with the Rellich property the spectrum of `-Δ_Γ` has a least point `λ₁`, the
first mixed eigenvalue, and the **Rayleigh principle** identifies it as the greatest `C` with
`C ‖u‖²_{L²} ≤ ‖∇u‖²_{L²}` on `H¹_Γ(Ω)`. It is computed from the shift `ω = 1`, where the mixed
form `∫_Ω ∇u · ∇v + ∫_Ω u v` is the inner product of `H¹(Ω)`: `λ₁ + 1` is the reciprocal of the
norm of its solution operator.

Under a Poincaré–Friedrichs inequality `‖u‖_{L²} ≤ P ‖∇u‖_{L²}` on `H¹_Γ(Ω)`, the Rayleigh
principle identifies `λ₁^{-1/2}` as the optimal Poincaré–Friedrichs constant; this and the inverse
of `-Δ_Γ` are in `TauCeti/Analysis/PDE/Spectrum/Operator/PoincareFriedrichs.lean`. For `Γ = ∅` the
constants lie in `H¹_∅(Ω)` on every bounded `Ω`, so `λ₁ = 0` there
(`TauCeti.PDE.isLeast_spectrum_mixedOperator_laplacian_empty`) and some hypothesis on `Γ` is
needed for `λ₁ > 0`.

## Main declarations

* `TauCeti.PDE.mixedOperator`: the mixed realization, with
  `TauCeti.PDE.mem_graph_mixedOperator_iff`, `TauCeti.PDE.mem_domain_mixedOperator_iff`,
  `TauCeti.PDE.value_mem_domain_mixedOperator`, `TauCeti.PDE.energyFormH1_eq_inner_mixedOperator`,
  `TauCeti.PDE.mixedOperator_apply_eq` and
  `TauCeti.PDE.exists_mixedOperator_apply_eq_smul_iff` (its eigenvectors).
* `TauCeti.PDE.mixedForm`, `TauCeti.PDE.isCoercive_mixedForm` and
  `TauCeti.PDE.mixedOperator_eq_formOperator`: the shifted energy form on `H¹_Γ(Ω)`, coercive
  under a Gårding inequality, whose form operator is the mixed realization; unshifted, it is the
  energy form (`TauCeti.PDE.mixedForm_zero_apply`, `TauCeti.PDE.mixedForm_zero`).
* `TauCeti.PDE.mixedSolutionOperator`, `TauCeti.PDE.mixedSolutionOperator_apply_eq` and
  `TauCeti.PDE.resolvent_mixedOperator_neg`: the solution operator of the shifted mixed problem,
  which returns the weak solution, and is the resolvent at `-ω` up to sign; its spectral
  interface `TauCeti.PDE.hasEigenvalue_mixedSolutionOperator_iff` (eigenvalue `(κ + ω)⁻¹` for each
  mixed eigenvalue `κ`), `TauCeti.PDE.isCompactOperator_mixedSolutionOperator`,
  `TauCeti.PDE.isSymmetric_mixedSolutionOperator`,
  `TauCeti.PDE.inner_mixedSolutionOperator_self_nonneg` and
  `TauCeti.PDE.mixedSolutionOperator_injective`.
* `TauCeti.PDE.zero_mem_resolventSet_mixedOperator` and
  `TauCeti.PDE.resolvent_mixedOperator_zero`: for an energy form coercive on `H¹_Γ(Ω)`, the
  realization is invertible with inverse the unshifted solution operator.
* `TauCeti.PDE.mixedOperator_frontier`: at `Γ = ∂Ω` it is the Dirichlet realization
  `TauCeti.PDE.dirichletOperator`.
* `TauCeti.PDE.isSelfAdjoint_mixedOperator`, `TauCeti.PDE.hasCompactResolvent_mixedOperator`,
  `TauCeti.PDE.mem_spectrum_mixedOperator_iff` and `TauCeti.PDE.spectrum_mixedOperator`:
  self-adjointness, compact resolvent and spectrum.
* `TauCeti.PDE.resolvent_mixedOperator_apply`: the resolvent solves the shifted mixed problem.
* `TauCeti.PDE.isSelfAdjoint_mixedOperator_laplacian`,
  `TauCeti.PDE.inner_mixedOperator_laplacian_nonneg`,
  `TauCeti.PDE.mem_resolventSet_mixedOperator_laplacian_of_neg`,
  `TauCeti.PDE.hasCompactResolvent_mixedOperator_laplacian`,
  `TauCeti.PDE.mem_spectrum_mixedOperator_laplacian_iff`,
  `TauCeti.PDE.spectrum_mixedOperator_laplacian`,
  `TauCeti.PDE.mem_graph_mixedOperator_laplacian_iff`,
  `TauCeti.PDE.mem_domain_mixedOperator_laplacian_iff`,
  `TauCeti.PDE.value_mem_domain_mixedOperator_laplacian` and
  `TauCeti.PDE.isSelfAdjoint_resolvent_mixedOperator_laplacian`: the mixed Laplacian `-Δ_Γ`.
* `TauCeti.PDE.mixedOperator_laplacian_apply_eq_zero_iff`,
  `TauCeti.PDE.zero_mem_spectrum_mixedOperator_laplacian_of_gradient_eq_zero` and
  `TauCeti.PDE.isLeast_spectrum_mixedOperator_laplacian_empty`: the kernel of `-Δ_Γ`, and the
  eigenvalue `0` at the bottom of the spectrum of `-Δ_∅` on a bounded set.
* `TauCeti.PDE.exists_isLeast_spectrum_mixedOperator_laplacian` and
  `TauCeti.PDE.isGreatest_of_isLeast_spectrum_mixedOperator_laplacian`: the first mixed
  eigenvalue and its Rayleigh principle.
* `TauCeti.PDE.mem_resolventSet_mixedOperator_of_lt` and
  `TauCeti.PDE.le_of_mem_spectrum_mixedOperator`: the spectrum lies above every lower bound of
  the energy, and for `-Δ_Γ` above `P⁻²` for a Poincaré–Friedrichs constant `P`
  (`TauCeti.PDE.mem_resolventSet_mixedOperator_laplacian_of_lt`,
  `TauCeti.PDE.inv_sq_le_of_mem_spectrum_mixedOperator_laplacian`).
* `TauCeti.PDE.exists_pos_spectrum_mixedOperator_laplacian_subset_Ici_of_isLipschitzDomainWith`,
  `TauCeti.PDE.zero_mem_resolventSet_mixedOperator_laplacian_of_isLipschitzDomainWith` and
  `TauCeti.PDE.isCompactOperator_resolvent_mixedOperator_laplacian_zero_of_isLipschitzDomainWith`:
  with a Dirichlet part of positive surface measure on a bounded connected Lipschitz domain, the
  spectrum of `-Δ_Γ` is bounded away from `0` and `-Δ_Γ` has a compact self-adjoint inverse.
* `TauCeti.PDE.isCoercive_mixedForm_laplacian_of_isLipschitzDomainWith`: on a bounded connected
  Lipschitz domain with `Γ` of positive surface measure, `∫_Ω ∇u · ∇v` is coercive on `H¹_Γ(Ω)`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 9.31 (the Dirichlet case) and Proposition 9.24 (the Neumann problem).
* S. Bauer, D. Pauly and M. Schomburg, *The Maxwell compactness property in bounded weak
  Lipschitz domains with mixed boundary conditions*, Theorem 4.8 (the Poincaré–Friedrichs
  inequality for mixed boundary conditions).
* T. Kato, *Perturbation Theory for Linear Operators*, Chapter VI, §2 (the representation
  theorem for closed semibounded forms).
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Bornology Filter MeasureTheory Module Set TopologicalSpace
open scoped InnerProductSpace NNReal

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {Γ : Set (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ}

attribute [local instance] W1pVanishingOn.instNormedAddCommGroup
  W1pVanishingOn.instInnerProductSpace

/-! ### The energy form on `H¹_Γ(Ω)` -/

/-- **The mixed form**: the energy form `a` of `L` on `H¹_Γ(Ω)` shifted by `ω` times the `L²`
inner product, `a(u, v) + ω ⟪u, v⟫_{L²(Ω)}` (`TauCeti.PDE.mixedForm_apply`). Under a Gårding
inequality it is coercive (`TauCeti.PDE.isCoercive_mixedForm`), and the mixed realization is its
form operator along the value map (`TauCeti.PDE.mixedOperator_eq_formOperator`). -/
def mixedForm
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (Γ : Set (EuclideanSpace ℝ ι)) (omega : ℝ) :
    W1pVanishingOn mu Omega 2 Γ →L[ℝ] W1pVanishingOn mu Omega 2 Γ →L[ℝ] ℝ :=
  energyFormH1LVanishingOn (memLp_energyIntegrand_mass_sub_const hcoeff (-omega)) Γ

/-- The mixed form is `a(u, v) + ω ⟪u, v⟫_{L²(Ω)}`. -/
@[simp]
theorem mixedForm_apply
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (omega : ℝ) (u v : W1pVanishingOn mu Omega 2 Γ) :
    mixedForm hcoeff Γ omega u v =
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) +
        omega * ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
  refine (energyFormH1LVanishingOn_apply
    (memLp_energyIntegrand_mass_sub_const hcoeff (-omega)) u v).trans ?_
  rw [energyFormH1_mass_sub_const hcoeff]
  ring

/-- The unshifted mixed form is the energy form `a(u, v)`. -/
theorem mixedForm_zero_apply
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (u v : W1pVanishingOn mu Omega 2 Γ) :
    mixedForm hcoeff Γ 0 u v = energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) := by
  rw [mixedForm_apply, zero_mul, add_zero]

/-- The unshifted mixed form is the energy form of `L` on `H¹_Γ(Ω)`. -/
theorem mixedForm_zero
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega)) :
    mixedForm hcoeff Γ 0 = energyFormH1LVanishingOn hcoeff Γ := by
  ext u v
  rw [mixedForm_zero_apply, energyFormH1LVanishingOn_apply]

/-- The mixed form at `ω` is the unshifted one plus `ω ⟪J u, J v⟫` along the value map `J`. -/
private theorem mixedForm_apply_eq_zero_add
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (omega : ℝ) (u v : W1pVanishingOn mu Omega 2 Γ) :
    mixedForm hcoeff Γ omega u v =
      mixedForm hcoeff Γ 0 u v +
        omega * ⟪W1pVanishingOn.valueL u, W1pVanishingOn.valueL v⟫_ℝ := by
  rw [mixedForm_apply, mixedForm_zero_apply, W1pVanishingOn.valueL_apply,
    W1pVanishingOn.valueL_apply]

/-- **A Gårding inequality is coercivity of the mixed form**: if
`θ ‖v‖²_{H¹} ≤ a(v, v) + ω ‖v‖²_{L²}` for every `v ∈ H¹_Γ(Ω)`, with `θ > 0`, then the mixed form
shifted by `ω` is coercive on `H¹_Γ(Ω)`. -/
theorem isCoercive_mixedForm
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    {theta omega : ℝ} (htheta : 0 < theta)
    (hgarding : ∀ v : W1pVanishingOn mu Omega 2 Γ,
      theta * ‖(v : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) +
          omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2) :
    IsCoercive (mixedForm hcoeff Γ omega) := by
  refine ⟨theta, htheta, fun v ↦ ?_⟩
  rw [mixedForm_apply, real_inner_self_eq_norm_sq, mul_assoc, ← sq]
  exact hgarding v

/-! ### The realization -/

/-- The pairs `(u, f)` of `L²(Ω) × L²(Ω)` with `u ∈ H¹_Γ(Ω)` and `a(u, v) = ⟪f, v⟫` for every
`v ∈ H¹_Γ(Ω)`. -/
private def mixedGraph
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (Γ : Set (EuclideanSpace ℝ ι)) :
    Submodule ℝ (Lp ℝ 2 (mu.restrict Omega) × Lp ℝ 2 (mu.restrict Omega)) where
  carrier := {x | ∃ u : W1pVanishingOn mu Omega 2 Γ,
    W1pVanishingOn.valueL u = x.1 ∧
      ∀ v, mixedForm hcoeff Γ 0 u v = ⟪x.2, W1pVanishingOn.valueL v⟫_ℝ}
  add_mem' := by
    rintro x y ⟨u, hu, hxu⟩ ⟨w, hw, hyw⟩
    refine ⟨u + w, by rw [map_add, hu, hw, Prod.fst_add], fun v ↦ ?_⟩
    rw [map_add, add_apply, hxu, hyw, Prod.snd_add, inner_add_left]
  zero_mem' := ⟨0, by simp, fun v ↦ by simp⟩
  smul_mem' := by
    rintro r x ⟨u, hu, hxu⟩
    refine ⟨r • u, by rw [map_smul, hu, Prod.smul_fst], fun v ↦ ?_⟩
    rw [map_smul, smul_apply, hxu, Prod.smul_snd, real_inner_smul_left,
      smul_eq_mul]

/-- Membership in `mixedGraph` unfolds to its defining condition. -/
private theorem mem_mixedGraph_iff
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    {x : Lp ℝ 2 (mu.restrict Omega) × Lp ℝ 2 (mu.restrict Omega)} :
    x ∈ mixedGraph hcoeff Γ ↔ ∃ u : W1pVanishingOn mu Omega 2 Γ,
      W1pVanishingOn.valueL u = x.1 ∧
        ∀ v, mixedForm hcoeff Γ 0 u v = ⟪x.2, W1pVanishingOn.valueL v⟫_ℝ :=
  Iff.rfl

/-- `mixedGraph` is the graph of a partial linear map: a pair `(0, f)` in it has `f = 0`. -/
private theorem mixedGraph_snd_eq_zero
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hΓ : Disjoint Γ Omega) :
    ∀ x ∈ mixedGraph hcoeff Γ, x.1 = 0 → x.2 = 0 := by
  rintro x ⟨u, hu, hxu⟩ hx
  -- The value of `u` vanishes, so `u = 0` and `f` is orthogonal to the dense range of the value
  -- map.
  have hu0 : u = 0 := W1pVanishingOn.valueL_injective (by rw [hu, hx, map_zero])
  have horth : ∀ y, ⟪x.2, y⟫_ℝ = 0 := fun y ↦
    (W1pVanishingOn.denseRange_valueL_two hΓ).induction_on y
      (isClosed_eq (continuous_const.inner continuous_id) continuous_const)
      fun v ↦ by rw [← hxu v, hu0, map_zero, zero_apply]
  exact inner_self_eq_zero.1 (horth x.2)

/-- **The mixed realization** of `L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` on `L²(Ω)`, with the
Dirichlet condition on a set `Γ` and the natural condition on the rest of the boundary. When `Γ`
is disjoint from `Ω`, its graph consists of the pairs `(u, f)` with `u ∈ H¹_Γ(Ω)` and
`a(u, v) = ∫_Ω f v` for every `v ∈ H¹_Γ(Ω)` (`TauCeti.PDE.mem_graph_mixedOperator_iff`). If `Γ`
meets `Ω` these pairs need not form a graph, and the definition has no meaning. -/
def mixedOperator
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (Γ : Set (EuclideanSpace ℝ ι)) :
    Lp ℝ 2 (mu.restrict Omega) →ₗ.[ℝ] Lp ℝ 2 (mu.restrict Omega) :=
  (mixedGraph hcoeff Γ).toLinearPMap

/-- The graph of the mixed realization, in terms of the value map and the unshifted form. -/
private theorem mem_graph_mixedOperator_iff_mixedForm
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hΓ : Disjoint Γ Omega) (x : Lp ℝ 2 (mu.restrict Omega) × Lp ℝ 2 (mu.restrict Omega)) :
    x ∈ (mixedOperator hcoeff Γ).graph ↔ ∃ u : W1pVanishingOn mu Omega 2 Γ,
      W1pVanishingOn.valueL u = x.1 ∧
        ∀ v, mixedForm hcoeff Γ 0 u v = ⟪x.2, W1pVanishingOn.valueL v⟫_ℝ := by
  rw [mixedOperator, Submodule.toLinearPMap_graph_eq _ (mixedGraph_snd_eq_zero hcoeff hΓ),
    mem_mixedGraph_iff]

/-- **The graph of the mixed realization** consists of the pairs `(u, f)` for which `u ∈ H¹_Γ(Ω)`
is a weak solution of `L u = f`: `a(u, v) = ⟪f, v⟫_{L²(Ω)}` for every `v ∈ H¹_Γ(Ω)`. -/
theorem mem_graph_mixedOperator_iff
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hΓ : Disjoint Γ Omega)
    {x : Lp ℝ 2 (mu.restrict Omega) × Lp ℝ 2 (mu.restrict Omega)} :
    x ∈ (mixedOperator hcoeff Γ).graph ↔
      ∃ u : W1pVanishingOn mu Omega 2 Γ,
        W1p.value (u : W1p mu Omega 2) = x.1 ∧
          ∀ v : W1pVanishingOn mu Omega 2 Γ,
            energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
              ⟪x.2, W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
  rw [mem_graph_mixedOperator_iff_mixedForm hcoeff hΓ]
  simp only [W1pVanishingOn.valueL_apply, mixedForm_zero_apply]

/-- **The domain of the mixed realization**: the values of the `u ∈ H¹_Γ(Ω)` for which `L u` lies
in `L²(Ω)`, that is, which weakly solve `L u = g` for some `g ∈ L²(Ω)`. -/
theorem mem_domain_mixedOperator_iff
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hΓ : Disjoint Γ Omega) {f : Lp ℝ 2 (mu.restrict Omega)} :
    f ∈ (mixedOperator hcoeff Γ).domain ↔
      ∃ u : W1pVanishingOn mu Omega 2 Γ,
        W1p.value (u : W1p mu Omega 2) = f ∧ ∃ g : Lp ℝ 2 (mu.restrict Omega),
          ∀ v : W1pVanishingOn mu Omega 2 Γ,
            energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
              ⟪g, W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
  simp only [LinearPMap.mem_domain_iff, mem_graph_mixedOperator_iff hcoeff hΓ]
  exact ⟨fun ⟨g, u, hu, hg⟩ ↦ ⟨u, hu, g, hg⟩, fun ⟨u, hu, g, hg⟩ ↦ ⟨g, u, hu, hg⟩⟩

/-- The value of a weak solution `u ∈ H¹_Γ(Ω)` of `L u = g`, `a(u, v) = ⟪g, v⟫_{L²(Ω)}` for every
`v ∈ H¹_Γ(Ω)`, lies in the domain of the mixed realization. -/
theorem value_mem_domain_mixedOperator
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hΓ : Disjoint Γ Omega) {g : Lp ℝ 2 (mu.restrict Omega)}
    {u : W1pVanishingOn mu Omega 2 Γ}
    (hu : ∀ v : W1pVanishingOn mu Omega 2 Γ,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        ⟪g, W1p.value (v : W1p mu Omega 2)⟫_ℝ) :
    W1p.value (u : W1p mu Omega 2) ∈ (mixedOperator hcoeff Γ).domain :=
  (mem_domain_mixedOperator_iff hcoeff hΓ).2 ⟨u, rfl, g, hu⟩

/-- **The mixed realization is `L`**: if `u ∈ H¹_Γ(Ω)` represents `f` in the domain, then `u` is a
weak solution of `L u = A f`: `a(u, v) = ⟪A f, v⟫_{L²(Ω)}` for every `v ∈ H¹_Γ(Ω)`. -/
theorem energyFormH1_eq_inner_mixedOperator
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hΓ : Disjoint Γ Omega) (f : (mixedOperator hcoeff Γ).domain)
    {u : W1pVanishingOn mu Omega 2 Γ}
    (hu : W1p.value (u : W1p mu Omega 2) = f)
    (v : W1pVanishingOn mu Omega 2 Γ) :
    energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
      ⟪mixedOperator hcoeff Γ f, W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
  obtain ⟨w, hw, hwf⟩ := (mem_graph_mixedOperator_iff hcoeff hΓ).1
    ((mixedOperator hcoeff Γ).mem_graph f)
  obtain rfl : w = u := W1pVanishingOn.valueL_injective (by
    simpa only [W1pVanishingOn.valueL_apply] using hw.trans hu.symm)
  exact hwf v

/-- The mixed realization sends `f` to `g` when some `u ∈ H¹_Γ(Ω)` representing `f` in the domain
weakly solves `L u = g`. -/
theorem mixedOperator_apply_eq
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hΓ : Disjoint Γ Omega) {f : (mixedOperator hcoeff Γ).domain}
    {g : Lp ℝ 2 (mu.restrict Omega)} {u : W1pVanishingOn mu Omega 2 Γ}
    (hu : W1p.value (u : W1p mu Omega 2) = f)
    (hg : ∀ v : W1pVanishingOn mu Omega 2 Γ,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        ⟪g, W1p.value (v : W1p mu Omega 2)⟫_ℝ) :
    mixedOperator hcoeff Γ f = g :=
  ((LinearPMap.image_iff f.property).2
    ((mem_graph_mixedOperator_iff hcoeff hΓ).2 ⟨u, hu, hg⟩)).symm

/-- **The eigenvectors of the mixed realization** are the values of the mixed eigenfunctions: `f`
lies in the domain with `A f = κ f` exactly when `f` is the value of some `u ∈ H¹_Γ(Ω)` with
`a(u, v) = κ ⟪u, v⟫_{L²(Ω)}` for every `v ∈ H¹_Γ(Ω)`. -/
theorem exists_mixedOperator_apply_eq_smul_iff
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hΓ : Disjoint Γ Omega) {kappa : ℝ} {f : Lp ℝ 2 (mu.restrict Omega)} :
    (∃ hf : f ∈ (mixedOperator hcoeff Γ).domain, mixedOperator hcoeff Γ ⟨f, hf⟩ = kappa • f) ↔
      ∃ u : W1pVanishingOn mu Omega 2 Γ,
        W1p.value (u : W1p mu Omega 2) = f ∧
          ∀ v : W1pVanishingOn mu Omega 2 Γ,
            energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
              kappa * ⟪f, W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
  have hgraph : (∃ hf : f ∈ (mixedOperator hcoeff Γ).domain,
      mixedOperator hcoeff Γ ⟨f, hf⟩ = kappa • f) ↔
        (f, kappa • f) ∈ (mixedOperator hcoeff Γ).graph := by
    simp only [LinearPMap.mem_graph_iff, Subtype.exists, exists_and_left, exists_eq_left]
  simp only [hgraph, mem_graph_mixedOperator_iff hcoeff hΓ, real_inner_smul_left]

/-- **The mixed realization as a quadratic form**: on its domain, `⟪A f, f⟫_{L²(Ω)} = a(u, u)` for
the `u ∈ H¹_Γ(Ω)` whose value is `f`. -/
theorem inner_mixedOperator_eq_energyFormH1
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hΓ : Disjoint Γ Omega) (f : (mixedOperator hcoeff Γ).domain)
    {u : W1pVanishingOn mu Omega 2 Γ}
    (hu : W1p.value (u : W1p mu Omega 2) = f) :
    ⟪mixedOperator hcoeff Γ f, (f : Lp ℝ 2 (mu.restrict Omega))⟫_ℝ =
      energyFormH1 a b c (u : W1p mu Omega 2) (u : W1p mu Omega 2) := by
  rw [energyFormH1_eq_inner_mixedOperator hcoeff hΓ f hu, hu]

/-- **The resolvent of the mixed realization solves the shifted mixed problem.** At a point `κ`
of the resolvent set, the resolvent sends `f` to `-u`, where `u ∈ H¹_Γ(Ω)` is a weak solution of
`L u - κ u = f`. -/
theorem resolvent_mixedOperator_apply
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hΓ : Disjoint Γ Omega) {kappa : ℝ}
    (hkappa : kappa ∈ (mixedOperator hcoeff Γ).resolventSet)
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1pVanishingOn mu Omega 2 Γ}
    (hu : ∀ v : W1pVanishingOn mu Omega 2 Γ,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) -
          kappa * ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ =
        ⟪f, W1p.value (v : W1p mu Omega 2)⟫_ℝ) :
    (mixedOperator hcoeff Γ).resolvent kappa f = -W1p.value (u : W1p mu Omega 2) := by
  -- `L (-u) = -(f + κ u)`, so `(κ - L) (-u) = f`.
  have hval : W1p.value ((-u : W1pVanishingOn mu Omega 2 Γ) :
      W1p mu Omega 2) = -W1p.value (u : W1p mu Omega 2) := by
    rw [← W1pVanishingOn.valueL_apply, ← W1pVanishingOn.valueL_apply, map_neg]
  have hsol (v : W1pVanishingOn mu Omega 2 Γ) :
      energyFormH1 a b c ((-u : W1pVanishingOn mu Omega 2 Γ) :
        W1p mu Omega 2) (v : W1p mu Omega 2) =
        ⟪-(f + kappa • W1p.value (u : W1p mu Omega 2)), W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
    rw [NegMemClass.coe_neg, energyFormH1_neg_left, inner_neg_left, inner_add_left,
      real_inner_smul_left, ← hu v]
    ring
  have hmem : -W1p.value (u : W1p mu Omega 2) ∈ (mixedOperator hcoeff Γ).domain :=
    (mem_domain_mixedOperator_iff hcoeff hΓ).2 ⟨-u, hval, _, hsol⟩
  have happly := mixedOperator_apply_eq hcoeff hΓ (f := ⟨_, hmem⟩) hval hsol
  have h := LinearPMap.resolvent_smul_sub_apply hkappa ⟨_, hmem⟩
  rwa [happly, smul_neg, sub_neg_eq_add, neg_add_cancel_comm_assoc] at h

/-! ### The realization as a form operator

Under a Gårding inequality the mixed realization is the operator of the energy form along the
value map, shifted by `ω` (`IsCoercive.formOperator`), and its operator theory is that of the form
operator. -/

variable {theta omega : ℝ}

/-- **The mixed realization is a form operator**: when the mixed form shifted by `ω` is coercive,
the mixed realization is the operator of the energy form along the value map
`H¹_Γ(Ω) → L²(Ω)`, shifted by `ω`. -/
theorem mixedOperator_eq_formOperator
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hΓ : Disjoint Γ Omega) (hB : IsCoercive (mixedForm hcoeff Γ omega)) :
    mixedOperator hcoeff Γ = hB.formOperator W1pVanishingOn.valueL omega :=
  hB.eq_formOperator_of_mem_graph_iff (W1pVanishingOn.denseRange_valueL_two hΓ)
    (mixedForm_apply_eq_zero_add hcoeff omega) (mem_graph_mixedOperator_iff_mixedForm hcoeff hΓ)

/-- **The solution operator of the shifted mixed problem**: for a mixed form coercive after the
shift by `ω`, the operator on `L²(Ω)` sending `f` to the value of the solution `u ∈ H¹_Γ(Ω)` of
`a(u, v) + ω ⟪u, v⟫_{L²(Ω)} = ⟪f, v⟫_{L²(Ω)}` for every `v ∈ H¹_Γ(Ω)`. It is `(A + ω)⁻¹` for the
mixed realization `A` (`TauCeti.PDE.resolvent_mixedOperator_neg`). -/
def mixedSolutionOperator
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (Γ : Set (EuclideanSpace ℝ ι)) (hB : IsCoercive (mixedForm hcoeff Γ omega)) :
    Lp ℝ 2 (mu.restrict Omega) →L[ℝ] Lp ℝ 2 (mu.restrict Omega) :=
  hB.formSolutionOperator W1pVanishingOn.valueL

/-- The mixed solution operator is the solution operator of the mixed form along the value map
`H¹_Γ(Ω) → L²(Ω)`. -/
theorem mixedSolutionOperator_def
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hB : IsCoercive (mixedForm hcoeff Γ omega)) :
    mixedSolutionOperator hcoeff Γ hB = hB.formSolutionOperator W1pVanishingOn.valueL :=
  (rfl)

/-- **The mixed solution operator returns the solution of the shifted mixed problem**: if
`u ∈ H¹_Γ(Ω)` satisfies `a(u, v) + ω ⟪u, v⟫_{L²(Ω)} = ⟪f, v⟫_{L²(Ω)}` for every `v ∈ H¹_Γ(Ω)`,
then the mixed solution operator sends `f` to the value of `u`. -/
theorem mixedSolutionOperator_apply_eq
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hB : IsCoercive (mixedForm hcoeff Γ omega)) {f : Lp ℝ 2 (mu.restrict Omega)}
    {u : W1pVanishingOn mu Omega 2 Γ}
    (hu : ∀ v : W1pVanishingOn mu Omega 2 Γ,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) +
          omega * ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ =
        ⟪f, W1p.value (v : W1p mu Omega 2)⟫_ℝ) :
    mixedSolutionOperator hcoeff Γ hB f = W1p.value (u : W1p mu Omega 2) := by
  rw [mixedSolutionOperator_def, IsCoercive.formSolutionOperator_apply,
    ← hB.eq_formSolutionMap W1pVanishingOn.valueL fun v ↦ by
      rw [mixedForm_apply, W1pVanishingOn.valueL_apply, hu], W1pVanishingOn.valueL_apply]

/-- **The shifted mixed problem is solvable**: for every `f ∈ L²(Ω)` there is `u ∈ H¹_Γ(Ω)` with
`a(u, v) + ω ⟪u, v⟫_{L²(Ω)} = ⟪f, v⟫_{L²(Ω)}` for every `v ∈ H¹_Γ(Ω)`, and the mixed solution
operator sends `f` to its value. -/
theorem exists_mixedSolutionOperator_apply_eq
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hB : IsCoercive (mixedForm hcoeff Γ omega)) (f : Lp ℝ 2 (mu.restrict Omega)) :
    ∃ u : W1pVanishingOn mu Omega 2 Γ,
      (∀ v : W1pVanishingOn mu Omega 2 Γ,
        energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) +
            omega * ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ =
          ⟪f, W1p.value (v : W1p mu Omega 2)⟫_ℝ) ∧
        mixedSolutionOperator hcoeff Γ hB f = W1p.value (u : W1p mu Omega 2) := by
  have hu (v : W1pVanishingOn mu Omega 2 Γ) :
      energyFormH1 a b c (hB.formSolutionMap W1pVanishingOn.valueL f : W1p mu Omega 2)
          (v : W1p mu Omega 2) +
        omega * ⟪W1p.value (hB.formSolutionMap W1pVanishingOn.valueL f : W1p mu Omega 2),
          W1p.value (v : W1p mu Omega 2)⟫_ℝ = ⟪f, W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
    rw [← mixedForm_apply hcoeff, hB.apply_formSolutionMap, W1pVanishingOn.valueL_apply]
  exact ⟨_, hu, mixedSolutionOperator_apply_eq hcoeff hB hu⟩

/-- **The mixed eigenvalues are read off the mixed solution operator**: for `κ + ω ≠ 0`, the
mixed solution operator has eigenvalue `(κ + ω)⁻¹` exactly when `a(u, v) = κ ⟪u, v⟫_{L²(Ω)}` for
some nonzero `u ∈ H¹_Γ(Ω)` and every `v ∈ H¹_Γ(Ω)`. -/
theorem hasEigenvalue_mixedSolutionOperator_iff
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hB : IsCoercive (mixedForm hcoeff Γ omega)) {kappa : ℝ} (hkappa : kappa + omega ≠ 0) :
    Module.End.HasEigenvalue (mixedSolutionOperator hcoeff Γ hB :
        Lp ℝ 2 (mu.restrict Omega) →ₗ[ℝ] Lp ℝ 2 (mu.restrict Omega)) (kappa + omega)⁻¹ ↔
      ∃ u : W1pVanishingOn mu Omega 2 Γ, u ≠ 0 ∧
        ∀ v : W1pVanishingOn mu Omega 2 Γ,
          energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
            kappa * ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
  rw [mixedSolutionOperator_def, hB.hasEigenvalue_formSolutionOperator_iff _ hkappa]
  refine exists_congr fun u ↦ and_congr_right fun _ ↦ forall_congr' fun v ↦ ?_
  rw [mixedForm_apply, W1pVanishingOn.valueL_apply, W1pVanishingOn.valueL_apply, add_mul,
    add_left_inj]

/-- **The mixed solution operator is compact** when `Ω` has the Rellich property that the value
map `H¹(Ω) → L²(Ω)` is compact. -/
theorem isCompactOperator_mixedSolutionOperator
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hB : IsCoercive (mixedForm hcoeff Γ omega))
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2))) :
    IsCompactOperator (mixedSolutionOperator hcoeff Γ hB) :=
  hB.isCompactOperator_formSolutionOperator (W1pVanishingOn.isCompactOperator_valueL hK)

/-- **The mixed solution operator of a symmetric form is symmetric.** With no drift and an almost
everywhere symmetric principal coefficient the symmetry hypothesis is supplied by
`TauCeti.PDE.energyFormH1_comm_of_isSymm_ae`. -/
theorem isSymmetric_mixedSolutionOperator
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hB : IsCoercive (mixedForm hcoeff Γ omega))
    (hsymm : ∀ u v : W1pVanishingOn mu Omega 2 Γ,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2)) :
    LinearMap.IsSymmetric (mixedSolutionOperator hcoeff Γ hB :
      Lp ℝ 2 (mu.restrict Omega) →ₗ[ℝ] Lp ℝ 2 (mu.restrict Omega)) :=
  hB.isSymmetric_formSolutionOperator _ fun u v ↦ by
    rw [mixedForm_apply, mixedForm_apply, hsymm, real_inner_comm]

/-- **The mixed solution operator is positive semidefinite**: its quadratic form is the shifted
energy of the solution it produces. -/
theorem inner_mixedSolutionOperator_self_nonneg
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hB : IsCoercive (mixedForm hcoeff Γ omega)) (f : Lp ℝ 2 (mu.restrict Omega)) :
    0 ≤ ⟪f, mixedSolutionOperator hcoeff Γ hB f⟫_ℝ :=
  hB.inner_formSolutionOperator_self_nonneg _ f

/-- **The mixed solution operator is injective**: a forcing whose solution vanishes is zero,
because the value map `H¹_Γ(Ω) → L²(Ω)` has dense range when `Γ` misses `Ω`. -/
theorem mixedSolutionOperator_injective
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hΓ : Disjoint Γ Omega) (hB : IsCoercive (mixedForm hcoeff Γ omega)) :
    Function.Injective (mixedSolutionOperator hcoeff Γ hB) :=
  hB.formSolutionOperator_injective (W1pVanishingOn.denseRange_valueL_two hΓ)

/-- **`(A + ω)⁻¹ = S`.** The resolvent of the mixed realization at `-ω` is minus the mixed
solution operator. -/
theorem resolvent_mixedOperator_neg
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hΓ : Disjoint Γ Omega) (hB : IsCoercive (mixedForm hcoeff Γ omega)) :
    (mixedOperator hcoeff Γ).resolvent (-omega) = -mixedSolutionOperator hcoeff Γ hB := by
  rw [mixedOperator_eq_formOperator hcoeff hΓ hB]
  exact hB.resolvent_formOperator_neg (W1pVanishingOn.denseRange_valueL_two hΓ)

/-- **`-ω` is a resolvent point of the mixed realization** when the energy form satisfies the
Gårding inequality `θ ‖v‖²_{H¹} ≤ a(v, v) + ω ‖v‖²_{L²}` on `H¹_Γ(Ω)`, `θ > 0`. -/
theorem neg_mem_resolventSet_mixedOperator
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hΓ : Disjoint Γ Omega) (htheta : 0 < theta)
    (hgarding : ∀ v : W1pVanishingOn mu Omega 2 Γ,
      theta * ‖(v : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) +
          omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2) :
    -omega ∈ (mixedOperator hcoeff Γ).resolventSet := by
  have hB := isCoercive_mixedForm hcoeff htheta hgarding
  rw [mixedOperator_eq_formOperator hcoeff hΓ hB]
  exact hB.neg_mem_resolventSet_formOperator (W1pVanishingOn.denseRange_valueL_two hΓ)

/-- **`0` is a resolvent point of the mixed realization** when the energy form is coercive on
`H¹_Γ(Ω)` and `Γ` misses `Ω`. -/
theorem zero_mem_resolventSet_mixedOperator
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hΓ : Disjoint Γ Omega) (hB : IsCoercive (mixedForm hcoeff Γ 0)) :
    (0 : ℝ) ∈ (mixedOperator hcoeff Γ).resolventSet := by
  have h : -(0 : ℝ) ∈ (hB.formOperator W1pVanishingOn.valueL 0).resolventSet :=
    hB.neg_mem_resolventSet_formOperator (W1pVanishingOn.denseRange_valueL_two hΓ)
  rwa [← mixedOperator_eq_formOperator hcoeff hΓ hB, neg_zero] at h

/-- **`A⁻¹ = S`.** When the energy form is coercive on `H¹_Γ(Ω)` and `Γ` misses `Ω`, the resolvent
of the mixed realization at `0` is minus the mixed solution operator. -/
theorem resolvent_mixedOperator_zero
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hΓ : Disjoint Γ Omega) (hB : IsCoercive (mixedForm hcoeff Γ 0)) :
    (mixedOperator hcoeff Γ).resolvent 0 = -mixedSolutionOperator hcoeff Γ hB := by
  simpa only [neg_zero] using resolvent_mixedOperator_neg hcoeff hΓ hB

/-- **The mixed realization is bounded below by `-ω`** under the inequality
`θ ‖v‖²_{H¹} ≤ a(v, v) + ω ‖v‖²_{L²}` on `H¹_Γ(Ω)` with `θ ≥ 0`: `⟪A f, f⟫ ≥ -ω ‖f‖²` on its
domain. -/
theorem neg_mul_norm_sq_le_inner_mixedOperator
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hΓ : Disjoint Γ Omega) (htheta : 0 ≤ theta)
    (hgarding : ∀ v : W1pVanishingOn mu Omega 2 Γ,
      theta * ‖(v : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) +
          omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2)
    (f : (mixedOperator hcoeff Γ).domain) :
    -omega * ‖(f : Lp ℝ 2 (mu.restrict Omega))‖ ^ 2 ≤
      ⟪mixedOperator hcoeff Γ f, (f : Lp ℝ 2 (mu.restrict Omega))⟫_ℝ := by
  obtain ⟨u, hu, -⟩ := (mem_domain_mixedOperator_iff hcoeff hΓ).1 f.property
  rw [inner_mixedOperator_eq_energyFormH1 hcoeff hΓ f hu, ← hu]
  nlinarith [hgarding u, sq_nonneg ‖(u : W1p mu Omega 2)‖]

/-- **The mixed realization of a symmetric form is self-adjoint**, under the Gårding inequality
`θ ‖v‖²_{H¹} ≤ a(v, v) + ω ‖v‖²_{L²}` on `H¹_Γ(Ω)`. With no drift and an almost everywhere
symmetric principal coefficient the symmetry hypothesis is supplied by
`TauCeti.PDE.energyFormH1_comm_of_isSymm_ae`. -/
theorem isSelfAdjoint_mixedOperator
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hΓ : Disjoint Γ Omega) (htheta : 0 < theta)
    (hgarding : ∀ v : W1pVanishingOn mu Omega 2 Γ,
      theta * ‖(v : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) +
          omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2)
    (hsymm : ∀ u v : W1pVanishingOn mu Omega 2 Γ,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2)) :
    IsSelfAdjoint (mixedOperator hcoeff Γ) := by
  have hB := isCoercive_mixedForm hcoeff htheta hgarding
  rw [mixedOperator_eq_formOperator hcoeff hΓ hB]
  exact hB.isSelfAdjoint_formOperator (W1pVanishingOn.denseRange_valueL_two hΓ)
    (mixedForm_apply_eq_zero_add hcoeff omega) fun u v ↦ by
      rw [mixedForm_zero_apply, mixedForm_zero_apply, hsymm]

/-- **The mixed realization has compact resolvent** under the Gårding inequality
`θ ‖v‖²_{H¹} ≤ a(v, v) + ω ‖v‖²_{L²}` on `H¹_Γ(Ω)`, when `Ω` has the Rellich property that the
value map `H¹(Ω) → L²(Ω)` is compact. -/
theorem hasCompactResolvent_mixedOperator
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hΓ : Disjoint Γ Omega) (htheta : 0 < theta)
    (hgarding : ∀ v : W1pVanishingOn mu Omega 2 Γ,
      theta * ‖(v : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) +
          omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2)
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2))) :
    (mixedOperator hcoeff Γ).HasCompactResolvent := by
  have hB := isCoercive_mixedForm hcoeff htheta hgarding
  rw [mixedOperator_eq_formOperator hcoeff hΓ hB]
  exact hB.hasCompactResolvent_formOperator (W1pVanishingOn.isCompactOperator_valueL hK)
    (W1pVanishingOn.denseRange_valueL_two hΓ)

/-- **The spectrum of the mixed realization consists of the mixed eigenvalues.** Under the
Gårding inequality `θ ‖v‖²_{H¹} ≤ a(v, v) + ω ‖v‖²_{L²}` on `H¹_Γ(Ω)`, on a domain with the Rellich
property, `κ` lies in the spectrum exactly when `a(u, v) = κ ⟪u, v⟫_{L²(Ω)}` for some nonzero
`u ∈ H¹_Γ(Ω)` and every `v ∈ H¹_Γ(Ω)`. -/
theorem mem_spectrum_mixedOperator_iff
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hΓ : Disjoint Γ Omega) (htheta : 0 < theta)
    (hgarding : ∀ v : W1pVanishingOn mu Omega 2 Γ,
      theta * ‖(v : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) +
          omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2)
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2))) {kappa : ℝ} :
    kappa ∈ (mixedOperator hcoeff Γ).spectrum ↔
      ∃ u : W1pVanishingOn mu Omega 2 Γ, u ≠ 0 ∧
        ∀ v : W1pVanishingOn mu Omega 2 Γ,
          energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
            kappa * ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
  have hB := isCoercive_mixedForm hcoeff htheta hgarding
  rw [mixedOperator_eq_formOperator hcoeff hΓ hB,
    hB.mem_spectrum_formOperator_iff (W1pVanishingOn.isCompactOperator_valueL hK)
      (W1pVanishingOn.denseRange_valueL_two hΓ) (mixedForm_apply_eq_zero_add hcoeff omega)]
  simp only [mixedForm_zero_apply, W1pVanishingOn.valueL_apply]

/-- The spectrum of the mixed realization, as a set: under the Gårding inequality
`θ ‖v‖²_{H¹} ≤ a(v, v) + ω ‖v‖²_{L²}` on `H¹_Γ(Ω)`, on a domain with the Rellich property, it
consists of the mixed eigenvalues. -/
theorem spectrum_mixedOperator
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hΓ : Disjoint Γ Omega) (htheta : 0 < theta)
    (hgarding : ∀ v : W1pVanishingOn mu Omega 2 Γ,
      theta * ‖(v : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) +
          omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2)
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2))) :
    (mixedOperator hcoeff Γ).spectrum =
      {kappa | ∃ u : W1pVanishingOn mu Omega 2 Γ, u ≠ 0 ∧
        ∀ v : W1pVanishingOn mu Omega 2 Γ,
          energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
            kappa * ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ} :=
  Set.ext fun _ ↦ mem_spectrum_mixedOperator_iff hcoeff hΓ htheta hgarding hK

/-! ### A lower bound for the spectrum

A Poincaré-type lower bound `C ‖v‖²_{L²} ≤ a(v, v)` on `H¹_Γ(Ω)`, together with a Gårding
inequality, puts every `κ < C` in the resolvent set: a convex combination of the two inequalities is
a Gårding inequality for the shift by `-κ`. No compactness is needed. -/

/-- **Every `κ` below a lower bound of the energy is a resolvent point of the mixed realization.**
If the energy form satisfies the Gårding inequality `θ ‖v‖²_{H¹} ≤ a(v, v) + ω ‖v‖²_{L²}`, `θ > 0`,
and the lower bound `C ‖v‖²_{L²} ≤ a(v, v)` on `H¹_Γ(Ω)`, then every `κ < C` lies in the resolvent
set. -/
theorem mem_resolventSet_mixedOperator_of_lt
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hΓ : Disjoint Γ Omega) (htheta : 0 < theta)
    (hgarding : ∀ v : W1pVanishingOn mu Omega 2 Γ,
      theta * ‖(v : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) +
          omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2)
    {C kappa : ℝ}
    (hC : ∀ v : W1pVanishingOn mu Omega 2 Γ,
      C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2))
    (hkappa : kappa < C) :
    kappa ∈ (mixedOperator hcoeff Γ).resolventSet := by
  -- The weight `s ∈ (0, 1)` of the Gårding inequality is small enough that
  -- `s (C + ω) ≤ C - κ`; then `s θ ‖v‖²_{H¹} ≤ a(v, v) - κ ‖v‖²_{L²}`.
  set s := (C - kappa) / (|C + omega| + (C - kappa))
  have hden : 0 < |C + omega| + (C - kappa) := by
    have := sub_pos.2 hkappa
    positivity
  have hs : 0 < s := div_pos (sub_pos.2 hkappa) hden
  have hs_eq : s * (|C + omega| + (C - kappa)) = C - kappa := div_mul_cancel₀ _ hden.ne'
  have hs1 : s ≤ 1 := (div_le_one hden).2 (le_add_of_nonneg_left (abs_nonneg _))
  have hsC : s * (C + omega) ≤ C - kappa := by
    nlinarith [le_abs_self (C + omega), sub_pos.2 hkappa]
  have h := neg_mem_resolventSet_mixedOperator hcoeff hΓ (mul_pos hs htheta)
    (omega := -kappa) fun v ↦ by
      have hg := mul_le_mul_of_nonneg_left (hgarding v) hs.le
      have hc := mul_le_mul_of_nonneg_left (hC v) (sub_nonneg.2 hs1)
      have hn := mul_nonneg (sub_nonneg.2 hsC) (sq_nonneg ‖W1p.value (v : W1p mu Omega 2)‖)
      nlinarith
  rwa [neg_neg] at h

/-- **The spectrum of the mixed realization lies above every lower bound of the energy.** Under the
Gårding inequality `θ ‖v‖²_{H¹} ≤ a(v, v) + ω ‖v‖²_{L²}`, `θ > 0`, and the lower bound
`C ‖v‖²_{L²} ≤ a(v, v)` on `H¹_Γ(Ω)`, every point of the spectrum is at least `C`. -/
theorem le_of_mem_spectrum_mixedOperator
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hΓ : Disjoint Γ Omega) (htheta : 0 < theta)
    (hgarding : ∀ v : W1pVanishingOn mu Omega 2 Γ,
      theta * ‖(v : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) +
          omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2)
    {C kappa : ℝ}
    (hC : ∀ v : W1pVanishingOn mu Omega 2 Γ,
      C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2))
    (hkappa : kappa ∈ (mixedOperator hcoeff Γ).spectrum) :
    C ≤ kappa :=
  not_lt.1 fun h ↦ (LinearPMap.mem_spectrum_iff _ _).1 hkappa
    (mem_resolventSet_mixedOperator_of_lt hcoeff hΓ htheta hgarding hC h)

/-! ### The Dirichlet case -/

/-- **At the whole frontier the mixed realization is the Dirichlet realization**, since
`H¹_{∂Ω}(Ω) = H¹₀(Ω)` (`TauCeti.w1pVanishingOnSubmodule_frontier`). -/
theorem mixedOperator_frontier
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) :
    mixedOperator hcoeff (frontier (Omega : Set (EuclideanSpace ℝ ι))) =
      dirichletOperator hcoeff hcoercive :=
  LinearPMap.eq_of_eq_graph <| Submodule.ext fun x ↦ by
    rw [mem_graph_mixedOperator_iff _ (disjoint_frontier_iff_isOpen.2 Omega.isOpen),
      mem_graph_dirichletOperator_iff, W1pVanishingOn, w1pVanishingOnSubmodule_frontier]
    simp only [isWeakSolutionDirichlet_iff_inner]

/-! ### The mixed Laplacian -/

section Laplacian

variable [DecidableEq ι]

/-- **The graph of the mixed Laplacian `-Δ_Γ`** consists of the pairs `(u, f)` for which
`u ∈ H¹_Γ(Ω)` is a weak solution of `-Δ u = f`: `∫_Ω ∇u · ∇v = ∫_Ω f v` for every
`v ∈ H¹_Γ(Ω)`. -/
theorem mem_graph_mixedOperator_laplacian_iff (hΓ : Disjoint Γ Omega)
    {x : Lp ℝ 2 (mu.restrict Omega) × Lp ℝ 2 (mu.restrict Omega)} :
    x ∈ (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
      (1 : Matrix ι ι ℝ)) Γ).graph ↔
      ∃ u : W1pVanishingOn mu Omega 2 Γ,
        W1p.value (u : W1p mu Omega 2) = x.1 ∧
          ∀ v : W1pVanishingOn mu Omega 2 Γ,
            ⟪W1p.gradient (u : W1p mu Omega 2), W1p.gradient (v : W1p mu Omega 2)⟫_ℝ =
              ⟪x.2, W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
  simp only [mem_graph_mixedOperator_iff _ hΓ, energyFormH1_one_zero_zero_eq_inner]

/-- **The domain of the mixed Laplacian `-Δ_Γ`**: the values of the `u ∈ H¹_Γ(Ω)` that weakly
solve `-Δ u = g`, `∫_Ω ∇u · ∇v = ∫_Ω g v` for every `v ∈ H¹_Γ(Ω)`, for some `g ∈ L²(Ω)`. -/
theorem mem_domain_mixedOperator_laplacian_iff (hΓ : Disjoint Γ Omega)
    {f : Lp ℝ 2 (mu.restrict Omega)} :
    f ∈ (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
      (1 : Matrix ι ι ℝ)) Γ).domain ↔
      ∃ u : W1pVanishingOn mu Omega 2 Γ,
        W1p.value (u : W1p mu Omega 2) = f ∧ ∃ g : Lp ℝ 2 (mu.restrict Omega),
          ∀ v : W1pVanishingOn mu Omega 2 Γ,
            ⟪W1p.gradient (u : W1p mu Omega 2), W1p.gradient (v : W1p mu Omega 2)⟫_ℝ =
              ⟪g, W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
  simp only [mem_domain_mixedOperator_iff _ hΓ, energyFormH1_one_zero_zero_eq_inner]

/-- The value of a weak solution `u ∈ H¹_Γ(Ω)` of `-Δ u = g`, `∫_Ω ∇u · ∇v = ∫_Ω g v` for every
`v ∈ H¹_Γ(Ω)`, lies in the domain of the mixed Laplacian `-Δ_Γ`. -/
theorem value_mem_domain_mixedOperator_laplacian (hΓ : Disjoint Γ Omega)
    {g : Lp ℝ 2 (mu.restrict Omega)} {u : W1pVanishingOn mu Omega 2 Γ}
    (hu : ∀ v : W1pVanishingOn mu Omega 2 Γ,
      ⟪W1p.gradient (u : W1p mu Omega 2), W1p.gradient (v : W1p mu Omega 2)⟫_ℝ =
        ⟪g, W1p.value (v : W1p mu Omega 2)⟫_ℝ) :
    W1p.value (u : W1p mu Omega 2) ∈
      (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
      (1 : Matrix ι ι ℝ)) Γ).domain :=
  (mem_domain_mixedOperator_laplacian_iff hΓ).2 ⟨u, rfl, g, hu⟩

/-- **The mixed Laplacian `-Δ_Γ` is self-adjoint.** -/
theorem isSelfAdjoint_mixedOperator_laplacian (hΓ : Disjoint Γ Omega) :
    IsSelfAdjoint (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
      (1 : Matrix ι ι ℝ)) Γ) :=
  isSelfAdjoint_mixedOperator _ hΓ (lt_min one_pos one_pos)
    (fun v ↦ min_mul_norm_sq_le_energyFormH1_one_zero_zero_add 1 (v : W1p mu Omega 2))
    fun u v ↦ energyFormH1_one_zero_zero_comm (u : W1p mu Omega 2) v

/-- **The mixed Laplacian `-Δ_Γ` is nonnegative**: `⟪-Δ_Γ f, f⟫_{L²(Ω)} = ∫_Ω |∇u|² ≥ 0` on its
domain. -/
theorem inner_mixedOperator_laplacian_nonneg (hΓ : Disjoint Γ Omega)
    (f : (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
      (1 : Matrix ι ι ℝ)) Γ).domain) :
    0 ≤ ⟪mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
      (1 : Matrix ι ι ℝ)) Γ f, (f : Lp ℝ 2 (mu.restrict Omega))⟫_ℝ := by
  obtain ⟨u, hu, -⟩ := (mem_domain_mixedOperator_iff _ hΓ).1 f.property
  rw [inner_mixedOperator_eq_energyFormH1 _ hΓ f hu, energyFormH1_one_zero_zero_eq_inner]
  exact real_inner_self_nonneg

/-- **Every negative number is a resolvent point of the mixed Laplacian `-Δ_Γ`.** -/
theorem mem_resolventSet_mixedOperator_laplacian_of_neg (hΓ : Disjoint Γ Omega) {kappa : ℝ}
    (hkappa : kappa < 0) :
    kappa ∈ (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
      (1 : Matrix ι ι ℝ)) Γ).resolventSet := by
  have h := neg_mem_resolventSet_mixedOperator
    (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega) (1 : Matrix ι ι ℝ)) hΓ
    (lt_min one_pos (neg_pos.2 hkappa))
    fun v ↦ min_mul_norm_sq_le_energyFormH1_one_zero_zero_add (-kappa) (v : W1p mu Omega 2)
  rwa [neg_neg] at h

/-- **The mixed Laplacian `-Δ_Γ` has compact resolvent** on a domain with the Rellich property
that the value map `H¹(Ω) → L²(Ω)` is compact. -/
theorem hasCompactResolvent_mixedOperator_laplacian (hΓ : Disjoint Γ Omega)
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2))) :
    (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
      (1 : Matrix ι ι ℝ)) Γ).HasCompactResolvent :=
  hasCompactResolvent_mixedOperator _ hΓ (lt_min one_pos one_pos)
    (fun v ↦ min_mul_norm_sq_le_energyFormH1_one_zero_zero_add 1 (v : W1p mu Omega 2)) hK

/-- **The spectrum of the mixed Laplacian `-Δ_Γ`.** On a domain with the Rellich property, `κ`
lies in the spectrum of `-Δ_Γ` exactly when `∫_Ω ∇u · ∇v = κ ∫_Ω u v` for some nonzero
`u ∈ H¹_Γ(Ω)` and every `v ∈ H¹_Γ(Ω)`; such a `κ` is nonnegative
(`TauCeti.PDE.mem_resolventSet_mixedOperator_laplacian_of_neg`). -/
theorem mem_spectrum_mixedOperator_laplacian_iff (hΓ : Disjoint Γ Omega)
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2))) {kappa : ℝ} :
    kappa ∈ (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
      (1 : Matrix ι ι ℝ)) Γ).spectrum ↔
      ∃ u : W1pVanishingOn mu Omega 2 Γ, u ≠ 0 ∧
        ∀ v : W1pVanishingOn mu Omega 2 Γ,
          ⟪W1p.gradient (u : W1p mu Omega 2), W1p.gradient (v : W1p mu Omega 2)⟫_ℝ =
            kappa * ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
  rw [mem_spectrum_mixedOperator_iff
    (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega) (1 : Matrix ι ι ℝ)) hΓ
    (lt_min one_pos one_pos)
    (fun v ↦ min_mul_norm_sq_le_energyFormH1_one_zero_zero_add 1 (v : W1p mu Omega 2)) hK]
  simp only [energyFormH1_one_zero_zero_eq_inner]

/-- The spectrum of the mixed Laplacian `-Δ_Γ`, as a set: on a domain with the Rellich property, the
`κ` for which `∫_Ω ∇u · ∇v = κ ∫_Ω u v` has a nonzero solution `u ∈ H¹_Γ(Ω)`. -/
theorem spectrum_mixedOperator_laplacian (hΓ : Disjoint Γ Omega)
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2))) :
    (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
      (1 : Matrix ι ι ℝ)) Γ).spectrum =
      {kappa | ∃ u : W1pVanishingOn mu Omega 2 Γ, u ≠ 0 ∧
        ∀ v : W1pVanishingOn mu Omega 2 Γ,
          ⟪W1p.gradient (u : W1p mu Omega 2), W1p.gradient (v : W1p mu Omega 2)⟫_ℝ =
            kappa * ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ} :=
  Set.ext fun _ ↦ mem_spectrum_mixedOperator_laplacian_iff hΓ hK

/-- **Every `κ < P⁻²` is a resolvent point of the mixed Laplacian `-Δ_Γ`** when `P` is a
Poincaré–Friedrichs constant of `H¹_Γ(Ω)`: `‖u‖_{L²} ≤ P ‖∇u‖_{L²}` for every `u ∈ H¹_Γ(Ω)`. -/
theorem mem_resolventSet_mixedOperator_laplacian_of_lt (hΓ : Disjoint Γ Omega) {P kappa : ℝ}
    (hP : ∀ u ∈ w1pVanishingOnSubmodule mu Omega 2 Γ, ‖W1p.value u‖ ≤ P * ‖W1p.gradient u‖)
    (hkappa : kappa < (P ^ 2)⁻¹) :
    kappa ∈ (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
      (1 : Matrix ι ι ℝ)) Γ).resolventSet := by
  have hC (v : W1pVanishingOn mu Omega 2 Γ) :
      (P ^ 2)⁻¹ * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 (fun _ ↦ (1 : Matrix ι ι ℝ)) 0 0 (v : W1p mu Omega 2)
          (v : W1p mu Omega 2) := by
    rw [energyFormH1_one_zero_zero_eq_inner, real_inner_self_eq_norm_sq]
    -- `‖u‖ ≤ P ‖∇u‖` gives `‖u‖² ≤ P² ‖∇u‖²`; at `P = 0` the left side is `0`.
    rcases eq_or_ne P 0 with rfl | hP0
    · simp
    · rw [inv_mul_le_iff₀ (by positivity)]
      nlinarith [mul_self_le_mul_self (norm_nonneg _) (hP _ v.property)]
  exact mem_resolventSet_mixedOperator_of_lt
    (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega) (1 : Matrix ι ι ℝ)) hΓ
    (lt_min one_pos one_pos)
    (fun v ↦ min_mul_norm_sq_le_energyFormH1_one_zero_zero_add 1 (v : W1p mu Omega 2)) hC hkappa

/-- **The spectrum of the mixed Laplacian `-Δ_Γ` lies above `P⁻²`** when `P` is a
Poincaré–Friedrichs constant of `H¹_Γ(Ω)`: `‖u‖_{L²} ≤ P ‖∇u‖_{L²}` for every `u ∈ H¹_Γ(Ω)`. -/
theorem inv_sq_le_of_mem_spectrum_mixedOperator_laplacian (hΓ : Disjoint Γ Omega) {P kappa : ℝ}
    (hP : ∀ u ∈ w1pVanishingOnSubmodule mu Omega 2 Γ, ‖W1p.value u‖ ≤ P * ‖W1p.gradient u‖)
    (hkappa : kappa ∈ (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu)
      (Omega := Omega) (1 : Matrix ι ι ℝ)) Γ).spectrum) :
    (P ^ 2)⁻¹ ≤ kappa :=
  not_lt.1 fun h ↦ (LinearPMap.mem_spectrum_iff _ _).1 hkappa
    (mem_resolventSet_mixedOperator_laplacian_of_lt hΓ hP h)

/-- **The resolvent of the mixed Laplacian `-Δ_Γ` is self-adjoint** at every point of its
resolvent set. -/
theorem isSelfAdjoint_resolvent_mixedOperator_laplacian (hΓ : Disjoint Γ Omega) {kappa : ℝ}
    (hkappa : kappa ∈ (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu)
      (Omega := Omega) (1 : Matrix ι ι ℝ)) Γ).resolventSet) :
    IsSelfAdjoint ((mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu)
      (Omega := Omega) (1 : Matrix ι ι ℝ)) Γ).resolvent kappa) :=
  IsSelfAdjoint.isSelfAdjoint_resolvent (isSelfAdjoint_mixedOperator_laplacian hΓ) hkappa
    RCLike.im_to_real

/-! ### The bottom of the spectrum of the mixed Laplacian -/

/-- A point `κ` of the spectrum of `-Δ_Γ`, on a domain with the Rellich property, has an
eigenfunction `u ∈ H¹_Γ(Ω)` with nonzero value and `‖∇u‖² = κ ‖u‖²`. -/
private theorem exists_value_ne_zero_of_mem_spectrum_mixedOperator_laplacian
    (hΓ : Disjoint Γ Omega)
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2))) {kappa : ℝ}
    (hkappa : kappa ∈ (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu)
      (Omega := Omega) (1 : Matrix ι ι ℝ)) Γ).spectrum) :
    ∃ u : W1pVanishingOn mu Omega 2 Γ, W1p.value (u : W1p mu Omega 2) ≠ 0 ∧
      ‖W1p.gradient (u : W1p mu Omega 2)‖ ^ 2 =
        kappa * ‖W1p.value (u : W1p mu Omega 2)‖ ^ 2 := by
  obtain ⟨u, hu, heq⟩ := (mem_spectrum_mixedOperator_laplacian_iff hΓ hK).1 hkappa
  refine ⟨u, fun h ↦ hu (W1pVanishingOn.valueL_injective ?_), ?_⟩
  · rw [W1pVanishingOn.valueL_apply, h, map_zero]
  · rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, heq u]

/-- Every `C` with `C ‖u‖² ≤ ‖∇u‖²` on `H¹_Γ(Ω)` lies below every point of the spectrum of
`-Δ_Γ`, on a domain with the Rellich property. -/
private theorem le_of_mem_spectrum_mixedOperator_laplacian (hΓ : Disjoint Γ Omega)
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2))) {C kappa : ℝ}
    (hC : ∀ u : W1pVanishingOn mu Omega 2 Γ,
      C * ‖W1p.value (u : W1p mu Omega 2)‖ ^ 2 ≤ ‖W1p.gradient (u : W1p mu Omega 2)‖ ^ 2)
    (hkappa : kappa ∈ (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu)
      (Omega := Omega) (1 : Matrix ι ι ℝ)) Γ).spectrum) :
    C ≤ kappa := by
  obtain ⟨u, hu, heq⟩ := exists_value_ne_zero_of_mem_spectrum_mixedOperator_laplacian hΓ hK hkappa
  have hpos : 0 < ‖W1p.value (u : W1p mu Omega 2)‖ ^ 2 := by positivity
  exact le_of_mul_le_mul_right (heq ▸ hC u) hpos

/-- On a domain with the Rellich property and a nonzero value map `H¹_Γ(Ω) → L²(Ω)`, some point
`μ` of the spectrum of `-Δ_Γ` has `μ ‖u‖² ≤ ‖∇u‖²` on all of `H¹_Γ(Ω)`. It is `‖S‖⁻¹ - 1` for
the solution operator `S` of the coercive form `∫_Ω ∇u · ∇v + ∫_Ω u v`, by the Rayleigh principle
for that form. -/
private theorem exists_mem_spectrum_mixedOperator_laplacian_forall_mul_le
    (hΓ : Disjoint Γ Omega)
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (hJ : (W1pVanishingOn.valueL (mu := mu) (Omega := Omega) (p := 2) (Γ := Γ)) ≠ 0) :
    ∃ μ ∈ (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
      (1 : Matrix ι ι ℝ)) Γ).spectrum, ∀ u : W1pVanishingOn mu Omega 2 Γ,
        μ * ‖W1p.value (u : W1p mu Omega 2)‖ ^ 2 ≤ ‖W1p.gradient (u : W1p mu Omega 2)‖ ^ 2 := by
  have hB := isCoercive_mixedForm
    (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega) (1 : Matrix ι ι ℝ))
    (Γ := Γ) (lt_min one_pos one_pos)
    fun v ↦ min_mul_norm_sq_le_energyFormH1_one_zero_zero_add 1 (v : W1p mu Omega 2)
  have hsymm (u v : W1pVanishingOn mu Omega 2 Γ) :
      mixedForm (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
        (1 : Matrix ι ι ℝ)) Γ 1 u v =
      mixedForm (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
        (1 : Matrix ι ι ℝ)) Γ 1 v u := by
    rw [mixedForm_apply, mixedForm_apply, energyFormH1_one_zero_zero_comm, real_inner_comm]
  obtain ⟨u, hu, heq⟩ := hB.exists_ne_zero_forall_apply_eq_inv_norm_smul_inner
    (W1pVanishingOn.isCompactOperator_valueL hK) hsymm hJ
  refine ⟨‖hB.formSolutionOperator W1pVanishingOn.valueL‖⁻¹ - 1,
    (mem_spectrum_mixedOperator_laplacian_iff hΓ hK).2 ⟨u, hu, fun v ↦ ?_⟩, fun v ↦ ?_⟩
  · have h := heq v
    rw [mixedForm_apply, energyFormH1_one_zero_zero_eq_inner, W1pVanishingOn.valueL_apply,
      W1pVanishingOn.valueL_apply] at h
    linarith
  · have h := hB.inv_norm_formSolutionOperator_mul_norm_apply_sq_le W1pVanishingOn.valueL hsymm v
    rw [mixedForm_apply, energyFormH1_one_zero_zero_eq_inner, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq, W1pVanishingOn.valueL_apply] at h
    linarith

/-- **The spectrum of `-Δ_Γ` has a least point** `λ₁ ≥ 0` on a nonempty domain with the Rellich
property, for every `Γ` disjoint from `Ω`. It is the first mixed eigenvalue, characterized by the
Rayleigh principle `TauCeti.PDE.isGreatest_of_isLeast_spectrum_mixedOperator_laplacian`. -/
theorem exists_isLeast_spectrum_mixedOperator_laplacian (hΓ : Disjoint Γ Omega)
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (hOmega : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty) :
    ∃ lam : ℝ, IsLeast (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu)
      (Omega := Omega) (1 : Matrix ι ι ℝ)) Γ).spectrum lam := by
  obtain ⟨μ, hμ, hle⟩ := exists_mem_spectrum_mixedOperator_laplacian_forall_mul_le hΓ hK
    (W1pVanishingOn.valueL_ne_zero hΓ hOmega)
  exact ⟨μ, hμ, fun _ ↦ le_of_mem_spectrum_mixedOperator_laplacian hΓ hK hle⟩

/-- **The Rayleigh principle for the first mixed eigenvalue.** On a domain with the Rellich
property, the least point `λ₁` of the spectrum of the mixed Laplacian `-Δ_Γ` is the greatest `C`
with

`C ‖u‖²_{L²(Ω)} ≤ ‖∇u‖²_{L²(Ω)}` for every `u ∈ H¹_Γ(Ω)`. -/
theorem isGreatest_of_isLeast_spectrum_mixedOperator_laplacian (hΓ : Disjoint Γ Omega)
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2))) {lam : ℝ}
    (hlam : IsLeast (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu)
      (Omega := Omega) (1 : Matrix ι ι ℝ)) Γ).spectrum lam) :
    IsGreatest {C : ℝ | ∀ u : W1pVanishingOn mu Omega 2 Γ,
      C * ‖W1p.value (u : W1p mu Omega 2)‖ ^ 2 ≤ ‖W1p.gradient (u : W1p mu Omega 2)‖ ^ 2} lam := by
  -- An eigenfunction of `λ₁` shows that the value map is nonzero.
  obtain ⟨u, hu, -⟩ := exists_value_ne_zero_of_mem_spectrum_mixedOperator_laplacian hΓ hK hlam.1
  obtain ⟨μ, hμ, hle⟩ := exists_mem_spectrum_mixedOperator_laplacian_forall_mul_le hΓ hK
    fun h ↦ hu (by rw [← W1pVanishingOn.valueL_apply, h, zero_apply])
  have hμlam : μ = lam :=
    (IsLeast.unique ⟨hμ, fun _ ↦ le_of_mem_spectrum_mixedOperator_laplacian hΓ hK hle⟩ hlam)
  exact ⟨hμlam ▸ hle, fun C hC ↦ le_of_mem_spectrum_mixedOperator_laplacian hΓ hK hC hlam.1⟩

/-- **The kernel of the mixed Laplacian `-Δ_Γ`**: an element `f` of its domain has `-Δ_Γ f = 0`
exactly when `f` is the value of some `u ∈ H¹_Γ(Ω)` with vanishing weak gradient. -/
theorem mixedOperator_laplacian_apply_eq_zero_iff (hΓ : Disjoint Γ Omega)
    (f : (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
      (1 : Matrix ι ι ℝ)) Γ).domain) :
    mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
        (1 : Matrix ι ι ℝ)) Γ f = 0 ↔
      ∃ u : W1pVanishingOn mu Omega 2 Γ, W1p.value (u : W1p mu Omega 2) = f ∧
        W1p.gradient (u : W1p mu Omega 2) = 0 := by
  constructor
  · -- Testing the weak equation `∫ ∇u · ∇v = 0` with `v = u` gives `‖∇u‖² = 0`.
    intro hf
    obtain ⟨u, hu, -⟩ := (mem_domain_mixedOperator_iff _ hΓ).1 f.property
    have huu := energyFormH1_eq_inner_mixedOperator _ hΓ f hu u
    rw [hf, inner_zero_left, energyFormH1_one_zero_zero_eq_inner] at huu
    exact ⟨u, hu, inner_self_eq_zero.1 huu⟩
  · rintro ⟨u, hu, hgrad⟩
    refine mixedOperator_apply_eq _ hΓ hu fun v ↦ ?_
    rw [energyFormH1_one_zero_zero_eq_inner, hgrad, inner_zero_left, inner_zero_left]

/-- **A function of `H¹_Γ(Ω)` with vanishing gradient makes `0` a spectral value of `-Δ_Γ`**: if
some `u ∈ H¹_Γ(Ω)` with nonzero value has `∇u = 0`, then its value is an eigenvector of `-Δ_Γ` for
the eigenvalue `0`, and `-Δ_Γ` is not invertible. -/
theorem zero_mem_spectrum_mixedOperator_laplacian_of_gradient_eq_zero (hΓ : Disjoint Γ Omega)
    {u : W1p mu Omega 2} (hu : u ∈ w1pVanishingOnSubmodule mu Omega 2 Γ)
    (hval : W1p.value u ≠ 0) (hgrad : W1p.gradient u = 0) :
    (0 : ℝ) ∈ (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
      (1 : Matrix ι ι ℝ)) Γ).spectrum := by
  rw [LinearPMap.mem_spectrum_iff]
  intro h0
  -- The value of `u` lies in the kernel, which a resolvent point `0` makes trivial.
  have hdom : W1p.value u ∈ (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu)
      (Omega := Omega) (1 : Matrix ι ι ℝ)) Γ).domain :=
    value_mem_domain_mixedOperator_laplacian (u := ⟨u, hu⟩) hΓ (g := 0) fun v ↦ by
      rw [hgrad, inner_zero_left, inner_zero_left]
  have hker := (mixedOperator_laplacian_apply_eq_zero_iff hΓ ⟨_, hdom⟩).2 ⟨⟨u, hu⟩, rfl, hgrad⟩
  have h := LinearPMap.eq_zero_of_apply_eq_smul h0 ⟨_, hdom⟩ (by rw [hker, zero_smul])
  exact hval (congrArg Subtype.val h)

/-- **The mixed Laplacian `-Δ_∅` is not invertible.** On a nonempty bounded open set, `0` is the
least point of the spectrum of the mixed Laplacian `-Δ_∅`, which is the Neumann Laplacian where
`H¹_∅(Ω) = H¹(Ω)`. In particular `-Δ_∅` has no inverse. -/
theorem isLeast_spectrum_mixedOperator_laplacian_empty
    (hb : IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
    (hΩ : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty) :
    IsLeast (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
      (1 : Matrix ι ι ℝ)) ∅).spectrum 0 := by
  have : IsFiniteMeasure (mu.restrict (Omega : Set (EuclideanSpace ℝ ι))) :=
    isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  refine ⟨?_, fun kappa hkappa ↦ not_lt.1 fun h ↦
    (LinearPMap.mem_spectrum_iff _ _).1 hkappa
      (mem_resolventSet_mixedOperator_laplacian_of_neg (empty_disjoint _) h)⟩
  -- The constant `1` lies in `H¹_∅(Ω)`, has nonzero value and vanishing gradient.
  exact zero_mem_spectrum_mixedOperator_laplacian_of_gradient_eq_zero (empty_disjoint _)
    (W1p.const_mem_w1pVanishingOnSubmodule_empty ENNReal.ofNat_ne_top hb 1)
    (W1p.value_const_ne_zero hΩ one_ne_zero) (W1p.gradient_const 1)

end Laplacian

/-! ### A Dirichlet part of positive surface measure

On a bounded connected Lipschitz domain, a Dirichlet part `Γ` of positive surface measure gives a
Poincaré–Friedrichs inequality on `H¹_Γ(Ω)`, so the bottom of the spectrum of `-Δ_Γ` is positive and
`-Δ_Γ` is invertible, with a compact self-adjoint inverse. As in
`TauCeti/Analysis/PDE/MixedProblem.lean`, the domain is an isometric copy of a Lipschitz domain in
the product `ℝ × E` of its boundary charts. -/

section Lipschitz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {V : Opens (WithLp 2 (ℝ × E))} {L : NNReal} [DecidableEq ι]

/-- **The mixed Laplacian is coercive on a Lipschitz domain** for a boundary part of positive
measure: let an affine isometry `e` carry the connected open set `Ω ⊆ EuclideanSpace ℝ ι` onto a
bounded Lipschitz domain `V`, and let `Γ` meet the frontier of `Ω` in a set of positive surface
measure. Then `∫_Ω ∇u · ∇v` is coercive on `H¹_Γ(Ω)`, by the Poincaré–Friedrichs inequality. -/
theorem isCoercive_mixedForm_laplacian_of_isLipschitzDomainWith
    (hV : (V : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hVb : IsBounded (V : Set (WithLp 2 (ℝ × E))))
    (e : EuclideanSpace ℝ ι ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E))
    (hVΩ : (V : Set (WithLp 2 (ℝ × E))) = e.symm ⁻¹' Omega)
    (hconn : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (hΓ : (μHE[finrank ℝ E] : Measure (EuclideanSpace ℝ ι))
      (Γ ∩ frontier (Omega : Set (EuclideanSpace ℝ ι))) ≠ 0) :
    IsCoercive (mixedForm (memLp_energyIntegrand_const_zero_zero (mu := volume) (Omega := Omega)
      (1 : Matrix ι ι ℝ)) Γ 0) := by
  rw [mixedForm_zero]
  exact IsUniformlyEllipticAE.isCoercive_energyFormH1LVanishingOn_of_isLipschitzDomainWith
    ((uniformlyEllipticOn_const_one_one _).isUniformlyEllipticAE
      Omega.isOpen.measurableSet.nullMeasurableSet)
    aestronglyMeasurable_const MemLp.zero EventuallyEq.rfl (ae_of_all _ fun _ ↦ le_rfl) _ hV hVb e
    hVΩ hconn hΓ

/-- **The spectrum of the mixed Laplacian is bounded away from `0`.** Let an affine isometry `e`
carry the connected open set `Ω ⊆ EuclideanSpace ℝ ι` onto a bounded Lipschitz domain `V`, and let
`Γ`, disjoint from `Ω`, meet the frontier of `Ω` in a set of positive surface measure. Then the
spectrum of `-Δ_Γ` lies in `[C, ∞)` for some `C > 0`. -/
theorem exists_pos_spectrum_mixedOperator_laplacian_subset_Ici_of_isLipschitzDomainWith
    (hΓ : Disjoint Γ Omega) (hV : (V : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hVb : IsBounded (V : Set (WithLp 2 (ℝ × E))))
    (e : EuclideanSpace ℝ ι ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E))
    (hVΩ : (V : Set (WithLp 2 (ℝ × E))) = e.symm ⁻¹' Omega)
    (hconn : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (hΓμ : (μHE[Module.finrank ℝ E] : Measure (EuclideanSpace ℝ ι))
      (Γ ∩ frontier (Omega : Set (EuclideanSpace ℝ ι))) ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
      (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := volume) (Omega := Omega)
        (1 : Matrix ι ι ℝ)) Γ).spectrum ⊆ Ici C := by
  obtain ⟨P, hP0, hP⟩ :=
    W1p.exists_norm_value_le_mul_norm_gradient_of_mem_w1pVanishingOnSubmodule_of_affineIsometryEquiv
      (p := 2) ENNReal.ofNat_ne_top hV hVb e hVΩ hconn hΓμ
  -- Enlarge the constant to `P + 1 > 0`, so that `(P + 1)⁻²` is positive.
  have hP' : ∀ u ∈ w1pVanishingOnSubmodule volume Omega 2 Γ,
      ‖W1p.value u‖ ≤ (P + 1) * ‖W1p.gradient u‖ := fun u hu ↦
    (hP u hu).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
      (norm_nonneg _))
  exact ⟨((P + 1) ^ 2)⁻¹, by positivity, fun _ hkappa ↦
    inv_sq_le_of_mem_spectrum_mixedOperator_laplacian hΓ hP' hkappa⟩

/-- **The mixed Laplacian is invertible**: under the hypotheses of
`TauCeti.PDE.exists_pos_spectrum_mixedOperator_laplacian_subset_Ici_of_isLipschitzDomainWith`, `0`
is a resolvent point of `-Δ_Γ`. The resolvent at `0` is minus the inverse, and sends `f` to `-u`
for the weak solution `u ∈ H¹_Γ(Ω)` of `-Δu = f` (`TauCeti.PDE.resolvent_mixedOperator_apply`). -/
theorem zero_mem_resolventSet_mixedOperator_laplacian_of_isLipschitzDomainWith
    (hΓ : Disjoint Γ Omega) (hV : (V : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hVb : IsBounded (V : Set (WithLp 2 (ℝ × E))))
    (e : EuclideanSpace ℝ ι ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E))
    (hVΩ : (V : Set (WithLp 2 (ℝ × E))) = e.symm ⁻¹' Omega)
    (hconn : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (hΓμ : (μHE[Module.finrank ℝ E] : Measure (EuclideanSpace ℝ ι))
      (Γ ∩ frontier (Omega : Set (EuclideanSpace ℝ ι))) ≠ 0) :
    (0 : ℝ) ∈ (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := volume)
      (Omega := Omega) (1 : Matrix ι ι ℝ)) Γ).resolventSet := by
  obtain ⟨C, hC, hsub⟩ :=
    exists_pos_spectrum_mixedOperator_laplacian_subset_Ici_of_isLipschitzDomainWith hΓ hV hVb e
      hVΩ hconn hΓμ
  by_contra h
  exact (hsub ((LinearPMap.mem_spectrum_iff _ _).2 h)).not_gt hC

/-- **The inverse of the mixed Laplacian is compact**: under the hypotheses of
`TauCeti.PDE.exists_pos_spectrum_mixedOperator_laplacian_subset_Ici_of_isLipschitzDomainWith`, the
resolvent of `-Δ_Γ` at `0`, which is minus its inverse, is a compact operator on `L²(Ω)`. It is also
self-adjoint (`TauCeti.PDE.isSelfAdjoint_resolvent_mixedOperator_laplacian`). -/
theorem isCompactOperator_resolvent_mixedOperator_laplacian_zero_of_isLipschitzDomainWith
    (hΓ : Disjoint Γ Omega) (hV : (V : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hVb : IsBounded (V : Set (WithLp 2 (ℝ × E))))
    (e : EuclideanSpace ℝ ι ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E))
    (hVΩ : (V : Set (WithLp 2 (ℝ × E))) = e.symm ⁻¹' Omega)
    (hconn : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (hΓμ : (μHE[Module.finrank ℝ E] : Measure (EuclideanSpace ℝ ι))
      (Γ ∩ frontier (Omega : Set (EuclideanSpace ℝ ι))) ≠ 0) :
    IsCompactOperator ((mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := volume)
      (Omega := Omega) (1 : Matrix ι ι ℝ)) Γ).resolvent 0) :=
  (hasCompactResolvent_mixedOperator_laplacian hΓ
    (W1p.isCompactOperator_valueL_of_isLipschitzDomainWith_of_affineIsometryEquiv hV hVb e
      hVΩ)).isCompactOperator_resolvent
    (zero_mem_resolventSet_mixedOperator_laplacian_of_isLipschitzDomainWith hΓ hV hVb e hVΩ hconn
      hΓμ)

end Lipschitz

end PDE

end TauCeti
