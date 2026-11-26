/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Variational.Sequence
public import TauCeti.Analysis.PDE.Spectrum.MinMax
public import TauCeti.Analysis.PDE.Spectrum.Operator.Mixed
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic
public import TauCeti.Analysis.Sobolev.LipschitzDomain.RellichKondrachov
public import TauCeti.Analysis.Sobolev.W1p.BoundaryPart
import TauCeti.Analysis.InnerProductSpace.Variational.Rayleigh

/-!
# Mixed and Neumann eigenvalues

Let `Ω ⊆ ℝⁿ` be open, let `Γ` be a set disjoint from `Ω`, typically a part of its boundary, and
let `H¹_Γ(Ω)` be the space `TauCeti.W1pVanishingOn mu Ω 2 Γ` of Sobolev functions vanishing on
`Γ`, the subspace `TauCeti.w1pVanishingOnSubmodule`: the closure in `H¹(Ω)` of the restrictions
of test functions supported away from `closure Γ`, so it depends on `Γ` only through
`closure Γ`. For the divergence-form operator
`L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` with energy form `a(u, v)`, a real number `κ` is a
**mixed eigenvalue** (`TauCeti.PDE.IsMixedEigenvalue`) when some nonzero `u ∈ H¹_Γ(Ω)` satisfies

`a(u, v) = κ ∫_Ω u v` for every `v ∈ H¹_Γ(Ω)`.

This is the weak form of `L u = κ u` in `Ω` with the Dirichlet condition `u = 0` on `closure Γ`,
which may be larger than `Γ`, and, formally (for solutions and boundaries regular enough for the
conormal derivative to make sense), the natural (conormal) condition on the remaining boundary
`∂Ω \ closure Γ`, where the test functions `v` are not constrained. For `Γ = ∂Ω` it is the
Dirichlet eigenvalue problem (`TauCeti.PDE.isMixedEigenvalue_frontier_iff`). For `Γ = ∅` it is
the Neumann eigenvalue problem whenever `H¹_∅(Ω) = H¹(Ω)`. This identity is currently proved
only for bounded Lipschitz domains in the model coordinates `ℝ × E` with Lebesgue measure
`volume` (`TauCeti.w1pVanishingOnSubmodule_empty_of_isLipschitzDomainWith`), not for this file's
domains in `EuclideanSpace ℝ ι` with a general Haar measure.

When the energy form is coercive on `H¹_Γ(Ω)` itself, with no shift, the **first mixed
eigenvalue** `λ₁` is the reciprocal of the norm of the solution operator `S` of the mixed problem
(`TauCeti.PDE.firstMixedEigenvalue`), as `TauCeti.PDE.firstDirichletEigenvalue` is for `Γ = ∂Ω`,
with which it agrees there (`TauCeti.PDE.firstMixedEigenvalue_frontier`). In the indexing of the
eigenvalue sequence below it is `λ₀`. For a symmetric energy form:

* `λ₁ ‖u‖²_{L²} ≤ a(u, u)` on `H¹_Γ(Ω)`, and `λ₁` is the largest constant with this property
  (`TauCeti.PDE.isGreatest_firstMixedEigenvalue`);
* `λ₁` is at most every mixed eigenvalue (`TauCeti.PDE.firstMixedEigenvalue_le`), and on a domain
  with the Rellich property, that the value map `H¹(Ω) → L²(Ω)` is compact, it is itself a mixed
  eigenvalue: it is the minimum of the Rayleigh quotient `a(u, u) / ‖u‖²_{L²}`
  (`TauCeti.PDE.isLeast_rayleighQuotient_firstMixedEigenvalue`) and the least point of the
  spectrum of the mixed realization `A`
  (`TauCeti.PDE.isLeast_spectrum_mixedOperator_firstMixedEigenvalue`);
* `0` is a resolvent point of `A`, with resolvent `-S` there
  (`TauCeti.PDE.zero_mem_resolventSet_mixedOperator`, `TauCeti.PDE.resolvent_mixedOperator_zero`),
  so `A` has the inverse `S`, which is symmetric and, under the Rellich property, compact.

For the mixed Laplacian `-Δ_Γ`, with energy form `∫_Ω ∇u · ∇v`, coercivity on `H¹_Γ(Ω)` is exactly
a **Poincaré–Friedrichs inequality** `‖u‖_{L²} ≤ P ‖∇u‖_{L²}`
(`TauCeti.PDE.UniformlyEllipticOn.isCoercive_energyFormH1LVanishingOn_of_poincare`, transported
along `TauCeti.PDE.mixedForm_zero`), and `λ₁ = 1 / P²` for the optimal
constant `P` (`TauCeti.PDE.isLeast_norm_value_le_mul_norm_gradient_inv_sqrt_firstMixedEigenvalue`).
On a bounded connected Lipschitz domain the Poincaré–Friedrichs inequality holds as soon as `Γ`
meets the boundary in a set of positive surface measure. There, then, `λ₁ > 0` is the least point
of the spectrum of `-Δ_Γ`, it is the reciprocal of the square of the optimal Poincaré–Friedrichs
constant, and `-Δ_Γ` has a compact self-adjoint inverse
(`TauCeti.PDE.exists_firstMixedEigenvalue_laplacian_of_isLipschitzDomainWith`).

Unlike the Dirichlet case, the energy form need not be coercive on `H¹_Γ(Ω)`: for `-Δ` and
`Γ = ∅` the constants have zero energy. It is coercive after a shift by the `L²` inner product,
`θ ‖u‖²_{H¹} ≤ a(u, u) + ω ‖u‖²_{L²}` (a Gårding inequality on `H¹_Γ(Ω)`, with `θ = ω = 1` for
`-Δ`). Under this inequality, symmetry of the form and the **Rellich property** of `Ω`, that the
value map `H¹(Ω) → L²(Ω)` is compact, as it is on a bounded Lipschitz domain (for domains in
`ℝ × E` this is `TauCeti.W1p.isCompactOperator_valueL_of_isLipschitzDomainWith`), the mixed
eigenvalues form a sequence

`λ₀ ≤ λ₁ ≤ λ₂ ≤ ⋯ → ∞`,

repeated according to multiplicity, with an orthonormal basis of `L²(Ω)` of eigenfunctions in
`H¹_Γ(Ω)` (`TauCeti.PDE.exists_hilbertBasis_nat_isMixedEigenvalue_monotone`). The eigenvalues of
the shifted form `TauCeti.PDE.mixedForm` are `λₖ + ω`; they are positive, and the abstract
eigenbasis of a coercive form along a compact embedding of dense range applies to it. The value
map `H¹_Γ(Ω) → L²(Ω)` has dense range because `H¹_Γ(Ω)` contains `H¹₀(Ω)` when `Γ` misses `Ω`.

The **min–max principle** defines the `k`-th mixed eigenvalue `λₖ` without eigenfunctions
(`TauCeti.PDE.mixedEigenvalue`): the infimum of the `C` for which some subspace of `H¹_Γ(Ω)`, whose
values span a subspace of `L²(Ω)` of dimension at least `k + 1`, satisfies `a(v, v) ≤ C ‖v‖²_{L²}`
on it. For a symmetric form bounded below, `a(v, v) + ω ‖v‖²_{L²} ≥ 0`, with an eigenbasis it is
the `k`-th term of every nondecreasing listing of the eigenvalues
(`TauCeti.PDE.mixedEigenvalue_eq_of_hilbertBasis`), and the infimum is attained
(`TauCeti.PDE.isLeast_mixedEigenvalue`); a Gårding inequality makes the form bounded below. At
`Γ = ∂Ω` it is the Dirichlet eigenvalue `TauCeti.PDE.dirichletEigenvalue`
(`TauCeti.PDE.mixedEigenvalue_frontier`), and since `H¹_Γ(Ω)` shrinks as `Γ` grows, the
eigenvalues grow with `Γ`: `λₖ(Γ) ≤ λₖ(Γ')` for `Γ ⊆ Γ'`
(`TauCeti.PDE.mixedEigenvalue_le_of_subset`).

For `-Δ`, whose energy form is `∫_Ω ∇u · ∇v`, all hypotheses except the Rellich property hold
outright, and the Rellich property holds on every bounded Lipschitz domain of `ℝⁿ`
(`TauCeti.W1p.isCompactOperator_valueL_of_isLipschitzDomain`). So on a nonempty bounded
Lipschitz domain the mixed eigenvalues of `-Δ` are nonnegative and the eigenbasis and min–max
hold outright (`TauCeti.PDE.mixedEigenvalue_laplacian_spectrum`).

## Main declarations

* `TauCeti.PDE.IsMixedEigenvalue`: the mixed eigenvalue problem, and
  `TauCeti.PDE.isMixedEigenvalue_frontier_iff`: at `Γ = ∂Ω` it is the Dirichlet one.
* `TauCeti.PDE.firstMixedEigenvalue`: the first mixed eigenvalue `‖S‖⁻¹`.
* `TauCeti.PDE.firstMixedEigenvalue_pos`, `TauCeti.PDE.firstMixedEigenvalue_le`,
  `TauCeti.PDE.exists_ne_zero_forall_energyFormH1_eq_firstMixedEigenvalue_mul`: it is positive,
  at most every mixed eigenvalue, and under the Rellich property a mixed eigenvalue.
* `TauCeti.PDE.firstMixedEigenvalue_mul_norm_value_sq_le`,
  `TauCeti.PDE.isGreatest_firstMixedEigenvalue` and
  `TauCeti.PDE.isLeast_rayleighQuotient_firstMixedEigenvalue`: the Rayleigh principle.
* `TauCeti.PDE.isLeast_spectrum_mixedOperator_firstMixedEigenvalue`: it is the bottom of the
  spectrum of the mixed realization.
* `TauCeti.PDE.firstMixedEigenvalue_frontier`: at `Γ = ∂Ω` it is the first Dirichlet eigenvalue.
* `TauCeti.PDE.isLeast_norm_value_le_mul_norm_gradient_inv_sqrt_firstMixedEigenvalue`: for `-Δ_Γ`,
  the optimal Poincaré–Friedrichs constant.
* `TauCeti.PDE.exists_firstMixedEigenvalue_laplacian_of_isLipschitzDomainWith`: the mixed Laplacian
  on a bounded connected Lipschitz domain, for `Γ` of positive surface measure.
* `TauCeti.PDE.exists_hilbertBasis_nat_isMixedEigenvalue_monotone`: the mixed eigenvalues of a
  symmetric form satisfying a Gårding inequality on `H¹_Γ(Ω)`, as a nondecreasing sequence tending
  to infinity with an orthonormal eigenbasis of `L²(Ω)`.
* `TauCeti.PDE.mixedEigenvalue`: the `k`-th mixed eigenvalue, by min–max, with
  `TauCeti.PDE.mixedEigenvalue_eq_of_hilbertBasis`, `TauCeti.PDE.isLeast_mixedEigenvalue`,
  `TauCeti.PDE.exists_hilbertBasis_mixedEigenvalue`, `TauCeti.PDE.monotone_mixedEigenvalue`,
  `TauCeti.PDE.tendsto_mixedEigenvalue_atTop`,
  `TauCeti.PDE.isMixedEigenvalue_iff_exists_mixedEigenvalue_eq` and, for a nonnegative form,
  `TauCeti.PDE.mixedEigenvalue_nonneg`.
* `TauCeti.PDE.mixedEigenvalue_frontier` and `TauCeti.PDE.mixedEigenvalue_le_of_subset`: the
  Dirichlet case and monotonicity in `Γ`.
* `TauCeti.PDE.exists_hilbertBasis_mixedEigenvalue_laplacian`,
  `TauCeti.PDE.isLeast_mixedEigenvalue_laplacian`,
  `TauCeti.PDE.mixedEigenvalue_laplacian_spectrum` and
  `TauCeti.PDE.mixedEigenvalue_laplacian_le_of_subset`: the same for `-Δ`, and
  `TauCeti.PDE.mixedEigenvalue_laplacian_le_dirichletEigenvalue`: for `Γ ⊆ ∂Ω` the mixed
  eigenvalues of `-Δ` lie below the Dirichlet ones.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 9.31 and its proof (the Dirichlet case), and Proposition 9.24 (the Neumann problem).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 6.5.1, Theorem 2 (the
  variational characterization of the principal eigenvalue).
* R. Courant and D. Hilbert, *Methods of Mathematical Physics*, Vol. I, Chapter VI, §1–§2 (the
  min–max principle and the comparison of boundary conditions).
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Bornology Filter MeasureTheory Module Set TopologicalSpace
open scoped ENNReal InnerProductSpace NNReal

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {Γ Γ' : Set (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ}

attribute [local instance] W1pVanishingOn.instNormedAddCommGroup
  W1pVanishingOn.instInnerProductSpace

/-! ### Mixed eigenvalues -/

variable (mu Omega Γ a b c) in
/-- **A mixed eigenvalue** of the divergence-form operator `L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u`
on `Ω`, with the Dirichlet condition on `closure Γ`: a real number `κ` for which some
nonzero `u ∈ H¹_Γ(Ω)` satisfies

`a(u, v) = κ ∫_Ω u v` for every `v ∈ H¹_Γ(Ω)`,

where `a` is the energy form of `L` and `H¹_Γ(Ω)` is `TauCeti.w1pVanishingOnSubmodule`, the closure
of the test functions supported away from `closure Γ`. So the Dirichlet condition is imposed on
`closure Γ`, which may be larger than `Γ`. The test functions are unconstrained on the remaining
boundary `∂Ω \ closure Γ`, where, for regular enough solutions and boundaries, this weak
formulation encodes the natural (conormal) boundary condition. For
`Γ = ∂Ω` this is `TauCeti.PDE.IsDirichletEigenvalue`, and for `Γ = ∅`, on a domain where
`H¹_∅(Ω) = H¹(Ω)`, the Neumann eigenvalue problem. -/
def IsMixedEigenvalue (kappa : ℝ) : Prop :=
  ∃ u : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule, u ≠ 0 ∧
    ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        kappa * ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ

/-- Unfolding `TauCeti.PDE.IsMixedEigenvalue`: a nonzero `u ∈ H¹_Γ(Ω)` with
`a(u, v) = κ ⟪u, v⟫_{L²(Ω)}` for every `v ∈ H¹_Γ(Ω)`. -/
theorem isMixedEigenvalue_iff (kappa : ℝ) :
    IsMixedEigenvalue mu Omega Γ a b c kappa ↔
      ∃ u : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule, u ≠ 0 ∧
        ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
          energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
            kappa * ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ :=
  Iff.rfl

/-- **At the whole frontier the mixed eigenvalues are the Dirichlet eigenvalues**, since
`H¹_{∂Ω}(Ω) = H¹₀(Ω)` (`TauCeti.w1pVanishingOnSubmodule_frontier`). -/
@[simp]
theorem isMixedEigenvalue_frontier_iff (kappa : ℝ) :
    IsMixedEigenvalue mu Omega (frontier (Omega : Set (EuclideanSpace ℝ ι))) a b c kappa ↔
      IsDirichletEigenvalue mu Omega a b c kappa := by
  rw [IsMixedEigenvalue, w1pVanishingOnSubmodule_frontier, isDirichletEigenvalue_iff]

/-! ### The first mixed eigenvalue -/

/-- The **first mixed eigenvalue** of a divergence-form operator whose energy form is coercive on
`H¹_Γ(Ω)`: the reciprocal of the norm of the mixed solution operator. For a symmetric energy form
it is the optimal constant in `λ₁ ‖u‖²_{L²} ≤ a(u, u)`
(`TauCeti.PDE.isGreatest_firstMixedEigenvalue`), and on a domain with the Rellich property it is
the least mixed eigenvalue (`TauCeti.PDE.isLeast_spectrum_mixedOperator_firstMixedEigenvalue`). -/
def firstMixedEigenvalue
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (Γ : Set (EuclideanSpace ℝ ι)) (hB : IsCoercive (mixedForm hcoeff Γ 0)) : ℝ :=
  ‖mixedSolutionOperator hcoeff Γ hB‖⁻¹

/-- The first mixed eigenvalue is the reciprocal of the operator norm of the mixed solution
operator. -/
theorem firstMixedEigenvalue_def
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hB : IsCoercive (mixedForm hcoeff Γ 0)) :
    firstMixedEigenvalue hcoeff Γ hB = ‖mixedSolutionOperator hcoeff Γ hB‖⁻¹ :=
  (rfl)

/-- The unshifted mixed form of a symmetric energy form is symmetric. -/
private theorem mixedForm_zero_comm
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hsymm : ∀ u v : W1pVanishingOn mu Omega 2 Γ,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    (u v : W1pVanishingOn mu Omega 2 Γ) :
    mixedForm hcoeff Γ 0 u v = mixedForm hcoeff Γ 0 v u := by
  rw [mixedForm_zero_apply, mixedForm_zero_apply]
  exact hsymm u v

/-- The first mixed eigenvalue is positive on a nonempty `Ω`, when `Γ` misses `Ω`. -/
theorem firstMixedEigenvalue_pos
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hB : IsCoercive (mixedForm hcoeff Γ 0)) (hΓ : Disjoint Γ Omega)
    (hOmega : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty) :
    0 < firstMixedEigenvalue hcoeff Γ hB := by
  rw [firstMixedEigenvalue_def, mixedSolutionOperator_def]
  exact inv_pos.mpr (norm_pos_iff.mpr
    (hB.formSolutionOperator_ne_zero (W1pVanishingOn.valueL_ne_zero hΓ hOmega)))

/-- **The first mixed eigenvalue is at most every mixed eigenvalue**: if
`a(u, v) = κ ∫_Ω u v` for some nonzero `u ∈ H¹_Γ(Ω)` and every `v ∈ H¹_Γ(Ω)`, then `λ₁ ≤ κ`. -/
theorem firstMixedEigenvalue_le
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hB : IsCoercive (mixedForm hcoeff Γ 0)) {kappa : ℝ} {u : W1pVanishingOn mu Omega 2 Γ}
    (hu : u ≠ 0)
    (heq : ∀ v : W1pVanishingOn mu Omega 2 Γ,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        kappa * ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ) :
    firstMixedEigenvalue hcoeff Γ hB ≤ kappa := by
  rw [firstMixedEigenvalue_def, mixedSolutionOperator_def]
  exact hB.inv_norm_formSolutionOperator_le W1pVanishingOn.valueL hu fun v ↦ by
    rw [mixedForm_zero_apply, heq v, W1pVanishingOn.valueL_apply,
      W1pVanishingOn.valueL_apply]

/-- **The first mixed eigenvalue is a mixed eigenvalue** on a nonempty domain with the Rellich
property, for a symmetric energy form: `a(u, v) = λ₁ ∫_Ω u v` for some nonzero `u ∈ H¹_Γ(Ω)` and
every `v ∈ H¹_Γ(Ω)`. -/
theorem exists_ne_zero_forall_energyFormH1_eq_firstMixedEigenvalue_mul
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hB : IsCoercive (mixedForm hcoeff Γ 0)) (hΓ : Disjoint Γ Omega)
    (hsymm : ∀ u v : W1pVanishingOn mu Omega 2 Γ,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (hOmega : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty) :
    ∃ u : W1pVanishingOn mu Omega 2 Γ, u ≠ 0 ∧
      ∀ v : W1pVanishingOn mu Omega 2 Γ,
        energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
          firstMixedEigenvalue hcoeff Γ hB *
            ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
  obtain ⟨u, hu, heq⟩ := hB.exists_ne_zero_forall_apply_eq_inv_norm_smul_inner
    (W1pVanishingOn.isCompactOperator_valueL hK) (mixedForm_zero_comm hcoeff hsymm)
    (W1pVanishingOn.valueL_ne_zero hΓ hOmega)
  refine ⟨u, hu, fun v ↦ ?_⟩
  have hv := heq v
  rwa [mixedForm_zero_apply, W1pVanishingOn.valueL_apply,
    W1pVanishingOn.valueL_apply, ← mixedSolutionOperator_def, ← firstMixedEigenvalue_def] at hv

/-! ### The Rayleigh principle -/

/-- **The first mixed eigenvalue is a Poincaré constant for the energy form**:
`λ₁ ‖u‖²_{L²(Ω)} ≤ a(u, u)` for every `u ∈ H¹_Γ(Ω)`, for a symmetric energy form. By
`TauCeti.PDE.isGreatest_firstMixedEigenvalue` it is the largest such constant. -/
theorem firstMixedEigenvalue_mul_norm_value_sq_le
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hB : IsCoercive (mixedForm hcoeff Γ 0))
    (hsymm : ∀ u v : W1pVanishingOn mu Omega 2 Γ,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    (u : W1pVanishingOn mu Omega 2 Γ) :
    firstMixedEigenvalue hcoeff Γ hB * ‖W1p.value (u : W1p mu Omega 2)‖ ^ 2 ≤
      energyFormH1 a b c (u : W1p mu Omega 2) (u : W1p mu Omega 2) := by
  rw [firstMixedEigenvalue_def, mixedSolutionOperator_def]
  have h := hB.inv_norm_formSolutionOperator_mul_norm_apply_sq_le W1pVanishingOn.valueL
    (mixedForm_zero_comm hcoeff hsymm) u
  rwa [mixedForm_zero_apply, W1pVanishingOn.valueL_apply] at h

/-- **The first mixed eigenvalue is the optimal Poincaré constant of the energy form**: on a
nonempty `Ω`, for `Γ` missing `Ω` and a symmetric energy form, `λ₁` is the largest `C` with
`C ‖u‖²_{L²(Ω)} ≤ a(u, u)` for every `u ∈ H¹_Γ(Ω)`. No compactness is needed. -/
theorem isGreatest_firstMixedEigenvalue
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hB : IsCoercive (mixedForm hcoeff Γ 0)) (hΓ : Disjoint Γ Omega)
    (hsymm : ∀ u v : W1pVanishingOn mu Omega 2 Γ,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    (hOmega : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty) :
    IsGreatest {C : ℝ | ∀ u : W1pVanishingOn mu Omega 2 Γ,
        C * ‖W1p.value (u : W1p mu Omega 2)‖ ^ 2 ≤
          energyFormH1 a b c (u : W1p mu Omega 2) (u : W1p mu Omega 2)}
      (firstMixedEigenvalue hcoeff Γ hB) := by
  have hset : {C : ℝ | ∀ u : W1pVanishingOn mu Omega 2 Γ,
      C * ‖W1p.value (u : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (u : W1p mu Omega 2) (u : W1p mu Omega 2)} =
      {C : ℝ | ∀ u : W1pVanishingOn mu Omega 2 Γ,
        C * ‖W1pVanishingOn.valueL u‖ ^ 2 ≤ mixedForm hcoeff Γ 0 u u} := by
    simp only [W1pVanishingOn.valueL_apply, mixedForm_zero_apply]
  rw [hset, firstMixedEigenvalue_def, mixedSolutionOperator_def]
  exact hB.isGreatest_inv_norm_formSolutionOperator (mixedForm_zero_comm hcoeff hsymm)
    (W1pVanishingOn.valueL_ne_zero hΓ hOmega)

/-- **The Rayleigh principle for the mixed problem.** On a nonempty domain with the Rellich
property, for `Γ` missing `Ω` and a symmetric energy form, the first mixed eigenvalue is the
minimum of the Rayleigh quotient

`a(u, u) / ‖u‖²_{L²(Ω)}`

over the `u ∈ H¹_Γ(Ω)` with nonzero value; the minimum is attained at an eigenfunction. -/
theorem isLeast_rayleighQuotient_firstMixedEigenvalue
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hB : IsCoercive (mixedForm hcoeff Γ 0)) (hΓ : Disjoint Γ Omega)
    (hsymm : ∀ u v : W1pVanishingOn mu Omega 2 Γ,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (hOmega : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty) :
    IsLeast {r : ℝ | ∃ u : W1pVanishingOn mu Omega 2 Γ, W1p.value (u : W1p mu Omega 2) ≠ 0 ∧
        energyFormH1 a b c (u : W1p mu Omega 2) (u : W1p mu Omega 2) /
          ‖W1p.value (u : W1p mu Omega 2)‖ ^ 2 = r}
      (firstMixedEigenvalue hcoeff Γ hB) := by
  have hset : {r : ℝ | ∃ u : W1pVanishingOn mu Omega 2 Γ, W1p.value (u : W1p mu Omega 2) ≠ 0 ∧
      energyFormH1 a b c (u : W1p mu Omega 2) (u : W1p mu Omega 2) /
        ‖W1p.value (u : W1p mu Omega 2)‖ ^ 2 = r} =
      {r : ℝ | ∃ u : W1pVanishingOn mu Omega 2 Γ, W1pVanishingOn.valueL u ≠ 0 ∧
        mixedForm hcoeff Γ 0 u u / ‖W1pVanishingOn.valueL u‖ ^ 2 = r} := by
    simp only [W1pVanishingOn.valueL_apply, mixedForm_zero_apply]
  rw [hset, firstMixedEigenvalue_def, mixedSolutionOperator_def]
  exact hB.isLeast_rayleighQuotient (W1pVanishingOn.isCompactOperator_valueL hK)
    (mixedForm_zero_comm hcoeff hsymm) (W1pVanishingOn.valueL_ne_zero hΓ hOmega)

/-! ### The mixed realization -/

/-- Coercivity of the unshifted mixed form is the Gårding inequality with `ω = 0`. -/
private theorem exists_garding_of_isCoercive_mixedForm_zero
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hB : IsCoercive (mixedForm hcoeff Γ 0)) :
    ∃ theta : ℝ, 0 < theta ∧ ∀ v : W1pVanishingOn mu Omega 2 Γ,
      theta * ‖(v : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) +
          0 * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2 := by
  obtain ⟨C, hC, hle⟩ := hB
  refine ⟨C, hC, fun v ↦ ?_⟩
  have hv := hle v
  rw [mixedForm_zero_apply, ← Submodule.norm_coe] at hv
  rw [zero_mul, add_zero, sq, ← mul_assoc]
  exact hv

/-- **The first mixed eigenvalue is the bottom of the spectrum.** On a nonempty domain with the
Rellich property, for `Γ` missing `Ω` and a symmetric energy form coercive on `H¹_Γ(Ω)`, the first
mixed eigenvalue is the least point of the spectrum of the mixed realization. -/
theorem isLeast_spectrum_mixedOperator_firstMixedEigenvalue
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hB : IsCoercive (mixedForm hcoeff Γ 0)) (hΓ : Disjoint Γ Omega)
    (hsymm : ∀ u v : W1pVanishingOn mu Omega 2 Γ,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (hOmega : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty) :
    IsLeast (mixedOperator hcoeff Γ).spectrum (firstMixedEigenvalue hcoeff Γ hB) := by
  obtain ⟨theta, htheta, hgarding⟩ := exists_garding_of_isCoercive_mixedForm_zero hcoeff hB
  refine ⟨(mem_spectrum_mixedOperator_iff hcoeff hΓ htheta hgarding hK).2
    (exists_ne_zero_forall_energyFormH1_eq_firstMixedEigenvalue_mul hcoeff hB hΓ hsymm hK hOmega),
    fun kappa hkappa ↦ ?_⟩
  obtain ⟨u, hu, heq⟩ := (mem_spectrum_mixedOperator_iff hcoeff hΓ htheta hgarding hK).1 hkappa
  exact firstMixedEigenvalue_le hcoeff hB hu heq

/-- **At the whole frontier the first mixed eigenvalue is the first Dirichlet eigenvalue**: the
mixed realization at `Γ = ∂Ω` is the Dirichlet realization, so the two solution operators, minus
their resolvents at `0`, agree. -/
theorem firstMixedEigenvalue_frontier
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hB : IsCoercive (mixedForm hcoeff (frontier (Omega : Set (EuclideanSpace ℝ ι))) 0))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) :
    firstMixedEigenvalue hcoeff (frontier (Omega : Set (EuclideanSpace ℝ ι))) hB =
      firstDirichletEigenvalue hcoeff hcoercive := by
  have h := resolvent_mixedOperator_zero hcoeff (disjoint_frontier_iff_isOpen.2 Omega.isOpen) hB
  rw [mixedOperator_frontier hcoeff hcoercive, resolvent_dirichletOperator_zero, neg_inj] at h
  rw [firstMixedEigenvalue_def, firstDirichletEigenvalue_def, h]

/-! ### The first eigenvalue of the mixed Laplacian -/

section Laplacian

variable [DecidableEq ι]

/-- **The optimal Poincaré–Friedrichs constant is `1 / √λ₁`.** On a nonempty `Ω`, for `Γ` missing
`Ω`, when `∫_Ω ∇u · ∇v` is coercive on `H¹_Γ(Ω)`, the least `P ≥ 0` with
`‖u‖_{L²(Ω)} ≤ P ‖∇u‖_{L²(Ω)}` for every `u ∈ H¹_Γ(Ω)` is `1 / √λ₁` for the first mixed
eigenvalue `λ₁` of `-Δ_Γ`: `λ₁` is the reciprocal of the square of the optimal constant. -/
theorem isLeast_norm_value_le_mul_norm_gradient_inv_sqrt_firstMixedEigenvalue
    (hΓ : Disjoint Γ Omega) (hOmega : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty)
    (hB : IsCoercive (mixedForm (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
      (1 : Matrix ι ι ℝ)) Γ 0)) :
    IsLeast {P : ℝ | 0 ≤ P ∧ ∀ u ∈ w1pVanishingOnSubmodule mu Omega 2 Γ,
        ‖W1p.value u‖ ≤ P * ‖W1p.gradient u‖}
      (√(firstMixedEigenvalue _ Γ hB))⁻¹ := by
  have hpos := firstMixedEigenvalue_pos _ hB hΓ hOmega
  have hgreat := isGreatest_firstMixedEigenvalue _ hB hΓ
    (fun u v ↦ energyFormH1_one_zero_zero_comm (u : W1p mu Omega 2) v) hOmega
  have hsqrt := Real.sqrt_pos.mpr hpos
  refine ⟨⟨inv_nonneg.mpr (Real.sqrt_nonneg _), fun u hu ↦ ?_⟩, fun P ⟨hP0, hP⟩ ↦ ?_⟩
  · -- `λ₁ ‖u‖² ≤ ‖∇u‖²`, so `√λ₁ ‖u‖ ≤ ‖∇u‖`.
    have h := hgreat.1 ⟨u, hu⟩
    rw [energyFormH1_one_zero_zero_eq_inner, real_inner_self_eq_norm_sq] at h
    rw [← div_eq_inv_mul, le_div_iff₀ hsqrt]
    refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp ?_
    rw [mul_pow, Real.sq_sqrt hpos.le]
    linarith
  · -- `P = 0` would kill every value; otherwise `1 / P²` is a Poincaré constant, so `≤ λ₁`.
    have hPpos : 0 < P := by
      refine hP0.lt_of_ne fun h ↦ W1pVanishingOn.valueL_ne_zero (mu := mu) (p := 2) hΓ hOmega ?_
      ext1 u
      have hu := hP _ u.property
      rw [← h, zero_mul, norm_le_zero_iff] at hu
      rw [W1pVanishingOn.valueL_apply, hu, zero_apply]
    have hC : (P ^ 2)⁻¹ ≤ firstMixedEigenvalue _ Γ hB := hgreat.2 fun u ↦ by
      rw [energyFormH1_one_zero_zero_eq_inner, real_inner_self_eq_norm_sq,
        inv_mul_le_iff₀ (by positivity), ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hP _ u.property) 2
    rw [inv_le_comm₀ hsqrt hPpos, Real.le_sqrt (inv_nonneg.mpr hP0) hpos.le, inv_pow]
    exact hC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {V : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0}

/-- **The first mixed eigenvalue of `-Δ_Γ` for a boundary part of positive measure.** Let an
affine isometry `e` carry the connected open set `Ω ⊆ EuclideanSpace ℝ ι` onto a bounded Lipschitz
domain `V`, and let `Γ`, disjoint from `Ω`, meet the frontier of `Ω` in a set of positive surface
measure. Then `∫_Ω ∇u · ∇v` is coercive on `H¹_Γ(Ω)`, and its first mixed eigenvalue `λ₁`

* is positive;
* is the least point of the spectrum of the mixed Laplacian `-Δ_Γ`;
* is the reciprocal of the square of the optimal Poincaré–Friedrichs constant: `1 / √λ₁` is the
  least `P ≥ 0` with `‖u‖_{L²(Ω)} ≤ P ‖∇u‖_{L²(Ω)}` on `H¹_Γ(Ω)`.

Moreover `-Δ_Γ` is invertible with a compact self-adjoint inverse: `0` is a resolvent point, where
the resolvent is `-S` for the mixed solution operator `S`, which is compact and symmetric. -/
theorem exists_firstMixedEigenvalue_laplacian_of_isLipschitzDomainWith
    (hV : (V : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hVb : IsBounded (V : Set (WithLp 2 (ℝ × E))))
    (e : EuclideanSpace ℝ ι ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E))
    (hVΩ : (V : Set (WithLp 2 (ℝ × E))) = e.symm ⁻¹' Omega)
    (hconn : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (hΓ : (μHE[finrank ℝ E] : Measure (EuclideanSpace ℝ ι))
      (Γ ∩ frontier (Omega : Set (EuclideanSpace ℝ ι))) ≠ 0)
    (hΓΩ : Disjoint Γ Omega) :
    ∃ hB : IsCoercive (mixedForm (memLp_energyIntegrand_const_zero_zero (mu := volume)
        (Omega := Omega) (1 : Matrix ι ι ℝ)) Γ 0),
      0 < firstMixedEigenvalue _ Γ hB ∧
      IsLeast (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := volume)
        (Omega := Omega) (1 : Matrix ι ι ℝ)) Γ).spectrum (firstMixedEigenvalue _ Γ hB) ∧
      IsLeast {P : ℝ | 0 ≤ P ∧ ∀ u ∈ w1pVanishingOnSubmodule volume Omega 2 Γ,
          ‖W1p.value u‖ ≤ P * ‖W1p.gradient u‖} (√(firstMixedEigenvalue _ Γ hB))⁻¹ ∧
      (0 : ℝ) ∈ (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := volume)
        (Omega := Omega) (1 : Matrix ι ι ℝ)) Γ).resolventSet ∧
      (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := volume)
        (Omega := Omega) (1 : Matrix ι ι ℝ)) Γ).resolvent 0 =
          -mixedSolutionOperator _ Γ hB ∧
      IsCompactOperator (mixedSolutionOperator _ Γ hB) ∧
      LinearMap.IsSymmetric (mixedSolutionOperator _ Γ hB :
        Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ ι))) →ₗ[ℝ]
          Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ ι)))) := by
  -- `Ω` is nonempty, since `Γ` meets its frontier in a set of positive measure.
  have hOmega : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty := by
    refine ne_empty_iff_nonempty.mp fun h ↦ hΓ ?_
    rw [h, frontier_empty, inter_empty, measure_empty]
  have hB := isCoercive_mixedForm_laplacian_of_isLipschitzDomainWith hV hVb e hVΩ hconn hΓ
  have hK := W1p.isCompactOperator_valueL_of_isLipschitzDomainWith_of_affineIsometryEquiv
    (p := 2) hV hVb e hVΩ
  have hsymm (u v : W1pVanishingOn volume Omega 2 Γ) :
      energyFormH1 (fun _ ↦ 1) 0 0 (u : W1p volume Omega 2) (v : W1p volume Omega 2) =
        energyFormH1 (fun _ ↦ 1) 0 0 (v : W1p volume Omega 2) (u : W1p volume Omega 2) :=
    energyFormH1_one_zero_zero_comm _ _
  exact ⟨hB, firstMixedEigenvalue_pos _ hB hΓΩ hOmega,
    isLeast_spectrum_mixedOperator_firstMixedEigenvalue _ hB hΓΩ hsymm hK hOmega,
    isLeast_norm_value_le_mul_norm_gradient_inv_sqrt_firstMixedEigenvalue hΓΩ hOmega hB,
    zero_mem_resolventSet_mixedOperator _ hΓΩ hB, resolvent_mixedOperator_zero _ hΓΩ hB,
    isCompactOperator_mixedSolutionOperator _ hB hK, isSymmetric_mixedSolutionOperator _ hB hsymm⟩

end Laplacian

/-! ### The shifted energy form on `H¹_Γ(Ω)` -/

/-- The eigenvalue equations of the energy form and of its shift by `ω` correspond, with
eigenvalues `κ` and `κ + ω`. -/
private theorem forall_mixedForm_eq_iff
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (omega kappa : ℝ) (u : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule) :
    (∀ v, mixedForm hcoeff Γ omega u v =
        (kappa + omega) * ⟪W1pVanishingOn.valueL u, W1pVanishingOn.valueL v⟫_ℝ) ↔
      ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
        energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
          kappa * ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
  refine forall_congr' fun v ↦ ?_
  rw [mixedForm_apply, W1pVanishingOn.valueL_apply, W1pVanishingOn.valueL_apply, add_mul]
  exact add_left_inj _

/-! ### The mixed eigenvalues as a sequence -/

/-- **The mixed eigenvalues form a sequence `λ₀ ≤ λ₁ ≤ ⋯ → ∞`.** Let `Ω ⊆ ℝⁿ`, `n ≥ 1`, be a
nonempty open set with the Rellich property, that the value map `H¹(Ω) → L²(Ω)` is compact, for
instance a bounded Lipschitz domain, and let `Γ` miss `Ω`. Let the energy form `a` be symmetric on
`H¹_Γ(Ω)` and satisfy the Gårding inequality `θ ‖v‖²_{H¹} ≤ a(v, v) + ω ‖v‖²_{L²}` there, with
`θ > 0`. Then there are a nondecreasing sequence `λₖ` tending to infinity and an orthonormal basis
`(eₖ)` of `L²(Ω)` such that `eₖ` is the value of some `uₖ ∈ H¹_Γ(Ω)` with

`a(uₖ, v) = λₖ ∫_Ω uₖ v` for every `v ∈ H¹_Γ(Ω)`.

The sequence lists the mixed spectrum with multiplicity: `κ` is a mixed eigenvalue exactly when
`κ = λₖ` for some `k`. -/
theorem exists_hilbertBasis_nat_isMixedEigenvalue_monotone [Nonempty ι]
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hrellich : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (hΓ : Disjoint Γ Omega)
    (hsymm : ∀ u v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    {theta omega : ℝ} (htheta : 0 < theta)
    (hgarding : ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      theta * ‖(v : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) +
          omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2)
    (hOmega_nonempty : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty) :
    ∃ (basis : HilbertBasis ℕ ℝ (Lp ℝ 2 (mu.restrict Omega))) (kappa : ℕ → ℝ)
      (u : ℕ → (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule),
      Monotone kappa ∧ Tendsto kappa atTop atTop ∧
      (∀ k, W1p.value (u k : W1p mu Omega 2) = basis k) ∧
      (∀ (k : ℕ) (v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule),
        energyFormH1 a b c (u k : W1p mu Omega 2) (v : W1p mu Omega 2) =
          kappa k * ⟪W1p.value (u k : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ) ∧
      ∀ kappa' : ℝ, IsMixedEigenvalue mu Omega Γ a b c kappa' ↔ ∃ k, kappa k = kappa' := by
  have hB := isCoercive_mixedForm hcoeff htheta hgarding
  obtain ⟨basis, kappa, u, hmono, htendsto, -, hvalue, heq, hiff, -⟩ :=
    hB.exists_hilbertBasis_nat_forall_apply_eq_smul_inner_monotone
      (W1pVanishingOn.isCompactOperator_valueL hrellich)
      (W1pVanishingOn.denseRange_valueL_two hΓ)
      (fun u v ↦ by rw [mixedForm_apply, mixedForm_apply, hsymm, real_inner_comm])
      (L2.not_finiteDimensional_restrict_of_isOpen mu Omega.isOpen hOmega_nonempty)
  refine ⟨basis, fun k ↦ kappa k - omega, u, fun k l hkl ↦ by simpa using hmono hkl,
    by simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right _ (-omega) htendsto,
    fun k ↦ by rw [← W1pVanishingOn.valueL_apply, hvalue],
    fun k ↦ (forall_mixedForm_eq_iff hcoeff omega _ (u k)).1 ?_, fun kappa' ↦ ?_⟩
  · simpa only [sub_add_cancel] using heq k
  · rw [isMixedEigenvalue_iff]
    simp_rw [← forall_mixedForm_eq_iff hcoeff omega kappa', hiff (kappa' + omega),
      sub_eq_iff_eq_add]

/-! ### The min–max principle -/

variable (mu Omega Γ a b c) in
/-- **The `k`-th mixed eigenvalue** of the divergence-form operator with coefficients `a, b, c` on
`Ω`, with the Dirichlet condition on `closure Γ`, counted from `k = 0` with multiplicity, by the
Courant–Fischer min–max principle: the infimum of the constants `C` such that
`a(v, v) ≤ C ‖v‖²_{L²(Ω)}` for every `v` in some subspace `W` of `H¹_Γ(Ω)` whose values span a
subspace of `L²(Ω)` of dimension at least `k + 1`.

For a symmetric form bounded below, `a(v, v) + ω ‖v‖²_{L²} ≥ 0`, with an orthonormal eigenbasis
the infimum is attained and equals the `k`-th term of the nondecreasing listing of the eigenvalues
(`TauCeti.PDE.mixedEigenvalue_eq_of_hilbertBasis`). Otherwise the infimum may be over an empty or
unbounded set, and the value carries no information. -/
def mixedEigenvalue (k : ℕ) : ℝ :=
  sInf {C : ℝ | ∃ W : Submodule ℝ (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
    k + 1 ≤ Module.finrank ℝ
      (W.map ((W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap ∘ₗ
        (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule.subtype)) ∧
      ∀ v ∈ W, energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
        C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2}

/-- The definition of the `k`-th mixed eigenvalue as an infimum. -/
theorem mixedEigenvalue_def (k : ℕ) :
    mixedEigenvalue mu Omega Γ a b c k =
      sInf {C : ℝ | ∃ W : Submodule ℝ (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
        k + 1 ≤ Module.finrank ℝ
          (W.map ((W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap ∘ₗ
            (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule.subtype)) ∧
          ∀ v ∈ W, energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
            C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2} :=
  (rfl)

/-- **At the whole frontier the mixed eigenvalues are the Dirichlet eigenvalues**, since
`H¹_{∂Ω}(Ω) = H¹₀(Ω)` (`TauCeti.w1pVanishingOnSubmodule_frontier`). -/
@[simp]
theorem mixedEigenvalue_frontier :
    mixedEigenvalue mu Omega (frontier (Omega : Set (EuclideanSpace ℝ ι))) a b c =
      dirichletEigenvalue mu Omega a b c := by
  have hJ : (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap ∘ₗ
      (w1p0Submodule mu Omega 2).toSubmodule.subtype = (W1p0.valueL).toLinearMap :=
    LinearMap.ext fun v ↦ by simp
  funext k
  rw [mixedEigenvalue_def, dirichletEigenvalue_def, w1pVanishingOnSubmodule_frontier, hJ]

/-- The min–max principle `TauCeti.isLeast_minMax_of_hilbertBasis` for the energy form on
`H¹_Γ(Ω)` and the value map `H¹_Γ(Ω) → L²(Ω)`, for a form bounded below by `-ω ‖v‖²_{L²}`. It
is applied to the nonnegative form shifted by `ω`, with eigenvalues `κⱼ + ω`, and the least
constant is shifted back by `ω`. -/
private theorem isLeast_of_hilbertBasis
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hsymm : ∀ u v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    {omega : ℝ} (hlower : ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      0 ≤ energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) +
        omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2)
    (basis : HilbertBasis ℕ ℝ (Lp ℝ 2 (mu.restrict Omega))) {kappa : ℕ → ℝ}
    (hkappa : Monotone kappa) {u : ℕ → (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule}
    (hvalue : ∀ j, W1p.value (u j : W1p mu Omega 2) = basis j)
    (heq : ∀ (j : ℕ) (v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule),
      energyFormH1 a b c (u j : W1p mu Omega 2) (v : W1p mu Omega 2) =
        kappa j * ⟪W1p.value (u j : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ)
    (k : ℕ) :
    IsLeast {C : ℝ | ∃ W : Submodule ℝ (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      k + 1 ≤ Module.finrank ℝ
        (W.map ((W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap ∘ₗ
          (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule.subtype)) ∧
        ∀ v ∈ W, energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
          C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2} (kappa k) := by
  let J := (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap ∘ₗ
    (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule.subtype
  have hJ (v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule) :
      J v = W1p.value (v : W1p mu Omega 2) := by
    simp [J]
  have hB (u v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule) :
      (mixedForm hcoeff Γ omega).toLinearMap₁₂ u v =
        energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) +
          omega * ⟪J u, J v⟫_ℝ := by
    rw [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, mixedForm_apply, hJ, hJ]
  -- `C` is admissible for the form exactly when `C + ω` is admissible for the shifted form.
  have hmem (W : Submodule ℝ (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule) (C : ℝ) :
      (∀ v ∈ W, (mixedForm hcoeff Γ omega).toLinearMap₁₂ v v ≤ (C + omega) * ‖J v‖ ^ 2) ↔
        ∀ v ∈ W, energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
          C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2 := by
    refine forall₂_congr fun v _ ↦ ?_
    rw [hB, real_inner_self_eq_norm_sq, hJ, add_mul]
    exact add_le_add_iff_right (omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2)
  have h := isLeast_minMax_of_hilbertBasis (B := (mixedForm hcoeff Γ omega).toLinearMap₁₂)
    (J := J) (fun v w ↦ by rw [hB, hB, hsymm, real_inner_comm])
    (fun v ↦ by rw [hB, real_inner_self_eq_norm_sq, hJ]; exact hlower v)
    basis (kappa := fun j ↦ kappa j + omega) (fun _ _ hij ↦ by simpa using hkappa hij)
    (fun j ↦ by rw [hJ, hvalue]) (fun j v ↦ by rw [hB, hJ, hJ, heq, add_mul]) k
  refine ⟨?_, fun C ⟨W, hW, hC⟩ ↦ le_of_add_le_add_right (h.2 ⟨W, hW, (hmem W C).2 hC⟩)⟩
  obtain ⟨W, hW, hC⟩ := h.1
  exact ⟨W, hW, (hmem W (kappa k)).1 hC⟩

/-- **The Courant–Fischer min–max principle for the mixed eigenvalues.** Let the energy form `a`
be symmetric on `H¹_Γ(Ω)` and bounded below there, `a(v, v) + ω ‖v‖²_{L²} ≥ 0` for some `ω`,
as under a Gårding inequality, and let `κ₀ ≤ κ₁ ≤ ⋯` be eigenvalues with
eigenfunctions `uⱼ ∈ H¹_Γ(Ω)`, `a(uⱼ, v) = κⱼ ⟪uⱼ, v⟫_{L²}` for every `v ∈ H¹_Γ(Ω)`, whose values
form an orthonormal basis of `L²(Ω)`. Then `κₖ` is the `k`-th mixed eigenvalue `λₖ`. In
particular any two such listings agree. -/
theorem mixedEigenvalue_eq_of_hilbertBasis
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hsymm : ∀ u v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    {omega : ℝ} (hlower : ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      0 ≤ energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) +
        omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2)
    (basis : HilbertBasis ℕ ℝ (Lp ℝ 2 (mu.restrict Omega))) {kappa : ℕ → ℝ}
    (hkappa : Monotone kappa) {u : ℕ → (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule}
    (hvalue : ∀ j, W1p.value (u j : W1p mu Omega 2) = basis j)
    (heq : ∀ (j : ℕ) (v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule),
      energyFormH1 a b c (u j : W1p mu Omega 2) (v : W1p mu Omega 2) =
        kappa j * ⟪W1p.value (u j : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ)
    (k : ℕ) :
    mixedEigenvalue mu Omega Γ a b c k = kappa k :=
  (isLeast_of_hilbertBasis hcoeff hsymm hlower basis hkappa hvalue heq k).csInf_eq

/-- A Gårding inequality `θ ‖v‖²_{H¹} ≤ a(v, v) + ω ‖v‖²_{L²}` bounds the energy form below by
`-ω ‖v‖²_{L²}`. -/
private theorem energyFormH1_add_nonneg_of_garding {theta omega : ℝ} (htheta : 0 < theta)
    (hgarding : ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      theta * ‖(v : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) +
          omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2)
    (v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule) :
    0 ≤ energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) +
      omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2 :=
  (mul_nonneg htheta.le (sq_nonneg _)).trans (hgarding v)

/-- **The mixed eigenvalues of a nonnegative form are nonnegative**: if `a(v, v) ≥ 0` for every
`v ∈ H¹_Γ(Ω)`, then `0 ≤ λₖ` for every `k`. Every constant `C` admissible in the min–max
principle is nonnegative, since an admissible subspace contains some `v` with nonzero value in
`L²(Ω)`, and `0 ≤ a(v, v) ≤ C ‖v‖²_{L²(Ω)}`. -/
theorem mixedEigenvalue_nonneg
    (hnonneg : ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      0 ≤ energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2)) (k : ℕ) :
    0 ≤ mixedEigenvalue mu Omega Γ a b c k := by
  refine Real.sInf_nonneg fun C ⟨W, hW, hC⟩ ↦ ?_
  have hne : W.map ((W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap ∘ₗ
      (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule.subtype) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hW
    omega
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hy
  have hpos : 0 < ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2 :=
    pow_pos (norm_pos_iff.2 (by simpa [W1p.valueL_apply] using hy0)) 2
  exact nonneg_of_mul_nonneg_left ((hnonneg v).trans (hC v hv)) hpos

section Spectrum

variable [Nonempty ι]
  (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
  (hrellich : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
  (hΓ : Disjoint Γ Omega)
  (hsymm : ∀ u v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
    energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
      energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
  {theta omega : ℝ} (htheta : 0 < theta)
  (hgarding : ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
    theta * ‖(v : W1p mu Omega 2)‖ ^ 2 ≤
      energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) +
        omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2)
  (hOmega_nonempty : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty)
include hcoeff hrellich hΓ hsymm htheta hgarding hOmega_nonempty

/-- **The mixed eigenvalues with an eigenbasis.** On a nonempty open set with the Rellich property,
for a symmetric energy form satisfying a Gårding inequality on `H¹_Γ(Ω)`, there is an
orthonormal basis `(eₖ)` of `L²(Ω)` such that `eₖ` is the value of some `uₖ ∈ H¹_Γ(Ω)` with
`a(uₖ, v) = λₖ ⟪uₖ, v⟫_{L²}` for every `v ∈ H¹_Γ(Ω)`, where `λₖ` is the min–max eigenvalue
`TauCeti.PDE.mixedEigenvalue`. -/
theorem exists_hilbertBasis_mixedEigenvalue :
    ∃ (basis : HilbertBasis ℕ ℝ (Lp ℝ 2 (mu.restrict Omega)))
      (u : ℕ → (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule),
      (∀ k, W1p.value (u k : W1p mu Omega 2) = basis k) ∧
      ∀ (k : ℕ) (v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule),
        energyFormH1 a b c (u k : W1p mu Omega 2) (v : W1p mu Omega 2) =
          mixedEigenvalue mu Omega Γ a b c k *
            ⟪W1p.value (u k : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
  obtain ⟨basis, kappa, u, hmono, -, hvalue, heq, -⟩ :=
    exists_hilbertBasis_nat_isMixedEigenvalue_monotone hcoeff hrellich hΓ hsymm htheta hgarding
      hOmega_nonempty
  refine ⟨basis, u, hvalue, fun k v ↦ ?_⟩
  rw [mixedEigenvalue_eq_of_hilbertBasis hcoeff hsymm
    (energyFormH1_add_nonneg_of_garding htheta hgarding) basis hmono hvalue heq k, heq]

/-- **The min–max principle is attained.** On a nonempty open set with the Rellich property, for a
symmetric energy form satisfying a Gårding inequality on `H¹_Γ(Ω)`, `λₖ` is the least
`C` for which some subspace `W` of `H¹_Γ(Ω)`, whose values span a subspace of `L²(Ω)` of dimension
at least `k + 1`, satisfies `a(v, v) ≤ C ‖v‖²_{L²(Ω)}` for every `v ∈ W`. -/
theorem isLeast_mixedEigenvalue (k : ℕ) :
    IsLeast {C : ℝ | ∃ W : Submodule ℝ (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      k + 1 ≤ Module.finrank ℝ
        (W.map ((W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap ∘ₗ
          (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule.subtype)) ∧
        ∀ v ∈ W, energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
          C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2} (mixedEigenvalue mu Omega Γ a b c k) := by
  obtain ⟨basis, kappa, u, hmono, -, hvalue, heq, -⟩ :=
    exists_hilbertBasis_nat_isMixedEigenvalue_monotone hcoeff hrellich hΓ hsymm htheta hgarding
      hOmega_nonempty
  rw [mixedEigenvalue_eq_of_hilbertBasis hcoeff hsymm
    (energyFormH1_add_nonneg_of_garding htheta hgarding) basis hmono hvalue heq]
  exact isLeast_of_hilbertBasis hcoeff hsymm
    (energyFormH1_add_nonneg_of_garding htheta hgarding) basis hmono hvalue heq k

/-- Under the hypotheses of `TauCeti.PDE.exists_hilbertBasis_nat_isMixedEigenvalue_monotone`, the
mixed eigenvalues `λₖ` are that nondecreasing listing of the mixed spectrum. -/
private theorem mixedEigenvalue_properties :
    Monotone (mixedEigenvalue mu Omega Γ a b c) ∧
      Tendsto (mixedEigenvalue mu Omega Γ a b c) atTop atTop ∧
      ∀ kappa' : ℝ, IsMixedEigenvalue mu Omega Γ a b c kappa' ↔
        ∃ k, mixedEigenvalue mu Omega Γ a b c k = kappa' := by
  obtain ⟨basis, kappa, u, hmono, htendsto, hvalue, heq, hiff⟩ :=
    exists_hilbertBasis_nat_isMixedEigenvalue_monotone hcoeff hrellich hΓ hsymm htheta hgarding
      hOmega_nonempty
  obtain rfl : mixedEigenvalue mu Omega Γ a b c = kappa :=
    funext <| mixedEigenvalue_eq_of_hilbertBasis hcoeff hsymm
      (energyFormH1_add_nonneg_of_garding htheta hgarding) basis hmono hvalue heq
  exact ⟨hmono, htendsto, hiff⟩

/-- The mixed eigenvalues are nondecreasing: `λ₀ ≤ λ₁ ≤ ⋯`. -/
theorem monotone_mixedEigenvalue : Monotone (mixedEigenvalue mu Omega Γ a b c) :=
  (mixedEigenvalue_properties hcoeff hrellich hΓ hsymm htheta hgarding
    hOmega_nonempty).1

/-- The mixed eigenvalues tend to infinity. -/
theorem tendsto_mixedEigenvalue_atTop :
    Tendsto (mixedEigenvalue mu Omega Γ a b c) atTop atTop :=
  (mixedEigenvalue_properties hcoeff hrellich hΓ hsymm htheta hgarding
    hOmega_nonempty).2.1

/-- The mixed eigenvalues `λₖ` are exactly the mixed spectrum. -/
theorem isMixedEigenvalue_iff_exists_mixedEigenvalue_eq (kappa' : ℝ) :
    IsMixedEigenvalue mu Omega Γ a b c kappa' ↔
      ∃ k, mixedEigenvalue mu Omega Γ a b c k = kappa' :=
  (mixedEigenvalue_properties hcoeff hrellich hΓ hsymm htheta hgarding
    hOmega_nonempty).2.2 kappa'

end Spectrum

/-! ### Monotonicity in the boundary part -/

/-- The inclusion `H¹_{Γ'}(Ω) → H¹_Γ(Ω)` for `Γ ⊆ Γ'` turns a subspace admissible in the min–max
principle for `Γ'` into one admissible for `Γ` with the same constant. -/
private theorem mem_setOf_mixedEigenvalue_of_subset (hΓΓ' : Γ ⊆ Γ') {k : ℕ} {C : ℝ}
    (h : ∃ W : Submodule ℝ (w1pVanishingOnSubmodule mu Omega 2 Γ').toSubmodule,
      k + 1 ≤ Module.finrank ℝ
        (W.map ((W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap ∘ₗ
          (w1pVanishingOnSubmodule mu Omega 2 Γ').toSubmodule.subtype)) ∧
        ∀ v ∈ W, energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
          C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2) :
    ∃ W : Submodule ℝ (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      k + 1 ≤ Module.finrank ℝ
        (W.map ((W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap ∘ₗ
          (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule.subtype)) ∧
        ∀ v ∈ W, energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
          C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2 := by
  obtain ⟨W, hW, hC⟩ := h
  let i := Submodule.inclusion (p := (w1pVanishingOnSubmodule mu Omega 2 Γ').toSubmodule)
    (p' := (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule)
    (w1pVanishingOnSubmodule_antitone hΓΓ')
  refine ⟨W.map i, ?_, ?_⟩
  · rwa [← Submodule.map_comp, LinearMap.comp_assoc, Submodule.subtype_comp_inclusion]
  · rintro _ ⟨v, hv, rfl⟩
    exact hC v hv

/-- **The mixed eigenvalues grow with the Dirichlet part.** For `Γ ⊆ Γ'`, both missing `Ω`,
`λₖ(Γ) ≤ λₖ(Γ')` for every `k`, under the hypotheses of
`TauCeti.PDE.isLeast_mixedEigenvalue` for `Γ`. Indeed `H¹_{Γ'}(Ω) ⊆ H¹_Γ(Ω)`, so the min–max
principle for `Γ` runs over more subspaces. -/
theorem mixedEigenvalue_le_of_subset [Nonempty ι] (hΓΓ' : Γ ⊆ Γ')
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hrellich : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (hΓ' : Disjoint Γ' Omega)
    (hsymm : ∀ u v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    {theta omega : ℝ} (htheta : 0 < theta)
    (hgarding : ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      theta * ‖(v : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) +
          omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2)
    (hOmega_nonempty : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty) (k : ℕ) :
    mixedEigenvalue mu Omega Γ a b c k ≤ mixedEigenvalue mu Omega Γ' a b c k := by
  have hle := w1pVanishingOnSubmodule_antitone (mu := mu) (Omega := Omega) (p := 2) hΓΓ'
  -- The hypotheses pass from `H¹_Γ(Ω)` to its subspace `H¹_{Γ'}(Ω)`.
  let i : (w1pVanishingOnSubmodule mu Omega 2 Γ').toSubmodule →
      (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule := fun v ↦ ⟨v, hle v.property⟩
  exact csInf_le_csInf
    (isLeast_mixedEigenvalue hcoeff hrellich (hΓ'.mono_left hΓΓ') hsymm htheta hgarding
      hOmega_nonempty k).bddBelow
    (isLeast_mixedEigenvalue hcoeff hrellich hΓ' (fun u v ↦ hsymm (i u) (i v))
      htheta (fun v ↦ hgarding (i v)) hOmega_nonempty k).nonempty
    fun _ hC ↦ mem_setOf_mixedEigenvalue_of_subset hΓΓ' hC

/-! ### The mixed eigenvalues of `-Δ` -/

section Laplacian

variable [DecidableEq ι] [Nonempty ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (hΩ : (Omega : Set (EuclideanSpace ℝ ι)).IsLipschitzDomain E)
  (hb : IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
  (hOmega_nonempty : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty)
include hΩ hb hOmega_nonempty

/-- **The mixed eigenvalues of `-Δ` grow with the Dirichlet part**: on a nonempty bounded
Lipschitz domain `Ω`, for `Γ ⊆ Γ'`, both missing `Ω`, `λₖ(Γ) ≤ λₖ(Γ')` for every `k`. -/
theorem mixedEigenvalue_laplacian_le_of_subset (hΓΓ' : Γ ⊆ Γ') (hΓ' : Disjoint Γ' Omega)
    (k : ℕ) :
    mixedEigenvalue mu Omega Γ (fun _ ↦ 1) 0 0 k ≤ mixedEigenvalue mu Omega Γ' (fun _ ↦ 1) 0 0 k :=
  mixedEigenvalue_le_of_subset hΓΓ' (memLp_energyIntegrand_const_zero_zero 1)
    (W1p.isCompactOperator_valueL_of_isLipschitzDomain hΩ hb) hΓ'
    (fun _ _ ↦ energyFormH1_one_zero_zero_comm _ _) (lt_min one_pos one_pos)
    (fun v ↦ by exact min_mul_norm_sq_le_energyFormH1_one_zero_zero_add 1 (v : W1p mu Omega 2))
    hOmega_nonempty k

/-- **The mixed eigenvalues of `-Δ` lie below the Dirichlet ones**: on a nonempty bounded
Lipschitz domain `Ω` and for a boundary part `Γ ⊆ ∂Ω`, `λₖ(Γ) ≤ λₖ(∂Ω)`, the `k`-th Dirichlet
eigenvalue of `-Δ`. -/
theorem mixedEigenvalue_laplacian_le_dirichletEigenvalue
    (hΓ : Γ ⊆ frontier (Omega : Set (EuclideanSpace ℝ ι))) (k : ℕ) :
    mixedEigenvalue mu Omega Γ (fun _ ↦ 1) 0 0 k ≤
      dirichletEigenvalue mu Omega (fun _ ↦ 1) 0 0 k := by
  rw [← mixedEigenvalue_frontier]
  exact mixedEigenvalue_laplacian_le_of_subset hΩ hb hOmega_nonempty hΓ
    (disjoint_frontier_iff_isOpen.2 Omega.isOpen) k

variable (hΓ : Disjoint Γ Omega)
include hΓ

/-- **The mixed eigenbasis of `-Δ`.** On a nonempty bounded Lipschitz domain `Ω ⊆ ℝⁿ` and for `Γ`
missing `Ω`, for instance `Γ ⊆ ∂Ω`, there is an orthonormal basis `(eₖ)` of `L²(Ω)` such that `eₖ`
is the value of some `uₖ ∈ H¹_Γ(Ω)` with
`∫_Ω ∇uₖ · ∇v = λₖ ∫_Ω uₖ v` for every `v ∈ H¹_Γ(Ω)`, where `λₖ` is the min–max eigenvalue
`TauCeti.PDE.mixedEigenvalue`. -/
theorem exists_hilbertBasis_mixedEigenvalue_laplacian :
    ∃ (basis : HilbertBasis ℕ ℝ (Lp ℝ 2 (mu.restrict Omega)))
      (u : ℕ → (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule),
      (∀ k, W1p.value (u k : W1p mu Omega 2) = basis k) ∧
      ∀ (k : ℕ) (v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule),
        energyFormH1 (fun _ ↦ 1) 0 0 (u k : W1p mu Omega 2) (v : W1p mu Omega 2) =
          mixedEigenvalue mu Omega Γ (fun _ ↦ 1) 0 0 k *
            ⟪W1p.value (u k : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ :=
  exists_hilbertBasis_mixedEigenvalue (memLp_energyIntegrand_const_zero_zero 1)
    (W1p.isCompactOperator_valueL_of_isLipschitzDomain hΩ hb) hΓ
    (fun _ _ ↦ energyFormH1_one_zero_zero_comm _ _) (lt_min one_pos one_pos)
    (fun v ↦ by exact min_mul_norm_sq_le_energyFormH1_one_zero_zero_add 1 (v : W1p mu Omega 2))
    hOmega_nonempty

/-- **The min–max principle for `-Δ` is attained**: `λₖ` is the least `C` for which some subspace
`W` of `H¹_Γ(Ω)`, whose values span a subspace of `L²(Ω)` of dimension at least `k + 1`, satisfies
`∫_Ω |∇v|² ≤ C ∫_Ω v²` for every `v ∈ W`. For `k = 0` this says that `λ₀` is the least Rayleigh
quotient over nonzero `v ∈ H¹_Γ(Ω)`. -/
theorem isLeast_mixedEigenvalue_laplacian (k : ℕ) :
    IsLeast {C : ℝ | ∃ W : Submodule ℝ (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      k + 1 ≤ Module.finrank ℝ
        (W.map ((W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).toLinearMap ∘ₗ
          (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule.subtype)) ∧
        ∀ v ∈ W, energyFormH1 (fun _ ↦ 1) 0 0 (v : W1p mu Omega 2) (v : W1p mu Omega 2) ≤
          C * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2}
      (mixedEigenvalue mu Omega Γ (fun _ ↦ 1) 0 0 k) :=
  isLeast_mixedEigenvalue (memLp_energyIntegrand_const_zero_zero 1)
    (W1p.isCompactOperator_valueL_of_isLipschitzDomain hΩ hb) hΓ
    (fun _ _ ↦ energyFormH1_one_zero_zero_comm _ _) (lt_min one_pos one_pos)
    (fun v ↦ by exact min_mul_norm_sq_le_energyFormH1_one_zero_zero_add 1 (v : W1p mu Omega 2))
    hOmega_nonempty k

/-- **The mixed spectrum of `-Δ`.** On a nonempty bounded Lipschitz domain and for `Γ` missing
`Ω`, the mixed eigenvalues of `-Δ` satisfy `0 ≤ λ₀ ≤ λ₁ ≤ ⋯ → ∞`, and a real number is a
mixed eigenvalue of `-Δ` exactly when it is some `λₖ`. -/
theorem mixedEigenvalue_laplacian_spectrum :
    0 ≤ mixedEigenvalue mu Omega Γ (fun _ ↦ 1) 0 0 0 ∧
      Monotone (mixedEigenvalue mu Omega Γ (fun _ ↦ 1) 0 0) ∧
      Tendsto (mixedEigenvalue mu Omega Γ (fun _ ↦ 1) 0 0) atTop atTop ∧
      ∀ kappa : ℝ, IsMixedEigenvalue mu Omega Γ (fun _ ↦ 1) 0 0 kappa ↔
        ∃ k, mixedEigenvalue mu Omega Γ (fun _ ↦ 1) 0 0 k = kappa := by
  have hcoeff := memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
    (1 : Matrix ι ι ℝ)
  have hsymm (u v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule) :=
    energyFormH1_one_zero_zero_comm (u : W1p mu Omega 2) v
  have hnonneg (v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule) :=
    energyFormH1_one_zero_zero_self_nonneg (v : W1p mu Omega 2)
  have hgarding (v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule) :=
    min_mul_norm_sq_le_energyFormH1_one_zero_zero_add 1 (v : W1p mu Omega 2)
  have htheta : (0 : ℝ) < min 1 1 := lt_min one_pos one_pos
  have hrellich := W1p.isCompactOperator_valueL_of_isLipschitzDomain (mu := mu) (p := 2) hΩ hb
  exact ⟨mixedEigenvalue_nonneg hnonneg 0,
    monotone_mixedEigenvalue hcoeff hrellich hΓ hsymm htheta hgarding hOmega_nonempty,
    tendsto_mixedEigenvalue_atTop hcoeff hrellich hΓ hsymm htheta hgarding
      hOmega_nonempty,
    isMixedEigenvalue_iff_exists_mixedEigenvalue_eq hcoeff hrellich hΓ hsymm htheta
      hgarding hOmega_nonempty⟩

end Laplacian

end PDE

end TauCeti
