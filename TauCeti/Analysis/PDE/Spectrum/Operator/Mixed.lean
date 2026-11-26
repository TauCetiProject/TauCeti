/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Variational.FormOperator
public import TauCeti.Analysis.PDE.MixedProblem
public import TauCeti.Analysis.PDE.Spectrum.Operator.Basic

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
  (`TauCeti.PDE.mem_spectrum_mixedOperator_iff`).

For `-Δ`, with energy form `∫_Ω ∇u · ∇v`, the Gårding inequality holds with `θ = ω = 1` and every
hypothesis but the Rellich property holds outright: the mixed Laplacian `-Δ_Γ` is self-adjoint and
nonnegative, every negative number is a resolvent point, and on a domain with the Rellich property
it has compact resolvent and spectrum its mixed eigenvalues, all nonnegative.

## Main declarations

* `TauCeti.PDE.mixedOperator`: the mixed realization, with
  `TauCeti.PDE.mem_graph_mixedOperator_iff`, `TauCeti.PDE.mem_domain_mixedOperator_iff`,
  `TauCeti.PDE.value_mem_domain_mixedOperator`, `TauCeti.PDE.energyFormH1_eq_inner_mixedOperator`,
  `TauCeti.PDE.mixedOperator_apply_eq` and
  `TauCeti.PDE.exists_mixedOperator_apply_eq_smul_iff` (its eigenvectors).
* `TauCeti.PDE.mixedForm`, `TauCeti.PDE.isCoercive_mixedForm` and
  `TauCeti.PDE.mixedOperator_eq_formOperator`: the shifted energy form on `H¹_Γ(Ω)`, coercive
  under a Gårding inequality, whose form operator is the mixed realization.
* `TauCeti.PDE.mixedSolutionOperator`, `TauCeti.PDE.mixedSolutionOperator_apply_eq` and
  `TauCeti.PDE.resolvent_mixedOperator_neg`: the solution operator of the shifted mixed problem,
  which returns the weak solution, and is the resolvent at `-ω` up to sign; its spectral
  interface `TauCeti.PDE.hasEigenvalue_mixedSolutionOperator_iff` (eigenvalue `(κ + ω)⁻¹` for each
  mixed eigenvalue `κ`), `TauCeti.PDE.isCompactOperator_mixedSolutionOperator`,
  `TauCeti.PDE.isSymmetric_mixedSolutionOperator`,
  `TauCeti.PDE.inner_mixedSolutionOperator_self_nonneg` and
  `TauCeti.PDE.mixedSolutionOperator_injective`.
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
  `TauCeti.PDE.mem_domain_mixedOperator_laplacian_iff` and
  `TauCeti.PDE.value_mem_domain_mixedOperator_laplacian`: the mixed Laplacian `-Δ_Γ`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 9.31 (the Dirichlet case) and Proposition 9.24 (the Neumann problem).
* T. Kato, *Perturbation Theory for Linear Operators*, Chapter VI, §2 (the representation
  theorem for closed semibounded forms).
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Bornology MeasureTheory Set TopologicalSpace
open scoped InnerProductSpace

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

private theorem mixedForm_zero_apply
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (u v : W1pVanishingOn mu Omega 2 Γ) :
    mixedForm hcoeff Γ 0 u v = energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) := by
  rw [mixedForm_apply, zero_mul, add_zero]

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

end Laplacian

end PDE

end TauCeti
