/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Galerkin
public import TauCeti.Analysis.PDE.EnergyForm.Restriction

/-!
# The Dirichlet problem along an exhaustion of the domain

Let `L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` be a divergence-form operator on an open set `Ω ⊆ ℝⁿ`
whose energy form is bounded and coercive on `H¹₀(Ω)`, and let the open sets `U k ⊆ Ω` exhaust
`Ω`: they increase with `k` along a directed index set and their union is `Ω`. Coercivity passes
to every `U k` (`TauCeti.PDE.isCoercive_energyFormH1L0_of_domain_le`), so the Dirichlet problem
`L u = f` in `U k`, `u = 0` on `∂U k`, has a unique weak solution `u k ∈ H¹₀(U k)`. This file
proves that the zero extensions of the `u k` converge in `H¹₀(Ω)` to the weak solution `u` of the
Dirichlet problem on `Ω`, both for a forcing `ℓ ∈ H⁻¹(Ω)`
(`TauCeti.PDE.tendsto_extendByZeroL_of_forall_energyFormH1_eq`) and for an `L²` right-hand side
(`TauCeti.PDE.tendsto_extendByZeroL_of_isWeakSolutionDirichlet`). No boundedness or boundary
regularity of `Ω` or of the `U k` is assumed. For instance the balls `B(0, k)` exhaust `ℝⁿ`, so
solutions of `-Δu + u = f` on `ℝⁿ` are limits of solutions of the same equation on balls with
zero boundary values. Taking for the right-hand sides on `U k` the restrictions of one
`f ∈ L²(Ω)`, the theorem says that the solution operators of the Dirichlet problems on the `U k`,
extended by zero, converge strongly to the solution operator on `Ω`; for `L + λ` these are the
resolvents of the Dirichlet realizations of `L`.

## The argument

Zero extension is an isometry `H¹₀(U k) → H¹₀(Ω)` that preserves the energy form
(`TauCeti.PDE.energyFormH1_extendByZeroL`) and the forcing functional
(`TauCeti.PDE.dirichletForcing_extendByZeroL`). So the zero extension of `u k` is the Galerkin
approximation of `u` in the subspace of zero extensions of `H¹₀(U k)`. These subspaces increase
with `k`, and their union is dense in `H¹₀(Ω)` (`TauCeti.W1p0.dense_iUnion_range_extendByZeroL`),
since every test function on `Ω` is supported in some `U k`. Céa's lemma then gives convergence
(`IsCoercive.tendsto_of_forall_apply_sub_eq_zero`).

## Main declarations

* `TauCeti.PDE.tendsto_extendByZeroL_of_forall_energyFormH1_eq`: convergence along an exhaustion
  for a forcing in `H⁻¹(Ω)`.
* `TauCeti.PDE.tendsto_extendByZeroL_of_isWeakSolutionDirichlet`: the same for weak solutions
  with an `L²` right-hand side.

## References

* J. Céa, *Approximation variationnelle des problèmes aux limites*, Ann. Inst. Fourier
  (Grenoble) **14** (1964), 345–444 (Galerkin approximation by subspaces with dense union).
* T. Kato, *Perturbation Theory for Linear Operators*, Springer, 1966, Chapter VIII, §3, and
  B. Simon, *A canonical decomposition for quadratic forms with applications to monotone
  convergence theorems*, J. Funct. Anal. **28** (1978), 377–385: for symmetric forms, the
  monotone convergence theorems for forms, of which this is the case of increasing domains.
-/

public section

open Filter MeasureTheory Set Topology TopologicalSpace

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ}
  {α : Type*} [Preorder α] [IsDirected α (· ≤ ·)] {U : α → Opens (EuclideanSpace ℝ ι)}

/-- Every `u ∈ H¹₀(Ω)` is approximated by zero extensions from `U k`, for all large `k`: it is
close to a zero extension from some `U k`, which is also one from every later `U j`. -/
private theorem eventually_exists_norm_sub_extendByZeroL_lt [Nonempty α] (hU : ∀ k, U k ≤ Omega)
    (hmono : Monotone U) (hcover : Omega ≤ ⨆ k, U k) (u : W1p0 mu Omega 2) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ j in atTop, ∃ z, ‖u - W1p0.extendByZeroL (hU j) z‖ < ε := by
  obtain ⟨y, hy, hdist⟩ :=
    (W1p0.dense_iUnion_range_extendByZeroL (mu := mu) (p := 2) hU hmono.directed_le
      hcover).exists_dist_lt u hε
  obtain ⟨k, v, rfl⟩ := mem_iUnion.1 hy
  filter_upwards [eventually_ge_atTop k] with j hj
  refine ⟨W1p0.extendByZeroL (hmono hj) v, ?_⟩
  rwa [W1p0.extendByZeroL_extendByZeroL, ← dist_eq_norm]

/-- **Galerkin orthogonality.** If `u` solves the problem on `Ω` and `u'` solves it on `U ⊆ Ω`
against zero extensions, then `u` minus the zero extension of `u'` is energy-orthogonal to every
zero extension from `U`. -/
private theorem energyFormH1L0_sub_extendByZeroL_eq_zero {V : Opens (EuclideanSpace ℝ ι)}
    (hV : V ≤ Omega)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    {ℓ : StrongDual ℝ (W1p0 mu Omega 2)} {u : W1p0 mu Omega 2} {u' : W1p0 mu V 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c (u : W1p mu Omega 2) v = ℓ v)
    (hu' : ∀ v : W1p0 mu V 2,
      energyFormH1 a b c (u' : W1p mu V 2) v = ℓ (W1p0.extendByZeroL hV v))
    (v : W1p0 mu V 2) :
    energyFormH1L0 hcoeff (u - W1p0.extendByZeroL hV u') (W1p0.extendByZeroL hV v) = 0 := by
  rw [energyFormH1L0_apply hcoeff, Submodule.coe_sub, energyFormH1_sub_left hcoeff, hu,
    energyFormH1_extendByZeroL a b c hV]
  exact sub_eq_zero.2 (hu' v).symm

/-- **The Dirichlet problem along an exhaustion, with a forcing in `H⁻¹(Ω)`.** Let the open sets
`U k ⊆ Ω` increase with `k` and cover `Ω`, let the energy form on `H¹₀(Ω)` be bounded and
coercive, and let `ℓ` be a continuous linear functional on `H¹₀(Ω)`. If `u ∈ H¹₀(Ω)` solves
`a(u, v) = ℓ(v)` for every `v ∈ H¹₀(Ω)`, and each `u' k ∈ H¹₀(U k)` solves `a(u' k, v) = ℓ(v₀)`
for every `v ∈ H¹₀(U k)` with zero extension `v₀`, then the zero extensions of the `u' k` tend to
`u` in `H¹₀(Ω)`. -/
theorem tendsto_extendByZeroL_of_forall_energyFormH1_eq (hU : ∀ k, U k ≤ Omega)
    (hmono : Monotone U) (hcover : Omega ≤ ⨆ k, U k)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) {ℓ : StrongDual ℝ (W1p0 mu Omega 2)}
    {u : W1p0 mu Omega 2} {u' : (k : α) → W1p0 mu (U k) 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c (u : W1p mu Omega 2) v = ℓ v)
    (hu' : ∀ k (v : W1p0 mu (U k) 2),
      energyFormH1 a b c (u' k : W1p mu (U k) 2) v = ℓ (W1p0.extendByZeroL (hU k) v)) :
    Tendsto (fun k => W1p0.extendByZeroL (hU k) (u' k)) atTop (𝓝 u) := by
  cases isEmpty_or_nonempty α
  · exact tendsto_of_isEmpty
  -- The zero extension of `u' k` is the Galerkin approximation of `u` in the zero extensions
  -- from `U k`; the orthogonality is read through the coercion of `W1p0.extendByZeroL (hU k)` to
  -- a linear map, which agrees with it by definition (`ContinuousLinearMap.coe_coe`).
  exact hcoercive.tendsto_of_forall_apply_sub_eq_zero
    (fun k => (W1p0.extendByZeroL (hU k)).toLinearMap)
    (fun k => energyFormH1L0_sub_extendByZeroL_eq_zero (hU k) hcoeff hu (hu' k))
    fun _ hε => eventually_exists_norm_sub_extendByZeroL_lt hU hmono hcover u hε

/-- **The Dirichlet problem along an exhaustion.** Let the open sets `U k ⊆ Ω` increase with `k`
and cover `Ω`, and let the energy form on `H¹₀(Ω)` be bounded and coercive. Let `u ∈ H¹₀(Ω)` be a
weak solution of `L u = f` in `Ω` with `f ∈ L²(Ω)`, and let each `u' k ∈ H¹₀(U k)` be a weak
solution of `L (u' k) = f' k` in `U k`, where `f' k ∈ L²(U k)` agrees with `f` on `U k`. Then the
zero extensions of the `u' k` tend to `u` in `H¹₀(Ω)`. The weak solutions on `U k` exist and are
unique, since coercivity passes to smaller domains
(`TauCeti.PDE.isCoercive_energyFormH1L0_of_domain_le`). -/
theorem tendsto_extendByZeroL_of_isWeakSolutionDirichlet (hU : ∀ k, U k ≤ Omega)
    (hmono : Monotone U) (hcover : Omega ≤ ⨆ k, U k)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) {f : Lp ℝ 2 (mu.restrict Omega)}
    {f' : (k : α) → Lp ℝ 2 (mu.restrict (U k))} (hf' : ∀ k, ⇑(f' k) =ᵐ[mu.restrict (U k)] ⇑f)
    {u : W1p0 mu Omega 2} {u' : (k : α) → W1p0 mu (U k) 2}
    (hu : IsWeakSolutionDirichlet a b c f u)
    (hu' : ∀ k, IsWeakSolutionDirichlet a b c (f' k) (u' k)) :
    Tendsto (fun k => W1p0.extendByZeroL (hU k) (u' k)) atTop (𝓝 u) :=
  tendsto_extendByZeroL_of_forall_energyFormH1_eq hU hmono hcover hcoeff hcoercive
    hu.energyFormH1_eq_dirichletForcing fun k v =>
      ((hu' k).energyFormH1_eq_dirichletForcing v).trans
        (dirichletForcing_extendByZeroL (hU k) (hf' k) v).symm

end PDE

end TauCeti
