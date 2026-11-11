/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Inverse
public import TauCeti.Analysis.PDE.ClassicalSolution
public import TauCeti.Analysis.PDE.Spectrum.Sequence
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# The Dirichlet realization of an elliptic operator on `L²(Ω)`

Let `L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` be a divergence-form operator on an open set
`Ω ⊆ ℝⁿ` whose energy form `a(·, ·)` is coercive on `H¹₀(Ω)`. The **Dirichlet realization** of
`L` is the unbounded operator `A` on `L²(Ω)` with

`D(A) = {u ∈ H¹₀(Ω) : L u ∈ L²(Ω)}`, `A u = L u`,

where `L u = g ∈ L²(Ω)` is meant weakly: `a(u, v) = ⟪g, v⟫_{L²(Ω)}` for every `v ∈ H¹₀(Ω)`
(`TauCeti.PDE.mem_graph_dirichletOperator_iff`). It is the inverse of the Dirichlet solution
operator `S = TauCeti.PDE.dirichletSolutionOperator`, which is injective because the value map
`H¹₀(Ω) → L²(Ω)` has dense range, and that is how it is constructed here
(`TauCeti.PDE.dirichletOperator`). The operator theory of `A` then comes from the bounded
operator `S`:

* `A` is self-adjoint when the energy form is symmetric, for instance for `-Δ`
  (`TauCeti.PDE.isSelfAdjoint_dirichletOperator`);
* `0` is a resolvent point of `A`, with resolvent `-S`;
* on a bounded domain `A` has compact resolvent, and its spectrum is exactly the set of
  Dirichlet eigenvalues (`TauCeti.PDE.mem_spectrum_dirichletOperator_iff`); off the spectrum the
  resolvent `(κ I - A)⁻¹ f` is the solution of the shifted Dirichlet problem `L u - κ u = -f`.

For `-Δ` the weak condition is the distributional one: `u ∈ H¹₀(Ω)` lies in the domain exactly
when its distributional Laplacian is an `L²(Ω)` function
(`TauCeti.PDE.mem_domain_dirichletOperator_laplacian_iff`), so `D(A) = {u ∈ H¹₀(Ω) : Δu ∈ L²}`.
No regularity of `∂Ω` is used: the boundary condition is membership in `H¹₀(Ω)`.

## Main declarations

* `TauCeti.PDE.dirichletOperator`: the Dirichlet realization of `L` as a partial linear map on
  `L²(Ω)`, with its graph and domain characterized by
  `TauCeti.PDE.mem_graph_dirichletOperator_iff` and
  `TauCeti.PDE.mem_domain_dirichletOperator_iff`.
* `TauCeti.PDE.isSelfAdjoint_dirichletOperator`: self-adjointness for a symmetric energy form.
* `TauCeti.PDE.mem_spectrum_dirichletOperator_iff` and
  `TauCeti.PDE.hasCompactResolvent_dirichletOperator`: the spectrum and compactness of the
  resolvent on a bounded domain.
* `TauCeti.PDE.exists_value_eq_resolvent_dirichletOperator`: the resolvent solves the shifted
  Dirichlet problem.
* `TauCeti.PDE.mem_graph_dirichletOperator_laplacian_iff` and
  `TauCeti.PDE.mem_domain_dirichletOperator_laplacian_iff`: for `-Δ`, the graph and domain
  through distributional Laplacians.
* `TauCeti.PDE.exists_spectrum_dirichletOperator_laplacian_eq_range`: on a nonempty bounded
  domain the Dirichlet Laplacian is self-adjoint with spectrum `{λ₀ ≤ λ₁ ≤ ⋯ → ∞}`.

## References

* L. C. Evans, *Partial Differential Equations*, Section 6.5.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Section 9.8.
* D. Gilbarg and N. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 8.12.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Bornology InnerProductSpace Laplacian MeasureTheory Module.End TopologicalSpace
open scoped Distributions InnerProductSpace

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)}

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

section Operator

variable {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ}
  (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
  (hcoercive : IsCoercive (energyFormH1L0 hcoeff))

/-- **The Dirichlet realization** of the divergence-form operator
`L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` on `L²(Ω)`: the unbounded operator with domain
`{u ∈ H¹₀(Ω) : L u ∈ L²(Ω)}` acting by `L`, defined as the inverse of the Dirichlet solution
operator. Its graph is described by `TauCeti.PDE.mem_graph_dirichletOperator_iff`. -/
def dirichletOperator : Lp ℝ 2 (mu.restrict Omega) →ₗ.[ℝ] Lp ℝ 2 (mu.restrict Omega) :=
  ((dirichletSolutionOperator hcoeff hcoercive : Lp ℝ 2 (mu.restrict Omega) →ₗ[ℝ]
    Lp ℝ 2 (mu.restrict Omega)).toPMap ⊤).inverse

/-- **The graph of the Dirichlet realization.** `(f, g)` lies on the graph of `A` exactly when
`f` is the value of some `u ∈ H¹₀(Ω)` solving `L u = g` weakly. -/
theorem mem_graph_dirichletOperator_iff {f g : Lp ℝ 2 (mu.restrict Omega)} :
    (f, g) ∈ (dirichletOperator hcoeff hcoercive).graph ↔
      ∃ u : W1p0 mu Omega 2, W1p.value (u : W1p mu Omega 2) = f ∧
        IsWeakSolutionDirichlet a b c g u := by
  -- `delta` rather than `rw`, which would generate an equation lemma whose statement is slow to
  -- type-check at default transparency.
  delta dirichletOperator
  rw [ContinuousLinearMap.mem_graph_inverse_toPMap_top_iff
    (injective_dirichletSolutionOperator hcoeff hcoercive), dirichletSolutionOperator_apply]
  constructor
  · intro h
    exact ⟨_, h, isWeakSolutionDirichlet_weakSolutionDirichlet hcoeff hcoercive g⟩
  · rintro ⟨u, rfl, hu⟩
    rw [← eq_weakSolutionDirichlet hcoeff hcoercive hu]

/-- **The domain of the Dirichlet realization** is `{u ∈ H¹₀(Ω) : L u ∈ L²(Ω)}`: the values of
those `u ∈ H¹₀(Ω)` that solve `L u = g` weakly for some `g ∈ L²(Ω)`. -/
theorem mem_domain_dirichletOperator_iff {f : Lp ℝ 2 (mu.restrict Omega)} :
    f ∈ (dirichletOperator hcoeff hcoercive).domain ↔
      ∃ u : W1p0 mu Omega 2, W1p.value (u : W1p mu Omega 2) = f ∧
        ∃ g : Lp ℝ 2 (mu.restrict Omega), IsWeakSolutionDirichlet a b c g u := by
  constructor
  · intro hf
    obtain ⟨u, hu, hsol⟩ := (mem_graph_dirichletOperator_iff hcoeff hcoercive).1
      ((dirichletOperator hcoeff hcoercive).mem_graph ⟨f, hf⟩)
    exact ⟨u, hu, _, hsol⟩
  · rintro ⟨u, hu, g, hsol⟩
    exact LinearPMap.mem_domain_of_mem_graph
      ((mem_graph_dirichletOperator_iff hcoeff hcoercive).2 ⟨u, hu, hsol⟩)

/-- The value of the Dirichlet realization: `A f = g` exactly when `f` is the value of some
`u ∈ H¹₀(Ω)` solving `L u = g` weakly. -/
theorem dirichletOperator_apply_eq_iff (f : (dirichletOperator hcoeff hcoercive).domain)
    (g : Lp ℝ 2 (mu.restrict Omega)) :
    dirichletOperator hcoeff hcoercive f = g ↔
      ∃ u : W1p0 mu Omega 2, W1p.value (u : W1p mu Omega 2) = f ∧
        IsWeakSolutionDirichlet a b c g u := by
  rw [← mem_graph_dirichletOperator_iff hcoeff hcoercive, LinearPMap.mem_graph_iff]
  constructor
  · rintro rfl
    exact ⟨f, rfl, rfl⟩
  · rintro ⟨f', hf', h⟩
    exact (congrArg _ (Subtype.ext hf'.symm)).trans h

/-- Every value of the Dirichlet solution operator lies in the domain of the Dirichlet
realization. -/
theorem dirichletSolutionOperator_mem_domain_dirichletOperator (g : Lp ℝ 2 (mu.restrict Omega)) :
    dirichletSolutionOperator hcoeff hcoercive g ∈ (dirichletOperator hcoeff hcoercive).domain :=
  ContinuousLinearMap.apply_mem_domain_inverse_toPMap_top g

/-- The Dirichlet realization inverts the solution operator: `A (S g) = g`. -/
theorem dirichletOperator_dirichletSolutionOperator (g : Lp ℝ 2 (mu.restrict Omega))
    (hg : dirichletSolutionOperator hcoeff hcoercive g ∈
      (dirichletOperator hcoeff hcoercive).domain) :
    dirichletOperator hcoeff hcoercive ⟨_, hg⟩ = g :=
  ContinuousLinearMap.inverse_toPMap_top_apply
    (injective_dirichletSolutionOperator hcoeff hcoercive) g hg

/-- The solution operator inverts the Dirichlet realization: `S (A f) = f`. -/
theorem dirichletSolutionOperator_dirichletOperator
    (f : (dirichletOperator hcoeff hcoercive).domain) :
    dirichletSolutionOperator hcoeff hcoercive (dirichletOperator hcoeff hcoercive f) = f :=
  (ContinuousLinearMap.inverse_toPMap_top_apply_eq_iff
    (injective_dirichletSolutionOperator hcoeff hcoercive) f _).1 rfl

/-- **The Dirichlet realization of a symmetric operator is self-adjoint.** With no drift and an
almost everywhere symmetric principal coefficient, the symmetry hypothesis is supplied by
`TauCeti.PDE.energyFormH1_comm_of_isSymm_ae`. -/
theorem isSelfAdjoint_dirichletOperator
    (hsymm : ∀ u v : W1p0 mu Omega 2,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2)) :
    IsSelfAdjoint (dirichletOperator hcoeff hcoercive) :=
  ContinuousLinearMap.isSelfAdjoint_inverse_toPMap_top
    (isSymmetric_dirichletSolutionOperator hcoeff hcoercive hsymm)
    (injective_dirichletSolutionOperator hcoeff hcoercive)

/-- `0` lies in the resolvent set of the Dirichlet realization. -/
theorem zero_mem_resolventSet_dirichletOperator :
    (0 : ℝ) ∈ (dirichletOperator hcoeff hcoercive).resolventSet :=
  ContinuousLinearMap.zero_mem_resolventSet_inverse_toPMap_top
    (injective_dirichletSolutionOperator hcoeff hcoercive)

/-- The resolvent of the Dirichlet realization at `0` is minus the solution operator:
`(0 • I - A)⁻¹ = -S`. -/
theorem resolvent_dirichletOperator_zero :
    (dirichletOperator hcoeff hcoercive).resolvent 0 =
      -dirichletSolutionOperator hcoeff hcoercive :=
  ContinuousLinearMap.resolvent_inverse_toPMap_top_zero
    (injective_dirichletSolutionOperator hcoeff hcoercive)

/-- **The resolvent solves the shifted Dirichlet problem.** At a resolvent point `κ` of the
Dirichlet realization, `(κ I - A)⁻¹ f` is the value of some `u ∈ H¹₀(Ω)` solving
`L u - κ u = -f` weakly. -/
theorem exists_value_eq_resolvent_dirichletOperator {κ : ℝ}
    (hκ : κ ∈ (dirichletOperator hcoeff hcoercive).resolventSet)
    (f : Lp ℝ 2 (mu.restrict Omega)) :
    ∃ u : W1p0 mu Omega 2,
      W1p.value (u : W1p mu Omega 2) = (dirichletOperator hcoeff hcoercive).resolvent κ f ∧
        IsWeakSolutionDirichletMassShift a b c κ (-f) u := by
  set A := dirichletOperator hcoeff hcoercive
  set w : A.domain := ⟨_, LinearPMap.resolvent_mem_domain hκ f⟩
  -- `(κ I - A) w = f`, so `A w = κ w - f`.
  have hAw : A w = κ • (w : Lp ℝ 2 (mu.restrict Omega)) - f := by
    rw [← LinearPMap.smul_sub_apply_resolvent hκ f, sub_sub_cancel]
  obtain ⟨u, hu, hsol⟩ := (dirichletOperator_apply_eq_iff hcoeff hcoercive w _).1 hAw
  refine ⟨u, hu, (isWeakSolutionDirichletMassShift_iff κ (-f) u).2 fun v ↦ ?_⟩
  rw [← dirichletForcing_apply_eq_setIntegral, hsol.energyFormH1_eq_dirichletForcing v,
    dirichletForcing_apply, dirichletForcing_apply, hu, inner_sub_left, real_inner_smul_left,
    inner_neg_left]
  ring

/-- **The spectrum of the Dirichlet realization** on a bounded domain is exactly the set of
Dirichlet eigenvalues. No symmetry of the energy form is needed. -/
theorem mem_spectrum_dirichletOperator_iff (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
    {κ : ℝ} :
    κ ∈ (dirichletOperator hcoeff hcoercive).spectrum ↔ IsDirichletEigenvalue mu Omega a b c κ := by
  delta dirichletOperator
  rw [ContinuousLinearMap.mem_spectrum_inverse_toPMap_top_iff
    (injective_dirichletSolutionOperator hcoeff hcoercive)]
  constructor
  · rintro ⟨hκ, hmem⟩
    rw [isDirichletEigenvalue_iff_hasEigenvalue hcoeff hcoercive hκ]
    exact ((isCompactOperator_dirichletSolutionOperator hcoeff hcoercive hOmega)
      |>.hasEigenvalue_iff_mem_spectrum (inv_ne_zero hκ)).2 hmem
  · intro h
    have hκ := (pos_of_isDirichletEigenvalue hcoeff hcoercive h).ne'
    refine ⟨hκ, ((isCompactOperator_dirichletSolutionOperator hcoeff hcoercive hOmega)
      |>.hasEigenvalue_iff_mem_spectrum (inv_ne_zero hκ)).1 ?_⟩
    exact (isDirichletEigenvalue_iff_hasEigenvalue hcoeff hcoercive hκ).1 h

/-- On a bounded domain the Dirichlet realization has compact resolvent, by
Rellich--Kondrachov. -/
theorem hasCompactResolvent_dirichletOperator
    (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ ι))) :
    (dirichletOperator hcoeff hcoercive).HasCompactResolvent :=
  ContinuousLinearMap.hasCompactResolvent_inverse_toPMap_top
    (injective_dirichletSolutionOperator hcoeff hcoercive)
    (isCompactOperator_dirichletSolutionOperator hcoeff hcoercive hOmega)

end Operator

/-! ### The Dirichlet Laplacian -/

section Laplacian

variable [DecidableEq ι]
  (hcoeff : MemLp (fun x ↦ energyIntegrand ((fun _ ↦ (1 : Matrix ι ι ℝ)) x)
    ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x) ((0 : EuclideanSpace ℝ ι → ℝ) x)) ⊤
    (mu.restrict Omega))
  (hcoercive : IsCoercive (energyFormH1L0 hcoeff))

/-- **The graph of the Dirichlet Laplacian.** For `-Δ`, `(f, g)` lies on the graph of the
Dirichlet realization exactly when `f` is the value of some `u ∈ H¹₀(Ω)` and `-Δf = g` in the
sense of distributions on `Ω`. -/
theorem mem_graph_dirichletOperator_laplacian_iff {f g : Lp ℝ 2 (mu.restrict Omega)} :
    (f, g) ∈ (dirichletOperator hcoeff hcoercive).graph ↔
      (∃ u : W1p0 mu Omega 2, W1p.value (u : W1p mu Omega 2) = f) ∧
        ∀ φ : 𝓓(Omega, ℝ), -∫ x in Omega, Δ (φ : EuclideanSpace ℝ ι → ℝ) x * f x ∂mu =
          ∫ x in Omega, g x * φ x ∂mu := by
  -- The integral of `Δφ • f` over the whole space only sees `Ω`, which carries `Δφ`.
  have hset (φ : 𝓓(Omega, ℝ)) : ∫ x, Δ (φ : EuclideanSpace ℝ ι → ℝ) x • f x ∂mu =
      ∫ x in Omega, Δ (φ : EuclideanSpace ℝ ι → ℝ) x * f x ∂mu :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [image_eq_zero_of_notMem_tsupport fun h' ↦
        hx (φ.tsupport_subset (tsupport_laplacian_subset _ h')), zero_smul]).symm
  rw [mem_graph_dirichletOperator_iff]
  constructor
  · rintro ⟨u, rfl, hu⟩
    refine ⟨⟨u, rfl⟩, fun φ ↦ ?_⟩
    rw [← hset, ← energyFormH1_one_zero_zero_ofTestFunctionₗ]
    exact hu.energyFormH1_ofTestFunctionₗ φ
  · rintro ⟨⟨u, rfl⟩, h⟩
    refine ⟨u, rfl, (isWeakSolutionDirichlet_iff_forall_testFunction hcoeff g u).2 fun φ ↦ ?_⟩
    rw [energyFormH1_one_zero_zero_ofTestFunctionₗ, hset]
    exact h φ

/-- **The domain of the Dirichlet Laplacian** is `{u ∈ H¹₀(Ω) : Δu ∈ L²(Ω)}`: the values of
`H¹₀(Ω)` whose distributional Laplacian on `Ω` is an `L²(Ω)` function. -/
theorem mem_domain_dirichletOperator_laplacian_iff {f : Lp ℝ 2 (mu.restrict Omega)} :
    f ∈ (dirichletOperator hcoeff hcoercive).domain ↔
      (∃ u : W1p0 mu Omega 2, W1p.value (u : W1p mu Omega 2) = f) ∧
        ∃ g : Lp ℝ 2 (mu.restrict Omega), ∀ φ : 𝓓(Omega, ℝ),
          ∫ x in Omega, Δ (φ : EuclideanSpace ℝ ι → ℝ) x * f x ∂mu =
            ∫ x in Omega, g x * φ x ∂mu := by
  constructor
  · intro hf
    obtain ⟨hu, h⟩ := (mem_graph_dirichletOperator_laplacian_iff hcoeff hcoercive).1
      ((dirichletOperator hcoeff hcoercive).mem_graph ⟨f, hf⟩)
    refine ⟨hu, -dirichletOperator hcoeff hcoercive ⟨f, hf⟩, fun φ ↦ ?_⟩
    rw [← neg_neg (∫ x in Omega, _ ∂mu), h φ, ← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_neg (dirichletOperator hcoeff hcoercive ⟨f, hf⟩)] with x hx
    rw [hx, Pi.neg_apply, neg_mul]
  · rintro ⟨hu, g, h⟩
    refine LinearPMap.mem_domain_of_mem_graph (y := -g)
      ((mem_graph_dirichletOperator_laplacian_iff hcoeff hcoercive).2 ⟨hu, fun φ ↦ ?_⟩)
    rw [h φ, ← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_neg g] with x hx
    rw [hx, Pi.neg_apply, neg_mul]

/-- **The spectrum of the Dirichlet Laplacian.** On a nonempty bounded open set `Ω ⊆ ℝ^{n+1}`
the Dirichlet realization of `-Δ` is a self-adjoint operator on `L²(Ω)` whose spectrum is the
range of the sequence of Dirichlet eigenvalues `0 < λ₀ ≤ λ₁ ≤ ⋯ → ∞`, repeated according to
multiplicity as in `TauCeti.PDE.exists_hilbertBasis_nat_isDirichletEigenvalue_laplacian_monotone`.
-/
theorem exists_spectrum_dirichletOperator_laplacian_eq_range {n : ℕ}
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hOmega_nonempty : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))).Nonempty)
    (hcoeff : MemLp (fun x ↦ energyIntegrand
      ((fun _ ↦ (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) x)
      ((0 : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) x)
      ((0 : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)) ⊤
      (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) :
    IsSelfAdjoint (dirichletOperator hcoeff hcoercive) ∧
      ∃ kappa : ℕ → ℝ, 0 < kappa 0 ∧ Monotone kappa ∧ Filter.Tendsto kappa Filter.atTop
        Filter.atTop ∧ (dirichletOperator hcoeff hcoercive).spectrum = Set.range kappa := by
  refine ⟨isSelfAdjoint_dirichletOperator hcoeff hcoercive
    fun u v ↦ energyFormH1_comm_of_isSymm_ae (ae_of_all _ fun _ ↦ Matrix.isSymm_one) _ _, ?_⟩
  refine (exists_hilbertBasis_nat_isDirichletEigenvalue_laplacian_monotone hOmega
    hOmega_nonempty).elim fun _ h ↦ h.elim fun kappa h ↦ h.elim fun _ h ↦
      ⟨kappa, h.1, h.2.1, h.2.2.1, Set.ext fun κ ↦ ?_⟩
  rw [mem_spectrum_dirichletOperator_iff hcoeff hcoercive hOmega, Set.mem_range]
  exact h.2.2.2.2.2.2 κ

end Laplacian

end PDE

end TauCeti
