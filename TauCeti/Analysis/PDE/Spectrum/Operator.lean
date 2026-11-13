/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Inverse
public import TauCeti.Analysis.PDE.Spectrum.Sequence
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import TauCeti.Analysis.PDE.WeakLaplacian

/-!
# The Dirichlet realization of a divergence-form operator

Let `L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` be a divergence-form operator on an open set `Ω ⊆ ℝⁿ` whose
energy form `a` is bounded and coercive on `H¹₀(Ω)`. This file realizes `L` with the Dirichlet
boundary condition as an unbounded operator on `L²(Ω)`, the partial linear map
`TauCeti.PDE.dirichletOperator`. Its domain consists of the `u ∈ H¹₀(Ω)` with `L u ∈ L²(Ω)` in the
weak sense, and it sends `u` to `L u`: `(u, f)` lies on its graph exactly when

`a(u, v) = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`,

that is, when `u` is the weak solution of the Dirichlet problem `L u = f` in `Ω`, `u = 0` on `∂Ω`
(`TauCeti.PDE.mem_graph_dirichletOperator_iff`). For `L = -Δ` the weak condition is the
distributional one, so the domain is `{u ∈ H¹₀(Ω) : Δu ∈ L²(Ω)}`, the values of `H¹₀(Ω)` whose
distributional Laplacian on `Ω` is an `L²(Ω)` function
(`TauCeti.PDE.mem_domain_dirichletOperator_laplacian_iff`). The boundary condition is
membership in `H¹₀(Ω)`, so no regularity of `∂Ω` enters.

By coercivity the Dirichlet problem is uniquely solvable, and the realization is defined as the
inverse of the injective solution operator `S = TauCeti.PDE.dirichletSolutionOperator`. Its
operator theory follows from that of `S`
(`TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Inverse`,
`TauCeti.Analysis.InnerProductSpace.LinearPMap.Inverse`):

* `0` is a resolvent point with `R(0) = -S`, and on a bounded domain the resolvent is compact
  (`TauCeti.PDE.hasCompactResolvent_dirichletOperator`);
* on a bounded domain the spectrum is exactly the set of Dirichlet eigenvalues
  (`TauCeti.PDE.spectrum_dirichletOperator`), and at every resolvent point `κ` the resolvent
  sends `f` to `-u`, where `u` is a weak solution of `L u - κ u = f`
  (`TauCeti.PDE.resolvent_dirichletOperator_apply`);
* for a symmetric energy form, for instance with no drift and an almost everywhere symmetric
  principal coefficient, the realization is self-adjoint
  (`TauCeti.PDE.isSelfAdjoint_dirichletOperator`).

For `-Δ` on a nonempty bounded open subset of `ℝ^{n+1}` this is the self-adjoint Dirichlet
Laplacian with compact resolvent, whose spectrum is the nondecreasing sequence of Dirichlet
eigenvalues `0 < λ₀ ≤ λ₁ ≤ ⋯ → ∞` and which is diagonal in an orthonormal basis of `L²(Ω)`
(`TauCeti.PDE.exists_isSelfAdjoint_dirichletOperator_laplacian`). In the generator convention
`A = Δ`, the operator `A = -L` has spectrum `{-λₖ}`, and its resolvent at `λ` is `-R(-λ)`.

## Main declarations

* `TauCeti.PDE.dirichletOperator`: the Dirichlet realization, with
  `TauCeti.PDE.mem_graph_dirichletOperator_iff`, `TauCeti.PDE.mem_domain_dirichletOperator_iff`,
  `TauCeti.PDE.isWeakSolutionDirichlet_dirichletOperator` and
  `TauCeti.PDE.dirichletOperator_apply_eq_of_isWeakSolutionDirichlet`.
* `TauCeti.PDE.isSelfAdjoint_dirichletOperator`: self-adjointness for a symmetric energy form.
* `TauCeti.PDE.spectrum_dirichletOperator`: the spectrum is the Dirichlet spectrum.
* `TauCeti.PDE.resolvent_dirichletOperator_apply`: the resolvent solves the shifted Dirichlet
  problem.
* `TauCeti.PDE.mem_graph_dirichletOperator_laplacian_iff` and
  `TauCeti.PDE.mem_domain_dirichletOperator_laplacian_iff`: for `-Δ`, the graph and domain
  through distributional Laplacians.
* `TauCeti.PDE.neg_setIntegral_laplacian_mul_eq_setIntegral_dirichletOperator_mul` and
  `TauCeti.PDE.dirichletOperator_apply_eq_of_forall_setIntegral_laplacian_mul_eq`: on its domain,
  the Dirichlet Laplacian is the distributional `-Δ`.
* `TauCeti.PDE.exists_isSelfAdjoint_dirichletOperator_laplacian`: the Dirichlet Laplacian.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 6.5.1.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Section 9.8.
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics IV: Analysis of Operators*,
  §XIII.14.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Bornology Filter MeasureTheory Set TopologicalSpace
open scoped InnerProductSpace

section Domain

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}

/-! ### The realization -/

/-- **The Dirichlet realization** of `L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` on `L²(Ω)`, for an energy
form that is coercive on `H¹₀(Ω)`. It is the inverse of the solution operator
`S = TauCeti.PDE.dirichletSolutionOperator`, which is injective. Its domain consists of the
values of the `u ∈ H¹₀(Ω)` with `L u ∈ L²(Ω)` weakly, and it sends such a `u` to `L u`: `(u, f)`
lies on its graph exactly when `a(u, v) = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`
(`TauCeti.PDE.mem_graph_dirichletOperator_iff`). -/
def dirichletOperator
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) :
    Lp ℝ 2 (mu.restrict Omega) →ₗ.[ℝ] Lp ℝ 2 (mu.restrict Omega) :=
  ((dirichletSolutionOperator hcoeff hcoercive :
    Lp ℝ 2 (mu.restrict Omega) →ₗ[ℝ] Lp ℝ 2 (mu.restrict Omega)).toPMap ⊤).inverse

/-- The Dirichlet realization is, by definition, the inverse of the solution operator. -/
theorem dirichletOperator_def
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) :
    dirichletOperator hcoeff hcoercive =
      ((dirichletSolutionOperator hcoeff hcoercive :
        Lp ℝ 2 (mu.restrict Omega) →ₗ[ℝ] Lp ℝ 2 (mu.restrict Omega)).toPMap ⊤).inverse :=
  (rfl)

/-- **The graph of the Dirichlet realization** consists of the pairs `(u, f)` for which
`u ∈ H¹₀(Ω)` is a weak solution of `L u = f`. -/
theorem mem_graph_dirichletOperator_iff
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    {x : Lp ℝ 2 (mu.restrict Omega) × Lp ℝ 2 (mu.restrict Omega)} :
    x ∈ (dirichletOperator hcoeff hcoercive).graph ↔
      ∃ u : W1p0 mu Omega 2,
        W1p.value (u : W1p mu Omega 2) = x.1 ∧ IsWeakSolutionDirichlet a b c x.2 u := by
  rw [dirichletOperator_def, ContinuousLinearMap.mem_graph_inverse_toPMap_top_iff _
    (dirichletSolutionOperator_injective hcoeff hcoercive), dirichletSolutionOperator_apply]
  constructor
  · intro h
    exact ⟨_, h, isWeakSolutionDirichlet_weakSolutionDirichlet hcoeff hcoercive x.2⟩
  · rintro ⟨u, hu, hsol⟩
    rw [← eq_weakSolutionDirichlet hcoeff hcoercive hsol, hu]

/-- **The domain of the Dirichlet realization**: the values of the `u ∈ H¹₀(Ω)` for which `L u`
lies in `L²(Ω)`, that is, which weakly solve `L u = g` for some `g ∈ L²(Ω)`. -/
theorem mem_domain_dirichletOperator_iff
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    {f : Lp ℝ 2 (mu.restrict Omega)} :
    f ∈ (dirichletOperator hcoeff hcoercive).domain ↔
      ∃ u : W1p0 mu Omega 2, W1p.value (u : W1p mu Omega 2) = f ∧
        ∃ g : Lp ℝ 2 (mu.restrict Omega), IsWeakSolutionDirichlet a b c g u := by
  simp only [LinearPMap.mem_domain_iff, mem_graph_dirichletOperator_iff]
  exact ⟨fun ⟨g, u, hu, hg⟩ => ⟨u, hu, g, hg⟩, fun ⟨u, hu, g, hg⟩ => ⟨g, u, hu, hg⟩⟩

/-- The value of a weak solution of `L u = g` lies in the domain of the Dirichlet realization. -/
theorem value_mem_domain_dirichletOperator
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    {g : Lp ℝ 2 (mu.restrict Omega)} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a b c g u) :
    W1p.value (u : W1p mu Omega 2) ∈ (dirichletOperator hcoeff hcoercive).domain :=
  (mem_domain_dirichletOperator_iff hcoeff hcoercive).2 ⟨u, rfl, g, hu⟩

/-- **The Dirichlet realization is `L`**: if `u ∈ H¹₀(Ω)` represents `f` in its domain, then `u`
is a weak solution of `L u = A f`. -/
theorem isWeakSolutionDirichlet_dirichletOperator
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    (f : (dirichletOperator hcoeff hcoercive).domain) {u : W1p0 mu Omega 2}
    (hu : W1p.value (u : W1p mu Omega 2) = f) :
    IsWeakSolutionDirichlet a b c (dirichletOperator hcoeff hcoercive f) u := by
  obtain ⟨w, hw, hwf⟩ := (mem_graph_dirichletOperator_iff hcoeff hcoercive).1
    ((dirichletOperator hcoeff hcoercive).mem_graph f)
  rwa [Subtype.ext (W1p.ext_value (hw.trans hu.symm))] at hwf

/-- The Dirichlet realization sends the value of a weak solution of `L u = g` to `g`. -/
theorem dirichletOperator_apply_eq_of_isWeakSolutionDirichlet
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    {f : (dirichletOperator hcoeff hcoercive).domain} {g : Lp ℝ 2 (mu.restrict Omega)}
    {u : W1p0 mu Omega 2} (hu : W1p.value (u : W1p mu Omega 2) = f)
    (hg : IsWeakSolutionDirichlet a b c g u) : dirichletOperator hcoeff hcoercive f = g :=
  ((LinearPMap.image_iff f.2).2
    ((mem_graph_dirichletOperator_iff hcoeff hcoercive).2 ⟨u, hu, hg⟩)).symm

/-- A Dirichlet eigenfunction is an eigenvector of the Dirichlet realization: if
`a(u, v) = κ ⟪u, v⟫_{L²(Ω)}` for every `v ∈ H¹₀(Ω)`, the value of `u` lies in the domain and is
sent to `κ u`. -/
theorem exists_dirichletOperator_apply_eq_smul
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    {kappa : ℝ} {u : W1p0 mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        kappa * ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ) :
    ∃ hmem : W1p.value (u : W1p mu Omega 2) ∈ (dirichletOperator hcoeff hcoercive).domain,
      dirichletOperator hcoeff hcoercive ⟨_, hmem⟩ = kappa • W1p.value (u : W1p mu Omega 2) := by
  have hsol : IsWeakSolutionDirichlet a b c (kappa • W1p.value (u : W1p mu Omega 2)) u :=
    (isWeakSolutionDirichlet_iff_inner _ _).2 fun v => by rw [hu v, real_inner_smul_left]
  exact ⟨value_mem_domain_dirichletOperator hcoeff hcoercive hsol,
    dirichletOperator_apply_eq_of_isWeakSolutionDirichlet hcoeff hcoercive rfl hsol⟩

/-- **The resolvent of the Dirichlet realization solves the shifted Dirichlet problem.** At a
point `κ` of the resolvent set, the resolvent sends `f` to `-u`, where `u` is a weak solution of
`L u - κ u = f`. -/
theorem resolvent_dirichletOperator_apply
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    {kappa : ℝ} (hkappa : kappa ∈ (dirichletOperator hcoeff hcoercive).resolventSet)
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichletMassShift a b c kappa f u) :
    (dirichletOperator hcoeff hcoercive).resolvent kappa f = -W1p.value (u : W1p mu Omega 2) := by
  -- `L (-u) = -(f + κ u)`, so `(κ - L) (-u) = f`.
  have hsol : IsWeakSolutionDirichlet a b c
      (-(f + kappa • W1p.value (u : W1p mu Omega 2))) (-u) := by
    refine (isWeakSolutionDirichlet_iff_inner _ _).2 fun v => ?_
    have h := (isWeakSolutionDirichletMassShift_iff kappa f u).1 hu v
    rw [← dirichletForcing_apply_eq_setIntegral, dirichletForcing_apply] at h
    rw [← energyFormH1L0_apply hcoeff, map_neg, neg_apply, energyFormH1L0_apply, inner_neg_left,
      inner_add_left, real_inner_smul_left, ← h]
    ring
  have hval : W1p.value ((-u : W1p0 mu Omega 2) : W1p mu Omega 2) =
      -W1p.value (u : W1p mu Omega 2) := by
    rw [← W1p0.valueL_apply, ← W1p0.valueL_apply, map_neg]
  have hmem : -W1p.value (u : W1p mu Omega 2) ∈ (dirichletOperator hcoeff hcoercive).domain :=
    hval ▸ value_mem_domain_dirichletOperator hcoeff hcoercive hsol
  have happly := dirichletOperator_apply_eq_of_isWeakSolutionDirichlet hcoeff hcoercive
    (f := ⟨_, hmem⟩) hval hsol
  have h := LinearPMap.resolvent_smul_sub_apply hkappa ⟨_, hmem⟩
  rwa [happly, smul_neg, sub_neg_eq_add, neg_add_cancel_comm_assoc] at h

/-! ### Self-adjointness, resolvent and spectrum -/

/-- **The Dirichlet realization of a symmetric coercive form is self-adjoint.** With no drift and
an almost everywhere symmetric principal coefficient the symmetry hypothesis is supplied by
`TauCeti.PDE.energyFormH1_comm_of_isSymm_ae`. -/
theorem isSelfAdjoint_dirichletOperator
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    (hsymm : ∀ u v : W1p0 mu Omega 2,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2)) :
    IsSelfAdjoint (dirichletOperator hcoeff hcoercive) :=
  ContinuousLinearMap.isSelfAdjoint_inverse_toPMap_top _
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2
      (isSymmetric_dirichletSolutionOperator hcoeff hcoercive hsymm))
    (dirichletSolutionOperator_injective hcoeff hcoercive)

/-- `0` is a resolvent point of the Dirichlet realization. -/
theorem zero_mem_resolventSet_dirichletOperator
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) :
    (0 : ℝ) ∈ (dirichletOperator hcoeff hcoercive).resolventSet :=
  ContinuousLinearMap.zero_mem_resolventSet_inverse_toPMap_top _
    (dirichletSolutionOperator_injective hcoeff hcoercive)

/-- The resolvent of the Dirichlet realization at `0` is minus the solution operator. -/
@[simp]
theorem resolvent_dirichletOperator_zero
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) :
    (dirichletOperator hcoeff hcoercive).resolvent 0 =
      -dirichletSolutionOperator hcoeff hcoercive :=
  ContinuousLinearMap.resolvent_inverse_toPMap_top_zero _
    (dirichletSolutionOperator_injective hcoeff hcoercive)

/-- **The Dirichlet realization has compact resolvent** on a bounded domain, by
Rellich--Kondrachov. -/
theorem hasCompactResolvent_dirichletOperator
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ ι))) :
    (dirichletOperator hcoeff hcoercive).HasCompactResolvent :=
  ContinuousLinearMap.hasCompactResolvent_inverse_toPMap_top _
    (dirichletSolutionOperator_injective hcoeff hcoercive)
    (isCompactOperator_dirichletSolutionOperator hcoeff hcoercive hOmega)

/-- **The spectrum of the Dirichlet realization is the Dirichlet spectrum**: on a bounded domain,
`κ` lies in the spectrum exactly when `L u = κ u` has a nonzero weak solution `u ∈ H¹₀(Ω)`. -/
theorem mem_spectrum_dirichletOperator_iff
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ ι))) {kappa : ℝ} :
    kappa ∈ (dirichletOperator hcoeff hcoercive).spectrum ↔
      IsDirichletEigenvalue mu Omega a b c kappa := by
  rcases eq_or_ne kappa 0 with rfl | hkappa
  · exact iff_of_false (fun h => (LinearPMap.mem_spectrum_iff _ _).1 h
      (zero_mem_resolventSet_dirichletOperator hcoeff hcoercive))
      fun h => (pos_of_isDirichletEigenvalue hcoeff hcoercive h).ne rfl
  · rw [isDirichletEigenvalue_iff_hasEigenvalue hcoeff hcoercive hkappa]
    exact ContinuousLinearMap.mem_spectrum_inverse_toPMap_top_iff_hasEigenvalue _
      (dirichletSolutionOperator_injective hcoeff hcoercive)
      (isCompactOperator_dirichletSolutionOperator hcoeff hcoercive hOmega) hkappa

/-- The spectrum of the Dirichlet realization, as a set: the Dirichlet eigenvalues. -/
theorem spectrum_dirichletOperator
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ ι))) :
    (dirichletOperator hcoeff hcoercive).spectrum =
      {kappa | IsDirichletEigenvalue mu Omega a b c kappa} :=
  Set.ext fun _ => mem_spectrum_dirichletOperator_iff hcoeff hcoercive hOmega

end Domain

/-! ### The domain of the Dirichlet Laplacian -/

section LaplacianDomain

open Laplacian
open scoped Distributions

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}

/-- **The graph of the Dirichlet Laplacian.** For `-Δ`, `x = (f, g)` lies on the graph of the
Dirichlet realization exactly when `f` is the value of some `u ∈ H¹₀(Ω)` and `-Δf = g` in the
sense of distributions on `Ω`. -/
theorem mem_graph_dirichletOperator_laplacian_iff
    (hcoeff : MemLp (fun x ↦ energyIntegrand ((fun _ ↦ (1 : Matrix ι ι ℝ)) x)
      ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x) ((0 : EuclideanSpace ℝ ι → ℝ) x)) ⊤
      (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    {x : Lp ℝ 2 (mu.restrict Omega) × Lp ℝ 2 (mu.restrict Omega)} :
    x ∈ (dirichletOperator hcoeff hcoercive).graph ↔
      (∃ u : W1p0 mu Omega 2, W1p.value (u : W1p mu Omega 2) = x.1) ∧
        ∀ φ : 𝓓(Omega, ℝ), -∫ y in Omega, Δ (φ : EuclideanSpace ℝ ι → ℝ) y * x.1 y ∂mu =
          ∫ y in Omega, x.2 y * φ y ∂mu := by
  obtain ⟨f, g⟩ := x
  simp only [mem_graph_dirichletOperator_iff,
    isWeakSolutionDirichlet_one_zero_zero_iff_forall_setIntegral_laplacian_mul_eq]
  constructor
  · rintro ⟨u, rfl, h⟩
    exact ⟨⟨u, rfl⟩, h⟩
  · rintro ⟨⟨u, rfl⟩, h⟩
    exact ⟨u, rfl, h⟩

/-- **The domain of the Dirichlet Laplacian** is `{u ∈ H¹₀(Ω) : Δu ∈ L²(Ω)}`: the values of
`H¹₀(Ω)` whose distributional Laplacian on `Ω` is an `L²(Ω)` function. -/
theorem mem_domain_dirichletOperator_laplacian_iff
    (hcoeff : MemLp (fun x ↦ energyIntegrand ((fun _ ↦ (1 : Matrix ι ι ℝ)) x)
      ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x) ((0 : EuclideanSpace ℝ ι → ℝ) x)) ⊤
      (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) {f : Lp ℝ 2 (mu.restrict Omega)} :
    f ∈ (dirichletOperator hcoeff hcoercive).domain ↔
      (∃ u : W1p0 mu Omega 2, W1p.value (u : W1p mu Omega 2) = f) ∧
        ∃ g : Lp ℝ 2 (mu.restrict Omega), ∀ φ : 𝓓(Omega, ℝ),
          ∫ x in Omega, Δ (φ : EuclideanSpace ℝ ι → ℝ) x * f x ∂mu =
            ∫ x in Omega, g x * φ x ∂mu := by
  simp only [LinearPMap.mem_domain_iff, mem_graph_dirichletOperator_laplacian_iff,
    exists_and_left]
  refine and_congr_right' <| (Equiv.neg _).exists_congr fun g ↦ forall_congr' fun φ ↦ ?_
  have hg : ∫ x in Omega, (-g) x * φ x ∂mu = -∫ x in Omega, g x * φ x ∂mu := by
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_neg g] with x hx
    rw [hx, Pi.neg_apply, neg_mul]
  rw [Equiv.neg_apply, hg, neg_eq_iff_eq_neg]

/-- On its domain, the Dirichlet Laplacian is the distributional `-Δ`: for `f` in the domain,
`-∫_Ω Δφ f = ∫_Ω (A f) φ` for every test function `φ` on `Ω`. -/
theorem neg_setIntegral_laplacian_mul_eq_setIntegral_dirichletOperator_mul
    (hcoeff : MemLp (fun x ↦ energyIntegrand ((fun _ ↦ (1 : Matrix ι ι ℝ)) x)
      ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x) ((0 : EuclideanSpace ℝ ι → ℝ) x)) ⊤
      (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    (f : (dirichletOperator hcoeff hcoercive).domain) (φ : 𝓓(Omega, ℝ)) :
    -∫ x in Omega, Δ (φ : EuclideanSpace ℝ ι → ℝ) x * (f : Lp ℝ 2 (mu.restrict Omega)) x ∂mu =
      ∫ x in Omega, dirichletOperator hcoeff hcoercive f x * φ x ∂mu :=
  ((mem_graph_dirichletOperator_laplacian_iff hcoeff hcoercive).1
    ((dirichletOperator hcoeff hcoercive).mem_graph f)).2 φ

/-- The Dirichlet Laplacian sends `f` in its domain to `g` when `-Δf = g` in the sense of
distributions on `Ω`. -/
theorem dirichletOperator_apply_eq_of_forall_setIntegral_laplacian_mul_eq
    (hcoeff : MemLp (fun x ↦ energyIntegrand ((fun _ ↦ (1 : Matrix ι ι ℝ)) x)
      ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x) ((0 : EuclideanSpace ℝ ι → ℝ) x)) ⊤
      (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    {f : (dirichletOperator hcoeff hcoercive).domain} {g : Lp ℝ 2 (mu.restrict Omega)}
    (hg : ∀ φ : 𝓓(Omega, ℝ),
      -∫ x in Omega, Δ (φ : EuclideanSpace ℝ ι → ℝ) x * (f : Lp ℝ 2 (mu.restrict Omega)) x ∂mu =
        ∫ x in Omega, g x * φ x ∂mu) :
    dirichletOperator hcoeff hcoercive f = g :=
  ((LinearPMap.image_iff f.2).2 ((mem_graph_dirichletOperator_laplacian_iff hcoeff hcoercive).2
    ⟨((mem_domain_dirichletOperator_laplacian_iff hcoeff hcoercive).1 f.2).1, hg⟩)).symm

end LaplacianDomain

/-! ### The Dirichlet Laplacian -/

section Laplacian

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}

/-- **The Dirichlet Laplacian.** On a nonempty bounded open set `Ω ⊆ ℝ^{n+1}`, the Dirichlet
realization of `-Δ` on `L²(Ω)`, with domain `{u ∈ H¹₀(Ω) : Δu ∈ L²(Ω)}`, is self-adjoint with
compact resolvent. Its spectrum is a nondecreasing sequence `0 < λ₀ ≤ λ₁ ≤ ⋯ → ∞`, repeated
according to multiplicity, with an orthonormal basis `(eₖ)` of `L²(Ω)` in its domain such that
`-Δ eₖ = λₖ eₖ`. -/
theorem exists_isSelfAdjoint_dirichletOperator_laplacian
    (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hOmega_nonempty : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))).Nonempty) :
    ∃ (hcoeff : MemLp (fun x ↦ energyIntegrand
        ((fun _ ↦ (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) x)
        ((0 : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) x)
        ((0 : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)) ⊤
        (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))))
      (hcoercive : IsCoercive (energyFormH1L0 hcoeff)),
      IsSelfAdjoint (dirichletOperator hcoeff hcoercive) ∧
      (dirichletOperator hcoeff hcoercive).HasCompactResolvent ∧
      ∃ (basis : HilbertBasis ℕ ℝ
          (Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))))
        (kappa : ℕ → ℝ),
        0 < kappa 0 ∧ Monotone kappa ∧ Tendsto kappa atTop atTop ∧
        (∀ k, ∃ hk : basis k ∈ (dirichletOperator hcoeff hcoercive).domain,
          dirichletOperator hcoeff hcoercive ⟨basis k, hk⟩ = kappa k • basis k) ∧
        (dirichletOperator hcoeff hcoercive).spectrum = range kappa := by
  have hsymm (u v : W1p0 volume Omega 2) :
      energyFormH1 (fun _ ↦ 1) 0 0 (u : W1p volume Omega 2) (v : W1p volume Omega 2) =
        energyFormH1 (fun _ ↦ 1) 0 0 (v : W1p volume Omega 2) (u : W1p volume Omega 2) :=
    energyFormH1_comm_of_isSymm_ae (ae_of_all _ fun _ ↦ Matrix.isSymm_one) _ _
  refine (exists_isCoercive_laplacian_of_isBounded hOmega).elim fun hcoeff hcoercive ↦ ?_
  obtain ⟨basis, kappa, u, hpos, hmono, htends, -, hvalue, heq, hiff⟩ :=
    exists_hilbertBasis_nat_isDirichletEigenvalue_laplacian_monotone hOmega hOmega_nonempty
  refine ⟨hcoeff, hcoercive, isSelfAdjoint_dirichletOperator hcoeff hcoercive hsymm,
    hasCompactResolvent_dirichletOperator hcoeff hcoercive hOmega, basis, kappa, hpos, hmono,
    htends, fun k => ?_, ?_⟩
  · obtain ⟨hmem, happly⟩ := exists_dirichletOperator_apply_eq_smul hcoeff hcoercive (heq k)
    simp only [hvalue k] at hmem happly
    exact ⟨hmem, happly⟩
  · ext kappa'
    exact (mem_spectrum_dirichletOperator_iff hcoeff hcoercive hOmega).trans (hiff kappa')

end Laplacian

end PDE

end TauCeti
