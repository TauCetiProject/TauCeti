/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Variational.FormOperator
public import TauCeti.Analysis.PDE.Spectrum.Operator
public import TauCeti.Analysis.Sobolev.W1p.BoundaryPart

/-!
# The mixed realization of a divergence-form operator

Let `L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` be a divergence-form operator with essentially bounded
coefficients on an open set `Ω ⊆ ℝⁿ`, and let `Γ` be a set disjoint from `Ω`, typically a part of
its boundary. Write `H¹_Γ(Ω)` for the space `TauCeti.w1pVanishingOnSubmodule mu Ω 2 Γ` of Sobolev
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

the form `a + ω ⟪·, ·⟫_{L²}` is coercive on `H¹_Γ(Ω)`, and the realization is the operator of the
form `a` along the value map shifted by `ω` (`IsCoercive.formOperator`); the shift does not change
it. Its operator theory follows from that construction:

* `-ω` is a resolvent point (`TauCeti.PDE.neg_mem_resolventSet_mixedOperator`), and at every
  resolvent point `κ` the resolvent sends `f` to `-u` for a weak solution `u` of `L u - κ u = f`
  (`TauCeti.PDE.resolvent_mixedOperator_apply`);
* `⟪A u, u⟫ = a(u, u)` on the domain (`TauCeti.PDE.inner_mixedOperator_eq_energyFormH1`), so the
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
  `TauCeti.PDE.mixedOperator_apply_eq` and
  `TauCeti.PDE.exists_mixedOperator_apply_eq_smul_iff` (its eigenvectors).
* `TauCeti.PDE.mixedOperator_frontier`: at `Γ = ∂Ω` it is the Dirichlet realization
  `TauCeti.PDE.dirichletOperator`.
* `TauCeti.PDE.isSelfAdjoint_mixedOperator`, `TauCeti.PDE.hasCompactResolvent_mixedOperator`
  and `TauCeti.PDE.mem_spectrum_mixedOperator_iff`: self-adjointness, compact resolvent and
  spectrum.
* `TauCeti.PDE.resolvent_mixedOperator_apply`: the resolvent solves the shifted mixed problem.
* `TauCeti.PDE.isSelfAdjoint_mixedOperator_laplacian`,
  `TauCeti.PDE.inner_mixedOperator_laplacian_nonneg`,
  `TauCeti.PDE.mem_resolventSet_mixedOperator_laplacian_of_neg`,
  `TauCeti.PDE.hasCompactResolvent_mixedOperator_laplacian` and
  `TauCeti.PDE.mem_spectrum_mixedOperator_laplacian_iff`: the mixed Laplacian `-Δ_Γ`.

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

/-- Shortcut instance for the normed group structure of `H¹_Γ(Ω)`, inherited through the nested
Sobolev subspaces; instance search can time out on it inside abstract Hilbert space lemmas. -/
local instance : NormedAddCommGroup (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule :=
  inferInstance

/-- Shortcut instance for the Hilbert space structure of `H¹_Γ(Ω)`. -/
local instance : InnerProductSpace ℝ (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule :=
  inferInstance

/-- `H¹_Γ(Ω)` is complete, as a closed subspace of `H¹(Ω)`. -/
local instance : CompleteSpace (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule :=
  (w1pVanishingOnSubmodule mu Omega 2 Γ).isClosed.completeSpace_coe

/-! ### The value map and the energy form on `H¹_Γ(Ω)` -/

/-- The value map `H¹_Γ(Ω) → L²(Ω)`. -/
private def vanishingValueL (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure]
    (Omega : Opens (EuclideanSpace ℝ ι)) (Γ : Set (EuclideanSpace ℝ ι)) :
    (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule →L[ℝ] Lp ℝ 2 (mu.restrict Omega) :=
  W1p.valueL.comp (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule.subtypeL

private theorem vanishingValueL_apply (u : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule) :
    vanishingValueL mu Omega Γ u = W1p.value (u : W1p mu Omega 2) := by
  simp [vanishingValueL]

/-- The value map `H¹_Γ(Ω) → L²(Ω)` has dense range when `Γ` misses `Ω`, since `H¹_Γ(Ω)`
contains `H¹₀(Ω)`. -/
private theorem denseRange_vanishingValueL (hΓ : Disjoint Γ Omega) :
    DenseRange (vanishingValueL mu Omega Γ) :=
  W1p0.denseRange_valueL_two.mono <| by
    rintro _ ⟨w, rfl⟩
    exact ⟨⟨w, w1p0Submodule_le_w1pVanishingOnSubmodule hΓ w.property⟩, by
      simp only [vanishingValueL_apply, W1p0.valueL_apply]⟩

/-- The value map `H¹_Γ(Ω) → L²(Ω)` is compact when the value map of `H¹(Ω)` is. -/
private theorem isCompactOperator_vanishingValueL
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2))) :
    IsCompactOperator (vanishingValueL mu Omega Γ) :=
  hK.comp_clm _

/-- The energy form on `H¹_Γ(Ω)`, shifted by `ω` times the `L²` inner product. -/
private def shiftedForm
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (Γ : Set (EuclideanSpace ℝ ι)) (omega : ℝ) :
    (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule →L[ℝ]
      (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule →L[ℝ] ℝ :=
  (energyFormH1L (memLp_energyIntegrand_mass_sub_const hcoeff (-omega))).bilinearComp
    (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule.subtypeL
    (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule.subtypeL

private theorem shiftedForm_apply
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (omega : ℝ) (u v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule) :
    shiftedForm hcoeff Γ omega u v =
      shiftedForm hcoeff Γ 0 u v +
        omega * ⟪vanishingValueL mu Omega Γ u, vanishingValueL mu Omega Γ v⟫_ℝ := by
  simp only [shiftedForm, ContinuousLinearMap.bilinearComp_apply, energyFormH1L_apply,
    energyFormH1_mass_sub_const hcoeff, Submodule.subtypeL_apply, vanishingValueL_apply]
  ring

private theorem shiftedForm_zero_apply
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (u v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule) :
    shiftedForm hcoeff Γ 0 u v = energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) := by
  simp only [shiftedForm, ContinuousLinearMap.bilinearComp_apply, energyFormH1L_apply,
    energyFormH1_mass_sub_const hcoeff, Submodule.subtypeL_apply]
  ring

/-- A Gårding inequality on `H¹_Γ(Ω)` is coercivity of the shifted form. -/
private theorem isCoercive_shiftedForm
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    {theta omega : ℝ} (htheta : 0 < theta)
    (hgarding : ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      theta * ‖(v : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) +
          omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2) :
    IsCoercive (shiftedForm hcoeff Γ omega) := by
  refine ⟨theta, htheta, fun v ↦ ?_⟩
  rw [shiftedForm_apply, shiftedForm_zero_apply, real_inner_self_eq_norm_sq,
    vanishingValueL_apply, mul_assoc, ← sq]
  exact hgarding v

/-! ### The realization -/

/-- The pairs `(u, f)` of `L²(Ω) × L²(Ω)` with `u ∈ H¹_Γ(Ω)` and `a(u, v) = ⟪f, v⟫` for every
`v ∈ H¹_Γ(Ω)`. -/
private def mixedGraph
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (Γ : Set (EuclideanSpace ℝ ι)) :
    Submodule ℝ (Lp ℝ 2 (mu.restrict Omega) × Lp ℝ 2 (mu.restrict Omega)) where
  carrier := {x | ∃ u : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
    vanishingValueL mu Omega Γ u = x.1 ∧
      ∀ v, shiftedForm hcoeff Γ 0 u v = ⟪x.2, vanishingValueL mu Omega Γ v⟫_ℝ}
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

/-- `mixedGraph` is the graph of a partial linear map: a pair `(0, f)` in it has `f = 0`. -/
private theorem mixedGraph_snd_eq_zero
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hΓ : Disjoint Γ Omega) :
    ∀ x ∈ mixedGraph hcoeff Γ, x.1 = 0 → x.2 = 0 := by
  rintro x ⟨u, hu, hxu⟩ hx
  -- The value of `u` vanishes, so `u = 0` and `f` is orthogonal to the dense range of the value
  -- map.
  have hu0 : u = 0 := Subtype.ext (W1p.ext_value (by
    rw [← vanishingValueL_apply, hu, hx, ZeroMemClass.coe_zero, W1p.value_zero]))
  have horth : ∀ y, ⟪x.2, y⟫_ℝ = 0 := fun y ↦
    (denseRange_vanishingValueL hΓ).induction_on y
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

/-- **The graph of the mixed realization** consists of the pairs `(u, f)` for which `u ∈ H¹_Γ(Ω)`
is a weak solution of `L u = f`: `a(u, v) = ⟪f, v⟫_{L²(Ω)}` for every `v ∈ H¹_Γ(Ω)`. -/
theorem mem_graph_mixedOperator_iff
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hΓ : Disjoint Γ Omega)
    {x : Lp ℝ 2 (mu.restrict Omega) × Lp ℝ 2 (mu.restrict Omega)} :
    x ∈ (mixedOperator hcoeff Γ).graph ↔
      ∃ u : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
        W1p.value (u : W1p mu Omega 2) = x.1 ∧
          ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
            energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
              ⟪x.2, W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
  rw [mixedOperator, Submodule.toLinearPMap_graph_eq _ (mixedGraph_snd_eq_zero hcoeff hΓ)]
  change (∃ u, _ ∧ _) ↔ _
  simp only [vanishingValueL_apply, shiftedForm_zero_apply]

/-- **The domain of the mixed realization**: the values of the `u ∈ H¹_Γ(Ω)` for which `L u` lies
in `L²(Ω)`, that is, which weakly solve `L u = g` for some `g ∈ L²(Ω)`. -/
theorem mem_domain_mixedOperator_iff
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hΓ : Disjoint Γ Omega) {f : Lp ℝ 2 (mu.restrict Omega)} :
    f ∈ (mixedOperator hcoeff Γ).domain ↔
      ∃ u : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
        W1p.value (u : W1p mu Omega 2) = f ∧ ∃ g : Lp ℝ 2 (mu.restrict Omega),
          ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
            energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
              ⟪g, W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
  simp only [LinearPMap.mem_domain_iff, mem_graph_mixedOperator_iff hcoeff hΓ]
  exact ⟨fun ⟨g, u, hu, hg⟩ ↦ ⟨u, hu, g, hg⟩, fun ⟨u, hu, g, hg⟩ ↦ ⟨g, u, hu, hg⟩⟩

/-- **The mixed realization is `L`**: if `u ∈ H¹_Γ(Ω)` weakly solves `L u = g` and represents `f`
in the domain, then the realization sends `f` to `g`. -/
theorem mixedOperator_apply_eq
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hΓ : Disjoint Γ Omega) {f : (mixedOperator hcoeff Γ).domain}
    {g : Lp ℝ 2 (mu.restrict Omega)} {u : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule}
    (hu : W1p.value (u : W1p mu Omega 2) = f)
    (hg : ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
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
      ∃ u : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
        W1p.value (u : W1p mu Omega 2) = f ∧
          ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
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
    {u : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule}
    (hu : W1p.value (u : W1p mu Omega 2) = f) :
    ⟪mixedOperator hcoeff Γ f, (f : Lp ℝ 2 (mu.restrict Omega))⟫_ℝ =
      energyFormH1 a b c (u : W1p mu Omega 2) (u : W1p mu Omega 2) := by
  obtain ⟨w, hw, hwf⟩ := (mem_graph_mixedOperator_iff hcoeff hΓ).1
    ((mixedOperator hcoeff Γ).mem_graph f)
  obtain rfl : w = u := Subtype.ext (W1p.ext_value (hw.trans hu.symm))
  rw [hwf, hu]

/-- **The resolvent of the mixed realization solves the shifted mixed problem.** At a point `κ`
of the resolvent set, the resolvent sends `f` to `-u`, where `u ∈ H¹_Γ(Ω)` is a weak solution of
`L u - κ u = f`. -/
theorem resolvent_mixedOperator_apply
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hΓ : Disjoint Γ Omega) {kappa : ℝ}
    (hkappa : kappa ∈ (mixedOperator hcoeff Γ).resolventSet)
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule}
    (hu : ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) -
          kappa * ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ =
        ⟪f, W1p.value (v : W1p mu Omega 2)⟫_ℝ) :
    (mixedOperator hcoeff Γ).resolvent kappa f = -W1p.value (u : W1p mu Omega 2) := by
  -- `L (-u) = -(f + κ u)`, so `(κ - L) (-u) = f`.
  have hval : W1p.value ((-u : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule) :
      W1p mu Omega 2) = -W1p.value (u : W1p mu Omega 2) := by
    rw [← vanishingValueL_apply, ← vanishingValueL_apply, map_neg]
  have hsol (v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule) :
      energyFormH1 a b c ((-u : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule) :
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

-- Each proof below identifies the two operators by their graphs and transfers the property of the
-- form operator. The identification is not stated as a separate lemma: an equation between these
-- operators, with the instances of the subtype `H¹_Γ(Ω)` in its statement, is too expensive for
-- the environment linter to re-check.

variable {theta omega : ℝ}

/-- **`-ω` is a resolvent point of the mixed realization** when the energy form satisfies the
Gårding inequality `θ ‖v‖²_{H¹} ≤ a(v, v) + ω ‖v‖²_{L²}` on `H¹_Γ(Ω)`, `θ > 0`. -/
theorem neg_mem_resolventSet_mixedOperator
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hΓ : Disjoint Γ Omega) (htheta : 0 < theta)
    (hgarding : ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      theta * ‖(v : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) +
          omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2) :
    -omega ∈ (mixedOperator hcoeff Γ).resolventSet := by
  have hB := isCoercive_shiftedForm hcoeff htheta hgarding
  have heq : mixedOperator hcoeff Γ = hB.formOperator (vanishingValueL mu Omega Γ) omega :=
    LinearPMap.eq_of_eq_graph <| Submodule.ext fun x ↦ by
      rw [mem_graph_mixedOperator_iff hcoeff hΓ,
        hB.mem_graph_formOperator_iff (denseRange_vanishingValueL hΓ) (Q := shiftedForm hcoeff Γ 0)
          (shiftedForm_apply hcoeff omega)]
      simp only [vanishingValueL_apply, shiftedForm_zero_apply]
  rw [heq]
  exact hB.neg_mem_resolventSet_formOperator (denseRange_vanishingValueL hΓ)

/-- **The mixed realization is bounded below by `-ω`** under the inequality
`θ ‖v‖²_{H¹} ≤ a(v, v) + ω ‖v‖²_{L²}` on `H¹_Γ(Ω)` with `θ ≥ 0`: `⟪A f, f⟫ ≥ -ω ‖f‖²` on its
domain. -/
theorem neg_mul_norm_sq_le_inner_mixedOperator
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hΓ : Disjoint Γ Omega) (htheta : 0 ≤ theta)
    (hgarding : ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
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
    (hgarding : ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      theta * ‖(v : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) +
          omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2)
    (hsymm : ∀ u v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2)) :
    IsSelfAdjoint (mixedOperator hcoeff Γ) := by
  have hB := isCoercive_shiftedForm hcoeff htheta hgarding
  have heq : mixedOperator hcoeff Γ = hB.formOperator (vanishingValueL mu Omega Γ) omega :=
    LinearPMap.eq_of_eq_graph <| Submodule.ext fun x ↦ by
      rw [mem_graph_mixedOperator_iff hcoeff hΓ,
        hB.mem_graph_formOperator_iff (denseRange_vanishingValueL hΓ) (Q := shiftedForm hcoeff Γ 0)
          (shiftedForm_apply hcoeff omega)]
      simp only [vanishingValueL_apply, shiftedForm_zero_apply]
  rw [heq]
  exact hB.isSelfAdjoint_formOperator (denseRange_vanishingValueL hΓ)
    (shiftedForm_apply hcoeff omega) fun u v ↦ by
      rw [shiftedForm_zero_apply, shiftedForm_zero_apply, hsymm]

/-- **The mixed realization has compact resolvent** under the Gårding inequality
`θ ‖v‖²_{H¹} ≤ a(v, v) + ω ‖v‖²_{L²}` on `H¹_Γ(Ω)`, when `Ω` has the Rellich property that the
value map `H¹(Ω) → L²(Ω)` is compact. -/
theorem hasCompactResolvent_mixedOperator
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hΓ : Disjoint Γ Omega) (htheta : 0 < theta)
    (hgarding : ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      theta * ‖(v : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) +
          omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2)
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2))) :
    (mixedOperator hcoeff Γ).HasCompactResolvent := by
  have hB := isCoercive_shiftedForm hcoeff htheta hgarding
  have heq : mixedOperator hcoeff Γ = hB.formOperator (vanishingValueL mu Omega Γ) omega :=
    LinearPMap.eq_of_eq_graph <| Submodule.ext fun x ↦ by
      rw [mem_graph_mixedOperator_iff hcoeff hΓ,
        hB.mem_graph_formOperator_iff (denseRange_vanishingValueL hΓ) (Q := shiftedForm hcoeff Γ 0)
          (shiftedForm_apply hcoeff omega)]
      simp only [vanishingValueL_apply, shiftedForm_zero_apply]
  rw [heq]
  exact hB.hasCompactResolvent_formOperator (isCompactOperator_vanishingValueL hK)
    (denseRange_vanishingValueL hΓ)

/-- **The spectrum of the mixed realization consists of the mixed eigenvalues.** Under the
Gårding inequality `θ ‖v‖²_{H¹} ≤ a(v, v) + ω ‖v‖²_{L²}` on `H¹_Γ(Ω)`, on a domain with the Rellich
property, `κ` lies in the spectrum exactly when `a(u, v) = κ ⟪u, v⟫_{L²(Ω)}` for some nonzero
`u ∈ H¹_Γ(Ω)` and every `v ∈ H¹_Γ(Ω)`. -/
theorem mem_spectrum_mixedOperator_iff
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hΓ : Disjoint Γ Omega) (htheta : 0 < theta)
    (hgarding : ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
      theta * ‖(v : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2) +
          omega * ‖W1p.value (v : W1p mu Omega 2)‖ ^ 2)
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2))) {kappa : ℝ} :
    kappa ∈ (mixedOperator hcoeff Γ).spectrum ↔
      ∃ u : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule, u ≠ 0 ∧
        ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
          energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
            kappa * ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
  have hB := isCoercive_shiftedForm hcoeff htheta hgarding
  have heq : mixedOperator hcoeff Γ = hB.formOperator (vanishingValueL mu Omega Γ) omega :=
    LinearPMap.eq_of_eq_graph <| Submodule.ext fun x ↦ by
      rw [mem_graph_mixedOperator_iff hcoeff hΓ,
        hB.mem_graph_formOperator_iff (denseRange_vanishingValueL hΓ) (Q := shiftedForm hcoeff Γ 0)
          (shiftedForm_apply hcoeff omega)]
      simp only [vanishingValueL_apply, shiftedForm_zero_apply]
  rw [heq, hB.mem_spectrum_formOperator_iff
    (isCompactOperator_vanishingValueL hK) (denseRange_vanishingValueL hΓ)
    (shiftedForm_apply hcoeff omega)]
  simp only [shiftedForm_zero_apply, vanishingValueL_apply]

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
      mem_graph_dirichletOperator_iff, w1pVanishingOnSubmodule_frontier]
    simp only [isWeakSolutionDirichlet_iff_inner]

/-! ### The mixed Laplacian -/

section Laplacian

variable [DecidableEq ι]

/-- The Gårding inequality of `-Δ`: `min 1 ω ‖v‖²_{H¹} ≤ ∫ |∇v|² + ω ‖v‖²_{L²}` for every `ω`. -/
private theorem min_mul_norm_sq_le_energyFormH1_laplacian (omega : ℝ) (v : W1p mu Omega 2) :
    min 1 omega * ‖v‖ ^ 2 ≤
      energyFormH1 (fun _ ↦ 1) 0 0 v v + omega * ‖W1p.value v‖ ^ 2 := by
  rw [energyFormH1_one_zero_zero_eq_inner, real_inner_self_eq_norm_sq,
    W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq]
  nlinarith [min_le_left 1 omega, min_le_right 1 omega, sq_nonneg ‖W1p.value v‖,
    sq_nonneg ‖W1p.gradient v‖]

/-- The energy form of `-Δ` is symmetric. -/
private theorem energyFormH1_laplacian_comm (u v : W1p mu Omega 2) :
    energyFormH1 (fun _ ↦ 1) 0 0 u v = energyFormH1 (fun _ ↦ 1) 0 0 v u := by
  rw [energyFormH1_one_zero_zero_eq_inner, energyFormH1_one_zero_zero_eq_inner, real_inner_comm]

/-- **The mixed Laplacian `-Δ_Γ` is self-adjoint.** -/
theorem isSelfAdjoint_mixedOperator_laplacian (hΓ : Disjoint Γ Omega) :
    IsSelfAdjoint (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
      (1 : Matrix ι ι ℝ)) Γ) :=
  isSelfAdjoint_mixedOperator _ hΓ (lt_min one_pos one_pos)
    (fun v ↦ min_mul_norm_sq_le_energyFormH1_laplacian 1 (v : W1p mu Omega 2))
    fun u v ↦ energyFormH1_laplacian_comm (u : W1p mu Omega 2) v

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
    fun v ↦ min_mul_norm_sq_le_energyFormH1_laplacian (-kappa) (v : W1p mu Omega 2)
  rwa [neg_neg] at h

/-- **The mixed Laplacian `-Δ_Γ` has compact resolvent** on a domain with the Rellich property
that the value map `H¹(Ω) → L²(Ω)` is compact. -/
theorem hasCompactResolvent_mixedOperator_laplacian (hΓ : Disjoint Γ Omega)
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2))) :
    (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
      (1 : Matrix ι ι ℝ)) Γ).HasCompactResolvent :=
  hasCompactResolvent_mixedOperator _ hΓ (lt_min one_pos one_pos)
    (fun v ↦ min_mul_norm_sq_le_energyFormH1_laplacian 1 (v : W1p mu Omega 2)) hK

/-- **The spectrum of the mixed Laplacian `-Δ_Γ`.** On a domain with the Rellich property, `κ`
lies in the spectrum of `-Δ_Γ` exactly when `∫_Ω ∇u · ∇v = κ ∫_Ω u v` for some nonzero
`u ∈ H¹_Γ(Ω)` and every `v ∈ H¹_Γ(Ω)`; such a `κ` is nonnegative
(`TauCeti.PDE.mem_resolventSet_mixedOperator_laplacian_of_neg`). -/
theorem mem_spectrum_mixedOperator_laplacian_iff (hΓ : Disjoint Γ Omega)
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2))) {kappa : ℝ} :
    kappa ∈ (mixedOperator (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega)
      (1 : Matrix ι ι ℝ)) Γ).spectrum ↔
      ∃ u : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule, u ≠ 0 ∧
        ∀ v : (w1pVanishingOnSubmodule mu Omega 2 Γ).toSubmodule,
          ⟪W1p.gradient (u : W1p mu Omega 2), W1p.gradient (v : W1p mu Omega 2)⟫_ℝ =
            kappa * ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
  rw [mem_spectrum_mixedOperator_iff
    (memLp_energyIntegrand_const_zero_zero (mu := mu) (Omega := Omega) (1 : Matrix ι ι ℝ)) hΓ
    (lt_min one_pos one_pos)
    (fun v ↦ min_mul_norm_sq_le_energyFormH1_laplacian 1 (v : W1p mu Omega 2)) hK]
  simp only [energyFormH1_one_zero_zero_eq_inner]

end Laplacian

end PDE

end TauCeti
