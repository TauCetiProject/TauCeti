/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.MeasurePreserving
public import TauCeti.Analysis.Sobolev.W1p.Multiplication
public import TauCeti.Analysis.Sobolev.W1p.Restriction
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.ContDiff.Indicator
import TauCeti.Analysis.Sobolev.W1p.Density
import TauCeti.Analysis.Sobolev.W1p.Lipschitz
import TauCeti.MeasureTheory.Function.Lp.Restriction

/-!
# Sobolev functions vanishing on a part of the boundary

For an open set `Ω`, a set `Γ` and `1 ≤ p ≤ ∞`, this file defines `W^{1,p}_Γ(Ω)`, the closure in
`W^{1,p}(Ω)` of the restrictions to `Ω` of the smooth compactly supported functions on the whole
space whose support stays away from `closure Γ`. For a boundary part `Γ ⊆ frontier Ω` it is the
space of the mixed boundary value problem: a Dirichlet condition is imposed on `closure Γ`, which
may be larger than `Γ`, and nothing on the rest `frontier Ω \ closure Γ` of the boundary, where
the weak formulation produces the natural (Neumann) condition. No regularity of `Ω` or of `Γ` is
assumed in the definition.

The two extreme cases are the familiar ones. At `Γ = frontier Ω` every generator restricts to a
test function supported in `Ω`, and conversely, so `W^{1,p}_Γ(Ω) = W^{1,p}_0(Ω)` for every open `Ω`
and every `p` (`TauCeti.w1pVanishingOnSubmodule_frontier`). At `Γ = ∅` the generators are all
restrictions of test functions, which are dense in `W^{1,p}(Ω)` on bounded Lipschitz domains for
finite `p`; that case lives with the Lipschitz-domain theory.

The space shrinks as `Γ` grows and depends on `Γ` only through its closure. When `Γ` misses `Ω`,
as a boundary part does, it contains `W^{1,p}_0(Ω)`; this can fail when `Γ` meets `Ω`, for
instance when `Γ` contains a nonempty open subset of `Ω`. Multiplication by a smooth function
bounded together with its gradient preserves it, as for `W^{1,p}_0(Ω)`. Its invariance under rigid
motions is in `TauCeti.Analysis.Sobolev.W1p.BoundaryPart.ChangeOfVariables`.

For finite `p` the generators need not be smooth: a function on the whole space vanishing outside a
compact set disjoint from `closure Γ` lies in `W^{1,p}_Γ(Ω)` as soon as it lies in `W^{1,p}`, in
particular when it is locally Lipschitz. A cutoff equal to one on the compact set and supported away
from `closure Γ` turns the test functions approximating it on the whole space into generators. This
is what transports `W^{1,p}_Γ` along Lipschitz changes of variables, whose composites with test
functions are only Lipschitz.

## Main declarations

* `TauCeti.w1pVanishingOnSubmodule`: the closed subspace `W^{1,p}_Γ(Ω)` of `W^{1,p}(Ω)`, and
  `TauCeti.W1pVanishingOn`, the same space as a complete normed space.
* `TauCeti.W1p.restrictL_ofTestFunctionₗ_mem_w1pVanishingOnSubmodule` and
  `TauCeti.w1pVanishingOnSubmodule_subset_of_isClosed`: the generators lie in it, and a closed set
  containing them contains all of it.
* `TauCeti.W1p.apply_ae_eq_zero_of_mem_w1pVanishingOnSubmodule`: every trace operator, a
  continuous linear map sending each generator to its boundary values, vanishes on `Γ` on it.
* `TauCeti.mem_w1pVanishingOnSubmodule_iff_exists_seq_tendsto`: its elements are the limits of
  sequences of generators.
* `TauCeti.w1pVanishingOnSubmodule_antitone` and `TauCeti.w1pVanishingOnSubmodule_closure`: it is
  antitone in `Γ` and depends only on `closure Γ`.
* `TauCeti.w1p0Submodule_le_w1pVanishingOnSubmodule`: it contains `W^{1,p}_0(Ω)` when `Γ` misses
  `Ω`, and more generally `TauCeti.W1p.restrictL_mem_w1pVanishingOnSubmodule`: restriction from a
  larger open set `U` maps `W^{1,p}_0(U)` into it when `Γ` misses `U`.
* `TauCeti.w1pVanishingOnSubmodule_frontier`: at `Γ = frontier Ω` it is `W^{1,p}_0(Ω)`.
* `TauCeti.W1p.contDiffSMul_mem_w1pVanishingOnSubmodule`: it is stable under multiplication by
  smooth functions bounded with their gradients.
* `TauCeti.W1p.restrictL_mem_w1pVanishingOnSubmodule_of_isCompact` and
  `TauCeti.W1p.mem_w1pVanishingOnSubmodule_of_locallyLipschitz`: for finite `p` it contains the
  restrictions of the Sobolev, in particular of the locally Lipschitz, functions on the whole space
  vanishing outside a compact set disjoint from `closure Γ`.
* `TauCeti.W1pVanishingOn.instNormedAddCommGroup` and
  `TauCeti.W1pVanishingOn.instInnerProductSpace`: shortcut instances, registered locally by files
  applying abstract Hilbert space results to `W^{1,2}_Γ(Ω)`.

## References

* S. Bauer, D. Pauly, M. Schomburg, *The Maxwell compactness property in bounded weak Lipschitz
  domains with mixed boundary conditions*, SIAM J. Math. Anal. 48 (2016), §2 (the spaces of
  functions vanishing on a boundary part, defined as closures of test functions supported away
  from it).
* P. Grisvard, *Elliptic Problems in Nonsmooth Domains*, §1.5 (mixed boundary conditions).
-/

public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Topology Gradient ContDiff

namespace TauCeti

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Γ : Set E}

/-! ### The definition -/

/-- **The space `W^{1,p}_Γ(Ω)` of Sobolev functions vanishing on `Γ`**: the closure in
`W^{1,p}(Ω)` of the restrictions to `Ω` of the smooth compactly supported functions on the whole
space whose topological support is disjoint from `closure Γ`. These generators are the test
functions supported in the open set `(closure Γ)ᶜ`, viewed as test functions on the whole space.
No regularity of `Ω` or `Γ` is assumed. -/
def w1pVanishingOnSubmodule (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (Γ : Set E) : ClosedSubmodule ℝ (W1p mu Omega p) :=
  (LinearMap.range ((W1p.restrictL (le_top : Omega ≤ ⊤)).toLinearMap ∘ₗ
    W1p.ofTestFunctionₗ mu ⊤ p ∘ₗ ContinuousLinearMap.toLinearMap
      (TestFunction.monoCLM ℝ : 𝓓((Closeds.closure Γ).compl, ℝ) →L[ℝ] 𝓓((⊤ : Opens E), ℝ)))).closure

/-- `W^{1,p}_Γ(Ω)` is the closure of the set of restrictions to `Ω` of the test functions on the
whole space whose support is disjoint from `closure Γ`. -/
theorem coe_w1pVanishingOnSubmodule :
    (w1pVanishingOnSubmodule mu Omega p Γ : Set (W1p mu Omega p)) =
      closure ((fun φ : 𝓓((⊤ : Opens E), ℝ) =>
          W1p.restrictL (le_top : Omega ≤ ⊤) (W1p.ofTestFunctionₗ mu ⊤ p φ)) ''
        {φ | Disjoint (tsupport φ) (closure Γ)}) := by
  rw [w1pVanishingOnSubmodule, Submodule.coe_closure, LinearMap.coe_range]
  congr 1
  ext u
  simp only [mem_range, mem_image, LinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_coe]
  -- The inclusion of test functions supported in `(closure Γ)ᶜ` does not change the function.
  have hmono (φ : 𝓓((Closeds.closure Γ).compl, ℝ)) :
      ⇑(TestFunction.monoCLM ℝ φ : 𝓓((⊤ : Opens E), ℝ)) = φ := by
    simp [TestFunction.monoCLM_apply]
  constructor
  · rintro ⟨φ, rfl⟩
    refine ⟨TestFunction.monoCLM ℝ φ, ?_, rfl⟩
    rw [mem_ofPred, hmono]
    exact subset_compl_iff_disjoint_right.1 φ.tsupport_subset
  · rintro ⟨φ, hφ, rfl⟩
    refine ⟨⟨φ, φ.contDiff, φ.hasCompactSupport, subset_compl_iff_disjoint_right.2 hφ⟩, ?_⟩
    congr 2
    exact DFunLike.coe_injective (hmono _)

/-- **The generators lie in `W^{1,p}_Γ(Ω)`**: the restriction to `Ω` of a test function on the
whole space whose support is disjoint from `closure Γ`. -/
theorem W1p.restrictL_ofTestFunctionₗ_mem_w1pVanishingOnSubmodule {φ : 𝓓((⊤ : Opens E), ℝ)}
    (hφ : Disjoint (tsupport φ) (closure Γ)) :
    W1p.restrictL (le_top : Omega ≤ ⊤) (W1p.ofTestFunctionₗ mu ⊤ p φ) ∈
      w1pVanishingOnSubmodule mu Omega p Γ := by
  rw [← SetLike.mem_coe, coe_w1pVanishingOnSubmodule]
  exact subset_closure ⟨φ, hφ, rfl⟩

/-- **Minimality of the closure**: a closed set containing the restriction to `Ω` of every test
function whose support is disjoint from `closure Γ` contains all of `W^{1,p}_Γ(Ω)`. -/
theorem w1pVanishingOnSubmodule_subset_of_isClosed {s : Set (W1p mu Omega p)} (hs : IsClosed s)
    (h : ∀ φ : 𝓓((⊤ : Opens E), ℝ), Disjoint (tsupport φ) (closure Γ) →
      W1p.restrictL (le_top : Omega ≤ ⊤) (W1p.ofTestFunctionₗ mu ⊤ p φ) ∈ s) :
    (w1pVanishingOnSubmodule mu Omega p Γ : Set (W1p mu Omega p)) ⊆ s := by
  rw [coe_w1pVanishingOnSubmodule]
  exact closure_minimal (by rintro _ ⟨φ, hφ, rfl⟩; exact h φ hφ) hs

/-- **Functions vanishing on `Γ` have zero boundary values on `Γ`, for any trace operator.** Let
`T : W^{1,p}(Ω) → Lᵖ(σ)` be a continuous linear map that sends the restriction to `Ω` of every test
function `φ` on the whole space to `φ` itself, `σ`-almost everywhere. Then `T u` vanishes
`σ`-almost everywhere on `Γ` for every `u ∈ W^{1,p}_Γ(Ω)`. No regularity of `Ω` or of `Γ` is
assumed; the traces on a Lipschitz domain are the main examples. -/
theorem W1p.apply_ae_eq_zero_of_mem_w1pVanishingOnSubmodule {σ : Measure E}
    {T : W1p mu Omega p →L[ℝ] Lp ℝ p σ}
    (hT : ∀ φ : 𝓓((⊤ : Opens E), ℝ),
      T (W1p.restrictL (le_top : Omega ≤ ⊤) (W1p.ofTestFunctionₗ mu ⊤ p φ)) =ᵐ[σ] φ)
    {u : W1p mu Omega p} (hu : u ∈ w1pVanishingOnSubmodule mu Omega p Γ) :
    T u =ᵐ[σ.restrict Γ] 0 := by
  -- Vanishing on `Γ` is the kernel of a continuous linear map, hence a closed condition.
  let R := (LpToLpRestrictCLM E ℝ ℝ σ p Γ).comp T
  have hclosed : IsClosed {v : W1p mu Omega p | R v = 0} := isClosed_eq R.continuous
    continuous_const
  have h := w1pVanishingOnSubmodule_subset_of_isClosed hclosed (fun φ hφ => ?_) hu
  · exact (LpToLpRestrictCLM_eq_zero_iff (𝕜 := ℝ) Γ _).1 h
  -- The boundary values of a generator are the generator itself, which is zero on `closure Γ`.
  rw [mem_ofPred, ContinuousLinearMap.comp_apply, LpToLpRestrictCLM_eq_zero_iff (𝕜 := ℝ)]
  filter_upwards [ae_restrict_of_ae (hT φ), ae_restrict_of_ae_restrict_of_subset subset_closure
      (ae_restrict_mem (μ := σ) isClosed_closure.measurableSet)] with x hx hxΓ
  rw [hx, Pi.zero_apply]
  exact image_eq_zero_of_notMem_tsupport (hφ.notMem_of_mem_right hxΓ)

/-- **The Sobolev space `W^{1,p}_Γ(Ω)`** as a type: the subspace `w1pVanishingOnSubmodule`, with
the normed structure inherited from `W^{1,p}(Ω)`. For `p = 2` it is a Hilbert space, the test
space of the mixed boundary value problem. -/
abbrev W1pVanishingOn (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (Γ : Set E) := (w1pVanishingOnSubmodule mu Omega p Γ).toSubmodule

/-- Shortcut instance for the norm `W^{1,p}_Γ(Ω)` inherits through the nested Sobolev subspaces;
instance search does not find the dual-space norm on its own without it. -/
noncomputable instance instSeminormedAddCommGroupW1pVanishingOn :
    SeminormedAddCommGroup (W1pVanishingOn mu Omega p Γ) := inferInstance

/-- Shortcut instance for the scalar action `W^{1,p}_Γ(Ω)` inherits through the nested Sobolev
subspaces. -/
noncomputable instance instNormedSpaceW1pVanishingOn :
    NormedSpace ℝ (W1pVanishingOn mu Omega p Γ) := inferInstance

/-- `W^{1,p}_Γ(Ω)` is complete: it is a closed subspace of the complete space `W^{1,p}(Ω)`. -/
instance : CompleteSpace (W1pVanishingOn mu Omega p Γ) :=
  (w1pVanishingOnSubmodule mu Omega p Γ).isClosed.completeSpace_coe

/-- **Sequential characterization of `W^{1,p}_Γ(Ω)`**: an element of `W^{1,p}(Ω)` lies in
`W^{1,p}_Γ(Ω)` exactly when it is the limit of the restrictions to `Ω` of a sequence of test
functions on the whole space whose supports are disjoint from `closure Γ`. -/
theorem mem_w1pVanishingOnSubmodule_iff_exists_seq_tendsto {u : W1p mu Omega p} :
    u ∈ w1pVanishingOnSubmodule mu Omega p Γ ↔
      ∃ φ : ℕ → 𝓓((⊤ : Opens E), ℝ), (∀ k, Disjoint (tsupport (φ k)) (closure Γ)) ∧
        Tendsto (fun k => W1p.restrictL (le_top : Omega ≤ ⊤) (W1p.ofTestFunctionₗ mu ⊤ p (φ k)))
          atTop (𝓝 u) := by
  rw [← SetLike.mem_coe, coe_w1pVanishingOnSubmodule, mem_closure_iff_seq_limit]
  constructor
  · rintro ⟨w, hw, hlim⟩
    choose φ hφ hφw using hw
    exact ⟨φ, hφ, by simpa only [hφw] using hlim⟩
  · rintro ⟨φ, hφ, hlim⟩
    exact ⟨_, fun k => ⟨φ k, hφ k, rfl⟩, hlim⟩

/-! ### Dependence on `Γ` -/

/-- **`W^{1,p}_Γ(Ω)` shrinks as `Γ` grows**: if `Γ ⊆ Γ'`, every generator for `Γ'` is a
generator for `Γ`, so `W^{1,p}_{Γ'}(Ω) ≤ W^{1,p}_Γ(Ω)`. -/
theorem w1pVanishingOnSubmodule_antitone :
    Antitone (w1pVanishingOnSubmodule mu Omega p) := fun Γ _ hΓ _ hu =>
  w1pVanishingOnSubmodule_subset_of_isClosed (w1pVanishingOnSubmodule mu Omega p Γ).isClosed
    (fun _ hφ => W1p.restrictL_ofTestFunctionₗ_mem_w1pVanishingOnSubmodule
      (hφ.mono_right (closure_mono hΓ))) hu

/-- `W^{1,p}_Γ(Ω)` depends on `Γ` only through its closure. -/
@[simp]
theorem w1pVanishingOnSubmodule_closure :
    w1pVanishingOnSubmodule mu Omega p (closure Γ) = w1pVanishingOnSubmodule mu Omega p Γ :=
  le_antisymm (w1pVanishingOnSubmodule_antitone subset_closure) fun _ hu =>
    w1pVanishingOnSubmodule_subset_of_isClosed
      (w1pVanishingOnSubmodule mu Omega p (closure Γ)).isClosed
      (fun _ hφ => W1p.restrictL_ofTestFunctionₗ_mem_w1pVanishingOnSubmodule
        (by rwa [closure_closure])) hu

/-! ### Comparison with `W^{1,p}_0(Ω)` -/

/-- **Restriction maps `W^{1,p}_0(U)` into `W^{1,p}_Γ(Ω)` when `Ω ⊆ U` and `Γ` misses `U`.** A test
function supported in `U`, extended by zero to the whole space, has support disjoint from
`closure Γ`, since an open set disjoint from `Γ` is disjoint from its closure, so its restriction to
`Ω` is a generator. -/
theorem W1p.restrictL_mem_w1pVanishingOnSubmodule {U : Opens E} (hΩU : Omega ≤ U)
    (hΓ : Disjoint Γ U) {u : W1p mu U p} (hu : u ∈ w1p0Submodule mu U p) :
    W1p.restrictL hΩU u ∈ w1pVanishingOnSubmodule mu Omega p Γ := by
  refine w1p0Submodule_subset_of_isClosed ((w1pVanishingOnSubmodule mu Omega p Γ).isClosed.preimage
    (W1p.restrictL hΩU).continuous) (fun ψ => ?_) hu
  -- `ψ`, viewed as a test function on the whole space, is a generator.
  obtain ⟨φ, hφ⟩ : ∃ φ : 𝓓((⊤ : Opens E), ℝ), ⇑φ = ψ :=
    ⟨⟨ψ, ψ.contDiff, ψ.hasCompactSupport, subset_univ _⟩, rfl⟩
  have h := W1p.restrictL_ofTestFunctionₗ_mem_w1pVanishingOnSubmodule (mu := mu) (p := p)
    (Omega := Omega) (φ := φ)
    (hφ ▸ (hΓ.closure_left U.isOpen).symm.mono_left ψ.tsupport_subset)
  rwa [← W1p.restrictL_restrictL (le_top : U ≤ ⊤) hΩU,
    W1p.restrictL_ofTestFunctionₗ_eq_of_eqOn le_top (ψ := ψ) (hφ ▸ eqOn_refl _ _)] at h

/-- **`W^{1,p}_0(Ω) ≤ W^{1,p}_Γ(Ω)` when `Γ` misses `Ω`.** A test function supported in `Ω` has
support disjoint from `closure Γ`, since an open set disjoint from `Γ` is disjoint from its
closure. In particular this holds for every `Γ ⊆ frontier Ω`. -/
theorem w1p0Submodule_le_w1pVanishingOnSubmodule (hΓ : Disjoint Γ Omega) :
    w1p0Submodule mu Omega p ≤ w1pVanishingOnSubmodule mu Omega p Γ := fun u hu => by
  simpa only [W1p.restrictL_self] using W1p.restrictL_mem_w1pVanishingOnSubmodule le_rfl hΓ hu

/-- **At the whole frontier, `W^{1,p}_Γ(Ω)` is `W^{1,p}_0(Ω)`**, for every open `Ω` and every
`1 ≤ p ≤ ∞`. A test function on the whole space whose support misses the frontier agrees on `Ω`
with its indicator along `Ω`, which is a test function supported in `Ω`; conversely a test function
supported in `Ω` has support disjoint from the frontier. -/
@[simp]
theorem w1pVanishingOnSubmodule_frontier :
    w1pVanishingOnSubmodule mu Omega p (frontier (Omega : Set E)) = w1p0Submodule mu Omega p := by
  refine le_antisymm (fun u hu => ?_)
    (w1p0Submodule_le_w1pVanishingOnSubmodule (disjoint_frontier_iff_isOpen.2 Omega.isOpen))
  refine w1pVanishingOnSubmodule_subset_of_isClosed (w1p0Submodule mu Omega p).isClosed
    (fun φ hφ => ?_) hu
  rw [isClosed_frontier.closure_eq] at hφ
  -- The indicator of `φ` along `Ω` is supported in `closure Ω ∩ tsupport φ`, which misses the
  -- frontier, hence lies in `Ω`.
  have hsupp : tsupport ((Omega : Set E).indicator φ) ⊆ Omega := fun x hx => by
    have hx' := closure_inter_subset_inter_closure _ _
      ((closure_mono (support_indicator (s := (Omega : Set E)) (f := φ)).le) hx)
    by_contra hxO
    exact hφ.notMem_of_mem_left hx'.2
      ⟨hx'.1, fun hxi => hxO (Omega.isOpen.interior_eq ▸ hxi)⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : 𝓓(Omega, ℝ), ⇑ψ = (Omega : Set E).indicator φ :=
    ⟨⟨(Omega : Set E).indicator φ, φ.contDiff.indicator_of_disjoint_frontier hφ,
      φ.hasCompactSupport.mono fun x hx => by
        rw [support_indicator] at hx
        exact hx.2, hsupp⟩, rfl⟩
  rw [W1p.restrictL_ofTestFunctionₗ_eq_of_eqOn le_top (ψ := ψ) fun x hx => by
    rw [hψ, indicator_of_mem hx]]
  exact W1p.ofTestFunctionₗ_mem_w1p0Submodule ψ

/-! ### Multiplication by smooth functions -/

/-- **`W^{1,p}_Γ(Ω)` is stable under multiplication by a smooth function** `ψ` bounded together
with its gradient on `Ω`. The product of `ψ` with a generator is again a generator, since its
support lies in that of the generator, and continuity extends this to the closure. -/
theorem W1p.contDiffSMul_mem_w1pVanishingOnSubmodule {psi : E → ℝ} {M : ℝ}
    (hpsi : ContDiff ℝ ∞ psi) (hM : 0 ≤ M) (hpsiM : ∀ x ∈ Omega, |psi x| ≤ M)
    (hgradM : ∀ x ∈ Omega, ‖∇ psi x‖ ≤ M) {u : W1p mu Omega p}
    (hu : u ∈ w1pVanishingOnSubmodule mu Omega p Γ) :
    W1p.contDiffSMul psi hpsi hM hpsiM hgradM u ∈ w1pVanishingOnSubmodule mu Omega p Γ := by
  have hclosed : IsClosed (W1p.contDiffSMulL psi hpsi hM hpsiM hgradM ⁻¹'
      (w1pVanishingOnSubmodule mu Omega p Γ : Set (W1p mu Omega p))) :=
    (w1pVanishingOnSubmodule mu Omega p Γ).isClosed.preimage
      (W1p.contDiffSMulL psi hpsi hM hpsiM hgradM).continuous
  have h := w1pVanishingOnSubmodule_subset_of_isClosed hclosed (fun φ hφ => ?_) hu
  · simpa only [mem_preimage, SetLike.mem_coe, W1p.contDiffSMulL_apply] using h
  -- The product `ψ φ` is a test function on the whole space with support inside that of `φ`.
  obtain ⟨Φ, hΦφ⟩ : ∃ Φ : 𝓓((⊤ : Opens E), ℝ), ⇑Φ = fun x => psi x * φ x :=
    ⟨⟨fun x => psi x * φ x, hpsi.mul φ.contDiff, φ.hasCompactSupport.mul_left, subset_univ _⟩,
      rfl⟩
  have hΦ : W1p.contDiffSMul psi hpsi hM hpsiM hgradM
      (W1p.restrictL (le_top : Omega ≤ ⊤) (W1p.ofTestFunctionₗ mu ⊤ p φ)) =
      W1p.restrictL (le_top : Omega ≤ ⊤) (W1p.ofTestFunctionₗ mu ⊤ p Φ) := by
    refine W1p.ext_value (Lp.ext ?_)
    filter_upwards [W1p.value_contDiffSMul_ae hpsi hM hpsiM hgradM
        (W1p.restrictL (le_top : Omega ≤ ⊤) (W1p.ofTestFunctionₗ mu ⊤ p φ)),
      W1p.value_restrictL_ofTestFunctionₗ_ae (mu := mu) (p := p) (le_top : Omega ≤ ⊤) φ,
      W1p.value_restrictL_ofTestFunctionₗ_ae (mu := mu) (p := p) (le_top : Omega ≤ ⊤) Φ]
      with x h h₁ h₂
    rw [h, h₁, h₂, smul_eq_mul, hΦφ]
  simp only [mem_preimage, SetLike.mem_coe, W1p.contDiffSMulL_apply, hΦ]
  exact W1p.restrictL_ofTestFunctionₗ_mem_w1pVanishingOnSubmodule
    (hΦφ ▸ hφ.mono_left (tsupport_mul_subset_right (f := psi) (g := φ)))

/-! ### Compactly supported functions vanishing near `Γ` -/

/-- **A compactly supported Sobolev function vanishing near `Γ` restricts into `W^{1,p}_Γ(Ω)`.**
Let `1 ≤ p < ∞`. If `w ∈ W^{1,p}(E)` vanishes almost everywhere outside a compact set `K` disjoint
from `closure Γ`, then the restriction of `w` to any open `Ω` lies in `W^{1,p}_Γ(Ω)`. No relation
between `Ω` and `Γ` is assumed. -/
theorem W1p.restrictL_mem_w1pVanishingOnSubmodule_of_isCompact (hp : p ≠ (∞ : ℝ≥0∞)) {K : Set E}
    (hK : IsCompact K) (hKΓ : Disjoint K (closure Γ)) {w : W1p mu ⊤ p}
    (hw : ∀ᵐ x ∂mu, x ∉ K → W1p.value w x = 0) :
    W1p.restrictL (le_top : Omega ≤ ⊤) w ∈ w1pVanishingOnSubmodule mu Omega p Γ := by
  -- A cutoff `χ`, equal to one near `K` and supported away from `closure Γ`.
  obtain ⟨chi, M, hchi, -, hchi_one, -, hchi_ts, hM0, hchiM, hgradM⟩ :=
    hK.exists_contDiff_cutoff_with_bounds isClosed_closure.isOpen_compl
      (subset_compl_iff_disjoint_right.2 hKΓ)
  set T : W1p mu ⊤ p →L[ℝ] W1p mu Omega p := (W1p.restrictL (le_top : Omega ≤ ⊤)).comp
    (W1p.contDiffSMulL chi hchi hM0 (fun x _ => hchiM x) fun x _ => hgradM x) with hTdef
  -- `T` sends each test function `φ` to the restriction of the generator `χ φ`, so it maps their
  -- closure `W^{1,p}_0(E) = W^{1,p}(E)` into `W^{1,p}_Γ(Ω)`.
  have hw0 : w ∈ w1p0Submodule mu ⊤ p := by
    rw [w1p0Submodule_top_eq_top hp]
    trivial
  have hT : T w ∈ w1pVanishingOnSubmodule mu Omega p Γ := by
    refine w1p0Submodule_subset_of_isClosed
      ((w1pVanishingOnSubmodule mu Omega p Γ).isClosed.preimage T.continuous) (fun φ => ?_) hw0
    obtain ⟨Φ, hΦ⟩ : ∃ Φ : 𝓓((⊤ : Opens E), ℝ), ⇑Φ = chi * ⇑φ :=
      ⟨⟨chi * φ, hchi.mul φ.contDiff, φ.hasCompactSupport.mul_left, subset_univ _⟩, rfl⟩
    rw [mem_preimage, hTdef, ContinuousLinearMap.comp_apply, W1p.contDiffSMulL_apply,
      W1p.contDiffSMul_ofTestFunctionₗ hchi hM0 _ _ φ Φ hΦ]
    exact W1p.restrictL_ofTestFunctionₗ_mem_w1pVanishingOnSubmodule
      (subset_compl_iff_disjoint_right.1 (hΦ ▸ tsupport_mul_subset_left.trans hchi_ts))
  -- Since `χ = 1` on `K`, outside of which `w` vanishes, `χ w = w`.
  have hcw : W1p.contDiffSMulL chi hchi hM0 (fun x _ => hchiM x) (fun x _ => hgradM x) w = w := by
    refine W1p.ext_value (Lp.ext ?_)
    filter_upwards [W1p.value_contDiffSMul_ae hchi hM0 (fun x _ => hchiM x)
      (fun x _ => hgradM x) w, ae_restrict_of_ae hw] with x h1 h2
    rw [W1p.contDiffSMulL_apply, h1]
    by_cases hxK : x ∈ K
    · have hx1 : chi x = 1 := interior_subset (hchi_one hxK)
      rw [hx1, one_smul]
    · rw [h2 hxK, smul_zero]
  rwa [hTdef, ContinuousLinearMap.comp_apply, hcw] at hT

/-- **A compactly supported locally Lipschitz function vanishing near `Γ` lies in
`W^{1,p}_Γ(Ω)`.** Let `1 ≤ p < ∞`. If `G` is locally Lipschitz with compact support disjoint from
`closure Γ`, then every `u ∈ W^{1,p}(Ω)` whose value agrees with `G` almost everywhere on `Ω` lies
in `W^{1,p}_Γ(Ω)`. Unlike the generators of `W^{1,p}_Γ(Ω)`, `G` need not be smooth: composites of
test functions with Lipschitz changes of variables are of this form. -/
theorem W1p.mem_w1pVanishingOnSubmodule_of_locallyLipschitz (hp : p ≠ (∞ : ℝ≥0∞)) {G : E → ℝ}
    (hG : LocallyLipschitz G) (hGc : HasCompactSupport G)
    (hGΓ : Disjoint (tsupport G) (closure Γ)) {u : W1p mu Omega p}
    (hu : W1p.value u =ᵐ[mu.restrict Omega] G) :
    u ∈ w1pVanishingOnSubmodule mu Omega p Γ := by
  have hμ : mu.restrict ((⊤ : Opens E) : Set E) = mu := by simp
  -- `G` is Lipschitz on a compact neighbourhood of its support, so its gradient is bounded.
  obtain ⟨K', hK', hGK'⟩ := exists_compact_superset hGc.isCompact
  obtain ⟨L, hL⟩ := hG.locallyLipschitzOn.exists_lipschitzOnWith_of_compact hK'
  have hbound (x : E) : ‖∇ G x‖ ≤ L := by
    rw [_root_.gradient, LinearIsometryEquiv.norm_map]
    by_cases hx : x ∈ tsupport G
    · exact norm_fderiv_le_of_lipschitzOn ℝ (mem_interior_iff_mem_nhds.1 (hGK' hx)) hL
    · rw [fderiv_of_notMem_tsupport ℝ hx, norm_zero]
      exact L.coe_nonneg
  have hgrad : MemLp (∇ G) p mu :=
    ((hGc.fderiv ℝ).comp_left (map_zero (InnerProductSpace.toDual ℝ E).symm)).memLp_of_bound
      ((InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp
        (measurable_fderiv ℝ G)).aestronglyMeasurable L (ae_of_all _ hbound)
  -- `G` is the value of some `w ∈ W^{1,p}(E)`, whose restriction to `Ω` is `u`.
  obtain ⟨w, hw, -⟩ := W1p.exists_value_gradient_ae_eq_of_locallyLipschitzOn (mu := mu) (p := p)
    (Omega := ⊤) hG.locallyLipschitzOn
    (by rw [hμ]; exact hG.continuous.memLp_of_hasCompactSupport hGc) (by rwa [hμ])
  replace hw : ⇑(W1p.value w) =ᵐ[mu] G :=
    ((ae_restrict_iff' (⊤ : Opens E).isOpen.measurableSet).1 hw).mono fun x hx => hx trivial
  have h := W1p.restrictL_mem_w1pVanishingOnSubmodule_of_isCompact (Omega := Omega) hp
    hGc.isCompact hGΓ (w := w) (hw.mono fun x hx hxK => by
      rw [hx]
      exact image_eq_zero_of_notMem_tsupport hxK)
  rwa [W1p.restrictL_eq_of_value_ae_eq le_top ((hw.filter_mono ae_restrict_le).trans hu.symm)] at h

/-! ### Shortcut instances for the Hilbert space `W^{1,2}_Γ(Ω)`

The instances below are `local`, so they take part in instance search only in a file that
registers them with `attribute [local instance]`, as for `W^{1,2}_0(Ω)`. -/

/-- Shortcut instance for the normed group structure of `W^{1,p}_Γ(Ω)`, the separated form of
`instSeminormedAddCommGroupW1pVanishingOn`. Instance search can time out on it while elaborating
the arguments of an abstract Hilbert space lemma. -/
noncomputable local instance W1pVanishingOn.instNormedAddCommGroup :
    NormedAddCommGroup (W1pVanishingOn mu Omega p Γ) := inferInstance

/-- Shortcut instance for the Hilbert space structure of `W^{1,2}_Γ(Ω)`, inherited from
`W^{1,2}(Ω)`. A file that applies abstract Hilbert space results to `W^{1,2}_Γ(Ω)` registers it
together with `W1pVanishingOn.instNormedAddCommGroup`. -/
noncomputable local instance W1pVanishingOn.instInnerProductSpace :
    InnerProductSpace ℝ (W1pVanishingOn mu Omega 2 Γ) := inferInstance

end TauCeti
