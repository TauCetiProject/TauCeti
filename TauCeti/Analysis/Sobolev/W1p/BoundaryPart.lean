/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Multiplication
public import TauCeti.Analysis.Sobolev.W1p.Restriction
import TauCeti.Analysis.Calculus.ContDiff.Indicator

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
bounded together with its gradient preserves it, as for `W^{1,p}_0(Ω)`.

## Main declarations

* `TauCeti.w1pVanishingOnSubmodule`: the closed subspace `W^{1,p}_Γ(Ω)` of `W^{1,p}(Ω)`.
* `TauCeti.W1p.restrictL_ofTestFunctionₗ_mem_w1pVanishingOnSubmodule` and
  `TauCeti.w1pVanishingOnSubmodule_subset_of_isClosed`: the generators lie in it, and a closed set
  containing them contains all of it.
* `TauCeti.mem_w1pVanishingOnSubmodule_iff_exists_seq_tendsto`: its elements are the limits of
  sequences of generators.
* `TauCeti.w1pVanishingOnSubmodule_antitone` and `TauCeti.w1pVanishingOnSubmodule_closure`: it is
  antitone in `Γ` and depends only on `closure Γ`.
* `TauCeti.w1p0Submodule_le_w1pVanishingOnSubmodule`: it contains `W^{1,p}_0(Ω)` when `Γ` misses
  `Ω`.
* `TauCeti.w1pVanishingOnSubmodule_frontier`: at `Γ = frontier Ω` it is `W^{1,p}_0(Ω)`.
* `TauCeti.W1p.contDiffSMul_mem_w1pVanishingOnSubmodule`: it is stable under multiplication by
  smooth functions bounded with their gradients.

## References

* S. Bauer, D. Pauly, M. Schomburg, *The Maxwell compactness property in bounded weak Lipschitz
  domains with mixed boundary conditions*, SIAM J. Math. Anal. 48 (2016), §2 (the spaces of
  functions vanishing on a boundary part, defined as closures of test functions supported away
  from it).
* P. Grisvard, *Elliptic Problems in Nonsmooth Domains*, §1.5 (mixed boundary conditions).
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Topology Gradient ContDiff

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

/-- **`W^{1,p}_0(Ω) ≤ W^{1,p}_Γ(Ω)` when `Γ` misses `Ω`.** A test function supported in `Ω` has
support disjoint from `closure Γ`, since an open set disjoint from `Γ` is disjoint from its
closure. In particular this holds for every `Γ ⊆ frontier Ω`. -/
theorem w1p0Submodule_le_w1pVanishingOnSubmodule (hΓ : Disjoint Γ Omega) :
    w1p0Submodule mu Omega p ≤ w1pVanishingOnSubmodule mu Omega p Γ := by
  refine fun u hu => w1p0Submodule_subset_of_isClosed
    (w1pVanishingOnSubmodule mu Omega p Γ).isClosed (fun ψ => ?_) hu
  -- `ψ`, viewed as a test function on the whole space, is a generator.
  obtain ⟨φ, hφ⟩ : ∃ φ : 𝓓((⊤ : Opens E), ℝ), ⇑φ = ψ :=
    ⟨⟨ψ, ψ.contDiff, ψ.hasCompactSupport, subset_univ _⟩, rfl⟩
  have h := W1p.restrictL_ofTestFunctionₗ_mem_w1pVanishingOnSubmodule (mu := mu) (p := p)
    (Omega := Omega) (φ := φ)
    (hφ ▸ (hΓ.closure_left Omega.isOpen).symm.mono_left ψ.tsupport_subset)
  rwa [W1p.restrictL_ofTestFunctionₗ_eq_of_eqOn le_top (ψ := ψ) (hφ ▸ eqOn_refl _ _)] at h

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

end TauCeti
