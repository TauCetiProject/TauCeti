/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Order.Filter.EventuallyConst
public import Mathlib.Topology.DiscreteSubset
public import TauCeti.Analysis.Meromorphic.PrincipalPart
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.DerivedSet
import Mathlib.Topology.Homeomorph.Lemmas
import TauCeti.Analysis.Complex.RemovableSingularity
import TauCeti.Analysis.Complex.Runge.Laurent
import TauCeti.Analysis.Complex.UniformLimit
import TauCeti.Analysis.Normed.Module.Exhaustion
import TauCeti.Topology.Codiscrete

/-!
# The Mittag-Leffler theorem and holomorphic functions with prescribed isolated singularities

Let `Ω ⊆ ℂ` be an arbitrary subset (not necessarily open), let `E ⊆ Ω` be a relatively closed
discrete subset (`Eᶜ ∈ Filter.codiscreteWithin Ω`), and let `F` be a complex Banach space. Given at
each point `a : E` a local singular germ `P a : ℂ → F` complex-differentiable on a punctured
neighborhood of `a.val` (allowing poles of arbitrary order as well as essential singularities), this
file constructs a global function `f : ℂ → F` complex-differentiable on `Ω \ E` such that at every
`a : E` the difference `f - P a` agrees on `𝓝[≠] a.val` with a function complex-analytic at
`a.val`. Openness of `Ω` is not needed for the existence theorems: whenever `E ⊆ Ω` satisfies
`Eᶜ ∈ Filter.codiscreteWithin Ω`, the subset `Ω` avoids `derivedSet E`, so the open-set
construction on `(derivedSet E)ᶜ` restricts to `Ω`.

Specializing to meromorphic germs `MeromorphicAt (P a) a.val` yields the **Mittag-Leffler theorem**
on arbitrary subsets of `ℂ` (`TauCeti.exists_meromorphic_prescribed_principal_parts`, together with
its normal-form refinement `TauCeti.exists_meromorphicNFOn_prescribed_principal_parts` and scalar
polynomial principal-part form `TauCeti.exists_meromorphic_principalPart_eq`).

The predicate `TauCeti.HasPrescribedSingularities f Ω E P` packages the realization condition and
records its algebraic and geometric properties: congruence and invariance under changing the
prescribed germs by analytic germs, closure under linear operations, restriction to subsets,
compatibility with precomposition (including pullback along nowhere-locally-constant analytic maps,
translations, and nonzero complex dilations), characterization via
`TauCeti.meromorphicGerms.principalPart`, and uniqueness of solutions on `Ω \ E` modulo functions
complex-differentiable on all of `Ω` (without requiring openness of `Ω` or completeness of `F`).

## Main definitions and results

* `TauCeti.HasPrescribedSingularities`: `f` is complex-differentiable on `Ω \ E` and `f - P a`
  agrees on `𝓝[≠] a.val` with an analytic function at `a.val` for every `a : E`.
* `TauCeti.HasPrescribedSingularities.comp_analyticOnNhd`: pullback along an analytic map
  `φ : ℂ → ℂ` not locally constant at points of `Ω' ∩ φ ⁻¹' E`.
* `TauCeti.HasPrescribedSingularities.exists_differentiableOn_eqOn_sub`,
  `TauCeti.HasPrescribedSingularities.iff_exists_differentiableOn_eqOn_add`, and
  `TauCeti.exists_differentiableOn_eqOn_sub_of_principalPart_mk_eq`: uniqueness modulo functions
  complex-differentiable on `Ω` (for general `Ω`) and the affine-coset characterization on open
  sets.
* `TauCeti.exists_hasPrescribedSingularities_of_eventually_differentiableAt` and
  `TauCeti.exists_holomorphic_prescribed_isolated_singularities`: global realization of arbitrary
  isolated singularities (including essential singularities) on `Ω \ E`.
* `TauCeti.hasPrescribedSingularities_eval_inv_sub_iff`,
  `TauCeti.exists_meromorphic_prescribed_principal_parts`,
  `TauCeti.exists_meromorphicNFOn_prescribed_principal_parts`, and
  `TauCeti.exists_meromorphic_principalPart_eq`: polynomial principal-part characterization and the
  Mittag-Leffler theorem on subsets of `ℂ`.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorems 12.1 and 15.7.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 13.10.
* L. V. Ahlfors, *Complex Analysis*, 3rd ed., Chapter 5, §2.1.
* J. B. Conway, *Functions of One Complex Variable I*, 2nd ed., Springer, 1978, Chapter VIII, §3.
-/

public section

open Complex Filter Function Metric Polynomial Set
open scoped ENNReal Topology

namespace TauCeti

section Predicate

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- `HasPrescribedSingularities f Ω E P` states that `f : ℂ → F` is complex-differentiable on
`Ω \ E` and, at each marked point `a : E`, differs on a punctured neighborhood of `a.val` from the
prescribed local germ `P a` by a function complex-analytic at `a.val`. -/
def HasPrescribedSingularities (f : ℂ → F) (Ω E : Set ℂ) (P : E → ℂ → F) : Prop :=
  DifferentiableOn ℂ f (Ω \ E) ∧
    ∀ a : E, ∃ g : ℂ → F, AnalyticAt ℂ g a.val ∧ ∀ᶠ z in 𝓝[≠] a.val, f z - P a z = g z

/-- Explicit characterization of `HasPrescribedSingularities`. -/
theorem hasPrescribedSingularities_iff {f : ℂ → F} {Ω E : Set ℂ} {P : E → ℂ → F} :
    HasPrescribedSingularities f Ω E P ↔
      DifferentiableOn ℂ f (Ω \ E) ∧
        ∀ a : E, ∃ g : ℂ → F, AnalyticAt ℂ g a.val ∧ ∀ᶠ z in 𝓝[≠] a.val, f z - P a z = g z :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

namespace HasPrescribedSingularities

/-- A function realizing prescribed singularities along `E` is complex-differentiable on `Ω \ E`. -/
theorem differentiableOn {f : ℂ → F} {Ω E : Set ℂ} {P : E → ℂ → F}
    (hf : HasPrescribedSingularities f Ω E P) : DifferentiableOn ℂ f (Ω \ E) :=
  hf.1

/-- At each `a : E`, `f - P a` agrees on `𝓝[≠] a.val` with a function complex-analytic at `a.val`.
-/
theorem exists_analyticAt_sub {f : ℂ → F} {Ω E : Set ℂ} {P : E → ℂ → F}
    (hf : HasPrescribedSingularities f Ω E P) (a : E) :
    ∃ g : ℂ → F, AnalyticAt ℂ g a.val ∧ ∀ᶠ z in 𝓝[≠] a.val, f z - P a z = g z :=
  hf.2 a

/-- With empty singular locus, `HasPrescribedSingularities` reduces to complex differentiability on
`Ω`. -/
@[simp]
theorem _root_.TauCeti.hasPrescribedSingularities_empty {f : ℂ → F} {Ω : Set ℂ}
    {P : (∅ : Set ℂ) → ℂ → F} :
    HasPrescribedSingularities f Ω ∅ P ↔ DifferentiableOn ℂ f Ω := by
  simp [hasPrescribedSingularities_iff]

/-- The zero function realizes zero singularity data. -/
@[simp]
theorem zero (Ω E : Set ℂ) : HasPrescribedSingularities (0 : ℂ → F) Ω E 0 :=
  ⟨differentiableOn_const 0, fun _ => ⟨0, analyticAt_const, by simp⟩⟩

/-- Congruence in `f`: replacing `f₁` by `f₂` agreeing with `f₁` on `Ω \ E` and on `𝓝[≠] a.val`
for every `a : E` preserves `HasPrescribedSingularities`. -/
theorem congr {f₁ f₂ : ℂ → F} {Ω E : Set ℂ} {P : E → ℂ → F}
    (hf₁ : HasPrescribedSingularities f₁ Ω E P) (hf : EqOn f₁ f₂ (Ω \ E))
    (hfE : ∀ a : E, f₁ =ᶠ[𝓝[≠] a.val] f₂) :
    HasPrescribedSingularities f₂ Ω E P := by
  refine ⟨hf₁.1.congr hf.symm, fun a => ?_⟩
  obtain ⟨g, hg, heq⟩ := hf₁.2 a
  refine ⟨g, hg, ?_⟩
  filter_upwards [hfE a, heq] with z hzf hz
  rwa [← hzf]

/-- On an open set `Ω` with `E ⊆ Ω` and `Eᶜ ∈ Filter.codiscreteWithin Ω`, replacing `f₁` by any
`f₂` agreeing with `f₁` on `Ω \ E` preserves `HasPrescribedSingularities`. -/
theorem congr_of_eqOn {f₁ f₂ : ℂ → F} {Ω E : Set ℂ} {P : E → ℂ → F}
    (hf₁ : HasPrescribedSingularities f₁ Ω E P) (hΩ : IsOpen Ω) (hEΩ : E ⊆ Ω)
    (hE : Eᶜ ∈ codiscreteWithin Ω) (hf : EqOn f₁ f₂ (Ω \ E)) :
    HasPrescribedSingularities f₂ Ω E P :=
  hf₁.congr hf fun a =>
    mem_of_superset (hΩ.sdiff_mem_nhdsNE_of_compl_mem_codiscreteWithin hE (hEΩ a.property)) hf

/-- Realizing prescribed singularities is closed under pointwise addition. -/
theorem add {f₁ f₂ : ℂ → F} {Ω E : Set ℂ} {P₁ P₂ : E → ℂ → F}
    (h₁ : HasPrescribedSingularities f₁ Ω E P₁) (h₂ : HasPrescribedSingularities f₂ Ω E P₂) :
    HasPrescribedSingularities (f₁ + f₂) Ω E (P₁ + P₂) := by
  refine ⟨h₁.1.add h₂.1, fun a => ?_⟩
  obtain ⟨g₁, hg₁, heq₁⟩ := h₁.2 a
  obtain ⟨g₂, hg₂, heq₂⟩ := h₂.2 a
  refine ⟨g₁ + g₂, hg₁.add hg₂, ?_⟩
  filter_upwards [heq₁, heq₂] with z hz₁ hz₂
  simp only [Pi.add_apply, add_sub_add_comm, hz₁, hz₂]

/-- Realizing prescribed singularities is closed under negation. -/
theorem neg {f : ℂ → F} {Ω E : Set ℂ} {P : E → ℂ → F}
    (hf : HasPrescribedSingularities f Ω E P) : HasPrescribedSingularities (-f) Ω E (-P) := by
  refine ⟨hf.1.neg, fun a => ?_⟩
  obtain ⟨g, hg, heq⟩ := hf.2 a
  refine ⟨-g, hg.neg, ?_⟩
  filter_upwards [heq] with z hz
  simp only [Pi.neg_apply, ← hz]
  abel

/-- Negating both `f` and `P` preserves `HasPrescribedSingularities`. -/
@[simp]
theorem _root_.TauCeti.hasPrescribedSingularities_neg_iff {f : ℂ → F} {Ω E : Set ℂ}
    {P : E → ℂ → F} :
    HasPrescribedSingularities (-f) Ω E (-P) ↔ HasPrescribedSingularities f Ω E P :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, HasPrescribedSingularities.neg⟩

/-- Realizing prescribed singularities is closed under pointwise subtraction. -/
theorem sub {f₁ f₂ : ℂ → F} {Ω E : Set ℂ} {P₁ P₂ : E → ℂ → F}
    (h₁ : HasPrescribedSingularities f₁ Ω E P₁) (h₂ : HasPrescribedSingularities f₂ Ω E P₂) :
    HasPrescribedSingularities (f₁ - f₂) Ω E (P₁ - P₂) := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg

/-- Realizing prescribed singularities is closed under complex scalar multiplication. -/
theorem const_smul {f : ℂ → F} {Ω E : Set ℂ} {P : E → ℂ → F}
    (hf : HasPrescribedSingularities f Ω E P) (c : ℂ) :
    HasPrescribedSingularities (c • f) Ω E (c • P) := by
  refine ⟨hf.1.const_smul c, fun a => ?_⟩
  obtain ⟨g, hg, heq⟩ := hf.2 a
  refine ⟨c • g, hg.const_smul, ?_⟩
  filter_upwards [heq] with z hz
  simp only [Pi.smul_apply, ← smul_sub, hz]

/-- **Restriction compatibility.** Restricting the ambient set to `Ω' ⊆ Ω` and the singular locus
to `E' ⊆ E` with `Ω' ∩ E ⊆ E'` preserves `HasPrescribedSingularities`. -/
theorem mono {f : ℂ → F} {Ω Ω' E E' : Set ℂ} {P : E → ℂ → F}
    (hf : HasPrescribedSingularities f Ω E P) (hΩ : Ω' ⊆ Ω) (hEE : E' ⊆ E)
    (hinter : Ω' ∩ E ⊆ E') :
    HasPrescribedSingularities f Ω' E' (fun a => P ⟨a.val, hEE a.property⟩) :=
  ⟨hf.1.mono fun _ ⟨hzΩ', hzE'⟩ => ⟨hΩ hzΩ', fun hzE => hzE' (hinter ⟨hzΩ', hzE⟩)⟩,
    fun a => hf.2 ⟨a.val, hEE a.property⟩⟩

/-- Restricting a solution from `(Ω, E)` to `(Ω', Ω' ∩ E)` for `Ω' ⊆ Ω`. -/
theorem restrict {f : ℂ → F} {Ω Ω' E : Set ℂ} {P : E → ℂ → F}
    (hf : HasPrescribedSingularities f Ω E P) (hΩ : Ω' ⊆ Ω) :
    HasPrescribedSingularities f Ω' (Ω' ∩ E) (fun a => P ⟨a.val, a.property.2⟩) :=
  hf.mono hΩ inter_subset_right Subset.rfl

/-- **Precomposition compatibility.** Precomposing with a map `φ : ℂ → ℂ` complex-differentiable on
`φ ⁻¹' (Ω \ E)` that is complex-analytic and maps `𝓝[≠] a.val` into `𝓝[≠] (φ a.val)` at every
`a : φ ⁻¹' E` pulls back `HasPrescribedSingularities`. -/
theorem comp {f : ℂ → F} {Ω E : Set ℂ} {P : E → ℂ → F}
    (hf : HasPrescribedSingularities f Ω E P) {φ : ℂ → ℂ}
    (hφ_diff : DifferentiableOn ℂ φ (φ ⁻¹' (Ω \ E)))
    (hφ_an : ∀ a : (φ ⁻¹' E : Set ℂ), AnalyticAt ℂ φ a.val)
    (hφ_tend : ∀ a : (φ ⁻¹' E : Set ℂ), Tendsto φ (𝓝[≠] a.val) (𝓝[≠] (φ a.val))) :
    HasPrescribedSingularities (fun z => f (φ z)) (φ ⁻¹' Ω) (φ ⁻¹' E)
      (fun a z => P ⟨φ a.val, a.property⟩ (φ z)) := by
  refine ⟨hf.1.comp hφ_diff fun _ hz => hz, fun a => ?_⟩
  obtain ⟨g, hg, heq⟩ := hf.2 ⟨φ a.val, a.property⟩
  exact ⟨fun z => g (φ z), hg.fun_comp_of_eq (hφ_an a) rfl, (hφ_tend a).eventually heq⟩

/-- **Pullback along a nowhere-locally-constant analytic map.** If `φ : ℂ → ℂ` is analytic on `Ω'`
with `MapsTo φ Ω' Ω` and is not locally constant at points of `Ω' ∩ φ ⁻¹' E`, then precomposing
pulls back `HasPrescribedSingularities` to `(Ω', Ω' ∩ φ ⁻¹' E)`. When `φ` is nowhere locally
constant on `Ω'` and `Eᶜ ∈ codiscreteWithin Ω`, `(φ ⁻¹' E)ᶜ ∈ codiscreteWithin Ω'` also follows
from `AnalyticOnNhd.preimage_mem_codiscreteWithin`. -/
theorem comp_analyticOnNhd {f : ℂ → F} {Ω Ω' E : Set ℂ} {P : E → ℂ → F}
    (hf : HasPrescribedSingularities f Ω E P) {φ : ℂ → ℂ}
    (hφ : AnalyticOnNhd ℂ φ Ω') (hnc : ∀ z ∈ Ω' ∩ φ ⁻¹' E, ¬EventuallyConst φ (𝓝 z))
    (hmaps : MapsTo φ Ω' Ω) :
    HasPrescribedSingularities (fun z => f (φ z)) Ω' (Ω' ∩ φ ⁻¹' E)
      (fun b z => P ⟨φ b.val, b.property.2⟩ (φ z)) := by
  refine ⟨hf.1.comp (hφ.differentiableOn.mono sdiff_subset) fun z hz =>
    ⟨hmaps hz.1, fun hzE => hz.2 ⟨hz.1, hzE⟩⟩, fun b => ?_⟩
  obtain ⟨g, hg, heq⟩ := hf.2 ⟨φ b.val, b.property.2⟩
  exact ⟨fun z => g (φ z), hg.fun_comp_of_eq (hφ b.val b.property.1) rfl,
    ((hφ b.val b.property.1).map_nhdsNE (hnc b.val b.property)) heq⟩

/-- **Translation compatibility.** Precomposing with `z ↦ z + c` shifts both the domain, the
singular locus, and the prescribed local germs. -/
theorem comp_add_right {f : ℂ → F} {Ω E : Set ℂ} {P : E → ℂ → F}
    (hf : HasPrescribedSingularities f Ω E P) (c : ℂ) :
    HasPrescribedSingularities (fun z => f (z + c)) ((· + c) ⁻¹' Ω) ((· + c) ⁻¹' E)
      (fun a z => P ⟨a.val + c, a.property⟩ (z + c)) :=
  hf.comp (differentiable_id.add_const c).differentiableOn
    (fun _ => analyticAt_id.add analyticAt_const)
    (fun _ => Filter.map_add_right_nhdsNE.le)

/-- **Scaling compatibility.** Precomposing with `z ↦ c * z` for `c ≠ 0` scales the domain, the
singular locus, and the prescribed local germs. -/
theorem comp_mul_left {f : ℂ → F} {Ω E : Set ℂ} {P : E → ℂ → F}
    (hf : HasPrescribedSingularities f Ω E P) {c : ℂ} (hc : c ≠ 0) :
    HasPrescribedSingularities (fun z => f (c * z)) ((c * ·) ⁻¹' Ω) ((c * ·) ⁻¹' E)
      (fun a z => P ⟨c * a.val, a.property⟩ (c * z)) :=
  hf.comp (differentiable_id.const_mul c).differentiableOn
    (fun _ => analyticAt_const.mul analyticAt_id)
    (fun a => ((Homeomorph.mulLeft₀ c hc).map_punctured_nhds_eq a.val).le)

/-- **Uniqueness modulo `H(Ω)`.** Two functions realizing the same prescribed singularities on a set
`Ω` along `E` (`Eᶜ ∈ Filter.codiscreteWithin Ω`) differ on `Ω \ E` by a function
complex-differentiable on all of `Ω` (which is unique on `Ω` when `Ω` is open or preperfect by
`Preperfect.eqOn_of_eqOn_sdiff_of_compl_mem_codiscreteWithin`). Neither openness of `Ω` nor
completeness of `F` is required. -/
theorem exists_differentiableOn_eqOn_sub {f₁ f₂ : ℂ → F} {Ω E : Set ℂ} {P : E → ℂ → F}
    (hf₁ : HasPrescribedSingularities f₁ Ω E P) (hf₂ : HasPrescribedSingularities f₂ Ω E P)
    (hE : Eᶜ ∈ codiscreteWithin Ω) :
    ∃ h : ℂ → F, DifferentiableOn ℂ h Ω ∧ EqOn (f₁ - f₂) h (Ω \ E) :=
  exists_differentiableOn_eqOn_of_analyticAt_nhdsNE hE (hf₁.1.sub hf₂.1) fun a ha => by
    obtain ⟨g, hg, heq⟩ := (hf₁.sub hf₂).2 ⟨a, ha.2⟩
    exact ⟨g, hg, heq.mono fun _ hz => by simpa only [sub_self, Pi.zero_apply, sub_zero] using hz⟩

end HasPrescribedSingularities

/-- **Invariance under analytic germ perturbations.** Changing each prescribed germ `P₁ a` by a
germ that agrees on `𝓝[≠] a.val` with an analytic function at `a.val` leaves
`HasPrescribedSingularities` unchanged. -/
theorem hasPrescribedSingularities_iff_of_analyticAt_sub {f : ℂ → F} {Ω E : Set ℂ}
    {P₁ P₂ : E → ℂ → F}
    (hP : ∀ a : E, ∃ q : ℂ → F, AnalyticAt ℂ q a.val ∧
      ∀ᶠ z in 𝓝[≠] a.val, P₁ a z - P₂ a z = q z) :
    HasPrescribedSingularities f Ω E P₁ ↔ HasPrescribedSingularities f Ω E P₂ := by
  have aux {Q₁ Q₂ : E → ℂ → F}
      (hQ : ∀ a : E, ∃ q : ℂ → F, AnalyticAt ℂ q a.val ∧
        ∀ᶠ z in 𝓝[≠] a.val, Q₁ a z - Q₂ a z = q z)
      (hf : HasPrescribedSingularities f Ω E Q₁) : HasPrescribedSingularities f Ω E Q₂ := by
    refine ⟨hf.1, fun a => ?_⟩
    obtain ⟨g, hg, hfg⟩ := hf.2 a
    obtain ⟨q, hq, hQq⟩ := hQ a
    refine ⟨g + q, hg.add hq, ?_⟩
    filter_upwards [hfg, hQq] with z hz₁ hz₂
    rw [Pi.add_apply, ← hz₁, ← hz₂, sub_add_sub_cancel]
  refine ⟨aux hP, aux fun a => ?_⟩
  obtain ⟨q, hq, hQq⟩ := hP a
  refine ⟨-q, hq.neg, ?_⟩
  filter_upwards [hQq] with z hz
  rw [Pi.neg_apply, ← hz, neg_sub]

/-- Congruence for `HasPrescribedSingularities` under equality on `Ω \ E` and punctured
neighborhoods of `E`. -/
theorem hasPrescribedSingularities_congr {f₁ f₂ : ℂ → F} {Ω E : Set ℂ}
    {P₁ P₂ : E → ℂ → F} (hf : EqOn f₁ f₂ (Ω \ E))
    (hfE : ∀ a : E, f₁ =ᶠ[𝓝[≠] a.val] f₂)
    (hP : ∀ a : E, P₁ a =ᶠ[𝓝[≠] a.val] P₂ a) :
    HasPrescribedSingularities f₁ Ω E P₁ ↔ HasPrescribedSingularities f₂ Ω E P₂ := by
  rw [hasPrescribedSingularities_iff_of_analyticAt_sub (P₂ := P₂) fun a =>
    ⟨0, analyticAt_const, (hP a).mono fun _ hz => by simp [hz]⟩]
  exact ⟨fun h => h.congr hf hfE, fun h => h.congr hf.symm fun a => (hfE a).symm⟩

end Predicate

section CompleteSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace HasPrescribedSingularities

/-- Adding a function complex-differentiable on an open set `Ω` (`E ⊆ Ω`) preserves
`HasPrescribedSingularities`. -/
theorem add_differentiableOn {f h : ℂ → F} {Ω E : Set ℂ} {P : E → ℂ → F}
    (hf : HasPrescribedSingularities f Ω E P) (hΩ : IsOpen Ω) (hEΩ : E ⊆ Ω)
    (hh : DifferentiableOn ℂ h Ω) :
    HasPrescribedSingularities (f + h) Ω E P := by
  refine ⟨hf.1.add (hh.mono sdiff_subset), fun a => ?_⟩
  obtain ⟨g, hg, heq⟩ := hf.2 a
  refine ⟨g + h, hg.add ((hh.analyticOnNhd hΩ) a.val (hEΩ a.property)), ?_⟩
  filter_upwards [heq] with z hz
  simp only [Pi.add_apply, add_sub_right_comm, hz]

/-- **Affine-coset characterization of solutions.** Given a solution `f₁` of the prescribed
singularity problem `(Ω, E, P)`, another function `f₂` is a solution if and only if `f₂` agrees on
`Ω \ E` with `f₁ + h` for a function `h` complex-differentiable on all of `Ω`. -/
theorem iff_exists_differentiableOn_eqOn_add {f₁ f₂ : ℂ → F} {Ω E : Set ℂ} {P : E → ℂ → F}
    (hf₁ : HasPrescribedSingularities f₁ Ω E P)
    (hΩ : IsOpen Ω) (hEΩ : E ⊆ Ω) (hE : Eᶜ ∈ codiscreteWithin Ω) :
    HasPrescribedSingularities f₂ Ω E P ↔
      ∃ h : ℂ → F, DifferentiableOn ℂ h Ω ∧ EqOn f₂ (f₁ + h) (Ω \ E) := by
  refine ⟨fun hf₂ => ?_, ?_⟩
  · obtain ⟨h, hh, heq⟩ := hf₂.exists_differentiableOn_eqOn_sub hf₁ hE
    exact ⟨h, hh, fun z hz => by simp [Pi.add_apply, ← heq hz]⟩
  · rintro ⟨h, hh, heq⟩
    exact (hf₁.add_differentiableOn hΩ hEΩ hh).congr_of_eqOn hΩ hEΩ hE heq.symm

/-- If every prescribed germ `P a` is meromorphic at `a.val`, any solution of
`HasPrescribedSingularities f Ω E P` is meromorphic on all of `Ω`. -/
theorem meromorphicOn {f : ℂ → F} {Ω E : Set ℂ} {P : E → ℂ → F}
    (hf : HasPrescribedSingularities f Ω E P) (hΩ : IsOpen Ω) (hE : Eᶜ ∈ codiscreteWithin Ω)
    (hP : ∀ a : E, MeromorphicAt (P a) a.val) : MeromorphicOn f Ω := by
  intro x hx
  by_cases hxE : x ∈ E
  · obtain ⟨g, hg, heq⟩ := hf.2 ⟨x, hxE⟩
    refine ((hP ⟨x, hxE⟩).add hg.meromorphicAt).congr ?_
    filter_upwards [heq] with z hz
    rw [Pi.add_apply, ← hz, add_sub_cancel]
  · exact ((hf.1.analyticOnNhd (hΩ.sdiff_of_compl_mem_codiscreteWithin hE))
      x ⟨hx, hxE⟩).meromorphicAt

end HasPrescribedSingularities

end CompleteSpace

/-! ### Compact-exhaustion patching -/

section Existence

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- If `f` agrees on a neighborhood `U` of `a.val` (`a ∈ s`) with `(∑ b ∈ s, q b) + H` for
`q b` analytic on `{b.val}ᶜ`, `P a - q a` analytic near `a.val`, and `H` analytic at `a.val`,
then `f - P a` agrees on `𝓝[≠] a.val` with a function analytic at `a.val`. -/
private theorem exists_analyticAt_sub_of_eqOn_sum_add
    {U E : Set ℂ} {P q : E → ℂ → F} (hq : ∀ b : E, AnalyticOnNhd ℂ (q b) {b.val}ᶜ)
    {g₀ : ℂ → F} {a : E} (hg₀ : AnalyticAt ℂ g₀ a.val)
    (hPq : ∀ᶠ z in 𝓝[≠] a.val, P a z - q a z = g₀ z)
    {s : Finset E} (has : a ∈ s) {f H : ℂ → F} (hU : U ∈ 𝓝 a.val)
    (hH : AnalyticAt ℂ H a.val) (hf : EqOn f ((fun z => ∑ b ∈ s, q b z) + H) U) :
    ∃ g : ℂ → F, AnalyticAt ℂ g a.val ∧ ∀ᶠ z in 𝓝[≠] a.val, f z - P a z = g z := by
  classical
  refine ⟨-g₀ + (fun z => (∑ b ∈ s.erase a, q b z) + H z), ?_, ?_⟩
  · refine hg₀.neg.add <| (Finset.analyticAt_fun_sum _ fun b hb =>
      hq b a.val (mem_compl_singleton_iff.mpr
        (Subtype.val_injective.ne (Finset.ne_of_mem_erase hb).symm))).add hH
  · filter_upwards [nhdsWithin_le_nhds hU, hPq] with z hz₁ hz₂
    simp only [Pi.add_apply, Pi.neg_apply, hf hz₁,
      ← Finset.add_sum_erase s (fun b => q b z) has, ← hz₂]
    abel

variable [CompleteSpace F]

/-- Open-set case of `exists_hasPrescribedSingularities_of_eventually_differentiableAt`. -/
private theorem exists_hasPrescribedSingularities_of_isOpen
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {E : Set ℂ} (hEΩ : E ⊆ Ω) (hE : Eᶜ ∈ codiscreteWithin Ω)
    (P : E → ℂ → F) (hP : ∀ a : E, ∀ᶠ z in 𝓝[≠] a.val, DifferentiableAt ℂ (P a) z) :
    ∃ f : ℂ → F, HasPrescribedSingularities f Ω E P := by
  classical
  obtain ⟨K, hKcpt, hKint, hKunion, hKfill⟩ := hΩ.exists_isFilledIn_compact_exhaustion
  have hKmono : Monotone K := monotone_nat_of_le_succ fun n => (hKint n).trans interior_subset
  have hKΩ (n : ℕ) : K n ⊆ Ω := hKunion ▸ subset_iUnion K n
  have hfin (n : ℕ) : (((↑) : E → ℂ) ⁻¹' K n).Finite :=
    ((hKcpt n).finite_inter_of_compl_mem_codiscreteWithin (hKΩ n) hE).preimage
      Subtype.val_injective.injOn |>.subset fun a ha => ⟨ha, a.property⟩
  let A : ℕ → Finset E := fun n => (hfin n).toFinset
  have hAmono : Monotone A := fun i j hij a ha => by
    simpa only [A, Finite.mem_toFinset, mem_preimage] using hKmono hij (by simpa [A] using ha)
  have havoid (k : ℕ) : ∀ a ∈ A (k + 1) \ A k, a.val ∉ K k := fun a ha haK =>
    (Finset.mem_sdiff.mp ha).2 (by simp [A, haK])
  choose q hq_an _ g hg_an hPq using fun a : E =>
    exists_analyticOnNhd_compl_singleton_tendsto_cocompact_sub_analyticAt (hP a)
  choose Q hQdiff hQlt using fun k : ℕ =>
    (hKfill k).exists_differentiableOn_norm_sum_sub_lt_of_differentiableOn_compl_singleton
      (A (k + 1) \ A k) hΩ (hKcpt k) (hKΩ k) (havoid k)
      (fun a _ => (hq_an a).differentiableOn) (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k)
  let S : ℕ → ℂ → F := fun k z => ∑ a ∈ A k, q a z
  have hS_sub (k : ℕ) : S (k + 1) - S k = fun z => ∑ a ∈ A (k + 1) \ A k, q a z :=
    funext fun _ => (Finset.sum_sdiff_eq_sub (hAmono k.le_succ)).symm
  let f : ℂ → F := fun z => S 0 z + ∑' k, (S (k + 1) - S k - Q k) z
  have hfK (m : ℕ) : ∃ H : ℂ → F, DifferentiableOn ℂ H (interior (K m)) ∧
      EqOn f (S m + H) (interior (K m)) :=
    exists_differentiableOn_eqOn_add_tsum isOpen_interior
      (fun k => (hQdiff k).mono (interior_subset.trans (hKΩ m))) summable_geometric_two m
      (fun k hmk => hS_sub k ▸ DifferentiableOn.fun_sum fun a ha =>
        (hq_an a).differentiableOn.mono (subset_compl_singleton_iff.mpr fun hz =>
          havoid k a ha (hKmono hmk (interior_subset hz))))
      fun k hmk z hz => by rw [hS_sub k]; exact (hQlt k z (hKmono hmk (interior_subset hz))).le
  refine ⟨f, fun z₀ hz₀ => ?_, fun a => ?_⟩
  · obtain ⟨n, hz₀n⟩ := mem_iUnion.mp (hKunion ▸ hz₀.1)
    obtain ⟨H, hH, hfH⟩ := hfK (n + 1)
    have hopen : IsOpen (interior (K (n + 1)) \ E) :=
      isOpen_interior.sdiff_of_compl_mem_codiscreteWithin
        (codiscreteWithin_mono (interior_subset.trans (hKΩ (n + 1))) hE)
    have hsum_diff : DifferentiableOn ℂ (S (n + 1) + H) (interior (K (n + 1)) \ E) :=
      (DifferentiableOn.fun_sum (s := interior (K (n + 1)) \ E) fun b _ =>
        (hq_an b).differentiableOn.mono (subset_compl_singleton_iff.mpr fun h =>
          h.2 b.property)).add (hH.mono sdiff_subset)
    exact ((hsum_diff.congr (hfH.mono sdiff_subset)).differentiableAt
      (hopen.mem_nhds ⟨hKint n hz₀n, hz₀.2⟩)).differentiableWithinAt
  · obtain ⟨n, han⟩ := mem_iUnion.mp (hKunion ▸ hEΩ a.property)
    obtain ⟨H, hH, hfH⟩ := hfK (n + 1)
    have hmem : interior (K (n + 1)) ∈ 𝓝 a.val := isOpen_interior.mem_nhds (hKint n han)
    exact exists_analyticAt_sub_of_eqOn_sum_add hq_an (hg_an a) (hPq a)
      (by simp [A, hKmono n.le_succ han]) hmem (hH.analyticAt hmem) hfH

/-- **Master prescribed-isolated-singularities theorem (punctured-germ form).** Given a subset
`Ω ⊆ ℂ` (not necessarily open), a subset `E ⊆ Ω` with `Eᶜ ∈ Filter.codiscreteWithin Ω`, and local
germs `P : E → ℂ → F` each complex-differentiable on `𝓝[≠] a.val`, there exists `f : ℂ → F`
realizing `HasPrescribedSingularities f Ω E P`. -/
theorem exists_hasPrescribedSingularities_of_eventually_differentiableAt
    {Ω E : Set ℂ} (hEΩ : E ⊆ Ω) (hE : Eᶜ ∈ codiscreteWithin Ω)
    (P : E → ℂ → F) (hP : ∀ a : E, ∀ᶠ z in 𝓝[≠] a.val, DifferentiableAt ℂ (P a) z) :
    ∃ f : ℂ → F, HasPrescribedSingularities f Ω E P := by
  let Ω₀ : Set ℂ := (derivedSet E)ᶜ
  have hΩ_sub : Ω ⊆ Ω₀ := subset_compl_derivedSet_of_compl_mem_codiscreteWithin hEΩ hE
  obtain ⟨f, hf⟩ := exists_hasPrescribedSingularities_of_isOpen
    (isClosed_derivedSet E).isOpen_compl (hEΩ.trans hΩ_sub)
    (compl_mem_codiscreteWithin_of_subset_compl_derivedSet subset_rfl) P hP
  exact ⟨f, hf.mono hΩ_sub subset_rfl inter_subset_right⟩

/-- **Holomorphic functions with prescribed isolated singularities.** Let `Ω ⊆ ℂ` (not necessarily
open) and let `E ⊆ Ω` satisfy `Eᶜ ∈ Filter.codiscreteWithin Ω`. Given at each `a : E` an open
neighborhood `U a` of `a.val` and a function `P a : ℂ → F` complex-differentiable on
`U a \ {a.val}` (possibly with an essential singularity at `a.val`), there exists `f : ℂ → F`
complex-differentiable on `Ω \ E` whose difference `f - P a` at every `a : E` agrees on
`𝓝[≠] a.val` with a function complex-analytic at `a.val`. -/
theorem exists_holomorphic_prescribed_isolated_singularities
    {Ω E : Set ℂ} (hEΩ : E ⊆ Ω) (hE : Eᶜ ∈ codiscreteWithin Ω)
    (U : E → Set ℂ) (P : E → ℂ → F)
    (hU : ∀ a, IsOpen (U a)) (haU : ∀ a : E, a.val ∈ U a)
    (hP : ∀ a : E, DifferentiableOn ℂ (P a) (U a \ {a.val})) :
    ∃ f : ℂ → F, DifferentiableOn ℂ f (Ω \ E) ∧
      ∀ a : E, ∃ g : ℂ → F, AnalyticAt ℂ g a.val ∧
        ∀ᶠ z in 𝓝[≠] a.val, f z - P a z = g z := by
  have hP' : ∀ a : E, ∀ᶠ z in 𝓝[≠] a.val, DifferentiableAt ℂ (P a) z := fun a => by
    have hopen : IsOpen (U a \ {a.val}) := (hU a).sdiff isClosed_singleton
    filter_upwards [sdiff_mem_nhdsWithin_compl ((hU a).mem_nhds (haU a)) {a.val}] with z hz
    exact (hP a).differentiableAt (hopen.mem_nhds hz)
  obtain ⟨f, hf⟩ :=
    exists_hasPrescribedSingularities_of_eventually_differentiableAt hEΩ hE P hP'
  exact ⟨f, hf.1, hf.2⟩

/-- **The Mittag-Leffler theorem.** Let `Ω ⊆ ℂ` (not necessarily open) and let `E ⊆ Ω` satisfy
`Eᶜ ∈ Filter.codiscreteWithin Ω`. Given meromorphic germs `P : E → ℂ → F` with
`MeromorphicAt (P a) a.val` for every `a : E`, there exists a function `f : ℂ → F` meromorphic on
`Ω` and complex-differentiable on `Ω \ E` such that at every `a : E`, `f - P a` agrees on
`𝓝[≠] a.val` with a function complex-analytic at `a.val`. -/
theorem exists_meromorphic_prescribed_principal_parts
    {Ω E : Set ℂ} (hEΩ : E ⊆ Ω) (hE : Eᶜ ∈ codiscreteWithin Ω)
    (P : E → ℂ → F) (hP : ∀ a : E, MeromorphicAt (P a) a.val) :
    ∃ f : ℂ → F, MeromorphicOn f Ω ∧
      (∀ a : E, ∃ g : ℂ → F, AnalyticAt ℂ g a.val ∧
        ∀ᶠ z in 𝓝[≠] a.val, f z - P a z = g z) ∧
      DifferentiableOn ℂ f (Ω \ E) := by
  let Ω₀ : Set ℂ := (derivedSet E)ᶜ
  have hΩ₀ : IsOpen Ω₀ := (isClosed_derivedSet E).isOpen_compl
  have hΩ_sub : Ω ⊆ Ω₀ := subset_compl_derivedSet_of_compl_mem_codiscreteWithin hEΩ hE
  have hE₀ : Eᶜ ∈ codiscreteWithin Ω₀ :=
    compl_mem_codiscreteWithin_of_subset_compl_derivedSet subset_rfl
  have hP' : ∀ a : E, ∀ᶠ z in 𝓝[≠] a.val, DifferentiableAt ℂ (P a) z :=
    fun a => (hP a).eventually_analyticAt.mono fun _ hz => hz.differentiableAt
  obtain ⟨f, hf⟩ := exists_hasPrescribedSingularities_of_isOpen hΩ₀ (hEΩ.trans hΩ_sub) hE₀ P hP'
  exact ⟨f, (hf.meromorphicOn hΩ₀ hE₀ hP).mono_set hΩ_sub, hf.2,
    hf.1.mono (sdiff_subset_sdiff_left hΩ_sub)⟩

/-- **Normal-form Mittag-Leffler theorem.** Under the hypotheses of
`exists_meromorphic_prescribed_principal_parts`, the realizing function `f : ℂ → F` can be chosen in
meromorphic normal form on `Ω` (`MeromorphicNFOn f Ω`), taking its analytic value at removable
points and `0` at poles. -/
theorem exists_meromorphicNFOn_prescribed_principal_parts
    {Ω E : Set ℂ} (hEΩ : E ⊆ Ω) (hE : Eᶜ ∈ codiscreteWithin Ω)
    (P : E → ℂ → F) (hP : ∀ a : E, MeromorphicAt (P a) a.val) :
    ∃ f : ℂ → F, MeromorphicNFOn f Ω ∧
      (∀ a : E, ∃ g : ℂ → F, AnalyticAt ℂ g a.val ∧
        ∀ᶠ z in 𝓝[≠] a.val, f z - P a z = g z) ∧
      DifferentiableOn ℂ f (Ω \ E) := by
  let Ω₀ : Set ℂ := (derivedSet E)ᶜ
  have hΩ₀ : IsOpen Ω₀ := (isClosed_derivedSet E).isOpen_compl
  have hΩ_sub : Ω ⊆ Ω₀ := subset_compl_derivedSet_of_compl_mem_codiscreteWithin hEΩ hE
  have hE₀ : Eᶜ ∈ codiscreteWithin Ω₀ :=
    compl_mem_codiscreteWithin_of_subset_compl_derivedSet subset_rfl
  have hEΩ₀ : E ⊆ Ω₀ := hEΩ.trans hΩ_sub
  obtain ⟨f₀, hf₀_mero, hf₀_sing, hf₀_diff⟩ :=
    exists_meromorphic_prescribed_principal_parts hEΩ₀ hE₀ P hP
  refine ⟨toMeromorphicNFOn f₀ Ω₀,
    fun _ hz => meromorphicNFOn_toMeromorphicNFOn f₀ Ω₀ (hΩ_sub hz), fun a => ?_, ?_⟩
  · obtain ⟨g, hg, heq⟩ := hf₀_sing a
    refine ⟨g, hg, ?_⟩
    filter_upwards [hf₀_mero.toMeromorphicNFOn_eq_self_on_nhdsNE (hEΩ₀ a.property), heq]
      with z hnf hz
    rwa [hnf]
  · have hopen := hΩ₀.sdiff_of_compl_mem_codiscreteWithin hE₀
    refine (hf₀_diff.congr fun z hz => ?_).mono (sdiff_subset_sdiff_left hΩ_sub)
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hf₀_mero hz.1,
      toMeromorphicNFAt_eq_self.mpr ((hf₀_diff.analyticOnNhd hopen) z hz).meromorphicNFAt]

end Existence

/-- At any marked point `a : E` where `f` and `P a` are meromorphic, realizing prescribed
singularities implies that `f` and `P a` have the same algebraic principal part. -/
theorem HasPrescribedSingularities.principalPart_mk_eq {f : ℂ → ℂ} {Ω E : Set ℂ}
    {P : E → ℂ → ℂ} (hf : HasPrescribedSingularities f Ω E P) (a : E)
    (hfa : MeromorphicAt f a.val) (hPa : MeromorphicAt (P a) a.val) :
    meromorphicGerms.principalPart (meromorphicGerms.mk f hfa) =
      meromorphicGerms.principalPart (meromorphicGerms.mk (P a) hPa) :=
  (meromorphicGerms.principalPart_mk_eq_principalPart_mk_iff hfa hPa).mpr (hf.2 a)

/-- **Characterization of polynomial principal parts via `HasPrescribedSingularities`.** Given an
open set `Ω ⊆ ℂ`, a subset `E ⊆ Ω` with `Eᶜ ∈ Filter.codiscreteWithin Ω`, and polynomials
`P : E → ℂ[X]` without constant term, `f : ℂ → ℂ` satisfies
`HasPrescribedSingularities f Ω E (fun a z => (P a).eval (z - a.val)⁻¹)` if and only if `f` is
meromorphic on `Ω`, complex-differentiable on `Ω \ E`, and has algebraic principal part `P a` at
every `a : E`. -/
theorem hasPrescribedSingularities_eval_inv_sub_iff {f : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {E : Set ℂ} (hEΩ : E ⊆ Ω) (hE : Eᶜ ∈ codiscreteWithin Ω)
    {P : E → ℂ[X]} (hP : ∀ a : E, (P a).coeff 0 = 0) :
    HasPrescribedSingularities f Ω E (fun a z => (P a).eval (z - a.val)⁻¹) ↔
      ∃ hf : MeromorphicOn f Ω, DifferentiableOn ℂ f (Ω \ E) ∧
        ∀ a : E, meromorphicGerms.principalPart
          (meromorphicGerms.mk f (hf a.val (hEΩ a.property))) = P a := by
  refine ⟨fun h => ?_, fun ⟨hf, hdiff, hprin⟩ => ⟨hdiff, fun a => ?_⟩⟩
  · have hf : MeromorphicOn f Ω :=
      h.meromorphicOn hΩ hE fun a => (P a).meromorphicAt_eval_inv_sub a.val
    refine ⟨hf, h.1, fun a => ?_⟩
    have hmk : meromorphicGerms.mk (fun z => (P a).eval (z - a.val)⁻¹)
        ((P a).meromorphicAt_eval_inv_sub a.val) = meromorphicGerms.evalInvSub a.val (P a) :=
      Subtype.ext (by rw [meromorphicGerms.coe_mk, coe_evalInvSub])
    rw [h.principalPart_mk_eq a (hf a.val (hEΩ a.property))
      ((P a).meromorphicAt_eval_inv_sub a.val), hmk,
      meromorphicGerms.principalPart_evalInvSub_of_coeff_zero (hP a)]
  · obtain ⟨-, g, hg, hgφ⟩ := meromorphicGerms.principalPart_eq_iff.mp (hprin a)
    refine ⟨g, hg, ?_⟩
    rwa [AddSubgroupClass.coe_sub, meromorphicGerms.coe_mk, coe_evalInvSub, ← Germ.coe_sub,
      Germ.coe_eq] at hgφ

/-- **Polynomial principal-part Mittag-Leffler theorem.** Given a subset `Ω ⊆ ℂ` (not necessarily
open), a relatively closed discrete subset `E ⊆ Ω`, and at each `a : E` a polynomial
`P a : ℂ[X]` without constant term, there exists `f : ℂ → ℂ` meromorphic on `Ω` and
complex-differentiable on `Ω \ E` whose algebraic principal part `meromorphicGerms.principalPart`
at every `a : E` equals `P a`. -/
theorem exists_meromorphic_principalPart_eq
    {Ω E : Set ℂ} (hEΩ : E ⊆ Ω) (hE : Eᶜ ∈ codiscreteWithin Ω)
    (P : E → ℂ[X]) (hP : ∀ a : E, (P a).coeff 0 = 0) :
    ∃ (f : ℂ → ℂ) (hf : MeromorphicOn f Ω), DifferentiableOn ℂ f (Ω \ E) ∧
      ∀ a : E, meromorphicGerms.principalPart
        (meromorphicGerms.mk f (hf a.val (hEΩ a.property))) = P a := by
  obtain ⟨f, hfm, hsing, hdiff⟩ := exists_meromorphic_prescribed_principal_parts hEΩ hE
    (fun a z => (P a).eval (z - a.val)⁻¹) fun a => (P a).meromorphicAt_eval_inv_sub a.val
  refine ⟨f, hfm, hdiff, fun a => ?_⟩
  obtain ⟨g, hg, hfg⟩ := hsing a
  refine meromorphicGerms.principalPart_eq_iff.mpr ⟨hP a, g, hg, ?_⟩
  rw [AddSubgroupClass.coe_sub, meromorphicGerms.coe_mk, Polynomial.coe_evalInvSub,
    ← Germ.coe_sub, Germ.coe_eq]
  exact hfg

/-- **Uniqueness via `meromorphicGerms.principalPart` modulo functions complex-differentiable on
`Ω`.** Two functions meromorphic on `Ω ∩ E`, complex-differentiable on `Ω \ E`
(`Eᶜ ∈ Filter.codiscreteWithin Ω`), and having the same algebraic
`meromorphicGerms.principalPart` at every point of `Ω ∩ E` differ on `Ω \ E` by a function
complex-differentiable on all of `Ω`. -/
theorem exists_differentiableOn_eqOn_sub_of_principalPart_mk_eq
    {Ω E : Set ℂ} (hE : Eᶜ ∈ codiscreteWithin Ω) {f₁ f₂ : ℂ → ℂ}
    (hf₁m : MeromorphicOn f₁ (Ω ∩ E)) (hf₂m : MeromorphicOn f₂ (Ω ∩ E))
    (hf₁ : DifferentiableOn ℂ f₁ (Ω \ E)) (hf₂ : DifferentiableOn ℂ f₂ (Ω \ E))
    (hprin : ∀ a (ha : a ∈ Ω ∩ E),
      meromorphicGerms.principalPart (meromorphicGerms.mk f₁ (hf₁m a ha)) =
        meromorphicGerms.principalPart (meromorphicGerms.mk f₂ (hf₂m a ha))) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h Ω ∧ EqOn (f₁ - f₂) h (Ω \ E) :=
  exists_differentiableOn_eqOn_of_analyticAt_nhdsNE hE (hf₁.sub hf₂) fun a ha =>
    (meromorphicGerms.principalPart_mk_eq_principalPart_mk_iff
      (hf₁m a ha) (hf₂m a ha)).mp (hprin a ha)

end TauCeti
