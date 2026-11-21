/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Meromorphic.NormalForm
public import TauCeti.Analysis.Meromorphic.PrincipalPart
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Homeomorph.Lemmas
import TauCeti.Analysis.Complex.Laurent.Expansion
import TauCeti.Analysis.Complex.RemovableSingularity
import TauCeti.Analysis.Complex.Runge.Approximation
import TauCeti.Analysis.Normed.Module.Exhaustion
import TauCeti.Topology.Codiscrete

/-!
# The Mittag-Leffler theorem and holomorphic functions with prescribed isolated singularities

Let `Ω` be a subset of `ℂ`, not necessarily open, let `E ⊆ Ω` be a relatively closed discrete
subset (`Eᶜ ∈ Filter.codiscreteWithin Ω`), and let `F` be a complex Banach space. Given at each
point `a : E` a local singular germ `P a : ℂ → F` complex-differentiable on a punctured neighborhood
of `a.val` (allowing poles of arbitrary order as well as essential singularities), this file
constructs a global function `f : ℂ → F` complex-differentiable on `Ω \ E` such that at every
`a : E` the difference `f - P a` agrees on `𝓝[≠] a.val` with a function complex-analytic at `a.val`.
The construction runs on an open set; a general `Ω` is first thickened to the open superset
`(derivedSet E)ᶜ`, within which `Eᶜ` is still codiscrete
(`TauCeti.subset_compl_derivedSet_of_compl_mem_codiscreteWithin`).

Specializing to meromorphic germs `MeromorphicAt (P a) a.val` yields the **Mittag-Leffler theorem**
on arbitrary subsets of `ℂ` (`TauCeti.exists_meromorphic_prescribed_principal_parts`, together
with its normal-form refinement `TauCeti.exists_meromorphicNFOn_prescribed_principal_parts` and
scalar polynomial principal-part form `TauCeti.exists_meromorphic_principalPart_eq`).

The predicate `TauCeti.HasPrescribedSingularities f Ω E P` packages the realization condition and
records its algebraic and geometric properties: congruence and invariance under changing the
prescribed germs by analytic germs, closure under linear operations, restriction to subsets,
compatibility with precomposition (in particular translations, nonzero complex dilations, and
non-locally-constant analytic maps), characterization via `TauCeti.meromorphicGerms.principalPart`,
and uniqueness of solutions on `Ω \ E` up to a function complex-differentiable on all of `Ω`
(unique on `Ω` when `Ω` is open).

## Main definitions and results

* `TauCeti.HasPrescribedSingularities`: `f` is complex-differentiable on `Ω \ E` and `f - P a`
  agrees on `𝓝[≠] a.val` with an analytic function at `a.val` for every `a : E`.
* `TauCeti.HasPrescribedSingularities.comp_of_analyticOnNhd`: pullback of solutions along analytic
  maps that are nowhere locally constant.
* `TauCeti.HasPrescribedSingularities.exists_differentiableOn_eqOn_sub` and
  `TauCeti.exists_differentiableOn_eqOn_sub_of_principalPart_mk_eq`: two solutions, or two scalar
  functions with the same algebraic principal parts along `E`, differ on `Ω \ E` by a function
  complex-differentiable on `Ω`, for arbitrary `Ω`.
* `TauCeti.HasPrescribedSingularities.iff_exists_differentiableOn_eqOn_add`: given one solution
  `f₁` on an open set `Ω`, any `f₂` realizes the same singularities if and only if it agrees on
  `Ω \ E` with `f₁ + h` for a function `h` complex-differentiable on `Ω` (unique on `Ω`).
* `TauCeti.exists_holomorphic_prescribed_isolated_singularities`: global realization of arbitrary
  isolated singularities (including essential singularities) on `Ω \ E`.
* `TauCeti.hasPrescribedSingularities_eval_inv_sub_iff`,
  `TauCeti.exists_meromorphic_prescribed_principal_parts`, and
  `TauCeti.exists_meromorphic_principalPart_eq`: polynomial principal-part characterization and the
  Mittag-Leffler theorem on subsets of `ℂ`.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorems 12.1 and 15.7.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 13.10.
* L. V. Ahlfors, *Complex Analysis*, 3rd ed., Chapter 5, §2.1.
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

/-- **Pullback along a non-locally-constant analytic map.** If `φ : ℂ → ℂ` is analytic and nowhere
locally constant on `Ω'` and maps `Ω'` into `Ω`, precomposing with `φ` pulls a solution on `(Ω, E)`
back to a solution on `(Ω', Ω' ∩ φ ⁻¹' E)`. The pulled-back singular locus is again relatively
closed and discrete in `Ω'` by `AnalyticOnNhd.preimage_mem_codiscreteWithin`. -/
theorem comp_of_analyticOnNhd {f : ℂ → F} {Ω Ω' E : Set ℂ} {P : E → ℂ → F}
    (hf : HasPrescribedSingularities f Ω E P) {φ : ℂ → ℂ} (hφ : AnalyticOnNhd ℂ φ Ω')
    (hnc : ∀ z ∈ Ω', ¬EventuallyConst φ (𝓝 z)) (hmaps : MapsTo φ Ω' Ω) :
    HasPrescribedSingularities (fun z => f (φ z)) Ω' (Ω' ∩ φ ⁻¹' E)
      (fun a z => P ⟨φ a.val, a.property.2⟩ (φ z)) := by
  refine ⟨hf.1.comp (hφ.differentiableOn.mono sdiff_subset) fun z hz =>
    ⟨hmaps hz.1, fun hzE => hz.2 ⟨hz.1, hzE⟩⟩, fun a => ?_⟩
  obtain ⟨g, hg, heq⟩ := hf.2 ⟨φ a.val, a.property.2⟩
  exact ⟨fun z => g (φ z), hg.fun_comp_of_eq (hφ a.val a.property.1) rfl,
    Tendsto.eventually ((hφ a.val a.property.1).map_nhdsNE (hnc a.val a.property.1)) heq⟩

/-- **Uniqueness modulo `H(Ω)`.** Two functions realizing the same prescribed singularities on a
set `Ω` along `E` (`Eᶜ ∈ Filter.codiscreteWithin Ω`) differ on `Ω \ E` by a function
complex-differentiable on all of `Ω`. The set `Ω` need not be open; when it is, this function is
unique on `Ω` by `IsOpen.eqOn_of_eqOn_sdiff_of_compl_mem_codiscreteWithin`. Applied with `Ω ∩ E` in
place of `E`, it only requires the singularity condition at the points of `Ω ∩ E`. -/
theorem exists_differentiableOn_eqOn_sub {f₁ f₂ : ℂ → F} {Ω E : Set ℂ} {P : E → ℂ → F}
    (hf₁ : HasPrescribedSingularities f₁ Ω E P) (hf₂ : HasPrescribedSingularities f₂ Ω E P)
    (hE : Eᶜ ∈ codiscreteWithin Ω) :
    ∃ h : ℂ → F, DifferentiableOn ℂ h Ω ∧ EqOn (f₁ - f₂) h (Ω \ E) := by
  have hdiff := hf₁.sub hf₂
  refine exists_differentiableOn_eqOn_of_analyticAt_nhdsNE hE hdiff.1 fun a ha => ?_
  obtain ⟨g, hg, heq⟩ := hdiff.2 ⟨a, ha.2⟩
  exact ⟨g, hg, heq.mono fun z hz => by simpa only [Pi.sub_apply, sub_self, sub_zero] using hz⟩

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

/-! ### Compact-exhaustion patching -/

omit [CompleteSpace F] in
/-- Construct holomorphic Runge correction terms on each compact piece `K k` for the `(k + 1)`-th
batch of global singular representatives. -/
private theorem exists_corr_seq {Ω E : Set ℂ}
    {K : ℕ → Set ℂ} (hKcpt : ∀ n, IsCompact (K n)) (hKΩ : ∀ n, K n ⊆ Ω)
    (hKfill : ∀ n, IsFilledIn (K n) Ω) (S : ℕ → Finset E)
    (hSavoid : ∀ k, ∀ a ∈ S (k + 1), a.val ∉ K k)
    {q : E → ℂ → F} (hq : ∀ a : E, DifferentiableOn ℂ (q a) {a.val}ᶜ) :
    ∃ corr : ℕ → ℂ → F, (∀ n, DifferentiableOn ℂ (corr n) Ω) ∧
      ∀ k, ∀ z ∈ K k, ‖(∑ a ∈ S (k + 1), q a z) - corr (k + 1) z‖ ≤ (1 / 2 : ℝ) ^ k := by
  have hstep : ∀ k : ℕ, ∃ g : ℂ → F, DifferentiableOn ℂ g Ω ∧
      ∀ z ∈ K k, ‖(∑ a ∈ S (k + 1), q a z) - g z‖ < (1 / 2 : ℝ) ^ k := fun k => by
    let U : Set ℂ := (Subtype.val '' (S (k + 1) : Set E))ᶜ
    have hU_open : IsOpen U :=
      ((S (k + 1)).finite_toSet.image Subtype.val).isClosed.isOpen_compl
    have hKU : K k ⊆ U := fun z hz ⟨a, ha, haz⟩ => hSavoid k a ha (haz ▸ hz)
    have hsum_diff : DifferentiableOn ℂ (fun z => ∑ a ∈ S (k + 1), q a z) U :=
      DifferentiableOn.fun_sum fun a ha =>
        (hq a).mono fun z hz hza => hz ⟨a, ha, hza.symm⟩
    exact (hKfill k).exists_differentiableOn_norm_sub_lt (hKcpt k) (hKΩ k) hU_open hKU hsum_diff
      (by positivity)
  choose g hg hbound using hstep
  refine ⟨Nat.rec 0 fun k _ => g k, ?_, fun k z hz => (hbound k z hz).le⟩
  rintro (_ | k)
  · exact differentiableOn_const 0
  · exact hg k

/-- On `interior (K m)`, the tail `∑' k, term (k + (m + 1))` of the Mittag-Leffler series is
complex-differentiable and splits `∑' n, term n` into its `(m + 1)`-term prefix plus that tail. -/
private theorem differentiableOn_tail_and_tsum_eq {Ω E : Set ℂ}
    {K : ℕ → Set ℂ} (hKmono : Monotone K) (hKΩ : ∀ n, K n ⊆ Ω)
    (S : ℕ → Finset E) (hSavoid : ∀ m n, m < n → ∀ a ∈ S n, a.val ∉ K m)
    {q : E → ℂ → F} (hq : ∀ a : E, DifferentiableOn ℂ (q a) {a.val}ᶜ)
    {corr : ℕ → ℂ → F} (hcorr : ∀ n, DifferentiableOn ℂ (corr n) Ω)
    (hbound : ∀ k, ∀ z ∈ K k, ‖(∑ a ∈ S (k + 1), q a z) - corr (k + 1) z‖ ≤ (1 / 2 : ℝ) ^ k)
    (m : ℕ) :
    let term : ℕ → ℂ → F := fun n z => (∑ a ∈ S n, q a z) - corr n z
    DifferentiableOn ℂ (fun z => ∑' k : ℕ, term (k + (m + 1)) z) (interior (K m)) ∧
      ∀ z ∈ interior (K m),
        (∑' n : ℕ, term n z) =
          (∑ n ∈ Finset.range (m + 1), term n z) + ∑' k : ℕ, term (k + (m + 1)) z := by
  intro term
  have hu : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ (k + m)) :=
    (summable_nat_add_iff m).mpr summable_geometric_two
  have hterm_diff : ∀ k : ℕ, DifferentiableOn ℂ (term (k + (m + 1))) (interior (K m)) := fun k => by
    have hbatch : DifferentiableOn ℂ (fun z => ∑ a ∈ S (k + (m + 1)), q a z) (interior (K m)) :=
      DifferentiableOn.fun_sum fun a ha => (hq a).mono fun z hz hza =>
        hSavoid m (k + (m + 1)) (by omega) a ha (hza ▸ interior_subset hz)
    exact hbatch.sub ((hcorr (k + (m + 1))).mono (interior_subset.trans (hKΩ m)))
  have hterm_le : ∀ (k : ℕ) (z : ℂ), z ∈ interior (K m) →
      ‖term (k + (m + 1)) z‖ ≤ (1 / 2 : ℝ) ^ (k + m) := fun k z hz => by
    have hzk : z ∈ K (k + m) := hKmono (Nat.le_add_left m k) (interior_subset hz)
    simpa only [term, Nat.add_assoc] using hbound (k + m) z hzk
  refine ⟨differentiableOn_tsum_of_summable_norm hu hterm_diff isOpen_interior hterm_le,
    fun z hz => ?_⟩
  have hsum_tail : Summable (fun k : ℕ => term (k + (m + 1)) z) :=
    .of_norm_bounded hu fun k => hterm_le k z hz
  exact (((summable_nat_add_iff (m + 1)).mp hsum_tail).sum_add_tsum_nat_add (m + 1)).symm

/-- The Mittag-Leffler series `∑' n, ((∑ a ∈ S n, q a z) - corr n z)` is complex-differentiable on
`Ω \ E`. -/
private theorem differentiableOn_tsum_term {Ω E : Set ℂ} (hΩ : IsOpen Ω)
    (hE : Eᶜ ∈ codiscreteWithin Ω) {K : ℕ → Set ℂ}
    (hKint : ∀ n, K n ⊆ interior (K (n + 1))) (hKiUnion : ⋃ n, K n = Ω)
    (S : ℕ → Finset E) (hSavoid : ∀ m n, m < n → ∀ a ∈ S n, a.val ∉ K m)
    {q : E → ℂ → F} (hq : ∀ a : E, DifferentiableOn ℂ (q a) {a.val}ᶜ)
    {corr : ℕ → ℂ → F} (hcorr : ∀ n, DifferentiableOn ℂ (corr n) Ω)
    (hbound : ∀ k, ∀ z ∈ K k, ‖(∑ a ∈ S (k + 1), q a z) - corr (k + 1) z‖ ≤ (1 / 2 : ℝ) ^ k) :
    DifferentiableOn ℂ (fun z => ∑' n : ℕ, ((∑ a ∈ S n, q a z) - corr n z)) (Ω \ E) := by
  have hKΩ : ∀ n, K n ⊆ Ω := fun n => (subset_iUnion K n).trans_eq hKiUnion
  have hKmono : Monotone K := monotone_nat_of_le_succ fun n => (hKint n).trans interior_subset
  let term : ℕ → ℂ → F := fun n z => (∑ a ∈ S n, q a z) - corr n z
  intro z₀ ⟨hz₀Ω, hz₀E⟩
  obtain ⟨j, hzj⟩ := mem_iUnion.mp (hKiUnion ▸ hz₀Ω)
  have hz_int : z₀ ∈ interior (K (j + 1)) := hKint j hzj
  obtain ⟨htail, hfeq⟩ :=
    differentiableOn_tail_and_tsum_eq hKmono hKΩ S hSavoid hq hcorr hbound (j + 1)
  have hpref : DifferentiableOn ℂ (fun z => ∑ n ∈ Finset.range (j + 2), term n z) (Ω \ E) :=
    DifferentiableOn.fun_sum fun n _ =>
      (DifferentiableOn.fun_sum fun a _ =>
        (hq a).mono fun _ (hz : _ ∈ Ω \ E) hza => hz.2 (hza ▸ a.property)).sub
        ((hcorr n).mono sdiff_subset)
  have hopen : IsOpen (interior (K (j + 1)) ∩ (Ω \ E)) :=
    isOpen_interior.inter (hΩ.sdiff_of_compl_mem_codiscreteWithin hE)
  have hsum_diff : DifferentiableOn ℂ
      (fun z => (∑ n ∈ Finset.range (j + 2), term n z) + ∑' k : ℕ, term (k + (j + 2)) z)
      (interior (K (j + 1)) ∩ (Ω \ E)) :=
    (hpref.mono inter_subset_right).add (htail.mono inter_subset_left)
  refine ((hsum_diff.differentiableAt (hopen.mem_nhds ⟨hz_int, hz₀Ω, hz₀E⟩)).congr_of_eventuallyEq
    ?_).differentiableWithinAt
  filter_upwards [isOpen_interior.mem_nhds hz_int] with z hz
  exact hfeq z hz

/-- Extract the single singular summand `q a₀` from the finite prefix `∑ n < m + 1, term n`, leaving
a sum that is complex-analytic at `a₀.val`. -/
private theorem prefix_eq_add_analyticAt {Ω E : Set ℂ} (hΩ : IsOpen Ω) (hEΩ : E ⊆ Ω)
    {idx : E → ℕ} {S : ℕ → Finset E} (hS : ∀ n a, a ∈ S n ↔ idx a = n)
    {q : E → ℂ → F} (hq : ∀ a : E, AnalyticOnNhd ℂ (q a) {a.val}ᶜ)
    {corr : ℕ → ℂ → F} (hcorr : ∀ n, DifferentiableOn ℂ (corr n) Ω)
    (a₀ : E) {m : ℕ} (hm : idx a₀ < m + 1) :
    ∃ r : ℂ → F, AnalyticAt ℂ r a₀.val ∧
      ∀ z : ℂ, (∑ n ∈ Finset.range (m + 1), ((∑ a ∈ S n, q a z) - corr n z)) =
        q a₀ z + r z := by
  classical
  let r : ℂ → F :=
    fun z => ∑ n ∈ Finset.range (m + 1), ((∑ a ∈ (S n).erase a₀, q a z) - corr n z)
  have hr_an : AnalyticAt ℂ r a₀.val := by
    refine Finset.analyticAt_fun_sum _ fun n _ => ?_
    have hbatch : AnalyticAt ℂ (fun z => ∑ a ∈ (S n).erase a₀, q a z) a₀.val :=
      Finset.analyticAt_fun_sum _ fun a ha =>
        hq a a₀.val (Subtype.coe_ne_coe.mpr (Finset.ne_of_mem_erase ha)).symm
    exact hbatch.sub ((hcorr n).analyticOnNhd hΩ a₀.val (hEΩ a₀.property))
  refine ⟨r, hr_an, fun z => ?_⟩
  have hq_ite : q a₀ z = ∑ n ∈ Finset.range (m + 1), if n = idx a₀ then q a₀ z else 0 := by
    simp only [Finset.sum_ite_eq', Finset.mem_range.mpr hm, ↓reduceIte]
  rw [hq_ite, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rcases eq_or_ne n (idx a₀) with rfl | hn
  · have ha₀ : a₀ ∈ S (idx a₀) := (hS (idx a₀) a₀).mpr rfl
    simp only [↓reduceIte]
    rw [← add_sub_assoc, Finset.add_sum_erase (S (idx a₀)) (fun a => q a z) ha₀]
  · have ha₀ : a₀ ∉ S n := fun h => hn ((hS n a₀).mp h).symm
    simp only [hn, ↓reduceIte, zero_add, Finset.erase_eq_of_notMem ha₀]

/-- Open-set case of `exists_hasPrescribedSingularities_of_eventually_differentiableAt`. -/
private theorem exists_hasPrescribedSingularities_of_isOpen
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {E : Set ℂ} (hEΩ : E ⊆ Ω) (hE : Eᶜ ∈ codiscreteWithin Ω)
    (P : E → ℂ → F) (hP : ∀ a : E, ∀ᶠ z in 𝓝[≠] a.val, DifferentiableAt ℂ (P a) z) :
    ∃ f : ℂ → F, HasPrescribedSingularities f Ω E P := by
  classical
  obtain ⟨K, hKcpt, hKint, hKiUnion, hKfill⟩ := hΩ.exists_isFilledIn_compact_exhaustion
  have hKΩ : ∀ n, K n ⊆ Ω := fun n => (subset_iUnion K n).trans_eq hKiUnion
  have hKmono : Monotone K := monotone_nat_of_le_succ fun n => (hKint n).trans interior_subset
  have hex : ∀ a : E, ∃ n, a.val ∈ K n := fun a => mem_iUnion.mp (hKiUnion ▸ hEΩ a.property)
  let idx : E → ℕ := fun a => Nat.find (hex a)
  have hSfin : ∀ n : ℕ, {a : E | idx a = n}.Finite := fun n => by
    refine Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn
    refine ((hKcpt n).finite_inter_of_compl_mem_codiscreteWithin (hKΩ n) hE).subset ?_
    rintro _ ⟨a, ha : idx a = n, rfl⟩
    exact ⟨ha ▸ Nat.find_spec (hex a), a.property⟩
  let S : ℕ → Finset E := fun n => (hSfin n).toFinset
  have hS : ∀ n a, a ∈ S n ↔ idx a = n := fun n a => (hSfin n).mem_toFinset
  have hSavoid : ∀ m n, m < n → ∀ a ∈ S n, a.val ∉ K m := fun m n hmn a ha =>
    Nat.find_min (hex a) (hmn.trans_eq ((hS n a).mp ha).symm)
  choose q hq_an _ g hg_an hPq using fun a : E =>
    exists_analyticOnNhd_compl_singleton_tendsto_cocompact_sub_analyticAt (hP a)
  have hq_diff : ∀ a : E, DifferentiableOn ℂ (q a) {a.val}ᶜ := fun a => (hq_an a).differentiableOn
  obtain ⟨corr, hcorr, hbound⟩ := exists_corr_seq hKcpt hKΩ hKfill S
    (fun k => hSavoid k (k + 1) (Nat.lt_succ_self k)) hq_diff
  let term : ℕ → ℂ → F := fun n z => (∑ a ∈ S n, q a z) - corr n z
  refine ⟨fun z => ∑' n : ℕ, term n z,
    differentiableOn_tsum_term hΩ hE hKint hKiUnion S hSavoid hq_diff hcorr hbound, fun a₀ => ?_⟩
  let m := idx a₀ + 1
  have ha₀_int : a₀.val ∈ interior (K m) := hKint (idx a₀) (Nat.find_spec (hex a₀))
  obtain ⟨htail, hfeq⟩ :=
    differentiableOn_tail_and_tsum_eq hKmono hKΩ S hSavoid hq_diff hcorr hbound m
  obtain ⟨r, hr_an, hpref⟩ :=
    prefix_eq_add_analyticAt hΩ hEΩ hS hq_an hcorr a₀ (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
  have htail_an : AnalyticAt ℂ (fun z => ∑' k : ℕ, term (k + (m + 1)) z) a₀.val :=
    htail.analyticOnNhd isOpen_interior a₀.val ha₀_int
  refine ⟨-(g a₀) + r + fun z => ∑' k : ℕ, term (k + (m + 1)) z,
    ((hg_an a₀).neg.add hr_an).add htail_an, ?_⟩
  filter_upwards [nhdsWithin_le_nhds (isOpen_interior.mem_nhds ha₀_int), hPq a₀]
    with z hz_int hPz
  rw [hfeq z hz_int, hpref z]
  simp only [Pi.add_apply, Pi.neg_apply, ← hPz]
  abel

/-- **Thickening to an open set.** Any `Ω ⊇ E` with `Eᶜ ∈ Filter.codiscreteWithin Ω` lies in the
open set `(derivedSet E)ᶜ`, within which `Eᶜ` is still codiscrete. -/
private theorem exists_isOpen_superset_compl_mem_codiscreteWithin {Ω E : Set ℂ} (hEΩ : E ⊆ Ω)
    (hE : Eᶜ ∈ codiscreteWithin Ω) :
    ∃ Ω₀ : Set ℂ, IsOpen Ω₀ ∧ Ω ⊆ Ω₀ ∧ Eᶜ ∈ codiscreteWithin Ω₀ :=
  ⟨(derivedSet E)ᶜ, (isClosed_derivedSet E).isOpen_compl,
    subset_compl_derivedSet_of_compl_mem_codiscreteWithin hEΩ hE,
    compl_mem_codiscreteWithin_of_subset_compl_derivedSet Subset.rfl⟩

/-- **Master prescribed-isolated-singularities theorem (punctured-germ form).** Given a set
`Ω ⊆ ℂ`, not necessarily open, a subset `E ⊆ Ω` with `Eᶜ ∈ Filter.codiscreteWithin Ω`, and local
germs `P : E → ℂ → F` each complex-differentiable on `𝓝[≠] a.val`, there exists `f : ℂ → F`
realizing `HasPrescribedSingularities f Ω E P`. -/
theorem exists_hasPrescribedSingularities_of_eventually_differentiableAt
    {Ω E : Set ℂ} (hEΩ : E ⊆ Ω) (hE : Eᶜ ∈ codiscreteWithin Ω)
    (P : E → ℂ → F) (hP : ∀ a : E, ∀ᶠ z in 𝓝[≠] a.val, DifferentiableAt ℂ (P a) z) :
    ∃ f : ℂ → F, HasPrescribedSingularities f Ω E P := by
  obtain ⟨Ω₀, hΩ₀, hΩΩ₀, hE₀⟩ := exists_isOpen_superset_compl_mem_codiscreteWithin hEΩ hE
  obtain ⟨f, hf⟩ := exists_hasPrescribedSingularities_of_isOpen hΩ₀ (hEΩ.trans hΩΩ₀) hE₀ P hP
  exact ⟨f, hf.mono hΩΩ₀ Subset.rfl inter_subset_right⟩

/-- **Holomorphic functions with prescribed isolated singularities.** Let `Ω ⊆ ℂ` be any set, not
necessarily open, and let `E ⊆ Ω` satisfy `Eᶜ ∈ Filter.codiscreteWithin Ω`. Given at each `a : E`
an open neighborhood `U a` of `a.val` and a function `P a : ℂ → F` complex-differentiable on
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
  obtain ⟨f, hf⟩ := exists_hasPrescribedSingularities_of_eventually_differentiableAt hEΩ hE P hP'
  exact ⟨f, hf.1, hf.2⟩

/-- **The Mittag-Leffler theorem.** Let `Ω ⊆ ℂ` be any set, not necessarily open, and let `E ⊆ Ω`
satisfy `Eᶜ ∈ Filter.codiscreteWithin Ω`. Given meromorphic germs `P : E → ℂ → F` with
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
  have hP' : ∀ a : E, ∀ᶠ z in 𝓝[≠] a.val, DifferentiableAt ℂ (P a) z :=
    fun a => (hP a).eventually_analyticAt.mono fun _ hz => hz.differentiableAt
  obtain ⟨Ω₀, hΩ₀, hΩΩ₀, hE₀⟩ := exists_isOpen_superset_compl_mem_codiscreteWithin hEΩ hE
  obtain ⟨f, hf⟩ := exists_hasPrescribedSingularities_of_isOpen hΩ₀ (hEΩ.trans hΩΩ₀) hE₀ P hP'
  exact ⟨f, (hf.meromorphicOn hΩ₀ hE₀ hP).mono_set hΩΩ₀, hf.2,
    hf.1.mono (sdiff_subset_sdiff_left hΩΩ₀)⟩

/-- **Normal-form Mittag-Leffler theorem.** Under the hypotheses of
`exists_meromorphic_prescribed_principal_parts`, the realizing function `f : ℂ → F` can be chosen in
meromorphic normal form on `Ω` (`MeromorphicNFOn f Ω`), taking its analytic value at removable
points and `0` at poles. As there, `Ω` need not be open. -/
theorem exists_meromorphicNFOn_prescribed_principal_parts
    {Ω E : Set ℂ} (hEΩ : E ⊆ Ω) (hE : Eᶜ ∈ codiscreteWithin Ω)
    (P : E → ℂ → F) (hP : ∀ a : E, MeromorphicAt (P a) a.val) :
    ∃ f : ℂ → F, MeromorphicNFOn f Ω ∧
      (∀ a : E, ∃ g : ℂ → F, AnalyticAt ℂ g a.val ∧
        ∀ᶠ z in 𝓝[≠] a.val, f z - P a z = g z) ∧
      DifferentiableOn ℂ f (Ω \ E) := by
  obtain ⟨Ω₀, hΩ₀, hΩΩ₀, hE₀⟩ := exists_isOpen_superset_compl_mem_codiscreteWithin hEΩ hE
  obtain ⟨f₀, hf₀_mero, hf₀_sing, hf₀_diff⟩ :=
    exists_meromorphic_prescribed_principal_parts (hEΩ.trans hΩΩ₀) hE₀ P hP
  refine ⟨toMeromorphicNFOn f₀ Ω₀,
    fun _ hz => meromorphicNFOn_toMeromorphicNFOn f₀ Ω₀ (hΩΩ₀ hz), fun a => ?_, ?_⟩
  · obtain ⟨g, hg, heq⟩ := hf₀_sing a
    refine ⟨g, hg, ?_⟩
    filter_upwards [hf₀_mero.toMeromorphicNFOn_eq_self_on_nhdsNE (hΩΩ₀ (hEΩ a.property)), heq]
      with z hnf hz
    rwa [hnf]
  · have hopen := hΩ₀.sdiff_of_compl_mem_codiscreteWithin hE₀
    refine (hf₀_diff.congr fun z hz => ?_).mono (sdiff_subset_sdiff_left hΩΩ₀)
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hf₀_mero hz.1,
      toMeromorphicNFAt_eq_self.mpr ((hf₀_diff.analyticOnNhd hopen) z hz).meromorphicNFAt]

end CompleteSpace

/-- At any marked point `a : E` where `f` and `P a` are meromorphic, realizing prescribed
singularities implies that `f` and `P a` have the same algebraic principal part. -/
theorem HasPrescribedSingularities.principalPart_mk_eq {f : ℂ → ℂ} {Ω E : Set ℂ}
    {P : E → ℂ → ℂ} (hf : HasPrescribedSingularities f Ω E P) (a : E)
    (hfa : MeromorphicAt f a.val) (hPa : MeromorphicAt (P a) a.val) :
    meromorphicGerms.principalPart (meromorphicGerms.mk f hfa) =
      meromorphicGerms.principalPart (meromorphicGerms.mk (P a) hPa) := by
  obtain ⟨g, hg, heq⟩ := hf.2 a
  exact (meromorphicGerms.principalPart_mk_eq_principalPart_mk_iff hfa hPa).mpr ⟨g, hg, heq⟩

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

/-- **Polynomial principal-part Mittag-Leffler theorem.** Given a set `Ω ⊆ ℂ`, not necessarily open,
a relatively closed discrete subset `E ⊆ Ω`, and at each `a : E` a polynomial `P a : ℂ[X]` without
constant term, there exists `f : ℂ → ℂ` meromorphic on `Ω` and complex-differentiable on `Ω \ E`
whose algebraic principal part `meromorphicGerms.principalPart` at every `a : E` equals `P a`. -/
theorem exists_meromorphic_principalPart_eq
    {Ω E : Set ℂ} (hEΩ : E ⊆ Ω) (hE : Eᶜ ∈ codiscreteWithin Ω)
    (P : E → ℂ[X]) (hP : ∀ a : E, (P a).coeff 0 = 0) :
    ∃ (f : ℂ → ℂ) (hf : MeromorphicOn f Ω), DifferentiableOn ℂ f (Ω \ E) ∧
      ∀ a : E, meromorphicGerms.principalPart
        (meromorphicGerms.mk f (hf a.val (hEΩ a.property))) = P a := by
  obtain ⟨Ω₀, hΩ₀, hΩΩ₀, hE₀⟩ := exists_isOpen_superset_compl_mem_codiscreteWithin hEΩ hE
  obtain ⟨f, _, hsing, hdiff⟩ := exists_meromorphic_prescribed_principal_parts (hEΩ.trans hΩΩ₀)
    hE₀ (fun a z => (P a).eval (z - a.val)⁻¹) fun a => (P a).meromorphicAt_eval_inv_sub a.val
  obtain ⟨hf, hdiff, hprin⟩ :=
    (hasPrescribedSingularities_eval_inv_sub_iff hΩ₀ (hEΩ.trans hΩΩ₀) hE₀ hP).mp ⟨hdiff, hsing⟩
  exact ⟨f, hf.mono_set hΩΩ₀, hdiff.mono (sdiff_subset_sdiff_left hΩΩ₀), hprin⟩

/-- **Uniqueness via `meromorphicGerms.principalPart` modulo functions complex-differentiable on
`Ω`.** Two functions meromorphic on `Ω ∩ E`, complex-differentiable on `Ω \ E`
(`Eᶜ ∈ Filter.codiscreteWithin Ω`), and having the same algebraic `meromorphicGerms.principalPart`
at every point of `Ω ∩ E` differ on `Ω \ E` by a function complex-differentiable on all of `Ω`. The
set `Ω` need not be open. -/
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
