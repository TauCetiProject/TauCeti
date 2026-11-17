/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Strip.Jet

/-!
# The Sobolev space `W^{1,2}` on the strip with linear boundary conditions

Let `V` be a real normed space and `L₀`, `L₁` two subspaces of `V`. Sections of the trivial
bundle with fibre `V` over the strip `ℝ × [0, 1]` with boundary values in `L₀` along `t = 0` and
in `L₁` along `t = 1` are the domain of the linearized Floer operators of strips with Lagrangian,
or more generally totally real, boundary conditions. This file sets up the Sobolev space of such
sections, the strip counterpart of `TauCeti.CylinderSobolev.H1`.

* **Test sections** (`TauCeti.StripSobolev.testSection L₀ L₁`) are the compactly supported `C²`
  maps `ξ : ℝ × ℝ → V` with `ξ (s, 0) ∈ L₀` and `ξ (s, 1) ∈ L₁` for every `s`. Only their values on
  the strip matter below.
* The jet `(ξ, ∂s ξ, ∂t ξ)` (`TauCeti.StripSobolev.jet`) of a test section is square integrable
  on the strip (`TauCeti.StripSobolev.memLp_jet`), for the Lebesgue measure
  `TauCeti.StripSobolev.stripMeasure` of `ℝ × [0, 1]`. This gives the linear map
  `TauCeti.StripSobolev.jetₗ` into `L²(ℝ × [0, 1], V × V × V)`, whose norm is the `W^{1,2}` norm
  up to a factor between `1` and `√3`.
* `TauCeti.StripSobolev.H1 L₀ L₁` is the closure of the jets of test sections: the completion of
  the test sections in the `W^{1,2}` norm, realized inside `L²` as a closed subspace, hence
  complete when `V` is. The `L²` jets and their closure are the constructions
  `TauCeti.StripSobolev.jetLp` and `TauCeti.StripSobolev.jetClosure` shared with the cylinder,
  applied to the test sections of the strip.
* **Translation invariance.** Translation in the `s` direction, `ξ ↦ ξ (· + a, ·)`, preserves the
  test sections (`TauCeti.StripSobolev.comp_add_right_mem_testSection`). By the results of
  `TauCeti.Analysis.Sobolev.Strip.Jet` on translation-invariant spaces of sections, translation
  `TauCeti.StripSobolev.translateL` of `L²` jets maps `H1 L₀ L₁` onto itself
  (`TauCeti.StripSobolev.translateL_mem_jetClosure_iff`) and is a linear isometric equivalence
  `TauCeti.StripSobolev.translate (testSection L₀ L₁) a` of `H1 L₀ L₁`, so the `W^{1,2}` norm of a
  section and of its translates agree (`TauCeti.StripSobolev.norm_jetLp_comp_add_right`). This is
  the translation-invariant norm of the strip, which a norm built from one compact piece of the
  strip does not have.

The boundary conditions are imposed on the test sections; they hold for the elements of `H1` in
the sense of this closure. First-order operators with essentially bounded coefficients act on the
`L²` jets by `TauCeti.CylinderSobolev.jetOperator`, which only depends on the strip and not on the
periodicity of the cylinder. For linear isotropic boundary conditions the Cauchy–Riemann operator
`∂s + J ∂t` on `H1 L₀ L₁` is studied in `TauCeti.Geometry.Symplectic.JHolomorphic.StripSobolev`.

## Main definitions

* `TauCeti.StripSobolev.testSection L₀ L₁`: the test sections with boundary values in `L₀`, `L₁`.
* `TauCeti.StripSobolev.jetₗ`: the `L²` jet of a test section.
* `TauCeti.StripSobolev.H1 L₀ L₁`: the Sobolev space `W^{1,2}` of the strip with these boundary
  conditions.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Appendix B
  and Section 3.1, on Sobolev spaces of sections with totally real boundary conditions.
* A. Floer, *The unregularized gradient flow of the symplectic action*, Comm. Pure Appl. Math. 41
  (1988), Section 3, on the Sobolev completion of sections over the strip with Lagrangian boundary
  conditions.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace TauCeti.StripSobolev

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {L₀ L₁ : Submodule ℝ V}

variable (L₀ L₁) in
/-- The test sections over the strip with boundary values in `L₀` and `L₁`: the compactly
supported `C²` maps `ξ : ℝ × ℝ → V` with `ξ (s, 0) ∈ L₀` and `ξ (s, 1) ∈ L₁` for every `s`. -/
def testSection : Submodule ℝ (ℝ × ℝ → V) where
  carrier := {ξ | ContDiff ℝ 2 ξ ∧ HasCompactSupport ξ ∧ (∀ s, ξ (s, 0) ∈ L₀) ∧
    ∀ s, ξ (s, 1) ∈ L₁}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero, fun _ ↦ L₀.zero_mem,
    fun _ ↦ L₁.zero_mem⟩
  add_mem' := by
    rintro ξ η ⟨hξ, hξc, hξ₀, hξ₁⟩ ⟨hη, hηc, hη₀, hη₁⟩
    exact ⟨hξ.add hη, hξc.add hηc, fun s ↦ L₀.add_mem (hξ₀ s) (hη₀ s),
      fun s ↦ L₁.add_mem (hξ₁ s) (hη₁ s)⟩
  smul_mem' := by
    rintro c ξ ⟨hξ, hξc, hξ₀, hξ₁⟩
    exact ⟨contDiff_const.smul hξ, hξc.smul_left, fun s ↦ L₀.smul_mem c (hξ₀ s),
      fun s ↦ L₁.smul_mem c (hξ₁ s)⟩

/-- Membership in the test sections. -/
theorem mem_testSection_iff {ξ : ℝ × ℝ → V} : ξ ∈ testSection L₀ L₁ ↔
    ContDiff ℝ 2 ξ ∧ HasCompactSupport ξ ∧ (∀ s, ξ (s, 0) ∈ L₀) ∧ ∀ s, ξ (s, 1) ∈ L₁ :=
  Iff.rfl

variable {ξ η : ℝ × ℝ → V}

/-- The jet of a test section is square integrable on the strip. -/
theorem memLp_jet (hξ : ξ ∈ testSection L₀ L₁) : MemLp (jet ξ) 2 stripMeasure := by
  obtain ⟨hξ2, hc, -⟩ := mem_testSection_iff.1 hξ
  exact (continuous_jet (hξ2.of_le (by norm_num))).memLp_of_hasCompactSupport
    (hasCompactSupport_jet hc)

/-- The test sections are differentiable with square integrable jets. -/
instance : HasL2Jets (testSection L₀ L₁) :=
  ⟨fun _ hξ ↦ (mem_testSection_iff.1 hξ).1.differentiable (by norm_num), fun _ ↦ memLp_jet⟩

variable (L₀ L₁) in
/-- The `L²` jet `(ξ, ∂s ξ, ∂t ξ)` of a test section, as a linear map into
`L²(ℝ × [0, 1], V × V × V)`. -/
abbrev jetₗ : testSection L₀ L₁ →ₗ[ℝ] Lp (V × V × V) 2 stripMeasure :=
  jetLp (testSection L₀ L₁)

variable (L₀ L₁) in
/-- The Sobolev space `W^{1,2}` of the strip `ℝ × [0, 1]` with boundary values in `L₀` and `L₁`:
the closure in `L²(ℝ × [0, 1], V × V × V)` of the jets of test sections, that is, the completion
of the test sections in the `W^{1,2}` norm. An element is an `L²` jet `(ξ, ξ_s, ξ_t)`. -/
abbrev H1 : Submodule ℝ (Lp (V × V × V) 2 stripMeasure) :=
  jetClosure (testSection L₀ L₁)

/-! ### Translation in the `s` direction -/

/-- The translate `ξ (· + a, ·)` of a test section is a test section. -/
theorem comp_add_right_mem_testSection (hξ : ξ ∈ testSection L₀ L₁) (a : ℝ) :
    (fun z ↦ ξ (z + (a, 0))) ∈ testSection L₀ L₁ := by
  obtain ⟨hξ2, hξc, hξ₀, hξ₁⟩ := mem_testSection_iff.1 hξ
  refine ⟨hξ2.comp (contDiff_id.add contDiff_const), ?_, fun s ↦ by simpa using hξ₀ (s + a),
    fun s ↦ by simpa using hξ₁ (s + a)⟩
  exact hξc.comp_homeomorph (Homeomorph.addRight ((a, 0) : ℝ × ℝ))

/-- The test sections are invariant under translation in the `s` direction. -/
instance : IsTranslationInvariant (testSection L₀ L₁) :=
  ⟨fun _ hξ a ↦ comp_add_right_mem_testSection hξ a⟩

end TauCeti.StripSobolev
