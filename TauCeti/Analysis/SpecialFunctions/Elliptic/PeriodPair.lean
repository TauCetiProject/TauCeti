/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Removable singularities along a period lattice

Elementary analytic facts about functions that are only controlled off the lattice `L.lattice` of
a period pair `L`:

* `PeriodPair.differentiableAt_zero_ite_div`: the quotient `A / B` of two functions analytic at
  `0` and vanishing there, extended by `c` on the lattice, is differentiable at `0`;
* `PeriodPair.differentiable_of_periodic`: a lattice-periodic function that is differentiable at
  `0` and off the lattice is entire;
* `PeriodPair.eq_of_forall_notMem_lattice`: two continuous functions that agree off the lattice
  agree everywhere.
-/

public section

namespace PeriodPair

variable (L : PeriodPair)

open Classical in
/-- The quotient `A / B` of two functions analytic at `0` and vanishing there, extended by `c` on
the lattice, is differentiable at `0` when `A` and `B` have derivatives `c * b` and `b ≠ 0`
there. -/
lemma differentiableAt_zero_ite_div {A B : ℂ → ℂ} {c b : ℂ} (hA : AnalyticAt ℂ A 0)
    (hB : AnalyticAt ℂ B 0) (hA₀ : A 0 = 0) (hB₀ : B 0 = 0) (hdA : HasDerivAt A (c * b) 0)
    (hdB : HasDerivAt B b 0) (hb : b ≠ 0) :
    DifferentiableAt ℂ (fun z ↦ if z ∈ L.lattice then c else A z / B z) 0 := by
  have hBd : dslope B 0 0 ≠ 0 := by
    rwa [dslope_same, hdB.deriv]
  refine ((hA.dslope 0).differentiableAt.div (hB.dslope 0).differentiableAt
    hBd).congr_of_eventuallyEq ?_
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with x hx
  by_cases hx₀ : x = 0
  · subst hx₀
    simp only [L.lattice.zero_mem, ite_true, Pi.div_apply, dslope_same, hdA.deriv, hdB.deriv]
    exact (mul_div_cancel_right₀ c hb).symm
  · have hxL : x ∉ L.lattice := fun h ↦ hx ⟨h, hx₀⟩
    simp only [hxL, ite_false]
    rw [Pi.div_apply, dslope_of_ne _ hx₀, dslope_of_ne _ hx₀, slope_def_field, slope_def_field,
      hA₀, hB₀, sub_zero, sub_zero, sub_zero, div_div_div_cancel_right₀ hx₀]

/-- A function that is periodic under every lattice vector, differentiable at `0` and
differentiable off the lattice is differentiable everywhere. -/
lemma differentiable_of_periodic {H : ℂ → ℂ} (hper : ∀ w ∈ L.lattice, Function.Periodic H w)
    (h₀ : DifferentiableAt ℂ H 0) (hoff : ∀ x ∉ L.lattice, DifferentiableAt ℂ H x) :
    Differentiable ℂ H := by
  intro x
  by_cases hx : x ∈ L.lattice
  · have hcomp : H = fun y ↦ H (y - x) := funext fun y ↦ by
      rw [← hper x hx (y - x), sub_add_cancel]
    have h₁ : DifferentiableAt ℂ (fun y : ℂ ↦ y - x) x := differentiableAt_id.sub_const x
    have h₂ : DifferentiableAt ℂ H ((fun y : ℂ ↦ y - x) x) := by simpa using h₀
    have h₃ : DifferentiableAt ℂ (fun y ↦ H (y - x)) x := h₂.comp (f := fun y ↦ y - x) x h₁
    rwa [← hcomp] at h₃
  · exact hoff x hx

/-- Two continuous functions into a Hausdorff space that agree off the lattice agree everywhere. -/
lemma eq_of_forall_notMem_lattice {Y : Type*} [TopologicalSpace Y] [T2Space Y] {f g : ℂ → Y}
    (hf : Continuous f) (hg : Continuous g) (h : ∀ y ∉ L.lattice, f y = g y) (z : ℂ) :
    f z = g z := by
  have : Countable L.lattice := L.latticeEquivProd.injective.countable
  have hdense : Dense (L.lattice : Set ℂ)ᶜ :=
    (Set.countable_coe_iff.mp this).dense_compl ℂ
  exact congrFun (hf.ext_on hdense hg h) z

end PeriodPair
